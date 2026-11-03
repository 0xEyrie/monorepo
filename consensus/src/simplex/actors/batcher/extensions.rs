//! Incremental exact-subject extension vote collection for the extended phase.
//! Stock rounds do not instantiate this collector. Native voter eligibility and
//! application evidence must be checked before locally constructing any vote.

use crate::{
    simplex::{
        extension::{
            certificate::Certificate,
            vote::{Statement, Vote},
        },
        scheme,
        types::Proposal,
    },
    types::{Participant, Round},
};
use commonware_cryptography::{Digest, certificate::AssemblyError};
use commonware_parallel::Strategy;
use commonware_utils::{Faults as _, N3f1, iter::NonEmpty, ordered::Quorum as _};
use rand_core::CryptoRng;
use std::{collections::HashMap, sync::Arc};

/// Result of admitting one authenticated vote.
#[derive(Debug)]
pub enum Outcome<S: scheme::Scheme<D>, D: Digest> {
    /// Stored one new identity; no exact subject has quorum yet.
    Pending,
    /// The same identity and exact subject was already retained.
    Duplicate,
    /// Two verified signed subjects from one identity in this slot and ballot.
    /// Only attributable schemes provide transferable blame; threshold partials
    /// require authenticated peer provenance and cannot be exported as such proof.
    Equivocation {
        first: Vote<S, D>,
        second: Vote<S, D>,
    },
    /// An exact-subject quorum, classified without changing its native role.
    Certificate(Certificate<S, D>),
    /// Collection already produced a certificate. Caller retains/retransmits it.
    Complete,
}

/// A failed admission. Invalid remote messages never consume a participant slot.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("extension vote does not match collector context")]
    Context,
    #[error("invalid extension signature or signer")]
    Signature,
    #[error("extension collector requires a valid native roster")]
    Roster,
    #[error("extension collector failed during certificate assembly")]
    Poisoned,
    #[error(transparent)]
    Assembly(#[from] AssemblyError),
}

/// A bounded native-batcher collector for one original proposal and target ballot.
///
/// Tracks at most one verified vote per configured participant, and at most n
/// exact-subject groups. Different directions or parent interpretations never
/// share a quorum. The caller bounds how many collectors are active. Neither a
/// vote nor an assembled certificate authenticates application policy by itself.
pub struct Collector<S: scheme::Scheme<D>, D: Digest> {
    scheme: Arc<S>,
    proposal: Proposal<D>,
    domain: D,
    ballot: Round,
    quorum: usize,
    votes: Vec<Option<Vote<S, D>>>,
    groups: HashMap<Statement<D>, Vec<Participant>>,
    complete: bool,
    poisoned: bool,
}
impl<S: scheme::Scheme<D>, D: Digest> Collector<S, D> {
    /// Opens a bounded collector for a native-authorized proposal/ballot context.
    /// This checks structure only; the owner must establish that authorization.
    pub fn new(
        scheme: Arc<S>,
        proposal: Proposal<D>,
        domain: D,
        ballot: Round,
    ) -> Result<Self, Error> {
        let n = u32::try_from(scheme.participants().len()).map_err(|_| Error::Roster)?;
        if n == 0 {
            return Err(Error::Roster);
        }
        if ballot.epoch() != proposal.round.epoch() || ballot.view() < proposal.round.view() {
            return Err(Error::Context);
        }
        Ok(Self {
            scheme,
            proposal,
            domain,
            ballot,
            quorum: N3f1::quorum(n) as usize,
            votes: (0..n).map(|_| None).collect(),
            groups: HashMap::new(),
            complete: false,
            poisoned: false,
        })
    }

    /// Admits a network vote only from its authenticated participant. This is
    /// required for threshold partials and matches the stock batcher boundary.
    pub fn insert_from<R: CryptoRng>(
        &mut self,
        rng: &mut R,
        sender: &S::PublicKey,
        vote: Vote<S, D>,
        strategy: &impl Strategy,
    ) -> Result<Outcome<S, D>, Error> {
        if self.scheme.participants().index(sender) != Some(vote.attestation.signer) {
            return Err(Error::Signature);
        }
        self.insert(rng, vote, strategy)
    }

    /// Admits a local or already source-authenticated vote. Network messages must
    /// use `insert_from` to retain the native sender/signature identity check.
    /// Verifies and admits a vote. A bad signature cannot reserve an identity or
    /// poison an equivocation record. Native assembly consumes verified votes.
    pub fn insert<R: CryptoRng>(
        &mut self,
        rng: &mut R,
        vote: Vote<S, D>,
        strategy: &impl Strategy,
    ) -> Result<Outcome<S, D>, Error> {
        if self.poisoned {
            return Err(Error::Poisoned);
        }
        if self.complete {
            return Ok(Outcome::Complete);
        }
        if vote.statement.proposal != self.proposal
            || vote.statement.domain != self.domain
            || vote.statement.ballot != self.ballot
        {
            return Err(Error::Context);
        }
        let signer = vote.attestation.signer;
        let id = usize::from(signer);
        if id >= self.votes.len() {
            return Err(Error::Signature);
        }
        if self.votes[id].as_ref().is_some_and(|first| {
            first.statement == vote.statement && first.attestation == vote.attestation
        }) {
            return Ok(Outcome::Duplicate);
        }
        if !vote.verify(rng, self.scheme.as_ref(), strategy) {
            return Err(Error::Signature);
        }
        if let Some(first) = &self.votes[id] {
            return Ok(if first.statement == vote.statement {
                Outcome::Duplicate
            } else {
                Outcome::Equivocation {
                    first: first.clone(),
                    second: vote,
                }
            });
        }
        let statement = vote.statement.clone();
        self.votes[id] = Some(vote);
        let group = self.groups.entry(statement.clone()).or_default();
        group.push(signer);
        if group.len() < self.quorum {
            return Ok(Outcome::Pending);
        }
        // Consume only the exact group. Assembly cannot mix subjects or identities.
        let group = self
            .groups
            .remove(&statement)
            .expect("quorum group retained");
        let mut attestations = group.into_iter().map(|id| {
            self.votes[usize::from(id)]
                .take()
                .expect("verified vote retained")
                .attestation
        });
        let first = attestations.next().expect("positive quorum");
        let assembled = self
            .scheme
            .assemble(NonEmpty::new(first, attestations), strategy);
        let certificate = match assembled {
            Ok(certificate) => certificate,
            Err(error) => {
                self.poisoned = true;
                return Err(error.into());
            }
        };
        let certificate = Certificate::classify(crate::simplex::extension::vote::Certificate {
            statement,
            certificate,
        })
        .expect("collector enforces structural ballot relation");
        self.complete = true;
        self.votes.clear();
        self.groups.clear();
        Ok(Outcome::Certificate(certificate))
    }
}
