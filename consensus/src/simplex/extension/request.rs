//! Authenticated leader requests for the native voter's recovery journal.
//! A valid signature alone does not grant ballot, timeout or application eligibility.
use super::{
    recovery::{Error, Proof, Status},
    vote::{Statement, Vote},
};
use crate::{
    simplex::{
        scheme,
        types::{Proposal, Subject},
    },
    types::{Round, View},
};
use bytes::{BufMut, Bytes};
use commonware_codec::{
    Buf, Encode as _, EncodeSize, Error as CodecError, Read, ReadExt as _, Write,
};
use commonware_cryptography::{
    Digest,
    certificate::{Attestation, Scheme},
};
use commonware_parallel::Strategy;
use rand_core::CryptoRng;

pub(crate) const SIGNING_TAG: &[u8] = b"_COMMONWARE_CONSENSUS_SIMPLEX_RECOVERY_REQUEST_V1";
/// Aggregate request bound, including the original signed status proof.
pub const MAX_BYTES: usize = 1024 * 1024;
/// A request's exact decision. All fields are covered by the leader signature.
#[derive(Clone, Debug)]
pub enum Command<D: Digest> {
    /// Freeze status and fence older signing for this original proposal.
    Promise {
        proposal: Proposal<D>,
        domain: D,
        ballot: Round,
    },
    /// Accept an interpretation only after verifying the attached status proof.
    Accept(Statement<D>),
}
impl<D: Digest> Command<D> {
    pub const fn proposal(&self) -> &Proposal<D> {
        match self {
            Self::Promise { proposal, .. } => proposal,
            Self::Accept(s) => &s.proposal,
        }
    }
    pub const fn ballot(&self) -> Round {
        match self {
            Self::Promise { ballot, .. } => *ballot,
            Self::Accept(s) => s.ballot,
        }
    }
    pub const fn domain(&self) -> D {
        match self {
            Self::Promise { domain, .. } => *domain,
            Self::Accept(s) => s.domain,
        }
    }
    pub const fn subject(&self) -> Option<&Statement<D>> {
        match self {
            Self::Promise { .. } => None,
            Self::Accept(s) => Some(s),
        }
    }
}
impl<D: Digest> Write for Command<D> {
    fn write(&self, w: &mut impl BufMut) {
        match self {
            Self::Promise {
                proposal,
                domain,
                ballot,
            } => {
                0u8.write(w);
                proposal.write(w);
                domain.write(w);
                ballot.write(w);
            }
            Self::Accept(s) => {
                1u8.write(w);
                s.write(w);
            }
        }
    }
}
impl<D: Digest> EncodeSize for Command<D> {
    fn encode_size(&self) -> usize {
        1 + match self {
            Self::Promise {
                proposal,
                domain,
                ballot,
            } => proposal.encode_size() + domain.encode_size() + ballot.encode_size(),
            Self::Accept(s) => s.encode_size(),
        }
    }
}
impl<D: Digest> Read for Command<D> {
    type Cfg = ();
    fn read_cfg(r: &mut impl Buf, _: &()) -> Result<Self, CodecError> {
        match u8::read(r)? {
            0 => Ok(Self::Promise {
                proposal: Proposal::read(r)?,
                domain: D::read(r)?,
                ballot: Round::read(r)?,
            }),
            1 => Ok(Self::Accept(Statement::read(r)?)),
            _ => Err(CodecError::Invalid("recovery request", "unknown command")),
        }
    }
}
/// Untrusted request from a replacement leader; native state checks its elected identity.
#[derive(Clone, Debug)]
pub struct Request<S: Scheme, D: Digest> {
    pub command: Command<D>,
    /// Absent for Promise, mandatory for Accept. Original signatures are retained.
    pub proof: Option<Proof<S, D>>,
    pub attestation: Attestation<S>,
}
impl<S: scheme::Scheme<D>, D: Digest> Request<S, D> {
    fn valid(&self, members: usize) -> bool {
        let ballot = self.command.ballot();
        let p = self.command.proposal();
        self.encode_size() <= MAX_BYTES
            && ballot.epoch() == p.round.epoch()
            && ballot.view() > p.round.view()
            && match (&self.command, &self.proof) {
                (Command::Promise { .. }, None) => true,
                (Command::Accept(_), Some(proof)) => proof.statuses.len() <= members,
                _ => false,
            }
    }
    fn payload(command: &Command<D>, proof: &Option<Proof<S, D>>) -> Bytes {
        (command.clone(), proof.clone()).encode()
    }
    /// Signs a request without granting native eligibility or modifying local fences.
    pub fn sign(
        scheme: &S,
        command: Command<D>,
        proof: Option<Proof<S, D>>,
    ) -> Result<Self, Error> {
        if !S::is_attributable() {
            return Err(Error::Attribution);
        }
        if command.encode_size() + proof.encode_size() > MAX_BYTES {
            return Err(Error::Context);
        }
        let payload = Self::payload(&command, &proof);
        let attestation = scheme
            .sign::<D>(Subject::ExtensionRequest {
                round: command.ballot(),
                payload: &payload,
            })
            .ok_or(Error::Signature)?;
        let request = Self {
            command,
            proof,
            attestation,
        };
        if !request.valid(scheme.participants().len()) {
            return Err(Error::Context);
        }
        Ok(request)
    }
    /// Verifies the entire request, including original status evidence bytes.
    pub fn verify<R: CryptoRng>(&self, rng: &mut R, scheme: &S, strategy: &impl Strategy) -> bool {
        if !S::is_attributable() || !self.valid(scheme.participants().len()) {
            return false;
        }
        let payload = Self::payload(&self.command, &self.proof);
        scheme.verify_attestation::<_, D>(
            rng,
            Subject::ExtensionRequest {
                round: self.command.ballot(),
                payload: &payload,
            },
            &self.attestation,
            strategy,
        )
    }
}
impl<S: Scheme, D: Digest> Request<S, D> {
    pub const fn view(&self) -> View {
        self.command.proposal().round.view()
    }
}
impl<S: Scheme, D: Digest> Write for Request<S, D> {
    fn write(&self, w: &mut impl BufMut) {
        self.command.write(w);
        self.proof.write(w);
        self.attestation.write(w);
    }
}
impl<S: Scheme, D: Digest> EncodeSize for Request<S, D> {
    fn encode_size(&self) -> usize {
        self.command.encode_size() + self.proof.encode_size() + self.attestation.encode_size()
    }
}
impl<S: Scheme, D: Digest> Read for Request<S, D> {
    type Cfg = usize;
    fn read_cfg(r: &mut impl Buf, members: &usize) -> Result<Self, CodecError> {
        if r.remaining() > MAX_BYTES {
            return Err(CodecError::Invalid("recovery request", "oversized input"));
        }
        Ok(Self {
            command: Command::read(r)?,
            proof: Option::<Proof<S, D>>::read_cfg(r, &(*members).min(4096))?,
            attestation: Attestation::read(r)?,
        })
    }
}
/// Local coordinator query; never a peer authorization or a persisted decision.
/// The native voter selects eligible slots/ballots and authenticates all evidence.
#[derive(Clone, Debug)]
pub enum Query<S: Scheme, D: Digest> {
    /// Find the earliest eligible unresolved slot when this node is the known leader.
    Discover,
    /// Build an acceptance request in the retained promise's ballot, even after
    /// ordinary views advance. Responses must contain a complete original quorum.
    Accept {
        promise: Request<S, D>,
        responses: Vec<Response<S, D>>,
    },
}
impl<S: Scheme, D: Digest> Query<S, D> {
    /// Mailbox scheduling identity; discovery has no caller-selected view.
    pub const fn view(&self) -> View {
        match self {
            Self::Discover => View::zero(),
            Self::Accept { promise, .. } => promise.view(),
        }
    }
    /// Bounds retained local work before enqueueing, independently of authentication.
    pub fn bounded(&self) -> bool {
        match self {
            Self::Discover => true,
            Self::Accept { promise, responses } => {
                responses.len() <= 4096
                    && responses
                        .iter()
                        .try_fold(promise.encode_size(), |n, r| n.checked_add(r.encode_size()))
                        .is_some_and(|n| n <= MAX_BYTES)
            }
        }
    }
}

/// Emitted only after the native voter synchronizes the exact journal record.
#[derive(Clone, Debug)]
pub enum Response<S: Scheme, D: Digest> {
    /// The full prior statement is a preimage of the signed status value, not new authority.
    Status {
        status: Status<S, D>,
        accepted: Option<Statement<D>>,
    },
    Vote(Vote<S, D>),
}

impl<S: Scheme, D: Digest> EncodeSize for Response<S, D> {
    fn encode_size(&self) -> usize {
        1 + match self {
            Self::Status { status, accepted } => status.encode_size() + accepted.encode_size(),
            Self::Vote(vote) => vote.encode_size(),
        }
    }
}

impl<S: Scheme, D: Digest> Write for Response<S, D> {
    fn write(&self, w: &mut impl BufMut) {
        match self {
            Self::Status { status, accepted } => {
                0u8.write(w);
                status.write(w);
                accepted.write(w);
            }
            Self::Vote(vote) => {
                1u8.write(w);
                vote.write(w);
            }
        }
    }
}
impl<S: Scheme, D: Digest> Read for Response<S, D> {
    type Cfg = ();
    fn read_cfg(r: &mut impl Buf, _: &()) -> Result<Self, CodecError> {
        if r.remaining() > MAX_BYTES {
            return Err(CodecError::Invalid("recovery response", "oversized input"));
        }
        match u8::read(r)? {
            0 => Ok(Self::Status {
                status: Status::read(r)?,
                accepted: Option::<Statement<D>>::read(r)?,
            }),
            1 => Ok(Self::Vote(Vote::read(r)?)),
            _ => Err(CodecError::Invalid("recovery response", "unknown tag")),
        }
    }
}
#[cfg(feature = "arbitrary")]
impl<'a, S: Scheme, D: Digest + for<'b> arbitrary::Arbitrary<'b>> arbitrary::Arbitrary<'a>
    for Response<S, D>
where
    S::Signature: for<'b> arbitrary::Arbitrary<'b>,
{
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        Ok(if u.arbitrary()? {
            Self::Status {
                status: u.arbitrary()?,
                accepted: u.arbitrary()?,
            }
        } else {
            Self::Vote(u.arbitrary()?)
        })
    }
}

#[cfg(feature = "arbitrary")]
impl<'a, D: Digest + for<'b> arbitrary::Arbitrary<'b>> arbitrary::Arbitrary<'a> for Command<D> {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        Ok(if u.arbitrary()? {
            Self::Accept(u.arbitrary()?)
        } else {
            Self::Promise {
                proposal: u.arbitrary()?,
                domain: u.arbitrary()?,
                ballot: u.arbitrary()?,
            }
        })
    }
}
#[cfg(feature = "arbitrary")]
impl<'a, S: Scheme, D: Digest + for<'b> arbitrary::Arbitrary<'b>> arbitrary::Arbitrary<'a>
    for Request<S, D>
where
    S::Signature: for<'b> arbitrary::Arbitrary<'b>,
{
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        Ok(Self {
            command: u.arbitrary()?,
            proof: u.arbitrary()?,
            attestation: u.arbitrary()?,
        })
    }
}
