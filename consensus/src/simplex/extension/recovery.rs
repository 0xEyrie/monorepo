//! Authenticated status proofs for one unresolved extension slot.
//!
//! Statuses are forwarded individual claims, so their signing scheme must be
//! attributable. Threshold partial signatures alone are not sufficient. The
//! application may configure a separate attributable scheme over the identical
//! validator roster when final votes use a threshold scheme.
//!
//! This implements only the bounded n > 5f status-selection rule. It does not
//! authorize a native view change, a skipped proposal, or canonical delivery.
//! Native ancestry, leader authority and application validity remain mandatory.

use super::vote::Statement;
use crate::{
    simplex::{
        scheme,
        types::{Proposal, Subject},
    },
    types::Round,
};
use bytes::BufMut;
use commonware_codec::{Buf, EncodeSize, Error as CodecError, Read, ReadExt as _, Write};
use commonware_cryptography::{
    Digest, Hasher,
    certificate::{self, Attestation},
};
use commonware_parallel::Strategy;
use commonware_utils::{Faults as _, N3f1};
use rand_core::CryptoRng;
use std::collections::BTreeMap;

pub(crate) const SIGNING_TAG: &[u8] = b"_COMMONWARE_CONSENSUS_SIMPLEX_EXTENSION_STATUS_V1";

/// A frozen pre-ballot claim, signed only after persisting the local promise.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Promise<D: Digest> {
    /// Immutable original first-phase proposal.
    pub proposal: Proposal<D>,
    /// Genesis/runtime/interpretation-version commitment.
    pub domain: D,
    /// Target recovery ballot, strictly after the original proposal round.
    pub ballot: Round,
    /// Last accepted ballot and complete value commitment before this promise.
    /// No acceptance is an explicit signed claim, not missing evidence.
    pub accepted: Option<(Round, D)>,
}

impl<D: Digest> Promise<D> {
    /// Binds a returned local fence status to its exact signing context.
    ///
    /// This checks the conversion only. The caller must obtain `status` from a
    /// successful durable promise, never from an untrusted peer or local cache.
    #[cfg(not(target_arch = "wasm32"))]
    pub fn from_fenced<H: Hasher<Digest = D>>(
        statement: &Statement<D>,
        status: super::fence::Status<D>,
    ) -> Result<Self, Error> {
        if status.slot != statement.slot::<H>() || status.ballot != statement.ballot.view().get() {
            return Err(Error::Context);
        }
        let promise = Self {
            proposal: statement.proposal.clone(),
            domain: statement.domain,
            ballot: statement.ballot,
            accepted: status.accepted.map(|accepted| {
                (
                    Round::new(
                        statement.ballot.epoch(),
                        crate::types::View::new(accepted.ballot),
                    ),
                    accepted.value,
                )
            }),
        };
        if !promise.valid() {
            return Err(Error::Context);
        }
        Ok(promise)
    }

    /// Structural context checks; this does not prove that a promise is durable.
    pub fn valid(&self) -> bool {
        self.ballot.epoch() == self.proposal.round.epoch()
            && self.ballot.view() > self.proposal.round.view()
            && self.accepted.as_ref().is_none_or(|(round, _)| {
                round.epoch() == self.ballot.epoch()
                    && round.view() >= self.proposal.round.view()
                    && round.view() < self.ballot.view()
            })
    }
}

impl<D: Digest> Write for Promise<D> {
    fn write(&self, writer: &mut impl BufMut) {
        1u8.write(writer);
        self.proposal.write(writer);
        self.domain.write(writer);
        self.ballot.write(writer);
        self.accepted.write(writer);
    }
}
impl<D: Digest> EncodeSize for Promise<D> {
    fn encode_size(&self) -> usize {
        1 + self.proposal.encode_size()
            + self.domain.encode_size()
            + self.ballot.encode_size()
            + self.accepted.encode_size()
    }
}
impl<D: Digest> Read for Promise<D> {
    type Cfg = ();
    fn read_cfg(reader: &mut impl Buf, _: &()) -> Result<Self, CodecError> {
        if u8::read(reader)? != 1 {
            return Err(CodecError::Invalid("extension status", "unknown version"));
        }
        Ok(Self {
            proposal: Proposal::read(reader)?,
            domain: D::read(reader)?,
            ballot: Round::read(reader)?,
            accepted: Option::<(Round, D)>::read_cfg(reader, &((), ()))?,
        })
    }
}

/// Individually attributable recovery status, not a common-message certificate.
#[derive(Clone, Debug)]
pub struct Status<S: certificate::Scheme, D: Digest> {
    /// The exact frozen promise.
    pub promise: Promise<D>,
    /// Individual native-scheme signature and participant identity.
    pub attestation: Attestation<S>,
}
impl<S: scheme::Scheme<D>, D: Digest> Status<S, D> {
    /// Signs after the caller durably fences this slot against all older ballots.
    ///
    /// Non-attributable schemes are rejected even when they can sign final votes.
    pub fn sign(scheme: &S, promise: Promise<D>) -> Result<Self, Error> {
        if !S::is_attributable() {
            return Err(Error::Attribution);
        }
        if !promise.valid() {
            return Err(Error::Context);
        }
        let attestation = scheme
            .sign::<D>(Subject::ExtensionStatus { promise: &promise })
            .ok_or(Error::Signature)?;
        Ok(Self {
            promise,
            attestation,
        })
    }

    /// Checks transferable attribution and structural context, not persistence.
    pub fn verify<R: CryptoRng>(&self, rng: &mut R, scheme: &S, strategy: &impl Strategy) -> bool {
        S::is_attributable()
            && self.promise.valid()
            && scheme.verify_attestation::<_, D>(
                rng,
                Subject::ExtensionStatus {
                    promise: &self.promise,
                },
                &self.attestation,
                strategy,
            )
    }
}
impl<S: certificate::Scheme, D: Digest> Write for Status<S, D> {
    fn write(&self, writer: &mut impl BufMut) {
        self.promise.write(writer);
        self.attestation.write(writer);
    }
}
impl<S: certificate::Scheme, D: Digest> EncodeSize for Status<S, D> {
    fn encode_size(&self) -> usize {
        self.promise.encode_size() + self.attestation.encode_size()
    }
}
impl<S: certificate::Scheme, D: Digest> Read for Status<S, D> {
    type Cfg = ();
    fn read_cfg(reader: &mut impl Buf, _: &()) -> Result<Self, CodecError> {
        Ok(Self {
            promise: Promise::read(reader)?,
            attestation: Attestation::read(reader)?,
        })
    }
}

/// A frozen set of distinct, ascending-participant status messages.
#[derive(Clone, Debug)]
pub struct Proof<S: certificate::Scheme, D: Digest> {
    /// Exactly the native quorum, with each original signature retained.
    pub statuses: Vec<Status<S, D>>,
}
impl<S: certificate::Scheme, D: Digest> Write for Proof<S, D> {
    fn write(&self, writer: &mut impl BufMut) {
        self.statuses.write(writer);
    }
}
impl<S: certificate::Scheme, D: Digest> EncodeSize for Proof<S, D> {
    fn encode_size(&self) -> usize {
        self.statuses.encode_size()
    }
}
impl<S: certificate::Scheme, D: Digest> Read for Proof<S, D> {
    /// Maximum participants allowed by the configured roster; checked before allocation.
    type Cfg = usize;
    fn read_cfg(reader: &mut impl Buf, max: &usize) -> Result<Self, CodecError> {
        Ok(Self {
            statuses: Vec::read_cfg(reader, &((0..=*max).into(), ()))?,
        })
    }
}

/// A failed recovery evidence check. No failure authorizes identity fallback.
#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum Error {
    /// Individual signatures are not transferable identity evidence.
    #[error("recovery status requires an attributable signing scheme")]
    Attribution,
    /// The elementary recovery rule has not been established for this roster.
    #[error("extension recovery requires n > 5f under the configured native fault model")]
    UnsupportedRoster,
    /// Status count differs from the unchanged native quorum.
    #[error("invalid extension recovery quorum")]
    Quorum,
    /// Original proposal/domain/target ballot or accepted ballot is invalid.
    #[error("invalid extension recovery context")]
    Context,
    /// Duplicate or non-canonical participant ordering.
    #[error("recovery signers must be distinct and ascending")]
    Identity,
    /// A signer or signature is invalid, or the local scheme cannot sign.
    #[error("invalid extension status signature")]
    Signature,
}

/// Checked single-slot selection constraints, not native recovery authority.
///
/// This value cannot be decoded or constructed without verifying a proof.
/// Callers must retain the original proof and separately verify native eligibility,
/// parent certification, leader identity and the application interpretation.
#[derive(Clone, Debug)]
pub struct Verified<D: Digest> {
    proposal: Proposal<D>,
    domain: D,
    ballot: Round,
    forced: Option<D>,
}
impl<D: Digest> Verified<D> {
    /// Value that every valid selection from this proof must preserve, if any.
    pub const fn forced_value(&self) -> Option<D> {
        self.forced
    }

    /// Checks this exact proposal/domain/ballot and any forced interpretation.
    pub fn permits<H: Hasher<Digest = D>>(&self, statement: &Statement<D>) -> bool {
        self.permits_value(statement, statement.value::<H>())
    }

    pub(crate) fn permits_value(&self, statement: &Statement<D>, value: D) -> bool {
        statement.proposal == self.proposal
            && statement.domain == self.domain
            && statement.ballot == self.ballot
            && self.forced.is_none_or(|forced| forced == value)
    }
}

impl<S: scheme::Scheme<D>, D: Digest> Proof<S, D> {
    /// Authenticates the frozen proof and applies the n > 5f status rule.
    ///
    /// A quorum q = n-f preserves a hidden old certificate via at least
    /// 2q-n-f original status claims. Distinct values cannot both reach that
    /// threshold inside one q-sized proof when n > 5f. This is a single-slot
    /// constraint, not a proof of the composed Simplex recovery protocol.
    pub fn verify<R: CryptoRng>(
        &self,
        rng: &mut R,
        scheme: &S,
        expected: &Statement<D>,
        strategy: &impl Strategy,
    ) -> Result<Verified<D>, Error> {
        if !S::is_attributable() {
            return Err(Error::Attribution);
        }
        let n = u32::try_from(scheme.participants().len()).map_err(|_| Error::UnsupportedRoster)?;
        if n == 0 {
            return Err(Error::UnsupportedRoster);
        }
        let f = N3f1::max_faults(n);
        if u64::from(n) <= 5 * u64::from(f) {
            return Err(Error::UnsupportedRoster);
        }
        let q = N3f1::quorum(n);
        if self.statuses.len() != q as usize {
            return Err(Error::Quorum);
        }
        if !expected.valid_ballot() || expected.ballot == expected.proposal.round {
            return Err(Error::Context);
        }
        let mut previous = None;
        let mut support = BTreeMap::<D, u32>::new();
        for status in &self.statuses {
            let promise = &status.promise;
            if promise.proposal != expected.proposal
                || promise.domain != expected.domain
                || promise.ballot != expected.ballot
                || !promise.valid()
            {
                return Err(Error::Context);
            }
            let id = status.attestation.signer;
            if previous.is_some_and(|last| last >= id) {
                return Err(Error::Identity);
            }
            previous = Some(id);
            if !status.verify(rng, scheme, strategy) {
                return Err(Error::Signature);
            }
            if let Some((_, value)) = promise.accepted {
                *support.entry(value).or_default() += 1;
            }
        }
        let threshold = q - 2 * f;
        let forced = support
            .into_iter()
            .find_map(|(value, count)| (count >= threshold).then_some(value));
        Ok(Verified {
            proposal: expected.proposal.clone(),
            domain: expected.domain,
            ballot: expected.ballot,
            forced,
        })
    }
}

#[cfg(feature = "arbitrary")]
impl<'a, D: Digest + for<'b> arbitrary::Arbitrary<'b>> arbitrary::Arbitrary<'a> for Promise<D> {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        Ok(Self {
            proposal: u.arbitrary()?,
            domain: u.arbitrary()?,
            ballot: u.arbitrary()?,
            accepted: u.arbitrary()?,
        })
    }
}
#[cfg(feature = "arbitrary")]
impl<'a, S: certificate::Scheme, D: Digest + for<'b> arbitrary::Arbitrary<'b>>
    arbitrary::Arbitrary<'a> for Status<S, D>
where
    S::Signature: for<'b> arbitrary::Arbitrary<'b>,
{
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        Ok(Self {
            promise: u.arbitrary()?,
            attestation: u.arbitrary()?,
        })
    }
}
#[cfg(feature = "arbitrary")]
impl<'a, S: certificate::Scheme, D: Digest + for<'b> arbitrary::Arbitrary<'b>>
    arbitrary::Arbitrary<'a> for Proof<S, D>
where
    S::Signature: for<'b> arbitrary::Arbitrary<'b>,
{
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let mut statuses = Vec::new();
        for _ in 0..u.int_in_range(0..=16)? {
            statuses.push(u.arbitrary()?);
        }
        Ok(Self { statuses })
    }
}
