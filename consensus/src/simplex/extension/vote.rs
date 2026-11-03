//! Exact final-vote subjects using the existing Simplex signing schemes.
//!
//! These signatures authenticate a proposed interpretation, not application
//! validity or consensus finality. The voter must verify original notarization,
//! leader authority, extension evidence, ancestry and recovery proofs, and persist
//! its decision before publishing. No separate application approval round is added.

use crate::{
    simplex::{
        scheme,
        types::{Proposal, Subject},
    },
    types::Round,
};
use bytes::BufMut;
use commonware_codec::{
    Buf, Encode as _, EncodeSize, Error as CodecError, Read, ReadExt as _, Write,
};
use commonware_cryptography::{
    Digest, Hasher,
    certificate::{self, AssemblyError, Attestation},
};
use commonware_parallel::Strategy;
use commonware_utils::iter::NonEmpty;
use rand_core::CryptoRng;
use std::collections::BTreeSet;

/// Domain tag inside the existing finalize namespace. Its message contains the
/// entire statement and cannot be confused with the shorter ordinary Proposal.
pub(crate) const SIGNING_TAG: &[u8] = b"_COMMONWARE_CONSENSUS_SIMPLEX_EXTENSION_FINALIZE_V1";
const SLOT_TAG: &[u8] = b"_COMMONWARE_CONSENSUS_SIMPLEX_EXTENSION_SLOT_V1";
const VALUE_TAG: &[u8] = b"_COMMONWARE_CONSENSUS_SIMPLEX_EXTENSION_VALUE_V1";

/// Immutable original proposal and its exact proposed execution interpretation.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Statement<D: Digest> {
    /// Original first-phase proposal; recovery never rewrites it.
    pub proposal: Proposal<D>,
    /// Genesis/runtime/interpretation-version commitment, checked by the caller.
    pub domain: D,
    /// Target voting round, in the same epoch and no earlier than the original.
    pub ballot: Round,
    /// Commitment to the complete execution-parent interpretation.
    pub parent: D,
    /// Commitment to the immutable selected extension and required evidence.
    pub extension: D,
}

impl<D: Digest> Statement<D> {
    /// Checks only the structural ballot relation, not leader or recovery authority.
    pub fn valid_ballot(&self) -> bool {
        self.ballot.epoch() == self.proposal.round.epoch()
            && self.ballot.view() >= self.proposal.round.view()
    }

    /// Stable slot across differing parent interpretations and recovery ballots.
    pub fn slot<H: Hasher<Digest = D>>(&self) -> D {
        H::hash(&[SLOT_TAG, &self.domain.encode(), &self.proposal.encode()])
    }

    /// Accepted value independent of the ballot used to reaffirm it.
    pub fn value<H: Hasher<Digest = D>>(&self) -> D {
        H::hash(&[
            VALUE_TAG,
            &self.domain.encode(),
            &self.proposal.encode(),
            &self.parent.encode(),
            &self.extension.encode(),
        ])
    }
}

impl<D: Digest> Write for Statement<D> {
    fn write(&self, writer: &mut impl BufMut) {
        1u8.write(writer);
        self.proposal.write(writer);
        self.domain.write(writer);
        self.ballot.write(writer);
        self.parent.write(writer);
        self.extension.write(writer);
    }
}
impl<D: Digest> EncodeSize for Statement<D> {
    fn encode_size(&self) -> usize {
        1 + self.proposal.encode_size()
            + self.domain.encode_size()
            + self.ballot.encode_size()
            + self.parent.encode_size()
            + self.extension.encode_size()
    }
}
impl<D: Digest> Read for Statement<D> {
    type Cfg = ();
    fn read_cfg(reader: &mut impl Buf, _: &()) -> Result<Self, CodecError> {
        if u8::read(reader)? != 1 {
            return Err(CodecError::Invalid("simplex extension", "unknown version"));
        }
        Ok(Self {
            proposal: Proposal::read(reader)?,
            domain: D::read(reader)?,
            ballot: Round::read(reader)?,
            parent: D::read(reader)?,
            extension: D::read(reader)?,
        })
    }
}

/// A native-scheme final vote over the complete extension statement.
#[derive(Clone, Debug)]
pub struct Vote<S: certificate::Scheme, D: Digest> {
    /// Exact subject, including the immutable first proposal.
    pub statement: Statement<D>,
    /// Native signature and participant index.
    pub attestation: Attestation<S>,
}

impl<S: scheme::Scheme<D>, D: Digest> Vote<S, D> {
    /// Constructs a signature after external validity and local fence checks.
    ///
    /// As with native Finalize::sign, this does not itself persist or publish.
    pub fn sign(scheme: &S, statement: Statement<D>) -> Option<Self> {
        if !statement.valid_ballot() {
            return None;
        }
        let attestation = scheme.sign::<D>(Subject::FinalizeExtension {
            statement: &statement,
        })?;
        Some(Self {
            statement,
            attestation,
        })
    }

    /// Verifies the signature and ballot relation, not agreement authority.
    pub fn verify<R: CryptoRng>(&self, rng: &mut R, scheme: &S, strategy: &impl Strategy) -> bool {
        self.statement.valid_ballot()
            && scheme.verify_attestation::<_, D>(
                rng,
                Subject::FinalizeExtension {
                    statement: &self.statement,
                },
                &self.attestation,
                strategy,
            )
    }
}

impl<S: certificate::Scheme, D: Digest> Write for Vote<S, D> {
    fn write(&self, writer: &mut impl BufMut) {
        self.statement.write(writer);
        self.attestation.write(writer);
    }
}
impl<S: certificate::Scheme, D: Digest> EncodeSize for Vote<S, D> {
    fn encode_size(&self) -> usize {
        self.statement.encode_size() + self.attestation.encode_size()
    }
}
impl<S: certificate::Scheme, D: Digest> Read for Vote<S, D> {
    type Cfg = ();
    fn read_cfg(reader: &mut impl Buf, _: &()) -> Result<Self, CodecError> {
        Ok(Self {
            statement: Statement::read(reader)?,
            attestation: Attestation::read(reader)?,
        })
    }
}

/// Failure to assemble one exact statement from authenticated distinct votes.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// A vote concerns a different proposal, interpretation or target ballot.
    #[error("conflicting extension vote subject")]
    Subject,
    /// At least one signature or structural ballot is invalid.
    #[error("invalid extension vote")]
    InvalidVote,
    /// Native quorum/identity/signature-format validation failed.
    #[error(transparent)]
    Assembly(#[from] AssemblyError),
}

/// A native-scheme quorum certificate for one exact interpretation.
///
/// Not a finality capability by itself: original notarization, parent proofs and
/// the extended voter's view-change rules must also be verified before delivery.
#[derive(Clone, Debug)]
pub struct Certificate<S: certificate::Scheme, D: Digest> {
    /// Complete signed subject.
    pub statement: Statement<D>,
    /// Native scheme certificate, using its unchanged quorum requirement.
    pub certificate: S::Certificate,
}

impl<S: scheme::Scheme<D>, D: Digest> Certificate<S, D> {
    /// Verifies and consumes distinct votes for the same complete statement.
    pub fn from_votes<R: CryptoRng, I: Iterator<Item = Vote<S, D>> + Send>(
        rng: &mut R,
        scheme: &S,
        votes: NonEmpty<I>,
        strategy: &impl Strategy,
    ) -> Result<Self, Error> {
        let (first, rest) = votes.into_parts();
        if !first.verify(rng, scheme, strategy) {
            return Err(Error::InvalidVote);
        }
        let mut identities = BTreeSet::new();
        identities.insert(first.attestation.signer);
        let mut attestations = Vec::new();
        for vote in rest {
            if vote.statement != first.statement {
                return Err(Error::Subject);
            }
            if !identities.insert(vote.attestation.signer) {
                return Err(AssemblyError::DuplicateSigner(vote.attestation.signer).into());
            }
            if !vote.verify(rng, scheme, strategy) {
                return Err(Error::InvalidVote);
            }
            attestations.push(vote.attestation);
        }
        let certificate = scheme.assemble(
            NonEmpty::new(first.attestation, attestations.into_iter()),
            strategy,
        )?;
        Ok(Self {
            statement: first.statement,
            certificate,
        })
    }
}

impl<S: certificate::Scheme, D: Digest> Certificate<S, D> {
    /// Checks native certificate authentication and structural ballot validity.
    pub fn verify<R: CryptoRng>(
        &self,
        rng: &mut R,
        scheme: &impl scheme::CertificateVerifier<D, Certificate = S::Certificate>,
        strategy: &impl Strategy,
    ) -> bool {
        self.statement.valid_ballot()
            && scheme.verify_certificate::<_, D>(
                rng,
                Subject::FinalizeExtension {
                    statement: &self.statement,
                },
                &self.certificate,
                strategy,
            )
    }
}
impl<S: certificate::Scheme, D: Digest> Write for Certificate<S, D> {
    fn write(&self, writer: &mut impl BufMut) {
        self.statement.write(writer);
        self.certificate.write(writer);
    }
}
impl<S: certificate::Scheme, D: Digest> EncodeSize for Certificate<S, D> {
    fn encode_size(&self) -> usize {
        self.statement.encode_size() + self.certificate.encode_size()
    }
}
impl<S: certificate::Scheme, D: Digest> Read for Certificate<S, D> {
    type Cfg = <S::Certificate as Read>::Cfg;
    fn read_cfg(reader: &mut impl Buf, cfg: &Self::Cfg) -> Result<Self, CodecError> {
        Ok(Self {
            statement: Statement::read(reader)?,
            certificate: S::Certificate::read_cfg(reader, cfg)?,
        })
    }
}

#[cfg(feature = "arbitrary")]
impl<'a, D: Digest + for<'b> arbitrary::Arbitrary<'b>> arbitrary::Arbitrary<'a> for Statement<D> {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        Ok(Self {
            proposal: Proposal::arbitrary(u)?,
            domain: D::arbitrary(u)?,
            ballot: Round::arbitrary(u)?,
            parent: D::arbitrary(u)?,
            extension: D::arbitrary(u)?,
        })
    }
}
#[cfg(feature = "arbitrary")]
impl<'a, S: certificate::Scheme, D: Digest + for<'b> arbitrary::Arbitrary<'b>>
    arbitrary::Arbitrary<'a> for Vote<S, D>
where
    S::Signature: for<'b> arbitrary::Arbitrary<'b>,
{
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        Ok(Self {
            statement: Statement::arbitrary(u)?,
            attestation: Attestation::arbitrary(u)?,
        })
    }
}
#[cfg(feature = "arbitrary")]
impl<'a, S: certificate::Scheme, D: Digest + for<'b> arbitrary::Arbitrary<'b>>
    arbitrary::Arbitrary<'a> for Certificate<S, D>
where
    S::Certificate: for<'b> arbitrary::Arbitrary<'b>,
{
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        Ok(Self {
            statement: Statement::arbitrary(u)?,
            certificate: S::Certificate::arbitrary(u)?,
        })
    }
}
