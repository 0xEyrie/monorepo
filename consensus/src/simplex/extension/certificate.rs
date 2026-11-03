//! Distinct routing roles for current-round and recovery extension certificates.
//!
//! An interpretation recovered in a later ballot cannot itself advance native
//! finality: its original proposal may have been skipped. Descendant native
//! finality must establish that proposal's ancestry before canonical delivery.
//! These wrappers check role and signatures, not native ancestry or policy.

use super::vote;
use crate::{simplex::scheme, types::Round};
use bytes::BufMut;
use commonware_codec::{Buf, EncodeSize, Error, Read, ReadExt as _, Write};
use commonware_cryptography::{Digest, certificate::Scheme};
use commonware_parallel::Strategy;
use rand_core::CryptoRng;

/// Current-round finalization candidate, still requiring native eligibility,
/// application validation and exact parent interpretation before adoption.
#[derive(Clone, Debug)]
pub struct Finalization<S: Scheme, D: Digest>(vote::Certificate<S, D>);

impl<S: Scheme, D: Digest> Finalization<S, D> {
    /// Rejects later-ballot recovery certificates without erasing their context.
    pub fn new(certificate: vote::Certificate<S, D>) -> Result<Self, vote::Certificate<S, D>> {
        if certificate.statement.ballot != certificate.statement.proposal.round {
            return Err(certificate);
        }
        Ok(Self(certificate))
    }

    /// Exact immutable signed interpretation.
    pub const fn certificate(&self) -> &vote::Certificate<S, D> {
        &self.0
    }
}

/// Later-ballot interpretation certificate. Never a direct native finality input.
#[derive(Clone, Debug)]
pub struct Recovered<S: Scheme, D: Digest>(vote::Certificate<S, D>);
impl<S: Scheme, D: Digest> Recovered<S, D> {
    /// Rejects cross-epoch, earlier-ballot and ordinary finalization subjects.
    pub fn new(certificate: vote::Certificate<S, D>) -> Result<Self, vote::Certificate<S, D>> {
        if !certificate.statement.valid_ballot()
            || certificate.statement.ballot == certificate.statement.proposal.round
        {
            return Err(certificate);
        }
        Ok(Self(certificate))
    }

    /// Exact interpretation retained for parent verification and recovery.
    pub const fn certificate(&self) -> &vote::Certificate<S, D> {
        &self.0
    }
}

/// Explicit certificate role on the extension channel. The stock Simplex
/// certificate wire format is not used to represent either variant.
#[derive(Clone, Debug)]
pub enum Certificate<S: Scheme, D: Digest> {
    /// Candidate for native finalization in the original proposal round.
    Finalization(Finalization<S, D>),
    /// Interpretation recovery only, with no direct native finality authority.
    Recovered(Recovered<S, D>),
}
impl<S: Scheme, D: Digest> Certificate<S, D> {
    /// Classifies a structurally valid certificate without changing its subject.
    pub fn classify(certificate: vote::Certificate<S, D>) -> Result<Self, vote::Certificate<S, D>> {
        match Finalization::new(certificate) {
            Ok(value) => Ok(Self::Finalization(value)),
            Err(certificate) => Recovered::new(certificate).map(Self::Recovered),
        }
    }

    /// Moves an original-round candidate into the native extended envelope.
    /// Returns recovered interpretations to the caller for the recovery path;
    /// no ordinary Simplex certificate is fabricated by this conversion.
    pub fn into_native(
        self,
    ) -> Result<
        crate::simplex::types::CertificateWith<S, D, crate::simplex::phase2::Extended>,
        Recovered<S, D>,
    > {
        match self {
            Self::Finalization(certificate) => Ok(
                crate::simplex::types::CertificateWith::Finalization(certificate),
            ),
            Self::Recovered(certificate) => Err(certificate),
        }
    }

    /// Exact native-scheme certificate with its original proposal and ballot.
    pub const fn certificate(&self) -> &vote::Certificate<S, D> {
        match self {
            Self::Finalization(f) => f.certificate(),
            Self::Recovered(r) => r.certificate(),
        }
    }

    /// Target ballot for routing; this may differ from the original proposal view.
    pub const fn ballot(&self) -> Round {
        self.certificate().statement.ballot
    }

    /// Checks role-preserving cryptographic authentication, not consensus authority.
    pub fn verify<R: CryptoRng>(
        &self,
        rng: &mut R,
        scheme: &impl scheme::CertificateVerifier<D, Certificate = S::Certificate>,
        strategy: &impl Strategy,
    ) -> bool {
        self.certificate().verify(rng, scheme, strategy)
    }
}
impl<S: Scheme, D: Digest> Write for Certificate<S, D> {
    fn write(&self, writer: &mut impl BufMut) {
        1u8.write(writer);
        match self {
            Self::Finalization(_) => 0u8.write(writer),
            Self::Recovered(_) => 1u8.write(writer),
        }
        self.certificate().write(writer);
    }
}
impl<S: Scheme, D: Digest> EncodeSize for Certificate<S, D> {
    fn encode_size(&self) -> usize {
        2 + self.certificate().encode_size()
    }
}
impl<S: Scheme, D: Digest> Read for Certificate<S, D> {
    type Cfg = <S::Certificate as Read>::Cfg;
    fn read_cfg(reader: &mut impl Buf, cfg: &Self::Cfg) -> Result<Self, Error> {
        if u8::read(reader)? != 1 {
            return Err(Error::Invalid("extension certificate", "unknown version"));
        }
        let role = u8::read(reader)?;
        if role > 1 {
            return Err(Error::Invalid("extension certificate", "unknown role"));
        }
        let certificate = vote::Certificate::read_cfg(reader, cfg)?;
        match role {
            0 => Finalization::new(certificate).map(Self::Finalization),
            _ => Recovered::new(certificate).map(Self::Recovered),
        }
        .map_err(|_| Error::Invalid("extension certificate", "ballot does not match role"))
    }
}
#[cfg(feature = "arbitrary")]
impl<'a, S: Scheme, D: Digest + for<'b> arbitrary::Arbitrary<'b>> arbitrary::Arbitrary<'a>
    for Certificate<S, D>
where
    S::Certificate: for<'b> arbitrary::Arbitrary<'b>,
{
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let mut cert = vote::Certificate::<S, D>::arbitrary(u)?;
        let recovered: bool = u.arbitrary()?;
        cert.statement.ballot = cert.statement.proposal.round;
        if recovered {
            let view = cert
                .statement
                .proposal
                .round
                .view()
                .get()
                .checked_add(1)
                .ok_or(arbitrary::Error::IncorrectFormat)?;
            cert.statement.ballot = Round::new(
                cert.statement.proposal.round.epoch(),
                crate::types::View::new(view),
            );
        }
        Ok(Self::classify(cert).expect("generated valid role"))
    }
}

/// Original-round extension final vote. Later-ballot interpretation votes cannot
/// enter the native phase-two vote envelope through this type.
#[derive(Clone, Debug)]
pub struct Finalize<S: Scheme, D: Digest>(vote::Vote<S, D>);
impl<S: Scheme, D: Digest> Finalize<S, D> {
    /// Preserves the exact signed vote and rejects a recovery ballot.
    pub fn new(vote: vote::Vote<S, D>) -> Result<Self, vote::Vote<S, D>> {
        if vote.statement.ballot != vote.statement.proposal.round {
            return Err(vote);
        }
        Ok(Self(vote))
    }
    /// Immutable complete original-round vote.
    pub const fn vote(&self) -> &vote::Vote<S, D> {
        &self.0
    }
}
impl<S: Scheme, D: Digest> PartialEq for Finalize<S, D> {
    fn eq(&self, other: &Self) -> bool {
        self.0.statement == other.0.statement && self.0.attestation == other.0.attestation
    }
}
impl<S: Scheme, D: Digest> PartialEq for Finalization<S, D> {
    fn eq(&self, other: &Self) -> bool {
        self.0.statement == other.0.statement && self.0.certificate == other.0.certificate
    }
}
impl<S: Scheme, D: Digest> crate::Epochable for Finalize<S, D> {
    fn epoch(&self) -> crate::types::Epoch {
        self.0.statement.proposal.round.epoch()
    }
}
impl<S: Scheme, D: Digest> crate::Viewable for Finalize<S, D> {
    fn view(&self) -> crate::types::View {
        self.0.statement.proposal.round.view()
    }
}
impl<S: Scheme, D: Digest> crate::Epochable for Finalization<S, D> {
    fn epoch(&self) -> crate::types::Epoch {
        self.0.statement.proposal.round.epoch()
    }
}
impl<S: Scheme, D: Digest> crate::Viewable for Finalization<S, D> {
    fn view(&self) -> crate::types::View {
        self.0.statement.proposal.round.view()
    }
}
impl<S: Scheme, D: Digest> Write for Finalize<S, D> {
    fn write(&self, writer: &mut impl BufMut) {
        self.0.write(writer);
    }
}
impl<S: Scheme, D: Digest> EncodeSize for Finalize<S, D> {
    fn encode_size(&self) -> usize {
        self.0.encode_size()
    }
}
impl<S: Scheme, D: Digest> Read for Finalize<S, D> {
    type Cfg = ();
    fn read_cfg(reader: &mut impl Buf, _: &()) -> Result<Self, Error> {
        Self::new(vote::Vote::read(reader)?).map_err(|_| {
            Error::Invalid("extension finalize", "recovery vote is not native finality")
        })
    }
}
impl<S: Scheme, D: Digest> Write for Finalization<S, D> {
    fn write(&self, writer: &mut impl BufMut) {
        self.0.write(writer);
    }
}
impl<S: Scheme, D: Digest> EncodeSize for Finalization<S, D> {
    fn encode_size(&self) -> usize {
        self.0.encode_size()
    }
}
impl<S: Scheme, D: Digest> Read for Finalization<S, D> {
    type Cfg = <S::Certificate as Read>::Cfg;
    fn read_cfg(reader: &mut impl Buf, cfg: &Self::Cfg) -> Result<Self, Error> {
        Self::new(vote::Certificate::read_cfg(reader, cfg)?).map_err(|_| {
            Error::Invalid(
                "extension finalization",
                "recovery certificate is not native finality",
            )
        })
    }
}
#[cfg(feature = "arbitrary")]
impl<'a, S: Scheme, D: Digest + for<'b> arbitrary::Arbitrary<'b>> arbitrary::Arbitrary<'a>
    for Finalize<S, D>
where
    S::Signature: for<'b> arbitrary::Arbitrary<'b>,
{
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let mut vote = vote::Vote::<S, D>::arbitrary(u)?;
        vote.statement.ballot = vote.statement.proposal.round;
        Ok(Self::new(vote).expect("original-round vote"))
    }
}
#[cfg(feature = "arbitrary")]
impl<'a, S: Scheme, D: Digest + for<'b> arbitrary::Arbitrary<'b>> arbitrary::Arbitrary<'a>
    for Finalization<S, D>
where
    S::Certificate: for<'b> arbitrary::Arbitrary<'b>,
{
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let mut cert = vote::Certificate::<S, D>::arbitrary(u)?;
        cert.statement.ballot = cert.statement.proposal.round;
        Ok(Self::new(cert).expect("original-round certificate"))
    }
}

impl<S: Scheme, D: Digest> From<Finalize<S, D>>
    for crate::simplex::types::VoteWith<S, D, crate::simplex::phase2::Extended>
{
    fn from(vote: Finalize<S, D>) -> Self {
        Self::Finalize(vote)
    }
}

impl<S: Scheme, D: Digest> crate::types::Attributable for Finalize<S, D> {
    fn signer(&self) -> crate::types::Participant {
        self.0.attestation.signer
    }
}

impl<S: Scheme, D: Digest> Eq for Finalize<S, D> {}
impl<S: Scheme, D: Digest> Eq for Finalization<S, D> {}
impl<S: Scheme, D: Digest> std::hash::Hash for Finalize<S, D> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.statement.hash(state);
        self.0.attestation.hash(state);
    }
}
impl<S: Scheme, D: Digest> std::hash::Hash for Finalization<S, D> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.statement.hash(state);
        self.0.certificate.hash(state);
    }
}

impl<S: Scheme, D: Digest> PartialEq for Recovered<S, D> {
    fn eq(&self, other: &Self) -> bool {
        self.0.statement == other.0.statement && self.0.certificate == other.0.certificate
    }
}
impl<S: Scheme, D: Digest> crate::Epochable for Recovered<S, D> {
    fn epoch(&self) -> crate::types::Epoch {
        self.0.statement.proposal.round.epoch()
    }
}
impl<S: Scheme, D: Digest> crate::Viewable for Recovered<S, D> {
    fn view(&self) -> crate::types::View {
        self.0.statement.proposal.round.view()
    }
}
impl<S: Scheme, D: Digest> Write for Recovered<S, D> {
    fn write(&self, writer: &mut impl BufMut) {
        self.0.write(writer);
    }
}
impl<S: Scheme, D: Digest> EncodeSize for Recovered<S, D> {
    fn encode_size(&self) -> usize {
        self.0.encode_size()
    }
}
impl<S: Scheme, D: Digest> Read for Recovered<S, D> {
    type Cfg = <S::Certificate as Read>::Cfg;
    fn read_cfg(reader: &mut impl Buf, cfg: &Self::Cfg) -> Result<Self, Error> {
        Self::new(vote::Certificate::read_cfg(reader, cfg)?).map_err(|_| {
            Error::Invalid(
                "extension recovered",
                "original certificate is not recovery",
            )
        })
    }
}

#[cfg(feature = "arbitrary")]
impl<'a, S: Scheme, D: Digest + for<'b> arbitrary::Arbitrary<'b>> arbitrary::Arbitrary<'a>
    for Recovered<S, D>
where
    S::Certificate: for<'b> arbitrary::Arbitrary<'b>,
{
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let mut cert = vote::Certificate::<S, D>::arbitrary(u)?;
        let view = cert
            .statement
            .proposal
            .round
            .view()
            .get()
            .checked_add(1)
            .ok_or(arbitrary::Error::IncorrectFormat)?;
        cert.statement.ballot = Round::new(
            cert.statement.proposal.round.epoch(),
            crate::types::View::new(view),
        );
        Ok(Self::new(cert).expect("later-ballot certificate"))
    }
}
