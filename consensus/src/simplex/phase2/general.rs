//! Original G1 wire authentication and native-owned original issuance adapter.
//!
//! Checked application material is supplied by a trusted deployment adapter.
//! Later-ballot recovery, long-term retention and Source delivery are not
//! activated here. Authentication alone checks declared signed claims.

use super::{Mode, recovery, sealed};
use crate::{
    Epochable, Viewable,
    simplex::{
        extension::agreement::general as g,
        scheme,
        types::{Notarize, Proposal, Subject},
    },
    types::{Attributable, Epoch, Participant, View},
};
use bytes::{Buf as _, BufMut};
use commonware_codec::{Buf, DecodeExt as _, EncodeSize, Error, Read, ReadExt as _, Write};
use commonware_cryptography::{
    Digest, Hasher,
    certificate::{Scheme, Scoped},
};
use commonware_parallel::Strategy;
use rand_core::CryptoRng;
use std::{fmt, marker::PhantomData};

/// Global decoding/authentication ceilings, not an admitted startup profile.
/// Deployment Limits::validate and trusted application checks remain required.
pub const WIRE_LIMITS: g::Limits = g::Limits {
    report_bytes: g::MAX_FIRST_BYTES,
    order_bytes: g::MAX_FIRST_BYTES,
    build_bytes: g::MAX_FIRST_BYTES,
    material_bytes: g::MAX_FIRST_BYTES,
    origin_bytes: g::MAX_EVIDENCE_BYTES,
};
const MAX_NATIVE_VOTE_BYTES: usize = 16 * 1024;
commonware_macros::stability_mod!(ALPHA, pub mod voting_wal);
#[cfg(not(target_arch = "wasm32"))]
commonware_macros::stability_mod!(ALPHA, pub mod voting);
/// Complete first-pair frame ceiling, including both length prefixes.
pub const MAX_FIRST_VOTE_BYTES: usize = 8 + 4 + MAX_NATIVE_VOTE_BYTES + 1 + g::MAX_FIRST_BYTES;

/// An unchanged native first vote and an optional genuine G1 FIRST envelope.
/// None differs from a signed FIRST with absent optional fields. Only the
/// trusted derived Core can establish whether None is permitted for this owner.
#[derive(Clone, Debug)]
pub struct FirstVote<S: Scheme, D: Digest> {
    native: Notarize<S, D>,
    first: Option<g::Signed<S, D>>,
}
impl<S: Scheme, D: Digest> FirstVote<S, D> {
    /// Wraps raw data without granting authentication or admission.
    pub const fn new(native: Notarize<S, D>, first: Option<g::Signed<S, D>>) -> Self {
        Self { native, first }
    }
    /// Exact ordinary native proposal vote.
    pub const fn native(&self) -> &Notarize<S, D> {
        &self.native
    }
    /// Exact optional signed FIRST, never reconstructed from another report.
    pub const fn first(&self) -> Option<&g::Signed<S, D>> {
        self.first.as_ref()
    }
    /// Moves both original envelopes without changing either signature.
    pub fn into_parts(self) -> (Notarize<S, D>, Option<g::Signed<S, D>>) {
        (self.native, self.first)
    }
    fn body_size(&self) -> usize {
        4 + self.native.encode_size() + 1 + self.first.as_ref().map_or(0, EncodeSize::encode_size)
    }
}
impl<S: scheme::Scheme<D>, D: Digest> FirstVote<S, D> {
    /// Authenticates the native vote and any present original FIRST. This does
    /// not bind a peer's declared Slot/Core/Input to trusted application input.
    pub fn authenticate<R: CryptoRng>(
        &self,
        rng: &mut R,
        scheme: &S,
        strategy: &impl Strategy,
    ) -> Result<(), g::Error> {
        g::Committee::new(scheme.participants().len())?;
        if !S::is_attributable() || <D as commonware_codec::FixedSize>::SIZE != 32 {
            return Err(g::Error::Roster);
        }
        if self.native.encode_size() > MAX_NATIVE_VOTE_BYTES
            || self.encode_size() > MAX_FIRST_VOTE_BYTES
        {
            return Err(g::Error::Limit);
        }
        if let Some(first) = &self.first {
            if first.encode_size() > g::MAX_FIRST_BYTES {
                return Err(g::Error::Limit);
            }
            if !matches!(&first.message.kind, g::Kind::First(_))
                || first.message.round != self.native.proposal.round
                || first.attestation.signer != self.native.attestation.signer
            {
                return Err(g::Error::Context);
            }
        }
        if !self.native.verify(rng, scheme, strategy)
            || self
                .first
                .as_ref()
                .is_some_and(|first| !first.verify(rng, scheme, WIRE_LIMITS, strategy))
        {
            return Err(g::Error::Signature);
        }
        Ok(())
    }
}
impl<S: Scheme, D: Digest> PartialEq for FirstVote<S, D> {
    fn eq(&self, other: &Self) -> bool {
        self.native == other.native
            && match (&self.first, &other.first) {
                (None, None) => true,
                (Some(a), Some(b)) => same_signed(a, b),
                _ => false,
            }
    }
}
impl<S: Scheme, D: Digest> Eq for FirstVote<S, D> {}
impl<S: Scheme, D: Digest> Write for FirstVote<S, D> {
    fn write(&self, writer: &mut impl BufMut) {
        writer.put_slice(b"G1F2");
        (self.body_size() as u32).write(writer);
        (self.native.encode_size() as u32).write(writer);
        self.native.write(writer);
        match &self.first {
            None => 0u8.write(writer),
            Some(first) => {
                1u8.write(writer);
                first.write(writer);
            }
        }
    }
}
impl<S: Scheme, D: Digest> EncodeSize for FirstVote<S, D> {
    fn encode_size(&self) -> usize {
        8 + self.body_size()
    }
}
impl<S: Scheme, D: Digest> Read for FirstVote<S, D> {
    type Cfg = ();
    fn read_cfg(reader: &mut impl Buf, _: &()) -> Result<Self, Error> {
        if <[u8; 4]>::read(reader)? != *b"G1F2" {
            return Err(Error::Invalid("G1 first pair", "type/version"));
        }
        let length = u32::read(reader)? as usize;
        if length > MAX_FIRST_VOTE_BYTES - 8 || length > reader.remaining() {
            return Err(Error::InvalidLength(length));
        }
        let mut body = reader.copy_to_bytes(length);
        let native_length = u32::read(&mut body)? as usize;
        if native_length > MAX_NATIVE_VOTE_BYTES || native_length > body.remaining() {
            return Err(Error::InvalidLength(native_length));
        }
        let native = Notarize::decode(body.copy_to_bytes(native_length))?;
        let first = match u8::read(&mut body)? {
            0 => None,
            1 => Some(g::Signed::read_cfg(&mut body, &WIRE_LIMITS)?),
            _ => return Err(Error::Invalid("G1 first pair", "option tag")),
        };
        if body.has_remaining() {
            return Err(Error::ExtraData(body.remaining()));
        }
        Ok(Self { native, first })
    }
}
impl<S: Scheme, D: Digest> Epochable for FirstVote<S, D> {
    fn epoch(&self) -> Epoch {
        self.native.epoch()
    }
}
impl<S: Scheme, D: Digest> Viewable for FirstVote<S, D> {
    fn view(&self) -> View {
        self.native.view()
    }
}
impl<S: Scheme, D: Digest> Attributable for FirstVote<S, D> {
    fn signer(&self) -> Participant {
        self.native.attestation.signer
    }
}

/// Raw general original final pair, using its unchanged G1V1 inner frame.
#[derive(Clone, Debug)]
pub struct FinalVote<S: Scheme, D: Digest>(g::normal::Vote<S, D>);
impl<S: Scheme, D: Digest> FinalVote<S, D> {
    /// Wraps raw data without granting authentication or admission.
    pub const fn new(vote: g::normal::Vote<S, D>) -> Self {
        Self(vote)
    }
    /// Complete exact signed pair, including its untrusted retrieval hint.
    pub const fn inner(&self) -> &g::normal::Vote<S, D> {
        &self.0
    }
    /// Moves the unchanged original pair.
    pub fn into_inner(self) -> g::normal::Vote<S, D> {
        self.0
    }
}
impl<S: Scheme, D: Digest> PartialEq for FinalVote<S, D> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
impl<S: Scheme, D: Digest> Eq for FinalVote<S, D> {}
impl<S: Scheme, D: Digest> Write for FinalVote<S, D> {
    fn write(&self, writer: &mut impl BufMut) {
        self.0.write(writer);
    }
}
impl<S: Scheme, D: Digest> EncodeSize for FinalVote<S, D> {
    fn encode_size(&self) -> usize {
        self.0.encode_size()
    }
}
impl<S: Scheme, D: Digest> Read for FinalVote<S, D> {
    type Cfg = ();
    fn read_cfg(reader: &mut impl Buf, _: &()) -> Result<Self, Error> {
        g::normal::Vote::read_cfg(reader, &WIRE_LIMITS).map(Self)
    }
}
impl<S: Scheme, D: Digest> Epochable for FinalVote<S, D> {
    fn epoch(&self) -> Epoch {
        self.0.native.statement.proposal.epoch()
    }
}
impl<S: Scheme, D: Digest> Viewable for FinalVote<S, D> {
    fn view(&self) -> View {
        self.0.native.statement.proposal.view()
    }
}
impl<S: Scheme, D: Digest> Attributable for FinalVote<S, D> {
    fn signer(&self) -> Participant {
        self.0.native.attestation.signer
    }
}

/// Raw complete original certificate, using its unchanged G1C1 inner frame.
#[derive(Clone, Debug)]
pub struct Finalization<S: Scheme, D: Digest>(g::normal::Certificate<S, D>);
impl<S: Scheme, D: Digest> Finalization<S, D> {
    /// Wraps raw data without granting authentication or application admission.
    pub const fn new(certificate: g::normal::Certificate<S, D>) -> Self {
        Self(certificate)
    }
    /// Complete witness and both final QCs, retaining the original NQC.
    pub const fn inner(&self) -> &g::normal::Certificate<S, D> {
        &self.0
    }
    /// Moves the unchanged certificate and exact evidence.
    pub fn into_inner(self) -> g::normal::Certificate<S, D> {
        self.0
    }
}
impl<S: Scheme, D: Digest> PartialEq for Finalization<S, D> {
    fn eq(&self, other: &Self) -> bool {
        let (a, b) = (&self.0, &other.0);
        a.native.statement == b.native.statement
            && a.native.certificate == b.native.certificate
            && a.agreement.message == b.agreement.message
            && a.agreement.certificate == b.agreement.certificate
            && a.notarization.proposal == b.notarization.proposal
            && a.notarization.certificate == b.notarization.certificate
            && same_origin(&a.origin, &b.origin)
    }
}
fn same_signed<S: Scheme, D: Digest>(a: &g::Signed<S, D>, b: &g::Signed<S, D>) -> bool {
    a.message == b.message && a.attestation == b.attestation
}
fn same_origin<S: Scheme, D: Digest>(a: &g::Origin<S, D>, b: &g::Origin<S, D>) -> bool {
    let (a_body, b_body) = (&a.body, &b.body);
    a_body.decision == b_body.decision
        && a_body.core == b_body.core
        && a_body.population == b_body.population
        && a_body.build == b_body.build
        && a_body.material == b_body.material
        && a_body.firsts.len() == b_body.firsts.len()
        && a_body
            .firsts
            .iter()
            .zip(&b_body.firsts)
            .all(|(a, b)| same_signed(a, b))
        && same_signed(&a.selection, &b.selection)
}
impl<S: Scheme, D: Digest> Eq for Finalization<S, D> {}
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
        g::normal::Certificate::read_cfg(reader, &(WIRE_LIMITS, cfg.clone())).map(Self)
    }
}
impl<S: Scheme, D: Digest> Epochable for Finalization<S, D> {
    fn epoch(&self) -> Epoch {
        self.0.native.statement.proposal.epoch()
    }
}
impl<S: Scheme, D: Digest> Viewable for Finalization<S, D> {
    fn view(&self) -> View {
        self.0.native.statement.proposal.view()
    }
}

/// Original-only G1 representation. Its native-owned Voting adapter requires
/// checked deployment material; no later-ballot recovery or host is activated.
pub struct General<H>(PhantomData<fn() -> H>);
impl<H> Clone for General<H> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<H> Copy for General<H> {}
impl<H> Default for General<H> {
    fn default() -> Self {
        Self(PhantomData)
    }
}
impl<H> fmt::Debug for General<H> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("General")
    }
}
impl<H> PartialEq for General<H> {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl<H> Eq for General<H> {}
impl<H> sealed::Sealed for General<H> {}
impl<S, D, H> Mode<S, D> for General<H>
where
    S: scheme::Scheme<D>,
    S::Certificate: g::normal::CertificateSigners,
    D: Digest,
    H: Hasher<Digest = D>,
{
    const RETAIN_INTERPRETATION: bool = true;
    const ASSEMBLY_BUDGET: usize = g::MAX_EVIDENCE_BYTES + 64 * 1024;
    type Assembly = g::normal::Assembly<S, D>;
    fn assembly_proposal(assembly: &Self::Assembly) -> &Proposal<D> {
        assembly.proposal()
    }
    fn assembly_size(assembly: &Self::Assembly) -> usize {
        assembly.retained_bytes()
    }
    fn equivalent_assembly(a: &Self::Assembly, b: &Self::Assembly) -> bool {
        a.core() == b.core() && a.decision() == b.decision()
    }
    type Recovery = voting_wal::Wal<S, D>;
    type Recovered = recovery::NoRecovery;
    type RecoveryQuery = recovery::NoRecovery;
    #[cfg(not(target_arch = "wasm32"))]
    type RecoveryRequest = voting::SelectRequest<D>;
    #[cfg(target_arch = "wasm32")]
    type RecoveryRequest = recovery::NoRecovery;
    type RecoveryResponse = g::Signed<S, D>;
    fn read_recovered(
        _: &mut impl Buf,
        _: &<S::Certificate as Read>::Cfg,
    ) -> Result<Self::Recovered, Error> {
        Err(Error::Invalid("G1 original mode", "recovery disabled"))
    }
    fn recovered_proposal(value: &Self::Recovered) -> &Proposal<D> {
        match *value {}
    }
    fn verify_recovered<R: CryptoRng>(
        value: &Self::Recovered,
        _: &mut R,
        _: &S,
        _: &impl Strategy,
    ) -> bool {
        match *value {}
    }
    fn recovery_query_view(value: &Self::RecoveryQuery) -> View {
        match *value {}
    }
    fn recovery_view(value: &Self::RecoveryRequest) -> View {
        #[cfg(not(target_arch = "wasm32"))]
        {
            value.view()
        }
        #[cfg(target_arch = "wasm32")]
        {
            match *value {}
        }
    }
    type Notarize = FirstVote<S, D>;
    type Vote = FinalVote<S, D>;
    type Certificate = Finalization<S, D>;
    fn notarize(vote: &Self::Notarize) -> &Notarize<S, D> {
        vote.native()
    }
    fn into_notarize(vote: Self::Notarize) -> Notarize<S, D> {
        vote.into_parts().0
    }
    fn finalize_proposal(vote: &Self::Vote) -> &Proposal<D> {
        &vote.inner().native.statement.proposal
    }
    fn finalization_proposal(certificate: &Self::Certificate) -> &Proposal<D> {
        &certificate.inner().native.statement.proposal
    }
    fn finalization_certificate(certificate: &Self::Certificate) -> &S::Certificate {
        &certificate.inner().native.certificate
    }
    fn finalization_election_certificate(certificate: &Self::Certificate) -> &S::Certificate {
        &certificate.inner().notarization.certificate
    }
    fn signed_finalization_subject(certificate: &Self::Certificate) -> Subject<'_, D> {
        Subject::FinalizeExtension {
            statement: &certificate.inner().native.statement,
        }
    }
    fn verify_companion<R: CryptoRng>(
        certificate: &Self::Certificate,
        rng: &mut R,
        scoped: &Scoped<S>,
        strategy: &impl Strategy,
    ) -> bool {
        certificate
            .inner()
            .authenticate_scoped::<H, R>(rng, scoped, WIRE_LIMITS, strategy)
            .is_ok()
    }
    fn conflicting_finalize_subjects(a: &Self::Vote, b: &Self::Vote) -> bool {
        a.inner().native.statement.domain == b.inner().native.statement.domain
            && (a.inner().native.statement != b.inner().native.statement
                || a.inner().agreement.message != b.inner().agreement.message)
    }
    fn equivalent_finalize(a: &Self::Vote, b: &Self::Vote) -> bool {
        a.inner().same_signed_pair(b.inner())
    }
    fn verify_finalize<R: CryptoRng>(
        vote: &Self::Vote,
        rng: &mut R,
        scheme: &S,
        strategy: &impl Strategy,
    ) -> bool {
        vote.inner()
            .authenticate::<H, R>(rng, scheme, WIRE_LIMITS, strategy)
            .is_ok()
    }
    fn verify<R: CryptoRng>(
        certificate: &Self::Certificate,
        rng: &mut R,
        scheme: &S,
        strategy: &impl Strategy,
    ) -> bool {
        certificate
            .inner()
            .authenticate::<H, R>(rng, scheme, WIRE_LIMITS, strategy)
            .is_ok()
    }
}

#[cfg(feature = "arbitrary")]
mod arbitrary_impl {
    use super::*;
    use bytes::Bytes;
    use commonware_cryptography::certificate::Attestation;

    fn blob(u: &mut arbitrary::Unstructured<'_>) -> arbitrary::Result<Bytes> {
        let length = u.int_in_range(0..=u.len().min(256))?;
        Ok(Bytes::copy_from_slice(u.bytes(length)?))
    }

    fn signed<S: Scheme, D: Digest>(
        u: &mut arbitrary::Unstructured<'_>,
        kind: g::Kind<D>,
    ) -> arbitrary::Result<g::Signed<S, D>>
    where
        S::Signature: for<'a> arbitrary::Arbitrary<'a>,
        D: for<'a> arbitrary::Arbitrary<'a>,
    {
        Ok(g::Signed {
            message: g::Message {
                slot: u.arbitrary()?,
                round: u.arbitrary()?,
                leader: Participant::new(u.int_in_range(0..=63)?),
                kind,
            },
            attestation: Attestation {
                signer: Participant::new(u.int_in_range(0..=63)?),
                signature: u.arbitrary::<S::Signature>()?.into(),
            },
        })
    }

    fn first<S: Scheme, D: Digest>(
        u: &mut arbitrary::Unstructured<'_>,
    ) -> arbitrary::Result<g::Signed<S, D>>
    where
        S::Signature: for<'a> arbitrary::Arbitrary<'a>,
        D: for<'a> arbitrary::Arbitrary<'a>,
    {
        let row = g::First {
            core: u.arbitrary()?,
            input: u.arbitrary()?,
            owner: Participant::new(u.int_in_range(0..=63)?),
            report: if u.arbitrary()? { Some(blob(u)?) } else { None },
            preference: if u.arbitrary()? { Some(blob(u)?) } else { None },
        };
        signed(u, g::Kind::First(row))
    }

    fn phase<D: Digest>(u: &mut arbitrary::Unstructured<'_>) -> arbitrary::Result<g::Kind<D>>
    where
        D: for<'a> arbitrary::Arbitrary<'a>,
    {
        Ok(g::Kind::Phase {
            phase: g::Phase::FastFinal,
            decision: u.arbitrary()?,
        })
    }

    // These bounded codec values have arbitrary signatures and no authority.
    impl<S: Scheme, D: Digest> arbitrary::Arbitrary<'_> for FirstVote<S, D>
    where
        S::Signature: for<'a> arbitrary::Arbitrary<'a>,
        D: for<'a> arbitrary::Arbitrary<'a>,
    {
        fn arbitrary(u: &mut arbitrary::Unstructured<'_>) -> arbitrary::Result<Self> {
            let value = Self::new(
                u.arbitrary()?,
                if u.arbitrary()? {
                    Some(first(u)?)
                } else {
                    None
                },
            );
            if value.native.encode_size() > MAX_NATIVE_VOTE_BYTES
                || value.encode_size() > MAX_FIRST_VOTE_BYTES
            {
                return Err(arbitrary::Error::IncorrectFormat);
            }
            Ok(value)
        }
    }

    impl<S: Scheme, D: Digest> arbitrary::Arbitrary<'_> for FinalVote<S, D>
    where
        S::Signature: for<'a> arbitrary::Arbitrary<'a>,
        D: for<'a> arbitrary::Arbitrary<'a>,
    {
        fn arbitrary(u: &mut arbitrary::Unstructured<'_>) -> arbitrary::Result<Self> {
            let kind = phase(u)?;
            let value = Self::new(g::normal::Vote {
                native: u.arbitrary()?,
                agreement: signed(u, kind)?,
                origin_hint: u.arbitrary()?,
            });
            if value.inner().native.encode_size() > MAX_NATIVE_VOTE_BYTES
                || value.encode_size() > g::MAX_EVIDENCE_BYTES
            {
                return Err(arbitrary::Error::IncorrectFormat);
            }
            Ok(value)
        }
    }

    impl<S: Scheme, D: Digest> arbitrary::Arbitrary<'_> for Finalization<S, D>
    where
        S::Signature: for<'a> arbitrary::Arbitrary<'a>,
        S::Certificate: for<'a> arbitrary::Arbitrary<'a>,
        D: for<'a> arbitrary::Arbitrary<'a>,
    {
        fn arbitrary(u: &mut arbitrary::Unstructured<'_>) -> arbitrary::Result<Self> {
            let slot = g::Slot {
                profile: u.arbitrary()?,
                domain: u.arbitrary()?,
                roster: u.arbitrary()?,
                cut: u.arbitrary()?,
                proposal: u.arbitrary()?,
                parent: g::NativeParent::Genesis(u.arbitrary()?),
            };
            let leader = Participant::new(u.int_in_range(0..=63)?);
            let followers = (0..64)
                .map(Participant::new)
                .filter(|owner| *owner != leader)
                .take(2)
                .collect();
            let kind = g::Kind::Select {
                body: u.arbitrary()?,
                decision: u.arbitrary()?,
            };
            let origin = g::Origin {
                body: g::OriginBody {
                    decision: g::Decision {
                        slot: slot.clone(),
                        input: u.arbitrary()?,
                        order: blob(u)?,
                    },
                    core: g::Core {
                        slot,
                        leader,
                        followers,
                    },
                    firsts: (0..3).map(|_| first(u)).collect::<arbitrary::Result<_>>()?,
                    population: u.arbitrary()?,
                    build: blob(u)?,
                    material: blob(u)?,
                },
                selection: signed(u, kind)?,
            };
            let kind = phase(u)?;
            let value = Self::new(g::normal::Certificate {
                native: u.arbitrary()?,
                agreement: g::Quorum {
                    message: signed::<S, D>(u, kind)?.message,
                    certificate: u.arbitrary()?,
                },
                notarization: u.arbitrary()?,
                origin,
            });
            if value.inner().native.encode_size() > MAX_NATIVE_VOTE_BYTES
                || value.inner().notarization.encode_size() > MAX_NATIVE_VOTE_BYTES
                || value.encode_size() > g::MAX_EVIDENCE_BYTES
            {
                return Err(arbitrary::Error::IncorrectFormat);
            }
            // Generic certificate generators can emit codec-invalid values,
            // including empty signer sets. Filter local generated bytes only.
            let cfg = <S as commonware_cryptography::certificate::Verifier>::certificate_codec_config_unbounded();
            <Self as commonware_codec::Decode>::decode_cfg(
                commonware_codec::Encode::encode(&value),
                &cfg,
            )
            .map_err(|_| arbitrary::Error::IncorrectFormat)
        }
    }
}

#[cfg(test)]
#[path = "general_tests.rs"]
pub(crate) mod tests;
