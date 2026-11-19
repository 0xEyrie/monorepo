//! Genuine original-round native/G1 pairs. Native admission, custody and WAL
//! synchronization remain owned by the voter; a checked pair is not delivery.

use super::{
    Core, Decision, Error, First, Frame, Kind, Limits, Message, NativeParent, Origin, OriginBody,
    Phase, Quorum, Signed, VerificationSource, VerifiedRows, bounded,
    issuance::{Action, Record},
    native_size, read_blob, read_native, write_native,
};
use crate::{
    Epochable, Viewable,
    simplex::{
        extension::vote,
        scheme,
        types::{Notarization, Subject},
    },
    types::{Epoch, View},
};
use bytes::{Buf as _, BufMut};
use commonware_codec::{Buf, EncodeSize, Error as CodecError, Read, ReadExt as _, Write};
use commonware_cryptography::{
    Digest, Hasher,
    certificate::{self, Scoped},
};
use commonware_parallel::Strategy;
use commonware_utils::iter::NonEmpty;
use rand_core::CryptoRng;
use std::collections::BTreeSet;

commonware_macros::stability_mod!(ALPHA, pub mod signers);
pub use signers::CertificateSigners;
commonware_macros::stability_mod!(ALPHA, pub mod assembly);
pub use assembly::Assembly;

const PARENT: &[u8] = b"_COMMONWARE_CONSENSUS_G1_NATIVE_PARENT_V1";

/// Commits the tagged native anchor, not a parent execution interpretation.
pub fn native_parent<H: Hasher>(parent: &NativeParent<H::Digest>) -> H::Digest {
    let mut bytes = Vec::new();
    parent.write(&mut bytes);
    H::hash(&[PARENT, &bytes])
}

/// Maps the complete semantic decision into the genuine native signing role.
pub fn subject<H: Hasher>(decision: &Decision<H::Digest>) -> vote::Statement<H::Digest> {
    vote::Statement {
        proposal: decision.slot.proposal.clone(),
        domain: decision.slot.domain,
        ballot: decision.slot.proposal.round,
        parent: native_parent::<H>(&decision.slot.parent),
        extension: decision.id::<H>(),
    }
}

fn message<H: Hasher>(core: &Core<H::Digest>, decision: H::Digest) -> Message<H::Digest> {
    Message {
        slot: core.slot.id::<H>(),
        round: core.slot.proposal.round,
        leader: core.leader,
        kind: Kind::Phase {
            phase: Phase::FastFinal,
            decision,
        },
    }
}

/// One native-journal item authorizing both unsigned original final subjects.
/// The embedded record retains the exact own origin, including on alias retry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reservation<D: Digest> {
    pub(super) subject: vote::Statement<D>,
    pub(super) agreement: Record<D>,
}
impl<D: Digest> Reservation<D> {
    /// Exact native original final subject.
    pub const fn subject(&self) -> &vote::Statement<D> {
        &self.subject
    }
    /// G1 reservation included in every subsequent complete signing history.
    pub const fn agreement(&self) -> &Record<D> {
        &self.agreement
    }
    pub(super) fn check<H: Hasher<Digest = D>>(&self) -> Result<(), Error> {
        let Action::Reserve {
            message: m,
            authority: Some(_),
        } = self.agreement.action()
        else {
            return Err(Error::Context);
        };
        let Kind::Phase {
            phase: Phase::FastFinal,
            decision,
        } = m.kind
        else {
            return Err(Error::Phase);
        };
        let slot = self.agreement.slot();
        if m != &message::<H>(self.agreement.core(), decision)
            || self.subject.proposal != slot.proposal
            || self.subject.domain != slot.domain
            || self.subject.ballot != slot.proposal.round
            || self.subject.parent != native_parent::<H>(&slot.parent)
            || self.subject.extension != decision
        {
            return Err(Error::Context);
        }
        Ok(())
    }
}
impl<D: Digest> Epochable for Reservation<D> {
    fn epoch(&self) -> Epoch {
        self.agreement.epoch()
    }
}
impl<D: Digest> Viewable for Reservation<D> {
    fn view(&self) -> View {
        self.agreement.view()
    }
}
impl<D: Digest> Frame for Reservation<D> {
    const MAGIC: [u8; 4] = *b"G1G1";
    type Cfg = Limits;
    fn body_size(&self) -> usize {
        native_size(&self.subject) + self.agreement.encode_size()
    }
    fn write_body(&self, w: &mut impl BufMut) {
        write_native(&self.subject, w);
        self.agreement.write(w);
    }
    fn read_body(r: &mut impl Buf, l: &Limits) -> Result<Self, CodecError> {
        Ok(Self {
            subject: read_native(r)?,
            agreement: Record::read_cfg(r, l)?,
        })
    }
}
frame_codec!(Reservation<D>, [D: Digest], Limits);

/// Two exact-subject attestations by one owner. The hint is unauthenticated
/// retrieval metadata; it proves neither signing provenance nor origin custody.
#[derive(Clone, Debug)]
pub struct Vote<S: certificate::Scheme, D: Digest> {
    /// Genuine native FinalizeExtension attestation.
    pub native: vote::Vote<S, D>,
    /// Genuine G1 FAST_FINAL attestation from that same owner.
    pub agreement: Signed<S, D>,
    /// Optional retrieval location represented by an origin content address.
    pub origin_hint: D,
}
impl<S: certificate::Scheme, D: Digest> Vote<S, D> {
    /// Compares both exact signed envelopes while ignoring retrieval metadata.
    /// This performs no authentication and grants no new signer credit. Local
    /// outbox/replay equality still compares the complete original envelope.
    pub fn same_signed_pair(&self, other: &Self) -> bool {
        self.native.statement == other.native.statement
            && self.native.attestation == other.native.attestation
            && self.agreement.message == other.agreement.message
            && self.agreement.attestation == other.agreement.attestation
    }
}
impl<S: scheme::Scheme<D>, D: Digest> Vote<S, D> {
    /// Authenticates the two observable signed roles and their shared owner and
    /// Decision ID. No complete Origin, trusted context or application meaning
    /// is established, and the retrieval hint supplies no authority.
    pub fn authenticate<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &S,
        limits: Limits,
        strategy: &impl Strategy,
    ) -> Result<(), Error> {
        self.authenticate_with::<H, R>(rng, &VerificationSource::Scheme(s), limits, strategy)
    }
    /// Same pair authentication without exposing a signing scope.
    pub fn authenticate_scoped<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &Scoped<S>,
        limits: Limits,
        strategy: &impl Strategy,
    ) -> Result<(), Error> {
        self.authenticate_with::<H, R>(rng, &VerificationSource::Scoped(s), limits, strategy)
    }
    fn authenticate_with<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &VerificationSource<'_, S>,
        limits: Limits,
        strategy: &impl Strategy,
    ) -> Result<(), Error> {
        limits.check()?;
        let c = super::committee::<S>(s)?;
        let Kind::Phase {
            phase: Phase::FastFinal,
            decision,
        } = &self.agreement.message.kind
        else {
            return Err(Error::Phase);
        };
        self.agreement.message.check(c, limits)?;
        if self.native.encode_size() > super::NATIVE_BYTES
            || self.agreement.encode_size() > super::MAX_FIRST_BYTES
        {
            return Err(Error::Limit);
        }
        if <H::Digest as commonware_codec::FixedSize>::SIZE != 32
            || self.native.statement.ballot != self.native.statement.proposal.round
            || self.agreement.message.round != self.native.statement.proposal.round
            || self.native.statement.extension != *decision
            || self.native.attestation.signer != self.agreement.attestation.signer
        {
            return Err(Error::Context);
        }
        if !self.native.statement.valid_ballot()
            || !s.verify_attestation::<_, D>(
                rng,
                Subject::FinalizeExtension {
                    statement: &self.native.statement,
                },
                &self.native.attestation,
                strategy,
            )
            || !self.agreement.verify_with(rng, s, limits, strategy)
        {
            return Err(Error::Signature);
        }
        Ok(())
    }
    /// Checks the pair's crypto and exact subjects. The caller must separately
    /// verify a full same-decision Origin and native P admission.
    #[allow(clippy::too_many_arguments)]
    pub fn verify<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &S,
        core: &Core<D>,
        input: D,
        decision: &Decision<D>,
        limits: Limits,
        strategy: &impl Strategy,
    ) -> bool {
        core.check::<H, S>(&VerificationSource::Scheme(s)).is_ok()
            && decision.slot == core.slot
            && decision.input == input
            && decision.order.len() <= limits.order_bytes
            && self.native.statement == subject::<H>(decision)
            && self.agreement.message == message::<H>(core, decision.id::<H>())
            && self
                .authenticate_with::<H, R>(rng, &VerificationSource::Scheme(s), limits, strategy)
                .is_ok()
    }
}
impl<S: certificate::Scheme, D: Digest> PartialEq for Vote<S, D> {
    fn eq(&self, other: &Self) -> bool {
        self.same_signed_pair(other) && self.origin_hint == other.origin_hint
    }
}
impl<S: certificate::Scheme, D: Digest> Eq for Vote<S, D> {}
impl<S: certificate::Scheme, D: Digest> Frame for Vote<S, D> {
    const MAGIC: [u8; 4] = *b"G1V1";
    type Cfg = Limits;
    fn body_size(&self) -> usize {
        native_size(&self.native) + self.agreement.encode_size() + self.origin_hint.encode_size()
    }
    fn write_body(&self, w: &mut impl BufMut) {
        write_native(&self.native, w);
        self.agreement.write(w);
        self.origin_hint.write(w);
    }
    fn read_body(r: &mut impl Buf, l: &Limits) -> Result<Self, CodecError> {
        Ok(Self {
            native: read_native(r)?,
            agreement: Signed::read_cfg(r, l)?,
            origin_hint: D::read(r)?,
        })
    }
}
frame_codec!(Vote<S, D>, [S: certificate::Scheme, D: Digest], Limits);

/// Exact paired outbox plus its G1 receipt. The native owner journals this whole
/// object, synchronizes it and restores it before publishing or retransmitting.
#[derive(Clone, Debug)]
pub struct Released<S: certificate::Scheme, D: Digest> {
    pub(super) reservation: Reservation<D>,
    pub(super) receipt: Record<D>,
    pub(super) vote: Vote<S, D>,
}
impl<S: certificate::Scheme, D: Digest> Released<S, D> {
    /// Original joint unsigned authorization, never replaced by an alias.
    pub const fn reservation(&self) -> &Reservation<D> {
        &self.reservation
    }
    /// Agreement signed-outbox receipt included in complete G1 history.
    pub const fn receipt(&self) -> &Record<D> {
        &self.receipt
    }
    /// Complete originally emitted pair, including its exact hint bytes.
    pub const fn vote(&self) -> &Vote<S, D> {
        &self.vote
    }
}
impl<S: certificate::Scheme, D: Digest> PartialEq for Released<S, D> {
    fn eq(&self, other: &Self) -> bool {
        self.reservation == other.reservation
            && self.receipt == other.receipt
            && self.vote == other.vote
    }
}
impl<S: certificate::Scheme, D: Digest> Eq for Released<S, D> {}
impl<S: certificate::Scheme, D: Digest> Frame for Released<S, D> {
    const MAGIC: [u8; 4] = *b"G1X1";
    type Cfg = Limits;
    fn body_size(&self) -> usize {
        self.reservation.encode_size() + self.receipt.encode_size() + self.vote.encode_size()
    }
    fn write_body(&self, w: &mut impl BufMut) {
        self.reservation.write(w);
        self.receipt.write(w);
        self.vote.write(w);
    }
    fn read_body(r: &mut impl Buf, l: &Limits) -> Result<Self, CodecError> {
        Ok(Self {
            reservation: Reservation::read_cfg(r, l)?,
            receipt: Record::read_cfg(r, l)?,
            vote: Vote::read_cfg(r, l)?,
        })
    }
}
frame_codec!(Released<S, D>, [S: certificate::Scheme, D: Digest], Limits);

/// Both original final QCs plus a full decision witness and genuine original
/// NQC. The latter supplies the unchanged native successor-election seed.
#[derive(Clone, Debug)]
pub struct Certificate<S: certificate::Scheme, D: Digest> {
    /// Genuine native exact-P+D final certificate.
    pub native: vote::Certificate<S, D>,
    /// G1 quorum under the separate original-final role.
    pub agreement: Quorum<S, D>,
    /// Exact original proposal's genuine native first-phase certificate.
    pub notarization: Notarization<S, D>,
    /// One complete external same-decision witness, not per-signer provenance.
    pub origin: Origin<S, D>,
}
impl<S: scheme::Scheme<D>, D: Digest> Certificate<S, D>
where
    S::Certificate: CertificateSigners,
{
    /// Authenticates the complete claimed Origin, two exact-q owner-matched QCs
    /// and original NQC. Trusted Core/Input, application policy and native P
    /// admission are not established. Success creates no signing or delivery
    /// capability and cannot replace full application verification.
    pub fn authenticate<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &S,
        limits: Limits,
        strategy: &impl Strategy,
    ) -> Result<(), Error> {
        self.authenticate_with::<H, R>(rng, &VerificationSource::Scheme(s), limits, strategy)
    }
    /// Same complete wire authentication through a public-only epoch scope.
    pub fn authenticate_scoped<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &Scoped<S>,
        limits: Limits,
        strategy: &impl Strategy,
    ) -> Result<(), Error> {
        self.authenticate_with::<H, R>(rng, &VerificationSource::Scoped(s), limits, strategy)
    }
    fn authenticate_with<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &VerificationSource<'_, S>,
        limits: Limits,
        strategy: &impl Strategy,
    ) -> Result<(), Error> {
        let c = super::committee::<S>(s)?;
        self.origin.preflight(c, limits)?;
        if !matches!(
            &self.agreement.message.kind,
            Kind::Phase {
                phase: Phase::FastFinal,
                ..
            }
        ) {
            return Err(Error::Phase);
        }
        self.agreement.message.check(c, limits)?;
        if self.native.certificate.signers().len() > 64
            || self.agreement.certificate.signers().len() > 64
            || self.native.encode_size() > super::NATIVE_BYTES
            || self.notarization.encode_size() > super::NATIVE_BYTES
        {
            return Err(Error::Limit);
        }
        bounded(self)?;
        let body = &self.origin.body;
        if let Some(Kind::First(row)) = body.firsts.first().map(|first| &first.message.kind)
            && row.core != body.core.id::<H>()
        {
            // Wire authentication of an already paired final quorum. A signer or
            // application consumer still needs local policy replay for this scope.
            let empty = First::empty_route_scope::<H>(
                &body.core.slot,
                body.core.leader,
                body.decision.input,
            );
            let scope = body
                .firsts
                .iter()
                .find_map(|s| match &s.message.kind {
                    Kind::First(r) if r.core != empty => Some(r.core),
                    _ => None,
                })
                .unwrap_or(empty);
            body.authenticate_route_rows::<H, R>(
                rng,
                s,
                &body.core,
                body.decision.input,
                scope,
                limits,
                strategy,
            )?;
            self.origin
                .check_selection::<H, R>(rng, s, &body.core, limits, strategy)?;
        } else {
            self.origin
                .authenticate_with::<H, R>(rng, s, limits, strategy)?;
        }
        self.check_certificates::<H, R>(rng, s, &self.origin.body.core, c, limits, strategy)
    }
    /// Validates a full origin, both QCs' identical q-owner populations and the
    /// native NQC. Trusted expected context and application callbacks are required.
    #[allow(clippy::too_many_arguments)]
    pub fn verify<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &S,
        core: &Core<D>,
        input: D,
        limits: Limits,
        validate_row: impl FnMut(&First<D>) -> bool,
        validate_build: impl FnOnce(&VerifiedRows<S, D>, &OriginBody<S, D>) -> bool,
        strategy: &impl Strategy,
    ) -> Result<(), Error> {
        self.verify_with::<H, R>(
            rng,
            &VerificationSource::Scheme(s),
            core,
            input,
            limits,
            validate_row,
            validate_build,
            strategy,
        )
    }
    /// Same validation without exposing a signer or requiring a signing scope.
    #[allow(clippy::too_many_arguments)]
    pub fn verify_scoped<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &Scoped<S>,
        core: &Core<D>,
        input: D,
        limits: Limits,
        validate_row: impl FnMut(&First<D>) -> bool,
        validate_build: impl FnOnce(&VerifiedRows<S, D>, &OriginBody<S, D>) -> bool,
        strategy: &impl Strategy,
    ) -> Result<(), Error> {
        self.verify_with::<H, R>(
            rng,
            &VerificationSource::Scoped(s),
            core,
            input,
            limits,
            validate_row,
            validate_build,
            strategy,
        )
    }
    #[allow(clippy::too_many_arguments)]
    fn verify_with<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &VerificationSource<'_, S>,
        core: &Core<D>,
        input: D,
        limits: Limits,
        validate_row: impl FnMut(&First<D>) -> bool,
        validate_build: impl FnOnce(&VerifiedRows<S, D>, &OriginBody<S, D>) -> bool,
        strategy: &impl Strategy,
    ) -> Result<(), Error> {
        bounded(self)?;
        let committee = core.check::<H, S>(s)?;
        self.origin.verify_with::<H, R>(
            rng,
            s,
            core,
            input,
            limits,
            validate_row,
            validate_build,
            strategy,
        )?;
        self.check_certificates::<H, R>(rng, s, core, committee, limits, strategy)
    }
    #[allow(clippy::too_many_arguments)]
    fn check_certificates<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &VerificationSource<'_, S>,
        core: &Core<D>,
        committee: super::Committee,
        limits: Limits,
        strategy: &impl Strategy,
    ) -> Result<(), Error> {
        if self.native.statement != subject::<H>(&self.origin.body.decision)
            || self.agreement.message != message::<H>(core, self.origin.body.decision.id::<H>())
            || self.notarization.proposal != core.slot.proposal
        {
            return Err(Error::Context);
        }
        if !s.verify_certificate::<_, D>(
            rng,
            Subject::FinalizeExtension {
                statement: &self.native.statement,
            },
            &self.native.certificate,
            strategy,
        ) || !self.agreement.verify_with(rng, s, limits, strategy)
            || !s.verify_certificate::<_, D>(
                rng,
                Subject::Notarize {
                    proposal: &self.notarization.proposal,
                },
                &self.notarization.certificate,
                strategy,
            )
        {
            return Err(Error::Signature);
        }
        let native = self.native.certificate.signers();
        let agreement = self.agreement.certificate.signers();
        if native.len() != committee.len()
            || agreement.len() != committee.len()
            || native.count() != committee.quorum()
            || agreement.count() != committee.quorum()
            || native != agreement
        {
            return Err(Error::Identity);
        }
        Ok(())
    }

    /// Assembles exactly q distinct complete pairs. Same-decision origin hints
    /// may differ; they never replace the supplied full external witness.
    #[allow(clippy::too_many_arguments)]
    pub fn assemble<H: Hasher<Digest = D>, R: CryptoRng>(
        rng: &mut R,
        s: &S,
        core: &Core<D>,
        input: D,
        origin: &Origin<S, D>,
        notarization: &Notarization<S, D>,
        votes: &[Vote<S, D>],
        limits: Limits,
        validate_row: impl FnMut(&First<D>) -> bool,
        validate_build: impl FnOnce(&VerifiedRows<S, D>, &OriginBody<S, D>) -> bool,
        strategy: &impl Strategy,
    ) -> Result<Self, Error> {
        let committee = core.check::<H, S>(&VerificationSource::Scheme(s))?;
        limits.check()?;
        // Reject raw cardinality and field bounds before traversing envelopes
        // or identifying the Decision while checking the supplied pairs.
        origin.preflight(committee, limits)?;
        bounded(origin)?;
        if origin.encode_size() > limits.origin_bytes
            || origin.body.decision.order.len() > limits.order_bytes
            || origin.body.build.len() > limits.build_bytes
            || origin.body.material.len() > limits.material_bytes
            || notarization.encode_size() > super::NATIVE_BYTES
        {
            return Err(Error::Limit);
        }
        if votes.len() != committee.quorum() {
            return Err(Error::Quorum);
        }
        let mut owners = BTreeSet::new();
        for v in votes {
            if !owners.insert(v.native.attestation.signer) {
                return Err(Error::Identity);
            }
            if !v.verify::<H, R>(rng, s, core, input, &origin.body.decision, limits, strategy) {
                return Err(Error::Signature);
            }
        }
        let mut native = votes.iter().map(|v| v.native.clone());
        let native = vote::Certificate::from_votes(
            rng,
            s,
            NonEmpty::new(native.next().ok_or(Error::Quorum)?, native),
            strategy,
        )
        .map_err(|_| Error::Signature)?;
        let agreement = Quorum::from_votes(
            rng,
            s,
            &votes
                .iter()
                .map(|v| v.agreement.clone())
                .collect::<Vec<_>>(),
            limits,
            strategy,
        )?;
        let result = Self {
            native,
            agreement,
            notarization: notarization.clone(),
            origin: origin.clone(),
        };
        result.verify::<H, R>(
            rng,
            s,
            core,
            input,
            limits,
            validate_row,
            validate_build,
            strategy,
        )?;
        Ok(result)
    }
}
impl<S: certificate::Scheme, D: Digest> Frame for Certificate<S, D> {
    const MAGIC: [u8; 4] = *b"G1C1";
    type Cfg = (Limits, <S::Certificate as Read>::Cfg);
    fn body_size(&self) -> usize {
        native_size(&self.native)
            + self.agreement.encode_size()
            + native_size(&self.notarization)
            + self.origin.encode_size()
    }
    fn write_body(&self, w: &mut impl BufMut) {
        write_native(&self.native, w);
        self.agreement.write(w);
        write_native(&self.notarization, w);
        self.origin.write(w);
    }
    fn read_body(r: &mut impl Buf, cfg: &Self::Cfg) -> Result<Self, CodecError> {
        let native_bytes = super::read_blob(r, super::NATIVE_BYTES)?;
        let native = <vote::Certificate<S, D> as commonware_codec::Decode>::decode_cfg(
            native_bytes,
            &cfg.1,
        )?;
        let agreement = Quorum::read_cfg(r, cfg)?;
        let native_bytes = super::read_blob(r, super::NATIVE_BYTES)?;
        let notarization =
            <Notarization<S, D> as commonware_codec::Decode>::decode_cfg(native_bytes, &cfg.1)?;
        Ok(Self {
            native,
            agreement,
            notarization,
            origin: Origin::read_cfg(r, &cfg.0)?,
        })
    }
}
frame_codec!(Certificate<S, D>, [S: certificate::Scheme, D: Digest], (Limits, <S::Certificate as Read>::Cfg));
