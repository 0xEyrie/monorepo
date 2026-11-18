//! Private receipt-aware recovery fixture, not General mode or a recovery policy.
use super::*;
use crate::{
    simplex::{
        extension::recovery::{Promise, Status},
        scheme::ed25519,
    },
    types::{Epoch, View},
};
use bytes::{Buf as _, BufMut, Bytes};
use commonware_codec::{Buf, DecodeExt as _, Encode as _, ReadExt as _};
use commonware_cryptography::sha256::Digest as D;
use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};
type S = ed25519::Scheme;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct RecoveryProbe;
impl sealed::Sealed for RecoveryProbe {}

#[derive(Clone)]
pub(crate) struct RecoveryContext {
    pub domain: D,
    pub signed: Arc<AtomicUsize>,
    // Test-only I/O control, armed after the genuine response is staged.
    pub release_gate: Option<commonware_runtime::mocks::PendingSyncs>,
}
/// 0 reserves, 1 retains a complete signed response, 2 advances a local fence.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Wal {
    pub promise: Promise<D>,
    pub kind: u8,
    pub frame: Bytes,
}
impl Write for Wal {
    fn write(&self, w: &mut impl BufMut) {
        self.promise.write(w);
        self.kind.write(w);
        (self.frame.len() as u32).write(w);
        w.put_slice(&self.frame);
    }
}
impl EncodeSize for Wal {
    fn encode_size(&self) -> usize {
        self.promise.encode_size() + 1 + 4 + self.frame.len()
    }
}
impl Read for Wal {
    type Cfg = ();
    fn read_cfg(r: &mut impl Buf, _: &()) -> Result<Self, commonware_codec::Error> {
        let promise = Promise::read(r)?;
        let kind = u8::read(r)?;
        let len = u32::read(r)? as usize;
        if !promise.valid() || kind > 2 || len > 65536 || (kind != 1 && len != 0) {
            return Err(commonware_codec::Error::Invalid(
                "recovery probe WAL",
                "shape",
            ));
        }
        if r.remaining() < len {
            return Err(commonware_codec::Error::EndOfBuffer);
        }
        Ok(Self {
            promise,
            kind,
            frame: r.copy_to_bytes(len),
        })
    }
}
impl Epochable for Wal {
    fn epoch(&self) -> Epoch {
        self.promise.proposal.epoch()
    }
}
impl Viewable for Wal {
    fn view(&self) -> View {
        self.promise.proposal.view()
    }
}
#[derive(Default)]
pub(crate) struct Ledger {
    reserved: Option<Promise<D>>,
    frame: Option<Bytes>,
    floor: Option<crate::types::Round>,
}
impl Mode<S, D> for RecoveryProbe {
    const RETAIN_INTERPRETATION: bool = true;
    type Assembly = recovery::NoRecovery;
    fn assembly_proposal(v: &Self::Assembly) -> &Proposal<D> {
        match *v {}
    }
    fn assembly_size(v: &Self::Assembly) -> usize {
        match *v {}
    }
    type Recovery = Wal;
    type Recovered = recovery::NoRecovery;
    fn read_recovered(
        _: &mut impl Buf,
        _: &<<S as commonware_cryptography::certificate::Verifier>::Certificate as Read>::Cfg,
    ) -> Result<Self::Recovered, commonware_codec::Error> {
        Err(commonware_codec::Error::Invalid(
            "recovery probe",
            "recovered disabled",
        ))
    }
    fn recovered_proposal(v: &Self::Recovered) -> &Proposal<D> {
        match *v {}
    }
    fn verify_recovered<R: CryptoRng>(
        v: &Self::Recovered,
        _: &mut R,
        _: &S,
        _: &impl Strategy,
    ) -> bool {
        match *v {}
    }
    type QueryResult = Self::RecoveryRequest;
    type RecoveryQuery = recovery::NoRecovery;
    fn recovery_query_view(v: &Self::RecoveryQuery) -> View {
        match *v {}
    }
    type RecoveryRequest = Wal;
    type RecoveryResponse = Bytes;
    fn recovery_view(v: &Wal) -> View {
        v.view()
    }
    type Notarize = Notarize<S, D>;
    fn notarize(v: &Self::Notarize) -> &Notarize<S, D> {
        v
    }
    fn into_notarize(v: Self::Notarize) -> Notarize<S, D> {
        v
    }
    type Vote = Finalize<S, D>;
    fn finalize_proposal(v: &Self::Vote) -> &Proposal<D> {
        &v.proposal
    }
    type Certificate = Finalization<S, D>;
    fn finalization_proposal(v: &Self::Certificate) -> &Proposal<D> {
        &v.proposal
    }
    fn finalization_certificate(
        v: &Self::Certificate,
    ) -> &<S as commonware_cryptography::certificate::Verifier>::Certificate {
        &v.certificate
    }
    fn signed_finalization_subject(v: &Self::Certificate) -> Subject<'_, D> {
        Subject::Finalize {
            proposal: &v.proposal,
        }
    }
    fn verify_companion<R: CryptoRng>(
        _: &Self::Certificate,
        _: &mut R,
        _: &Scoped<S>,
        _: &impl Strategy,
    ) -> bool {
        true
    }
    fn conflicting_finalize_subjects(a: &Self::Vote, b: &Self::Vote) -> bool {
        a.proposal != b.proposal
    }
    fn verify_finalize<R: CryptoRng>(v: &Self::Vote, r: &mut R, s: &S, p: &impl Strategy) -> bool {
        v.verify(r, s, p)
    }
    fn verify<R: CryptoRng>(v: &Self::Certificate, r: &mut R, s: &S, p: &impl Strategy) -> bool {
        v.verify(r, s, p)
    }
}
impl voting::Voting<S, D> for RecoveryProbe {
    type FirstInput = ();
    const REQUIRE_PARENT_INTERPRETATION: bool = false;
    type Context = RecoveryContext;
    type RecoveryState = Ledger;
    const EMPTY_RECOVERY: Ledger = Ledger {
        reserved: None,
        frame: None,
        floor: None,
    };
    fn allows_original(l: &Ledger) -> bool {
        l.floor.is_none()
    }
    fn recovery_proposal(r: &Wal) -> &Proposal<D> {
        &r.promise.proposal
    }
    fn recovery_context(c: &RecoveryContext, r: &Wal) -> bool {
        c.domain == r.promise.domain
    }
    fn replay_recovery<R: CryptoRng>(
        _: &S,
        _: &RecoveryContext,
        _: &mut R,
        l: &mut Ledger,
        _: Option<&()>,
        r: &Wal,
    ) -> bool {
        if !r.promise.valid() {
            return false;
        }
        match r.kind {
            0 => {
                if let Some(old) = &l.reserved {
                    return old == &r.promise;
                }
                if l.floor.is_some_and(|b| b > r.promise.ballot) {
                    return false;
                }
                l.reserved = Some(r.promise.clone());
                l.floor = Some(r.promise.ballot);
                true
            }
            1 => {
                let Ok(response) = Status::<S, D>::decode(r.frame.clone()) else {
                    return false;
                };
                if l.reserved.as_ref() != Some(&r.promise)
                    || response.promise != r.promise
                    || l.frame.as_ref().is_some_and(|f| f != &r.frame)
                {
                    return false;
                }
                l.frame = Some(r.frame.clone());
                true
            }
            2 => {
                if !r.frame.is_empty() || l.floor.is_some_and(|b| b >= r.promise.ballot) {
                    return false;
                }
                l.floor = Some(r.promise.ballot);
                true
            }
            _ => false,
        }
    }
    fn validate_recovery_request<E, L>(s: &mut voting::StateWith<E, S, L, D, Self>, r: &Wal) -> bool
    where
        E: commonware_runtime::Clock + CryptoRng + commonware_runtime::Metrics,
        L: crate::simplex::elector::Elector<S>,
    {
        r.kind == 0
            && r.frame.is_empty()
            && r.promise.valid()
            && s.interpretation_context().domain == r.promise.domain
            && s.notarization(r.view())
                .is_some_and(|c| c.proposal == r.promise.proposal)
    }
    fn stage_recovery_request<E, L>(
        s: &mut voting::StateWith<E, S, L, D, Self>,
        r: &Wal,
        _: &mut impl voting::Participation<S, D, Self>,
    ) -> Option<Wal>
    where
        E: commonware_runtime::Clock + CryptoRng + commonware_runtime::Metrics,
        L: crate::simplex::elector::Elector<S>,
    {
        if !<Self as voting::Voting<S, D>>::validate_recovery_request(s, r) {
            return None;
        }
        // This private fixture only tests native journal ordering. It supplies
        // an admitted local request, not a portable recovery admission proof.
        s.replay(&crate::simplex::types::ArtifactWith::Recovery(r.clone()));
        Some(r.clone())
    }
    fn prepare_recovery_request<E, L>(
        _: &mut voting::StateWith<E, S, L, D, Self>,
        r: &Self::RecoveryQuery,
        _: &mut impl voting::Participation<S, D, Self>,
    ) -> Option<Wal>
    where
        E: commonware_runtime::Clock + CryptoRng + commonware_runtime::Metrics,
        L: crate::simplex::elector::Elector<S>,
    {
        match *r {}
    }
    fn sign_recovery(_: &S, _: &RecoveryContext, _: &Wal) -> Option<Bytes> {
        None
    }
    fn sign_recovery_current<R: CryptoRng>(
        s: &S,
        c: &RecoveryContext,
        rng: &mut R,
        l: &mut Ledger,
        r: &Wal,
    ) -> Option<(Bytes, Option<Wal>)> {
        if r.kind != 0 || c.domain != r.promise.domain || l.reserved.as_ref() != Some(&r.promise) {
            return None;
        }
        if let Some(frame) = &l.frame {
            return Some((frame.clone(), None));
        }
        if l.floor != Some(r.promise.ballot) {
            return None;
        }
        let response = Status::sign(s, r.promise.clone()).ok()?;
        assert!(response.verify(rng, s, &commonware_parallel::Sequential));
        c.signed.fetch_add(1, Ordering::SeqCst);
        let frame = response.encode();
        let receipt = Wal {
            promise: r.promise.clone(),
            kind: 1,
            frame: frame.clone(),
        };
        assert!(<Self as voting::Voting<S, D>>::replay_recovery(
            s, c, rng, l, None, &receipt
        ));
        if let Some(gate) = &c.release_gate {
            gate.arm();
        }
        Some((frame, Some(receipt)))
    }
    type FinalSubject = ();
    fn matches_context(_: &RecoveryContext, _: &()) -> bool {
        true
    }
    fn matches_subject(_: &Proposal<D>, _: &()) -> bool {
        true
    }
    fn matches_parent(
        _: &RecoveryContext,
        _: &(),
        _: Option<&Self::Certificate>,
        _: Option<&Self::Recovered>,
        _: bool,
    ) -> bool {
        true
    }
    fn recovered_subject(v: &Self::Recovered) {
        match *v {}
    }
    fn same_interpretation(_: &(), _: &()) -> bool {
        true
    }
    fn final_subject(_: &Self::Vote) {}
    fn finalization_subject(_: &Self::Certificate) {}
    fn reserve_finalize(_: &()) -> Option<Wal> {
        None
    }
    fn reserved_subject(_: &Wal) -> Option<()> {
        None
    }
    fn sign_finalize(s: &S, p: Proposal<D>, _: ()) -> Option<Self::Vote> {
        Finalize::sign(s, p)
    }
}
