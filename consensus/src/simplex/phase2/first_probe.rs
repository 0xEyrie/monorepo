//! Private actual-G1 FIRST fixture; no production G1 Mode or recovery activation.
use super::*;
use crate::{
    simplex::{
        extension::{agreement::general as g, report},
        types::Context as NativeContext,
    },
    types::{Epoch, Participant, Round, View},
};
use bytes::{BufMut, Bytes};
use commonware_codec::{Buf, Encode as _, Error};
use commonware_cryptography::sha256::{Digest as D, Sha256};
use commonware_parallel::Sequential;
use std::sync::{
    Arc,
    atomic::{AtomicBool, Ordering},
};

pub(crate) const LIMITS: g::Limits = g::Limits {
    report_bytes: 128,
    order_bytes: 128,
    build_bytes: 128,
    material_bytes: 128,
    origin_bytes: g::MAX_EVIDENCE_BYTES,
};
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FirstProbe;
impl sealed::Sealed for FirstProbe {}
#[derive(Clone, Debug)]
pub(crate) struct FirstContext {
    pub input: D,
    pub profile: D,
    pub domain: D,
    // Injected current-hook refusal, not a native recovery permission.
    pub ready: Arc<AtomicBool>,
}
#[derive(Default)]
pub(crate) struct Capture {
    pub report: Option<Bytes>,
    pub preference: Option<Bytes>,
}
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Wal(pub g::issuance::Record<D>);
impl Write for Wal {
    fn write(&self, w: &mut impl BufMut) {
        self.0.write(w)
    }
}
impl EncodeSize for Wal {
    fn encode_size(&self) -> usize {
        self.0.encode_size()
    }
}
impl Read for Wal {
    type Cfg = ();
    fn read_cfg(r: &mut impl Buf, _: &()) -> Result<Self, Error> {
        let v = g::issuance::Record::read_cfg(r, &LIMITS)?;
        if !matches!(
            v.action(),
            g::issuance::Action::NoFirst
                | g::issuance::Action::Released { .. }
                | g::issuance::Action::Fence { .. }
                | g::issuance::Action::Reserve {
                    message: g::Message {
                        kind: g::Kind::First(_),
                        ..
                    },
                    ..
                }
        ) {
            return Err(Error::Invalid("first probe WAL", "role"));
        }
        Ok(Self(v))
    }
}
impl Epochable for Wal {
    fn epoch(&self) -> Epoch {
        self.0.epoch()
    }
}
impl Viewable for Wal {
    fn view(&self) -> View {
        self.0.view()
    }
}
pub(crate) struct Ledger<S: commonware_cryptography::certificate::Scheme>(
    pub Option<g::issuance::State<S, D>>,
);
impl<S: Scheme> Mode<S, D> for FirstProbe {
    const RETAIN_INTERPRETATION: bool = true;
    type Assembly = super::recovery::NoRecovery;
    fn assembly_proposal(value: &Self::Assembly) -> &Proposal<D> {
        match *value {}
    }
    fn assembly_size(value: &Self::Assembly) -> usize {
        match *value {}
    }
    type Recovery = Wal;
    type Recovered = recovery::NoRecovery;
    fn read_recovered(
        _: &mut impl commonware_codec::Buf,
        _: &<S::Certificate as Read>::Cfg,
    ) -> Result<Self::Recovered, commonware_codec::Error> {
        Err(commonware_codec::Error::Invalid(
            "simplex recovered",
            "disabled mode",
        ))
    }
    fn recovered_proposal(certificate: &Self::Recovered) -> &Proposal<D> {
        match *certificate {}
    }
    fn verify_recovered<R: CryptoRng>(
        certificate: &Self::Recovered,
        _: &mut R,
        _: &S,
        _: &impl Strategy,
    ) -> bool
    where
        S: scheme::Scheme<D>,
    {
        match *certificate {}
    }
    type RecoveryQuery = recovery::NoRecovery;
    fn recovery_query_view(query: &Self::RecoveryQuery) -> crate::types::View {
        match *query {}
    }
    type RecoveryRequest = recovery::NoRecovery;
    type RecoveryResponse = recovery::NoRecovery;
    fn recovery_view(request: &Self::RecoveryRequest) -> crate::types::View {
        match *request {}
    }
    fn notarize(vote: &Self::Notarize) -> &Notarize<S, D> {
        vote.vote()
    }
    fn finalize_proposal(vote: &Self::Vote) -> &Proposal<D> {
        &vote.proposal
    }
    fn into_notarize(vote: Self::Notarize) -> Notarize<S, D> {
        vote.into_parts().0
    }
    fn finalization_proposal(certificate: &Self::Certificate) -> &Proposal<D> {
        &certificate.proposal
    }
    fn finalization_certificate(certificate: &Self::Certificate) -> &S::Certificate {
        &certificate.certificate
    }
    fn signed_finalization_subject(certificate: &Self::Certificate) -> Subject<'_, D> {
        Subject::Finalize {
            proposal: &certificate.proposal,
        }
    }
    fn verify_companion<R: CryptoRng>(
        _: &Self::Certificate,
        _: &mut R,
        scoped: &Scoped<S>,
        _: &impl Strategy,
    ) -> bool
    where
        S: scheme::Scheme<D>,
    {
        let _ = scoped;
        true
    }
    fn conflicting_finalize_subjects(a: &Self::Vote, b: &Self::Vote) -> bool {
        a.proposal != b.proposal
    }
    fn verify_finalize<R: CryptoRng>(
        vote: &Self::Vote,
        rng: &mut R,
        scheme: &S,
        strategy: &impl Strategy,
    ) -> bool
    where
        S: scheme::Scheme<D>,
    {
        vote.verify(rng, scheme, strategy)
    }
    type Notarize = report::Notarize<S, D>;
    type Vote = Finalize<S, D>;
    type Certificate = Finalization<S, D>;
    fn verify<R: CryptoRng>(
        certificate: &Self::Certificate,
        rng: &mut R,
        scheme: &S,
        strategy: &impl Strategy,
    ) -> bool
    where
        S: scheme::Scheme<D>,
    {
        certificate.verify(rng, scheme, strategy)
    }
}

impl<S: scheme::Scheme<D>> voting::Voting<S, D> for FirstProbe {
    const RESERVE_NOTARIZE: bool = true;
    type FirstInput = Capture;
    const REQUIRE_PARENT_INTERPRETATION: bool = false;
    type Context = FirstContext;
    type RecoveryState = Ledger<S>;
    const EMPTY_RECOVERY: Ledger<S> = Ledger(None);
    fn allows_original(s: &Ledger<S>) -> bool {
        s.0.as_ref()
            .is_none_or(|s| s.floor() == s.core().slot.proposal.round)
    }
    fn recovery_proposal(r: &Wal) -> &Proposal<D> {
        &r.0.slot().proposal
    }
    fn recovery_context(c: &FirstContext, r: &Wal) -> bool {
        r.0.slot().profile == c.profile && r.0.slot().domain == c.domain && r.0.input() == c.input
    }
    fn replay_recovery<R: CryptoRng>(
        _: &S,
        _: &FirstContext,
        _: &mut R,
        _: &mut Ledger<S>,
        _: Option<&()>,
        _: &Wal,
    ) -> bool {
        false
    }
    fn reserve_notarize(
        s: &S,
        c: &FirstContext,
        l: &mut Ledger<S>,
        p: &Proposal<D>,
        native: &NativeContext<D, S::PublicKey>,
        input: Capture,
    ) -> Option<Wal> {
        let leader = s
            .participants()
            .iter()
            .position(|key| key == &native.leader)?;
        let slot = g::Slot {
            profile: c.profile,
            domain: c.domain,
            roster: g::Slot::roster::<Sha256, _>(s),
            cut: 1,
            proposal: p.clone(),
            parent: if native.parent.0.is_zero() {
                g::NativeParent::Genesis(native.parent.1)
            } else {
                g::NativeParent::Proposal {
                    round: Round::new(p.round.epoch(), native.parent.0),
                    digest: native.parent.1,
                }
            },
        };
        let core = g::Core::derive::<Sha256, _>(s, slot, Participant::new(leader as u32)).ok()?;
        if l.0.is_none() {
            l.0 = Some(
                g::issuance::State::new::<Sha256>(s.clone(), core.clone(), c.input, LIMITS).ok()?,
            );
        }
        let ledger = l.0.as_mut()?;
        if ledger.core() != &core {
            return None;
        }
        let own = ledger.owner();
        let record = if own == core.leader || core.followers.contains(&own) {
            ledger
                .reserve_first::<Sha256>(input.report, input.preference, |_| true)
                .ok()?
        } else {
            ledger.close_first::<Sha256>().ok()?
        };
        Some(Wal(record))
    }
    fn notarize_record(r: &Wal) -> Option<&Proposal<D>> {
        Some(&r.0.slot().proposal)
    }
    fn reserved_notarize(r: &Wal) -> Option<&Proposal<D>> {
        matches!(
            r.0.action(),
            g::issuance::Action::NoFirst
                | g::issuance::Action::Reserve {
                    message: g::Message {
                        kind: g::Kind::First(_),
                        ..
                    },
                    ..
                }
        )
        .then_some(&r.0.slot().proposal)
    }
    fn replay_notarize<R: CryptoRng>(
        s: &S,
        c: &FirstContext,
        rng: &mut R,
        l: &mut Ledger<S>,
        r: &Wal,
    ) -> bool {
        if !<Self as voting::Voting<S, D>>::recovery_context(c, r) {
            return false;
        }
        if l.0.is_none() {
            l.0 = g::issuance::State::for_replay::<Sha256>(
                s.clone(),
                r.0.core().clone(),
                c.input,
                LIMITS,
            )
            .ok();
        }
        l.0.as_mut().is_some_and(|ledger| {
            ledger
                .restore::<Sha256, _>(
                    rng,
                    &r.0,
                    g::issuance::Material::None,
                    |_| true,
                    |_, _| false,
                    &Sequential,
                )
                .is_ok()
        })
    }
    fn finish_notarize_replay(l: &mut Ledger<S>) -> bool {
        l.0.as_mut()
            .is_none_or(|ledger| ledger.finish_replay().is_ok())
    }
    fn replay_notarize_vote(l: &Ledger<S>, v: &report::Notarize<S, D>) -> bool {
        let Some(ledger) = &l.0 else {
            return false;
        };
        let Some(r) = ledger.records().iter().find(|r| {
            <Self as voting::Voting<S, D>>::reserved_notarize(&Wal((*r).clone())).is_some()
        }) else {
            return false;
        };
        if matches!(r.action(), g::issuance::Action::NoFirst) {
            v.report().is_none()
        } else {
            ledger
                .outbox(r)
                .is_some_and(|frame| v.report() == Some(frame))
        }
    }
    fn sign_notarize_current<R: CryptoRng>(
        s: &S,
        c: &FirstContext,
        rng: &mut R,
        l: &mut Ledger<S>,
        p: Proposal<D>,
        native: &NativeContext<D, S::PublicKey>,
        _: &mut impl voting::Participation<S, D, Self>,
    ) -> Option<(report::Notarize<S, D>, Option<Wal>)> {
        if !c.ready.load(Ordering::SeqCst) {
            return None;
        }
        let ledger = l.0.as_mut()?;
        let parent = if native.parent.0.is_zero() {
            g::NativeParent::Genesis(native.parent.1)
        } else {
            g::NativeParent::Proposal {
                round: Round::new(p.round.epoch(), native.parent.0),
                digest: native.parent.1,
            }
        };
        let core = ledger.core();
        if native.round != p.round
            || native.parent.0 != p.parent
            || core.slot.proposal != p
            || core.slot.parent != parent
            || s.participants().get(usize::from(core.leader)) != Some(&native.leader)
        {
            return None;
        }
        if ledger.floor() != p.round {
            return None;
        }
        let reservation = ledger
            .records()
            .iter()
            .find(|r| {
                matches!(
                    r.action(),
                    g::issuance::Action::NoFirst
                        | g::issuance::Action::Reserve {
                            message: g::Message {
                                kind: g::Kind::First(_),
                                ..
                            },
                            ..
                        }
                )
            })?
            .clone();
        let (frame, receipt) = if matches!(reservation.action(), g::issuance::Action::NoFirst) {
            if ledger.floor() != p.round {
                return None;
            }
            (None, None)
        } else if let Some(frame) = ledger.outbox(&reservation) {
            (Some(frame.clone()), None)
        } else {
            let signed = ledger.sign_reserved(&reservation).ok()?;
            let receipt = ledger
                .record_signed::<Sha256, _>(rng, &reservation, &signed, &Sequential)
                .ok()?;
            (Some(signed.encode()), Some(Wal(receipt)))
        };
        let base = Notarize::sign(s, p)?;
        Some((report::Notarize::new(base, frame).ok()?, receipt))
    }
    fn validate_recovery_request<E, L>(
        _: &mut voting::StateWith<E, S, L, D, Self>,
        r: &Self::RecoveryRequest,
    ) -> bool
    where
        E: commonware_runtime::Clock + rand_core::CryptoRng + commonware_runtime::Metrics,
        L: crate::simplex::elector::Elector<S>,
    {
        match *r {}
    }
    fn stage_recovery_request<E, L>(
        _: &mut voting::StateWith<E, S, L, D, Self>,
        r: &Self::RecoveryRequest,
        _: &mut impl voting::Participation<S, D, Self>,
    ) -> Option<Wal>
    where
        E: commonware_runtime::Clock + rand_core::CryptoRng + commonware_runtime::Metrics,
        L: crate::simplex::elector::Elector<S>,
    {
        match *r {}
    }
    fn prepare_recovery_request<E, L>(
        _: &mut voting::StateWith<E, S, L, D, Self>,
        r: &Self::RecoveryQuery,
        _: &mut impl voting::Participation<S, D, Self>,
    ) -> Option<Self::RecoveryRequest>
    where
        E: commonware_runtime::Clock + rand_core::CryptoRng + commonware_runtime::Metrics,
        L: crate::simplex::elector::Elector<S>,
    {
        match *r {}
    }
    fn sign_recovery(_: &S, _: &FirstContext, _: &Wal) -> Option<Self::RecoveryResponse> {
        None
    }
    fn sign_recovery_current<R: rand_core::CryptoRng>(
        _: &S,
        _: &FirstContext,
        _: &mut R,
        _: &mut Ledger<S>,
        _: &Wal,
    ) -> Option<(Self::RecoveryResponse, Option<Self::Recovery>)> {
        None
    }
    type FinalSubject = ();
    fn matches_context(_: &FirstContext, _: &()) -> bool {
        true
    }
    fn matches_subject(_: &Proposal<D>, _: &()) -> bool {
        true
    }
    fn matches_parent(
        _: &FirstContext,
        _: &(),
        _: Option<&Self::Certificate>,
        _: Option<&Self::Recovered>,
        _: bool,
    ) -> bool {
        true
    }
    fn recovered_subject(r: &Self::Recovered) {
        match *r {}
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
