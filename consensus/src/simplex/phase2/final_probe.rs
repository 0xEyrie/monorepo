//! Private paired-final hook fixture, not a production G1 mode or recovery profile.
use super::*;
use crate::{
    simplex::{
        extension::{
            certificate, report,
            vote::{Statement, Vote as NativeVote},
        },
        types::Context as NativeContext,
    },
    types::{Epoch, Participant, View},
};
use bytes::{Buf as _, BufMut, Bytes};
use commonware_codec::{Buf, DecodeExt as _, Encode as _, ReadExt as _};
use commonware_cryptography::{certificate::Attestation, sha256::Digest as D};
use std::sync::{
    Arc,
    atomic::{AtomicBool, AtomicUsize, Ordering},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FinalProbe;
impl sealed::Sealed for FinalProbe {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Capture {
    pub statement: Statement<D>,
    pub leader: Participant,
    pub native_parent: D,
}
impl Write for Capture {
    fn write(&self, w: &mut impl BufMut) {
        self.statement.write(w);
        self.leader.write(w);
        self.native_parent.write(w);
    }
}
impl EncodeSize for Capture {
    fn encode_size(&self) -> usize {
        self.statement.encode_size() + self.leader.encode_size() + self.native_parent.encode_size()
    }
}
impl Read for Capture {
    type Cfg = ();
    fn read_cfg(r: &mut impl Buf, _: &()) -> Result<Self, commonware_codec::Error> {
        Ok(Self {
            statement: Statement::read(r)?,
            leader: Participant::read(r)?,
            native_parent: D::read(r)?,
        })
    }
}
#[derive(Clone, Debug)]
pub(crate) struct FinalContext {
    pub domain: D,
    // Explicit test-only release refusal, not a native recovery permission.
    pub ready: Arc<AtomicBool>,
    pub staged: Arc<AtomicUsize>,
}
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Wal {
    pub capture: Capture,
    // 0: unsigned reservation; 1: complete signed pair receipt; 2: local fence.
    pub kind: u8,
    pub frame: Bytes,
}
impl Write for Wal {
    fn write(&self, w: &mut impl BufMut) {
        self.capture.write(w);
        self.kind.write(w);
        (self.frame.len() as u32).write(w);
        w.put_slice(&self.frame);
    }
}
impl EncodeSize for Wal {
    fn encode_size(&self) -> usize {
        self.capture.encode_size() + 1 + 4 + self.frame.len()
    }
}
impl Read for Wal {
    type Cfg = ();
    fn read_cfg(r: &mut impl Buf, _: &()) -> Result<Self, commonware_codec::Error> {
        let capture = Capture::read(r)?;
        let kind = u8::read(r)?;
        let len = u32::read(r)? as usize;
        if kind > 2 || len > 65536 || (kind != 1 && len != 0) {
            return Err(commonware_codec::Error::Invalid("final probe WAL", "shape"));
        }
        if r.remaining() < len {
            return Err(commonware_codec::Error::EndOfBuffer);
        }
        let frame = r.copy_to_bytes(len);
        Ok(Self {
            capture,
            kind,
            frame,
        })
    }
}
impl Epochable for Wal {
    fn epoch(&self) -> Epoch {
        self.capture.statement.proposal.epoch()
    }
}
impl Viewable for Wal {
    fn view(&self) -> View {
        self.capture.statement.proposal.view()
    }
}
#[derive(Default)]
pub(crate) struct Ledger {
    capture: Option<Capture>,
    frame: Option<Bytes>,
    fenced: bool,
}
#[derive(Clone, Debug)]
pub(crate) struct Pair<S: Scheme> {
    pub capture: Capture,
    pub native: certificate::Finalize<S, D>,
    pub companion: Attestation<S>,
}
impl<S: Scheme> PartialEq for Pair<S> {
    fn eq(&self, other: &Self) -> bool {
        self.capture == other.capture
            && self.native == other.native
            && self.companion == other.companion
    }
}
impl<S: Scheme> Write for Pair<S> {
    fn write(&self, w: &mut impl BufMut) {
        self.capture.write(w);
        self.native.write(w);
        self.companion.write(w)
    }
}
impl<S: Scheme> EncodeSize for Pair<S> {
    fn encode_size(&self) -> usize {
        self.capture.encode_size() + self.native.encode_size() + self.companion.encode_size()
    }
}
impl<S: Scheme> Read for Pair<S> {
    type Cfg = ();
    fn read_cfg(r: &mut impl Buf, _: &()) -> Result<Self, commonware_codec::Error> {
        Ok(Self {
            capture: Capture::read(r)?,
            native: certificate::Finalize::read(r)?,
            companion: Attestation::read(r)?,
        })
    }
}
impl<S: Scheme> Epochable for Pair<S> {
    fn epoch(&self) -> Epoch {
        self.native.epoch()
    }
}
impl<S: Scheme> Viewable for Pair<S> {
    fn view(&self) -> View {
        self.native.view()
    }
}
impl<S: Scheme> crate::types::Attributable for Pair<S> {
    fn signer(&self) -> Participant {
        self.companion.signer
    }
}

impl<S: Scheme> Mode<S, D> for FinalProbe {
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
        _: &mut impl Buf,
        _: &<S::Certificate as Read>::Cfg,
    ) -> Result<Self::Recovered, commonware_codec::Error> {
        Err(commonware_codec::Error::Invalid(
            "final probe",
            "recovered disabled",
        ))
    }
    fn recovered_proposal(r: &Self::Recovered) -> &Proposal<D> {
        match *r {}
    }
    fn verify_recovered<R: CryptoRng>(
        r: &Self::Recovered,
        _: &mut R,
        _: &S,
        _: &impl Strategy,
    ) -> bool
    where
        S: scheme::Scheme<D>,
    {
        match *r {}
    }
    type QueryResult = Self::RecoveryRequest;
    type RecoveryQuery = recovery::NoRecovery;
    fn recovery_query_view(r: &Self::RecoveryQuery) -> View {
        match *r {}
    }
    type RecoveryRequest = recovery::NoRecovery;
    type RecoveryResponse = recovery::NoRecovery;
    fn recovery_view(r: &Self::RecoveryRequest) -> View {
        match *r {}
    }
    type Notarize = report::Notarize<S, D>;
    fn notarize(v: &Self::Notarize) -> &Notarize<S, D> {
        v.vote()
    }
    fn into_notarize(v: Self::Notarize) -> Notarize<S, D> {
        v.into_parts().0
    }
    type Vote = Pair<S>;
    fn finalize_proposal(v: &Self::Vote) -> &Proposal<D> {
        &v.capture.statement.proposal
    }
    type Certificate = certificate::Finalization<S, D>;
    fn finalization_proposal(c: &Self::Certificate) -> &Proposal<D> {
        &c.certificate().statement.proposal
    }
    fn finalization_certificate(c: &Self::Certificate) -> &S::Certificate {
        &c.certificate().certificate
    }
    fn signed_finalization_subject(c: &Self::Certificate) -> Subject<'_, D> {
        Subject::FinalizeExtension {
            statement: &c.certificate().statement,
        }
    }
    // This fixture never receives final certificates or creates a quorum.
    fn verify_companion<R: CryptoRng>(
        _: &Self::Certificate,
        _: &mut R,
        _: &Scoped<S>,
        _: &impl Strategy,
    ) -> bool
    where
        S: scheme::Scheme<D>,
    {
        false
    }
    fn conflicting_finalize_subjects(a: &Self::Vote, b: &Self::Vote) -> bool {
        a.capture.statement != b.capture.statement
    }
    fn verify_finalize<R: CryptoRng>(
        v: &Self::Vote,
        rng: &mut R,
        s: &S,
        strategy: &impl Strategy,
    ) -> bool
    where
        S: scheme::Scheme<D>,
    {
        v.native.vote().statement == v.capture.statement
            && v.native.vote().attestation.signer == v.companion.signer
            && v.native.vote().verify(rng, s, strategy)
            && s.verify_attestation::<_, D>(
                rng,
                Subject::ExtensionAgreement {
                    round: v.capture.statement.ballot,
                    payload: &v.capture.encode(),
                },
                &v.companion,
                strategy,
            )
    }
    fn verify<R: CryptoRng>(_: &Self::Certificate, _: &mut R, _: &S, _: &impl Strategy) -> bool
    where
        S: scheme::Scheme<D>,
    {
        false
    }
}
impl<S: scheme::Scheme<D>> voting::Voting<S, D> for FinalProbe {
    const JOINT_FINALIZE: bool = true;
    type FirstInput = ();
    const REQUIRE_PARENT_INTERPRETATION: bool = false;
    type Context = FinalContext;
    type RecoveryState = Ledger;
    const EMPTY_RECOVERY: Ledger = Ledger {
        capture: None,
        frame: None,
        fenced: false,
    };
    fn allows_original(l: &Ledger) -> bool {
        !l.fenced
    }
    fn recovery_proposal(r: &Wal) -> &Proposal<D> {
        &r.capture.statement.proposal
    }
    fn recovery_context(c: &FinalContext, r: &Wal) -> bool {
        r.capture.statement.domain == c.domain
    }
    fn replay_recovery<R: CryptoRng>(
        _: &S,
        _: &FinalContext,
        _: &mut R,
        l: &mut Ledger,
        original: Option<&Capture>,
        r: &Wal,
    ) -> bool {
        if l.capture.as_ref().is_some_and(|c| c != &r.capture)
            || original.is_some_and(|c| c != &r.capture)
        {
            return false;
        }
        match r.kind {
            0 => {
                if l.fenced {
                    return false;
                }
                l.capture = Some(r.capture.clone());
                true
            }
            1 => {
                if l.capture.as_ref() != Some(&r.capture)
                    || l.fenced
                    || r.frame.is_empty()
                    || l.frame.as_ref().is_some_and(|f| f != &r.frame)
                {
                    return false;
                }
                l.frame = Some(r.frame.clone());
                true
            }
            2 => {
                l.fenced = true;
                true
            }
            _ => false,
        }
    }
    fn validate_recovery_request<E, L>(
        _: &mut voting::StateWith<E, S, L, D, Self>,
        r: &Self::RecoveryRequest,
    ) -> bool
    where
        E: commonware_runtime::Clock + CryptoRng + commonware_runtime::Metrics,
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
        E: commonware_runtime::Clock + CryptoRng + commonware_runtime::Metrics,
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
        E: commonware_runtime::Clock + CryptoRng + commonware_runtime::Metrics,
        L: crate::simplex::elector::Elector<S>,
    {
        match *r {}
    }
    fn sign_recovery(_: &S, _: &FinalContext, _: &Wal) -> Option<Self::RecoveryResponse> {
        None
    }
    fn sign_recovery_current<R: rand_core::CryptoRng>(
        _: &S,
        _: &FinalContext,
        _: &mut R,
        _: &mut Ledger,
        _: &Wal,
    ) -> Option<(Self::RecoveryResponse, Option<Self::Recovery>)> {
        None
    }
    type FinalSubject = Capture;
    fn matches_context(c: &FinalContext, s: &Capture) -> bool {
        c.domain == s.statement.domain
    }
    fn matches_subject(p: &Proposal<D>, s: &Capture) -> bool {
        p == &s.statement.proposal && p.round == s.statement.ballot
    }
    fn matches_parent(
        _: &FinalContext,
        _: &Capture,
        _: Option<&Self::Certificate>,
        _: Option<&Self::Recovered>,
        _: bool,
    ) -> bool {
        true
    }
    fn recovered_subject(r: &Self::Recovered) -> Capture {
        match *r {}
    }
    fn same_interpretation(a: &Capture, b: &Capture) -> bool {
        a == b
    }
    fn final_subject(v: &Self::Vote) -> Capture {
        v.capture.clone()
    }
    fn finalization_subject(_: &Self::Certificate) -> Capture {
        unreachable!("fixture has no final certificate")
    }
    fn reserve_finalize(s: &Capture) -> Option<Wal> {
        Some(Wal {
            capture: s.clone(),
            kind: 0,
            frame: Bytes::new(),
        })
    }
    fn stage_final_reservation<R: CryptoRng>(
        scheme: &S,
        context: &FinalContext,
        _: &mut R,
        ledger: &mut Ledger,
        proposal: &Proposal<D>,
        native: Option<&NativeContext<D, S::PublicKey>>,
        capture: &Capture,
    ) -> Option<Option<Wal>> {
        let native = native?;
        if ledger.fenced
            || ledger.capture.is_some()
            || proposal != &capture.statement.proposal
            || native.round != proposal.round
            || native.parent != (proposal.parent, capture.native_parent)
            || scheme.participants().get(usize::from(capture.leader)) != Some(&native.leader)
        {
            return None;
        }
        ledger.capture = Some(capture.clone());
        context.staged.fetch_add(1, Ordering::SeqCst);
        Some(<Self as voting::Voting<S, D>>::reserve_finalize(capture))
    }
    fn reserved_subject(r: &Wal) -> Option<Capture> {
        (r.kind == 0).then(|| r.capture.clone())
    }
    fn sign_finalize(_: &S, _: Proposal<D>, _: Capture) -> Option<Self::Vote> {
        None
    }
    fn retained_finalize(l: &Ledger, c: &Capture) -> Option<Self::Vote> {
        if l.capture.as_ref() != Some(c) {
            return None;
        }
        Pair::decode(l.frame.clone()?).ok()
    }
    fn replay_finalize_vote(l: &Ledger, v: &Self::Vote) -> bool {
        l.capture.as_ref() == Some(&v.capture) && l.frame.as_ref().is_some_and(|f| f == &v.encode())
    }
    fn sign_finalize_current<R: CryptoRng>(
        s: &S,
        c: &FinalContext,
        _: &mut R,
        l: &mut Ledger,
        p: Proposal<D>,
        native: Option<&NativeContext<D, S::PublicKey>>,
        capture: Capture,
    ) -> Option<(Pair<S>, Option<Wal>)> {
        let native = native?;
        if !c.ready.load(Ordering::SeqCst)
            || l.fenced
            || p != capture.statement.proposal
            || native.round != p.round
            || native.parent != (p.parent, capture.native_parent)
            || s.participants().get(usize::from(capture.leader)) != Some(&native.leader)
            || l.capture.as_ref() != Some(&capture)
        {
            return None;
        }
        if let Some(frame) = &l.frame {
            return Some((
                Pair::decode(frame.clone()).expect("retained pair codec"),
                None,
            ));
        }
        l.capture = Some(capture.clone());
        let companion = s
            .sign::<D>(Subject::ExtensionAgreement {
                round: capture.statement.ballot,
                payload: &capture.encode(),
            })
            .expect("joint companion signer unavailable");
        let native = certificate::Finalize::new(
            NativeVote::sign(s, capture.statement.clone())
                .expect("joint native signer unavailable"),
        )
        .expect("original round");
        let pair = Pair {
            capture: capture.clone(),
            native,
            companion,
        };
        let frame = pair.encode();
        l.frame = Some(frame.clone());
        Some((
            pair,
            Some(Wal {
                capture,
                kind: 1,
                frame,
            }),
        ))
    }
}
