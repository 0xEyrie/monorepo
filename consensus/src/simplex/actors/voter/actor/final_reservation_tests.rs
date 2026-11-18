//! Actor/journal controls for a private paired-final mode. No production G1 activation.
use super::*;
use crate::simplex::{
    extension::agreement::general as g,
    phase2::{
        Mode as _,
        final_probe::{Capture, FinalContext, FinalProbe, Ledger, Wal},
    },
    types::Subject,
};
use commonware_codec::Encode as _;
use commonware_cryptography::{
    Digest,
    certificate::{self, Attestation},
};
use commonware_parallel::Strategy;
use commonware_utils::{iter::NonEmpty, ordered::Set};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
#[derive(Clone, Debug)]
struct FinalObserved {
    inner: S,
    native: Arc<AtomicUsize>,
    extension: Arc<AtomicUsize>,
    fail_native: Arc<AtomicBool>,
}
impl certificate::Verifier for FinalObserved {
    type Subject<'a, T: Digest> = Subject<'a, T>;
    type Faults = <S as certificate::Verifier>::Faults;
    type PublicKey = PublicKey;
    type Certificate = <S as certificate::Verifier>::Certificate;
    fn verify_certificate<R: CryptoRng, T: Digest>(
        &self,
        rng: &mut R,
        subject: Subject<'_, T>,
        certificate: &Self::Certificate,
        strategy: &impl Strategy,
    ) -> bool {
        self.inner
            .verify_certificate(rng, subject, certificate, strategy)
    }
    fn is_batchable() -> bool {
        S::is_batchable()
    }
    fn certificate_codec_config(&self) -> <Self::Certificate as Read>::Cfg {
        self.inner.certificate_codec_config()
    }
    fn certificate_codec_config_unbounded() -> <Self::Certificate as Read>::Cfg {
        S::certificate_codec_config_unbounded()
    }
}
impl certificate::Scheme for FinalObserved {
    type Signature = <S as certificate::Scheme>::Signature;
    fn me(&self) -> Option<crate::types::Participant> {
        self.inner.me()
    }
    fn participants(&self) -> &Set<PublicKey> {
        self.inner.participants()
    }
    fn sign<T: Digest>(&self, subject: Subject<'_, T>) -> Option<Attestation<Self>> {
        if matches!(subject, Subject::FinalizeExtension { .. }) {
            self.native.fetch_add(1, Ordering::SeqCst);
            if self.fail_native.load(Ordering::SeqCst) {
                return None;
            }
        }
        if matches!(subject, Subject::ExtensionAgreement { .. }) {
            self.extension.fetch_add(1, Ordering::SeqCst);
        }
        self.inner.sign(subject).map(|a| Attestation {
            signer: a.signer,
            signature: a.signature,
        })
    }
    fn verify_attestation<R: CryptoRng, T: Digest>(
        &self,
        rng: &mut R,
        subject: Subject<'_, T>,
        a: &Attestation<Self>,
        strategy: &impl Strategy,
    ) -> bool {
        self.inner.verify_attestation(
            rng,
            subject,
            &Attestation {
                signer: a.signer,
                signature: a.signature.clone(),
            },
            strategy,
        )
    }
    fn optimistic_assemble<'a, R: CryptoRng, T: Digest, I, J>(
        &self,
        rng: &mut R,
        subject: Subject<'_, T>,
        pending: I,
        verified: J,
        strategy: &impl Strategy,
    ) -> Result<Self::Certificate, certificate::Verification<Self>>
    where
        I: IntoIterator<Item = Attestation<Self>>,
        I::IntoIter: ExactSizeIterator + Send,
        J: IntoIterator<Item = &'a Attestation<Self>>,
        J::IntoIter: Send,
    {
        certificate::optimistic_assemble(self, rng, subject, pending, verified, strategy)
    }
    fn assemble<I: Iterator<Item = Attestation<Self>> + Send>(
        &self,
        attestations: NonEmpty<I>,
        strategy: &impl Strategy,
    ) -> Result<Self::Certificate, certificate::AssemblyError> {
        self.inner.assemble(
            non_empty![@attestations.into_iter().map(|a| Attestation {
                signer: a.signer, signature: a.signature,
            })],
            strategy,
        )
    }
    fn is_attributable() -> bool {
        true
    }
}

#[derive(Clone)]
struct FinalEvidence {
    capture: Capture,
    calls: Arc<AtomicUsize>,
    replayed: Arc<AtomicBool>,
}
impl Participation<FinalObserved, D, FinalProbe> for FinalEvidence {
    fn replayed(&mut self) {
        self.replayed.store(true, Ordering::SeqCst);
    }
    fn notarize(&mut self, v: Notarize<FinalObserved, D>) -> report::Notarize<FinalObserved, D> {
        v.into()
    }
    fn final_subject(&mut self, p: &Proposal<D>) -> Option<Capture> {
        self.calls.fetch_add(1, Ordering::SeqCst);
        (p == &self.capture.statement.proposal).then(|| self.capture.clone())
    }
    fn accepts_finalization(&mut self, _: &Finalization<FinalObserved, D>) -> bool {
        false
    }
    fn accepts_replay(&mut self, _: &ArtifactWith<FinalObserved, D, FinalProbe>) -> bool {
        true
    }
    fn prune(&mut self, _: View) {}
}
#[derive(Clone)]
struct FinalSink;
impl Reporter for FinalSink {
    type Activity = ActivityWith<FinalObserved, D, FinalProbe>;
    fn report(&mut self, _: Self::Activity) -> Feedback {
        Feedback::Ok
    }
}
fn final_context() -> FinalContext {
    FinalContext {
        domain: D::from([8; 32]),
        ready: Arc::new(AtomicBool::new(true)),
        staged: Arc::new(AtomicUsize::new(0)),
    }
}
fn capture(s: &FinalObserved, view: u64) -> Capture {
    use crate::simplex::elector::Elector as _;
    let elector: crate::simplex::elector::RoundRobinElector<FinalObserved> =
        RoundRobin::<Sha256>::default().build(s.participants());
    Capture {
        statement: statement(view, D::from([9; 32])),
        leader: elector.elect(proposal(view).round, None),
        native_parent: if view == 1 {
            D::from([0; 32])
        } else {
            proposal(view - 1).payload
        },
    }
}
fn evidence(capture: Capture) -> FinalEvidence {
    FinalEvidence {
        capture,
        calls: Arc::new(AtomicUsize::new(0)),
        replayed: Arc::new(AtomicBool::new(false)),
    }
}
// Real q OTHER validators: the local owner need not have issued any first vote.
fn peer_nqc(f: &Fixture<S>, p: Proposal<D>) -> Notarization<FinalObserved, D> {
    let q = g::Committee::new(f.schemes.len()).unwrap().quorum();
    let votes: Vec<_> = f
        .schemes
        .iter()
        .skip(1)
        .take(q)
        .map(|s| Notarize::sign(s, p.clone()).unwrap())
        .collect();
    let c =
        Notarization::from_notarizes(&f.verifier, non_empty![@votes.iter()], &Sequential).unwrap();
    Notarization {
        proposal: c.proposal,
        certificate: c.certificate,
    }
}
macro_rules! config {
    ($s:expr,$cache:expr,$partition:expr,$n:expr) => {
        Config {
            scheme: $s.clone(),
            elector: RoundRobin::<Sha256>::default().build($s.participants()),
            blocker: NoopBlocker::default(),
            automaton: App::default(),
            relay: App::default(),
            reporter: FinalSink,
            partition: $partition.into(),
            epoch: Epoch::new(1),
            floor: FloorWith::Genesis(D::from([0; 32])),
            mailbox_size: NZUsize!(32),
            leader_timeout: Duration::from_secs(60),
            certification_timeout: Duration::from_secs(60),
            timeout_retry: Duration::from_secs(60),
            skip_budget: u64::from($n),
            view_retention: ViewDelta::new(10),
            replay_buffer: NZUsize!(4096),
            write_buffer: NZUsize!(4096),
            page_cache: $cache.clone(),
        }
    };
}
macro_rules! journal_config {
    ($s:expr,$cache:expr,$partition:expr) => {
        JConfig {
            partition: $partition.into(),
            compression: None,
            codec_config: $s.certificate_codec_config(),
            page_cache: $cache.clone(),
            write_buffer: NZUsize!(4096),
        }
    };
}
fn live_joint(n: u32, case: u8) {
    deterministic::Runner::new(
        deterministic::Config::new()
            .with_timeout(Some(Duration::from_secs(20)))
            .with_catch_panics(true),
    )
    .start(move |mut context| async move {
        let f = ed25519::fixture(&mut context, b"_COMMONWARE_CONSENSUS_JOINT_FINAL_TEST", n);
        let native = Arc::new(AtomicUsize::new(0));
        let companion = Arc::new(AtomicUsize::new(0));
        let s = FinalObserved {
            inner: if case == 2 {
                f.verifier.clone()
            } else {
                f.schemes[0].clone()
            },
            native: native.clone(),
            extension: companion.clone(),
            fail_native: Arc::new(AtomicBool::new(false)),
        };
        let gates = PendingSyncs::default();
        gates.unblock();
        let actor_context = DelayedSyncContext {
            inner: context.child("voter"),
            pending: gates.clone(),
        };
        let cache = CacheRef::from_pooler(&actor_context, NZU16!(1024), NZUsize!(10));
        let c = final_context();
        let e = evidence(capture(&s, 1));
        if case == 3 {
            c.ready.store(false, Ordering::SeqCst);
        }
        let (mut actor, _) = ActorWith::new_with(
            actor_context,
            config!(s, cache, "joint-live", n),
            c.clone(),
            e.clone(),
        );
        actor.state.set_genesis(D::from([0; 32]));
        let cert = peer_nqc(&f, proposal(1));
        actor.state.add_notarization(cert.clone());
        actor
            .state
            .replay(&ArtifactWith::Certification(proposal(1).round, true));
        assert!(
            actor
                .state
                .construct_finalize_with(View::new(1), e.capture.clone())
                .is_none(),
            "joint public signer bypass"
        );
        assert_eq!(native.load(Ordering::SeqCst), 0);
        assert_eq!(companion.load(Ordering::SeqCst), 0);
        actor.journal = Some(
            Journal::init(
                actor.context.child("journal"),
                journal_config!(s, cache, "joint-live"),
            )
            .await
            .unwrap(),
        );
        actor = actor.append_journal(ArtifactWith::Notarization(cert)).await;
        actor = actor
            .append_journal(ArtifactWith::Certification(proposal(1).round, true))
            .await;
        actor = actor.sync_journal().await;
        gates.arm();
        let handle = context
            .child("prepare")
            .spawn(|_| actor.prepare_finalize(View::new(1)));
        if case == 2 {
            let (actor, vote) = handle.await.unwrap();
            assert!(vote.is_none());
            assert_eq!(gates.calls(), 0);
            assert_eq!(c.staged.load(Ordering::SeqCst), 0);
            assert_eq!(native.load(Ordering::SeqCst), 0);
            assert_eq!(companion.load(Ordering::SeqCst), 0);
            drop(actor);
            return;
        }
        while gates.lock().is_empty() {
            reschedule().await;
        }
        let gate = next_pending_sync(&gates);
        gate.blocked.await.unwrap();
        assert_eq!(
            c.staged.load(Ordering::SeqCst),
            1,
            "sole ledger owns the unsigned reservation before journal sync"
        );
        assert_eq!(
            native.load(Ordering::SeqCst),
            0,
            "native signer before sync"
        );
        assert_eq!(
            companion.load(Ordering::SeqCst),
            0,
            "companion signer before sync"
        );
        if case == 1 {
            drop(gate.release);
            assert!(handle.await.is_err());
            assert_eq!(native.load(Ordering::SeqCst), 0);
            assert_eq!(companion.load(Ordering::SeqCst), 0);
            return;
        }
        gate.release.send(Ok(())).unwrap();
        let (mut actor, mut vote) = handle.await.unwrap();
        if case == 3 {
            assert!(vote.is_none());
            assert_eq!(e.calls.load(Ordering::SeqCst), 1);
            assert_eq!(native.load(Ordering::SeqCst), 0);
            assert_eq!(companion.load(Ordering::SeqCst), 0);
            assert!(
                actor
                    .state
                    .construct_nullify(View::new(1), TimeoutReason::CertificationTimeout)
                    .is_none(),
                "pending final remains an irrevocable own choice"
            );
            c.ready.store(true, Ordering::SeqCst);
            (actor, vote) = Box::pin(actor.prepare_finalize(View::new(1))).await;
        }
        let vote = vote.unwrap();
        assert_eq!(vote.capture, e.capture);
        assert!(FinalProbe::verify_finalize(
            &vote,
            &mut context,
            &s,
            &Sequential
        ));
        assert_eq!(native.load(Ordering::SeqCst), 1);
        assert_eq!(companion.load(Ordering::SeqCst), 1);
        assert_eq!(e.calls.load(Ordering::SeqCst), 1);
        assert_eq!(c.staged.load(Ordering::SeqCst), 1);
        assert_eq!(actor.dirty_section, Some(View::new(1)));
        actor = actor.sync_journal().await;
        assert!(actor.dirty_section.is_none());
        let (actor, duplicate) = Box::pin(actor.prepare_finalize(View::new(1))).await;
        assert!(duplicate.is_none());
        assert_eq!(e.calls.load(Ordering::SeqCst), 1);
        drop(actor);
        let journal = Journal::<_, ArtifactWith<FinalObserved, D, FinalProbe>>::init(
            context.child("inspect"),
            journal_config!(s, cache, "joint-live"),
        )
        .await
        .unwrap();
        let mut replay = journal
            .replay(0, 0, NZUsize!(4096), ReadOptions::DONT_CACHE)
            .await
            .unwrap();
        let mut tail = Vec::new();
        while let Some(item) = replay.next().await {
            match item.unwrap().3 {
                ArtifactWith::Recovery(r) => tail.push((r.kind, r.frame)),
                ArtifactWith::Finalize(v) => {
                    assert_eq!(tail.last(), Some(&(1, v.encode())));
                    assert_eq!(v, vote);
                }
                _ => {}
            }
        }
        assert_eq!(tail.len(), 2);
        assert_eq!(tail[0].0, 0);
        assert_eq!(tail[1].0, 1);
        drop(replay.finish().unwrap());
    });
}
#[test]
fn joint_final_both_signers_wait_for_actor_wal_sync_general_rosters() {
    for n in [7, 8, 10] {
        live_joint(n, 0);
    }
}
#[test]
fn joint_final_failed_sync_never_calls_either_signer() {
    live_joint(10, 1);
}
#[test]
fn joint_final_observer_cannot_reserve_or_sign() {
    live_joint(8, 2);
}
#[test]
fn joint_final_refusal_then_ready_reuses_exact_pending_choice() {
    live_joint(10, 3);
}

// 0 unsigned; 1 unsigned+floor; 2 receipt-only+floor; 3 complete+floor;
// 4 ignored conflicting parent NQC; 5 replay refusal then ready; 6 missing receipt.
fn restart_joint(n: u32, case: u8) {
    deterministic::Runner::new(
        deterministic::Config::new()
            .with_timeout(Some(Duration::from_secs(20)))
            .with_catch_panics(true),
    )
    .start(move |mut context| async move {
        let f = ed25519::fixture(
            &mut context,
            b"_COMMONWARE_CONSENSUS_JOINT_FINAL_RESTART_TEST",
            n,
        );
        let native = Arc::new(AtomicUsize::new(0));
        let companion = Arc::new(AtomicUsize::new(0));
        let s = FinalObserved {
            inner: f.schemes[0].clone(),
            native: native.clone(),
            extension: companion.clone(),
            fail_native: Arc::new(AtomicBool::new(false)),
        };
        let cache = CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(10));
        let c = final_context();
        let view = if case == 4 || case == 7 { 2 } else { 1 };
        let target = View::new(view);
        let old = evidence(capture(&s, view));
        let (mut seed, _) = ActorWith::new_with(
            context.child("seed"),
            config!(s, cache, "joint-restart", n),
            c.clone(),
            old.clone(),
        );
        seed.state.set_genesis(D::from([0; 32]));
        let mut records: Vec<ArtifactWith<FinalObserved, D, FinalProbe>> = Vec::new();
        if case == 4 || case == 7 {
            let p = peer_nqc(&f, proposal(1));
            seed.state.add_notarization(p.clone());
            seed.state
                .replay(&ArtifactWith::Certification(proposal(1).round, true));
            records.push(ArtifactWith::Notarization(p));
            records.push(ArtifactWith::Certification(proposal(1).round, true));
        }
        let cert = peer_nqc(&f, proposal(view));
        seed.state.add_notarization(cert.clone());
        seed.state
            .replay(&ArtifactWith::Certification(proposal(view).round, true));
        records.push(ArtifactWith::Notarization(cert.clone()));
        records.push(ArtifactWith::Certification(proposal(view).round, true));
        assert_eq!(seed.state.leader_index(target), Some(old.capture.leader));
        let (_, reservation) = seed
            .state
            .stage_finalize_with(target, old.capture.clone())
            .unwrap();
        records.push(ArtifactWith::Recovery(reservation.unwrap()));
        seed.journal = Some(
            Journal::init(
                seed.context.child("journal"),
                journal_config!(s, cache, "joint-restart"),
            )
            .await
            .unwrap(),
        );
        for r in &records {
            if seed.dirty_section.is_some_and(|view| view != r.view()) {
                seed = seed.sync_journal().await;
            }
            seed = seed.append_journal(r.clone()).await;
        }
        seed = seed.sync_journal().await;
        assert_eq!(native.load(Ordering::SeqCst), 0);
        assert_eq!(companion.load(Ordering::SeqCst), 0);
        let mut exact = None;
        if matches!(case, 2 | 3 | 6) {
            // The unsigned pair reservation is genuinely synchronized first.
            let (vote, receipt) = seed
                .state
                .sign_reserved_finalize(target, old.capture.clone())
                .unwrap();
            if case != 6 {
                let receipt = ArtifactWith::Recovery(receipt.unwrap());
                records.push(receipt.clone());
                seed = seed.append_journal(receipt).await;
            }
            if case == 3 || case == 6 {
                let record = ArtifactWith::Finalize(vote.clone());
                records.push(record.clone());
                seed = seed.append_journal(record).await;
            }
            // case2 models crash after the complete pair receipt, before the
            // redundant outer native vote record, using the actual journal.
            exact = Some(vote);
        }
        if matches!(case, 1..=3) {
            let record = ArtifactWith::Recovery(Wal {
                capture: old.capture.clone(),
                kind: 2,
                frame: Bytes::new(),
            });
            records.push(record.clone());
            seed = seed.append_journal(record).await;
        }
        if case == 4 {
            // Native keeps its first NQC and ignores this conflicting one.
            // This adversarial control does not claim two conflicting QCs can
            // form within the native fault budget.
            let mut p = proposal(1);
            p.payload = D::from([94; 32]);
            let record = ArtifactWith::Notarization(peer_nqc(&f, p));
            records.push(record.clone());
            seed = seed.append_journal(record).await;
        }
        seed = seed.sync_journal().await;
        drop(seed);
        native.store(0, Ordering::SeqCst);
        companion.store(0, Ordering::SeqCst);
        c.staged.store(0, Ordering::SeqCst);
        if case == 5 {
            c.ready.store(false, Ordering::SeqCst);
        }
        let fresh = evidence(old.capture.clone());
        let (network, oracle) = Network::new_with_peers(
            context.child("network"),
            NConfig {
                max_size: 1024 * 1024,
                max_peers_per_set: NonZeroUsize::new(n as usize).unwrap(),
                disconnect_on_block: true,
                tracked_peer_sets: NZUsize!(1),
            },
            f.participants.clone(),
        )
        .await;
        network.start();
        let me = f.participants[0].clone();
        let (votes, _) = oracle
            .control(me.clone())
            .register(0, Quota::per_second(NZU32!(1000)))
            .await
            .unwrap();
        let (certificates, _) = oracle
            .control(me)
            .register(1, Quota::per_second(NZU32!(1000)))
            .await
            .unwrap();
        let (actor, mut input) = ActorWith::new_with(
            context.child("reopen"),
            config!(s, cache, "joint-restart", n),
            c.clone(),
            fresh.clone(),
        );
        let (batcher_tx, mut batcher_rx) = mailbox::new(context.child("batcher"), NZUsize!(32));
        let (resolver_tx, _resolver_rx) = mailbox::new(context.child("resolver"), NZUsize!(32));
        let handle = actor.start(
            batcher::Mailbox::new(batcher_tx),
            resolver::Mailbox::new(resolver_tx),
            votes,
            certificates,
        );
        if case == 6 {
            assert!(
                handle.await.is_err(),
                "complete native vote must require exact retained paired receipt"
            );
            assert!(!fresh.replayed.load(Ordering::SeqCst));
            assert_eq!(native.load(Ordering::SeqCst), 0);
            assert_eq!(companion.load(Ordering::SeqCst), 0);
            return;
        }
        while !fresh.replayed.load(Ordering::SeqCst) {
            reschedule().await;
        }
        if case == 5 {
            assert_eq!(native.load(Ordering::SeqCst), 0);
            assert_eq!(companion.load(Ordering::SeqCst), 0);
            c.ready.store(true, Ordering::SeqCst);
            // A genuine native event retries the retained reservation. Only
            // the private Mode readiness transition is injected.
            input.recovered(CertificateWith::Notarization(cert));
        }
        if case == 1 {
            assert_eq!(native.load(Ordering::SeqCst), 0);
            assert_eq!(companion.load(Ordering::SeqCst), 0);
            while let Some(message) = batcher_rx.recv().now_or_never().flatten() {
                assert!(!matches!(
                    message,
                    batcher::Message::Constructed(VoteWith::Finalize(_))
                ));
            }
        } else {
            let vote = loop {
                if let batcher::Message::Constructed(VoteWith::Finalize(v)) =
                    batcher_rx.recv().await.unwrap()
                {
                    break v;
                }
            };
            assert_eq!(vote.capture, old.capture);
            assert!(FinalProbe::verify_finalize(
                &vote,
                &mut context,
                &s,
                &Sequential
            ));
            if let Some(expected) = exact {
                assert_eq!(
                    vote.encode(),
                    expected.encode(),
                    "retained pair retransmission is byte exact"
                );
            }
            let newly_signed = usize::from(case == 0 || case == 4 || case == 5 || case == 7);
            assert_eq!(native.load(Ordering::SeqCst), newly_signed);
            assert_eq!(companion.load(Ordering::SeqCst), newly_signed);
        }
        assert_eq!(
            fresh.calls.load(Ordering::SeqCst),
            0,
            "replay/retry cannot recapture the retained final subject"
        );
        assert_eq!(
            c.staged.load(Ordering::SeqCst),
            0,
            "replay/retry cannot consume a second final reservation"
        );
        handle.abort();
        let _ = handle.await;
        let journal = Journal::<_, ArtifactWith<FinalObserved, D, FinalProbe>>::init(
            context.child("inspect"),
            journal_config!(s, cache, "joint-restart"),
        )
        .await
        .unwrap();
        let mut replay = journal
            .replay(0, 0, NZUsize!(4096), ReadOptions::DONT_CACHE)
            .await
            .unwrap();
        let mut retained = Vec::new();
        while let Some(item) = replay.next().await {
            retained.push(item.unwrap().3);
        }
        // Sections replay in native view order, so the changed-parent case has
        // its genuine parent replacement ordered before the child reservation.
        if case != 4 {
            for (actual, expected) in retained.iter().zip(&records) {
                assert_eq!(actual.encode(), expected.encode());
            }
            assert!(retained.len() >= records.len());
        }
        let complete: Vec<_> = retained
            .iter()
            .filter_map(|r| {
                if let ArtifactWith::Finalize(v) = r {
                    Some(v)
                } else {
                    None
                }
            })
            .collect();
        assert_eq!(complete.len(), usize::from(case != 1));
        if let Some(vote) = complete.first() {
            let position = retained
                .iter()
                .position(|r| matches!(r, ArtifactWith::Finalize(_)))
                .unwrap();
            assert!(retained[..position].iter().any(
                |r| matches!(r,ArtifactWith::Recovery(w) if w.kind==1 && w.frame==vote.encode())
            ));
        }
        drop(replay.finish().unwrap());
        if case == 2 {
            let (mut again, _) = ActorWith::new_with(
                context.child("second_replay"),
                config!(s, cache, "joint-unused", n),
                c,
                evidence(old.capture),
            );
            again.state.set_genesis(D::from([0; 32]));
            for artifact in &retained {
                // Actor replay installs native QCs through handle_notarization
                // after State::replay restores the local broadcast marker.
                if let ArtifactWith::Notarization(certificate) = artifact {
                    again.state.add_notarization(certificate.clone());
                }
                again.state.replay(artifact);
            }
            again.state.finish_notarize_replay();
            assert_eq!(native.load(Ordering::SeqCst), 0);
            assert_eq!(companion.load(Ordering::SeqCst), 0);
        }
    });
}
#[test]
fn joint_final_unsigned_actor_restart_general_rosters() {
    for n in [7, 8, 10] {
        restart_joint(n, 0);
    }
}
#[test]
fn joint_final_unsigned_replay_after_floor_never_signs() {
    restart_joint(10, 1);
}
#[test]
fn joint_final_retained_receipt_after_floor_restarts_exact_pair_without_signing() {
    restart_joint(10, 2);
}
#[test]
fn joint_final_complete_pair_after_floor_restarts_without_signing() {
    restart_joint(8, 3);
}
#[test]
fn joint_final_conflicting_parent_nqc_is_ignored_and_keeps_exact_parent() {
    restart_joint(10, 4);
}
#[test]
fn joint_final_startup_refusal_then_ready_never_recaptures_or_restages() {
    restart_joint(10, 5);
}
#[test]
fn joint_final_replay_rejects_native_pair_without_released_receipt() {
    restart_joint(10, 6);
}

#[test]
fn joint_final_same_native_parent_child_replay_signs_exact_choice() {
    restart_joint(10, 7);
}

// This isolated Mode-hook control assumes the caller's native preflight. The
// Actor tests above exercise its actual reservation/sync/release wiring. A
// changed current context here is not a claimed authenticated native trace.
#[test]
fn joint_final_current_hook_rejects_wrong_parent_before_both_signers() {
    deterministic::Runner::timed(Duration::from_secs(20)).start(|mut context| async move {
        let f = ed25519::fixture(
            &mut context,
            b"_COMMONWARE_CONSENSUS_JOINT_FINAL_CONTEXT_TEST",
            10,
        );
        let native_calls = Arc::new(AtomicUsize::new(0));
        let companion_calls = Arc::new(AtomicUsize::new(0));
        let s = FinalObserved {
            inner: f.schemes[0].clone(),
            native: native_calls.clone(),
            extension: companion_calls.clone(),
            fail_native: Arc::new(AtomicBool::new(false)),
        };
        let c = final_context();
        let accepted = capture(&s, 1);
        let current = Context {
            round: accepted.statement.proposal.round,
            leader: s.participants()[usize::from(accepted.leader)].clone(),
            parent: (accepted.statement.proposal.parent, accepted.native_parent),
        };
        let mut ledger = Ledger::default();
        let reservation = <FinalProbe as Voting<FinalObserved, D>>::stage_final_reservation(
            &s,
            &c,
            &mut context,
            &mut ledger,
            &accepted.statement.proposal,
            Some(&current),
            &accepted,
        )
        .unwrap()
        .unwrap();
        assert_eq!(c.staged.load(Ordering::SeqCst), 1);
        let cache = CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(10));
        let mut journal = Journal::<_, ArtifactWith<FinalObserved, D, FinalProbe>>::init(
            context.child("journal"),
            journal_config!(s, cache, "joint-current"),
        )
        .await
        .unwrap();
        for artifact in [
            ArtifactWith::Notarization(peer_nqc(&f, accepted.statement.proposal.clone())),
            ArtifactWith::Certification(accepted.statement.proposal.round, true),
            ArtifactWith::Recovery(reservation),
        ] {
            journal = journal.append(1, &artifact).await.unwrap().0;
        }
        journal = journal.sync(1).await.unwrap();
        assert_eq!(native_calls.load(Ordering::SeqCst), 0);
        assert_eq!(companion_calls.load(Ordering::SeqCst), 0);
        let mut wrong = current.clone();
        wrong.parent.1 = D::from([99; 32]);
        assert!(
            <FinalProbe as Voting<FinalObserved, D>>::sign_finalize_current(
                &s,
                &c,
                &mut context,
                &mut ledger,
                accepted.statement.proposal.clone(),
                Some(&wrong),
                accepted.clone(),
            )
            .is_none()
        );
        assert_eq!(native_calls.load(Ordering::SeqCst), 0);
        assert_eq!(companion_calls.load(Ordering::SeqCst), 0);
        let (pair, receipt) = <FinalProbe as Voting<FinalObserved, D>>::sign_finalize_current(
            &s,
            &c,
            &mut context,
            &mut ledger,
            accepted.statement.proposal.clone(),
            Some(&current),
            accepted.clone(),
        )
        .unwrap();
        assert_eq!(pair.capture, accepted);
        assert!(FinalProbe::verify_finalize(
            &pair,
            &mut context,
            &s,
            &Sequential
        ));
        assert_eq!(native_calls.load(Ordering::SeqCst), 1);
        assert_eq!(companion_calls.load(Ordering::SeqCst), 1);
        journal = journal
            .append(1, &ArtifactWith::Recovery(receipt.unwrap()))
            .await
            .unwrap()
            .0;
        journal = journal
            .append(1, &ArtifactWith::Finalize(pair))
            .await
            .unwrap()
            .0;
        journal = journal.sync(1).await.unwrap();
        drop(journal);
    });
}

#[test]
fn joint_final_partial_signer_failure_retires_actor_and_replays_unsigned_authority() {
    for fenced in [false, true] {
        deterministic::Runner::new(
            deterministic::Config::new()
                .with_timeout(Some(Duration::from_secs(20)))
                .with_catch_panics(true),
        )
        .start(move |mut context| async move {
            let n = 10u32;
            let f = ed25519::fixture(
                &mut context,
                b"_COMMONWARE_CONSENSUS_JOINT_FINAL_PARTIAL_TEST",
                n,
            );
            let native = Arc::new(AtomicUsize::new(0));
            let companion = Arc::new(AtomicUsize::new(0));
            let fail_native = Arc::new(AtomicBool::new(true));
            let s = FinalObserved {
                inner: f.schemes[0].clone(),
                native: native.clone(),
                extension: companion.clone(),
                fail_native: fail_native.clone(),
            };
            let cache = CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(10));
            let accepted = capture(&s, 1);
            let c = final_context();
            let e = evidence(accepted.clone());
            let (mut actor, _) = ActorWith::new_with(
                context.child("failed_owner"),
                config!(s, cache, "joint-partial", n),
                c.clone(),
                e.clone(),
            );
            actor.state.set_genesis(D::from([0; 32]));
            let cert = peer_nqc(&f, proposal(1));
            actor.state.add_notarization(cert.clone());
            actor
                .state
                .replay(&ArtifactWith::Certification(proposal(1).round, true));
            actor.journal = Some(
                Journal::init(
                    actor.context.child("journal"),
                    journal_config!(s, cache, "joint-partial"),
                )
                .await
                .unwrap(),
            );
            actor = actor.append_journal(ArtifactWith::Notarization(cert)).await;
            actor = actor
                .append_journal(ArtifactWith::Certification(proposal(1).round, true))
                .await;
            actor = actor.sync_journal().await;
            // The companion signer succeeds. The native signer then returns
            // None, so the hook must retire this Actor instead of returning a
            // recoverable refusal or publishing a half-pair.
            let handle = context
                .child("partial_release")
                .spawn(|_| actor.prepare_finalize(View::new(1)));
            assert!(
                handle.await.is_err(),
                "partial signing failure must retire owner"
            );
            assert_eq!(companion.load(Ordering::SeqCst), 1);
            assert_eq!(
                native.load(Ordering::SeqCst),
                1,
                "one refused native attempt"
            );
            assert_eq!(c.staged.load(Ordering::SeqCst), 1);
            assert_eq!(e.calls.load(Ordering::SeqCst), 1);
            let journal = Journal::<_, ArtifactWith<FinalObserved, D, FinalProbe>>::init(
                context.child("inspect_failed_owner"),
                journal_config!(s, cache, "joint-partial"),
            )
            .await
            .unwrap();
            let mut replay = journal
                .replay(0, 0, NZUsize!(4096), ReadOptions::DONT_CACHE)
                .await
                .unwrap();
            let mut reservations = 0;
            while let Some(item) = replay.next().await {
                match item.unwrap().3 {
                    ArtifactWith::Recovery(wal) => {
                        assert_eq!(wal.kind, 0, "no paired receipt may be fabricated");
                        assert!(wal.frame.is_empty());
                        assert_eq!(wal.capture, accepted);
                        reservations += 1;
                    }
                    ArtifactWith::Finalize(_) => std::panic!("partial pair was published to WAL"),
                    _ => {}
                }
            }
            assert_eq!(reservations, 1, "unsigned authority remains durable");
            let mut journal = replay.finish().unwrap();
            if fenced {
                journal = journal
                    .append(
                        1,
                        &ArtifactWith::Recovery(Wal {
                            capture: accepted.clone(),
                            kind: 2,
                            frame: Bytes::new(),
                        }),
                    )
                    .await
                    .unwrap()
                    .0;
                journal = journal.sync(1).await.unwrap();
            }
            drop(journal);
            // A fresh owner/ledger reconstructs the exact reservation from WAL.
            // Only the test signer failure is removed; no old State is reused.
            fail_native.store(false, Ordering::SeqCst);
            native.store(0, Ordering::SeqCst);
            companion.store(0, Ordering::SeqCst);
            let fresh = evidence(accepted.clone());
            let fresh_context = final_context();
            let (network, oracle) = Network::new_with_peers(
                context.child("network"),
                NConfig {
                    max_size: 1024 * 1024,
                    max_peers_per_set: NonZeroUsize::new(n as usize).unwrap(),
                    disconnect_on_block: true,
                    tracked_peer_sets: NZUsize!(1),
                },
                f.participants.clone(),
            )
            .await;
            network.start();
            let me = f.participants[0].clone();
            let (votes, _) = oracle
                .control(me.clone())
                .register(0, Quota::per_second(NZU32!(1000)))
                .await
                .unwrap();
            let (certificates, _) = oracle
                .control(me)
                .register(1, Quota::per_second(NZU32!(1000)))
                .await
                .unwrap();
            let (actor, _) = ActorWith::new_with(
                context.child("fresh_owner"),
                config!(s, cache, "joint-partial", n),
                fresh_context.clone(),
                fresh.clone(),
            );
            let (batcher_tx, mut batcher_rx) = mailbox::new(context.child("batcher"), NZUsize!(32));
            let (resolver_tx, _resolver_rx) = mailbox::new(context.child("resolver"), NZUsize!(32));
            let handle = actor.start(
                batcher::Mailbox::new(batcher_tx),
                resolver::Mailbox::new(resolver_tx),
                votes,
                certificates,
            );
            while !fresh.replayed.load(Ordering::SeqCst) {
                reschedule().await;
            }
            if fenced {
                assert_eq!(native.load(Ordering::SeqCst), 0);
                assert_eq!(companion.load(Ordering::SeqCst), 0);
                while let Some(message) = batcher_rx.recv().now_or_never().flatten() {
                    assert!(!matches!(
                        message,
                        batcher::Message::Constructed(VoteWith::Finalize(_))
                    ));
                }
            } else {
                let pair = loop {
                    if let batcher::Message::Constructed(VoteWith::Finalize(pair)) =
                        batcher_rx.recv().await.unwrap()
                    {
                        break pair;
                    }
                };
                assert_eq!(pair.capture, accepted);
                assert!(FinalProbe::verify_finalize(
                    &pair,
                    &mut context,
                    &s,
                    &Sequential
                ));
                assert_eq!(native.load(Ordering::SeqCst), 1);
                assert_eq!(companion.load(Ordering::SeqCst), 1);
            }
            assert_eq!(fresh.calls.load(Ordering::SeqCst), 0);
            assert_eq!(fresh_context.staged.load(Ordering::SeqCst), 0);
            handle.abort();
            let _ = handle.await;
        });
    }
}
