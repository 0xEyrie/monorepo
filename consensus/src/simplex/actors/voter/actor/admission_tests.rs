//! Native-anchor admission controls with a private Plain-shaped mode, not G1 activation.
use super::*;
use crate::simplex::{
    extension::agreement::general::Committee,
    phase2::{Plain, companion_probe as probe, voting::Voting},
    types::{Finalization as NativeFinalization, Finalize as NativeFinalize},
};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
type Admission = probe::AdmissionProbe;

#[derive(Clone, Default)]
struct AdmissionEvidence {
    ready: Arc<AtomicBool>,
    checked: Arc<AtomicUsize>,
    replayed: Arc<AtomicBool>,
}
impl Participation<S, D, Admission> for AdmissionEvidence {
    fn replayed(&mut self) {
        self.replayed.store(true, Ordering::SeqCst);
    }
    fn notarize(&mut self, vote: Notarize<S, D>) -> Notarize<S, D> {
        vote
    }
    fn final_subject(&mut self, _: &Proposal<D>) -> Option<()> {
        None
    }
    fn accepts_finalization(&mut self, _: &NativeFinalization<S, D>) -> bool {
        self.checked.fetch_add(1, Ordering::SeqCst);
        self.ready.load(Ordering::SeqCst)
    }
    fn accepts_replay(&mut self, _: &ArtifactWith<S, D, Admission>) -> bool {
        // Deliberately independent: replay acceptance is not application approval.
        true
    }
    fn prune(&mut self, _: View) {}
}
#[derive(Clone, Default)]
struct AdmissionSink(Arc<AtomicUsize>);
impl Reporter for AdmissionSink {
    type Activity = ActivityWith<S, D, Admission>;
    fn report(&mut self, activity: Self::Activity) -> Feedback {
        if matches!(activity, ActivityWith::Finalization(_)) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
        Feedback::Ok
    }
}
macro_rules! config {
    ($scheme:expr, $cache:expr, $partition:expr, $sink:expr) => {
        Config {
            scheme: $scheme.clone(),
            elector: RoundRobin::<Sha256>::default().build($scheme.participants()),
            blocker: NoopBlocker::default(),
            automaton: App::default(),
            relay: App::default(),
            reporter: $sink,
            partition: $partition.into(),
            epoch: Epoch::new(1),
            floor: FloorWith::Genesis(D::from([0; 32])),
            mailbox_size: NZUsize!(32),
            leader_timeout: Duration::from_secs(60),
            certification_timeout: Duration::from_secs(60),
            timeout_retry: Duration::from_secs(60),
            skip_budget: $scheme.participants().len() as u64,
            view_retention: ViewDelta::new(10),
            replay_buffer: NZUsize!(4096),
            write_buffer: NZUsize!(4096),
            page_cache: $cache.clone(),
        }
    };
}
macro_rules! journal_config {
    ($scheme:expr, $cache:expr, $partition:expr) => {
        JConfig {
            partition: $partition.into(),
            compression: None,
            codec_config: $scheme.certificate_codec_config(),
            page_cache: $cache.clone(),
            write_buffer: NZUsize!(4096),
        }
    };
}
fn peer_finalization(f: &Fixture<S>, p: Proposal<D>) -> NativeFinalization<S, D> {
    let q = Committee::new(f.schemes.len()).unwrap().quorum();
    let votes: Vec<_> = f
        .schemes
        .iter()
        .skip(1)
        .take(q)
        .map(|s| NativeFinalize::sign(s, p.clone()).unwrap())
        .collect();
    NativeFinalization::from_finalizes(&f.verifier, non_empty![@votes.iter()], &Sequential).unwrap()
}
fn peer_notarization(f: &Fixture<S>, p: Proposal<D>) -> Notarization<S, D> {
    let q = Committee::new(f.schemes.len()).unwrap().quorum();
    let votes: Vec<_> = f
        .schemes
        .iter()
        .skip(1)
        .take(q)
        .map(|s| Notarize::sign(s, p.clone()).unwrap())
        .collect();
    Notarization::from_notarizes(&f.verifier, non_empty![@votes.iter()], &Sequential).unwrap()
}

// 0 application unavailable; 1 wrong native anchor; 2 missing native ancestry.
fn live_admission(n: u32, case: u8) {
    deterministic::Runner::new(
        deterministic::Config::new().with_timeout(Some(Duration::from_secs(20))),
    )
    .start(move |mut context| async move {
        probe::reset_native_parents();
        probe::native_parent(View::zero(), &D::from([if case == 1 { 99 } else { 0 }; 32]));
        probe::native_parent(View::new(1), &proposal(1).payload);
        let f = ed25519::fixture(
            &mut context,
            b"_COMMONWARE_CONSENSUS_NATIVE_ADMISSION_TEST",
            n,
        );
        let cache = CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(10));
        let evidence = AdmissionEvidence::default();
        evidence.ready.store(case != 0, Ordering::SeqCst);
        let (mut actor, _) = ActorWith::new_with(
            context.child("voter"),
            config!(
                f.schemes[0],
                cache,
                "native-admission",
                AdmissionSink::default()
            ),
            (),
            evidence.clone(),
        );
        actor.state.set_genesis(D::from([0; 32]));
        actor.journal = Some(
            Journal::init(
                actor.context.child("journal"),
                journal_config!(f.schemes[0], cache, "native-admission"),
            )
            .await
            .unwrap(),
        );
        let target = if case == 2 { 2 } else { 1 };
        let qc = peer_finalization(&f, proposal(target));
        assert!(qc.verify(&mut context, &f.verifier, &Sequential));
        actor = actor.handle_finalization(qc).await;
        assert_eq!(actor.state.last_finalized(), View::zero());
        assert!(actor.pending_finalizations.contains_key(&View::new(target)));
        assert!(actor.dirty_section.is_none());
        assert!(evidence.checked.load(Ordering::SeqCst) > 0);
        if case == 0 {
            // A wake with no new evidence must not approve a certificate.
            (actor, _) = actor
                .process_message(Message::InterpretationReady {
                    span: Span::none(),
                    view: View::new(1),
                })
                .await;
            assert_eq!(actor.state.last_finalized(), View::zero());
            assert_eq!(evidence.checked.load(Ordering::SeqCst), 2);
            evidence.ready.store(true, Ordering::SeqCst);
        } else if case == 1 {
            assert!(probe::native_checks() > 0);
            probe::native_parent(View::zero(), &D::from([0; 32]));
        } else {
            // A genuine native parent is required even without an execution
            // interpretation. The parent section must sync before the child.
            actor = actor
                .handle_finalization(peer_finalization(&f, proposal(1)))
                .await;
            assert_eq!(actor.state.last_finalized(), View::new(1));
            let (tx, _rx) = mailbox::new(context.child("resolver"), NZUsize!(32));
            (actor, _) = actor
                .interpretation_dependents(&mut resolver::Mailbox::new(tx), View::new(1))
                .await;
        }
        if case != 2 {
            (actor, _) = actor
                .process_message(Message::InterpretationReady {
                    span: Span::none(),
                    view: View::new(1),
                })
                .await;
        }
        assert_eq!(actor.state.last_finalized(), View::new(target));
        assert!(actor.pending_finalizations.is_empty());
        actor = actor.sync_journal().await;
        drop(actor);
        let journal = Journal::<_, ArtifactWith<S, D, Admission>>::init(
            context.child("inspect"),
            journal_config!(f.schemes[0], cache, "native-admission"),
        )
        .await
        .unwrap();
        let mut replay = journal
            .replay(0, 0, NZUsize!(4096), ReadOptions::DONT_CACHE)
            .await
            .unwrap();
        let mut views = Vec::new();
        while let Some(record) = replay.next().await {
            if let ArtifactWith::Finalization(c) = record.unwrap().3 {
                views.push(c.view());
            }
        }
        assert_eq!(
            views,
            if case == 2 {
                vec![View::new(1), View::new(2)]
            } else {
                vec![View::new(1)]
            }
        );
        drop(replay.finish().unwrap());
    });
}
#[test]
fn native_anchor_mode_still_requires_application_admission_and_rechecks_wakes() {
    for n in [8, 10] {
        live_admission(n, 0);
    }
}
#[test]
fn native_anchor_mode_rejects_wrong_parent_then_rechecks_exact_anchor() {
    live_admission(10, 1);
}
#[test]
fn native_anchor_mode_waits_for_native_ancestry_without_execution_interpretation() {
    live_admission(8, 2);
}

#[test]
fn native_anchor_fresh_and_reserved_signing_recheck_native_parent() {
    deterministic::Runner::default().start(|mut context| async move {
        probe::reset_native_parents();
        probe::reset_voting();
        let f = ed25519::fixture(
            &mut context,
            b"_COMMONWARE_CONSENSUS_NATIVE_SIGN_ADMISSION_TEST",
            10,
        );
        let cache = CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(10));
        let (mut actor, _) = ActorWith::new_with(
            context.child("voter"),
            config!(
                f.schemes[0],
                cache,
                "sign-admission",
                AdmissionSink::default()
            ),
            (),
            AdmissionEvidence::default(),
        );
        actor.state.set_genesis(D::from([0; 32]));
        actor
            .state
            .add_notarization(peer_notarization(&f, proposal(1)));
        actor
            .state
            .replay(&ArtifactWith::Certification(proposal(1).round, true));
        probe::native_parent(View::zero(), &D::from([99; 32]));
        assert!(
            actor
                .state
                .construct_finalize_with(View::new(1), ())
                .is_none()
        );
        assert_eq!(probe::released(), 0);
        probe::native_parent(View::zero(), &D::from([0; 32]));
        actor.state.stage_finalize_with(View::new(1), ()).unwrap();
        assert_eq!(probe::staged(), 1);
        probe::native_parent(View::zero(), &D::from([99; 32]));
        assert!(
            actor
                .state
                .sign_reserved_finalize(View::new(1), ())
                .is_none()
        );
        assert_eq!(probe::released(), 0);
        probe::native_parent(View::zero(), &D::from([0; 32]));
        let (vote, _) = actor
            .state
            .sign_reserved_finalize(View::new(1), ())
            .unwrap();
        assert!(vote.verify(&mut context, &f.verifier, &Sequential));
        assert_eq!(probe::released(), 1);
    });
}

// 0 valid replay; 1 missing app evidence despite accepts_replay; 2 wrong anchor;
// 3 foreign epoch; 4 trusted sparse floor (no locally reconstructed parent).
fn restart_admission(case: u8) {
    deterministic::Runner::new(
        deterministic::Config::new()
            .with_timeout(Some(Duration::from_secs(20)))
            .with_catch_panics(true),
    )
    .start(move |mut context| async move {
        probe::reset_native_parents();
        probe::native_parent(View::zero(), &D::from([if case == 2 { 99 } else { 0 }; 32]));
        let n = 10;
        let f = ed25519::fixture(
            &mut context,
            b"_COMMONWARE_CONSENSUS_NATIVE_ADMISSION_REPLAY_TEST",
            n,
        );
        let cache = CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(10));
        let mut p = proposal(if case == 4 { 5 } else { 1 });
        if case == 3 {
            p.round = Rnd::new(Epoch::new(2), View::new(1));
        }
        let qc = peer_finalization(&f, p);
        assert!(qc.verify(&mut context, &f.verifier, &Sequential));
        if case != 4 {
            let journal = Journal::<_, ArtifactWith<S, D, Admission>>::init(
                context.child("seed"),
                journal_config!(f.schemes[0], cache, "admission-replay"),
            )
            .await
            .unwrap();
            let journal = journal
                .append(1, &ArtifactWith::Finalization(qc.clone()))
                .await
                .unwrap()
                .0;
            drop(journal.sync(1).await.unwrap());
        }
        let (network, oracle) = Network::new_with_peers(
            context.child("network"),
            NConfig {
                max_size: 1024 * 1024,
                max_peers_per_set: NZUsize!(10),
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
        let evidence = AdmissionEvidence::default();
        evidence.ready.store(case != 1, Ordering::SeqCst);
        let sink = AdmissionSink::default();
        let mut cfg = config!(f.schemes[0], cache, "admission-replay", sink.clone());
        if case == 4 {
            probe::reset_native_parents();
            cfg.floor = FloorWith::Finalized(qc);
        }
        let (actor, _) = ActorWith::new_with(context.child("reopen"), cfg, (), evidence.clone());
        let (batcher, _batcher_rx) = mailbox::new(context.child("batcher"), NZUsize!(32));
        let (resolver, _resolver_rx) = mailbox::new(context.child("resolver"), NZUsize!(32));
        let handle = actor.start(
            batcher::Mailbox::new(batcher),
            resolver::Mailbox::new(resolver),
            votes,
            certificates,
        );
        if matches!(case, 1..=3) {
            assert!(matches!(
                handle.await,
                Err(commonware_runtime::Error::Exited)
            ));
            assert!(!evidence.replayed.load(Ordering::SeqCst));
            assert_eq!(sink.0.load(Ordering::SeqCst), 0);
        } else {
            while !evidence.replayed.load(Ordering::SeqCst) {
                reschedule().await;
            }
            assert!(evidence.checked.load(Ordering::SeqCst) > 0);
            assert_eq!(sink.0.load(Ordering::SeqCst), 1);
            if case == 4 {
                assert_eq!(
                    probe::native_checks(),
                    0,
                    "trusted sparse floor is a separate bootstrap"
                );
            }
            handle.abort();
            let _ = handle.await;
        }
    });
}
#[test]
fn native_anchor_replay_requires_application_admission_even_if_accepts_replay_is_true() {
    restart_admission(1);
}
#[test]
fn native_anchor_replay_rechecks_exact_parent_and_epoch() {
    restart_admission(2);
    restart_admission(3);
}
#[test]
fn native_anchor_replay_accepts_exact_native_parent_without_execution_parent() {
    restart_admission(0);
}
#[test]
fn native_anchor_trusted_sparse_floor_keeps_separate_application_check() {
    restart_admission(4);
}
#[test]
fn native_anchor_admission_defaults_preserve_plain_and_extended() {
    const {
        assert!(!<Plain as Voting<S, D>>::REQUIRE_FINALIZATION_ADMISSION);
        assert!(<Extended as Voting<S, D>>::REQUIRE_FINALIZATION_ADMISSION);
        assert!(!<Admission as Voting<S, D>>::REQUIRE_PARENT_INTERPRETATION);
        assert!(<Admission as Voting<S, D>>::REQUIRE_FINALIZATION_ADMISSION);
    }
}
