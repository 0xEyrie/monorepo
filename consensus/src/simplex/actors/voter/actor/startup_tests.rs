//! Startup observation comes from completed native replay, not task construction.
use super::*;
use commonware_runtime::mocks::{DelayedReadContext, Gates};
use std::sync::atomic::{AtomicUsize, Ordering};

#[derive(Clone, Default)]
struct StartupEvidence {
    inner: Evidence,
    completed: Arc<AtomicUsize>,
}
impl Participation<S, D, Extended> for StartupEvidence {
    fn replayed(&mut self) {
        self.completed.fetch_add(1, Ordering::AcqRel);
    }
    fn notarize(&mut self, vote: Notarize<S, D>) -> report::Notarize<S, D> {
        self.inner.notarize(vote)
    }
    fn notarized(&mut self, certificate: &Notarization<S, D>) {
        self.inner.notarized(certificate);
    }
    fn final_subject(&mut self, proposal: &Proposal<D>) -> Option<Statement<D>> {
        self.inner.final_subject(proposal)
    }
    fn accepts_finalization(&mut self, certificate: &Finalization<S, D>) -> bool {
        self.inner.accepts_finalization(certificate)
    }
    fn accepts_replay(&mut self, artifact: &ArtifactWith<S, D, Extended>) -> bool {
        assert_eq!(self.completed.load(Ordering::Acquire), 0);
        self.inner.accepts_replay(artifact)
    }
    fn prune(&mut self, _: View) {}
}

#[derive(Clone, Copy)]
enum Failure {
    None,
    Read,
    Evidence,
}
fn exercise(failure: Failure) {
    deterministic::Runner::new(
        deterministic::Config::new()
            .with_timeout(Some(Duration::from_secs(20)))
            .with_catch_panics(true),
    )
    .start(move |mut context| async move {
        let fixture = ed25519::fixture(
            &mut context,
            b"_COMMONWARE_CONSENSUS_REPLAY_OBSERVATION_TEST",
            6,
        );
        let (network, oracle) = Network::new_with_peers(
            context.child("network"),
            NConfig {
                max_size: 1024 * 1024,
                max_peers_per_set: NZUsize!(6),
                disconnect_on_block: true,
                tracked_peer_sets: NZUsize!(1),
            },
            fixture.participants.clone(),
        )
        .await;
        network.start();
        let me = fixture.participants[0].clone();
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
        let cache = CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(10));
        let mut journal = Journal::<_, ArtifactWith<S, D, Extended>>::init(
            context.child("seed"),
            JConfig {
                partition: "replay_observation".into(),
                compression: None,
                codec_config: fixture.schemes[0].certificate_codec_config(),
                page_cache: cache.clone(),
                write_buffer: NZUsize!(4096),
            },
        )
        .await
        .unwrap();
        journal = journal
            .append(1, &ArtifactWith::Notarization(notarization(&fixture, 1)))
            .await
            .unwrap()
            .0;
        if matches!(failure, Failure::Evidence) {
            // Genuine certificate, deliberately unavailable application selection.
            // The native replay assertion must fail without publishing readiness.
            let certificate = finalization(&mut context, &fixture, statement(1, D::from([9; 32])));
            journal = journal
                .append(1, &ArtifactWith::Finalization(certificate))
                .await
                .unwrap()
                .0;
        }
        journal = journal.sync(1).await.unwrap();
        drop(journal);

        for attempt in 0..if matches!(failure, Failure::None) {
            2
        } else {
            1
        } {
            let gates = Gates::default();
            let gate = gates.arm();
            let evidence = StartupEvidence::default();
            let app = App::default();
            let (actor, mut input) = ActorWith::new_with(
                DelayedReadContext {
                    inner: context.child(if attempt == 0 {
                        "voter_first"
                    } else {
                        "voter_reopen"
                    }),
                    pending: gates,
                },
                Config {
                    scheme: fixture.schemes[0].clone(),
                    elector: RoundRobin::<Sha256>::default()
                        .build(fixture.schemes[0].participants()),
                    blocker: NoopBlocker::default(),
                    automaton: app.clone(),
                    relay: app,
                    reporter: Recorder::default(),
                    partition: "replay_observation".into(),
                    epoch: Epoch::new(1),
                    floor: FloorWith::Genesis(D::from([0; 32])),
                    mailbox_size: NZUsize!(8),
                    leader_timeout: Duration::from_secs(60),
                    certification_timeout: Duration::from_secs(60),
                    timeout_retry: Duration::from_secs(60),
                    skip_budget: 6,
                    view_retention: ViewDelta::new(10),
                    replay_buffer: NZUsize!(4096),
                    write_buffer: NZUsize!(4096),
                    page_cache: cache.clone(),
                },
                ExtendedContext::new::<Sha256>(D::from([8; 32]), D::from([9; 32])),
                evidence.clone(),
            );
            let (batcher_tx, _batcher_rx) = mailbox::new(
                context.child(if attempt == 0 {
                    "batcher_first"
                } else {
                    "batcher_reopen"
                }),
                NZUsize!(16),
            );
            let (resolver_tx, _resolver_rx) = mailbox::new(
                context.child(if attempt == 0 {
                    "resolver_first"
                } else {
                    "resolver_reopen"
                }),
                NZUsize!(16),
            );
            assert_eq!(evidence.completed.load(Ordering::Acquire), 0);
            let handle = actor.start(
                batcher::Mailbox::new(batcher_tx),
                resolver::Mailbox::new(resolver_tx),
                votes.clone(),
                certificates.clone(),
            );
            gate.blocked.await.unwrap();
            assert_eq!(
                evidence.completed.load(Ordering::Acquire),
                0,
                "entered journal read is still held"
            );
            assert!(evidence.inner.2.lock().is_empty());
            if matches!(failure, Failure::Read) {
                drop(gate.release);
            } else {
                gate.release.send(()).unwrap();
            }
            if !matches!(failure, Failure::None) {
                assert!(matches!(
                    handle.await,
                    Err(commonware_runtime::Error::Exited)
                ));
                assert_eq!(evidence.completed.load(Ordering::Acquire), 0);
                continue;
            }
            // The reply fences the live loop without assuming a fixed delay.
            input
                .prepare_recovery(crate::simplex::extension::request::Query::Discover)
                .await
                .unwrap();
            assert_eq!(evidence.completed.load(Ordering::Acquire), 1);
            assert_eq!(*evidence.inner.2.lock(), vec![proposal(1)]);
            input
                .prepare_recovery(crate::simplex::extension::request::Query::Discover)
                .await
                .unwrap();
            assert_eq!(
                evidence.completed.load(Ordering::Acquire),
                1,
                "once per actual voter instance"
            );
            handle.abort();
            let _ = handle.await;
        }
    });
}

#[test]
fn replayed_hook_waits_for_journal_and_fires_once_per_voter() {
    exercise(Failure::None);
}
#[test]
fn replayed_hook_is_absent_after_journal_read_failure() {
    exercise(Failure::Read);
}
#[test]
fn replayed_hook_is_absent_after_replay_evidence_rejection() {
    exercise(Failure::Evidence);
}
