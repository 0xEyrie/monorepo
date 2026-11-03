//! Actual mailbox adoption retains the parent QC before dependent final voting.
use super::*;
use crate::simplex::extension::certificate::Recovered;
#[test]
fn recovered_parent_wakes_child_only_after_journal_sync() {
    exercise(false, false);
}
#[test]
#[should_panic(expected = "unable to sync journal")]
fn failed_recovered_parent_sync_stops_the_voter() {
    exercise(true, false);
}
#[test]
fn cancelled_recovered_parent_ack_preserves_durable_adoption() {
    exercise(false, true);
}
fn exercise(fail: bool, cancel: bool) {
    deterministic::Runner::timed(Duration::from_secs(20)).start(move |mut context| async move {
        let f = ed25519::fixture(
            &mut context,
            b"_COMMONWARE_CONSENSUS_RECOVERED_PARENT_ACTOR_TEST",
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
        let pending = PendingSyncs::default();
        pending.unblock();
        let actor_context = DelayedSyncContext {
            inner: context.child("voter"),
            pending: pending.clone(),
        };
        let cache = CacheRef::from_pooler(&actor_context, NZU16!(1024), NZUsize!(10));
        let evidence = Evidence::default();
        let app = App::default();
        let recorder = Recorder::default();
        let elector = RoundRobin::<Sha256>::default().build(f.schemes[0].participants());
        let cfg = Config {
            scheme: f.schemes[0].clone(),
            elector,
            blocker: NoopBlocker::default(),
            automaton: app.clone(),
            relay: app,
            reporter: recorder.clone(),
            partition: "recovered_parent_actor".into(),
            epoch: Epoch::new(1),
            floor: FloorWith::Genesis(D::from([0; 32])),
            mailbox_size: NZUsize!(8),
            leader_timeout: Duration::from_secs(10),
            certification_timeout: Duration::from_secs(1),
            timeout_retry: Duration::from_secs(10),
            skip_budget: 6,
            view_retention: ViewDelta::new(10),
            replay_buffer: NZUsize!(4096),
            write_buffer: NZUsize!(4096),
            page_cache: cache.clone(),
        };
        let (actor, mut input) = ActorWith::new_with(
            actor_context,
            cfg,
            ExtendedContext::new::<Sha256>(D::from([8; 32]), D::from([9; 32])),
            evidence.clone(),
        );
        let (batcher_tx, mut batcher_rx) = mailbox::new(context.child("batcher"), NZUsize!(8));
        let (resolver_tx, mut resolver_rx) = mailbox::new(context.child("resolver"), NZUsize!(8));
        let handle = actor.start(
            batcher::Mailbox::new(batcher_tx),
            resolver::Mailbox::new(resolver_tx),
            votes,
            certificates,
        );
        input.proposal(proposal(1));
        loop {
            if matches!(
                batcher_rx.recv().await.unwrap(),
                batcher::Message::Constructed(VoteWith::Notarize(_))
            ) {
                break;
            }
        }
        input.recovered(CertificateWith::Notarization(notarization(&f, 1)));
        certified(&mut resolver_rx, View::new(1)).await;
        let first = statement(1, D::from([9; 32]));
        evidence.0.lock().insert(View::new(1), first.clone());
        input.interpretation_ready(View::new(1));
        assert_eq!(finalized(&mut batcher_rx, View::new(1)).await, first);

        input.proposal(proposal(2));
        input.recovered(CertificateWith::Notarization(notarization(&f, 2)));
        certified(&mut resolver_rx, View::new(2)).await;
        let child = statement(2, first.value::<Sha256>());
        evidence.0.lock().insert(View::new(2), child.clone());
        input.interpretation_ready(View::new(2));
        context.sleep(Duration::from_millis(10)).await;
        while let Some(Some(message)) = batcher_rx.recv().now_or_never() {
            assert!(!matches!(
                message,
                batcher::Message::Constructed(VoteWith::Finalize(_))
            ));
        }
        let mut recovered_subject = first.clone();
        recovered_subject.ballot = Rnd::new(Epoch::new(1), View::new(3));
        let votes: Vec<_> = f
            .schemes
            .iter()
            .take(5)
            .map(|signer| ExtensionVote::sign(signer, recovered_subject.clone()).unwrap())
            .collect();
        let certificate = Recovered::new(
            ExtensionCertificate::from_votes(
                &mut context,
                &f.verifier,
                non_empty![@votes],
                &Sequential,
            )
            .unwrap(),
        )
        .unwrap();
        pending.arm();
        let mut ack = input.install_recovered(certificate.clone());
        let sync = next_pending_sync(&pending);
        sync.blocked.await.unwrap();
        assert!(
            evidence.1.lock().is_empty(),
            "no SDK notification before native sync"
        );
        assert!((&mut ack).now_or_never().is_none());
        while let Some(Some(message)) = batcher_rx.recv().now_or_never() {
            assert!(!matches!(
                message,
                batcher::Message::Constructed(VoteWith::Finalize(_))
            ));
        }
        assert!(
            !recorder
                .0
                .lock()
                .iter()
                .any(|a| matches!(a, ActivityWith::Finalization(_)))
        );
        if fail {
            sync.release
                .send(Err(commonware_runtime::Error::Closed))
                .unwrap();
            let _ = ack.await;
            let _ = handle.await;
            core::panic!("voter survived failed recovered parent persistence");
        }
        if cancel {
            drop(ack);
            sync.release.send(Ok(())).unwrap();
            pending.unblock();
        } else {
            sync.release.send(Ok(())).unwrap();
            pending.unblock();
            assert!(ack.await.unwrap());
        }
        assert_eq!(finalized(&mut batcher_rx, View::new(2)).await, child);
        assert_eq!(evidence.1.lock().first(), Some(&recovered_subject));
        assert!(
            input.install_recovered(certificate.clone()).await.unwrap(),
            "lost ACK may be retried"
        );
        assert!(
            !recorder
                .0
                .lock()
                .iter()
                .any(|a| matches!(a, ActivityWith::Finalization(_)))
        );
        handle.abort();
        let _ = handle.await;
        let journal = Journal::<_, ArtifactWith<S, D, Extended>>::init(
            context.child("inspect"),
            JConfig {
                partition: "recovered_parent_actor".into(),
                compression: None,
                codec_config: f.verifier.certificate_codec_config(),
                page_cache: cache,
                write_buffer: NZUsize!(4096),
            },
        )
        .await
        .unwrap();
        let mut reader = journal
            .replay(0, 0, NZUsize!(4096), ReadOptions::DONT_CACHE)
            .await
            .unwrap();
        let mut parents = 0;
        let mut children = 0;
        while let Some(record) = reader.next().await {
            match record.unwrap().3 {
                ArtifactWith::Recovered(c) => {
                    assert_eq!(c, certificate);
                    parents += 1;
                }
                ArtifactWith::Finalize(v) if v.view() == View::new(2) => {
                    assert_eq!(parents, 1);
                    children += 1;
                }
                ArtifactWith::Finalization(_) => core::panic!("recovery fabricated finality"),
                _ => {}
            }
        }
        drop(reader.finish().unwrap());
        assert_eq!((parents, children), (1, 1));
    });
}
