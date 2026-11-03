//! Old original finality remains usable after proposal-admission evidence retires.
use super::*;
use crate::simplex::phase2::Mode as _;

#[test]
fn stale_original_finality_needs_exact_parent_but_not_retired_nullification() {
    deterministic::Runner::timed(Duration::from_secs(20)).start(|mut context| async move {
        let fixture = ed25519::fixture(
            &mut context,
            b"_COMMONWARE_CONSENSUS_RETIRED_FINALITY_ANCESTRY_TEST",
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
        let evidence = Evidence::default();
        let recorder = Recorder::default();
        let app = App::default();
        // A non-signing receiver has no old nullification vote or proposal state.
        let (actor, mut input) = ActorWith::new_with(
            context.child("voter"),
            Config {
                scheme: fixture.verifier.clone(),
                elector: <RoundRobin<Sha256> as crate::simplex::elector::Config<S>>::build(
                    RoundRobin::default(),
                    fixture.verifier.participants(),
                ),
                blocker: NoopBlocker::default(),
                automaton: app.clone(),
                relay: app,
                reporter: recorder.clone(),
                partition: "retired_finality_ancestry".into(),
                epoch: Epoch::new(1),
                floor: FloorWith::Genesis(D::from([0; 32])),
                mailbox_size: NZUsize!(16),
                leader_timeout: Duration::from_secs(30),
                certification_timeout: Duration::from_secs(30),
                timeout_retry: Duration::from_secs(30),
                skip_budget: 6,
                view_retention: ViewDelta::new(16),
                replay_buffer: NZUsize!(4096),
                write_buffer: NZUsize!(4096),
                page_cache: cache.clone(),
            },
            ExtendedContext::new::<Sha256>(D::from([8; 32]), D::from([9; 32])),
            evidence.clone(),
        );
        let (batcher_tx, mut batcher_rx) = mailbox::new(context.child("batcher"), NZUsize!(16));
        let (resolver_tx, _resolver_rx) = mailbox::new(context.child("resolver"), NZUsize!(16));
        let handle = actor.start(
            batcher::Mailbox::new(batcher_tx),
            resolver::Mailbox::new(resolver_tx),
            votes,
            certificates,
        );
        // Future NQCs move the ordinary verification cursor beyond this old
        // finalization. All QCs use actual signatures; the application fixture
        // controls only retained interpretation availability, not native votes.
        input.recovered(CertificateWith::Notarization(notarization(&fixture, 11)));
        let _ = input
            .prepare_recovery(crate::simplex::extension::request::Query::Discover)
            .await
            .unwrap();
        let mut subject = statement(2, D::from([9; 32]));
        subject.proposal.parent = View::zero();
        let mut foreign = subject.clone();
        foreign.domain = D::from([77; 32]);
        let mut wrong_parent = subject.clone();
        wrong_parent.parent = D::from([77; 32]);
        for invalid in [foreign, wrong_parent] {
            evidence.0.lock().insert(View::new(2), invalid.clone());
            let proof = finalization(&mut context, &fixture, invalid);
            assert!(Extended::verify(
                &proof,
                &mut context,
                &fixture.verifier,
                &Sequential
            ));
            input.recovered(CertificateWith::Finalization(proof));
            let _ = input
                .prepare_recovery(crate::simplex::extension::request::Query::Discover)
                .await
                .unwrap();
            assert!(!recorder.0.lock().iter().any(|activity| matches!(
                activity,
                ActivityWith::Finalization(_) | ActivityWith::Finalize(_)
            )));
        }
        // A genuine child QC cannot replace its missing exact parent. This
        // second term-boundary gap also has no retained nullification (view 3).
        let mut child = statement(4, subject.value::<Sha256>());
        child.proposal.parent = View::new(2);
        evidence.0.lock().insert(View::new(4), child.clone());
        let child_proof = finalization(&mut context, &fixture, child.clone());
        assert!(Extended::verify(
            &child_proof,
            &mut context,
            &fixture.verifier,
            &Sequential
        ));
        input.recovered(CertificateWith::Finalization(child_proof.clone()));
        let _ = input
            .prepare_recovery(crate::simplex::extension::request::Query::Discover)
            .await
            .unwrap();
        assert!(!recorder.0.lock().iter().any(|activity| matches!(
            activity,
            ActivityWith::Finalization(_) | ActivityWith::Finalize(_)
        )));
        evidence.0.lock().insert(View::new(2), subject.clone());
        let proof = finalization(&mut context, &fixture, subject.clone());
        assert!(Extended::verify(
            &proof,
            &mut context,
            &fixture.verifier,
            &Sequential
        ));
        input.recovered(CertificateWith::Finalization(proof.clone()));
        let deadline = context.current() + Duration::from_secs(1);
        loop {
            if [&subject, &child].into_iter().all(|expected| {
                recorder.0.lock().iter().any(|activity| {
                    matches!(activity, ActivityWith::Finalization(c) if &c.certificate().statement == expected)
                })
            }) {
                break;
            }
            assert!(
                context.current() < deadline,
                "verified old finality remained blocked on retired nullification"
            );
            context.sleep(Duration::from_millis(1)).await;
        }
        input.recovered(CertificateWith::Finalization(proof));
        input.recovered(CertificateWith::Finalization(child_proof));
        let _ = input
            .prepare_recovery(crate::simplex::extension::request::Query::Discover)
            .await
            .unwrap();
        for expected in [&subject, &child] {
            assert_eq!(
                recorder
                    .0
                    .lock()
                    .iter()
                    .filter(|activity| matches!(
                        activity, ActivityWith::Finalization(c) if &c.certificate().statement == expected
                    ))
                    .count(),
                1
            );
        }
        while let Some(message) = batcher_rx.recv().now_or_never().flatten() {
            assert!(!matches!(message, batcher::Message::Constructed(_)));
        }
        handle.abort();
        let _ = handle.await;
        let journal = Journal::<_, ArtifactWith<S, D, Extended>>::init(
            context.child("inspect"),
            JConfig {
                partition: "retired_finality_ancestry".into(),
                compression: None,
                codec_config: fixture.verifier.certificate_codec_config(),
                page_cache: cache,
                write_buffer: NZUsize!(4096),
            },
        )
        .await
        .unwrap();
        let mut replay = journal
            .replay(0, 0, NZUsize!(4096), ReadOptions::DONT_CACHE)
            .await
            .unwrap();
        let mut finalizations = Vec::new();
        while let Some(record) = replay.next().await {
            match record.unwrap().3 {
                ArtifactWith::Finalization(c) => {
                    finalizations.push(c.certificate().statement.clone())
                }
                ArtifactWith::Nullification(_) => {
                    core::panic!("fixture unexpectedly supplied old nullification")
                }
                _ => {}
            }
        }
        replay.finish().unwrap();
        assert_eq!(finalizations, vec![subject, child]);
    });
}
