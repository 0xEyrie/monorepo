//! The live voter mailbox must not release recovery signatures before sync.
use super::*;
use crate::simplex::{
    extension::{
        recovery::{Promise, Proof, Status},
        request::{Command, Query, Request as RecoveryRequest, Response},
    },
    types::Nullify,
};

#[test]
fn live_recovery_replies_wait_for_native_journal_sync() {
    exercise(false, false, false, false, false, false);
    exercise(true, false, false, false, false, false);
}
#[test]
fn cancelled_recovery_receiver_does_not_undo_the_persisted_promise() {
    exercise(false, true, false, false, false, false);
}
#[test]
#[should_panic(expected = "unable to sync journal")]
fn failed_native_recovery_sync_stops_the_voter() {
    exercise(false, false, true, false, false, false);
}
#[test]
fn live_native_coordinator_queries_prepare_requests_without_releasing_votes() {
    exercise(true, false, false, true, false, false);
}
#[test]
fn live_native_free_choice_recovers_when_original_leader_left_no_selection() {
    exercise(true, false, false, true, true, false);
}
#[test]
fn higher_native_promise_revokes_admitted_accept_before_dispatch() {
    exercise(true, false, false, true, true, true);
}
fn exercise(
    hold_accept: bool,
    cancel: bool,
    fail: bool,
    planning: bool,
    free: bool,
    supersede: bool,
) {
    deterministic::Runner::timed(Duration::from_secs(20)).start(move |mut context| async move {
        let f = ed25519::fixture(
            &mut context,
            b"_COMMONWARE_CONSENSUS_RECOVERY_ACTOR_TEST",
            6,
        );
        let elector = RoundRobin::<Sha256>::default().build(f.schemes[0].participants());
        let ballot = Rnd::new(Epoch::new(1), View::new(2));
        let leader = elector.elect(ballot, None);
        let local = if planning { usize::from(leader) } else { 0 };
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
        let me = f.participants[local].clone();
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
        let cfg = Config {
            scheme: f.schemes[local].clone(),
            elector,
            blocker: NoopBlocker::default(),
            automaton: app.clone(),
            relay: app,
            reporter: recorder.clone(),
            partition: "recovery_actor".into(),
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
        assert!(
            input
                .prepare_recovery(Query::Discover)
                .await
                .unwrap()
                .is_none()
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
        if !free {
            evidence.0.lock().insert(View::new(1), first.clone());
            input.interpretation_ready(View::new(1));
            assert_eq!(finalized(&mut batcher_rx, View::new(1)).await, first);
        }
        assert!(
            input
                .prepare_recovery(Query::Discover)
                .await
                .unwrap()
                .is_none()
        );
        let mut admission_subject = first.clone();
        admission_subject.ballot = ballot;
        let admission_proof = Proof {
            statuses: f
                .schemes
                .iter()
                .take(5)
                .map(|scheme| {
                    Status::sign(
                        scheme,
                        Promise {
                            proposal: first.proposal.clone(),
                            domain: first.domain,
                            ballot,
                            accepted: (!free).then(|| (first.ballot, first.value::<Sha256>())),
                        },
                    )
                    .unwrap()
                })
                .collect(),
        };
        let admission_request = RecoveryRequest::sign(
            &f.schemes[usize::from(leader)],
            Command::Accept(admission_subject.clone()),
            Some(admission_proof.clone()),
        )
        .unwrap();
        // No live admission before the native failure deadline or local promise.
        assert!(
            !input
                .validate_recovery(admission_request.clone())
                .await
                .unwrap()
        );
        context.sleep(Duration::from_millis(1100)).await;
        assert!(
            !input
                .validate_recovery(admission_request.clone())
                .await
                .unwrap()
        );
        let promise = RecoveryRequest::sign(
            &f.schemes[usize::from(leader)],
            Command::Promise {
                proposal: proposal(1),
                domain: first.domain,
                ballot,
            },
            None,
        )
        .unwrap();
        let discovered = input.prepare_recovery(Query::Discover).await.unwrap();
        if planning {
            let found = discovered.unwrap();
            assert_eq!(found.command.proposal(), promise.command.proposal());
            assert_eq!(found.command.ballot(), promise.command.ballot());
            assert!(found.verify(&mut context, &f.verifier, &Sequential));
        }
        let request = if hold_accept {
            let reply = input
                .recover_extension(promise.clone())
                .await
                .unwrap()
                .unwrap();
            let Response::Status { status, .. } = reply else {
                core::panic!("expected status")
            };
            assert!(status.verify(&mut context, &f.verifier, &Sequential));
            assert!(!input.validate_recovery(promise.clone()).await.unwrap());
            // A valid signature/proof from a non-elected participant grants no
            // admission. The genuine elected request is checked independently.
            let other = (usize::from(leader) + 1) % f.schemes.len();
            let wrong_leader = RecoveryRequest::sign(
                &f.schemes[other],
                admission_request.command.clone(),
                admission_request.proof.clone(),
            )
            .unwrap();
            assert!(wrong_leader.verify(&mut context, &f.verifier, &Sequential));
            assert!(!input.validate_recovery(wrong_leader).await.unwrap());
            let mut wrong_parent = admission_subject.clone();
            wrong_parent.parent = D::from([31; 32]);
            let wrong_parent = RecoveryRequest::sign(
                &f.schemes[usize::from(leader)],
                Command::Accept(wrong_parent),
                Some(admission_proof.clone()),
            )
            .unwrap();
            assert!(!input.validate_recovery(wrong_parent).await.unwrap());
            let mut short_proof = admission_proof.clone();
            short_proof.statuses.pop();
            let short = RecoveryRequest::sign(
                &f.schemes[usize::from(leader)],
                admission_request.command.clone(),
                Some(short_proof),
            )
            .unwrap();
            assert!(!input.validate_recovery(short).await.unwrap());
            assert!(
                input
                    .validate_recovery(admission_request.clone())
                    .await
                    .unwrap()
            );
            if free {
                assert!(
                    evidence.0.lock().is_empty(),
                    "native admission precedes application material"
                );
                let mut alternate = admission_subject.clone();
                alternate.extension = D::from([32; 32]);
                let alternate = RecoveryRequest::sign(
                    &f.schemes[usize::from(leader)],
                    Command::Accept(alternate),
                    Some(admission_proof.clone()),
                )
                .unwrap();
                // Read-only admission cannot freeze a choice: another permitted
                // value still passes, and no application free-choice callback ran.
                assert!(input.validate_recovery(alternate).await.unwrap());
                assert!(evidence.3.lock().is_empty());
            }
            assert!(
                input
                    .validate_recovery(admission_request.clone())
                    .await
                    .unwrap()
            );
            if supersede {
                // The preceding true reply came from the live voter's admission
                // handler. Advance native state while application custody would
                // be pending; the later request must not reuse that observation.
                let nullifies = f
                    .schemes
                    .iter()
                    .take(5)
                    .map(|scheme| Nullify::sign::<D>(scheme, ballot).unwrap())
                    .collect::<Vec<_>>();
                let certificate = Nullification::from_nullifies(
                    &f.verifier,
                    non_empty![@&nullifies],
                    &Sequential,
                )
                .unwrap();
                assert!(certificate.verify::<_, D>(&mut context, &f.verifier, &Sequential));
                input.recovered(CertificateWith::Nullification(certificate));
                let next_ballot = Rnd::new(ballot.epoch(), ballot.view().next());
                let next_elector =
                    <RoundRobin<Sha256> as crate::simplex::elector::Config<S>>::build(
                        RoundRobin::default(),
                        f.schemes[0].participants(),
                    );
                let next_leader = next_elector.elect(next_ballot, None);
                let next_promise = RecoveryRequest::sign(
                    &f.schemes[usize::from(next_leader)],
                    Command::Promise {
                        proposal: first.proposal.clone(),
                        domain: first.domain,
                        ballot: next_ballot,
                    },
                    None,
                )
                .unwrap();
                let Response::Status { status, accepted } = input
                    .recover_extension(next_promise)
                    .await
                    .unwrap()
                    .unwrap()
                else {
                    core::panic!("expected higher native promise");
                };
                assert_eq!(status.promise.proposal, first.proposal);
                assert_eq!(status.promise.domain, first.domain);
                assert_eq!(status.promise.ballot, next_ballot);
                assert_eq!(status.promise.accepted, None);
                assert_eq!(accepted, None);
                assert!(status.verify(&mut context, &f.verifier, &Sequential));
                // Make the original material available: refusal must be caused
                // by the new native fence, not by missing application evidence.
                evidence.0.lock().insert(View::new(1), first.clone());
                assert!(evidence.clone().accepts_recovery(&admission_subject));
                assert!(
                    !input
                        .validate_recovery(admission_request.clone())
                        .await
                        .unwrap()
                );
                assert!(
                    input
                        .recover_extension(admission_request)
                        .await
                        .unwrap()
                        .is_none()
                );
                assert!(evidence.3.lock().is_empty());
                handle.abort();
                let _ = handle.await;
                inspect(context, cache, &f, false).await;
                return;
            }
            let mut subject = first.clone();
            subject.ballot = ballot;
            let proof = Proof {
                statuses: f
                    .schemes
                    .iter()
                    .take(5)
                    .map(|scheme| {
                        Status::sign(
                            scheme,
                            Promise {
                                proposal: proposal(1),
                                domain: first.domain,
                                ballot,
                                accepted: (!free).then(|| (first.ballot, first.value::<Sha256>())),
                            },
                        )
                        .unwrap()
                    })
                    .collect(),
            };
            if planning {
                let responses: Vec<_> = proof
                    .statuses
                    .iter()
                    .cloned()
                    .map(|status| Response::Status {
                        status,
                        accepted: (!free).then(|| first.clone()),
                    })
                    .collect();
                if free {
                    // Insufficient statuses cannot authorize application work.
                    assert!(
                        input
                            .prepare_recovery(Query::Accept {
                                promise: promise.clone(),
                                responses: responses[..4].to_vec(),
                            })
                            .await
                            .unwrap()
                            .is_none()
                    );
                    assert!(evidence.3.lock().is_empty());
                    // Valid free-choice proof is announced without waiting for
                    // absent application material, and creates no signed vote.
                    assert!(
                        input
                            .prepare_recovery(Query::Accept {
                                promise: promise.clone(),
                                responses: responses.clone(),
                            })
                            .await
                            .unwrap()
                            .is_none()
                    );
                    let choices = evidence.3.lock().clone();
                    assert_eq!(choices.len(), 1);
                    let choice = &choices[0];
                    assert_eq!(choice.proposal, first.proposal);
                    assert_eq!(choice.domain, first.domain);
                    assert_eq!(choice.ballot, ballot);
                    assert_eq!(choice.parent, first.parent);
                    assert_eq!(choice.leader, leader);
                    assert!(
                        choice
                            .proof
                            .verify(&mut context, &f.verifier, &subject, &Sequential)
                            .unwrap()
                            .forced_value()
                            .is_none()
                    );
                    // Fixture stands in for a separately persisted/authenticated
                    // application selection. Native still checks and journals it.
                    evidence.0.lock().insert(View::new(1), first.clone());
                }
                let request = input
                    .prepare_recovery(Query::Accept {
                        promise: promise.clone(),
                        responses,
                    })
                    .await
                    .unwrap()
                    .unwrap();
                if !free {
                    assert!(
                        evidence.3.lock().is_empty(),
                        "forced values never authorize free choice"
                    );
                }
                request
            } else {
                RecoveryRequest::sign(
                    &f.schemes[usize::from(leader)],
                    Command::Accept(subject),
                    Some(proof),
                )
                .unwrap()
            }
        } else {
            promise.clone()
        };
        pending.arm();
        let mut reply = input.recover_extension(request);
        let sync = next_pending_sync(&pending);
        sync.blocked.await.unwrap();
        assert!(
            (&mut reply).now_or_never().is_none(),
            "no reply before native sync"
        );
        if fail {
            sync.release
                .send(Err(commonware_runtime::Error::Closed))
                .unwrap();
            let _ = reply.await;
            let _ = handle.await;
            core::panic!("voter survived a failed journal sync");
        }
        if cancel {
            drop(reply);
        } else {
            sync.release.send(Ok(())).unwrap();
            let response = reply.await.unwrap().unwrap();
            match response {
                Response::Status { status, accepted } => {
                    assert!(!hold_accept);
                    assert!(status.verify(&mut context, &f.verifier, &Sequential));
                    assert_eq!(accepted, Some(first.clone()));
                }
                Response::Vote(vote) => {
                    assert!(hold_accept);
                    assert_eq!(vote.statement.ballot, ballot);
                    assert!(vote.verify(&mut context, &f.verifier, &Sequential));
                }
            }
            // The gate is consumed; subsequent syncs proceed immediately.
            pending.unblock();
            if free {
                let mut alternate = admission_subject.clone();
                alternate.extension = D::from([32; 32]);
                let conflicting = RecoveryRequest::sign(
                    &f.schemes[usize::from(leader)],
                    Command::Accept(alternate),
                    Some(admission_proof.clone()),
                )
                .unwrap();
                // The same free proof was admissible before acceptance; now the
                // native same-ballot fence rejects both preflight and staging.
                assert!(!input.validate_recovery(conflicting.clone()).await.unwrap());
                assert!(
                    input
                        .recover_extension(conflicting)
                        .await
                        .unwrap()
                        .is_none()
                );
                assert!(
                    input
                        .validate_recovery(admission_request.clone())
                        .await
                        .unwrap()
                );
            }
            handle.abort();
            let _ = handle.await;
            inspect(context, cache, &f, hold_accept).await;
            return;
        }
        sync.release.send(Ok(())).unwrap();
        pending.unblock();
        let response = input.recover_extension(promise).await.unwrap().unwrap();
        let Response::Status { status, accepted } = response else {
            core::panic!("expected retried status")
        };
        assert_eq!(accepted, Some(first));
        assert!(status.verify(&mut context, &f.verifier, &Sequential));
        handle.abort();
        let _ = handle.await;
        inspect(context, cache, &f, false).await;
    });
}
async fn inspect(context: deterministic::Context, cache: CacheRef, f: &Fixture<S>, accepted: bool) {
    let journal = Journal::<_, ArtifactWith<S, D, Extended>>::init(
        context.child("inspect"),
        JConfig {
            partition: "recovery_actor".into(),
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
    let mut promises = 0;
    let mut accepts = 0;
    while let Some(record) = reader.next().await {
        if let ArtifactWith::Recovery(record) = record.unwrap().3 {
            match record {
                crate::simplex::phase2::recovery::Record::Promise { .. } => promises += 1,
                crate::simplex::phase2::recovery::Record::Accept(_) => accepts += 1,
            }
        }
    }
    let _ = reader.finish().unwrap();
    assert!(promises > 0);
    assert_eq!(accepts, usize::from(accepted));
}

#[test]
fn recovery_overflow_is_bounded_without_dropping_normal_readiness() {
    use commonware_actor::mailbox::{Overflow as _, Policy as _};
    deterministic::Runner::default().start(|mut context| async move {
        let f = ed25519::fixture(
            &mut context,
            b"_COMMONWARE_CONSENSUS_RECOVERY_OVERFLOW_TEST",
            6,
        );
        let mut pending = super::super::super::ingress::Pending::<S, D, Extended>::default();
        let mut responses = Vec::new();
        for view in 1..=100 {
            let p = proposal(view);
            let request = RecoveryRequest::sign(
                &f.schemes[0],
                Command::Promise {
                    domain: D::from([8; 32]),
                    ballot: Rnd::new(p.round.epoch(), p.round.view().next()),
                    proposal: p,
                },
                None,
            )
            .unwrap();
            let (reply, rx) = oneshot::channel();
            Message::handle(
                &mut pending,
                Message::Recovery {
                    span: tracing::Span::none(),
                    request,
                    reply,
                },
            );
            responses.push(rx);
        }
        Message::handle(
            &mut pending,
            Message::InterpretationReady {
                span: tracing::Span::none(),
                view: View::new(1),
            },
        );
        let mut retained = 0;
        let mut ready = false;
        pending.drain(|message| {
            match message {
                Message::Recovery { reply, .. } => {
                    retained += 1;
                    let _ = reply.send(None);
                }
                Message::InterpretationReady { .. } => ready = true,
                _ => core::panic!("unexpected message"),
            };
            None
        });
        assert!(ready);
        assert_eq!(retained, 16);
        for (i, rx) in responses.into_iter().enumerate() {
            if i < retained {
                assert!(rx.await.unwrap().is_none());
            } else {
                assert!(rx.await.is_err());
            }
        }
    });
}
