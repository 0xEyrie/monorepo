//! Actual coordinator-loop retention tests with a controlled native mailbox.
//! The mailbox replies are fixture data, not proof of native voter eligibility.
use super::{AdmittedRecovery, Readiness};
use crate::{
    simplex::{
        actors::voter::{Mailbox, Message},
        extension::{
            coordinator::{self, RetainError},
            recovery::{Promise, Proof, Status},
            recovery_wire::Wire,
            request::{Command, Query, Request, Response},
            vote::Statement,
        },
        phase2::{Extended, voting::ExtendedContext},
        scheme::ed25519,
        types::Proposal,
    },
    types::{Epoch, Round, View},
};
use bytes::Bytes;
use commonware_actor::mailbox;
use commonware_codec::{Decode as _, Encode as _};
use commonware_cryptography::{
    certificate::Verifier as _,
    sha256::{Digest as D, Sha256},
};
use commonware_p2p::{
    Receiver as _, Recipients,
    simulated::{Config as NetworkConfig, Link, Network},
    utils::codec::WrappedSender,
};
use commonware_parallel::Sequential;
use commonware_runtime::{
    BufferPooler as _, Clock as _, Quota, Runner as _, Spawner as _, Supervisor as _, deterministic,
};
use commonware_utils::{NZU32, NZUsize, channel::oneshot, probability, sync::Mutex};
use std::{collections::VecDeque, sync::Arc, time::Duration};

type S = ed25519::Scheme;
#[derive(Clone, Copy)]
enum Finish {
    Release,
    Retry,
    Fail,
    Cancel,
    Capacity,
    Refuse,
}

#[test]
fn local_accept_waits_for_retention_without_blocking_peer_promises() {
    exercise(true, Finish::Release);
}
#[test]
fn peer_accept_waits_for_retention_without_blocking_peer_promises() {
    exercise(false, Finish::Release);
}
#[test]
fn unavailable_and_rejected_accepts_never_dispatch_and_can_retry() {
    exercise(true, Finish::Retry);
    exercise(false, Finish::Retry);
}
#[test]
fn failed_retention_ends_local_and_peer_coordinators() {
    exercise(true, Finish::Fail);
    exercise(false, Finish::Fail);
}
#[test]
fn cancelling_coordinator_drops_held_retention_without_native_dispatch() {
    exercise(true, Finish::Cancel);
    exercise(false, Finish::Cancel);
}

#[test]
fn held_peer_retention_stays_within_existing_pending_limit() {
    exercise(false, Finish::Capacity);
}

#[test]
fn native_admission_refusal_never_calls_custody_or_dispatches_accept() {
    exercise(true, Finish::Refuse);
    exercise(false, Finish::Refuse);
}

fn exercise(local: bool, finish: Finish) {
    deterministic::Runner::timed(Duration::from_secs(5)).start(move |mut context| async move {
        let f = ed25519::fixture(
            &mut context,
            b"_COMMONWARE_CONSENSUS_RECOVERY_RETENTION_TEST",
            6,
        );
        let domain = D::from([1; 32]);
        let parent = D::from([2; 32]);
        let proposal = Proposal::new(
            Round::new(Epoch::new(1), View::new(1)),
            View::zero(),
            D::from([3; 32]),
        );
        let ballot = Round::new(Epoch::new(1), View::new(2));
        let promise = Request::sign(
            &f.schemes[0],
            Command::Promise {
                proposal: proposal.clone(),
                domain,
                ballot,
            },
            None,
        )
        .unwrap();
        let statuses: Vec<_> = f.schemes[..5]
            .iter()
            .map(|scheme| {
                Status::sign(
                    scheme,
                    Promise {
                        proposal: proposal.clone(),
                        domain,
                        ballot,
                        accepted: None,
                    },
                )
                .unwrap()
            })
            .collect();
        let accept = Request::sign(
            &f.schemes[usize::from(!local)],
            Command::Accept(Statement {
                proposal: proposal.clone(),
                domain,
                ballot,
                parent,
                extension: D::from([4; 32]),
            }),
            Some(Proof {
                statuses: statuses.clone(),
            }),
        )
        .unwrap();
        let expected = accept.encode();
        let (network, oracle) = Network::new_with_peers(
            context.child("network"),
            NetworkConfig {
                max_size: 2 * 1024 * 1024,
                max_peers_per_set: NZUsize!(6),
                disconnect_on_block: true,
                tracked_peer_sets: NZUsize!(1),
            },
            f.participants.clone(),
        )
        .await;
        network.start();
        let me = f.participants[0].clone();
        let peer = f.participants[1].clone();
        let wire = oracle
            .control(me.clone())
            .register(0, Quota::per_second(NZU32!(1000)))
            .await
            .unwrap();
        let remote = oracle
            .control(peer.clone())
            .register(0, Quota::per_second(NZU32!(1000)))
            .await
            .unwrap();
        for (from, to) in [(me.clone(), peer.clone()), (peer, me.clone())] {
            oracle
                .add_link(
                    from,
                    to,
                    Link {
                        latency: Duration::ZERO,
                        jitter: Duration::ZERO,
                        success_rate: probability!(1.0),
                    },
                )
                .await
                .unwrap();
        }
        let mut sender =
            WrappedSender::<_, Wire<S, D>>::new(context.network_buffer_pool().clone(), remote.0);
        let mut receiver = remote.1;
        let (tx, mut inbox) = mailbox::new(context.child("mailbox"), NZUsize!(32));
        let ready = Readiness::<S, D, Extended> {
            mailbox: Mailbox::new(tx),
        };
        let requests = Arc::new(Mutex::new(Vec::<Bytes>::new()));
        let promises = Arc::new(Mutex::new(0usize));
        let admissions = Arc::new(Mutex::new(0usize));
        let admitted_count = admissions.clone();
        let observed = requests.clone();
        let promise_count = promises.clone();
        let queried_promise = promise.clone();
        let queried_accept = accept.clone();
        let status_scheme = f.schemes[0].clone();
        let voter = context
            .child("controlled_voter")
            .spawn(move |_| async move {
                while let Some(message) = inbox.recv().await {
                    match message {
                        Message::RecoveryQuery { query, reply, .. } => {
                            let value = if local {
                                Some(match query {
                                    Query::Discover => queried_promise.clone(),
                                    Query::Accept { responses, .. } => {
                                        assert_eq!(responses.len(), 5);
                                        queried_accept.clone()
                                    }
                                })
                            } else {
                                None
                            };
                            let _ = reply.send(value);
                        }
                        Message::RecoveryAdmission { request, reply, .. } => {
                            assert!(matches!(request.command, Command::Accept(_)));
                            *admitted_count.lock() += 1;
                            let _ = reply.send(!matches!(finish, Finish::Refuse));
                        }
                        Message::Recovery { request, reply, .. } => match request.command {
                            Command::Promise {
                                proposal,
                                domain,
                                ballot,
                            } => {
                                *promise_count.lock() += 1;
                                let status = Status::sign(
                                    &status_scheme,
                                    Promise {
                                        proposal,
                                        domain,
                                        ballot,
                                        accepted: None,
                                    },
                                )
                                .unwrap();
                                let _ = reply.send(Some(Response::Status {
                                    status,
                                    accepted: None,
                                }));
                            }
                            Command::Accept(_) => {
                                observed.lock().push(request.encode());
                                // No vote is fabricated by this dispatch fixture.
                                let _ = reply.send(None);
                            }
                        },
                        _ => panic!("unexpected controlled voter message"),
                    }
                }
            });
        let calls = Arc::new(Mutex::new(Vec::<Bytes>::new()));
        let gates = Arc::new(Mutex::new(VecDeque::new()));
        let mut releases = VecDeque::new();
        for _ in 0..8 {
            let (release, gate) = oneshot::channel();
            releases.push_back(release);
            gates.lock().push_back(gate);
        }
        let retained = calls.clone();
        let retain = move |admission: AdmittedRecovery<S, D>| {
            retained.lock().push(admission.request().encode());
            let gate = gates.lock().pop_front().expect("bounded test retries");
            async move { gate.await.unwrap_or(Err(RetainError::Failed)) }
        };
        let coordinator = coordinator::start(
            context.child("coordinator"),
            ready,
            f.schemes[0].clone(),
            coordinator::Config {
                epoch: Epoch::new(1),
                context: ExtendedContext::new::<Sha256>(domain, parent),
                retry: Duration::from_millis(10),
                attempt_timeout: Duration::from_secs(2),
                pending: 4,
                retained: 4,
            },
            wire,
            Sequential,
            retain,
        )
        .unwrap();
        if local {
            // Wait for the actual coordinator to enter status collection before
            // supplying the four peer statuses to its normal wire intake.
            loop {
                let (_, bytes) = receiver.recv().await.unwrap();
                if matches!(
                    Wire::<S, D>::decode_cfg(bytes, &(6, f.verifier.certificate_codec_config()))
                        .unwrap(),
                    Wire::Request(Request {
                        command: Command::Promise { .. },
                        ..
                    })
                ) {
                    break;
                }
            }
            for status in statuses.iter().skip(1) {
                sender.send(
                    Recipients::One(me.clone()),
                    Wire::Response(Response::Status {
                        status: status.clone(),
                        accepted: None,
                    }),
                    true,
                );
            }
        } else {
            sender.send(
                Recipients::One(me.clone()),
                Wire::Request(accept.clone()),
                true,
            );
        }
        if matches!(finish, Finish::Refuse) {
            while *admissions.lock() == 0 {
                context.sleep(Duration::from_millis(1)).await;
            }
            assert!(calls.lock().is_empty());
            assert!(requests.lock().is_empty());
            coordinator.abort();
            let _ = coordinator.await;
            voter.abort();
            let _ = voter.await;
            return;
        }
        while calls.lock().is_empty() {
            context.sleep(Duration::from_millis(1)).await;
        }
        assert_eq!(calls.lock()[0], expected);
        assert!(
            requests.lock().is_empty(),
            "Accept reached voter before retention"
        );
        // A held Accept future does not occupy the coordinator's whole loop.
        let before = *promises.lock();
        let unrelated = Request::sign(
            &f.schemes[1],
            Command::Promise {
                proposal: Proposal::new(
                    Round::new(Epoch::new(1), View::new(2)),
                    View::zero(),
                    D::from([9; 32]),
                ),
                domain,
                ballot: Round::new(Epoch::new(1), View::new(3)),
            },
            None,
        )
        .unwrap();
        sender.send(Recipients::One(me.clone()), Wire::Request(unrelated), true);
        while *promises.lock() == before {
            context.sleep(Duration::from_millis(1)).await;
        }
        assert_eq!(
            calls.lock().len(),
            1,
            "Promise must bypass material retention"
        );
        assert!(requests.lock().is_empty());
        match finish {
            Finish::Refuse => unreachable!("refused before retention"),
            Finish::Capacity => {
                context.sleep(Duration::from_millis(20)).await;
                for _ in 0..4 {
                    sender.send(
                        Recipients::One(me.clone()),
                        Wire::Request(accept.clone()),
                        true,
                    );
                }
                context.sleep(Duration::from_millis(40)).await;
                assert_eq!(
                    calls.lock().len(),
                    3,
                    "pending-1 peer futures must bound held callbacks"
                );
                assert!(requests.lock().is_empty());
                coordinator.abort();
                let _ = coordinator.await;
                for _ in 0..3 {
                    let mut release = releases.pop_front().unwrap();
                    release.closed().await;
                    assert!(release.send(Ok(())).is_err());
                }
            }
            Finish::Cancel => {
                let mut release = releases.pop_front().unwrap();
                coordinator.abort();
                let _ = coordinator.await;
                release.closed().await;
                assert!(release.send(Ok(())).is_err());
                assert!(requests.lock().is_empty());
            }
            Finish::Fail => {
                releases
                    .pop_front()
                    .unwrap()
                    .send(Err(RetainError::Failed))
                    .unwrap();
                assert!(matches!(
                    coordinator.await.unwrap(),
                    Err(coordinator::Error::Retention)
                ));
                assert!(requests.lock().is_empty());
            }
            Finish::Release | Finish::Retry => {
                if matches!(finish, Finish::Retry) {
                    for (n, error) in [RetainError::Unavailable, RetainError::Rejected]
                        .into_iter()
                        .enumerate()
                    {
                        releases.pop_front().unwrap().send(Err(error)).unwrap();
                        context.sleep(Duration::from_millis(20)).await;
                        assert!(requests.lock().is_empty());
                        if !local {
                            sender.send(
                                Recipients::One(me.clone()),
                                Wire::Request(accept.clone()),
                                true,
                            );
                        }
                        while calls.lock().len() < n + 2 {
                            context.sleep(Duration::from_millis(1)).await;
                        }
                    }
                }
                releases.pop_front().unwrap().send(Ok(())).unwrap();
                while requests.lock().is_empty() {
                    context.sleep(Duration::from_millis(1)).await;
                }
                assert_eq!(requests.lock().as_slice(), &[expected]);
                assert!(calls.lock().iter().all(|bytes| *bytes == accept.encode()));
                coordinator.abort();
                let _ = coordinator.await;
            }
        }
        voter.abort();
        let _ = voter.await;
    });
}

// These schedules exercise coordinator service, not voter eligibility. All
// Promise signatures are genuine; the controlled mailbox supplies native replies.
mod retry_bounds {
    use super::*;
    use commonware_actor::{Feedback, Unreliable};
    use commonware_cryptography::ed25519::PublicKey;
    use commonware_p2p::{CheckedSender, LimitedSender, Message as Packet, Receiver};
    use commonware_runtime::{IoBufs, utils::reschedule};
    use commonware_utils::channel::mpsc;
    use std::{future::pending, time::SystemTime};

    type SentMessages = Arc<Mutex<Vec<(SystemTime, Wire<S, D>)>>>;

    #[derive(Clone)]
    struct Sent {
        clock: Arc<deterministic::Context>,
        peer: PublicKey,
        messages: SentMessages,
    }
    impl LimitedSender for Sent {
        type PublicKey = PublicKey;
        type Checked<'a> = Self;
        fn check(&mut self, _: Recipients<PublicKey>) -> Result<Self, SystemTime> {
            Ok(self.clone())
        }
    }
    impl CheckedSender for Sent {
        type PublicKey = PublicKey;
        fn recipients(&self) -> Vec<PublicKey> {
            vec![self.peer.clone()]
        }
        fn send(self, bytes: impl Into<IoBufs> + Send, _: bool) -> Unreliable<Feedback> {
            let wire = Wire::<S, D>::decode_cfg(bytes.into(), &(6, 6)).unwrap();
            let mut messages = self.messages.lock();
            assert!(messages.len() < 512, "retry monopolized one task poll");
            messages.push((self.clock.current(), wire));
            Unreliable::new(Feedback::Ok)
        }
    }

    struct ReadyInput {
        incoming: mpsc::Receiver<Packet<PublicKey>>,
        polls: usize,
    }
    impl std::fmt::Debug for ReadyInput {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.debug_struct("ReadyInput").finish_non_exhaustive()
        }
    }
    impl Receiver for ReadyInput {
        type Error = std::io::Error;
        type PublicKey = PublicKey;
        async fn recv(&mut self) -> Result<Packet<PublicKey>, Self::Error> {
            // A finite termination guard makes a ready-timer spin fail without
            // depending on a timeout task that the spin could itself starve.
            self.polls += 1;
            assert!(self.polls < 512, "retry did not yield to independent work");
            match self.incoming.recv().await {
                Some(packet) => Ok(packet),
                None => pending().await,
            }
        }
    }

    struct InvalidWaves {
        clock: deterministic::Context,
        peer: PublicKey,
        sent: SentMessages,
        next: Option<SystemTime>,
        frames: usize,
        waves: usize,
        before: usize,
        observed: Arc<Mutex<Vec<(usize, usize)>>>,
        finished: Option<oneshot::Sender<()>>,
    }
    impl std::fmt::Debug for InvalidWaves {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.debug_struct("InvalidWaves").finish_non_exhaustive()
        }
    }
    impl Receiver for InvalidWaves {
        type Error = std::io::Error;
        type PublicKey = PublicKey;
        async fn recv(&mut self) -> Result<Packet<PublicKey>, Self::Error> {
            if self.frames == 0 {
                if self.waves == 0 {
                    if let Some(finished) = self.finished.take() {
                        let _ = finished.send(());
                    }
                    return pending().await;
                }
                if self.next.is_none() {
                    // The first send is the local Promise completion; the next
                    // is a genuine timer retransmission. Its timestamp fixes
                    // the next due tick without an intervening retry window.
                    while self.sent.lock().len() < 2 {
                        self.clock.sleep(Duration::from_millis(1)).await;
                    }
                    let sent = self.sent.lock();
                    self.before = sent.len();
                    self.next = Some(sent.last().unwrap().0 + Duration::from_millis(10));
                }
                // Both deadline and baseline survive cancellation. A correct
                // loop may service this tick before re-polling this receiver.
                self.clock.sleep_until(self.next.unwrap()).await;
                self.frames = 64;
                self.waves -= 1;
            }
            self.frames -= 1;
            if self.frames == 0 {
                let after = self.sent.lock().len();
                self.observed.lock().push((self.before, after));
                self.before = after;
                self.next = Some(self.next.unwrap() + Duration::from_millis(10));
            }
            Ok((self.peer.clone(), Bytes::from_static(&[255]).into()))
        }
    }

    fn config(retry: Duration) -> coordinator::Config<D> {
        coordinator::Config {
            epoch: Epoch::new(1),
            context: ExtendedContext::new::<Sha256>(D::from([1; 32]), D::from([2; 32])),
            retry,
            attempt_timeout: Duration::from_secs(2),
            pending: 4,
            retained: 4,
        }
    }

    fn promise(scheme: &S, view: u64) -> Request<S, D> {
        Request::sign(
            scheme,
            Command::Promise {
                proposal: Proposal::new(
                    Round::new(Epoch::new(1), View::new(view)),
                    View::zero(),
                    D::from([3; 32]),
                ),
                domain: D::from([1; 32]),
                ballot: Round::new(Epoch::new(1), View::new(view + 1)),
            },
            None,
        )
        .unwrap()
    }

    fn voter(
        context: deterministic::Context,
        scheme: S,
        observed: Arc<Mutex<Vec<View>>>,
    ) -> (Readiness<S, D, Extended>, commonware_runtime::Handle<()>) {
        let (tx, mut inbox) =
            mailbox::new::<Message<S, D, Extended>>(context.child("inbox"), NZUsize!(16));
        let local = promise(&scheme, 1);
        let task = context
            .child("controlled_voter")
            .spawn(move |_| async move {
                while let Some(message) = inbox.recv().await {
                    match message {
                        Message::RecoveryQuery {
                            query: Query::Discover,
                            reply,
                            ..
                        } => {
                            let _ = reply.send(Some(local.clone()));
                        }
                        Message::Recovery { request, reply, .. } => {
                            let Command::Promise {
                                proposal,
                                domain,
                                ballot,
                            } = request.command
                            else {
                                panic!("no Accept belongs to this schedule");
                            };
                            observed.lock().push(proposal.round.view());
                            let status = Status::sign(
                                &scheme,
                                Promise {
                                    proposal,
                                    domain,
                                    ballot,
                                    accepted: None,
                                },
                            )
                            .unwrap();
                            let _ = reply.send(Some(Response::Status {
                                status,
                                accepted: None,
                            }));
                        }
                        _ => panic!("unexpected controlled voter operation"),
                    }
                }
            });
        (
            Readiness {
                mailbox: Mailbox::new(tx),
            },
            task,
        )
    }

    #[test]
    fn due_recovery_retry_progresses_inside_finite_invalid_waves() {
        deterministic::Runner::timed(Duration::from_secs(2)).start(|mut context| async move {
            let f = ed25519::fixture(
                &mut context,
                b"_COMMONWARE_CONSENSUS_RECOVERY_RETRY_BOUND",
                6,
            );
            let (ready, voter) = voter(
                context.child("native"),
                f.schemes[0].clone(),
                Arc::default(),
            );
            let sent = Arc::new(Mutex::new(Vec::new()));
            let observed = Arc::new(Mutex::new(Vec::new()));
            let (finished, done) = oneshot::channel();
            let receiver = InvalidWaves {
                clock: context.child("waves"),
                peer: f.participants[1].clone(),
                sent: sent.clone(),
                next: None,
                frames: 0,
                waves: 2,
                before: 0,
                observed: observed.clone(),
                finished: Some(finished),
            };
            let task = coordinator::start(
                context.child("coordinator"),
                ready,
                f.schemes[0].clone(),
                config(Duration::from_millis(10)),
                (
                    Sent {
                        clock: Arc::new(context.child("sender_clock")),
                        peer: f.participants[1].clone(),
                        messages: sent.clone(),
                    },
                    receiver,
                ),
                Sequential,
                |_| async { panic!("Promise does not retain Accept material") },
            )
            .unwrap();
            done.await.unwrap();
            let waves = observed.lock().clone();
            assert_eq!(waves.len(), 2);
            assert!(
                waves.iter().all(|(before, after)| after > before),
                "due Promise retry lost every ready-wave turn: {waves:?}"
            );
            assert!(sent.lock().iter().all(|(_, wire)| matches!(
                wire,
                Wire::Request(Request {
                    command: Command::Promise { .. },
                    ..
                })
            )));
            task.abort();
            let _ = task.await;
            voter.abort();
            let _ = voter.await;
        });
    }

    #[test]
    fn expired_recovery_retry_services_ready_peer() {
        expired_retry(false);
    }

    #[test]
    fn expired_recovery_retry_yields_to_later_peer_and_stop() {
        expired_retry(true);
    }

    fn expired_retry(later: bool) {
        deterministic::Runner::timed(Duration::from_secs(2)).start(move |mut context| async move {
            let f = ed25519::fixture(
                &mut context,
                b"_COMMONWARE_CONSENSUS_RECOVERY_TINY_RETRY",
                6,
            );
            let observed = Arc::new(Mutex::new(Vec::new()));
            let (ready, voter) = voter(
                context.child("native"),
                f.schemes[0].clone(),
                observed.clone(),
            );
            let sent = Arc::new(Mutex::new(Vec::new()));
            let sender = Sent {
                clock: Arc::new(context.child("sender_clock")),
                peer: f.participants[1].clone(),
                messages: sent.clone(),
            };
            let tiny = config(Duration::from_nanos(1));
            let (_probe_tx, probe_rx) = mpsc::channel(1);
            // Verify the actual public configuration is accepted. Abort before
            // polling the task; only the test launcher models elapsed poll cost.
            let probe = coordinator::start(
                context.child("admission_probe"),
                ready.clone(),
                f.schemes[0].clone(),
                tiny,
                (
                    sender.clone(),
                    ReadyInput {
                        incoming: probe_rx,
                        polls: 0,
                    },
                ),
                Sequential,
                |_| async { panic!("no Accept") },
            )
            .expect("valid 1ns retry must be admitted");
            probe.abort();
            let _ = probe.await;
            let (tx, rx) = mpsc::channel(2);
            let packet = (
                f.participants[1].clone(),
                Wire::<S, D>::Request(promise(&f.schemes[1], 2))
                    .encode()
                    .into(),
            );
            if !later {
                tx.send(packet.clone()).await.unwrap();
            }
            let scheme = f.schemes[0].clone();
            let task = context.child("coordinator").spawn(move |context| {
                coordinator::run_expired_retry_for_test(
                    context,
                    ready,
                    scheme,
                    tiny,
                    (
                        sender,
                        ReadyInput {
                            incoming: rx,
                            polls: 0,
                        },
                    ),
                    Sequential,
                    |_| async { panic!("no Accept") },
                )
            });
            // A separately scheduled caller must obtain a turn even when the
            // coordinator's next deadline has already elapsed on every poll.
            let observed_peer = observed.clone();
            let caller = context
                .child("later_caller")
                .spawn(move |context| async move {
                    reschedule().await;
                    if later {
                        while sent.lock().is_empty() {
                            reschedule().await;
                        }
                        tx.send(packet).await.unwrap();
                    }
                    while !observed_peer.lock().contains(&View::new(2)) {
                        reschedule().await;
                    }
                    context.stop(0, Some(Duration::from_secs(1))).await.unwrap();
                });
            assert!(task.await.unwrap().is_ok());
            caller.await.unwrap();
            assert!(observed.lock().contains(&View::new(2)));
            voter.abort();
            let _ = voter.await;
        });
    }

    #[test]
    fn unrepresentable_recovery_deadlines_reject_configuration() {
        deterministic::Runner::timed(Duration::from_secs(2)).start(|mut context| async move {
            let f = ed25519::fixture(
                &mut context,
                b"_COMMONWARE_CONSENSUS_RECOVERY_TIME_BOUND",
                6,
            );
            let (ready, voter) = voter(
                context.child("native"),
                f.schemes[0].clone(),
                Arc::default(),
            );
            for (index, retry) in [
                Duration::from_nanos(1),
                Duration::MAX - Duration::from_nanos(1),
            ]
            .into_iter()
            .enumerate()
            {
                let mut config = config(retry);
                config.attempt_timeout = Duration::MAX;
                let (_tx, rx) = mpsc::channel(1);
                let result = coordinator::start(
                    context.child("coordinator").with_attribute("case", index),
                    ready.clone(),
                    f.schemes[0].clone(),
                    config,
                    (
                        Sent {
                            clock: Arc::new(context.child("sender_clock")),
                            peer: f.participants[1].clone(),
                            messages: Arc::default(),
                        },
                        ReadyInput {
                            incoming: rx,
                            polls: 0,
                        },
                    ),
                    Sequential,
                    |_| async { panic!("no Accept") },
                );
                match result {
                    Err(coordinator::Error::Configuration) => {}
                    Err(error) => panic!("wrong configuration result: {error}"),
                    Ok(task) => {
                        task.abort();
                        let _ = task.await;
                        panic!("unrepresentable recovery deadline was accepted: case {index}");
                    }
                }
            }
            voter.abort();
            let _ = voter.await;
        });
    }
}
