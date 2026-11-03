//! Real six-node Engine networking with a prevalidated application-evidence fixture.
//! No manually assembled QCs or private actor mailboxes are used. This isolates
//! Engine wiring/readiness; it does not claim Baton selection or recovery liveness.
use bytes::Bytes;
use commonware_actor::Feedback;
use commonware_consensus::{
    Automaton, CertifiableAutomaton, Relay, Reporter, Viewable,
    simplex::{
        Config, Engine, FloorWith, ForwardPolicy, Plan, SkipPolicy,
        elector::RoundRobin,
        extension::{certificate::Finalization, report, vote::Statement},
        phase2::{
            Extended,
            voting::{ExtendedContext, Participation},
        },
        scheme::ed25519,
        types::{ActivityWith, ArtifactWith, Context, Notarize, Proposal},
    },
    types::{Attributable, Epoch, Participant, Round, View, ViewDelta},
};
use commonware_cryptography::{
    ed25519::PublicKey,
    sha256::{Digest as D, Sha256},
};
use commonware_p2p::simulated::{Config as NConfig, Link, Network};
use commonware_parallel::Sequential;
use commonware_runtime::{
    Clock, Quota, Runner, Supervisor, buffer::paged::CacheRef, deterministic,
};
use commonware_utils::{NZU16, NZU32, NZUsize, channel::oneshot, probability, sync::Mutex};
use std::{
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
    time::Duration,
};

type S = ed25519::Scheme;
type Activity = ActivityWith<S, D, Extended>;
const EPOCH: Epoch = Epoch::new(1);
const LAST: u64 = 3;
fn proposal(view: u64) -> Proposal<D> {
    Proposal::new(
        Round::new(EPOCH, View::new(view)),
        View::new(view - 1),
        D::from([view as u8; 32]),
    )
}
fn statement(view: u64) -> Statement<D> {
    Statement {
        ballot: proposal(view).round,
        proposal: proposal(view),
        domain: D::from([90; 32]),
        parent: if view == 1 {
            D::from([91; 32])
        } else {
            statement(view - 1).value::<Sha256>()
        },
        extension: D::from([view as u8 + 100; 32]),
    }
}
#[derive(Clone, Default)]
struct App(Arc<Mutex<Vec<oneshot::Sender<D>>>>);
impl Automaton for App {
    type Context = Context<D, PublicKey>;
    type Digest = D;
    async fn propose(&mut self, context: Self::Context) -> oneshot::Receiver<D> {
        let (tx, rx) = oneshot::channel();
        let view = context.round.view().get();
        if view <= LAST {
            assert_eq!(context.parent.0, View::new(view - 1));
            tx.send(proposal(view).payload).unwrap();
        } else {
            self.0.lock().push(tx);
        }
        rx
    }
    async fn verify(&mut self, context: Self::Context, payload: D) -> oneshot::Receiver<bool> {
        let (tx, rx) = oneshot::channel();
        let v = context.round.view().get();
        tx.send(
            v <= LAST && context.parent.0 == View::new(v - 1) && payload == proposal(v).payload,
        )
        .unwrap();
        rx
    }
}
impl CertifiableAutomaton for App {
    async fn certify(&mut self, _: Round, _: D) -> oneshot::Receiver<bool> {
        let (tx, rx) = oneshot::channel();
        tx.send(true).unwrap();
        rx
    }
}
impl Relay for App {
    type Digest = D;
    type PublicKey = PublicKey;
    type Plan = Plan<PublicKey>;
    fn broadcast(&mut self, _: D, _: Self::Plan) -> Feedback {
        Feedback::Ok
    }
}
#[derive(Clone, Default)]
struct Recorder(Arc<Mutex<Vec<Activity>>>);
impl Reporter for Recorder {
    type Activity = Activity;
    fn report(&mut self, event: Activity) -> Feedback {
        self.0.lock().push(event);
        Feedback::Ok
    }
}
#[derive(Clone, Default)]
struct Evidence(Arc<AtomicBool>);
impl Participation<S, D, Extended> for Evidence {
    fn notarize(&mut self, vote: Notarize<S, D>) -> report::Notarize<S, D> {
        report::Notarize::new(
            vote,
            Some(Bytes::from_static(b"prevalidated-engine-test-report")),
        )
        .unwrap()
    }
    fn final_subject(&mut self, p: &Proposal<D>) -> Option<Statement<D>> {
        if !self.0.load(Ordering::SeqCst) || p.view().get() > LAST {
            return None;
        }
        let s = statement(p.view().get());
        (s.proposal == *p).then_some(s)
    }
    fn accepts_finalization(&mut self, c: &Finalization<S, D>) -> bool {
        self.final_subject(&c.certificate().statement.proposal)
            .as_ref()
            == Some(&c.certificate().statement)
    }
    fn accepts_replay(&mut self, a: &ArtifactWith<S, D, Extended>) -> bool {
        match a {
            ArtifactWith::Finalize(v) => {
                self.final_subject(&v.vote().statement.proposal).as_ref()
                    == Some(&v.vote().statement)
            }
            ArtifactWith::Finalization(c) => self.accepts_finalization(c),
            _ => true,
        }
    }
    fn prune(&mut self, _: View) {}
}
fn exercise(delayed_nodes: usize, seed: u64) {
    deterministic::Runner::new(
        deterministic::Config::new()
            .with_seed(seed)
            .with_timeout(Some(Duration::from_secs(15))),
    )
    .start(move |mut context| async move {
        let fixture = ed25519::fixture(
            &mut context,
            b"_COMMONWARE_CONSENSUS_EXTENSION_ENGINE_TEST",
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
        for a in &fixture.participants {
            for b in &fixture.participants {
                if a != b {
                    oracle
                        .add_link(
                            a.clone(),
                            b.clone(),
                            Link {
                                latency: Duration::from_millis(25),
                                jitter: Duration::from_millis(2),
                                success_rate: probability!(1.0),
                            },
                        )
                        .await
                        .unwrap();
                }
            }
        }
        let mut nodes = Vec::new();
        for (i, scheme) in fixture.schemes.into_iter().enumerate() {
            let me = fixture.participants[i].clone();
            let control = oracle.control(me);
            let votes = control
                .register(0, Quota::per_second(NZU32!(10000)))
                .await
                .unwrap();
            let certificates = control
                .register(1, Quota::per_second(NZU32!(10000)))
                .await
                .unwrap();
            let resolver = control
                .register(2, Quota::per_second(NZU32!(10000)))
                .await
                .unwrap();
            let app = App::default();
            let record = Recorder::default();
            let evidence = Evidence::default();
            evidence.0.store(i >= delayed_nodes, Ordering::SeqCst);
            let engine = Engine::new_with(
                context.child("node").with_attribute("index", i),
                Config {
                    scheme,
                    elector: RoundRobin::<Sha256>::default(),
                    blocker: control,
                    automaton: app.clone(),
                    relay: app,
                    reporter: record.clone(),
                    track_historical_votes: true,
                    strategy: Sequential,
                    partition: format!("node{i}"),
                    mailbox_size: NZUsize!(128),
                    epoch: EPOCH,
                    floor: FloorWith::Genesis(D::from([0; 32])),
                    replay_buffer: NZUsize!(1024),
                    write_buffer: NZUsize!(1024),
                    page_cache: CacheRef::from_pooler(&context, NZU16!(4096), NZUsize!(8)),
                    leader_timeout: Duration::from_secs(2),
                    certification_timeout: Duration::from_secs(3),
                    timeout_retry: Duration::from_secs(1),
                    view_retention: ViewDelta::new(10),
                    skip: SkipPolicy::Disabled,
                    fetch_timeout: Duration::from_millis(100),
                    forward: ForwardPolicy::Disabled,
                },
                ExtendedContext::new::<Sha256>(D::from([90; 32]), D::from([91; 32])),
                evidence.clone(),
            );
            let ready = engine.readiness();
            let handle = engine.start(votes, certificates, resolver);
            nodes.push((record, evidence, ready, handle));
        }
        if delayed_nodes > 0 {
            // With all evidence delayed, first-phase progress still reaches a QC.
            // With one delayed node, the other five finish all three views.
            loop {
                let progressed = if delayed_nodes == nodes.len() {
                    nodes.iter().all(|(r, _, _, _)| {
                        r.0.lock().iter().any(
                            |a| matches!(a, Activity::Notarization(n) if n.view()==View::new(1)),
                        )
                    })
                } else {
                    nodes.iter().skip(delayed_nodes).all(|(r, _, _, _)| {
                        r.0.lock().iter().any(
                            |a| matches!(a, Activity::Finalization(c) if c.view()==View::new(LAST)),
                        )
                    })
                };
                if progressed {
                    break;
                }
                context.sleep(Duration::from_millis(5)).await;
            }
            // The raw Reporter also sees other nodes' final votes. Only this
            // node's own signature and voter-emitted final QC mean local progress.
            for (i, (r, e, ready, _)) in nodes.iter_mut().take(delayed_nodes).enumerate() {
                assert!(
                    !r.0.lock().iter().any(|a| match a {
                        Activity::Finalize(v) => v.signer() == Participant::new(i as u32),
                        Activity::Finalization(_) => true,
                        _ => false,
                    }),
                    "missing local evidence must prevent own final vote and accepted QC"
                );
                e.0.store(true, Ordering::SeqCst);
                for v in 1..=LAST {
                    ready.notify(View::new(v));
                }
            }
        }
        loop {
            if nodes.iter().all(|(r, _, _, _)| {
                (1..=LAST).all(|v| {
                    r.0.lock()
                        .iter()
                        .any(|a| matches!(a,Activity::Finalization(c) if c.view()==View::new(v)))
                })
            }) {
                break;
            }
            context.sleep(Duration::from_millis(5)).await;
        }
        for (r, _, _, handle) in nodes {
            for event in r.0.lock().iter() {
                match event {
                    Activity::Finalization(c) => {
                        assert!(c.certificate().verify(
                            &mut context,
                            &fixture.verifier,
                            &Sequential
                        ));
                        assert_eq!(c.certificate().statement, statement(c.view().get()));
                    }
                    Activity::Notarize(v) => {
                        assert_eq!(
                            v.report().unwrap().as_ref(),
                            b"prevalidated-engine-test-report"
                        );
                    }
                    Activity::ConflictingFinalize(_) | Activity::NullifyFinalize(_) => {
                        panic!("honest engines equivocated")
                    }
                    _ => {}
                }
            }
            handle.abort();
        }
    });
}
#[test]
fn extended_engine_six_nodes_three_views() {
    exercise(0, 101);
}
#[test]
fn extended_engine_readiness_preserves_first_phase() {
    exercise(6, 202);
}

#[test]
fn extended_engine_one_late_evidence_node_catches_up() {
    exercise(1, 303);
}
