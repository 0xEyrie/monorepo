//! Actual actor durability and parent-evidence wakeup with a prevalidated test adapter.
use super::*;
use crate::{
    Automaton,
    simplex::{
        elector::{Config as _, RoundRobin},
        extension::{
            certificate::Finalization,
            report,
            vote::{Certificate as ExtensionCertificate, Statement, Vote as ExtensionVote},
        },
        phase2::{Extended, voting::ExtendedContext},
        scheme::ed25519,
        types::Notarize,
    },
    types::{Epoch, ViewDelta},
};
use bytes::Bytes;
use commonware_actor::Feedback;
use commonware_codec::DecodeExt;
use commonware_cryptography::{
    certificate::{Scheme as _, Verifier as _, mocks::Fixture},
    ed25519::PublicKey,
    sha256::{Digest as D, Sha256},
};
use commonware_macros::select;
use commonware_p2p::{
    Receiver as _,
    simulated::{Config as NConfig, Link, Network},
    utils::mocks::NoopBlocker,
};
use commonware_parallel::Sequential;
use commonware_runtime::{
    Quota, Runner, Supervisor as _, deterministic,
    mocks::{DelayedSyncContext, PendingSyncs, next_pending_sync},
    reschedule,
};
use commonware_utils::{NZU16, NZU32, NZUsize, non_empty, probability, sync::Mutex};
use core::panic;
use futures::FutureExt as _;
use std::{sync::Arc, time::Duration};
type S = ed25519::Scheme;
type ExtActivity = ActivityWith<S, D, Extended>;

#[path = "startup_tests.rs"]
mod startup_tests;

#[path = "ancestry_tests.rs"]
mod ancestry_tests;

#[derive(Clone, Default)]
struct App(Arc<Mutex<Vec<oneshot::Sender<D>>>>);
impl Automaton for App {
    type Context = Context<D, PublicKey>;
    type Digest = D;
    async fn propose(&mut self, _: Self::Context) -> oneshot::Receiver<D> {
        let (tx, rx) = oneshot::channel();
        self.0.lock().push(tx);
        rx
    }
    async fn verify(&mut self, _: Self::Context, _: D) -> oneshot::Receiver<bool> {
        let (tx, rx) = oneshot::channel();
        tx.send(true).unwrap();
        rx
    }
}
impl CertifiableAutomaton for App {
    async fn certify(&mut self, _: Rnd, _: D) -> oneshot::Receiver<bool> {
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
struct Recorder(Arc<Mutex<Vec<ExtActivity>>>);
impl Reporter for Recorder {
    type Activity = ExtActivity;
    fn report(&mut self, a: ExtActivity) -> Feedback {
        self.0.lock().push(a);
        Feedback::Ok
    }
}
// This fixture supplies trusted application decisions. It does not model leader
// selection, route authentication, availability or complete recovery.
#[derive(Clone, Default)]
struct Evidence(
    Arc<Mutex<BTreeMap<View, Statement<D>>>>,
    Arc<Mutex<Vec<Statement<D>>>>,
    Arc<Mutex<Vec<Proposal<D>>>>,
    Arc<Mutex<Vec<Choice>>>,
);
#[derive(Clone)]
struct Choice {
    proposal: Proposal<D>,
    domain: D,
    ballot: Rnd,
    parent: D,
    leader: crate::types::Participant,
    proof: crate::simplex::extension::recovery::Proof<S, D>,
}
impl Participation<S, D, Extended> for Evidence {
    fn notarize(&mut self, vote: Notarize<S, D>) -> report::Notarize<S, D> {
        report::Notarize::new(vote, Some(Bytes::from_static(b"opaque-report-fixture"))).unwrap()
    }
    fn notarized(&mut self, certificate: &Notarization<S, D>) {
        self.2.lock().push(certificate.proposal.clone());
    }
    fn recovery_choice(
        &mut self,
        choice: crate::simplex::phase2::voting::RecoveryChoice<'_, S, D>,
    ) {
        self.3.lock().push(Choice {
            proposal: choice.proposal().clone(),
            domain: choice.domain(),
            ballot: choice.ballot(),
            parent: choice.parent(),
            leader: choice.leader(),
            proof: choice.proof().clone(),
        });
    }
    fn final_subject(&mut self, p: &Proposal<D>) -> Option<Statement<D>> {
        self.0
            .lock()
            .get(&p.round.view())
            .filter(|s| s.proposal == *p)
            .cloned()
    }
    fn accepts_finalization(&mut self, c: &Finalization<S, D>) -> bool {
        self.0.lock().get(&c.view()) == Some(&c.certificate().statement)
    }
    fn accepts_replay(&mut self, a: &ArtifactWith<S, D, Extended>) -> bool {
        match a {
            ArtifactWith::Finalize(v) => self.0.lock().get(&v.view()) == Some(&v.vote().statement),
            ArtifactWith::Finalization(c) => self.accepts_finalization(c),
            _ => true,
        }
    }
    fn accepts_recovery(&mut self, subject: &Statement<D>) -> bool {
        self.0
            .lock()
            .get(&subject.proposal.round.view())
            .is_some_and(|known| {
                known.proposal == subject.proposal
                    && known.domain == subject.domain
                    && known.parent == subject.parent
                    && known.extension == subject.extension
            })
    }
    fn recovered_installed(
        &mut self,
        c: &crate::simplex::extension::certificate::Recovered<S, D>,
    ) -> bool {
        self.1.lock().push(c.certificate().statement.clone());
        true
    }
    fn accepts_recovered(
        &mut self,
        certificate: &crate::simplex::extension::certificate::Recovered<S, D>,
    ) -> bool {
        self.accepts_recovery(&certificate.certificate().statement)
    }
    fn prune(&mut self, _: View) {}
}
fn proposal(view: u64) -> Proposal<D> {
    Proposal::new(
        Rnd::new(Epoch::new(1), View::new(view)),
        View::new(view - 1),
        D::from([view as u8; 32]),
    )
}
fn statement(view: u64, parent: D) -> Statement<D> {
    let p = proposal(view);
    Statement {
        ballot: p.round,
        proposal: p,
        domain: D::from([8; 32]),
        parent,
        extension: D::from([view as u8 + 10; 32]),
    }
}
fn notarization(f: &Fixture<S>, view: u64) -> Notarization<S, D> {
    let votes: Vec<_> = f
        .schemes
        .iter()
        .take(5)
        .map(|s| Notarize::sign(s, proposal(view)).unwrap())
        .collect();
    Notarization::from_notarizes(&f.verifier, non_empty![@&votes], &Sequential).unwrap()
}
fn finalization(
    context: &mut deterministic::Context,
    f: &Fixture<S>,
    subject: Statement<D>,
) -> Finalization<S, D> {
    let votes: Vec<_> = f
        .schemes
        .iter()
        .take(5)
        .map(|s| ExtensionVote::sign(s, subject.clone()).unwrap())
        .collect();
    Finalization::new(
        ExtensionCertificate::from_votes(context, &f.verifier, non_empty![@votes], &Sequential)
            .unwrap(),
    )
    .unwrap()
}
async fn certified(
    rx: &mut mailbox::Receiver<resolver::MailboxMessage<S, D, Extended>>,
    view: View,
) {
    loop {
        if let resolver::MailboxMessage::Certified {
            view: v, success, ..
        } = rx.recv().await.unwrap()
            && v == view
        {
            assert!(success);
            break;
        }
    }
}
async fn finalized(
    rx: &mut mailbox::Receiver<batcher::Message<S, D, Extended>>,
    view: View,
) -> Statement<D> {
    loop {
        if let batcher::Message::Constructed(VoteWith::Finalize(vote)) = rx.recv().await.unwrap()
            && vote.view() == view
        {
            return vote.vote().statement.clone();
        }
    }
}
#[test]
fn extended_actor_sync_and_parent_wakeup() {
    exercise_actor_sync(false);
    exercise_actor_sync(true);
}

// PendingSyncs::arm is a lifetime tracking gate, not a resettable latch. Use
// separate deterministic runs to hold the local vote and the parent anchor.
fn exercise_actor_sync(hold_parent: bool) {
    deterministic::Runner::timed(Duration::from_secs(20)).start(move |mut context|async move {
        let fixture=ed25519::fixture(&mut context,b"_COMMONWARE_CONSENSUS_EXTENSION_VOTER_ACTOR_TEST",6);
        let (network,oracle)=Network::new_with_peers(context.child("network"),NConfig {
            max_size:1024*1024,max_peers_per_set:NZUsize!(6),disconnect_on_block:true,tracked_peer_sets:NZUsize!(1),
        },fixture.participants.clone()).await;
        network.start();
        let me=fixture.participants[0].clone();
        let observer=fixture.participants[1].clone();
        let (votes,_)=oracle.control(me.clone()).register(0,Quota::per_second(NZU32!(1000))).await.unwrap();
        let (certificates,_)=oracle.control(me.clone()).register(1,Quota::per_second(NZU32!(1000))).await.unwrap();
        let (_,mut wire)=oracle.control(observer.clone()).register(0,Quota::per_second(NZU32!(1000))).await.unwrap();
        oracle.add_link(me,observer,Link {latency:Duration::ZERO,jitter:Duration::ZERO,success_rate:probability!(1.0)}).await.unwrap();
        let pending=PendingSyncs::default();
        pending.unblock();
        let actor_context=DelayedSyncContext {inner:context.child("voter"),pending:pending.clone()};
        let cache=CacheRef::from_pooler(&actor_context,NZU16!(1024),NZUsize!(10));
        let evidence=Evidence::default();
        let app=App::default();
        let recorder=Recorder::default();
        let config=||Config {
            scheme:fixture.schemes[0].clone(),elector:RoundRobin::<Sha256>::default().build(fixture.schemes[0].participants()),
            blocker:NoopBlocker::default(),automaton:app.clone(),relay:app.clone(),reporter:recorder.clone(),
            partition:"extension_actor".into(),epoch:Epoch::new(1),floor:FloorWith::Genesis(D::from([0;32])),
            mailbox_size:NZUsize!(8),leader_timeout:Duration::from_secs(10),certification_timeout:Duration::from_secs(10),
            timeout_retry:Duration::from_secs(10),skip_budget:6,view_retention:ViewDelta::new(10),
            replay_buffer:NZUsize!(4096),write_buffer:NZUsize!(4096),page_cache:cache.clone(),
        };
        let (actor,mut input)=ActorWith::new_with(actor_context,config(),ExtendedContext::new::<Sha256>(D::from([8;32]),D::from([9;32])),evidence.clone());
        let (batcher_tx,mut batcher_rx)=mailbox::new(context.child("batcher"),NZUsize!(8));
        let (resolver_tx,mut resolver_rx)=mailbox::new(context.child("resolver"),NZUsize!(8));
        // A valid signature from another deployment must not occupy the pending
        // slot and shadow a later legitimate QC whose evidence is not ready yet.
        let mut foreign=statement(1,D::from([9;32]));
        foreign.domain=D::from([99;32]);
        let actor=actor.handle_finalization(finalization(&mut context,&fixture,foreign)).await;
        assert!(actor.pending_finalizations.is_empty());
        let handle=actor.start(batcher::Mailbox::new(batcher_tx),resolver::Mailbox::new(resolver_tx),votes.clone(),certificates.clone());
        input.proposal(proposal(1));
        // A report is attached to the ordinary first vote before selection exists.
        loop {
            if let batcher::Message::Constructed(VoteWith::Notarize(v))=batcher_rx.recv().await.unwrap() {
                assert_eq!(v.vote().proposal,proposal(1));
                assert_eq!(v.report().unwrap().as_ref(),b"opaque-report-fixture");
                break;
            }
        }
        input.recovered(CertificateWith::Notarization(notarization(&fixture,1)));
        certified(&mut resolver_rx,View::new(1)).await;
        assert_eq!(*evidence.2.lock(), vec![proposal(1)]);
        // Repeated delivery is not another optional selection opportunity.
        input.recovered(CertificateWith::Notarization(notarization(&fixture,1)));
        let first=statement(1,D::from([9;32]));
        evidence.0.lock().insert(View::new(1),first.clone());
        if !hold_parent { pending.arm(); }
        input.interpretation_ready(View::new(1));
        if !hold_parent {
        while pending.lock().is_empty() {reschedule().await;}
        let sync=next_pending_sync(&pending);
        sync.blocked.await.unwrap();
        while let Some(message)=batcher_rx.recv().now_or_never().flatten() {
            assert!(!matches!(message,batcher::Message::Constructed(VoteWith::Finalize(_))));
        }
        let deadline=context.current()+Duration::from_millis(10);
        loop {select! {
            _=context.sleep_until(deadline)=>break,
            packet=wire.recv()=>{let (_,bytes)=packet.unwrap();let vote=VoteWith::<S,D,Extended>::decode(bytes).unwrap();assert!(!matches!(vote,VoteWith::Finalize(_)));},
        }}
        sync.release.send(Ok(())).unwrap();
        }
        assert_eq!(finalized(&mut batcher_rx,View::new(1)).await,first);
        let child=statement(2,first.value::<Sha256>());
        evidence.0.lock().insert(View::new(2),child.clone());
        input.recovered(CertificateWith::Notarization(notarization(&fixture,2)));
        certified(&mut resolver_rx,View::new(2)).await;
        while let Some(message)=batcher_rx.recv().now_or_never().flatten() {
            assert!(!matches!(message,batcher::Message::Constructed(VoteWith::Finalize(ref v)) if v.view()==View::new(2)));
        }
        // Hold the parent anchor's durability barrier. It must complete before
        // a dependent child's final vote can be published.
        if hold_parent { pending.arm(); }
        // No new child message follows: the parent's exact QC must wake it.
        input.recovered(CertificateWith::Finalization(finalization(&mut context,&fixture,first.clone())));
        if hold_parent {
        while pending.lock().is_empty() {reschedule().await;}
        let parent_sync=next_pending_sync(&pending);
        parent_sync.blocked.await.unwrap();
        while let Some(message)=batcher_rx.recv().now_or_never().flatten() {
            assert!(!matches!(message,batcher::Message::Constructed(VoteWith::Finalize(ref v)) if v.view()==View::new(2)));
        }
        parent_sync.release.send(Ok(())).unwrap();
        }
        assert_eq!(finalized(&mut batcher_rx,View::new(2)).await,child);
        assert_eq!(*evidence.2.lock(), vec![proposal(1),proposal(2)]);
        handle.abort();
        let _=handle.await;
        let journal=Journal::<_,ArtifactWith<S,D,Extended>>::init(context.child("inspect"),JConfig {
            partition:"extension_actor".into(),compression:None,codec_config:fixture.schemes[0].certificate_codec_config(),page_cache:cache.clone(),write_buffer:NZUsize!(4096),
        }).await.unwrap();
        let mut replay=journal.replay(0,0,NZUsize!(4096),ReadOptions::DONT_CACHE).await.unwrap();
        let mut restored=Vec::new();
        while let Some(record)=replay.next().await {
            if let ArtifactWith::Finalize(vote)=record.unwrap().3 {restored.push(vote.vote().statement.clone());}
        }
        let journal=replay.finish().unwrap();
        assert_eq!(restored,vec![first.clone(),child.clone()]);
        assert!(recorder.0.lock().iter().any(|a|matches!(a,ActivityWith::Finalization(c) if c.view()==View::new(1))));
        drop(journal);
        pending.unblock();
        // Reopen the actual voter from its native journal. Retain selected
        // application values; only clear observations from the previous instance.
        let selected = evidence.0.lock().clone();
        evidence.2.lock().clear();
        let (actor, mut input) = ActorWith::new_with(DelayedSyncContext {inner:context.child("restarted_voter"),pending:pending.clone()}, config(),
            ExtendedContext::new::<Sha256>(D::from([8;32]),D::from([9;32])), evidence.clone());
        let (batcher_tx, mut batcher_rx) = mailbox::new(context.child("restarted_batcher"), NZUsize!(8));
        let (resolver_tx, _resolver_rx) = mailbox::new(context.child("restarted_resolver"), NZUsize!(8));
        let restarted = actor.start(batcher::Mailbox::new(batcher_tx), resolver::Mailbox::new(resolver_tx), votes, certificates);
        assert_eq!(finalized(&mut batcher_rx, View::new(2)).await, child);
        assert_eq!(*evidence.0.lock(), selected);
        assert_eq!(*evidence.2.lock(), vec![proposal(1),proposal(2)]);
        input.recovered(CertificateWith::Notarization(notarization(&fixture, 2)));
        // A processed mailbox query fences the duplicate's preceding intake.
        let _ = input.prepare_recovery(crate::simplex::extension::request::Query::Discover).await.unwrap();
        assert_eq!(*evidence.2.lock(), vec![proposal(1),proposal(2)]);
        assert_eq!(*evidence.0.lock(), selected);
        restarted.abort();
        let _ = restarted.await;
    });
}

#[test]
fn extension_overflow_preserves_parent_and_readiness() {
    use commonware_actor::mailbox::{Overflow as _, Policy as _};
    deterministic::Runner::default().start(|mut context| async move {
        let fixture = ed25519::fixture(
            &mut context,
            b"_COMMONWARE_CONSENSUS_EXTENSION_VOTER_OVERFLOW_TEST",
            6,
        );
        let first = statement(1, D::from([9; 32]));
        let second = statement(2, first.value::<Sha256>());
        let mut pending = super::super::ingress::Pending::<S, D, Extended>::default();
        for subject in [&second, &first] {
            Message::handle(
                &mut pending,
                Message::Verified {
                    span: Span::none(),
                    from_resolver: true,
                    certificate: CertificateWith::Finalization(finalization(
                        &mut context,
                        &fixture,
                        subject.clone(),
                    )),
                },
            );
        }
        for _ in 0..2 {
            Message::handle(
                &mut pending,
                Message::InterpretationReady {
                    span: Span::none(),
                    view: View::new(1),
                },
            );
        }
        let mut received = Vec::new();
        pending.drain(|message| {
            received.push(message);
            None
        });
        assert_eq!(received.len(), 3);
        for (message, expected) in received.iter().take(2).zip([second, first]) {
            let Message::Verified {
                certificate: CertificateWith::Finalization(qc),
                ..
            } = message
            else {
                panic!("lost exact QC")
            };
            assert_eq!(qc.certificate().statement, expected);
        }
        assert!(matches!(received[2],Message::InterpretationReady {view,..} if view==View::new(1)));
    });
}

#[path = "recovery_tests.rs"]
mod recovery_tests;

#[path = "recovered_tests.rs"]
mod recovered_tests;
