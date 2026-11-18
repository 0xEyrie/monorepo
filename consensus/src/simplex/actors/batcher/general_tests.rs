//! Standalone original G1 actor wiring, without a voter or live G1 policy.

use super::*;
use crate::{
    Epochable as _,
    simplex::{
        extension::agreement::general as g,
        phase2::{
            Mode,
            general::{FinalVote, General, tests::Setup},
        },
        types::{ActivityWith, CertificateWith, VoteWith},
    },
};
use commonware_utils::channel::mpsc::error::TrySendError;
use futures::FutureExt as _;
use std::sync::atomic::{AtomicUsize, Ordering};

type S = ed25519::Scheme;
type M = General<Sha256>;
type D = Sha256Digest;

#[derive(Clone)]
struct GeneralReport(Arc<AtomicUsize>);

impl crate::Reporter for GeneralReport {
    type Activity = ActivityWith<S, D, M>;

    fn report(&mut self, activity: Self::Activity) -> Feedback {
        if matches!(activity, ActivityWith::Finalize(_)) {
            self.0.fetch_add(1, Ordering::Relaxed);
        }
        Feedback::Ok
    }
}

fn exercise(n: usize, material_first: bool, foreign_first: bool) {
    deterministic::Runner::timed(Duration::from_secs(10)).start(|mut context| async move {
        let setup = Setup::new(n, 721);
        let q = g::Committee::new(n).unwrap().quorum();
        let material = setup.assembly(setup.origin.clone());
        let me = setup.f.participants[n - 1].clone();
        let oracle = start_test_network_with_peers(
            context.child("network"),
            setup.f.participants.clone(),
        )
        .await;
        let observed = Arc::new(AtomicUsize::new(0));
        let mut cfg = test_config(
            setup.f.verifier.clone(),
            oracle.control(me.clone()),
            GeneralReport(observed.clone()),
            MockRelay::new(),
            material.epoch(),
            BatcherOptions {
                skip: SkipPolicy::Disabled,
                ..BatcherOptions::default()
            },
        );
        cfg.mailbox_size = NZUsize!(1);
        let (batcher, mut inbox) =
            ActorWith::<_, _, _, _, _, _, _, M>::new(context.child("actor"), cfg);
        let (sender, mut output) = mailbox::new::<voter::Message<S, D, M>>(
            context.child("voter"),
            NZUsize!(1),
        );
        let (_, votes) = oracle.control(me.clone()).register(0, TEST_QUOTA).await.unwrap();
        let (_, certs) = oracle.control(me.clone()).register(1, TEST_QUOTA).await.unwrap();
        let mut peers = Vec::new();
        for peer in setup.f.participants.iter().take(q) {
            peers.push(register_and_link_peer(
                &oracle,
                peer.clone(),
                me.clone(),
                0,
                Duration::from_millis(1),
            ).await);
        }
        let handle = batcher.start(voter::Mailbox::new(sender), votes, certs);

        // A checked cap is not a self-certifying jump to a distant future view.
        inbox.update(Span::none(), View::new(1), setup.core.leader, View::zero(), None);
        context.sleep(Duration::from_millis(10)).await;
        assert!(!inbox.submit_assembly(material.clone()).unwrap().await.unwrap());
        assert!(output.recv().now_or_never().is_none());
        inbox.update(Span::none(), material.view(), setup.core.leader, View::zero(), None);
        context.sleep(Duration::from_millis(10)).await;

        if foreign_first {
            let foreign = Setup::with_namespace(
                n,
                721,
                setup.core.leader,
                b"_COMMONWARE_CONSENSUS_G1_ACTOR_FOREIGN_ASSEMBLY_TEST",
            );
            assert_eq!(setup.core, foreign.core);
            assert!(inbox.submit_assembly(foreign.assembly(foreign.origin.clone()))
                .unwrap().await.unwrap());
        } else if material_first {
            assert!(inbox.submit_assembly(material.clone()).unwrap().await.unwrap());
        }

        for (owner, sender) in peers.iter_mut().enumerate() {
            let vote = VoteWith::<S, D, M>::Finalize(FinalVote::new(setup.pairs[owner].clone()));
            assert_eq!(sender.send(Recipients::One(me.clone()), vote.encode(), true), vec![me.clone()]);
        }
        if !material_first || foreign_first {
            context.sleep(Duration::from_millis(20)).await;
            assert_eq!(observed.load(Ordering::Relaxed), q);
            assert!(output.recv().now_or_never().is_none());
            assert!(inbox.submit_assembly(material.clone()).unwrap().await.unwrap());
        }

        select! {
            message = output.recv() => match message {
                Some(voter::Message::Verified {
                    certificate: CertificateWith::Finalization(certificate), ..
                }) => {
                    assert!(<M as Mode<S, D>>::verify(
                        &certificate, &mut context, &setup.f.verifier, &Sequential,
                    ));
                    assert_eq!(certificate.inner().origin.body.core, setup.core);
                    assert_eq!(certificate.inner().native.certificate.signers.count(), q);
                    assert_eq!(certificate.inner().agreement.certificate.signers.count(), q);
                    assert_eq!(certificate.inner().origin.id::<Sha256>(), setup.origin.id::<Sha256>());
                }
                _ => panic!("missing complete paired certificate in the native voter mailbox"),
            },
            _ = context.sleep(Duration::from_secs(1)) => panic!("paired actor did not progress"),
        }
        assert_eq!(observed.load(Ordering::Relaxed), q);
        // Completed collection and finalized admission both reject new custody.
        assert!(!inbox.submit_assembly(material.clone()).unwrap().await.unwrap());
        inbox.update(Span::none(), material.view().next(), setup.core.leader, material.view(), None);
        context.sleep(Duration::from_millis(10)).await;
        assert!(!inbox.submit_assembly(material).unwrap().await.unwrap());
        handle.abort();
    });
}

#[test]
fn standalone_general_actor_material_before_and_after_q() {
    for n in [4, 8, 9, 10, 13, 64] {
        for before in [false, true] {
            exercise(n, before, false);
        }
    }
}

#[test]
fn standalone_general_actor_failed_foreign_material_then_current_retry() {
    for n in [8, 9, 10, 13, 64] {
        exercise(n, false, true);
    }
}

#[test]
fn standalone_general_actor_public_port_enforces_byte_and_queue_custody() {
    deterministic::Runner::default().start(|context| async move {
        let setup = Setup::new(8, 722);
        let mut origin = setup.origin.clone();
        origin.body.build = bytes::Bytes::from(vec![77; g::MAX_FIRST_BYTES]);
        setup.endorse(&mut origin);
        let limits = g::Limits {
            build_bytes: g::MAX_FIRST_BYTES,
            ..crate::simplex::phase2::general::tests::LIMITS
        };
        // An explicit fixture policy accepts this large opaque literal; this
        // exercises native custody and does not model the SDK Build semantics.
        let material = g::normal::Assembly::new::<Sha256, _>(
            &mut TestRng::new(723),
            &setup.f.verifier,
            &setup.core,
            origin.body.decision.input,
            origin,
            setup.notarization(),
            limits,
            |_| true,
            |_, _| true,
            &Sequential,
        )
        .unwrap();
        let (actor, inbox) = ActorWith::<_, _, _, _, _, _, _, M>::new(
            context.child("byte_actor"),
            test_config(
                setup.f.verifier.clone(),
                NoopBlocker::default(),
                GeneralReport(Arc::new(AtomicUsize::new(0))),
                MockRelay::new(),
                material.epoch(),
                BatcherOptions::default(),
            ),
        );
        let mut replies = Vec::new();
        loop {
            match inbox.submit_assembly(material.clone()) {
                Ok(reply) => replies.push(reply),
                Err(TrySendError::Full(returned)) => {
                    assert_eq!(returned, material);
                    break;
                }
                Err(TrySendError::Closed(_)) => panic!("actor still owns the queue"),
            }
        }
        assert!(replies.len() < 128, "byte cap must fill before queue count");
        let budget = <M as Mode<S, D>>::ASSEMBLY_BUDGET;
        assert!(replies.len() * material.retained_bytes() <= budget);
        assert!((replies.len() + 1) * material.retained_bytes() > budget);
        drop(actor);
        for reply in replies {
            assert!(reply.await.is_err());
        }
        assert!(matches!(inbox.submit_assembly(material.clone()),
            Err(TrySendError::Closed(returned)) if returned == material));
    });
}
