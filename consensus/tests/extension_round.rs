//! Production batcher round: source admission, conflicts and exact certificate assembly.
use commonware_actor::Feedback;
use commonware_consensus::{
    Reporter,
    simplex::{
        extension::{
            certificate::Finalize as EF,
            report::Notarize as EN,
            vote::{Statement, Vote as EV},
        },
        phase2::{Extended, aggregation::RoundWith},
        scheme::{
            self, bls12381_multisig,
            bls12381_threshold::{standard, vrf},
            ed25519,
            reporter::AttributableReporterWith,
        },
        types::{
            ActivityWith, CertificateWith, Notarization, Notarize, Nullify, Proposal, VoteWith,
        },
    },
    types::{Epoch, Participant, Round, View},
};
use commonware_cryptography::{
    bls12381::primitives::variant::MinSig, certificate::mocks::Fixture, sha256::Digest,
};
use commonware_p2p::utils::mocks::NoopBlocker;
use commonware_parallel::Sequential;
use commonware_runtime::{Runner as _, deterministic};
use commonware_utils::{TestRng, non_empty, sync::Mutex};
use std::sync::Arc;
type A<S> = ActivityWith<S, Digest, Extended>;
#[derive(Clone)]
struct Record<S: scheme::Scheme<Digest>>(Arc<Mutex<Vec<A<S>>>>);
impl<S: scheme::Scheme<Digest>> Reporter for Record<S> {
    type Activity = A<S>;
    fn report(&mut self, a: Self::Activity) -> Feedback {
        self.0.lock().push(a);
        Feedback::Ok
    }
}
fn proposal(value: u8) -> Proposal<Digest> {
    Proposal::new(
        Round::new(Epoch::new(1), View::new(2)),
        View::new(1),
        Digest::from([value; 32]),
    )
}
fn final_vote<S: scheme::Scheme<Digest>>(
    f: &Fixture<S>,
    i: usize,
    p: Proposal<Digest>,
    d: u8,
) -> EF<S, Digest> {
    EF::new(
        EV::sign(
            &f.schemes[i],
            Statement {
                ballot: p.round,
                proposal: p,
                domain: Digest::from([2; 32]),
                parent: Digest::from([3; 32]),
                extension: Digest::from([d; 32]),
            },
        )
        .unwrap(),
    )
    .unwrap()
}
fn first_vote<S: scheme::Scheme<Digest>>(
    f: &Fixture<S>,
    i: usize,
    p: Proposal<Digest>,
    report: u8,
) -> EN<S, Digest> {
    EN::new(
        Notarize::sign(&f.schemes[i], p).unwrap(),
        Some(bytes::Bytes::from(vec![report])),
    )
    .unwrap()
}
async fn exercise<S: scheme::Scheme<Digest>>(f: Fixture<S>) {
    let p = proposal(1);
    // SDK route intake observes the raw activity before optional native fault
    // attribution filtering (threshold schemes deliberately filter first votes).
    let raw_events = Arc::new(Mutex::new(Vec::new()));
    let mut raw_round = RoundWith::<_, _, _, _, Extended>::new(
        p.round,
        Arc::new(f.verifier.clone()),
        NoopBlocker::default(),
        Record(raw_events.clone()),
        false,
    );
    raw_round.set_leader(Participant::new(0));
    for i in 0..5 {
        assert!(raw_round.add_network(
            f.verifier.participants()[i].clone(),
            VoteWith::Notarize(first_vote(&f, i, p.clone(), i as u8))
        ));
    }
    let raw_reports: Vec<_> = raw_events
        .lock()
        .iter()
        .filter_map(|event| {
            if let A::Notarize(vote) = event {
                Some(vote.report().unwrap().clone())
            } else {
                None
            }
        })
        .collect();
    assert_eq!(
        raw_reports,
        (0..5)
            .map(|i| bytes::Bytes::from(vec![i]))
            .collect::<Vec<_>>()
    );
    let events = Arc::new(Mutex::new(Vec::new()));
    let reporter = AttributableReporterWith::<_, _, _, _, _, Extended>::new(
        TestRng::new(9),
        f.verifier.clone(),
        Record(events.clone()),
        Sequential,
        true,
    );
    let mut round = RoundWith::<_, _, _, _, Extended>::new(
        p.round,
        Arc::new(f.verifier.clone()),
        NoopBlocker::default(),
        reporter.clone(),
        false,
    );
    let peers = f.verifier.participants();
    let mut rng = TestRng::new(10);
    // A remote peer cannot occupy a different signer's slot.
    assert!(!round.add_network(
        peers[1].clone(),
        VoteWith::Notarize(first_vote(&f, 0, p.clone(), 1))
    ));
    round.set_leader(Participant::new(0));
    for i in 0..5 {
        assert!(round.add_network(
            peers[i].clone(),
            VoteWith::Notarize(first_vote(&f, i, p.clone(), i as u8))
        ));
    }
    // The optional report is not a native notarize subject; a changed attachment
    // neither replaces the first report nor produces a native equivocation proof.
    assert!(!round.add_network(
        peers[0].clone(),
        VoteWith::Notarize(first_vote(&f, 0, p.clone(), 99))
    ));
    assert!(
        !events
            .lock()
            .iter()
            .any(|a| matches!(a, A::ConflictingNotarize(_)))
    );
    assert_eq!(
        round.try_forward_proposal(Participant::new(1)),
        Some(p.clone())
    );
    assert!(round.try_forward_proposal(Participant::new(1)).is_none());
    let qc = round
        .try_construct(&mut rng, &Sequential)
        .await
        .unwrap()
        .certificate
        .unwrap();
    assert!(matches!(qc, CertificateWith::Notarization(_)));
    assert!(qc.verify(&mut rng, &f.verifier, &Sequential));
    assert_eq!(round.notarizes().count(), 5);
    assert_eq!(
        round.notarizes().next().unwrap().report().unwrap().as_ref(),
        &[0]
    );
    // No compaction of extension subjects: a duplicate identity cannot be counted
    // twice after the first-phase certificate, and a distinct D is portable evidence.
    assert!(round.add_network(
        peers[0].clone(),
        VoteWith::Finalize(final_vote(&f, 0, p.clone(), 4))
    ));
    assert!(!round.add_network(
        peers[0].clone(),
        VoteWith::Finalize(final_vote(&f, 0, p.clone(), 5))
    ));
    assert_eq!(
        events
            .lock()
            .iter()
            .filter(|a| matches!(a, A::ConflictingFinalize(_)))
            .count(),
        usize::from(S::is_attributable())
    );
    for i in 1..6 {
        assert!(round.add_network(
            peers[i].clone(),
            VoteWith::Finalize(final_vote(&f, i, p.clone(), 5))
        ));
    }
    let qc = round
        .try_construct(&mut rng, &Sequential)
        .await
        .unwrap()
        .certificate
        .unwrap();
    assert!(qc.verify(&mut rng, &f.verifier, &Sequential));
    let CertificateWith::Finalization(qc) = qc else {
        panic!("wrong phase")
    };
    assert_eq!(qc.certificate().statement.extension, Digest::from([5; 32]));
    assert_eq!(round.notarizes().count(), 5);
    assert!(!round.add_network(
        peers[1].clone(),
        VoteWith::Nullify(Nullify::sign::<Digest>(&f.schemes[1], p.round).unwrap())
    ));
    assert_eq!(
        events
            .lock()
            .iter()
            .filter(|a| matches!(a, A::NullifyFinalize(_)))
            .count(),
        usize::from(S::is_attributable())
    );
    assert!(round.try_construct(&mut rng, &Sequential).await.is_none());
    // A leader's untrusted proposal can be superseded by an authenticated QC;
    // matching final votes that arrived before that QC must survive and assemble.
    let mut round = RoundWith::<_, _, _, _, Extended>::new(
        p.round,
        Arc::new(f.verifier.clone()),
        NoopBlocker::default(),
        reporter.clone(),
        false,
    );
    round.set_leader(Participant::new(0));
    assert!(round.add_network(
        peers[0].clone(),
        VoteWith::Notarize(first_vote(&f, 0, proposal(8), 1))
    ));
    for i in 0..5 {
        assert!(round.add_network(
            peers[i].clone(),
            VoteWith::Finalize(final_vote(&f, i, p.clone(), 5))
        ));
    }
    assert!(round.try_construct(&mut rng, &Sequential).await.is_none());
    let votes: Vec<_> = f
        .schemes
        .iter()
        .take(5)
        .map(|s| Notarize::sign(s, p.clone()).unwrap())
        .collect();
    let qc = Notarization::from_notarizes(&f.verifier, non_empty![@&votes], &Sequential).unwrap();
    assert!(qc.verify(&mut rng, &f.verifier, &Sequential));
    assert!(round.record_certificate(&CertificateWith::Notarization(qc)));
    let qc = round
        .try_construct(&mut rng, &Sequential)
        .await
        .unwrap()
        .certificate
        .unwrap();
    assert!(qc.verify(&mut rng, &f.verifier, &Sequential));
    assert!(matches!(qc, CertificateWith::Finalization(_)));
    // Split valid directions cannot be collapsed by the round into one QC.
    let mut round = RoundWith::<_, _, _, _, Extended>::new(
        p.round,
        Arc::new(f.verifier.clone()),
        NoopBlocker::default(),
        reporter,
        false,
    );
    round.set_leader(Participant::new(0));
    round.add_network(
        peers[0].clone(),
        VoteWith::Notarize(first_vote(&f, 0, p.clone(), 1)),
    );
    for i in 0..6 {
        assert!(round.add_network(
            peers[i].clone(),
            VoteWith::Finalize(final_vote(&f, i, p.clone(), if i < 3 { 4 } else { 5 }))
        ));
    }
    if let Some(batch) = round.try_construct(&mut rng, &Sequential).await {
        assert!(batch.certificate.is_none());
        assert!(batch.invalid.is_empty());
    }
}
const NS: &[u8] = b"_COMMONWARE_CONSENSUS_EXTENSION_ROUND_TEST";
#[test]
fn ed25519_round() {
    deterministic::Runner::default().start(|_| async {
        exercise(ed25519::fixture(&mut TestRng::new(1), NS, 6)).await;
    });
}
#[test]
fn multisig_round() {
    deterministic::Runner::default().start(|_| async {
        exercise(bls12381_multisig::fixture::<MinSig, _>(
            &mut TestRng::new(2),
            NS,
            6,
        ))
        .await;
    });
}
#[test]
fn threshold_round() {
    deterministic::Runner::default().start(|_| async {
        exercise(standard::fixture::<MinSig, _>(&mut TestRng::new(3), NS, 6)).await;
    });
}
#[test]
fn vrf_round() {
    deterministic::Runner::default().start(|_| async {
        exercise(vrf::fixture::<MinSig, _>(&mut TestRng::new(4), NS, 6)).await;
    });
}
