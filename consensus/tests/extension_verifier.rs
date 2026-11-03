//! Actual native batcher verifier with static Plain/Extended accumulation.
use commonware_consensus::{
    simplex::{
        extension::{
            certificate::Finalize as EFinalize,
            report::Notarize as ENotarize,
            vote::{Statement, Vote as EVote},
        },
        phase2::{
            Extended, Plain,
            aggregation::{FinalBuffer, VerifierWith, extended::Groups},
        },
        scheme::{
            self, bls12381_multisig,
            bls12381_threshold::{standard, vrf},
            ed25519,
        },
        types::{CertificateWith, Finalize, Notarize, Proposal, VoteWith},
    },
    types::{Epoch, Participant, Round, View},
};
use commonware_cryptography::{
    bls12381::primitives::variant::MinSig, certificate::mocks::Fixture, sha256::Digest,
};
use commonware_parallel::Sequential;
use commonware_runtime::{Runner as _, deterministic};
use commonware_utils::{Faults as _, N3f1, TestRng};
fn proposal() -> Proposal<Digest> {
    Proposal::new(
        Round::new(Epoch::new(1), View::new(2)),
        View::new(1),
        Digest::from([1; 32]),
    )
}
fn statement(p: Proposal<Digest>, extension: u8) -> Statement<Digest> {
    Statement {
        ballot: p.round,
        proposal: p,
        domain: Digest::from([2; 32]),
        parent: Digest::from([3; 32]),
        extension: Digest::from([extension; 32]),
    }
}
fn vote<S: scheme::Scheme<Digest>>(
    f: &Fixture<S>,
    signer: usize,
    extension: u8,
) -> EFinalize<S, Digest> {
    EFinalize::new(EVote::sign(&f.schemes[signer], statement(proposal(), extension)).unwrap())
        .unwrap()
}
fn verifier<S: scheme::Scheme<Digest>>(f: &Fixture<S>) -> VerifierWith<S, Digest, Extended> {
    let p = proposal();
    let mut v = VerifierWith::new(p.round, f.verifier.clone(), N3f1::quorum(f.schemes.len()));
    v.set_leader(
        Participant::new(0),
        Some(&Notarize::sign(&f.schemes[0], p).unwrap()),
    );
    v
}
async fn exercise<S: scheme::Scheme<Digest>>(f: Fixture<S>) {
    let mut rng = TestRng::new(0);
    let mut v = verifier(&f);
    for i in 0..6 {
        v.add(
            VoteWith::Finalize(vote(&f, i, if i < 3 { 4 } else { 5 })),
            false,
        );
    }
    if let Some(batch) = v.try_construct_finalization(&mut rng, &Sequential).await {
        assert!(batch.certificate.is_none());
        assert!(batch.invalid.is_empty());
    }
    // Parent and domain are part of the exact subject, even when D is identical.
    for vary_parent in [false, true] {
        let mut v = verifier(&f);
        for i in 0..6 {
            let mut s = statement(proposal(), 5);
            if i >= 3 {
                if vary_parent {
                    s.parent = Digest::from([8; 32]);
                } else {
                    s.domain = Digest::from([8; 32]);
                }
            }
            v.add(
                VoteWith::Finalize(EFinalize::new(EVote::sign(&f.schemes[i], s).unwrap()).unwrap()),
                false,
            );
        }
        if let Some(batch) = v.try_construct_finalization(&mut rng, &Sequential).await {
            assert!(batch.certificate.is_none());
            assert!(batch.invalid.is_empty());
        }
    }
    // First-arriving minority statement must not poison a different exact quorum.
    let mut v = verifier(&f);
    for i in 0..6 {
        v.add(
            VoteWith::Finalize(vote(&f, i, if i == 0 { 4 } else { 5 })),
            false,
        );
    }
    let batch = v
        .try_construct_finalization(&mut rng, &Sequential)
        .await
        .unwrap();
    assert!(batch.invalid.is_empty());
    let cert = batch.certificate.unwrap();
    assert!(cert.verify(&mut rng, &f.verifier, &Sequential));
    let CertificateWith::Finalization(cert) = cert else {
        panic!("wrong phase")
    };
    assert_eq!(cert.certificate().statement, statement(proposal(), 5));
    assert!(
        v.try_construct_finalization(&mut rng, &Sequential)
            .await
            .is_none()
    );
    // Known-valid local votes still need an exact-subject quorum, even before P is selected.
    let mut v = VerifierWith::<S, Digest, Extended>::new(proposal().round, f.verifier.clone(), 5);
    for i in 0..6 {
        v.add(
            VoteWith::Finalize(vote(&f, i, if i < 3 { 4 } else { 5 })),
            true,
        );
    }
    assert!(
        v.try_construct_finalization(&mut rng, &Sequential)
            .await
            .is_none()
    );
    let mut v = VerifierWith::<S, Digest, Extended>::new(proposal().round, f.verifier.clone(), 5);
    for i in 0..6 {
        v.add(
            VoteWith::Finalize(vote(&f, i, if i == 0 { 4 } else { 5 })),
            true,
        );
    }
    let batch = v
        .try_construct_finalization(&mut rng, &Sequential)
        .await
        .unwrap();
    assert!(batch.invalid.is_empty());
    assert!(
        batch
            .certificate
            .unwrap()
            .verify(&mut rng, &f.verifier, &Sequential)
    );
    // A signature made over different bytes is invalid, unlike an authentic alternate D.
    let mut v = verifier(&f);
    for i in 0..4 {
        v.add(VoteWith::Finalize(vote(&f, i, 5)), false);
    }
    let mut bad = EVote::sign(&f.schemes[4], statement(proposal(), 9)).unwrap();
    bad.statement.extension = Digest::from([5; 32]);
    v.add(VoteWith::Finalize(EFinalize::new(bad).unwrap()), false);
    let batch = v
        .try_construct_finalization(&mut rng, &Sequential)
        .await
        .unwrap();
    assert_eq!(batch.invalid, vec![Participant::new(4)]);
    assert!(batch.certificate.is_none());
    v.add(VoteWith::Finalize(vote(&f, 5, 5)), false);
    let batch = v
        .try_construct_finalization(&mut rng, &Sequential)
        .await
        .unwrap();
    assert!(batch.invalid.is_empty());
    assert!(
        batch
            .certificate
            .unwrap()
            .verify(&mut rng, &f.verifier, &Sequential)
    );
    // A duplicate identity cannot inflate a group to quorum.
    let mut v = verifier(&f);
    for _ in 0..6 {
        v.add(VoteWith::Finalize(vote(&f, 0, 5)), true);
    }
    assert!(
        v.try_construct_finalization(&mut rng, &Sequential)
            .await
            .is_none()
    );
    // Base votes retain the stock P-only notarization path despite different reports.
    let mut v = verifier(&f);
    for i in 0..5 {
        let n = ENotarize::new(
            Notarize::sign(&f.schemes[i], proposal()).unwrap(),
            Some(bytes::Bytes::from(vec![i as u8])),
        )
        .unwrap();
        v.add(VoteWith::Notarize(n), false);
    }
    let batch = v
        .try_construct_notarization(&mut rng, &Sequential)
        .await
        .unwrap();
    assert!(batch.invalid.is_empty());
    assert!(matches!(
        batch.certificate,
        Some(CertificateWith::Notarization(_))
    ));
    assert!(
        batch
            .certificate
            .unwrap()
            .verify(&mut rng, &f.verifier, &Sequential)
    );
    // Plain uses the same public verifier entry points and unchanged final subject.
    let p = proposal();
    let mut plain = VerifierWith::<S, Digest, Plain>::new(p.round, f.verifier.clone(), 5);
    plain.set_leader(
        Participant::new(0),
        Some(&Notarize::sign(&f.schemes[0], p.clone()).unwrap()),
    );
    for i in 0..5 {
        plain.add(
            VoteWith::Finalize(Finalize::sign(&f.schemes[i], p.clone()).unwrap()),
            false,
        );
    }
    let batch = plain
        .try_construct_finalization(&mut rng, &Sequential)
        .await
        .unwrap();
    assert!(batch.invalid.is_empty());
    assert!(
        batch
            .certificate
            .unwrap()
            .verify(&mut rng, &f.verifier, &Sequential)
    );
}
const NS: &[u8] = b"_COMMONWARE_CONSENSUS_EXTENSION_VERIFIER_TEST";
#[test]
fn ed25519_exact_groups() {
    deterministic::Runner::default().start(|_| async {
        exercise(ed25519::fixture(&mut TestRng::new(1), NS, 6)).await;
    });
}
#[test]
fn multisig_exact_groups() {
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
fn threshold_exact_groups() {
    deterministic::Runner::default().start(|_| async {
        exercise(standard::fixture::<MinSig, _>(&mut TestRng::new(3), NS, 6)).await;
    });
}
#[test]
fn vrf_exact_groups() {
    deterministic::Runner::default().start(|_| async {
        exercise(vrf::fixture::<MinSig, _>(&mut TestRng::new(4), NS, 6)).await;
    });
}
#[test]
fn proposal_switch_releases_only_removed_subjects_and_identity_slots() {
    deterministic::Runner::default().start(|_| async {
        let f = ed25519::fixture(&mut TestRng::new(5), NS, 6);
        let mut groups = Groups::new(5, 6);
        for i in 0..3 {
            groups.push(vote(&f, i, 4), false);
        }
        let p = Proposal::new(proposal().round, View::new(1), Digest::from([9; 32]));
        groups.retain_proposal(&p);
        for i in 0..5 {
            groups.push(
                EFinalize::new(EVote::sign(&f.schemes[i], statement(p.clone(), 5)).unwrap())
                    .unwrap(),
                false,
            );
        }
        let batch = groups
            .construct(
                &std::sync::Arc::new(f.verifier.clone()),
                p.round,
                &mut TestRng::new(6),
                &Sequential,
            )
            .await
            .unwrap();
        assert!(batch.invalid.is_empty());
        assert_eq!(
            batch.certificate.unwrap().certificate().statement.proposal,
            p
        );
        assert!(groups.is_complete());
        groups.complete();
        assert!(!groups.has_constructable_quorum());
    });
}
