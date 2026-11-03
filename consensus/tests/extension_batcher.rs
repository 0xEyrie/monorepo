//! Exact-subject native batcher collection and certificate-role regressions.
//! The live voter/transport are not enabled by these component tests.

use commonware_codec::{Decode as _, Encode as _};
use commonware_consensus::{
    simplex::{
        extension::{
            CollectError, CollectOutcome, Collector,
            certificate::{Certificate, Finalization, Recovered},
            vote::{Statement, Vote},
        },
        scheme::{
            self, bls12381_multisig,
            bls12381_threshold::{standard, vrf},
            ed25519,
        },
        types::Proposal,
    },
    types::{Epoch, Round, View},
};
use commonware_cryptography::{
    bls12381::primitives::variant::MinSig, certificate::mocks::Fixture, sha256::Digest,
};
use commonware_parallel::Sequential;
use commonware_utils::TestRng;
use std::sync::Arc;
const NS: &[u8] = b"_COMMONWARE_CONSENSUS_EXTENSION_BATCHER_TEST";
fn hash(byte: u8) -> Digest {
    Digest::from([byte; 32])
}
fn statement() -> Statement<Digest> {
    let round = Round::new(Epoch::new(2), View::new(4));
    Statement {
        proposal: Proposal::new(round, View::new(3), hash(1)),
        domain: hash(2),
        ballot: round,
        parent: hash(3),
        extension: hash(4),
    }
}
fn collect<S: scheme::Scheme<Digest>>(
    fixture: &Fixture<S>,
    s: &Statement<Digest>,
) -> Certificate<S, Digest> {
    let mut collector = Collector::new(
        Arc::new(fixture.verifier.clone()),
        s.proposal.clone(),
        s.domain,
        s.ballot,
    )
    .unwrap();
    let mut result = None;
    let mut rng = TestRng::new(8);
    for i in 0..5 {
        let vote = Vote::sign(&fixture.schemes[i], s.clone()).unwrap();
        match collector.insert(&mut rng, vote, &Sequential).unwrap() {
            CollectOutcome::Pending => assert!(i < 4),
            CollectOutcome::Certificate(certificate) => {
                assert_eq!(i, 4);
                result = Some(certificate);
            }
            other => panic!("unexpected result {other:?}"),
        }
    }
    let vote = Vote::sign(&fixture.schemes[5], s.clone()).unwrap();
    assert!(matches!(
        collector.insert(&mut rng, vote, &Sequential),
        Ok(CollectOutcome::Complete)
    ));
    result.unwrap()
}
fn check_scheme<S: scheme::Scheme<Digest>>(fixture: Fixture<S>) {
    let s = statement();
    let certificate = collect(&fixture, &s);
    assert!(matches!(&certificate, Certificate::Finalization(_)));
    assert!(certificate.verify(&mut TestRng::new(9), &fixture.verifier, &Sequential));
    assert_eq!(certificate.certificate().statement, s);
    let bytes = certificate.encode();
    let cfg = fixture.verifier.certificate_codec_config();
    assert_eq!(
        Certificate::<S, Digest>::decode_cfg(bytes.clone(), &cfg)
            .unwrap()
            .encode(),
        bytes
    );
    // Changing the explicit role cannot turn a normal certificate into recovery.
    let mut wrong = bytes.to_vec();
    wrong[1] = 1;
    assert!(Certificate::<S, Digest>::decode_cfg(wrong, &cfg).is_err());
    let mut later = s.clone();
    later.ballot = Round::new(s.ballot.epoch(), View::new(5));
    let recovered = collect(&fixture, &later);
    assert!(matches!(&recovered, Certificate::Recovered(_)));
    assert!(recovered.verify(&mut TestRng::new(10), &fixture.verifier, &Sequential));
    assert!(Finalization::new(recovered.certificate().clone()).is_err());
    assert!(Recovered::new(certificate.certificate().clone()).is_err());
    let encoded = recovered.encode();
    let mut wrong = encoded.to_vec();
    wrong[1] = 0;
    assert!(Certificate::<S, Digest>::decode_cfg(wrong, &cfg).is_err());
    // No relabeling as native finality: changing the signed ballot breaks the proof.
    let mut altered = recovered.certificate().clone();
    altered.statement.ballot = s.ballot;
    let altered = Certificate::classify(altered).unwrap();
    assert!(!altered.verify(&mut TestRng::new(11), &fixture.verifier, &Sequential));
    for end in 0..encoded.len() {
        assert!(Certificate::<S, Digest>::decode_cfg(encoded.slice(..end), &cfg).is_err());
    }
    let mut wrong = encoded.to_vec();
    wrong[0] = 2;
    assert!(Certificate::<S, Digest>::decode_cfg(wrong, &cfg).is_err());
    let mut wrong = encoded.to_vec();
    wrong[1] = 2;
    assert!(Certificate::<S, Digest>::decode_cfg(wrong, &cfg).is_err());
}
#[test]
fn ed25519_collection_and_role_binding() {
    check_scheme(ed25519::fixture(&mut TestRng::new(0), NS, 6));
}
#[test]
fn bls_multisig_collection_and_role_binding() {
    check_scheme(bls12381_multisig::fixture::<MinSig, _>(
        &mut TestRng::new(0),
        NS,
        6,
    ));
}
#[test]
fn bls_threshold_collection_and_role_binding() {
    check_scheme(standard::fixture::<MinSig, _>(&mut TestRng::new(0), NS, 6));
}
#[test]
fn bls_vrf_collection_and_role_binding() {
    check_scheme(vrf::fixture::<MinSig, _>(&mut TestRng::new(0), NS, 6));
}
#[test]
fn split_directions_never_share_a_quorum_for_the_same_proposal() {
    let fixture = ed25519::fixture(&mut TestRng::new(0), NS, 6);
    let s = statement();
    let mut other = s.clone();
    other.extension = hash(7);
    let mut collector = Collector::new(
        Arc::new(fixture.verifier.clone()),
        s.proposal.clone(),
        s.domain,
        s.ballot,
    )
    .unwrap();
    let mut rng = TestRng::new(2);
    for (i, scheme) in fixture.schemes.iter().enumerate() {
        let statement = if i < 3 { &s } else { &other };
        assert!(matches!(
            collector.insert(
                &mut rng,
                Vote::sign(scheme, statement.clone()).unwrap(),
                &Sequential
            ),
            Ok(CollectOutcome::Pending)
        ));
    }
    // One identity cannot move its already counted vote to complete another group.
    assert!(matches!(
        collector.insert(
            &mut rng,
            Vote::sign(&fixture.schemes[3], s.clone()).unwrap(),
            &Sequential
        ),
        Ok(CollectOutcome::Equivocation { .. })
    ));
    assert!(matches!(
        collector.insert(
            &mut rng,
            Vote::sign(&fixture.schemes[0], s).unwrap(),
            &Sequential
        ),
        Ok(CollectOutcome::Duplicate)
    ));
}
#[test]
fn invalid_votes_do_not_reserve_identities_or_create_equivocation_evidence() {
    let fixture = ed25519::fixture(&mut TestRng::new(0), NS, 6);
    let s = statement();
    let mut other = s.clone();
    other.parent = hash(8);
    let mut collector = Collector::new(
        Arc::new(fixture.verifier.clone()),
        s.proposal.clone(),
        s.domain,
        s.ballot,
    )
    .unwrap();
    let mut rng = TestRng::new(2);
    let mut bad = Vote::sign(&fixture.schemes[0], s.clone()).unwrap();
    bad.statement = other;
    assert!(matches!(
        collector.insert(&mut rng, bad.clone(), &Sequential),
        Err(CollectError::Signature)
    ));
    let good = Vote::sign(&fixture.schemes[0], s.clone()).unwrap();
    assert!(matches!(
        collector.insert(&mut rng, good, &Sequential),
        Ok(CollectOutcome::Pending)
    ));
    assert!(matches!(
        collector.insert(&mut rng, bad, &Sequential),
        Err(CollectError::Signature)
    ));
    let mut wrong = s.clone();
    wrong.proposal.payload = hash(9);
    assert!(matches!(
        collector.insert(
            &mut rng,
            Vote::sign(&fixture.schemes[1], wrong).unwrap(),
            &Sequential
        ),
        Err(CollectError::Context)
    ));
    for i in 1..5 {
        let outcome = collector
            .insert(
                &mut rng,
                Vote::sign(&fixture.schemes[i], s.clone()).unwrap(),
                &Sequential,
            )
            .unwrap();
        if i == 4 {
            assert!(matches!(outcome, CollectOutcome::Certificate(_)));
        } else {
            assert!(matches!(outcome, CollectOutcome::Pending));
        }
    }
}
#[test]
fn collector_rejects_earlier_and_cross_epoch_ballots() {
    let fixture = ed25519::fixture(&mut TestRng::new(0), NS, 6);
    let s = statement();
    for ballot in [
        Round::new(s.ballot.epoch(), View::new(3)),
        Round::new(Epoch::new(3), View::new(5)),
    ] {
        assert!(matches!(
            Collector::new(
                Arc::new(fixture.verifier.clone()),
                s.proposal.clone(),
                s.domain,
                ballot
            ),
            Err(CollectError::Context)
        ));
    }
}
#[cfg(feature = "arbitrary")]
mod conformance {
    use super::*;
    use commonware_codec::conformance::CodecConformance;
    commonware_conformance::conformance_tests! {CodecConformance<Certificate<ed25519::Scheme,Digest>> => 1024,}
}

#[test]
fn authenticated_peer_must_match_the_partial_signature_identity() {
    let fixture = vrf::fixture::<MinSig, _>(&mut TestRng::new(0), NS, 6);
    let s = statement();
    let mut collector = Collector::new(
        Arc::new(fixture.verifier.clone()),
        s.proposal.clone(),
        s.domain,
        s.ballot,
    )
    .unwrap();
    let vote = Vote::sign(&fixture.schemes[0], s).unwrap();
    let mut rng = TestRng::new(3);
    assert!(matches!(
        collector.insert_from(
            &mut rng,
            &fixture.participants[1],
            vote.clone(),
            &Sequential
        ),
        Err(CollectError::Signature)
    ));
    assert!(matches!(
        collector.insert_from(&mut rng, &fixture.participants[0], vote, &Sequential),
        Ok(CollectOutcome::Pending)
    ));
}
