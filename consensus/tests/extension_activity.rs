//! Exact extension fault evidence and native scheme attribution filtering.
use commonware_actor::Feedback;
use commonware_codec::{Decode as _, DecodeExt as _, Encode as _};
use commonware_consensus::{
    Reporter,
    simplex::{
        extension::{
            certificate::{Finalization as EC, Finalize as EF},
            report::Notarize as EN,
            vote::{Certificate as CertificateProof, Statement, Vote as EV},
        },
        phase2::Extended,
        scheme::{
            self, bls12381_multisig,
            bls12381_threshold::{standard, vrf},
            ed25519,
            reporter::AttributableReporterWith,
        },
        types::{
            ActivityWith, ConflictingFinalizeWith, Notarize, Nullify, NullifyFinalizeWith, Proposal,
        },
    },
    types::{Epoch, Round, View},
};
use commonware_cryptography::{
    bls12381::primitives::variant::MinSig, certificate::mocks::Fixture, sha256::Digest,
};
use commonware_parallel::Sequential;
use commonware_utils::{TestRng, iter::NonEmpty, sync::Mutex};
use std::sync::Arc;
type A<S> = ActivityWith<S, Digest, Extended>;
type Conflict<S> = ConflictingFinalizeWith<S, Digest, Extended>;
type Skip<S> = NullifyFinalizeWith<S, Digest, Extended>;
fn statement() -> Statement<Digest> {
    let round = Round::new(Epoch::new(1), View::new(2));
    Statement {
        proposal: Proposal::new(round, View::new(1), Digest::from([1; 32])),
        ballot: round,
        domain: Digest::from([2; 32]),
        parent: Digest::from([3; 32]),
        extension: Digest::from([4; 32]),
    }
}
fn pair_bytes<S: scheme::Scheme<Digest>>(a: &EF<S, Digest>, b: &EF<S, Digest>) -> Vec<u8> {
    let mut out = a.encode().to_vec();
    out.extend_from_slice(&b.encode());
    out
}
#[derive(Clone)]
struct Record<S: scheme::Scheme<Digest>> {
    events: Arc<Mutex<Vec<A<S>>>>,
}
impl<S: scheme::Scheme<Digest>> Reporter for Record<S> {
    type Activity = A<S>;
    fn report(&mut self, activity: Self::Activity) -> Feedback {
        self.events.lock().push(activity);
        Feedback::Ok
    }
}
fn exercise<S: scheme::Scheme<Digest>>(f: Fixture<S>) {
    let mut rng = TestRng::new(91);
    let a = statement();
    let cfg = commonware_cryptography::certificate::Verifier::certificate_codec_config(&f.verifier);
    let vote = Notarize::sign(&f.schemes[0], a.proposal.clone()).unwrap();
    let report = bytes::Bytes::from_static(b"independently-authenticated-route");
    let carried = A::Notarize(EN::new(vote.clone(), Some(report.clone())).unwrap());
    let encoded = carried.encode();
    assert_eq!(A::<S>::decode_cfg(encoded.clone(), &cfg).unwrap(), carried);
    for end in 0..encoded.len() {
        assert!(A::<S>::decode_cfg(encoded.slice(..end), &cfg).is_err());
    }
    assert!(!carried.verified());
    assert!(carried.verify(&mut rng, &f.verifier, &Sequential));
    // Native verification authenticates P only. The SDK must reject forged route
    // bytes itself, even when the enclosing native vote is valid.
    let changed =
        A::Notarize(EN::new(vote, Some(bytes::Bytes::from_static(b"forged-route"))).unwrap());
    assert_ne!(carried, changed);
    assert!(changed.verify(&mut rng, &f.verifier, &Sequential));
    let A::Notarize(decoded) = A::<S>::decode_cfg(encoded, &cfg).unwrap() else {
        panic!("wrong activity");
    };
    assert_eq!(decoded.report(), Some(&report));
    let mut b = a.clone();
    b.extension = Digest::from([5; 32]);
    let first = EF::new(EV::sign(&f.schemes[0], a.clone()).unwrap()).unwrap();
    let second = EF::new(EV::sign(&f.schemes[0], b.clone()).unwrap()).unwrap();
    let proof = Conflict::new(first.clone(), second);
    assert!(proof.verify(&mut rng, &f.verifier, &Sequential));
    let decoded = Conflict::<S>::decode(proof.encode()).unwrap();
    assert_eq!(decoded, proof);
    let activity = A::ConflictingFinalize(proof.clone());
    assert!(!activity.verified());
    assert!(activity.verify(&mut rng, &f.verifier, &Sequential));
    // P is unchanged; parent interpretation alone can also constitute a conflict.
    let mut parent = a.clone();
    parent.parent = Digest::from([9; 32]);
    assert!(
        Conflict::new(
            first.clone(),
            EF::new(EV::sign(&f.schemes[0], parent).unwrap()).unwrap()
        )
        .verify(&mut rng, &f.verifier, &Sequential)
    );
    // Exact duplicate, different signer, different round and different domain are not this evidence.
    assert!(Conflict::<S>::decode(pair_bytes(&first, &first)).is_err());
    assert!(
        Conflict::<S>::decode(pair_bytes(
            &first,
            &EF::new(EV::sign(&f.schemes[1], b.clone()).unwrap()).unwrap()
        ))
        .is_err()
    );
    let mut later = b.clone();
    later.proposal.round = Round::new(later.ballot.epoch(), View::new(3));
    later.ballot = later.proposal.round;
    assert!(
        Conflict::<S>::decode(pair_bytes(
            &first,
            &EF::new(EV::sign(&f.schemes[0], later).unwrap()).unwrap()
        ))
        .is_err()
    );
    let mut domain = b.clone();
    domain.domain = Digest::from([9; 32]);
    assert!(
        Conflict::<S>::decode(pair_bytes(
            &first,
            &EF::new(EV::sign(&f.schemes[0], domain).unwrap()).unwrap()
        ))
        .is_err()
    );
    let mut bad = EV::sign(&f.schemes[0], a.clone()).unwrap();
    bad.statement = b;
    let bad = EF::new(bad).unwrap();
    let forged = A::ConflictingFinalize(Conflict::new(first.clone(), bad));
    assert!(!forged.verify(&mut rng, &f.verifier, &Sequential));
    let nullify = Nullify::sign::<Digest>(&f.schemes[0], a.ballot).unwrap();
    let skip = Skip::new(nullify, first.clone());
    assert!(skip.verify(&mut rng, &f.verifier, &Sequential));
    assert_eq!(Skip::<S>::decode(skip.encode()).unwrap(), skip);
    let wrong_nullify = Nullify::sign::<Digest>(&f.schemes[1], a.ballot).unwrap();
    let mut bytes = wrong_nullify.encode().to_vec();
    bytes.extend_from_slice(&first.encode());
    assert!(Skip::<S>::decode(bytes).is_err());
    let mut bytes =
        Nullify::sign::<Digest>(&f.schemes[0], Round::new(a.ballot.epoch(), View::new(3)))
            .unwrap()
            .encode()
            .to_vec();
    bytes.extend_from_slice(&first.encode());
    assert!(Skip::<S>::decode(bytes).is_err());
    let bytes = activity.encode();
    let cfg = commonware_cryptography::certificate::Verifier::certificate_codec_config(&f.verifier);
    assert_eq!(A::<S>::decode_cfg(bytes.clone(), &cfg).unwrap(), activity);
    for end in 0..bytes.len() {
        assert!(A::<S>::decode_cfg(bytes.slice(..end), &cfg).is_err());
    }
    let events = Arc::new(Mutex::new(Vec::new()));
    let recorder = Record {
        events: events.clone(),
    };
    let mut reporter = AttributableReporterWith::<_, _, _, _, _, Extended>::new(
        TestRng::new(92),
        f.verifier.clone(),
        recorder,
        Sequential,
        true,
    );
    reporter.report(forged);
    assert!(events.lock().is_empty());
    reporter.report(activity);
    reporter.report(A::NullifyFinalize(skip));
    reporter.report(A::Finalize(first));
    assert_eq!(
        events.lock().len(),
        if S::is_attributable() { 3 } else { 0 }
    );
    let mut votes = f
        .schemes
        .iter()
        .take(5)
        .map(|s| EV::sign(s, a.clone()).unwrap());
    let raw = CertificateProof::from_votes(
        &mut rng,
        &f.verifier,
        NonEmpty::new(votes.next().unwrap(), votes),
        &Sequential,
    )
    .unwrap();
    let cert = EC::new(raw).unwrap();
    assert!(A::Finalization(cert.clone()).verify(&mut rng, &f.verifier, &Sequential));
    reporter.report(A::Finalization(cert));
    assert_eq!(
        events.lock().len(),
        if S::is_attributable() { 4 } else { 1 }
    );
}
const NS: &[u8] = b"_COMMONWARE_CONSENSUS_EXTENSION_ACTIVITY_TEST";
#[test]
fn ed25519_activity() {
    exercise(ed25519::fixture(&mut TestRng::new(1), NS, 6));
}
#[test]
fn multisig_activity() {
    exercise(bls12381_multisig::fixture::<MinSig, _>(
        &mut TestRng::new(2),
        NS,
        6,
    ));
}
#[test]
fn threshold_activity() {
    exercise(standard::fixture::<MinSig, _>(&mut TestRng::new(3), NS, 6));
}
#[test]
fn vrf_activity() {
    exercise(vrf::fixture::<MinSig, _>(&mut TestRng::new(4), NS, 6));
}
#[cfg(feature = "arbitrary")]
mod conformance {
    use super::*;
    use commonware_codec::conformance::CodecConformance;
    use commonware_consensus::simplex::types::{Activity, ConflictingFinalize, NullifyFinalize};
    type OriginalScheme = vrf::Scheme<commonware_cryptography::ed25519::PublicKey, MinSig>;
    type EActivity = A<ed25519::Scheme>;
    type EConflict = Conflict<ed25519::Scheme>;
    type ESkip = Skip<ed25519::Scheme>;
    commonware_conformance::conformance_tests! {
        CodecConformance<Activity<OriginalScheme,Digest>>,
        CodecConformance<ConflictingFinalize<OriginalScheme,Digest>>,
        CodecConformance<NullifyFinalize<OriginalScheme,Digest>>,
        CodecConformance<EActivity> =>1024,
        CodecConformance<EConflict> =>1024,
        CodecConformance<ESkip> =>1024,
    }
}
