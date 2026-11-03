//! Production voter round retains exact accepted subjects through replay.
use commonware_consensus::{
    simplex::{
        extension::{
            certificate::Finalization as EC,
            report::Notarize as EN,
            vote::{Certificate as RawCertificate, Statement, Vote as EV},
        },
        phase2::{
            Extended, Plain,
            voting::{RoundWith, Voting},
        },
        scheme::{
            self, bls12381_multisig,
            bls12381_threshold::{standard, vrf},
            ed25519,
        },
        types::{ArtifactWith, Finalize, Notarization, Notarize, Nullify, Proposal},
    },
    types::{Epoch, Round, View},
};
use commonware_cryptography::{
    bls12381::primitives::variant::MinSig, certificate::mocks::Fixture, sha256::Digest,
};
use commonware_parallel::Sequential;
use commonware_utils::{TestRng, non_empty};
use std::time::SystemTime;
fn proposal() -> Proposal<Digest> {
    Proposal::new(
        Round::new(Epoch::new(1), View::new(2)),
        View::new(1),
        Digest::from([1; 32]),
    )
}
fn subject(d: u8) -> Statement<Digest> {
    let p = proposal();
    Statement {
        ballot: p.round,
        proposal: p,
        domain: Digest::from([2; 32]),
        parent: Digest::from([3; 32]),
        extension: Digest::from([d; 32]),
    }
}
fn notarization<S: scheme::Scheme<Digest>>(f: &Fixture<S>) -> Notarization<S, Digest> {
    let votes: Vec<_> = f
        .schemes
        .iter()
        .take(5)
        .map(|s| Notarize::sign(s, proposal()).unwrap())
        .collect();
    Notarization::from_notarizes(&f.verifier, non_empty![@&votes], &Sequential).unwrap()
}
fn ready<S: scheme::Scheme<Digest>>(f: &Fixture<S>) -> RoundWith<S, Digest, Extended> {
    let mut round = RoundWith::new(f.schemes[0].clone(), proposal().round);
    assert!(round.proposed(SystemTime::UNIX_EPOCH, proposal()));
    round.add_notarization(notarization(f));
    round.certified(true);
    round
}
fn exercise<S: scheme::Scheme<Digest>>(f: Fixture<S>) {
    let p = proposal();
    let chosen = subject(4);
    let alternate = subject(5);
    let mut rng = TestRng::new(44);
    let mut pending = RoundWith::<_, _, Extended>::new(f.schemes[0].clone(), p.round);
    pending.proposed(SystemTime::UNIX_EPOCH, p.clone());
    assert!(pending.construct_finalize_with(chosen.clone()).is_none());
    pending.add_notarization(notarization(&f));
    assert!(pending.construct_finalize_with(chosen.clone()).is_none());
    pending.certified(true);
    // Wrong P or a later recovery ballot must not consume the native decision.
    let mut wrong = chosen.clone();
    wrong.proposal.payload = Digest::from([99; 32]);
    assert!(pending.construct_finalize_with(wrong.clone()).is_none());
    assert!(
        <Extended as Voting<S, Digest>>::sign_finalize(&f.schemes[0], p.clone(), wrong).is_none()
    );
    let mut later = chosen.clone();
    later.ballot = Round::new(p.round.epoch(), View::new(3));
    assert!(pending.construct_finalize_with(later.clone()).is_none());
    assert!(
        <Extended as Voting<S, Digest>>::sign_finalize(&f.schemes[0], p.clone(), later).is_none()
    );
    assert!(pending.final_subject().is_none());
    assert_eq!(pending.construct_finalize_with(chosen.clone()), Some(&p));
    assert_eq!(pending.final_subject(), Some(&chosen));
    assert!(pending.construct_finalize_with(alternate.clone()).is_none());
    let vote =
        <Extended as Voting<S, Digest>>::sign_finalize(&f.schemes[0], p.clone(), chosen.clone())
            .unwrap();
    assert!(vote.vote().verify(&mut rng, &f.verifier, &Sequential));
    let first = EN::new(
        Notarize::sign(&f.schemes[0], p.clone()).unwrap(),
        Some(bytes::Bytes::from_static(b"opaque-route")),
    )
    .unwrap();
    let mut recovered = RoundWith::<_, _, Extended>::new(f.schemes[0].clone(), p.round);
    recovered.replay(&ArtifactWith::Notarize(first));
    recovered.replay(&ArtifactWith::Finalize(vote.clone()));
    recovered.replay(&ArtifactWith::Finalize(vote));
    recovered.add_notarization(notarization(&f));
    recovered.certified(true);
    assert_eq!(recovered.final_subject(), Some(&chosen));
    assert!(
        recovered
            .construct_finalize_with(alternate.clone())
            .is_none()
    );
    // A different authenticated final QC can supersede a minority local vote;
    // retain both the local signing decision and the exact canonical certificate.
    let votes: Vec<_> = f
        .schemes
        .iter()
        .skip(1)
        .map(|s| EV::sign(s, alternate.clone()).unwrap())
        .collect();
    let cert = EC::new(
        RawCertificate::from_votes(&mut rng, &f.verifier, non_empty![@votes], &Sequential).unwrap(),
    )
    .unwrap();
    assert!(
        cert.certificate()
            .verify(&mut rng, &f.verifier, &Sequential)
    );
    assert!(recovered.add_finalization(cert.clone()).0);
    assert_eq!(recovered.finalization(), Some(&cert));
    assert_eq!(recovered.certificate_ancestry_payload(), Some(&p.payload));
    assert_eq!(recovered.broadcast_finalization(), Some(cert.clone()));
    assert!(recovered.broadcast_finalization().is_none());
    assert_eq!(recovered.final_subject(), Some(&chosen));
    let mut certificate_replay = RoundWith::<_, _, Extended>::new(f.schemes[0].clone(), p.round);
    certificate_replay.add_finalization(cert.clone());
    certificate_replay.replay(&ArtifactWith::Finalization(cert));
    assert!(certificate_replay.broadcast_finalization().is_none());
    let mut skipped = ready(&f);
    skipped.replay(&ArtifactWith::Nullify(
        Nullify::sign::<Digest>(&f.schemes[0], p.round).unwrap(),
    ));
    assert!(skipped.construct_finalize_with(chosen).is_none());
    // Plain still uses unit local state and the original native signing subject.
    let mut plain = RoundWith::<_, _, Plain>::new(f.schemes[0].clone(), p.round);
    plain.proposed(SystemTime::UNIX_EPOCH, p.clone());
    plain.add_notarization(notarization(&f));
    plain.certified(true);
    assert_eq!(plain.construct_finalize(), Some(&p));
    assert_eq!(plain.final_subject(), Some(&()));
    assert!(plain.construct_finalize().is_none());
    assert_eq!(
        <Plain as Voting<S, Digest>>::sign_finalize(&f.schemes[0], p.clone(), ()),
        Finalize::sign(&f.schemes[0], p)
    );
}
const NS: &[u8] = b"_COMMONWARE_CONSENSUS_EXTENSION_VOTER_ROUND_TEST";
#[test]
fn ed25519_voter_round() {
    exercise(ed25519::fixture(&mut TestRng::new(1), NS, 6));
}
#[test]
fn multisig_voter_round() {
    exercise(bls12381_multisig::fixture::<MinSig, _>(
        &mut TestRng::new(2),
        NS,
        6,
    ));
}
#[test]
fn threshold_voter_round() {
    exercise(standard::fixture::<MinSig, _>(&mut TestRng::new(3), NS, 6));
}
#[test]
fn vrf_voter_round() {
    exercise(vrf::fixture::<MinSig, _>(&mut TestRng::new(4), NS, 6));
}
#[test]
#[should_panic(expected = "replayed conflicting final subjects")]
fn conflicting_durable_subjects_fail_closed() {
    let f = ed25519::fixture(&mut TestRng::new(5), NS, 6);
    let mut round = RoundWith::<_, _, Extended>::new(f.schemes[0].clone(), proposal().round);
    for d in [4, 5] {
        let vote =
            <Extended as Voting<_, Digest>>::sign_finalize(&f.schemes[0], proposal(), subject(d))
                .unwrap();
        round.replay(&ArtifactWith::Finalize(vote));
    }
}
