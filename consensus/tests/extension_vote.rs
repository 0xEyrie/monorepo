//! Real native-scheme authentication of the extension final-vote subject.
//! These are crypto/codec/fence integration checks, not consensus network tests.

use commonware_codec::{Decode as _, DecodeExt as _, Encode as _};
use commonware_consensus::{
    simplex::{
        extension::vote::{Certificate, Error, Statement, Vote},
        scheme::{
            self, bls12381_multisig,
            bls12381_threshold::{standard, vrf},
            ed25519,
        },
        types::{Finalize, Proposal, Subject},
    },
    types::{Epoch, Round, View},
};
use commonware_cryptography::{
    Sha256,
    bls12381::primitives::variant::MinSig,
    certificate::{AssemblyError, Subject as _, mocks::Fixture},
    sha256::Digest,
};
use commonware_parallel::Sequential;
use commonware_utils::{TestRng, iter::NonEmpty};

const NS: &[u8] = b"_COMMONWARE_CONSENSUS_EXTENSION_VOTE_TEST";
fn hash(byte: u8) -> Digest {
    Digest::from([byte; 32])
}
fn statement() -> Statement<Digest> {
    let round = Round::new(Epoch::new(7), View::new(2));
    Statement {
        proposal: Proposal::new(round, View::new(1), hash(1)),
        domain: hash(2),
        ballot: round,
        parent: hash(3),
        extension: hash(4),
    }
}
fn nonempty<T>(items: Vec<T>) -> NonEmpty<std::vec::IntoIter<T>> {
    let mut iter = items.into_iter();
    NonEmpty::new(iter.next().unwrap(), iter)
}
fn votes<S: scheme::Scheme<Digest>>(
    fixture: &Fixture<S>,
    subject: &Statement<Digest>,
    count: usize,
) -> Vec<Vote<S, Digest>> {
    fixture
        .schemes
        .iter()
        .take(count)
        .map(|scheme| Vote::sign(scheme, subject.clone()).unwrap())
        .collect()
}

fn check_scheme<S: scheme::Scheme<Digest>>(fixture: Fixture<S>) {
    let mut rng = TestRng::new(91);
    let subject = statement();
    let proof = Certificate::from_votes(
        &mut rng,
        &fixture.verifier,
        nonempty(votes(&fixture, &subject, 5)),
        &Sequential,
    )
    .unwrap();
    assert!(proof.verify(&mut rng, &fixture.verifier, &Sequential));
    let encoded = proof.encode();
    let decoded = Certificate::<S, Digest>::decode_cfg(
        encoded.clone(),
        &fixture.verifier.certificate_codec_config(),
    )
    .unwrap();
    assert_eq!(decoded.encode(), encoded);
    assert!(decoded.verify(&mut rng, &fixture.verifier, &Sequential));
    let vote = Vote::sign(&fixture.schemes[0], subject.clone()).unwrap();
    let decoded = Vote::<S, Digest>::decode(vote.encode()).unwrap();
    assert!(decoded.verify(&mut rng, &fixture.verifier, &Sequential));

    // Every interpretation dimension is covered by the signature.
    let mut alternatives = Vec::new();
    let mut changed = subject.clone();
    changed.domain = hash(9);
    alternatives.push(changed);
    let mut changed = subject.clone();
    changed.parent = hash(9);
    alternatives.push(changed);
    let mut changed = subject.clone();
    changed.extension = hash(9);
    alternatives.push(changed);
    let mut changed = subject.clone();
    changed.proposal.payload = hash(9);
    alternatives.push(changed);
    let mut changed = subject.clone();
    changed.proposal.parent = View::zero();
    alternatives.push(changed);
    let mut changed = subject.clone();
    changed.ballot = Round::new(Epoch::new(7), View::new(4));
    alternatives.push(changed);
    for changed in alternatives {
        let bad = Certificate::<S, Digest> {
            statement: changed,
            certificate: proof.certificate.clone(),
        };
        assert!(!bad.verify(&mut rng, &fixture.verifier, &Sequential));
    }

    // Ordinary finalize signatures cannot approve an extension, nor vice versa.
    let plain = Finalize::sign(&fixture.schemes[0], subject.proposal.clone()).unwrap();
    assert!(plain.verify(&mut rng, &fixture.verifier, &Sequential));
    let wrong = Vote::<S, Digest> {
        statement: subject.clone(),
        attestation: plain.attestation,
    };
    assert!(!wrong.verify(&mut rng, &fixture.verifier, &Sequential));
    assert!(!fixture.verifier.verify_attestation::<_, Digest>(
        &mut rng,
        Subject::Finalize {
            proposal: &subject.proposal
        },
        &vote.attestation,
        &Sequential
    ));
    assert_eq!(
        Subject::Finalize {
            proposal: &subject.proposal
        }
        .message(),
        subject.proposal.encode()
    );
    assert_eq!(
        Subject::Notarize {
            proposal: &subject.proposal
        }
        .message(),
        subject.proposal.encode()
    );
    let nullify: Subject<'_, Digest> = Subject::Nullify {
        round: subject.proposal.round,
    };
    assert_eq!(nullify.message(), subject.proposal.round.encode());

    // The six-node native quorum remains five, not the route-support threshold three.
    assert!(matches!(
        Certificate::from_votes(
            &mut rng,
            &fixture.verifier,
            nonempty(votes(&fixture, &subject, 4)),
            &Sequential
        ),
        Err(Error::Assembly(AssemblyError::InsufficientAttestations(
            5, 4
        )))
    ));
    let mut duplicate = votes(&fixture, &subject, 5);
    duplicate[4] = duplicate[0].clone();
    assert!(matches!(
        Certificate::from_votes(
            &mut rng,
            &fixture.verifier,
            nonempty(duplicate),
            &Sequential
        ),
        Err(Error::Assembly(AssemblyError::DuplicateSigner(_)))
    ));
    let mut mixed = votes(&fixture, &subject, 5);
    let mut other = subject.clone();
    other.extension = hash(99);
    mixed[4] = Vote::sign(&fixture.schemes[4], other).unwrap();
    assert!(matches!(
        Certificate::from_votes(&mut rng, &fixture.verifier, nonempty(mixed), &Sequential),
        Err(Error::Subject)
    ));

    let mut malformed = subject.clone();
    malformed.ballot = Round::new(Epoch::new(7), View::new(1));
    assert!(Vote::sign(&fixture.schemes[0], malformed).is_none());
    let mut malformed = subject.clone();
    malformed.ballot = Round::new(Epoch::new(8), View::new(2));
    assert!(Vote::sign(&fixture.schemes[0], malformed).is_none());
    let mut recovery = subject.clone();
    recovery.ballot = Round::new(Epoch::new(7), View::new(9));
    let proof = Certificate::from_votes(
        &mut rng,
        &fixture.verifier,
        nonempty(votes(&fixture, &recovery, 5)),
        &Sequential,
    )
    .unwrap();
    assert!(proof.verify(&mut rng, &fixture.verifier, &Sequential));
    assert_eq!(subject.slot::<Sha256>(), recovery.slot::<Sha256>());
    assert_eq!(subject.value::<Sha256>(), recovery.value::<Sha256>());
}

#[test]
fn ed25519_exact_extension_subject() {
    check_scheme(ed25519::fixture(&mut TestRng::new(0), NS, 6));
}
#[test]
fn bls_multisig_exact_extension_subject() {
    check_scheme(bls12381_multisig::fixture::<MinSig, _>(
        &mut TestRng::new(0),
        NS,
        6,
    ));
}
#[test]
fn bls_threshold_exact_extension_subject() {
    check_scheme(standard::fixture::<MinSig, _>(&mut TestRng::new(0), NS, 6));
}
#[test]
fn bls_vrf_exact_extension_subject() {
    check_scheme(vrf::fixture::<MinSig, _>(&mut TestRng::new(0), NS, 6));
}

#[test]
fn slot_is_stable_when_parent_interpretation_changes() {
    let a = statement();
    let mut b = a.clone();
    b.parent = hash(44);
    assert_eq!(a.slot::<Sha256>(), b.slot::<Sha256>());
    assert_ne!(a.value::<Sha256>(), b.value::<Sha256>());
    b = a.clone();
    b.domain = hash(44);
    assert_ne!(a.slot::<Sha256>(), b.slot::<Sha256>());
    b = a.clone();
    b.proposal.payload = hash(44);
    assert_ne!(a.slot::<Sha256>(), b.slot::<Sha256>());
}

#[test]
fn statement_codec_rejects_truncation_and_unknown_version() {
    let bytes = statement().encode();
    assert_eq!(
        Statement::<Digest>::decode(bytes.clone()).unwrap(),
        statement()
    );
    for end in 0..bytes.len() {
        assert!(Statement::<Digest>::decode(bytes.slice(..end)).is_err());
    }
    let mut changed = bytes.to_vec();
    changed[0] = 2;
    assert!(Statement::<Digest>::decode(changed).is_err());
}

#[cfg(feature = "arbitrary")]
mod conformance {
    use super::*;
    use commonware_codec::conformance::CodecConformance;
    type OriginalScheme = vrf::Scheme<commonware_cryptography::ed25519::PublicKey, MinSig>;
    commonware_conformance::conformance_tests! {
        CodecConformance<Proposal<Digest>>,
        CodecConformance<Finalize<OriginalScheme, Digest>>,
        CodecConformance<commonware_consensus::simplex::types::Finalization<OriginalScheme, Digest>>,
        CodecConformance<Statement<Digest>>,
        CodecConformance<Vote<ed25519::Scheme, Digest>>,
        CodecConformance<Certificate<ed25519::Scheme, Digest>>,
    }
}

#[cfg(not(target_arch = "wasm32"))]
#[test]
fn native_statement_signing_fence_survives_restart() {
    use commonware_consensus::simplex::extension::fence::{Error as FenceError, Fence};
    use commonware_runtime::{
        Runner as _, Supervisor as _, buffer::paged::CacheRef, deterministic,
    };
    use commonware_storage::journal::segmented::variable::Config;
    use commonware_utils::{NZU16, NZUsize};
    let subject = statement();
    let fixture = ed25519::fixture(&mut TestRng::new(0), NS, 6);
    let signers = fixture.schemes;
    let (signed, checkpoint) =
        deterministic::Runner::default().start_and_recover(move |context| async move {
            let cfg = Config {
                partition: "native-vote-fence".into(),
                compression: None,
                codec_config: NZUsize!(4),
                page_cache: CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(8)),
                write_buffer: NZUsize!(1024),
            };
            let mut fence = Fence::open(context.child("fence"), cfg, NZUsize!(8), NZUsize!(1024))
                .await
                .unwrap();
            fence
                .vote(
                    subject.ballot.view().get(),
                    vec![(subject.slot::<Sha256>(), subject.value::<Sha256>())],
                )
                .await
                .unwrap();
            Vote::sign(&signers[0], subject).unwrap()
        });
    assert!(signed.verify(&mut TestRng::new(2), &fixture.verifier, &Sequential));
    deterministic::Runner::from(checkpoint).start(move |context| async move {
        let cfg = Config {
            partition: "native-vote-fence".into(),
            compression: None,
            codec_config: NZUsize!(4),
            page_cache: CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(8)),
            write_buffer: NZUsize!(1024),
        };
        let mut fence = Fence::open(context.child("recovered"), cfg, NZUsize!(8), NZUsize!(1024))
            .await
            .unwrap();
        let mut conflicting = signed.statement;
        conflicting.parent = hash(99);
        assert!(matches!(
            fence
                .vote(
                    conflicting.ballot.view().get(),
                    vec![(conflicting.slot::<Sha256>(), conflicting.value::<Sha256>())]
                )
                .await,
            Err(FenceError::Conflict)
        ));
    });
}
