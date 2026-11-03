//! Real signatures and storage for recovery evidence; not a native network proof.

use commonware_codec::{Decode as _, DecodeExt as _, Encode as _};
use commonware_consensus::{
    simplex::{
        extension::{
            recovery::{Error, Promise, Proof, Status},
            vote::{Certificate, Statement, Vote},
        },
        scheme::{
            self, bls12381_multisig,
            bls12381_threshold::{standard, vrf},
            ed25519,
        },
        types::{Proposal, Subject},
    },
    types::{Epoch, Round, View},
};
use commonware_cryptography::{
    Sha256, bls12381::primitives::variant::MinSig, certificate::mocks::Fixture, sha256::Digest,
};
use commonware_parallel::Sequential;
use commonware_utils::{TestRng, iter::NonEmpty};
const NS: &[u8] = b"_COMMONWARE_CONSENSUS_EXTENSION_RECOVERY_TEST";
fn hash(byte: u8) -> Digest {
    Digest::from([byte; 32])
}
const fn round(view: u64) -> Round {
    Round::new(Epoch::new(1), View::new(view))
}
fn statement() -> Statement<Digest> {
    Statement {
        proposal: Proposal::new(round(2), View::new(1), hash(1)),
        domain: hash(2),
        ballot: round(3),
        parent: hash(3),
        extension: hash(4),
    }
}
fn promise(s: &Statement<Digest>, accepted: Option<Digest>) -> Promise<Digest> {
    Promise {
        proposal: s.proposal.clone(),
        domain: s.domain,
        ballot: s.ballot,
        accepted: accepted.map(|v| (round(2), v)),
    }
}
fn proof<S: scheme::Scheme<Digest>>(
    fixture: &Fixture<S>,
    s: &Statement<Digest>,
    values: &[Option<Digest>],
) -> Proof<S, Digest> {
    Proof {
        statuses: fixture
            .schemes
            .iter()
            .zip(values)
            .map(|(scheme, value)| Status::sign(scheme, promise(s, *value)).unwrap())
            .collect(),
    }
}
fn check_attributable<S: scheme::Scheme<Digest>>(fixture: Fixture<S>) {
    let s = statement();
    let x = s.value::<Sha256>();
    let mut y = s.clone();
    y.extension = hash(8);
    let mut rng = TestRng::new(1);
    let p = proof(
        &fixture,
        &s,
        &[Some(x), Some(x), Some(x), Some(y.value::<Sha256>()), None],
    );
    let checked = p
        .verify(&mut rng, &fixture.verifier, &s, &Sequential)
        .unwrap();
    assert_eq!(checked.forced_value(), Some(x));
    assert!(checked.permits::<Sha256>(&s));
    assert!(!checked.permits::<Sha256>(&y));
    let bytes = p.encode();
    let decoded = Proof::<S, Digest>::decode_cfg(bytes.clone(), &6).unwrap();
    assert_eq!(decoded.encode(), bytes);
    assert!(
        decoded
            .verify(&mut rng, &fixture.verifier, &s, &Sequential)
            .unwrap()
            .permits::<Sha256>(&s)
    );
    assert!(Proof::<S, Digest>::decode_cfg(bytes.clone(), &4).is_err());
    for end in 0..bytes.len() {
        assert!(Proof::<S, Digest>::decode_cfg(bytes.slice(..end), &6).is_err());
    }
    let decoded = Status::<S, Digest>::decode(p.statuses[0].encode()).unwrap();
    assert!(decoded.verify(&mut rng, &fixture.verifier, &Sequential));
    let empty = proof(&fixture, &s, &[None; 5])
        .verify(&mut rng, &fixture.verifier, &s, &Sequential)
        .unwrap();
    assert!(empty.permits::<Sha256>(&y));
    assert_eq!(empty.forced_value(), None);
    let mut other = s.clone();
    other.parent = hash(9);
    assert!(empty.permits::<Sha256>(&other));
    other = s.clone();
    other.domain = hash(9);
    assert!(!empty.permits::<Sha256>(&other));
    other = s.clone();
    other.proposal.payload = hash(9);
    assert!(!empty.permits::<Sha256>(&other));
    other = s.clone();
    other.ballot = round(4);
    assert!(!empty.permits::<Sha256>(&other));
}
#[test]
fn ed25519_status_proofs() {
    check_attributable(ed25519::fixture(&mut TestRng::new(0), NS, 6));
}
#[test]
fn bls_multisig_status_proofs() {
    check_attributable(bls12381_multisig::fixture::<MinSig, _>(
        &mut TestRng::new(0),
        NS,
        6,
    ));
}

#[test]
fn status_proof_preserves_a_hidden_certificate_for_every_omission_and_faulty_claim() {
    let fixture = ed25519::fixture(&mut TestRng::new(0), NS, 6);
    let mut rng = TestRng::new(3);
    let s = statement();
    let x = s.value::<Sha256>();
    let mut y = s.clone();
    y.extension = hash(7);
    let yv = y.value::<Sha256>();
    let mut original = s.clone();
    original.ballot = round(2);
    let mut votes = [0, 1, 2, 3, 5]
        .into_iter()
        .map(|i| Vote::sign(&fixture.schemes[i], original.clone()).unwrap());
    let certificate = Certificate::from_votes(
        &mut rng,
        &fixture.verifier,
        NonEmpty::new(votes.next().unwrap(), votes),
        &Sequential,
    )
    .unwrap();
    assert!(certificate.verify(&mut rng, &fixture.verifier, &Sequential));
    for omitted in 0..6 {
        for lie in [None, Some(x), Some(yv)] {
            let statuses = (0..6)
                .filter(|i| *i != omitted)
                .map(|i| {
                    let value = if i < 4 {
                        Some(x)
                    } else if i == 4 {
                        Some(yv)
                    } else {
                        lie
                    };
                    Status::sign(&fixture.schemes[i], promise(&s, value)).unwrap()
                })
                .collect();
            let checked = Proof { statuses }
                .verify(&mut rng, &fixture.verifier, &s, &Sequential)
                .unwrap();
            assert_eq!(checked.forced_value(), Some(x));
            assert!(checked.permits::<Sha256>(&s));
            assert!(!checked.permits::<Sha256>(&y));
        }
    }
}
#[test]
fn malformed_context_quorum_and_identities_do_not_authorize_recovery() {
    let fixture = ed25519::fixture(&mut TestRng::new(0), NS, 6);
    let s = statement();
    let mut rng = TestRng::new(4);
    let base = proof(&fixture, &s, &[None; 5]);
    let mut bad = base.clone();
    bad.statuses.pop();
    assert_eq!(
        bad.verify(&mut rng, &fixture.verifier, &s, &Sequential)
            .unwrap_err(),
        Error::Quorum
    );
    bad = base.clone();
    bad.statuses[4] = bad.statuses[0].clone();
    assert_eq!(
        bad.verify(&mut rng, &fixture.verifier, &s, &Sequential)
            .unwrap_err(),
        Error::Identity
    );
    bad = base.clone();
    bad.statuses.swap(1, 2);
    assert_eq!(
        bad.verify(&mut rng, &fixture.verifier, &s, &Sequential)
            .unwrap_err(),
        Error::Identity
    );
    bad = base.clone();
    bad.statuses[0].promise.accepted = Some((round(2), hash(9)));
    assert_eq!(
        bad.verify(&mut rng, &fixture.verifier, &s, &Sequential)
            .unwrap_err(),
        Error::Signature
    );
    let mut expected = s.clone();
    expected.ballot = round(4);
    assert_eq!(
        base.verify(&mut rng, &fixture.verifier, &expected, &Sequential)
            .unwrap_err(),
        Error::Context
    );
    bad = base.clone();
    for status in &mut bad.statuses {
        status.promise.ballot = round(4);
    }
    assert_eq!(
        bad.verify(&mut rng, &fixture.verifier, &expected, &Sequential)
            .unwrap_err(),
        Error::Signature
    );
    for changed in [0, 1, 2, 3, 4] {
        let mut p = promise(&s, None);
        match changed {
            0 => p.ballot = round(2),
            1 => p.ballot = Round::new(Epoch::new(2), View::new(3)),
            2 => p.accepted = Some((round(1), hash(1))),
            3 => p.accepted = Some((round(3), hash(1))),
            _ => p.accepted = Some((Round::new(Epoch::new(2), View::new(2)), hash(1))),
        }
        assert!(matches!(
            Status::sign(&fixture.schemes[0], p),
            Err(Error::Context)
        ));
    }
    let final_vote = Vote::sign(&fixture.schemes[0], s.clone()).unwrap();
    let status = Status {
        promise: promise(&s, None),
        attestation: final_vote.attestation,
    };
    assert!(!status.verify(&mut rng, &fixture.verifier, &Sequential));
    let status = base.statuses[0].clone();
    let wrong_vote = Vote {
        statement: s,
        attestation: status.attestation,
    };
    assert!(!wrong_vote.verify(&mut rng, &fixture.verifier, &Sequential));
}
fn reject_threshold<S: scheme::Scheme<Digest>>(fixture: Fixture<S>) {
    let p = promise(&statement(), None);
    assert!(matches!(
        Status::sign(&fixture.schemes[0], p.clone()),
        Err(Error::Attribution)
    ));
    // Even a cryptographically valid native partial is not transferable attribution.
    let attestation = fixture.schemes[0]
        .sign::<Digest>(Subject::ExtensionStatus { promise: &p })
        .unwrap();
    let raw = Status {
        promise: p,
        attestation,
    };
    assert!(!raw.verify(&mut TestRng::new(3), &fixture.verifier, &Sequential));
    let evidence = Proof {
        statuses: vec![raw],
    };
    assert_eq!(
        evidence
            .verify(
                &mut TestRng::new(4),
                &fixture.verifier,
                &statement(),
                &Sequential
            )
            .unwrap_err(),
        Error::Attribution
    );
}
#[test]
fn threshold_partials_cannot_impersonate_transferable_statuses() {
    reject_threshold(standard::fixture::<MinSig, _>(&mut TestRng::new(0), NS, 6));
    reject_threshold(vrf::fixture::<MinSig, _>(&mut TestRng::new(0), NS, 6));
}
#[test]
fn unsupported_rosters_do_not_silently_weaken_the_fault_budget() {
    for n in [4, 5, 7, 11] {
        let fixture = ed25519::fixture(&mut TestRng::new(0), NS, n);
        let p = Proof::<ed25519::Scheme, Digest> { statuses: vec![] };
        assert_eq!(
            p.verify(
                &mut TestRng::new(1),
                &fixture.verifier,
                &statement(),
                &Sequential
            )
            .unwrap_err(),
            Error::UnsupportedRoster
        );
    }
}
#[test]
fn promise_codec_rejects_unknown_version() {
    let p = promise(&statement(), Some(hash(7)));
    let mut bytes = p.encode().to_vec();
    assert_eq!(Promise::<Digest>::decode(bytes.clone()).unwrap(), p);
    bytes[0] = 2;
    assert!(Promise::<Digest>::decode(bytes).is_err());
}
#[cfg(feature = "arbitrary")]
mod conformance {
    use super::*;
    use commonware_codec::conformance::CodecConformance;
    commonware_conformance::conformance_tests! {
        CodecConformance<Promise<Digest>>,
        CodecConformance<Status<ed25519::Scheme,Digest>>,
        CodecConformance<Proof<ed25519::Scheme,Digest>> => 1024,
    }
}

#[cfg(not(target_arch = "wasm32"))]
#[test]
fn durable_status_retransmission_and_repeated_recovery_preserve_the_value() {
    use commonware_consensus::simplex::extension::fence::{Error as FenceError, Fence};
    use commonware_runtime::{
        Runner as _, Supervisor as _, buffer::paged::CacheRef, deterministic,
    };
    use commonware_storage::journal::segmented::variable::Config;
    use commonware_utils::{NZU16, NZUsize};
    let fixture = ed25519::fixture(&mut TestRng::new(0), NS, 6);
    let schemes = fixture.schemes.clone();
    let verifier = fixture.verifier.clone();
    let ((statuses, certificate), checkpoint) =
        deterministic::Runner::default().start_and_recover(move |context| async move {
            let s = statement();
            let value = s.value::<Sha256>();
            let mut fences = Vec::new();
            let mut statuses = Vec::new();
            for (i, scheme) in schemes.iter().take(5).enumerate() {
                let cfg = Config {
                    partition: format!("status-{i}"),
                    compression: None,
                    codec_config: NZUsize!(4),
                    page_cache: CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(8)),
                    write_buffer: NZUsize!(1024),
                };
                let mut fence = Fence::open(
                    context.child("fence").with_attribute("node", i.to_string()),
                    cfg,
                    NZUsize!(8),
                    NZUsize!(1024),
                )
                .await
                .unwrap();
                // Three X and two different valid prior interpretations; no old QC.
                let mut old = s.clone();
                if i >= 3 {
                    old.extension = hash(8);
                }
                fence
                    .vote(2, vec![(s.slot::<Sha256>(), old.value::<Sha256>())])
                    .await
                    .unwrap();
                let frozen = fence.promise(3, vec![s.slot::<Sha256>()]).await.unwrap()[0];
                let mut wrong = s.clone();
                wrong.domain = hash(88);
                assert_eq!(
                    Promise::from_fenced::<Sha256>(&wrong, frozen).unwrap_err(),
                    Error::Context
                );
                let p = Promise::from_fenced::<Sha256>(&s, frozen).unwrap();
                statuses.push(Status::sign(scheme, p).unwrap());
                fences.push(fence);
            }
            let proof = Proof {
                statuses: statuses.clone(),
            };
            let checked = proof
                .verify(&mut TestRng::new(10), &verifier, &s, &Sequential)
                .unwrap();
            assert_eq!(checked.forced_value(), Some(value));
            assert!(checked.permits::<Sha256>(&s));
            let mut votes = Vec::new();
            for (i, fence) in fences.iter_mut().enumerate() {
                fence
                    .vote(3, vec![(s.slot::<Sha256>(), value)])
                    .await
                    .unwrap();
                votes.push(Vote::sign(&schemes[i], s.clone()).unwrap());
            }
            let mut votes = votes.into_iter();
            let certificate = Certificate::from_votes(
                &mut TestRng::new(12),
                &verifier,
                NonEmpty::new(votes.next().unwrap(), votes),
                &Sequential,
            )
            .unwrap();
            (statuses, certificate)
        });
    assert!(certificate.verify(&mut TestRng::new(13), &fixture.verifier, &Sequential));
    deterministic::Runner::from(checkpoint).start(move |context| async move {
        let s = statement();
        let mut next = s.clone();
        next.ballot = round(4);
        let mut statuses_next = Vec::new();
        for (i, original) in statuses.iter().enumerate() {
            let cfg = Config {
                partition: format!("status-{i}"),
                compression: None,
                codec_config: NZUsize!(4),
                page_cache: CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(8)),
                write_buffer: NZUsize!(1024),
            };
            let mut fence = Fence::open(
                context
                    .child("reopen")
                    .with_attribute("node", i.to_string()),
                cfg,
                NZUsize!(8),
                NZUsize!(1024),
            )
            .await
            .unwrap();
            let frozen = fence.promise(3, vec![s.slot::<Sha256>()]).await.unwrap()[0];
            let retransmitted = Status::sign(
                &fixture.schemes[i],
                Promise::from_fenced::<Sha256>(&s, frozen).unwrap(),
            )
            .unwrap();
            assert_eq!(retransmitted.encode(), original.encode());
            assert!(matches!(
                fence.vote(2, vec![(s.slot::<Sha256>(), hash(9))]).await,
                Err(FenceError::Stale)
            ));
            let frozen = fence.promise(4, vec![next.slot::<Sha256>()]).await.unwrap()[0];
            statuses_next.push(
                Status::sign(
                    &fixture.schemes[i],
                    Promise::from_fenced::<Sha256>(&next, frozen).unwrap(),
                )
                .unwrap(),
            );
        }
        let checked = Proof {
            statuses: statuses_next,
        }
        .verify(&mut TestRng::new(14), &fixture.verifier, &next, &Sequential)
        .unwrap();
        assert_eq!(checked.forced_value(), Some(s.value::<Sha256>()));
        assert!(checked.permits::<Sha256>(&next));
        next.extension = hash(9);
        assert!(!checked.permits::<Sha256>(&next));
    });
}
