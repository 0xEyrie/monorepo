//! Adversarial checks over actual attributable signatures, not mock proof labels.
use bytes::Bytes;
use commonware_codec::{Decode as _, DecodeExt as _, Encode as _, EncodeSize};
use commonware_conformance::{Conformance, conformance_tests};
use commonware_consensus::{
    simplex::{
        extension::agreement::{
            Core, Error, FastProof, Kind, Limits, Message, Origin, Quorum, Row, Signed, Slot, Value,
        },
        scheme::{bls12381_threshold::vrf, ed25519},
        types::{Notarize, Proposal, Subject},
    },
    types::{Epoch, Participant, Round, View},
};
use commonware_cryptography::{
    bls12381::primitives::variant::MinSig,
    certificate::{Scheme as _, Verifier as _, mocks::Fixture},
    sha256::{Digest, Sha256},
};
use commonware_parallel::Sequential;
use commonware_utils::{TestRng, non_empty};

type S = ed25519::Scheme;
type Proof = FastProof<S, Digest>;

#[path = "extension_agreement/general.rs"]
mod general;
#[path = "extension_agreement/general_authentication.rs"]
mod general_authentication;
#[path = "extension_agreement/general_checked_issuance.rs"]
mod general_checked_issuance;
#[path = "extension_agreement/general_core.rs"]
mod general_core;
#[path = "extension_agreement/general_entry.rs"]
mod general_entry;
#[path = "extension_agreement/general_history.rs"]
mod general_history;
#[path = "extension_agreement/general_issuance.rs"]
mod general_issuance;
#[path = "extension_agreement/general_normal.rs"]
mod general_normal;
#[path = "extension_agreement/general_normal_bounds.rs"]
mod general_normal_bounds;
#[path = "extension_agreement/general_recovery.rs"]
mod general_recovery;
#[path = "extension_agreement/general_recovery_issuance.rs"]
mod general_recovery_issuance;
#[path = "extension_agreement/general_signers.rs"]
mod general_signers;
#[path = "extension_agreement/general_wish.rs"]
mod general_wish;
#[path = "extension_agreement/issuance.rs"]
mod issuance;
#[path = "extension_agreement/normal.rs"]
mod normal;
#[path = "extension_agreement/recovery.rs"]
mod recovery;
#[path = "extension_agreement/scoped.rs"]
mod scoped;
const LIMITS: Limits = Limits {
    report_bytes: 64,
    direction_bytes: 64,
};

fn fixture(n: u32) -> Fixture<S> {
    ed25519::fixture(
        &mut TestRng::new(101),
        b"_COMMONWARE_CONSENSUS_AGREEMENT_TEST",
        n,
    )
}
const fn round(view: u64) -> Round {
    Round::new(Epoch::new(1), View::new(view))
}
fn slot(f: &Fixture<S>) -> Slot<Digest> {
    Slot {
        domain: Digest::from([1; 32]),
        roster: Slot::<Digest>::roster::<Sha256, _>(&f.verifier),
        selector: Digest::from([2; 32]),
        cut: 11,
        proposal: Proposal::new(round(4), View::new(3), Digest::from([3; 32])),
        parent: Digest::from([4; 32]),
    }
}
// Fixed toy policy preserves report semantics in the decision. Production supplies
// its authenticated selector and hard-order validator at this same boundary.
fn direction(rows: &[Row]) -> Bytes {
    rows.iter()
        .flat_map(|r| r.report.iter().flat_map(|b| b.iter().copied()))
        .collect()
}
fn policy(v: &Value<Digest>) -> bool {
    v.direction == direction(&v.reports)
}
fn select(f: &Fixture<S>, p: &mut Proof) {
    p.value.reports = p
        .firsts
        .iter()
        .map(|s| {
            let Kind::First { report, .. } = &s.message.kind else {
                panic!("FIRST fixture")
            };
            Row {
                owner: s.attestation.signer,
                report: report.clone(),
            }
        })
        .collect();
    p.value.direction = direction(&p.value.reports);
    p.selection = Signed::sign(
        &f.schemes[usize::from(p.core.leader)],
        Message {
            slot: p.core.slot.id::<Sha256>(),
            round: p.core.slot.proposal.round,
            leader: p.core.leader,
            kind: Kind::Select {
                core: p.core.id::<Sha256>(),
                value: p.value.id::<Sha256>(),
            },
        },
    )
    .unwrap();
}
fn proof(f: &Fixture<S>) -> Proof {
    let core = Core {
        slot: slot(f),
        leader: Participant::new(0),
        followers: [1, 2, 3, 4].map(Participant::new),
        leader_report: Core::<Digest>::row::<Sha256>(&Some(Bytes::from_static(b"a"))),
    };
    let firsts: Vec<_> = (0..5)
        .map(|id| {
            Signed::sign(
                &f.schemes[id],
                Message {
                    slot: core.slot.id::<Sha256>(),
                    round: core.slot.proposal.round,
                    leader: core.leader,
                    kind: Kind::First {
                        core: core.id::<Sha256>(),
                        report: Some(Bytes::from(vec![b'a' + id as u8])),
                    },
                },
            )
            .unwrap()
        })
        .collect();
    let value = Value {
        slot: core.slot.clone(),
        origin: Origin::Fast(core.id::<Sha256>()),
        reports: Vec::new(),
        direction: Bytes::new(),
    };
    let mut p = FastProof {
        core,
        selection: firsts[0].clone(),
        firsts,
        value,
    };
    select(f, &mut p);
    p
}
fn check(f: &Fixture<S>, p: &Proof) -> Result<(), Error> {
    p.verify::<Sha256, _>(
        &mut TestRng::new(202),
        &f.verifier,
        &slot(f),
        Participant::new(0),
        LIMITS,
        policy,
        &Sequential,
    )
    .map(|_| ())
}
fn votes(f: &Fixture<S>, kind: Kind<Digest>, ids: &[usize]) -> Vec<Signed<S, Digest>> {
    ids.iter()
        .map(|id| {
            Signed::sign(
                &f.schemes[*id],
                Message {
                    slot: slot(f).id::<Sha256>(),
                    round: round(4),
                    leader: Participant::new(0),
                    kind: kind.clone(),
                },
            )
            .unwrap()
        })
        .collect()
}
fn quorum(f: &Fixture<S>, votes: Vec<Signed<S, Digest>>) -> Result<Quorum<S, Digest>, Error> {
    Quorum::from_votes(
        &mut TestRng::new(303),
        &f.verifier,
        non_empty![@votes.into_iter()],
        &Sequential,
    )
}

#[test]
fn full_origin_and_any_five_terminal_signers_are_distinct_populations() {
    let f = fixture(7);
    let p = proof(&f);
    assert!(check(&f, &p).is_ok());
    let v = p.value.id::<Sha256>();
    // Both nodes outside the report cohort can sign the final exact value.
    let q = quorum(&f, votes(&f, Kind::FastFinal(v), &[2, 3, 4, 5, 6])).unwrap();
    assert!(q.verify(&mut TestRng::new(404), &f.verifier, &Sequential));
    assert_eq!(q.message.kind, Kind::FastFinal(v));
    // Ordinary P notarization independently remains any five.
    let ordinary = Notarize::sign(&f.schemes[6], p.core.slot.proposal).unwrap();
    assert!(ordinary.verify(&mut TestRng::new(505), &f.verifier, &Sequential));
}

#[test]
fn exact_parent_epoch_roster_selector_cut_and_elected_leader_are_required() {
    let f = fixture(7);
    let p = proof(&f);
    let mut wrong: Vec<_> = vec![slot(&f); 7];
    wrong[0].domain = Digest::from([90; 32]);
    wrong[1].parent = Digest::from([91; 32]);
    wrong[2].selector = Digest::from([92; 32]);
    wrong[3].cut += 1;
    wrong[4].proposal.round = Round::new(Epoch::new(2), View::new(4));
    wrong[5].proposal.parent = View::new(2);
    wrong[6].roster = Digest::from([93; 32]);
    for expected in wrong {
        assert!(
            p.verify::<Sha256, _>(
                &mut TestRng::new(606),
                &f.verifier,
                &expected,
                Participant::new(0),
                LIMITS,
                policy,
                &Sequential
            )
            .is_err()
        );
    }
    assert!(
        p.verify::<Sha256, _>(
            &mut TestRng::new(707),
            &f.verifier,
            &slot(&f),
            Participant::new(1),
            LIMITS,
            policy,
            &Sequential
        )
        .is_err()
    );
    let other = ed25519::fixture(
        &mut TestRng::new(808),
        b"_COMMONWARE_CONSENSUS_AGREEMENT_TEST",
        7,
    );
    assert!(check(&other, &p).is_err());
    assert!(Slot::<Digest>::decode(Bytes::from_static(&[1])).is_err());
}

#[test]
fn duplicate_outside_unsorted_or_missing_first_is_rejected() {
    let f = fixture(7);
    let p = proof(&f);
    let mut duplicate = p.clone();
    duplicate.firsts[4] = duplicate.firsts[3].clone();
    select(&f, &mut duplicate);
    assert!(check(&f, &duplicate).is_err());
    let mut unsorted = p.clone();
    unsorted.firsts.swap(1, 2);
    select(&f, &mut unsorted);
    assert!(check(&f, &unsorted).is_err());
    let mut missing = p.clone();
    missing.firsts.remove(0);
    select(&f, &mut missing);
    assert!(check(&f, &missing).is_err());
    let mut outside = p.clone();
    let mut message = outside.firsts[4].message.clone();
    message.kind = Kind::First {
        core: p.core.id::<Sha256>(),
        report: Some(Bytes::from_static(b"outside")),
    };
    outside.firsts[4] = Signed::sign(&f.schemes[6], message).unwrap();
    select(&f, &mut outside);
    assert!(check(&f, &outside).is_err());
    let mut core = p.core;
    core.followers = [1, 2, 2, 4].map(Participant::new);
    assert!(
        core.check::<Sha256, _>(&f.verifier, &slot(&f), Participant::new(0))
            .is_err()
    );
}

#[test]
fn forged_row_leader_selection_and_nondeterministic_direction_are_rejected() {
    let f = fixture(7);
    let p = proof(&f);
    let mut row = p.clone();
    row.firsts[2].message.kind = Kind::First {
        core: p.core.id::<Sha256>(),
        report: None,
    };
    select(&f, &mut row); // Leader endorsement does not bless a forged follower row.
    assert_eq!(check(&f, &row), Err(Error::Signature));
    let mut selection = p.clone();
    selection.selection = Signed::sign(&f.schemes[1], selection.selection.message).unwrap();
    assert_eq!(check(&f, &selection), Err(Error::Value));
    let mut invalid = p.clone();
    invalid.value.direction = Bytes::from_static(b"wrong");
    invalid.selection = Signed::sign(
        &f.schemes[0],
        Message {
            kind: Kind::Select {
                core: invalid.core.id::<Sha256>(),
                value: invalid.value.id::<Sha256>(),
            },
            ..invalid.selection.message
        },
    )
    .unwrap();
    assert_eq!(check(&f, &invalid), Err(Error::Policy));
    let mut wrong_leader_row = p.clone();
    wrong_leader_row.firsts[0] = Signed::sign(
        &f.schemes[0],
        Message {
            kind: Kind::First {
                core: p.core.id::<Sha256>(),
                report: None,
            },
            ..p.firsts[0].message.clone()
        },
    )
    .unwrap();
    select(&f, &mut wrong_leader_row);
    assert_eq!(check(&f, &wrong_leader_row), Err(Error::Value));
}

#[test]
fn different_original_rows_remain_different_values_even_for_equal_direction() {
    let f = fixture(7);
    let p = proof(&f);
    let mut v = p.value.clone();
    v.reports[2].report = None;
    assert_eq!(v.direction, p.value.direction);
    assert_ne!(v.id::<Sha256>(), p.value.id::<Sha256>());
    let mut origin = p.value.clone();
    origin.origin = Origin::Recovery {
        round: round(5),
        leader: Participant::new(1),
    };
    assert_ne!(origin.id::<Sha256>(), p.value.id::<Sha256>());
    // Carrier round changes do not recreate a carried value's identity.
    let first = votes(&f, Kind::Prepare(p.value.id::<Sha256>()), &[0])[0].clone();
    let later = Signed::sign(
        &f.schemes[0],
        Message {
            round: round(6),
            ..first.message.clone()
        },
    )
    .unwrap();
    assert_eq!(
        first.message.kind.voted_value(),
        later.message.kind.voted_value()
    );
    assert_ne!(first.message, later.message);
}

#[test]
fn less_than_five_duplicate_or_mixed_context_votes_never_assemble() {
    let f = fixture(7);
    let v = proof(&f).value.id::<Sha256>();
    assert!(quorum(&f, votes(&f, Kind::FastFinal(v), &[0, 1, 2, 3])).is_err());
    assert_eq!(
        quorum(&f, votes(&f, Kind::FastFinal(v), &[0, 1, 2, 3, 3])).unwrap_err(),
        Error::Identity
    );
    for kind in [
        Kind::Prepare(v),
        Kind::Commit(v),
        Kind::FastFinal(Digest::from([99; 32])),
    ] {
        let mut set = votes(&f, Kind::FastFinal(v), &[0, 1, 2, 3]);
        set.extend(votes(&f, kind, &[4]));
        assert!(quorum(&f, set).is_err());
    }
    let mut set = votes(&f, Kind::FastFinal(v), &[0, 1, 2, 3, 4]);
    set[4] = Signed::sign(
        &f.schemes[4],
        Message {
            round: round(5),
            ..set[4].message.clone()
        },
    )
    .unwrap();
    assert!(quorum(&f, set).is_err());
    assert!(
        quorum(
            &f,
            votes(
                &f,
                Kind::Recover {
                    history: None,
                    report: None
                },
                &[0, 1, 2, 3, 4]
            )
        )
        .is_err()
    );
}

#[test]
fn certificate_cannot_be_relabelled_to_another_phase_value_or_view() {
    let f = fixture(7);
    let v = proof(&f).value.id::<Sha256>();
    let q = quorum(&f, votes(&f, Kind::Prepare(v), &[0, 1, 2, 3, 4])).unwrap();
    for message in [
        Message {
            kind: Kind::Commit(v),
            ..q.message.clone()
        },
        Message {
            kind: Kind::Prepare(Digest::from([99; 32])),
            ..q.message.clone()
        },
        Message {
            round: round(5),
            ..q.message.clone()
        },
    ] {
        let forged = Quorum::<S, Digest> {
            message,
            certificate: q.certificate.clone(),
        };
        assert!(!forged.verify(&mut TestRng::new(909), &f.verifier, &Sequential));
    }
}

#[test]
fn agreement_signature_is_domain_separated_from_legacy_request() {
    let f = fixture(7);
    let signed = votes(&f, Kind::Commit(Digest::from([8; 32])), &[0])
        .pop()
        .unwrap();
    let payload = signed.message.encode();
    assert!(!f.verifier.verify_attestation::<_, Digest>(
        &mut TestRng::new(1001),
        Subject::ExtensionRequest {
            round: signed.message.round,
            payload: &payload
        },
        &signed.attestation,
        &Sequential
    ));
}

#[test]
fn codec_roundtrip_truncation_and_per_field_limits_are_enforced() {
    let f = fixture(7);
    let p = proof(&f);
    let bytes = p.encode();
    assert_eq!(bytes.len(), p.encode_size());
    let decoded = Proof::decode_cfg(bytes.clone(), &LIMITS).unwrap();
    assert_eq!(decoded.encode(), bytes);
    assert!(check(&f, &decoded).is_ok());
    for end in 0..bytes.len() {
        assert!(Proof::decode_cfg(bytes.slice(..end), &LIMITS).is_err());
    }
    assert!(
        Proof::decode_cfg(
            bytes.clone(),
            &Limits {
                report_bytes: 0,
                ..LIMITS
            }
        )
        .is_err()
    );
    assert!(
        Proof::decode_cfg(
            bytes,
            &Limits {
                direction_bytes: 0,
                ..LIMITS
            }
        )
        .is_err()
    );
    let absent = Message::<Digest> {
        slot: slot(&f).id::<Sha256>(),
        round: round(5),
        leader: Participant::new(1),
        kind: Kind::Recover {
            history: None,
            report: None,
        },
    };
    let empty = Message {
        kind: Kind::Recover {
            history: None,
            report: Some(Bytes::new()),
        },
        ..absent
    };
    assert_ne!(absent.encode(), empty.encode());
    assert_eq!(
        Message::<Digest>::decode_cfg(empty.encode(), &0).unwrap(),
        empty
    );
    let q = quorum(
        &f,
        votes(
            &f,
            Kind::FastFinal(p.value.id::<Sha256>()),
            &[0, 1, 2, 3, 4],
        ),
    )
    .unwrap();
    let encoded = q.encode();
    let cfg = f.verifier.certificate_codec_config();
    assert_eq!(
        Quorum::<S, Digest>::decode_cfg(encoded.clone(), &cfg)
            .unwrap()
            .encode(),
        encoded
    );
}

#[test]
fn seven_validator_profile_rejects_other_rosters_and_unsigned_observer() {
    let six = fixture(6);
    assert_eq!(
        slot(&six).check_roster::<Sha256, _>(&six.verifier),
        Err(Error::Roster)
    );
    let f = fixture(7);
    let message = votes(&f, Kind::Commit(Digest::from([8; 32])), &[0])
        .pop()
        .unwrap()
        .message;
    assert!(Signed::sign(&f.verifier, message).is_err());
    let threshold = vrf::fixture::<MinSig, _>(
        &mut TestRng::new(1020),
        b"_COMMONWARE_CONSENSUS_AGREEMENT_TEST",
        7,
    );
    assert!(!<vrf::Scheme<
        commonware_cryptography::ed25519::PublicKey,
        MinSig,
    >>::is_attributable());
    assert_eq!(
        slot(&f).check_roster::<Sha256, _>(&threshold.verifier),
        Err(Error::Roster)
    );
    let message = votes(&f, Kind::Commit(Digest::from([8; 32])), &[0])
        .pop()
        .unwrap()
        .message;
    assert_eq!(
        Signed::sign(&threshold.schemes[0], message.clone()).unwrap_err(),
        Error::Roster
    );
    let attestation = threshold.schemes[0]
        .sign::<Digest>(Subject::ExtensionAgreement {
            round: message.round,
            payload: &message.encode(),
        })
        .unwrap();
    let signed = Signed {
        message,
        attestation,
    };
    assert!(!signed.verify(&mut TestRng::new(1021), &threshold.verifier, &Sequential));
}

#[test]
fn foreign_roster_cannot_finalize_an_origin_checked_under_another_roster() {
    let f = fixture(7);
    let p = proof(&f);
    let origin = p
        .verify::<Sha256, _>(
            &mut TestRng::new(1101),
            &f.verifier,
            &slot(&f),
            Participant::new(0),
            LIMITS,
            policy,
            &Sequential,
        )
        .unwrap();
    let foreign = ed25519::fixture(
        &mut TestRng::new(1102),
        b"_COMMONWARE_CONSENSUS_AGREEMENT_TEST",
        7,
    );
    let signed: Vec<_> = foreign
        .schemes
        .iter()
        .take(5)
        .map(|scheme| {
            Signed::sign(
                scheme,
                Message {
                    slot: origin.slot(),
                    round: round(4),
                    leader: Participant::new(0),
                    kind: Kind::FastFinal(origin.value()),
                },
            )
            .unwrap()
        })
        .collect();
    let q = quorum(&foreign, signed).unwrap();
    assert!(q.verify(&mut TestRng::new(1103), &foreign.verifier, &Sequential));
    assert!(
        p.verify_finalization::<Sha256, _>(
            &mut TestRng::new(1104),
            &foreign.verifier,
            &slot(&f),
            Participant::new(0),
            LIMITS,
            policy,
            &q,
            &Sequential
        )
        .is_err()
    );
    assert!(
        p.verify_finalization::<Sha256, _>(
            &mut TestRng::new(1105),
            &f.verifier,
            &slot(&f),
            Participant::new(0),
            LIMITS,
            policy,
            &q,
            &Sequential
        )
        .is_err()
    );
}

#[test]
fn same_keys_in_a_different_signing_namespace_cannot_mix_proofs() {
    let f = fixture(7);
    let p = proof(&f);
    let namespace = b"_COMMONWARE_CONSENSUS_AGREEMENT_OTHER_NAMESPACE";
    let foreign = Fixture {
        participants: f.participants.clone(),
        private_keys: f.private_keys.clone(),
        schemes: f
            .private_keys
            .iter()
            .map(|key| {
                S::signer(namespace, f.verifier.participants().clone(), key.clone()).unwrap()
            })
            .collect(),
        verifier: S::verifier(namespace, f.verifier.participants().clone()),
    };
    assert_eq!(slot(&f).roster, slot(&foreign).roster);
    let q = quorum(
        &foreign,
        votes(
            &foreign,
            Kind::FastFinal(p.value.id::<Sha256>()),
            &[0, 1, 2, 3, 4],
        ),
    )
    .unwrap();
    assert!(q.verify(&mut TestRng::new(1151), &foreign.verifier, &Sequential));
    assert!(
        p.verify_finalization::<Sha256, _>(
            &mut TestRng::new(1152),
            &foreign.verifier,
            &slot(&f),
            Participant::new(0),
            LIMITS,
            policy,
            &q,
            &Sequential
        )
        .is_err()
    );
    assert!(
        p.verify_finalization::<Sha256, _>(
            &mut TestRng::new(1153),
            &f.verifier,
            &slot(&f),
            Participant::new(0),
            LIMITS,
            policy,
            &q,
            &Sequential
        )
        .is_err()
    );
}

#[test]
fn exact_origin_and_final_value_are_verified_together() {
    let f = fixture(7);
    let p = proof(&f);
    let v = p.value.id::<Sha256>();
    let q = quorum(&f, votes(&f, Kind::FastFinal(v), &[2, 3, 4, 5, 6])).unwrap();
    let verified = p
        .verify_finalization::<Sha256, _>(
            &mut TestRng::new(1106),
            &f.verifier,
            &slot(&f),
            Participant::new(0),
            LIMITS,
            policy,
            &q,
            &Sequential,
        )
        .unwrap();
    assert_eq!(verified.slot(), slot(&f).id::<Sha256>());
    assert_eq!(verified.value(), v);
    for kind in [
        Kind::Prepare(v),
        Kind::Commit(v),
        Kind::FastFinal(Digest::from([8; 32])),
    ] {
        let wrong = quorum(&f, votes(&f, kind, &[0, 1, 2, 3, 4])).unwrap();
        assert!(wrong.verify(&mut TestRng::new(1107), &f.verifier, &Sequential));
        assert!(
            p.verify_finalization::<Sha256, _>(
                &mut TestRng::new(1108),
                &f.verifier,
                &slot(&f),
                Participant::new(0),
                LIMITS,
                policy,
                &wrong,
                &Sequential
            )
            .is_err()
        );
    }
    let later: Vec<_> = votes(&f, Kind::FastFinal(v), &[0, 1, 2, 3, 4])
        .into_iter()
        .map(|s| {
            Signed::sign(
                &f.schemes[usize::from(s.attestation.signer)],
                Message {
                    round: round(5),
                    ..s.message
                },
            )
            .unwrap()
        })
        .collect();
    let later = quorum(&f, later).unwrap();
    assert!(later.verify(&mut TestRng::new(1109), &f.verifier, &Sequential));
    assert!(
        p.verify_finalization::<Sha256, _>(
            &mut TestRng::new(1110),
            &f.verifier,
            &slot(&f),
            Participant::new(0),
            LIMITS,
            policy,
            &later,
            &Sequential
        )
        .is_err()
    );
    let mut invalid = p;
    invalid.firsts.pop();
    assert!(
        invalid
            .verify_finalization::<Sha256, _>(
                &mut TestRng::new(1111),
                &f.verifier,
                &slot(&f),
                Participant::new(0),
                LIMITS,
                policy,
                &q,
                &Sequential
            )
            .is_err()
    );
}

#[test]
fn two_valid_semantic_forks_identify_leader_and_forking_follower() {
    let f = fixture(7);
    let p = proof(&f);
    let mut other = p.clone();
    other.firsts[2] = Signed::sign(
        &f.schemes[2],
        Message {
            kind: Kind::First {
                core: other.core.id::<Sha256>(),
                report: Some(Bytes::from_static(b"fork")),
            },
            ..other.firsts[2].message.clone()
        },
    )
    .unwrap();
    select(&f, &mut other);
    let left = p
        .verify::<Sha256, _>(
            &mut TestRng::new(1201),
            &f.verifier,
            &slot(&f),
            Participant::new(0),
            LIMITS,
            policy,
            &Sequential,
        )
        .unwrap();
    let right = other
        .verify::<Sha256, _>(
            &mut TestRng::new(1202),
            &f.verifier,
            &slot(&f),
            Participant::new(0),
            LIMITS,
            policy,
            &Sequential,
        )
        .unwrap();
    assert_eq!(left.faults(&right), Ok(Some([0, 2].map(Participant::new))));
    assert_eq!(right.faults(&left), Ok(Some([0, 2].map(Participant::new))));
    assert_eq!(left.faults(&left), Ok(None));
}

#[test]
fn equal_direction_different_reports_still_expose_semantic_forks() {
    let f = fixture(7);
    let mut left = proof(&f);
    let mut right = left.clone();
    right.firsts[3] = Signed::sign(
        &f.schemes[3],
        Message {
            kind: Kind::First {
                core: right.core.id::<Sha256>(),
                report: None,
            },
            ..right.firsts[3].message.clone()
        },
    )
    .unwrap();
    for p in [&mut left, &mut right] {
        select(&f, p);
        p.value.direction = Bytes::from_static(b"constant");
        p.selection = Signed::sign(
            &f.schemes[0],
            Message {
                kind: Kind::Select {
                    core: p.core.id::<Sha256>(),
                    value: p.value.id::<Sha256>(),
                },
                ..p.selection.message.clone()
            },
        )
        .unwrap();
    }
    let constant = |v: &Value<Digest>| v.direction == b"constant"[..];
    let a = left
        .verify::<Sha256, _>(
            &mut TestRng::new(1301),
            &f.verifier,
            &slot(&f),
            Participant::new(0),
            LIMITS,
            constant,
            &Sequential,
        )
        .unwrap();
    let b = right
        .verify::<Sha256, _>(
            &mut TestRng::new(1302),
            &f.verifier,
            &slot(&f),
            Participant::new(0),
            LIMITS,
            constant,
            &Sequential,
        )
        .unwrap();
    assert_ne!(a.value(), b.value());
    assert_eq!(a.faults(&b), Ok(Some([0, 3].map(Participant::new))));
}

#[test]
fn fork_attribution_rejects_more_than_the_declared_fault_budget() {
    let f = fixture(7);
    let p = proof(&f);
    let mut other = p.clone();
    for id in [2, 3] {
        other.firsts[id] = Signed::sign(
            &f.schemes[id],
            Message {
                kind: Kind::First {
                    core: p.core.id::<Sha256>(),
                    report: None,
                },
                ..p.firsts[id].message.clone()
            },
        )
        .unwrap();
    }
    select(&f, &mut other);
    let a = p
        .verify::<Sha256, _>(
            &mut TestRng::new(1401),
            &f.verifier,
            &slot(&f),
            Participant::new(0),
            LIMITS,
            policy,
            &Sequential,
        )
        .unwrap();
    let b = other
        .verify::<Sha256, _>(
            &mut TestRng::new(1402),
            &f.verifier,
            &slot(&f),
            Participant::new(0),
            LIMITS,
            policy,
            &Sequential,
        )
        .unwrap();
    assert_eq!(a.faults(&b), Err(Error::FaultBudget));
}

struct AgreementEvidenceConformance;
impl Conformance for AgreementEvidenceConformance {
    async fn commit(seed: u64) -> Vec<u8> {
        let f = ed25519::fixture(
            &mut TestRng::new(seed),
            b"_COMMONWARE_CONSENSUS_AGREEMENT_TEST",
            7,
        );
        let p = proof(&f);
        let v = p.value.id::<Sha256>();
        let mut encodings = vec![
            p.core.slot.encode(),
            p.core.encode(),
            p.value.encode(),
            p.encode(),
        ];
        let mut recovery_value = p.value.clone();
        recovery_value.origin = Origin::Recovery {
            round: round(5),
            leader: Participant::new(1),
        };
        encodings.push(recovery_value.encode());
        for kind in [
            Kind::First {
                core: p.core.id::<Sha256>(),
                report: None,
            },
            Kind::First {
                core: p.core.id::<Sha256>(),
                report: Some(Bytes::new()),
            },
            Kind::Select {
                core: p.core.id::<Sha256>(),
                value: v,
            },
            Kind::Recover {
                history: None,
                report: None,
            },
            Kind::Recover {
                history: Some(v),
                report: Some(Bytes::from_static(b"route")),
            },
            Kind::FastFinal(v),
            Kind::Prepare(v),
            Kind::Commit(v),
        ] {
            let signed = votes(&f, kind.clone(), &[0]).pop().unwrap();
            encodings.push(signed.message.encode());
            encodings.push(signed.encode());
            if kind.voted_value().is_some() {
                encodings.push(
                    quorum(&f, votes(&f, kind, &[0, 1, 2, 3, 4]))
                        .unwrap()
                        .encode(),
                );
            }
        }
        encodings.encode().to_vec()
    }
}
conformance_tests! { AgreementEvidenceConformance => 32 }
