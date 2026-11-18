//! Actual ed25519 checks for the inactive G1 cryptographic foundations.
use super::*;
use commonware_codec::Write as _;
use commonware_consensus::simplex::extension::agreement::general as g;
use commonware_cryptography::{Hasher as _, certificate::Scoped};
use std::sync::Arc;

const G_LIMITS: g::Limits = g::Limits {
    report_bytes: 128,
    order_bytes: 128,
    build_bytes: 256,
    material_bytes: 256,
    origin_bytes: g::MAX_EVIDENCE_BYTES,
};
type Origin = g::Origin<S, Digest>;
type Signed = g::Signed<S, Digest>;

fn g_slot(f: &Fixture<S>) -> g::Slot<Digest> {
    g::Slot {
        profile: Digest::from([90; 32]),
        domain: Digest::from([91; 32]),
        roster: g::Slot::<Digest>::roster::<Sha256, _>(&f.verifier),
        cut: 9,
        proposal: Proposal::new(round(4), View::new(3), Digest::from([92; 32])),
        parent: g::NativeParent::Proposal {
            round: round(3),
            digest: Digest::from([93; 32]),
        },
    }
}
fn g_core(f: &Fixture<S>) -> g::Core<Digest> {
    let c = g::Committee::new(f.schemes.len()).unwrap();
    g::Core {
        slot: g_slot(f),
        leader: Participant::new(0),
        followers: (1..c.quorum() as u32).map(Participant::new).collect(),
    }
}
fn input() -> Digest {
    Digest::from([94; 32])
}
fn sign(f: &Fixture<S>, owner: usize, kind: g::Kind<Digest>) -> Signed {
    let core = g_core(f);
    g::Signed::sign(
        &f.schemes[owner],
        g::Message {
            slot: core.slot.id::<Sha256>(),
            round: core.slot.proposal.round,
            leader: core.leader,
            kind,
        },
        G_LIMITS,
    )
    .unwrap()
}
fn resign(f: &Fixture<S>, row: &mut Signed) {
    *row = g::Signed::sign(
        &f.schemes[usize::from(row.attestation.signer)],
        row.message.clone(),
        G_LIMITS,
    )
    .unwrap();
}
fn firsts(f: &Fixture<S>) -> Vec<Signed> {
    let core = g_core(f);
    (0..=core.followers.len())
        .map(|owner| {
            sign(
                f,
                owner,
                g::Kind::First(g::First {
                    core: core.id::<Sha256>(),
                    input: input(),
                    owner: Participant::new(owner as u32),
                    report: (owner != 0).then(|| Bytes::from(vec![owner as u8])),
                    preference: (owner != 0).then(|| Bytes::from_static(b"AB")),
                }),
            )
        })
        .collect()
}
// This is a bounded two-block application fixture, not a selector implementation.
// It establishes that native checks cannot substitute signature checks for policy.
fn legal_row(row: &g::First<Digest>) -> bool {
    row.report.as_ref().is_none_or(|b| b.len() == 1)
        && row
            .preference
            .as_ref()
            .is_none_or(|b| b.as_ref() == b"AB" || b.as_ref() == b"BA")
}
fn build(rows: &[Signed]) -> Bytes {
    rows.iter()
        .flat_map(|r| {
            let g::Kind::First(row) = &r.message.kind else {
                panic!("FIRST fixture")
            };
            row.report.iter().flat_map(|b| b.iter().copied())
        })
        .collect()
}
fn population(rows: &[Signed]) -> Digest {
    let mut bytes = Vec::new();
    for r in rows {
        r.write(&mut bytes);
    }
    Sha256::hash(&[&bytes])
}
fn build_policy(rows: &g::VerifiedRows<S, Digest>, body: &g::OriginBody<S, Digest>) -> bool {
    body.decision.order.as_ref() == b"AB"
        && body.build == build(rows.originals())
        && body.population == population(rows.originals())
        && body.material.is_empty()
}
fn select(f: &Fixture<S>, body: &g::OriginBody<S, Digest>) -> Signed {
    sign(
        f,
        0,
        g::Kind::Select {
            body: body.id::<Sha256>(),
            decision: body.decision.id::<Sha256>(),
        },
    )
}
fn origin(f: &Fixture<S>) -> Origin {
    let firsts = firsts(f);
    let body = g::OriginBody {
        decision: g::Decision {
            slot: g_slot(f),
            input: input(),
            order: Bytes::from_static(b"AB"),
        },
        core: g_core(f),
        population: population(&firsts),
        build: build(&firsts),
        firsts,
        material: Bytes::new(),
    };
    let selection = select(f, &body);
    g::Origin { body, selection }
}
fn refresh(f: &Fixture<S>, p: &mut Origin) {
    p.body.population = population(&p.body.firsts);
    p.body.build = build(&p.body.firsts);
    p.selection = select(f, &p.body);
}
fn check(f: &Fixture<S>, p: &Origin) -> Result<g::VerifiedOrigin<Digest>, g::Error> {
    p.verify::<Sha256, _>(
        &mut TestRng::new(710),
        &f.verifier,
        &g_core(f),
        input(),
        G_LIMITS,
        legal_row,
        build_policy,
        &Sequential,
    )
}
fn check_rows(f: &Fixture<S>, rows: &[Signed]) -> Result<g::VerifiedRows<S, Digest>, g::Error> {
    g::verify_firsts::<Sha256, _, _>(
        &mut TestRng::new(711),
        &f.verifier,
        &g_core(f),
        input(),
        rows,
        G_LIMITS,
        legal_row,
        &Sequential,
    )
}

#[test]
fn generalized_arithmetic_is_native_quorum_and_not_planner_threshold() {
    for (n, f, q, s) in [
        (4, 1, 3, 2),
        (7, 2, 5, 3),
        (8, 2, 6, 4),
        (9, 2, 7, 4),
        (10, 3, 7, 5),
        (13, 4, 9, 6),
        (16, 5, 11, 8),
        (64, 21, 43, 32),
    ] {
        let c = g::Committee::new(n).unwrap();
        assert_eq!(
            (c.len(), c.faults(), c.quorum(), c.fast_support()),
            (n, f, q, s)
        );
        assert!(2 * s > (q - 1) + f - 1);
    }
    for n in [0, 1, 3, 65, usize::MAX] {
        assert_eq!(g::Committee::new(n), Err(g::Error::Roster));
    }
}

#[test]
fn all_supported_test_rosters_authenticate_rows_before_build_and_full_origin() {
    for n in [7, 8, 9, 10, 13, 16] {
        let f = fixture(n);
        let p = origin(&f);
        let rows = check_rows(&f, &p.body.firsts).unwrap();
        assert_eq!(rows.rows().len(), rows.committee().quorum());
        assert_eq!(
            rows.participants().iter().collect::<Vec<_>>(),
            f.verifier.participants().iter().collect::<Vec<_>>()
        );
        assert_eq!(rows.core(), &g_core(&f));
        assert_eq!(rows.slot(), &g_slot(&f));
        assert_eq!(rows.input(), input());
        let valid = check(&f, &p).unwrap();
        assert_eq!(valid.decision(), p.body.decision.id::<Sha256>());
        assert_eq!(valid.body(), p.body.id::<Sha256>());
        assert_eq!(valid.origin(), p.id::<Sha256>());
        let scope = Scoped::verifier(Arc::new(f.verifier.clone()));
        assert!(
            g::verify_firsts_scoped::<Sha256, _, _>(
                &mut TestRng::new(712),
                &scope,
                &g_core(&f),
                input(),
                &p.body.firsts,
                G_LIMITS,
                legal_row,
                &Sequential
            )
            .is_ok()
        );
        assert!(
            p.verify_scoped::<Sha256, _>(
                &mut TestRng::new(713),
                &scope,
                &g_core(&f),
                input(),
                G_LIMITS,
                legal_row,
                build_policy,
                &Sequential
            )
            .is_ok()
        );
    }
}

#[test]
fn boundary_committees_verify_origins_and_phase_quorums_with_highest_owner() {
    for n in [4u32, 64] {
        let f = fixture(n);
        let committee = g::Committee::new(n as usize).unwrap();
        let last = (n - 1) as usize;
        let owners: Vec<_> = (0..committee.quorum() - 1)
            .chain(std::iter::once(last))
            .collect();
        let core = g::Core {
            slot: g_slot(&f),
            leader: Participant::new(n - 1),
            followers: owners[..owners.len() - 1]
                .iter()
                .map(|owner| Participant::new(*owner as u32))
                .collect(),
        };
        let make_signed = |owner: usize, kind| {
            g::Signed::sign(
                &f.schemes[owner],
                g::Message {
                    slot: core.slot.id::<Sha256>(),
                    round: core.slot.proposal.round,
                    leader: core.leader,
                    kind,
                },
                G_LIMITS,
            )
            .unwrap()
        };
        let firsts: Vec<_> = owners
            .iter()
            .map(|owner| {
                make_signed(
                    *owner,
                    g::Kind::First(g::First {
                        core: core.id::<Sha256>(),
                        input: input(),
                        owner: Participant::new(*owner as u32),
                        report: (*owner != last).then(|| Bytes::from(vec![*owner as u8])),
                        preference: (*owner != last).then(|| Bytes::from_static(b"AB")),
                    }),
                )
            })
            .collect();
        let mut rng = TestRng::new(1064 + u64::from(n));
        let checked = g::verify_firsts::<Sha256, _, _>(
            &mut rng,
            &f.verifier,
            &core,
            input(),
            &firsts,
            G_LIMITS,
            legal_row,
            &Sequential,
        )
        .unwrap();
        assert_eq!(checked.committee(), committee);
        let leader_first = checked.originals().last().unwrap();
        assert_eq!(leader_first.attestation.signer, core.leader);
        assert_eq!(checked.rows().last().unwrap().owner, core.leader);
        assert!(checked.rows().last().unwrap().report.is_none());
        assert!(checked.rows().last().unwrap().preference.is_none());
        let body = g::OriginBody {
            decision: g::Decision {
                slot: core.slot.clone(),
                input: input(),
                order: Bytes::from_static(b"AB"),
            },
            core: core.clone(),
            population: population(&firsts),
            build: build(&firsts),
            firsts,
            material: Bytes::new(),
        };
        let selection = make_signed(
            last,
            g::Kind::Select {
                body: body.id::<Sha256>(),
                decision: body.decision.id::<Sha256>(),
            },
        );
        assert_eq!(selection.attestation.signer, core.leader);
        let origin = g::Origin { body, selection };
        let encoded = origin.encode();
        let decoded = Origin::decode_cfg(encoded.clone(), &G_LIMITS).unwrap();
        assert_eq!(decoded.encode(), encoded);
        assert_eq!(decoded.id::<Sha256>(), origin.id::<Sha256>());
        let origin = decoded;
        let scope = Scoped::verifier(Arc::new(f.verifier.clone()));
        let verified = origin
            .verify::<Sha256, _>(
                &mut rng,
                &f.verifier,
                &core,
                input(),
                G_LIMITS,
                legal_row,
                build_policy,
                &Sequential,
            )
            .unwrap();
        let scoped = origin
            .verify_scoped::<Sha256, _>(
                &mut rng,
                &scope,
                &core,
                input(),
                G_LIMITS,
                legal_row,
                build_policy,
                &Sequential,
            )
            .unwrap();
        assert_eq!(verified.decision(), origin.body.decision.id::<Sha256>());
        assert_eq!(scoped.origin(), verified.origin());
        for phase in [g::Phase::FastFinal, g::Phase::Prepare, g::Phase::Commit] {
            let votes: Vec<_> = owners
                .iter()
                .map(|owner| {
                    make_signed(
                        *owner,
                        g::Kind::Phase {
                            phase,
                            decision: verified.decision(),
                        },
                    )
                })
                .collect();
            let quorum =
                g::Quorum::from_votes(&mut rng, &f.verifier, &votes, G_LIMITS, &Sequential)
                    .unwrap();
            let expected: Vec<_> = owners
                .iter()
                .map(|owner| Participant::new(*owner as u32))
                .collect();
            assert_eq!(
                quorum.certificate.signers.iter().collect::<Vec<_>>(),
                expected
            );
            assert_eq!(quorum.certificate.signers.iter().last(), Some(core.leader));
            assert!(quorum.verify(&mut rng, &f.verifier, G_LIMITS, &Sequential));
            assert!(quorum.verify_scoped(&mut rng, &scope, G_LIMITS, &Sequential));
            let decoded =
                g::Quorum::<S, Digest>::decode_cfg(quorum.encode(), &(G_LIMITS, n as usize))
                    .unwrap();
            assert_eq!(
                decoded.certificate.signers.iter().collect::<Vec<_>>(),
                expected
            );
            assert!(decoded.verify(&mut rng, &f.verifier, G_LIMITS, &Sequential));
            assert_eq!(
                g::Quorum::from_votes(
                    &mut rng,
                    &f.verifier,
                    &votes[..votes.len() - 1],
                    G_LIMITS,
                    &Sequential,
                )
                .unwrap_err(),
                g::Error::Quorum,
            );
        }
    }
}

#[test]
fn independent_optional_fields_and_explicit_leader_absence() {
    let f = fixture(10);
    for (report, preference) in [
        (None, None),
        (Some(Bytes::from_static(b"r")), None),
        (None, Some(Bytes::from_static(b"AB"))),
        (
            Some(Bytes::from_static(b"r")),
            Some(Bytes::from_static(b"BA")),
        ),
    ] {
        let mut rows = firsts(&f);
        let g::Kind::First(row) = &mut rows[1].message.kind else {
            unreachable!()
        };
        row.report = report;
        row.preference = preference;
        resign(&f, &mut rows[1]);
        assert!(check_rows(&f, &rows).is_ok());
    }
    for preference in [false, true] {
        let mut rows = firsts(&f);
        let g::Kind::First(row) = &mut rows[0].message.kind else {
            unreachable!()
        };
        if preference {
            row.preference = Some(Bytes::from_static(b"AB"));
        } else {
            row.report = Some(Bytes::from_static(b"r"));
        }
        resign(&f, &mut rows[0]);
        assert_eq!(check_rows(&f, &rows).unwrap_err(), g::Error::Context);
    }
}

#[test]
fn original_signature_owner_core_and_context_gates() {
    let f = fixture(10);
    let originals = firsts(&f);
    let mut rows = originals.clone();
    rows[1].attestation = rows[2].attestation.clone();
    assert_eq!(check_rows(&f, &rows).unwrap_err(), g::Error::Identity);
    let mut rows = originals.clone();
    rows.swap(1, 2);
    assert_eq!(check_rows(&f, &rows).unwrap_err(), g::Error::Identity);
    assert_eq!(
        check_rows(&f, &originals[..originals.len() - 1]).unwrap_err(),
        g::Error::Identity
    );
    let mut rows = originals.clone();
    rows[2] = rows[1].clone();
    assert_eq!(check_rows(&f, &rows).unwrap_err(), g::Error::Identity);
    for field in 0..5 {
        let mut rows = originals.clone();
        match field {
            0 => rows[1].message.slot = Digest::from([0; 32]),
            1 => rows[1].message.round = round(5),
            2 => rows[1].message.leader = Participant::new(1),
            3 => {
                let g::Kind::First(row) = &mut rows[1].message.kind else {
                    unreachable!()
                };
                row.core = Digest::from([0; 32]);
            }
            _ => {
                let g::Kind::First(row) = &mut rows[1].message.kind else {
                    unreachable!()
                };
                row.input = Digest::from([0; 32]);
            }
        }
        resign(&f, &mut rows[1]);
        assert_eq!(check_rows(&f, &rows).unwrap_err(), g::Error::Context);
    }
    let mut rows = originals.clone();
    let g::Kind::First(row) = &mut rows[1].message.kind else {
        unreachable!()
    };
    row.report = Some(Bytes::from_static(b"x"));
    assert_eq!(check_rows(&f, &rows).unwrap_err(), g::Error::Signature);
    let mut wrong = g_core(&f);
    wrong.followers.pop();
    wrong.followers.push(Participant::new(9));
    assert_eq!(
        g::verify_firsts::<Sha256, _, _>(
            &mut TestRng::new(714),
            &f.verifier,
            &wrong,
            input(),
            &originals,
            G_LIMITS,
            legal_row,
            &Sequential
        )
        .unwrap_err(),
        g::Error::Context
    );
    let other = fixture(13);
    assert_eq!(
        check_rows(&other, &originals).unwrap_err(),
        g::Error::Identity
    );
}

#[test]
fn only_authenticated_rows_reach_application_callback() {
    let f = fixture(7);
    let mut rows = firsts(&f);
    let g::Kind::First(row) = &mut rows[4].message.kind else {
        unreachable!()
    };
    row.report = None;
    let mut called = false;
    assert_eq!(
        g::verify_firsts::<Sha256, _, _>(
            &mut TestRng::new(715),
            &f.verifier,
            &g_core(&f),
            input(),
            &rows,
            G_LIMITS,
            |_| {
                called = true;
                true
            },
            &Sequential
        )
        .unwrap_err(),
        g::Error::Signature
    );
    assert!(!called);
}

#[test]
fn equal_size_foreign_roster_cannot_replay_original_signatures_or_origin() {
    let f = fixture(10);
    let foreign = ed25519::fixture(
        &mut TestRng::new(1040),
        b"_COMMONWARE_CONSENSUS_AGREEMENT_TEST",
        10,
    );
    let p = origin(&f);
    assert_eq!(
        f.verifier.participants().len(),
        foreign.verifier.participants().len()
    );
    assert_ne!(g_slot(&f).roster, g_slot(&foreign).roster);
    // Hold the signed bytes and signature namespace fixed: only public keys change.
    assert!(p.body.firsts[1].verify(&mut TestRng::new(1041), &f.verifier, G_LIMITS, &Sequential));
    assert!(!p.body.firsts[1].verify(
        &mut TestRng::new(1042),
        &foreign.verifier,
        G_LIMITS,
        &Sequential
    ));
    assert_eq!(
        g::verify_firsts::<Sha256, _, _>(
            &mut TestRng::new(1043),
            &foreign.verifier,
            &p.body.core,
            input(),
            &p.body.firsts,
            G_LIMITS,
            legal_row,
            &Sequential
        )
        .unwrap_err(),
        g::Error::Context
    );
    assert_eq!(
        p.verify::<Sha256, _>(
            &mut TestRng::new(1044),
            &foreign.verifier,
            &p.body.core,
            input(),
            G_LIMITS,
            legal_row,
            build_policy,
            &Sequential
        )
        .unwrap_err(),
        g::Error::Context
    );
}

#[test]
fn last_roster_owner_can_lead_a_noncontiguous_core_with_exact_follower_threshold() {
    let f = fixture(8);
    let core = g::Core {
        slot: g_slot(&f),
        leader: Participant::new(7),
        followers: [0, 2, 3, 4, 6].map(Participant::new).to_vec(),
    };
    let make_signed = |owner: usize, kind| {
        g::Signed::sign(
            &f.schemes[owner],
            g::Message {
                slot: core.slot.id::<Sha256>(),
                round: core.slot.proposal.round,
                leader: core.leader,
                kind,
            },
            G_LIMITS,
        )
        .unwrap()
    };
    let firsts: Vec<_> = [0, 2, 3, 4, 6, 7]
        .into_iter()
        .map(|owner| {
            make_signed(
                owner,
                g::Kind::First(g::First {
                    core: core.id::<Sha256>(),
                    input: input(),
                    owner: Participant::new(owner as u32),
                    report: (owner != 7).then(|| Bytes::from(vec![owner as u8])),
                    preference: match owner {
                        7 => None,
                        6 => Some(Bytes::from_static(b"BA")),
                        _ => Some(Bytes::from_static(b"AB")),
                    },
                }),
            )
        })
        .collect();
    let checked = g::verify_firsts::<Sha256, _, _>(
        &mut TestRng::new(1045),
        &f.verifier,
        &core,
        input(),
        &firsts,
        G_LIMITS,
        legal_row,
        &Sequential,
    )
    .unwrap();
    assert_eq!(
        checked
            .rows()
            .iter()
            .map(|r| r.owner.get())
            .collect::<Vec<_>>(),
        vec![0, 2, 3, 4, 6, 7]
    );
    assert_eq!(checked.committee().fast_support(), 4);
    assert!(checked.rows().last().unwrap().report.is_none());
    let body = g::OriginBody {
        decision: g::Decision {
            slot: core.slot.clone(),
            input: input(),
            order: Bytes::from_static(b"AB"),
        },
        core: core.clone(),
        population: population(&firsts),
        build: build(&firsts),
        firsts,
        material: Bytes::new(),
    };
    let selection = make_signed(
        7,
        g::Kind::Select {
            body: body.id::<Sha256>(),
            decision: body.decision.id::<Sha256>(),
        },
    );
    let mut p = g::Origin { body, selection };
    assert!(
        p.verify::<Sha256, _>(
            &mut TestRng::new(1046),
            &f.verifier,
            &core,
            input(),
            G_LIMITS,
            legal_row,
            build_policy,
            &Sequential
        )
        .is_ok()
    );
    // Owner0 is an ordinary follower here; removing its support must cross s=4.
    let g::Kind::First(row) = &mut p.body.firsts[0].message.kind else {
        unreachable!()
    };
    row.preference = None;
    p.body.firsts[0] = make_signed(0, p.body.firsts[0].message.kind.clone());
    p.body.population = population(&p.body.firsts);
    p.body.build = build(&p.body.firsts);
    p.selection = make_signed(
        7,
        g::Kind::Select {
            body: p.body.id::<Sha256>(),
            decision: p.body.decision.id::<Sha256>(),
        },
    );
    assert_eq!(
        p.verify::<Sha256, _>(
            &mut TestRng::new(1047),
            &f.verifier,
            &core,
            input(),
            G_LIMITS,
            legal_row,
            build_policy,
            &Sequential
        )
        .unwrap_err(),
        g::Error::FastIneligible
    );
    let mut wrong = core.clone();
    wrong.followers = [0, 1, 2, 3, 4].map(Participant::new).to_vec();
    assert_eq!(
        p.verify::<Sha256, _>(
            &mut TestRng::new(1048),
            &f.verifier,
            &wrong,
            input(),
            G_LIMITS,
            legal_row,
            build_policy,
            &Sequential
        )
        .unwrap_err(),
        g::Error::Context
    );
}

#[test]
fn fast_gate_uses_exact_follower_preference_not_report_or_leader() {
    for n in [7, 8, 9, 10, 13, 16] {
        let f = fixture(n);
        let mut p = origin(&f);
        let threshold = g::Committee::new(n as usize).unwrap().fast_support();
        for (index, signed) in p.body.firsts.iter_mut().enumerate().skip(1) {
            let g::Kind::First(row) = &mut signed.message.kind else {
                unreachable!()
            };
            row.preference = (index <= threshold).then(|| Bytes::from_static(b"AB"));
            resign(&f, signed);
        }
        refresh(&f, &mut p);
        assert!(check(&f, &p).is_ok());
        let g::Kind::First(row) = &mut p.body.firsts[threshold].message.kind else {
            unreachable!()
        };
        row.preference = Some(Bytes::from_static(b"BA"));
        resign(&f, &mut p.body.firsts[threshold]);
        refresh(&f, &mut p);
        assert_eq!(check(&f, &p).unwrap_err(), g::Error::FastIneligible);
        assert!(check_rows(&f, &p.body.firsts).is_ok());
    }
}

#[test]
fn semantic_identity_excludes_alias_but_select_binds_exact_original_body() {
    let f = fixture(10);
    let a = origin(&f);
    let mut b = a.clone();
    let g::Kind::First(row) = &mut b.body.firsts[1].message.kind else {
        unreachable!()
    };
    row.report = Some(Bytes::from_static(b"z"));
    resign(&f, &mut b.body.firsts[1]);
    refresh(&f, &mut b);
    assert_eq!(
        a.body.decision.id::<Sha256>(),
        b.body.decision.id::<Sha256>()
    );
    assert_ne!(a.body.id::<Sha256>(), b.body.id::<Sha256>());
    assert_ne!(a.id::<Sha256>(), b.id::<Sha256>());
    assert!(check(&f, &a).is_ok());
    assert!(check(&f, &b).is_ok());
    b.selection = a.selection.clone();
    assert_eq!(check(&f, &b).unwrap_err(), g::Error::Context);
    let mut different = a.body.decision.clone();
    different.order = Bytes::from_static(b"BA");
    assert_ne!(different.id::<Sha256>(), a.body.decision.id::<Sha256>());
    different = a.body.decision.clone();
    different.slot.profile = Digest::from([0; 32]);
    assert_ne!(different.id::<Sha256>(), a.body.decision.id::<Sha256>());
    different = a.body.decision.clone();
    different.slot.parent = g::NativeParent::Proposal {
        round: round(3),
        digest: Digest::from([0; 32]),
    };
    assert_ne!(different.id::<Sha256>(), a.body.decision.id::<Sha256>());
}

#[test]
fn policy_is_mandatory_for_malformed_preferences_build_and_decision() {
    let f = fixture(10);
    let mut p = origin(&f);
    let g::Kind::First(row) = &mut p.body.firsts[1].message.kind else {
        unreachable!()
    };
    row.preference = Some(Bytes::from_static(b"AA"));
    resign(&f, &mut p.body.firsts[1]);
    refresh(&f, &mut p);
    assert_eq!(check(&f, &p).unwrap_err(), g::Error::Policy);
    p = origin(&f);
    p.body.build = Bytes::from_static(b"forged");
    p.selection = select(&f, &p.body);
    assert_eq!(check(&f, &p).unwrap_err(), g::Error::Policy);
    p = origin(&f);
    p.body.decision.order = Bytes::from_static(b"BA");
    p.selection = select(&f, &p.body);
    assert_eq!(check(&f, &p).unwrap_err(), g::Error::Policy);
}

#[test]
fn native_parent_and_expected_profile_are_captured_not_peer_assertions() {
    let f = fixture(10);
    let rows = firsts(&f);
    for variant in 0..5 {
        let mut expected = g_core(&f);
        match variant {
            0 => expected.slot.roster = Digest::from([0; 32]),
            1 => expected.slot.profile = Digest::from([0; 32]),
            2 => expected.slot.parent = g::NativeParent::Genesis(Digest::from([0; 32])),
            3 => {
                expected.slot.parent = g::NativeParent::Proposal {
                    round: Round::new(Epoch::new(2), View::new(3)),
                    digest: Digest::from([93; 32]),
                }
            }
            _ => expected.slot.proposal.parent = View::new(4),
        }
        assert_eq!(
            g::verify_firsts::<Sha256, _, _>(
                &mut TestRng::new(716),
                &f.verifier,
                &expected,
                input(),
                &rows,
                G_LIMITS,
                legal_row,
                &Sequential
            )
            .unwrap_err(),
            g::Error::Context
        );
    }
}

fn phase_votes(f: &Fixture<S>, phase: g::Phase, count: usize) -> Vec<Signed> {
    (0..count)
        .map(|id| {
            sign(
                f,
                id,
                g::Kind::Phase {
                    phase,
                    decision: Digest::from([95; 32]),
                },
            )
        })
        .collect()
}
#[test]
fn phase_quorums_require_native_n_minus_f_exact_subjects_and_unique_owners() {
    for n in [7, 8, 9, 10, 13, 16] {
        let f = fixture(n);
        let c = g::Committee::new(n as usize).unwrap();
        for phase in [g::Phase::FastFinal, g::Phase::Prepare, g::Phase::Commit] {
            let votes = phase_votes(&f, phase, c.quorum());
            let mut rng = TestRng::new(717);
            let q = g::Quorum::from_votes(&mut rng, &f.verifier, &votes, G_LIMITS, &Sequential)
                .unwrap();
            assert!(q.verify(&mut rng, &f.verifier, G_LIMITS, &Sequential));
            let scope = Scoped::verifier(Arc::new(f.verifier.clone()));
            assert!(q.verify_scoped(&mut rng, &scope, G_LIMITS, &Sequential));
            assert_eq!(
                g::Quorum::from_votes(
                    &mut rng,
                    &f.verifier,
                    &votes[..c.quorum() - 1],
                    G_LIMITS,
                    &Sequential
                )
                .unwrap_err(),
                g::Error::Quorum
            );
            let mut duplicate = votes.clone();
            duplicate[1] = duplicate[0].clone();
            assert_eq!(
                g::Quorum::from_votes(&mut rng, &f.verifier, &duplicate, G_LIMITS, &Sequential)
                    .unwrap_err(),
                g::Error::Identity
            );
            let mut mixed = votes.clone();
            mixed[1].message.round = round(5);
            resign(&f, &mut mixed[1]);
            assert_eq!(
                g::Quorum::from_votes(&mut rng, &f.verifier, &mixed, G_LIMITS, &Sequential)
                    .unwrap_err(),
                g::Error::Identity
            );
            let encoded = q.encode();
            let decoded =
                g::Quorum::<S, Digest>::decode_cfg(encoded, &(G_LIMITS, n as usize)).unwrap();
            assert!(decoded.verify(&mut rng, &f.verifier, G_LIMITS, &Sequential));
        }
    }
}

#[test]
fn g1_signature_domain_cannot_be_replayed_as_legacy_m1() {
    let f = fixture(7);
    let p = origin(&f);
    let signed = &p.body.firsts[1];
    let legacy = super::Signed::<S, Digest> {
        message: super::Message {
            slot: signed.message.slot,
            round: signed.message.round,
            leader: signed.message.leader,
            kind: super::Kind::First {
                core: p.body.core.id::<Sha256>(),
                report: Some(Bytes::from_static(b"x")),
            },
        },
        attestation: signed.attestation.clone(),
    };
    assert!(!legacy.verify(&mut TestRng::new(718), &f.verifier, &Sequential));
    let old = super::proof(&f);
    let mut replay = signed.clone();
    replay.attestation = old.firsts[1].attestation.clone();
    assert!(!replay.verify(&mut TestRng::new(719), &f.verifier, G_LIMITS, &Sequential));
}

#[test]
fn no_observer_nonattributable_scheme_or_wrong_role_can_sign() {
    let f = fixture(7);
    let row = firsts(&f)[1].message.clone();
    assert_eq!(
        g::Signed::sign(&f.verifier, row.clone(), G_LIMITS).unwrap_err(),
        g::Error::Signature
    );
    assert_eq!(
        g::Signed::sign(&f.schemes[2], row.clone(), G_LIMITS).unwrap_err(),
        g::Error::Identity
    );
    let p = origin(&f);
    assert_eq!(
        g::Signed::sign(&f.schemes[1], p.selection.message, G_LIMITS).unwrap_err(),
        g::Error::Identity
    );
    let threshold = vrf::fixture::<MinSig, _>(
        &mut TestRng::new(721),
        b"_COMMONWARE_CONSENSUS_G1_THRESHOLD_TEST",
        7,
    );
    assert_eq!(
        g::Signed::sign(&threshold.schemes[1], row, G_LIMITS).unwrap_err(),
        g::Error::Roster
    );
}

#[test]
fn assembled_phase_certificate_cannot_change_role_context_or_decision() {
    let f = fixture(10);
    let votes = phase_votes(&f, g::Phase::Prepare, 7);
    let q = g::Quorum::from_votes(
        &mut TestRng::new(722),
        &f.verifier,
        &votes,
        G_LIMITS,
        &Sequential,
    )
    .unwrap();
    for variant in 0..5 {
        let mut forged = q.clone();
        match variant {
            0 => forged.message.round = round(5),
            1 => forged.message.slot = Digest::from([0; 32]),
            2 => forged.message.leader = Participant::new(1),
            3 => {
                forged.message.kind = g::Kind::Phase {
                    phase: g::Phase::Commit,
                    decision: Digest::from([95; 32]),
                }
            }
            _ => {
                forged.message.kind = g::Kind::Phase {
                    phase: g::Phase::Prepare,
                    decision: Digest::from([0; 32]),
                }
            }
        }
        assert!(!forged.verify(&mut TestRng::new(723), &f.verifier, G_LIMITS, &Sequential));
    }
}

#[test]
fn frame_discriminants_owner_and_optional_fields_are_canonical() {
    let f = fixture(10);
    let p = origin(&f);
    let message = &p.body.firsts[1].message;
    let kind_offset = 8 + 32 + 4 + message.round.encode_size() + 4;
    let first_option = kind_offset + 1 + 32 + 32 + 4;
    for (offset, byte) in [(kind_offset, 255), (first_option, 2)] {
        let mut malformed = message.encode().to_vec();
        malformed[offset] = byte;
        assert!(g::Message::<Digest>::decode_cfg(malformed, &G_LIMITS).is_err());
    }
    let mut owner = message.encode().to_vec();
    owner[kind_offset + 1 + 64..kind_offset + 1 + 68].copy_from_slice(&64u32.to_be_bytes());
    assert!(g::Message::<Digest>::decode_cfg(owner, &G_LIMITS).is_err());
    let mut excess = message.encode().to_vec();
    let size = u32::from_be_bytes(excess[4..8].try_into().unwrap());
    excess[4..8].copy_from_slice(&(size + 1).to_be_bytes());
    excess.push(0);
    assert!(g::Message::<Digest>::decode_cfg(excess, &G_LIMITS).is_err());
    let mut huge_report = message.encode().to_vec();
    huge_report[first_option + 1..first_option + 5].copy_from_slice(&u32::MAX.to_be_bytes());
    assert!(g::Message::<Digest>::decode_cfg(huge_report, &G_LIMITS).is_err());
}

#[test]
fn bounded_canonical_codecs_reject_trailing_truncated_wrong_type_and_lengths() {
    let f = fixture(10);
    let p = origin(&f);
    let bytes = p.encode();
    let decoded = Origin::decode_cfg(bytes.clone(), &G_LIMITS).unwrap();
    assert_eq!(decoded.encode(), bytes);
    assert!(check(&f, &decoded).is_ok());
    assert_eq!(p.encode_size(), bytes.len());
    for len in 0..bytes.len() {
        assert!(Origin::decode_cfg(bytes.slice(..len), &G_LIMITS).is_err());
    }
    let mut extra = bytes.to_vec();
    extra.push(0);
    assert!(Origin::decode_cfg(extra, &G_LIMITS).is_err());
    let mut wrong = bytes.to_vec();
    wrong[3] = b'2';
    assert!(Origin::decode_cfg(wrong, &G_LIMITS).is_err());
    let mut huge = bytes.to_vec();
    huge[4..8].copy_from_slice(&u32::MAX.to_be_bytes());
    assert!(Origin::decode_cfg(huge, &G_LIMITS).is_err());
    let mut limited = G_LIMITS;
    limited.order_bytes = 1;
    assert!(Origin::decode_cfg(bytes, &limited).is_err());
    let mut rows = firsts(&f);
    let g::Kind::First(row) = &mut rows[1].message.kind else {
        unreachable!()
    };
    row.report = Some(Bytes::from(vec![0; G_LIMITS.report_bytes + 1]));
    assert_eq!(
        g::Signed::sign(&f.schemes[1], rows[1].message.clone(), G_LIMITS).unwrap_err(),
        g::Error::Limit
    );
    let mut body = p.body.clone();
    body.build = Bytes::from(vec![0; g::MAX_FIRST_BYTES]);
    let over = g::Origin {
        body,
        selection: p.selection,
    };
    assert_eq!(check(&f, &over).unwrap_err(), g::Error::Limit);
}

#[test]
fn complete_origin_budget_is_distinct_from_one_native_first_envelope() {
    let f = fixture(10);
    let limits = g::Limits {
        report_bytes: 30_000,
        order_bytes: 128,
        build_bytes: 256,
        material_bytes: 256,
        origin_bytes: 512 * 1024,
    };
    limits.validate::<S, Digest>(&g_core(&f)).unwrap();
    let mut p = origin(&f);
    for signed in p.body.firsts.iter_mut().skip(1) {
        let g::Kind::First(row) = &mut signed.message.kind else {
            unreachable!()
        };
        row.report = Some(Bytes::from(vec![row.owner.get() as u8; 30_000]));
        *signed = g::Signed::sign(
            &f.schemes[usize::from(signed.attestation.signer)],
            signed.message.clone(),
            limits,
        )
        .unwrap();
        assert!(signed.encode_size() < g::MAX_FIRST_BYTES);
    }
    p.body.population = population(&p.body.firsts);
    p.body.build = Bytes::new();
    p.selection = g::Signed::sign(
        &f.schemes[0],
        g::Message {
            slot: p.body.core.slot.id::<Sha256>(),
            round: round(4),
            leader: Participant::new(0),
            kind: g::Kind::Select {
                body: p.body.id::<Sha256>(),
                decision: p.body.decision.id::<Sha256>(),
            },
        },
        limits,
    )
    .unwrap();
    assert!(p.encode_size() > g::MAX_FIRST_BYTES);
    assert!(p.encode_size() < limits.origin_bytes);
    let decoded = Origin::decode_cfg(p.encode(), &limits).unwrap();
    assert!(
        decoded
            .verify::<Sha256, _>(
                &mut TestRng::new(720),
                &f.verifier,
                &g_core(&f),
                input(),
                limits,
                |r| r.report.as_ref().is_none_or(|b| b.len() == 30_000)
                    && r.preference.as_ref().is_none_or(|b| b.as_ref() == b"AB"),
                |rows, body| body.population == population(rows.originals())
                    && body.build.is_empty()
                    && body.decision.order.as_ref() == b"AB",
                &Sequential
            )
            .is_ok()
    );
    let mut small = limits;
    small.origin_bytes = g::MAX_FIRST_BYTES;
    assert!(small.validate::<S, Digest>(&g_core(&f)).is_err());
    assert!(Origin::decode_cfg(p.encode(), &small).is_err());
    let mut first_too_large = limits;
    first_too_large.report_bytes = g::MAX_FIRST_BYTES;
    assert!(first_too_large.validate::<S, Digest>(&g_core(&f)).is_err());
}

struct GeneralEvidenceConformance;
impl Conformance for GeneralEvidenceConformance {
    async fn commit(seed: u64) -> Vec<u8> {
        let f = ed25519::fixture(
            &mut TestRng::new(seed),
            b"_COMMONWARE_CONSENSUS_G1_CONFORMANCE",
            10,
        );
        let p = origin(&f);
        let mut encodings = vec![
            p.body.core.slot.encode(),
            p.body.core.encode(),
            p.body.decision.encode(),
            p.body.encode(),
            p.encode(),
            p.selection.message.encode(),
            p.selection.encode(),
        ];
        for (report, preference) in [
            (None, None),
            (Some(Bytes::new()), None),
            (None, Some(Bytes::new())),
            (
                Some(Bytes::from_static(b"r")),
                Some(Bytes::from_static(b"AB")),
            ),
        ] {
            let mut rows = firsts(&f);
            let g::Kind::First(row) = &mut rows[1].message.kind else {
                unreachable!()
            };
            row.report = report;
            row.preference = preference;
            resign(&f, &mut rows[1]);
            encodings.push(rows[1].message.encode());
            encodings.push(rows[1].encode());
        }
        for phase in [g::Phase::FastFinal, g::Phase::Prepare, g::Phase::Commit] {
            let votes = phase_votes(&f, phase, 7);
            let q = g::Quorum::from_votes(
                &mut TestRng::new(seed),
                &f.verifier,
                &votes,
                G_LIMITS,
                &Sequential,
            )
            .unwrap();
            encodings.push(q.message.encode());
            encodings.push(q.encode());
        }
        encodings.encode().to_vec()
    }
}
conformance_tests! { GeneralEvidenceConformance => 32 }

#[test]
fn recovery_subject_quorums_use_actual_roster_and_exact_unsigned_body() {
    for n in [4u32, 7, 8, 9, 10, 11, 12, 13, 16, 31, 64] {
        let f = fixture(n);
        let c = g::Committee::new(n as usize).unwrap();
        let mut rng = TestRng::new(9100 + u64::from(n));
        let subject = g::recovery::Subject {
            core: g_core(&f).id::<Sha256>(),
            input: input(),
            entry: Digest::from([21; 32]),
            proposal: Digest::from([22; 32]),
            decision: Digest::from([23; 32]),
        };
        for phase in [g::recovery::Phase::Prepare, g::recovery::Phase::Commit] {
            let votes: Vec<_> = (0..n as usize)
                .map(|owner| {
                    g::Signed::sign(
                        &f.schemes[owner],
                        g::Message {
                            slot: g_slot(&f).id::<Sha256>(),
                            round: round(8),
                            leader: Participant::new(n - 1),
                            kind: g::Kind::Recovery {
                                phase,
                                subject: subject.clone(),
                            },
                        },
                        G_LIMITS,
                    )
                    .unwrap()
                })
                .collect();
            assert_eq!(
                g::Quorum::from_votes(
                    &mut rng,
                    &f.verifier,
                    &votes[..c.quorum() - 1],
                    G_LIMITS,
                    &Sequential,
                )
                .unwrap_err(),
                g::Error::Quorum,
            );
            let quorum = g::Quorum::from_votes(
                &mut rng,
                &f.verifier,
                &votes[..c.quorum()],
                G_LIMITS,
                &Sequential,
            )
            .unwrap();
            assert!(quorum.verify(&mut rng, &f.verifier, G_LIMITS, &Sequential));
            let decoded = g::Quorum::<S, Digest>::decode_cfg(
                quorum.encode(),
                &(G_LIMITS, f.verifier.certificate_codec_config()),
            )
            .unwrap();
            assert!(decoded.verify(&mut rng, &f.verifier, G_LIMITS, &Sequential));
            let mut mixed = votes[..c.quorum()].to_vec();
            let mut message = mixed[0].message.clone();
            let g::Kind::Recovery {
                subject: mixed_subject,
                ..
            } = &mut message.kind
            else {
                unreachable!()
            };
            // Equal semantic decisions do not authorize different admissions.
            mixed_subject.proposal = Digest::from([24; 32]);
            mixed[0] = g::Signed::sign(&f.schemes[0], message, G_LIMITS).unwrap();
            assert_eq!(
                g::Quorum::from_votes(&mut rng, &f.verifier, &mixed, G_LIMITS, &Sequential,)
                    .unwrap_err(),
                g::Error::Identity,
            );
            let mut substituted = quorum;
            substituted.message.kind = g::Kind::Phase {
                phase: g::Phase::Commit,
                decision: subject.decision,
            };
            assert!(!substituted.verify(&mut rng, &f.verifier, G_LIMITS, &Sequential));
        }
    }
}

#[test]
fn recovery_propose_is_coordinator_only_and_not_a_quorum_vote() {
    let f = fixture(10);
    let mut rng = TestRng::new(9200);
    let message = g::Message {
        slot: g_slot(&f).id::<Sha256>(),
        round: round(8),
        leader: Participant::new(9),
        kind: g::Kind::Recovery {
            phase: g::recovery::Phase::Propose,
            subject: g::recovery::Subject {
                core: g_core(&f).id::<Sha256>(),
                input: input(),
                entry: Digest::from([21; 32]),
                proposal: Digest::from([22; 32]),
                decision: Digest::from([23; 32]),
            },
        },
    };
    assert_eq!(
        g::Signed::sign(&f.schemes[0], message.clone(), G_LIMITS).unwrap_err(),
        g::Error::Identity,
    );
    let proposal = g::Signed::sign(&f.schemes[9], message, G_LIMITS).unwrap();
    assert!(proposal.verify(&mut rng, &f.verifier, G_LIMITS, &Sequential));
    let mut forged = proposal.clone();
    let g::Kind::Recovery { phase, .. } = &mut forged.message.kind else {
        unreachable!()
    };
    *phase = g::recovery::Phase::Prepare;
    assert!(!forged.verify(&mut rng, &f.verifier, G_LIMITS, &Sequential));
    let votes = vec![proposal; g::Committee::new(10).unwrap().quorum()];
    assert_eq!(
        g::Quorum::from_votes(&mut rng, &f.verifier, &votes, G_LIMITS, &Sequential).unwrap_err(),
        g::Error::Phase,
    );
}
