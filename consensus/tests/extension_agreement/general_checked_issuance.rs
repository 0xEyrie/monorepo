//! Checked application capabilities retain exact material and current crypto.
//! These are component authority controls, not native WAL or live recovery proof.
use super::{general_normal as fixture, *};
use commonware_consensus::simplex::{
    extension::agreement::general::{
        self as g,
        issuance::{Error as IssuanceError, Material, State},
        normal::Assembly,
    },
    types::Notarization,
};
use std::cell::Cell;

type Fingerprint = (Vec<Bytes>, Round, Option<Bytes>);
fn fingerprint(state: &State<S, Digest>) -> Fingerprint {
    (
        state
            .records()
            .iter()
            .map(commonware_codec::Encode::encode)
            .collect(),
        state.floor(),
        state.snapshot().map(commonware_codec::Encode::encode),
    )
}
fn body_cap(f: &Fixture<S>, origin: &g::Origin<S, Digest>) -> g::VerifiedBody<Digest> {
    let rows = Cell::new(0usize);
    let builds = Cell::new(0usize);
    let checked = origin
        .body
        .verify::<Sha256, _>(
            &mut TestRng::new(15101),
            &f.verifier,
            &origin.body.core,
            fixture::input(),
            fixture::G_LIMITS,
            |row| {
                rows.set(rows.get() + 1);
                fixture::legal_row(row)
            },
            |rows, body| {
                builds.set(builds.get() + 1);
                fixture::build_policy(rows, body)
            },
            &Sequential,
        )
        .unwrap();
    assert_eq!(
        rows.get(),
        g::Committee::new(f.schemes.len()).unwrap().quorum()
    );
    assert_eq!(builds.get(), 1);
    checked
}
fn nqc(f: &Fixture<S>, c: &g::Core<Digest>) -> Notarization<S, Digest> {
    let q = g::Committee::new(f.schemes.len()).unwrap().quorum();
    let votes: Vec<_> = f
        .schemes
        .iter()
        .take(q)
        .map(|s| Notarize::sign(s, c.slot.proposal.clone()).unwrap())
        .collect();
    Notarization::from_notarizes(&f.verifier, non_empty![@votes.iter()], &Sequential).unwrap()
}
fn assembly(f: &Fixture<S>, origin: &g::Origin<S, Digest>) -> Assembly<S, Digest> {
    Assembly::new::<Sha256, _>(
        &mut TestRng::new(15102),
        &f.verifier,
        &origin.body.core,
        fixture::input(),
        origin.clone(),
        nqc(f, &origin.body.core),
        fixture::G_LIMITS,
        fixture::legal_row,
        fixture::build_policy,
        &Sequential,
    )
    .unwrap()
}
fn outside(c: &g::Core<Digest>, n: usize) -> usize {
    (0..n)
        .find(|owner| {
            let p = Participant::new(*owner as u32);
            p != c.leader && !c.followers.contains(&p)
        })
        .unwrap()
}
fn state(
    f: &Fixture<S>,
    c: &g::Core<Digest>,
    owner: usize,
    limits: g::Limits,
    replay: bool,
) -> State<S, Digest> {
    if replay {
        State::for_replay::<Sha256>(
            f.schemes[owner].clone(),
            c.clone(),
            fixture::input(),
            limits,
        )
        .unwrap()
    } else {
        State::new::<Sha256>(
            f.schemes[owner].clone(),
            c.clone(),
            fixture::input(),
            limits,
        )
        .unwrap()
    }
}
fn restore_first(state: &mut State<S, Digest>, first: &g::issuance::Record<Digest>) {
    state
        .restore::<Sha256, _>(
            &mut TestRng::new(15103),
            first,
            Material::None,
            fixture::legal_row,
            fixture::build_policy,
            &Sequential,
        )
        .unwrap();
}

#[test]
fn checked_capabilities_reauthenticate_same_roster_in_current_namespace() {
    for n in [8, 9, 10, 13] {
        let f = fixture(n);
        let foreign = ed25519::fixture(
            &mut TestRng::new(101),
            b"_COMMONWARE_CONSENSUS_CHECKED_FOREIGN_TEST",
            n,
        );
        assert_eq!(f.participants, foreign.participants);
        let c = fixture::core(&f);
        assert_eq!(c, fixture::core(&foreign));
        let a = fixture::origin(&f, &c, b"AB", false);
        let checked = body_cap(&f, &a);
        let material = assembly(&f, &a);
        let leader = usize::from(c.leader);
        let mut own = fixture::local(&f, &c, leader);
        let first = own
            .reserve_first::<Sha256>(None, None, fixture::legal_row)
            .unwrap();
        let selection = own
            .reserve_select_checked::<Sha256, _>(
                &mut TestRng::new(15104),
                &a.body,
                &checked,
                &Sequential,
            )
            .unwrap();
        let mut other = fixture::local(&foreign, &c, leader);
        other
            .reserve_first::<Sha256>(None, None, fixture::legal_row)
            .unwrap();
        let before = fingerprint(&other);
        assert_eq!(
            other.reserve_select_checked::<Sha256, _>(
                &mut TestRng::new(15105),
                &a.body,
                &checked.clone(),
                &Sequential
            ),
            Err(IssuanceError::Verification(g::Error::Signature))
        );
        assert_eq!(fingerprint(&other), before);
        let mut replay = state(&foreign, &c, leader, fixture::G_LIMITS, true);
        restore_first(&mut replay, &first);
        let before = fingerprint(&replay);
        assert_eq!(
            replay.restore_select_checked::<Sha256, _>(
                &mut TestRng::new(15106),
                &selection,
                &a.body,
                &checked,
                &Sequential
            ),
            Err(IssuanceError::Verification(g::Error::Signature))
        );
        assert_eq!(fingerprint(&replay), before);

        let owner = outside(&c, n as usize);
        let mut normal = fixture::local(&f, &c, owner);
        let records = fixture::prime(&mut normal, &c, &a);
        let reserved = normal
            .reserve_normal_checked::<Sha256, _>(&mut TestRng::new(15107), &material, &Sequential)
            .unwrap();
        let mut foreign_normal = fixture::local(&foreign, &c, owner);
        fixture::prime(&mut foreign_normal, &c, &a);
        let before = fingerprint(&foreign_normal);
        assert_eq!(
            foreign_normal.reserve_normal_checked::<Sha256, _>(
                &mut TestRng::new(15108),
                &material.clone(),
                &Sequential
            ),
            Err(IssuanceError::Verification(g::Error::Signature))
        );
        assert_eq!(fingerprint(&foreign_normal), before);
        let mut replay = state(&foreign, &c, owner, fixture::G_LIMITS, true);
        fixture::replay_prime(&mut replay, &a, &records);
        let before = fingerprint(&replay);
        assert_eq!(
            replay.restore_normal_checked::<Sha256, _>(
                &mut TestRng::new(15109),
                &reserved,
                &material,
                &Sequential
            ),
            Err(IssuanceError::Verification(g::Error::Signature))
        );
        assert_eq!(fingerprint(&replay), before);
    }
}

#[test]
fn every_checked_limit_is_bound_before_state_mutation() {
    let f = fixture(9);
    let c = fixture::core(&f);
    let a = fixture::origin(&f, &c, b"AB", false);
    let checked = body_cap(&f, &a);
    let material = assembly(&f, &a);
    let leader = usize::from(c.leader);
    let owner = outside(&c, f.schemes.len());
    let mut source = fixture::local(&f, &c, leader);
    let first = source
        .reserve_first::<Sha256>(None, None, fixture::legal_row)
        .unwrap();
    let selection = source
        .reserve_select_checked::<Sha256, _>(
            &mut TestRng::new(15110),
            &a.body,
            &checked,
            &Sequential,
        )
        .unwrap();
    let mut source = fixture::local(&f, &c, owner);
    let original_first = fixture::prime(&mut source, &c, &a);
    let reserved = source
        .reserve_normal_checked::<Sha256, _>(&mut TestRng::new(15111), &material, &Sequential)
        .unwrap();
    for field in 0..5 {
        let mut limits = fixture::G_LIMITS;
        match field {
            0 => limits.report_bytes += 1,
            1 => limits.order_bytes += 1,
            2 => limits.build_bytes += 1,
            3 => limits.material_bytes += 1,
            _ => limits.origin_bytes -= 1,
        }
        assert_ne!(limits, checked.limits());
        for replaying in [false, true] {
            let mut select = state(&f, &c, leader, limits, replaying);
            if replaying {
                restore_first(&mut select, &first);
            } else {
                select
                    .reserve_first::<Sha256>(None, None, fixture::legal_row)
                    .unwrap();
            }
            let before = fingerprint(&select);
            if replaying {
                assert_eq!(
                    select.restore_select_checked::<Sha256, _>(
                        &mut TestRng::new(15112),
                        &selection,
                        &a.body,
                        &checked,
                        &Sequential
                    ),
                    Err(IssuanceError::Authority)
                );
            } else {
                assert_eq!(
                    select.reserve_select_checked::<Sha256, _>(
                        &mut TestRng::new(15113),
                        &a.body,
                        &checked,
                        &Sequential
                    ),
                    Err(IssuanceError::Authority)
                );
            }
            assert_eq!(fingerprint(&select), before, "SELECT field {field}");
            let mut normal = state(&f, &c, owner, limits, replaying);
            if replaying {
                fixture::replay_prime(&mut normal, &a, &original_first);
            } else {
                fixture::prime(&mut normal, &c, &a);
            }
            let before = fingerprint(&normal);
            if replaying {
                assert_eq!(
                    normal.restore_normal_checked::<Sha256, _>(
                        &mut TestRng::new(15114),
                        &reserved,
                        &material,
                        &Sequential
                    ),
                    Err(IssuanceError::Authority)
                );
            } else {
                assert_eq!(
                    normal.reserve_normal_checked::<Sha256, _>(
                        &mut TestRng::new(15115),
                        &material,
                        &Sequential
                    ),
                    Err(IssuanceError::Authority)
                );
            }
            assert_eq!(fingerprint(&normal), before, "normal field {field}");
        }
    }
}

#[test]
fn raw_body_and_proof_mutations_cannot_reuse_immutable_checks() {
    let f = fixture(10);
    let c = fixture::core(&f);
    let a = fixture::origin(&f, &c, b"AB", false);
    let b = fixture::origin(&f, &c, b"AB", true);
    let checked = body_cap(&f, &a);
    let material = assembly(&f, &a);
    let retained = commonware_codec::Encode::encode(material.origin());
    let identity = material.id();
    let mut own = fixture::local(&f, &c, usize::from(c.leader));
    own.reserve_first::<Sha256>(None, None, fixture::legal_row)
        .unwrap();
    for mutation in 0..3 {
        let mut body = a.body.clone();
        match mutation {
            0 => body.build = Bytes::from_static(b"changed raw Build"),
            1 => {
                body.firsts[0].attestation.signature = body.firsts[1].attestation.signature.clone()
            }
            _ => body = b.body.clone(),
        }
        assert_ne!(body.id::<Sha256>(), checked.body());
        let before = fingerprint(&own);
        assert_eq!(
            own.reserve_select_checked::<Sha256, _>(
                &mut TestRng::new(15116),
                &body,
                &checked,
                &Sequential
            ),
            Err(IssuanceError::Authority)
        );
        assert_eq!(fingerprint(&own), before);
    }
    let mut raw = material.origin().clone();
    raw.selection.message.kind = g::Kind::Select {
        body: Digest::from([99; 32]),
        decision: raw.body.decision.id::<Sha256>(),
    };
    let callbacks = Cell::new(0usize);
    assert!(
        Assembly::new::<Sha256, _>(
            &mut TestRng::new(15117),
            &f.verifier,
            &c,
            fixture::input(),
            raw,
            nqc(&f, &c),
            fixture::G_LIMITS,
            fixture::legal_row,
            |rows, body| {
                callbacks.set(callbacks.get() + 1);
                fixture::build_policy(rows, body)
            },
            &Sequential
        )
        .is_err()
    );
    assert_eq!(callbacks.get(), 0, "wrong SELECT must not invoke Build");
    assert_eq!(material.id(), identity);
    assert_eq!(
        commonware_codec::Encode::encode(material.origin()),
        retained
    );
    assert_eq!(material.clone(), material);
}

#[test]
fn select_alias_retry_and_checked_replay_keep_exact_original_authority() {
    for n in [8, 9, 13] {
        let f = fixture(n);
        let c = fixture::core(&f);
        let a = fixture::origin(&f, &c, b"AB", false);
        let b = fixture::origin(&f, &c, b"AB", true);
        assert_eq!(a.body.decision, b.body.decision);
        let ca = body_cap(&f, &a);
        let cb = body_cap(&f, &b);
        assert_ne!(ca.body(), cb.body());
        let mut own = fixture::local(&f, &c, usize::from(c.leader));
        let first = own
            .reserve_first::<Sha256>(None, None, fixture::legal_row)
            .unwrap();
        let original = own
            .reserve_select_checked::<Sha256, _>(
                &mut TestRng::new(15118),
                &a.body,
                &ca,
                &Sequential,
            )
            .unwrap();
        let before = fingerprint(&own);
        let retry = own
            .reserve_select_checked::<Sha256, _>(
                &mut TestRng::new(15119),
                &b.body,
                &cb,
                &Sequential,
            )
            .unwrap();
        assert_eq!(retry, original);
        assert_eq!(retry.authority(), Some(ca.body()));
        assert_eq!(fingerprint(&own), before);
        let mut replay = state(&f, &c, usize::from(c.leader), fixture::G_LIMITS, true);
        restore_first(&mut replay, &first);
        let before = fingerprint(&replay);
        assert_eq!(
            replay.restore_select_checked::<Sha256, _>(
                &mut TestRng::new(15120),
                &original,
                &b.body,
                &cb,
                &Sequential
            ),
            Err(IssuanceError::Authority)
        );
        assert_eq!(fingerprint(&replay), before);
        replay
            .restore_select_checked::<Sha256, _>(
                &mut TestRng::new(15121),
                &original,
                &a.body,
                &ca,
                &Sequential,
            )
            .unwrap();
        replay.finish_replay().unwrap();
        let signed = replay.sign_reserved(&original).unwrap();
        assert_eq!(signed.message, original.message().unwrap().clone());
        assert!(matches!(signed.message.kind,g::Kind::Select {body,..} if body==ca.body()));
    }
}

#[test]
fn normal_alias_retry_and_checked_replay_keep_exact_original_origin() {
    for n in [8, 9, 13] {
        let f = fixture(n);
        let c = fixture::core(&f);
        let a = fixture::origin(&f, &c, b"AB", false);
        let b = fixture::origin(&f, &c, b"AB", true);
        let ca = assembly(&f, &a);
        let cb = assembly(&f, &b);
        assert_eq!(ca.decision(), cb.decision());
        assert_ne!(ca.origin().id::<Sha256>(), cb.origin().id::<Sha256>());
        let owner = outside(&c, f.schemes.len());
        let mut own = fixture::local(&f, &c, owner);
        let first = fixture::prime(&mut own, &c, &a);
        let original = own
            .reserve_normal_checked::<Sha256, _>(&mut TestRng::new(15122), &ca, &Sequential)
            .unwrap();
        let before = fingerprint(&own);
        let retry = own
            .reserve_normal_checked::<Sha256, _>(&mut TestRng::new(15123), &cb, &Sequential)
            .unwrap();
        assert_eq!(retry, original);
        assert_eq!(retry.agreement().authority(), Some(a.id::<Sha256>()));
        assert_eq!(fingerprint(&own), before);
        let mut replay = state(&f, &c, owner, fixture::G_LIMITS, true);
        fixture::replay_prime(&mut replay, &a, &first);
        let before = fingerprint(&replay);
        assert_eq!(
            replay.restore_normal_checked::<Sha256, _>(
                &mut TestRng::new(15124),
                &original,
                &cb,
                &Sequential
            ),
            Err(IssuanceError::Authority)
        );
        assert_eq!(fingerprint(&replay), before);
        replay
            .restore_normal_checked::<Sha256, _>(
                &mut TestRng::new(15125),
                &original,
                &ca,
                &Sequential,
            )
            .unwrap();
        replay.finish_replay().unwrap();
        let pair = replay.sign_normal::<Sha256>(&original).unwrap();
        assert_eq!(pair.origin_hint, a.id::<Sha256>());
        assert_ne!(pair.origin_hint, b.id::<Sha256>());
    }
}
