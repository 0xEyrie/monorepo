//! Public-key replay of declared original histories for the inactive G1 component.
//!
//! These checks do not establish recovery admission, Byzantine completeness,
//! journal synchronization, native finality, or operating recovery.
use super::*;
use commonware_consensus::simplex::extension::agreement::general::{
    self as g,
    issuance::{Action, HistoryPage, Material, Record, Snapshot, State, history},
};
use commonware_cryptography::Hasher as _;
use std::cell::Cell;

const G_LIMITS: g::Limits = g::Limits {
    report_bytes: 128,
    order_bytes: 128,
    build_bytes: 256,
    material_bytes: 256,
    origin_bytes: g::MAX_EVIDENCE_BYTES,
};
type GSigned = g::Signed<S, Digest>;
type GOrigin = g::Origin<S, Digest>;

fn core(f: &Fixture<S>) -> g::Core<Digest> {
    let c = g::Committee::new(f.schemes.len()).unwrap();
    let leader = Participant::new(c.len() as u32 - 1);
    g::Core {
        slot: g::Slot {
            profile: Digest::from([110; 32]),
            domain: Digest::from([111; 32]),
            roster: g::Slot::<Digest>::roster::<Sha256, _>(&f.verifier),
            cut: 9,
            proposal: Proposal::new(round(4), View::new(3), Digest::from([112; 32])),
            parent: g::NativeParent::Proposal {
                round: round(3),
                digest: Digest::from([113; 32]),
            },
        },
        leader,
        followers: (0..c.len() as u32 - 1)
            .filter(|owner| *owner != 1)
            .take(c.quorum() - 1)
            .map(Participant::new)
            .collect(),
    }
}

fn input() -> Digest {
    Digest::from([114; 32])
}

fn entry() -> Digest {
    Digest::from([115; 32])
}

#[test]
fn startup_limits_budget_maximal_recover_not_only_first() {
    let f = fixture(4);
    let core = core(&f);
    let owner = usize::from(core.leader);
    let mut state =
        State::new::<Sha256>(f.schemes[owner].clone(), core.clone(), input(), G_LIMITS).unwrap();
    // Future views have a larger native encoding than the original small view.
    let ballot = Round::new(core.slot.proposal.round.epoch(), View::new(u64::MAX));
    state.fence::<Sha256>(ballot, core.leader).unwrap();
    let recover = state
        .capture_history::<Sha256>(ballot, core.leader, entry(), Some(Bytes::new()))
        .unwrap();
    let recover = g::Signed::sign(&f.schemes[owner], recover, G_LIMITS).unwrap();
    let first = g::Signed::sign(
        &f.schemes[owner],
        g::Message {
            slot: core.slot.id::<Sha256>(),
            round: core.slot.proposal.round,
            leader: core.leader,
            kind: g::Kind::First(g::First {
                core: core.id::<Sha256>(),
                input: input(),
                owner: core.leader,
                report: Some(Bytes::new()),
                preference: Some(Bytes::new()),
            }),
        },
        G_LIMITS,
    )
    .unwrap();
    let report_bytes = g::MAX_FIRST_BYTES - recover.encode_size() + 1;
    assert!(first.encode_size() + report_bytes <= g::MAX_FIRST_BYTES);
    assert!(recover.encode_size() + report_bytes > g::MAX_FIRST_BYTES);
    let limits = g::Limits {
        report_bytes,
        order_bytes: 0,
        build_bytes: 0,
        material_bytes: 0,
        origin_bytes: g::MAX_EVIDENCE_BYTES,
    };
    // The pre-repair profile reaches capture even though its advertised maximum
    // report cannot fit. After repair startup itself must reject the profile.
    if let Ok(mut admitted) =
        State::new::<Sha256>(f.schemes[owner].clone(), core.clone(), input(), limits)
    {
        admitted.fence::<Sha256>(ballot, core.leader).unwrap();
        assert!(
            admitted
                .capture_history::<Sha256>(
                    ballot,
                    core.leader,
                    entry(),
                    Some(Bytes::from(vec![0; report_bytes])),
                )
                .is_err()
        );
    }
    assert_eq!(limits.validate::<S, Digest>(&core), Err(g::Error::Limit));
}

#[test]
fn startup_recover_boundary_is_exact_including_maximal_captured_epoch() {
    let f = fixture(4);
    for epoch in [1, u64::MAX] {
        let mut core = core(&f);
        core.slot.proposal.round = Round::new(Epoch::new(epoch), View::new(4));
        core.slot.parent = g::NativeParent::Proposal {
            round: Round::new(Epoch::new(epoch), View::new(3)),
            digest: Digest::from([113; 32]),
        };
        let owner = usize::from(core.leader);
        let ballot = Round::new(Epoch::new(epoch), View::new(u64::MAX));
        let mut state =
            State::new::<Sha256>(f.schemes[owner].clone(), core.clone(), input(), G_LIMITS)
                .unwrap();
        state.fence::<Sha256>(ballot, core.leader).unwrap();
        let empty = state
            .capture_history::<Sha256>(ballot, core.leader, entry(), Some(Bytes::new()))
            .unwrap();
        let overhead = g::Signed::sign(&f.schemes[owner], empty, G_LIMITS)
            .unwrap()
            .encode_size();
        let exact = g::MAX_FIRST_BYTES - overhead;
        for report_bytes in [exact - 1, exact, exact + 1] {
            let limits = g::Limits {
                report_bytes,
                order_bytes: 0,
                build_bytes: 0,
                material_bytes: 0,
                origin_bytes: g::MAX_EVIDENCE_BYTES,
            };
            assert_eq!(
                limits.validate::<S, Digest>(&core),
                if report_bytes <= exact {
                    Ok(())
                } else {
                    Err(g::Error::Limit)
                }
            );
            if report_bytes > exact {
                continue;
            }
            let mut state =
                State::new::<Sha256>(f.schemes[owner].clone(), core.clone(), input(), limits)
                    .unwrap();
            state.fence::<Sha256>(ballot, core.leader).unwrap();
            let message = state
                .capture_history::<Sha256>(
                    ballot,
                    core.leader,
                    entry(),
                    Some(Bytes::from(vec![0; report_bytes])),
                )
                .unwrap();
            let signed = g::Signed::sign(&f.schemes[owner], message, limits).unwrap();
            assert_eq!(signed.encode_size(), overhead + report_bytes);
            assert_eq!(
                GSigned::decode_cfg(signed.encode(), &limits)
                    .unwrap()
                    .encode(),
                signed.encode()
            );
        }
    }
}

fn sign(f: &Fixture<S>, core: &g::Core<Digest>, owner: usize, kind: g::Kind<Digest>) -> GSigned {
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

fn population(firsts: &[GSigned]) -> Digest {
    Sha256::hash(&[&firsts.iter().flat_map(|s| s.encode()).collect::<Vec<_>>()])
}

fn build(firsts: &[GSigned]) -> Bytes {
    firsts
        .iter()
        .flat_map(|s| {
            let g::Kind::First(first) = &s.message.kind else {
                panic!("FIRST fixture")
            };
            first.report.iter().flat_map(|r| r.iter().copied())
        })
        .collect()
}

fn legal_row(first: &g::First<Digest>) -> bool {
    first.report.as_ref().is_none_or(|r| r.len() == 1)
        && first
            .preference
            .as_ref()
            .is_none_or(|p| p.as_ref() == b"AB")
}

// A bounded application fixture, not the SDK selector or a recovery policy.
fn build_policy(rows: &g::VerifiedRows<S, Digest>, body: &g::OriginBody<S, Digest>) -> bool {
    body.decision.order.as_ref() == b"AB"
        && body.population == population(rows.originals())
        && body.build == build(rows.originals())
        && body.material.is_empty()
}

fn refresh(f: &Fixture<S>, origin: &mut GOrigin) {
    origin.body.population = population(&origin.body.firsts);
    origin.body.build = build(&origin.body.firsts);
    origin.selection = sign(
        f,
        &origin.body.core,
        usize::from(origin.body.core.leader),
        g::Kind::Select {
            body: origin.body.id::<Sha256>(),
            decision: origin.body.decision.id::<Sha256>(),
        },
    );
}

fn origin(f: &Fixture<S>, core: &g::Core<Digest>) -> GOrigin {
    let mut owners = core.followers.clone();
    owners.push(core.leader);
    owners.sort();
    let firsts: Vec<_> = owners
        .into_iter()
        .map(|owner| {
            sign(
                f,
                core,
                usize::from(owner),
                g::Kind::First(g::First {
                    core: core.id::<Sha256>(),
                    input: input(),
                    owner,
                    report: (owner != core.leader).then(|| Bytes::from(vec![owner.get() as u8])),
                    preference: (owner != core.leader).then(|| Bytes::from_static(b"AB")),
                }),
            )
        })
        .collect();
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
    let selection = sign(
        f,
        core,
        usize::from(core.leader),
        g::Kind::Select {
            body: body.id::<Sha256>(),
            decision: body.decision.id::<Sha256>(),
        },
    );
    g::Origin { body, selection }
}

struct Transcript {
    core: g::Core<Digest>,
    origin: GOrigin,
    ballot: Round,
    leader: Participant,
    notice: GSigned,
    pages: Vec<HistoryPage<Digest>>,
}

fn pages(state: &State<S, Digest>) -> Vec<HistoryPage<Digest>> {
    (0..state.records().len())
        .map(|i| state.history_page(i).unwrap())
        .collect()
}

fn captured(
    f: &Fixture<S>,
    state: &State<S, Digest>,
    ballot: Round,
    leader: Participant,
) -> GSigned {
    let message = state
        .capture_history::<Sha256>(ballot, leader, entry(), Some(Bytes::from_static(b"raw")))
        .unwrap();
    let g::Kind::Recover(recover) = &message.kind else {
        unreachable!()
    };
    g::Signed::sign(
        &f.schemes[usize::from(recover.snapshot.owner())],
        message,
        G_LIMITS,
    )
    .unwrap()
}

fn transcript(f: &Fixture<S>, full: bool) -> Transcript {
    let core = core(f);
    let origin = origin(f, &core);
    let mut state = State::new::<Sha256>(
        f.schemes[usize::from(core.leader)].clone(),
        core.clone(),
        input(),
        G_LIMITS,
    )
    .unwrap();
    let pending = full.then(|| {
        let first = state
            .reserve_first::<Sha256>(None, None, legal_row)
            .unwrap();
        let signed_first = state.sign_reserved(&first).unwrap();
        state
            .reserve_select::<Sha256, _>(
                &mut TestRng::new(3101),
                &origin.body,
                legal_row,
                build_policy,
                &Sequential,
            )
            .unwrap();
        let final_vote = state
            .reserve_fast_final::<Sha256, _>(
                &mut TestRng::new(3102),
                &origin,
                legal_row,
                build_policy,
                &Sequential,
            )
            .unwrap();
        let signed_final = state.sign_reserved(&final_vote).unwrap();
        (first, signed_first, final_vote, signed_final)
    });
    let ballot = round(6);
    let leader = Participant::new(f.schemes.len() as u32 - 2);
    state.fence::<Sha256>(ballot, leader).unwrap();
    let old_snapshot = state.snapshot().unwrap().clone();
    if let Some((first, signed_first, final_vote, signed_final)) = pending {
        assert!(state.sign_reserved(&first).is_err());
        assert!(state.sign_reserved(&final_vote).is_err());
        state
            .record_signed::<Sha256, _>(&mut TestRng::new(3103), &first, &signed_first, &Sequential)
            .unwrap();
        state
            .record_signed::<Sha256, _>(
                &mut TestRng::new(3104),
                &final_vote,
                &signed_final,
                &Sequential,
            )
            .unwrap();
    }
    state
        .retain_origin::<Sha256, _>(
            &mut TestRng::new(3105),
            &origin,
            legal_row,
            build_policy,
            &Sequential,
        )
        .unwrap();
    let notice = captured(f, &state, ballot, leader);
    assert_eq!(state.snapshot(), Some(&old_snapshot));
    let g::Kind::Recover(recover) = &notice.message.kind else {
        unreachable!()
    };
    assert_eq!(recover.snapshot.count() as usize, state.records().len());
    assert!(recover.snapshot.count() > old_snapshot.count());
    Transcript {
        core,
        origin,
        ballot,
        leader,
        notice,
        pages: pages(&state),
    }
}

#[derive(Default)]
struct Calls {
    material: Cell<usize>,
    rows: Cell<usize>,
    builds: Cell<usize>,
}
impl Calls {
    const fn counts(&self) -> (usize, usize, usize) {
        (self.material.get(), self.rows.get(), self.builds.get())
    }
}

const fn material<'a>(record: &Record<Digest>, origin: &'a GOrigin) -> Material<'a, S, Digest> {
    match record.action() {
        Action::Reserve {
            message:
                g::Message {
                    kind: g::Kind::Select { .. },
                    ..
                },
            ..
        } => Material::Body(&origin.body),
        _ => Material::Origin(origin),
    }
}

const fn bounds(t: &Transcript) -> history::Bounds {
    history::Bounds {
        pages: t.pages.len() as u32,
        encoded_bytes: u64::MAX,
        material_checks: 3,
    }
}

fn check<'a>(
    f: &Fixture<S>,
    t: &'a Transcript,
    notice: &'a GSigned,
    pages: &'a [HistoryPage<Digest>],
    bounds: history::Bounds,
    supplied: Option<&GOrigin>,
    calls: &Calls,
) -> Result<history::VerifiedHistory<'a, S, Digest>, history::Error> {
    history::verify::<Sha256, _, _, _>(
        &mut TestRng::new(3106),
        &g::VerificationContext::new(f.verifier.clone()),
        &t.core,
        input(),
        t.ballot,
        t.leader,
        entry(),
        notice,
        pages,
        G_LIMITS,
        bounds,
        |record| {
            calls.material.set(calls.material.get() + 1);
            supplied.map_or(Material::None, |origin| material(record, origin))
        },
        |row| {
            calls.rows.set(calls.rows.get() + 1);
            legal_row(row)
        },
        |rows, body| {
            calls.builds.set(calls.builds.get() + 1);
            build_policy(rows, body)
        },
        &Sequential,
    )
}

#[test]
fn public_only_replay_covers_general_rosters_and_current_post_fence_prefix() {
    for n in [4, 7, 8, 10, 13, 16, 64] {
        let f = fixture(n);
        assert!(f.verifier.me().is_none());
        let t = transcript(&f, true);
        let calls = Calls::default();
        let verified = check(
            &f,
            &t,
            &t.notice,
            &t.pages,
            bounds(&t),
            Some(&t.origin),
            &calls,
        )
        .unwrap();
        assert_eq!(verified.owner(), Participant::new(n - 1));
        assert_eq!(verified.core(), &t.core);
        assert_eq!(verified.input(), input());
        assert_eq!(verified.entry(), entry());
        assert!(std::ptr::eq(verified.notice(), &t.notice));
        assert!(std::ptr::eq(verified.pages(), t.pages.as_slice()));
        assert_eq!(verified.records().len(), 7);
        assert_eq!(verified.snapshot().count(), 7);
        assert_eq!(verified.snapshot().head(), Some(t.pages[6].id::<Sha256>()));
        assert_eq!(calls.material.get(), 3);
        assert_eq!(calls.builds.get(), 3);
        assert!(!t.core.followers.contains(&Participant::new(1)));
        assert_eq!(
            t.core.followers.len() + 1,
            g::Committee::new(n as usize).unwrap().quorum()
        );
        let actions: Vec<_> = verified.records().map(Record::action).collect();
        assert!(matches!(actions[1], Action::Reserve { .. }));
        assert!(matches!(actions[3], Action::Fence { .. }));
        assert!(matches!(actions[4], Action::Released { .. }));
        assert!(matches!(actions[5], Action::Released { .. }));
        assert!(matches!(actions[6], Action::RetainOrigin { .. }));
    }
}

#[test]
fn capture_requires_exact_installed_floor_and_completed_replay() {
    let f = fixture(8);
    let core = core(&f);
    let owner = usize::from(core.leader);
    let mut state =
        State::new::<Sha256>(f.schemes[owner].clone(), core.clone(), input(), G_LIMITS).unwrap();
    assert!(
        state
            .capture_history::<Sha256>(round(6), core.leader, entry(), None)
            .is_err()
    );
    state.fence::<Sha256>(round(6), core.leader).unwrap();
    for (ballot, leader) in [
        (round(5), core.leader),
        (round(7), core.leader),
        (round(6), Participant::new(0)),
    ] {
        assert!(
            state
                .capture_history::<Sha256>(ballot, leader, entry(), None)
                .is_err()
        );
    }
    let expected = state
        .capture_history::<Sha256>(round(6), core.leader, entry(), None)
        .unwrap();
    let mut replay =
        State::for_replay::<Sha256>(f.schemes[owner].clone(), core, input(), G_LIMITS).unwrap();
    assert!(
        replay
            .capture_history::<Sha256>(round(6), Participant::new(owner as u32), entry(), None)
            .is_err()
    );
    for record in state.records() {
        replay
            .restore::<Sha256, _>(
                &mut TestRng::new(3107),
                record,
                Material::None,
                legal_row,
                build_policy,
                &Sequential,
            )
            .unwrap();
    }
    assert!(
        replay
            .capture_history::<Sha256>(round(6), Participant::new(owner as u32), entry(), None)
            .is_err()
    );
    replay.finish_replay().unwrap();
    assert_eq!(
        replay
            .capture_history::<Sha256>(round(6), Participant::new(owner as u32), entry(), None)
            .unwrap(),
        expected
    );
}

#[test]
fn outside_core_no_first_and_signed_absence_are_distinct_histories() {
    let f = fixture(8);
    let t = transcript(&f, false);
    for (owner, absent) in [(1usize, false), (7usize, true)] {
        let mut state =
            State::new::<Sha256>(f.schemes[owner].clone(), t.core.clone(), input(), G_LIMITS)
                .unwrap();
        if absent {
            state
                .reserve_first::<Sha256>(None, None, legal_row)
                .unwrap();
        } else {
            state.close_first::<Sha256>().unwrap();
        }
        state.fence::<Sha256>(t.ballot, t.leader).unwrap();
        let notice = captured(&f, &state, t.ballot, t.leader);
        let pages = pages(&state);
        let calls = Calls::default();
        let verified = check(&f, &t, &notice, &pages, bounds(&t), None, &calls).unwrap();
        let first = verified.records().next().unwrap();
        if absent {
            assert!(matches!(
                first.message().unwrap().kind,
                g::Kind::First(g::First {
                    report: None,
                    preference: None,
                    ..
                })
            ));
        } else {
            assert!(matches!(first.action(), Action::NoFirst));
        }
        assert_eq!(calls.material.get(), 0);
    }
}

#[test]
fn static_limits_and_incomplete_pages_fail_before_any_callback() {
    let f = fixture(10);
    let t = transcript(&f, true);
    let static_bytes =
        t.notice.encode_size() + t.pages.iter().map(EncodeSize::encode_size).sum::<usize>();
    for bad in [
        history::Bounds {
            pages: t.pages.len() as u32 - 1,
            ..bounds(&t)
        },
        history::Bounds {
            encoded_bytes: static_bytes as u64 - 1,
            ..bounds(&t)
        },
        history::Bounds {
            material_checks: 2,
            ..bounds(&t)
        },
    ] {
        let calls = Calls::default();
        assert_eq!(
            check(&f, &t, &t.notice, &t.pages, bad, Some(&t.origin), &calls).map(|_| ()),
            Err(history::Error::Limit)
        );
        assert_eq!(calls.counts(), (0, 0, 0));
    }
    let mut variants = vec![t.pages[..t.pages.len() - 1].to_vec(), t.pages[1..].to_vec()];
    let mut reordered = t.pages.clone();
    reordered.swap(0, 1);
    variants.push(reordered);
    let mut duplicated = t.pages.clone();
    duplicated[2] = duplicated[1].clone();
    variants.push(duplicated);
    let mut changed_owner = t.pages.clone();
    let mut bytes = changed_owner[0].encode().to_vec();
    // Outer page/header, None predecessor, record/header, Core and Input.
    let owner = 8 + 1 + 8 + t.core.encode_size() + 32;
    bytes[owner..owner + 4].copy_from_slice(&0u32.to_be_bytes());
    changed_owner[0] = HistoryPage::decode_cfg(Bytes::from(bytes), &G_LIMITS).unwrap();
    variants.push(changed_owner);
    for pages in variants {
        let calls = Calls::default();
        assert!(
            check(
                &f,
                &t,
                &t.notice,
                &pages,
                bounds(&t),
                Some(&t.origin),
                &calls
            )
            .is_err()
        );
        assert_eq!(calls.counts(), (0, 0, 0));
    }
}

#[test]
fn signed_context_owner_and_old_domain_cannot_cross_history_boundary() {
    let f = fixture(8);
    let t = transcript(&f, false);
    for field in 0..4 {
        let mut message = t.notice.message.clone();
        let g::Kind::Recover(recover) = &mut message.kind else {
            unreachable!()
        };
        match field {
            0 => recover.core = Digest::from([121; 32]),
            1 => recover.input = Digest::from([122; 32]),
            2 => recover.entry = Digest::from([123; 32]),
            _ => message.slot = Digest::from([124; 32]),
        }
        // Even freshly signed wrong coordinates are not the caller's context.
        let owner = usize::from(t.core.leader);
        let notice = if field == 3 {
            let mut notice = t.notice.clone();
            notice.message = message;
            notice
        } else {
            g::Signed::sign(&f.schemes[owner], message, G_LIMITS).unwrap()
        };
        let calls = Calls::default();
        assert!(
            check(
                &f,
                &t,
                &notice,
                &t.pages,
                bounds(&t),
                Some(&t.origin),
                &calls
            )
            .is_err()
        );
        assert_eq!(calls.counts(), (0, 0, 0));
    }
    assert!(matches!(
        g::Signed::sign(&f.schemes[0], t.notice.message.clone(), G_LIMITS),
        Err(g::Error::Identity)
    ));
    let old_domain = [
        b"_COMMONWARE_CONSENSUS_G1_SIGNED_V1".as_slice(),
        t.notice.message.encode().as_ref(),
    ]
    .concat();
    let attestation = f.schemes[usize::from(t.core.leader)]
        .sign::<Digest>(Subject::ExtensionAgreement {
            round: t.ballot,
            payload: &old_domain,
        })
        .unwrap();
    let old_domain = GSigned {
        message: t.notice.message.clone(),
        attestation,
    };
    let calls = Calls::default();
    assert_eq!(
        check(
            &f,
            &t,
            &old_domain,
            &t.pages,
            bounds(&t),
            Some(&t.origin),
            &calls
        )
        .map(|_| ()),
        Err(history::Error::Verification(g::Error::Signature))
    );
    assert_eq!(calls.counts(), (0, 0, 0));
    let mut foreign_owner = t.notice.clone();
    foreign_owner.attestation.signer = Participant::new(0);
    assert!(!foreign_owner.verify(&mut TestRng::new(3108), &f.verifier, G_LIMITS, &Sequential));
    let votes = vec![t.notice; g::Committee::new(8).unwrap().quorum()];
    assert!(matches!(
        g::Quorum::from_votes(
            &mut TestRng::new(3109),
            &f.verifier,
            &votes,
            G_LIMITS,
            &Sequential
        ),
        Err(g::Error::Phase)
    ));
}

#[test]
fn missing_wrong_or_oversized_material_never_becomes_absence_or_an_alias() {
    let f = fixture(8);
    let t = transcript(&f, false);
    let calls = Calls::default();
    assert_eq!(
        check(&f, &t, &t.notice, &t.pages, bounds(&t), None, &calls).map(|_| ()),
        Err(history::Error::Material)
    );
    assert_eq!(calls.counts(), (1, 0, 0));

    let mut alias = t.origin.clone();
    let owner = usize::from(alias.body.firsts[0].attestation.signer);
    let g::Kind::First(row) = &mut alias.body.firsts[0].message.kind else {
        unreachable!()
    };
    row.report = Some(Bytes::from_static(b"z"));
    alias.body.firsts[0] = g::Signed::sign(
        &f.schemes[owner],
        alias.body.firsts[0].message.clone(),
        G_LIMITS,
    )
    .unwrap();
    refresh(&f, &mut alias);
    assert_eq!(alias.body.decision, t.origin.body.decision);
    assert_ne!(alias.id::<Sha256>(), t.origin.id::<Sha256>());
    let calls = Calls::default();
    assert!(
        check(
            &f,
            &t,
            &t.notice,
            &t.pages,
            bounds(&t),
            Some(&alias),
            &calls
        )
        .is_err()
    );
    assert_eq!(calls.counts(), (1, 0, 0));

    let mut oversized = t.origin.clone();
    oversized.body.build = Bytes::from(vec![0; G_LIMITS.build_bytes + 1]);
    let calls = Calls::default();
    assert!(
        check(
            &f,
            &t,
            &t.notice,
            &t.pages,
            bounds(&t),
            Some(&oversized),
            &calls
        )
        .is_err()
    );
    assert_eq!(calls.counts(), (1, 0, 0));
}

#[test]
fn aggregate_bytes_charge_each_material_occurrence_before_its_callbacks() {
    let f = fixture(8);
    let t = transcript(&f, true);
    let static_bytes =
        t.notice.encode_size() + t.pages.iter().map(EncodeSize::encode_size).sum::<usize>();
    let material_bytes = t.origin.body.encode_size() + 2 * t.origin.encode_size();
    let exact = history::Bounds {
        encoded_bytes: (static_bytes + material_bytes) as u64,
        ..bounds(&t)
    };
    let calls = Calls::default();
    check(&f, &t, &t.notice, &t.pages, exact, Some(&t.origin), &calls).unwrap();
    assert_eq!(calls.material.get(), 3);
    assert_eq!(calls.builds.get(), 3);
    let calls = Calls::default();
    assert_eq!(
        check(
            &f,
            &t,
            &t.notice,
            &t.pages,
            history::Bounds {
                encoded_bytes: exact.encoded_bytes - 1,
                ..exact
            },
            Some(&t.origin),
            &calls
        )
        .map(|_| ()),
        Err(history::Error::Limit)
    );
    assert_eq!(calls.material.get(), 3);
    // Earlier valid records can call application validators; the final failed
    // occurrence is bounded before its own row/Build callbacks.
    assert_eq!(calls.builds.get(), 2);
}

fn prefix(snapshot: &Snapshot<Digest>, head: Digest, count: u64) -> Snapshot<Digest> {
    let mut bytes = snapshot.encode().to_vec();
    let n = bytes.len();
    assert!(snapshot.head().is_some());
    bytes[n - 40..n - 8].copy_from_slice(head.as_ref());
    bytes[n - 8..].copy_from_slice(&count.to_be_bytes());
    Snapshot::decode(Bytes::from(bytes)).unwrap()
}

#[test]
fn terminal_history_replays_as_data_and_charges_two_artifacts() {
    let f = fixture(8);
    let t = transcript(&f, false);
    let q = g::Committee::new(8).unwrap().quorum();
    let votes: Vec<_> = (0..q)
        .map(|owner| {
            sign(
                &f,
                &t.core,
                owner,
                g::Kind::Phase {
                    phase: g::Phase::FastFinal,
                    decision: t.origin.body.decision.id::<Sha256>(),
                },
            )
        })
        .collect();
    let certificate = g::Quorum::from_votes(
        &mut TestRng::new(3110),
        &f.verifier,
        &votes,
        G_LIMITS,
        &Sequential,
    )
    .unwrap();
    let mut state =
        State::new::<Sha256>(f.schemes[7].clone(), t.core.clone(), input(), G_LIMITS).unwrap();
    state.fence::<Sha256>(t.ballot, t.leader).unwrap();
    let mut notice = captured(&f, &state, t.ballot, t.leader);
    state
        .terminal::<Sha256, _>(
            &mut TestRng::new(3111),
            &t.origin,
            &certificate,
            legal_row,
            build_policy,
            &Sequential,
        )
        .unwrap();
    assert!(
        state
            .capture_history::<Sha256>(t.ballot, t.leader, entry(), None)
            .is_err()
    );
    let pages = pages(&state);
    // A peer can construct signed data directly. This does not grant an honest
    // terminal owner permission to capture/publish another recovery notice.
    let g::Kind::Recover(recover) = &mut notice.message.kind else {
        unreachable!()
    };
    recover.snapshot = prefix(
        &recover.snapshot,
        pages.last().unwrap().id::<Sha256>(),
        pages.len() as u64,
    );
    notice = g::Signed::sign(&f.schemes[7], notice.message, G_LIMITS).unwrap();
    let checks = Cell::new(0);
    let app = Cell::new(0);
    let exact = (notice.encode_size()
        + pages.iter().map(EncodeSize::encode_size).sum::<usize>()
        + t.origin.encode_size()
        + certificate.encode_size()) as u64;
    for (material_checks, encoded_bytes, succeeds) in
        [(1, exact, false), (2, exact - 1, false), (2, exact, true)]
    {
        checks.set(0);
        app.set(0);
        let result = history::verify::<Sha256, _, _, _>(
            &mut TestRng::new(3112),
            &g::VerificationContext::new(f.verifier.clone()),
            &t.core,
            input(),
            t.ballot,
            t.leader,
            entry(),
            &notice,
            &pages,
            G_LIMITS,
            history::Bounds {
                pages: 2,
                encoded_bytes,
                material_checks,
            },
            |_| {
                checks.set(checks.get() + 1);
                Material::Terminal {
                    origin: &t.origin,
                    quorum: &certificate,
                }
            },
            |row| {
                app.set(app.get() + 1);
                legal_row(row)
            },
            build_policy,
            &Sequential,
        );
        assert_eq!(result.is_ok(), succeeds);
        if !succeeds {
            assert_eq!(result.map(|_| ()), Err(history::Error::Limit));
            assert_eq!(app.get(), 0);
        }
        assert_eq!(checks.get(), usize::from(material_checks == 2));
    }
}

#[test]
fn recover_frames_reject_malformed_lengths_versions_truncation_and_trailing_bytes() {
    let f = fixture(8);
    let t = transcript(&f, false);
    let g::Kind::Recover(recover) = &t.notice.message.kind else {
        unreachable!()
    };
    let frames = [
        recover.encode(),
        t.notice.message.encode(),
        t.notice.encode(),
    ];
    for (kind, frame) in frames.into_iter().enumerate() {
        let decode = |bytes: Bytes| match kind {
            0 => history::Recover::<Digest>::decode_cfg(bytes, &G_LIMITS).map(|_| ()),
            1 => g::Message::<Digest>::decode_cfg(bytes, &G_LIMITS).map(|_| ()),
            _ => GSigned::decode_cfg(bytes, &G_LIMITS).map(|_| ()),
        };
        assert!(decode(frame.clone()).is_ok());
        for end in 0..frame.len() {
            assert!(decode(frame.slice(..end)).is_err());
        }
        let mut version = frame.to_vec();
        version[3] = b'2';
        assert!(decode(Bytes::from(version)).is_err());
        let mut huge = frame.to_vec();
        huge[4..8].copy_from_slice(&u32::MAX.to_be_bytes());
        assert!(decode(Bytes::from(huge)).is_err());
        let mut trailing = frame.to_vec();
        trailing.push(0);
        assert!(decode(Bytes::from(trailing)).is_err());
    }
    assert_eq!(
        history::Recover::<Digest>::decode_cfg(recover.encode(), &G_LIMITS).unwrap(),
        *recover
    );
    assert_eq!(
        GSigned::decode_cfg(t.notice.encode(), &G_LIMITS)
            .unwrap()
            .encode(),
        t.notice.encode()
    );
    let mut report = recover.clone();
    report.report = Some(Bytes::from(vec![0; G_LIMITS.report_bytes + 1]));
    assert!(history::Recover::<Digest>::decode_cfg(report.encode(), &G_LIMITS).is_err());
    let mut owner = recover.encode().to_vec();
    // G1N1 header + three digests + nested G1L1 header + Slot digest.
    owner[8 + 96 + 8 + 32..8 + 96 + 8 + 36].copy_from_slice(&64u32.to_be_bytes());
    assert!(history::Recover::<Digest>::decode_cfg(Bytes::from(owner), &G_LIMITS).is_err());
    for page in &t.pages {
        assert_eq!(
            HistoryPage::<Digest>::decode_cfg(page.encode(), &G_LIMITS).unwrap(),
            *page
        );
        for end in 0..page.encode_size() {
            assert!(
                HistoryPage::<Digest>::decode_cfg(page.encode().slice(..end), &G_LIMITS).is_err()
            );
        }
    }
    // A grammar-correct decoded frame still needs trusted context and crypto.
    let mut decoded = GSigned::decode_cfg(t.notice.encode(), &G_LIMITS).unwrap();
    decoded.message.slot = Digest::from([129; 32]);
    let decoded = GSigned::decode_cfg(decoded.encode(), &G_LIMITS).unwrap();
    assert!(!decoded.verify(&mut TestRng::new(3113), &f.verifier, G_LIMITS, &Sequential));
}

struct GeneralHistoryConformance;
impl Conformance for GeneralHistoryConformance {
    async fn commit(seed: u64) -> Vec<u8> {
        let f = ed25519::fixture(
            &mut TestRng::new(seed),
            b"_COMMONWARE_CONSENSUS_G1_HISTORY_CONFORMANCE",
            10,
        );
        let t = transcript(&f, true);
        let g::Kind::Recover(recover) = &t.notice.message.kind else {
            unreachable!()
        };
        let mut encodings = vec![
            recover.encode(),
            recover.snapshot.encode(),
            t.notice.message.encode(),
            t.notice.encode(),
        ];
        encodings.extend(t.pages.iter().map(|p| p.encode()));
        encodings.encode().to_vec()
    }
}
conformance_tests! { GeneralHistoryConformance => 32 }
