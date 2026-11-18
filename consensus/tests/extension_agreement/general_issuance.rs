//! Real-signature and journal-replay checks for inactive G1 issuance.
//!
//! Journal tests exercise the existing storage primitive and issuance replay;
//! they do not establish voter Actor integration or a signer sync barrier.
//! A single live native owner per Slot is a caller prerequisite. Independent
//! fixtures do not prove that duplicate State constructors are prevented.
use super::*;
use commonware_codec::Write as _;
use commonware_consensus::{
    Viewable as _,
    simplex::extension::agreement::{
        general as g,
        general::issuance::{Action, HistoryPage, Material, Record, Snapshot, State},
    },
};
use commonware_cryptography::Hasher as _;
use commonware_runtime::{
    ReadOptions, Runner as _, Supervisor as _, buffer::paged::CacheRef, deterministic,
};
use commonware_storage::journal::segmented::variable::{Config as JournalConfig, Journal};
use commonware_utils::{NZU16, NZUsize};
use std::cell::Cell;

const G_LIMITS: g::Limits = g::Limits {
    report_bytes: 128,
    order_bytes: 128,
    build_bytes: 256,
    material_bytes: 256,
    origin_bytes: g::MAX_EVIDENCE_BYTES,
};
type GOrigin = g::Origin<S, Digest>;
type GSigned = g::Signed<S, Digest>;

fn core(f: &Fixture<S>) -> g::Core<Digest> {
    let committee = g::Committee::new(f.schemes.len()).unwrap();
    g::Core {
        slot: g::Slot {
            profile: Digest::from([70; 32]),
            domain: Digest::from([71; 32]),
            roster: g::Slot::<Digest>::roster::<Sha256, _>(&f.verifier),
            cut: 9,
            proposal: Proposal::new(round(4), View::new(3), Digest::from([72; 32])),
            parent: g::NativeParent::Proposal {
                round: round(3),
                digest: Digest::from([73; 32]),
            },
        },
        leader: Participant::new(0),
        followers: (1..committee.quorum() as u32)
            .map(Participant::new)
            .collect(),
    }
}

fn input() -> Digest {
    Digest::from([74; 32])
}

fn sign(f: &Fixture<S>, owner: usize, kind: g::Kind<Digest>) -> GSigned {
    let core = core(f);
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

fn population(rows: &[GSigned]) -> Digest {
    let mut bytes = Vec::new();
    for row in rows {
        row.write(&mut bytes);
    }
    Sha256::hash(&[&bytes])
}

fn build(rows: &[GSigned]) -> Bytes {
    rows.iter()
        .flat_map(|signed| {
            let g::Kind::First(row) = &signed.message.kind else {
                panic!("FIRST fixture")
            };
            row.report.iter().flat_map(|bytes| bytes.iter().copied())
        })
        .collect()
}

fn legal_row(row: &g::First<Digest>) -> bool {
    row.report.as_ref().is_none_or(|bytes| bytes.len() == 1)
        && row
            .preference
            .as_ref()
            .is_none_or(|bytes| bytes.as_ref() == b"AB" || bytes.as_ref() == b"BA")
}

// This policy is a two-block application fixture, not the SDK Build adapter.
fn build_policy(rows: &g::VerifiedRows<S, Digest>, body: &g::OriginBody<S, Digest>) -> bool {
    let expected = if build(rows.originals()).contains(&u8::MAX) {
        b"BA"
    } else {
        b"AB"
    };
    body.decision.order.as_ref() == expected
        && body.population == population(rows.originals())
        && body.build == build(rows.originals())
        && body.material.is_empty()
}

fn refresh(f: &Fixture<S>, origin: &mut GOrigin) {
    origin.body.population = population(&origin.body.firsts);
    origin.body.build = build(&origin.body.firsts);
    origin.selection = sign(
        f,
        0,
        g::Kind::Select {
            body: origin.body.id::<Sha256>(),
            decision: origin.body.decision.id::<Sha256>(),
        },
    );
}

fn origin(f: &Fixture<S>) -> GOrigin {
    let core = core(f);
    let firsts: Vec<_> = (0..=core.followers.len())
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
        .collect();
    let body = g::OriginBody {
        decision: g::Decision {
            slot: core.slot.clone(),
            input: input(),
            order: Bytes::from_static(b"AB"),
        },
        core,
        population: population(&firsts),
        build: build(&firsts),
        firsts,
        material: Bytes::new(),
    };
    let selection = sign(
        f,
        0,
        g::Kind::Select {
            body: body.id::<Sha256>(),
            decision: body.decision.id::<Sha256>(),
        },
    );
    g::Origin { body, selection }
}

fn alias(f: &Fixture<S>, original: &GOrigin) -> GOrigin {
    let mut alias = original.clone();
    let g::Kind::First(row) = &mut alias.body.firsts[2].message.kind else {
        unreachable!()
    };
    row.report = Some(Bytes::from_static(b"z"));
    alias.body.firsts[2] = g::Signed::sign(
        &f.schemes[2],
        alias.body.firsts[2].message.clone(),
        G_LIMITS,
    )
    .unwrap();
    refresh(f, &mut alias);
    alias
}

fn fork(f: &Fixture<S>, original: &GOrigin) -> GOrigin {
    let mut fork = original.clone();
    for (owner, signed) in fork.body.firsts.iter_mut().enumerate().skip(1) {
        let g::Kind::First(row) = &mut signed.message.kind else {
            unreachable!()
        };
        if owner == 1 {
            row.report = Some(Bytes::from_static(b"\xff"));
        }
        row.preference = Some(Bytes::from_static(b"BA"));
        *signed = g::Signed::sign(&f.schemes[owner], signed.message.clone(), G_LIMITS).unwrap();
    }
    fork.body.decision.order = Bytes::from_static(b"BA");
    refresh(f, &mut fork);
    fork
}

fn checked(f: &Fixture<S>, origin: &GOrigin) -> g::VerifiedOrigin<Digest> {
    origin
        .verify::<Sha256, _>(
            &mut TestRng::new(2101),
            &f.verifier,
            &core(f),
            input(),
            G_LIMITS,
            legal_row,
            build_policy,
            &Sequential,
        )
        .unwrap()
}

fn local(f: &Fixture<S>, owner: usize) -> State<S, Digest> {
    State::new::<Sha256>(f.schemes[owner].clone(), core(f), input(), G_LIMITS).unwrap()
}

fn replaying(f: &Fixture<S>, owner: usize) -> State<S, Digest> {
    State::for_replay::<Sha256>(f.schemes[owner].clone(), core(f), input(), G_LIMITS).unwrap()
}

fn restore(
    state: &mut State<S, Digest>,
    record: &Record<Digest>,
    material: Material<'_, S, Digest>,
) -> Result<(), g::issuance::Error> {
    state.restore::<Sha256, _>(
        &mut TestRng::new(2117),
        record,
        material,
        legal_row,
        build_policy,
        &Sequential,
    )
}

fn reserve_final(state: &mut State<S, Digest>, origin: &GOrigin) -> Record<Digest> {
    state
        .reserve_fast_final::<Sha256, _>(
            &mut TestRng::new(2118),
            origin,
            legal_row,
            build_policy,
            &Sequential,
        )
        .unwrap()
}

fn phase_quorum(
    f: &Fixture<S>,
    origin: &GOrigin,
    phase: g::Phase,
    count: usize,
) -> g::Quorum<S, Digest> {
    let votes: Vec<_> = (0..count)
        .map(|owner| {
            sign(
                f,
                owner,
                g::Kind::Phase {
                    phase,
                    decision: origin.body.decision.id::<Sha256>(),
                },
            )
        })
        .collect();
    g::Quorum::from_votes(
        &mut TestRng::new(2119),
        &f.verifier,
        &votes,
        G_LIMITS,
        &Sequential,
    )
    .unwrap()
}

#[test]
fn first_reservation_is_once_per_owner_in_general_committees() {
    for n in [4, 7, 8, 10, 13, 64] {
        let f = fixture(n);
        let mut state = local(&f, 1);
        let report = Some(Bytes::from_static(b"r"));
        let preference = Some(Bytes::from_static(b"AB"));
        let record = state
            .reserve_first::<Sha256>(report.clone(), preference.clone(), legal_row)
            .unwrap();
        assert_eq!(
            state
                .reserve_first::<Sha256>(report.clone(), preference.clone(), legal_row)
                .unwrap(),
            record
        );
        assert!(
            state
                .reserve_first::<Sha256>(Some(Bytes::from_static(b"s")), preference, legal_row)
                .is_err()
        );
        assert!(
            state
                .reserve_first::<Sha256>(report, Some(Bytes::from_static(b"BA")), legal_row)
                .is_err()
        );
        let signed = state.sign_reserved(&record).unwrap();
        assert_eq!(signed.attestation.signer, Participant::new(1));
        assert!(signed.verify(&mut TestRng::new(2102), &f.verifier, G_LIMITS, &Sequential));
        let g::Kind::First(row) = signed.message.kind else {
            unreachable!()
        };
        assert_eq!(row.owner, Participant::new(1));
        assert_eq!(row.report, Some(Bytes::from_static(b"r")));
        assert_eq!(row.preference, Some(Bytes::from_static(b"AB")));
        assert_eq!(state.records(), &[record]);
    }
}

#[test]
fn explicit_no_first_is_not_an_absent_report_or_signable_message() {
    for n in [4, 7, 8, 10, 13, 64] {
        let f = fixture(n);
        let mut state = local(&f, (n - 1) as usize);
        let closed = state.close_first::<Sha256>().unwrap();
        assert!(matches!(closed.action(), Action::NoFirst));
        assert_eq!(state.close_first::<Sha256>().unwrap(), closed);
        assert!(state.sign_reserved(&closed).is_err());
        assert!(
            state
                .reserve_first::<Sha256>(None, None, legal_row)
                .is_err()
        );
        assert!(
            state
                .reserve_first::<Sha256>(Some(Bytes::from_static(b"r")), None, legal_row)
                .is_err()
        );
        assert_eq!(state.records(), std::slice::from_ref(&closed));

        let mut absent = local(&f, 1);
        assert!(absent.close_first::<Sha256>().is_err());
        let first = absent
            .reserve_first::<Sha256>(None, None, legal_row)
            .unwrap();
        assert_ne!(first, closed);
        let signed = absent.sign_reserved(&first).unwrap();
        assert!(signed.verify(&mut TestRng::new(2103), &f.verifier, G_LIMITS, &Sequential));
        let g::Kind::First(row) = signed.message.kind else {
            unreachable!()
        };
        assert!(row.report.is_none());
        assert!(row.preference.is_none());
    }
}

#[test]
fn select_and_final_keep_their_exact_first_authority_for_same_decision_aliases() {
    for n in [4, 7, 8, 10, 13, 64] {
        let f = fixture(n);
        let original = origin(&f);
        let alias = alias(&f, &original);
        let fork = fork(&f, &original);
        assert_eq!(
            checked(&f, &original).decision(),
            checked(&f, &alias).decision()
        );
        assert_ne!(
            checked(&f, &original).origin(),
            checked(&f, &alias).origin()
        );
        assert_ne!(
            checked(&f, &original).decision(),
            checked(&f, &fork).decision()
        );

        let mut leader = local(&f, 0);
        leader
            .reserve_first::<Sha256>(None, None, legal_row)
            .unwrap();
        let selection = leader
            .reserve_select::<Sha256, _>(
                &mut TestRng::new(2104),
                &original.body,
                legal_row,
                build_policy,
                &Sequential,
            )
            .unwrap();
        assert_eq!(
            leader
                .reserve_select::<Sha256, _>(
                    &mut TestRng::new(2105),
                    &alias.body,
                    legal_row,
                    build_policy,
                    &Sequential,
                )
                .unwrap(),
            selection
        );
        assert!(
            leader
                .reserve_select::<Sha256, _>(
                    &mut TestRng::new(2106),
                    &fork.body,
                    legal_row,
                    build_policy,
                    &Sequential,
                )
                .is_err()
        );
        let selected = leader.sign_reserved(&selection).unwrap();
        assert_eq!(selected.message, original.selection.message);
        assert!(selected.verify(&mut TestRng::new(2107), &f.verifier, G_LIMITS, &Sequential));

        // This signer is outside Core, so aliases do not imply an own FIRST fork.
        let mut voter = local(&f, (n - 1) as usize);
        let final_choice = voter
            .reserve_fast_final::<Sha256, _>(
                &mut TestRng::new(2108),
                &original,
                legal_row,
                build_policy,
                &Sequential,
            )
            .unwrap();
        assert_eq!(
            voter
                .reserve_fast_final::<Sha256, _>(
                    &mut TestRng::new(2109),
                    &alias,
                    legal_row,
                    build_policy,
                    &Sequential,
                )
                .unwrap(),
            final_choice
        );
        assert!(
            voter
                .reserve_fast_final::<Sha256, _>(
                    &mut TestRng::new(2110),
                    &fork,
                    legal_row,
                    build_policy,
                    &Sequential,
                )
                .is_err()
        );
        let signed = voter.sign_reserved(&final_choice).unwrap();
        assert_eq!(signed.attestation.signer, Participant::new(n - 1));
        assert!(signed.verify(&mut TestRng::new(2111), &f.verifier, G_LIMITS, &Sequential));
        assert!(matches!(
            signed.message.kind,
            g::Kind::Phase { phase: g::Phase::FastFinal, decision }
                if decision == original.body.decision.id::<Sha256>()
        ));
        assert_eq!(voter.records(), &[final_choice]);
    }
}

#[test]
fn received_origin_cannot_reconstruct_missing_or_conflicting_own_first_and_select() {
    for n in [4, 7, 8, 10, 13, 64] {
        let f = fixture(n);
        let original = origin(&f);
        let mut follower = local(&f, 1);
        assert!(
            follower
                .reserve_fast_final::<Sha256, _>(
                    &mut TestRng::new(2112),
                    &original,
                    legal_row,
                    build_policy,
                    &Sequential,
                )
                .is_err()
        );
        follower
            .reserve_first::<Sha256>(
                Some(Bytes::from_static(b"x")),
                Some(Bytes::from_static(b"AB")),
                legal_row,
            )
            .unwrap();
        assert!(
            follower
                .reserve_fast_final::<Sha256, _>(
                    &mut TestRng::new(2113),
                    &original,
                    legal_row,
                    build_policy,
                    &Sequential,
                )
                .is_err()
        );
        assert_eq!(follower.records().len(), 1);

        let mut leader = local(&f, 0);
        leader
            .reserve_first::<Sha256>(None, None, legal_row)
            .unwrap();
        assert!(
            leader
                .reserve_fast_final::<Sha256, _>(
                    &mut TestRng::new(2114),
                    &original,
                    legal_row,
                    build_policy,
                    &Sequential,
                )
                .is_err()
        );
        let selection = leader
            .reserve_select::<Sha256, _>(
                &mut TestRng::new(2115),
                &original.body,
                legal_row,
                build_policy,
                &Sequential,
            )
            .unwrap();
        assert_eq!(
            leader.sign_reserved(&selection).unwrap().message,
            original.selection.message
        );
        assert!(
            leader
                .reserve_fast_final::<Sha256, _>(
                    &mut TestRng::new(2116),
                    &original,
                    legal_row,
                    build_policy,
                    &Sequential,
                )
                .is_ok()
        );
    }
}

#[test]
fn replay_reverifies_exact_authority_and_cannot_replace_it_with_a_same_decision_alias() {
    for n in [4, 7, 8, 10, 13, 64] {
        let f = fixture(n);
        let original = origin(&f);
        let alias = alias(&f, &original);
        let owner = (n - 1) as usize;
        let mut state = local(&f, owner);
        let choice = reserve_final(&mut state, &original);
        assert_eq!(choice.authority(), Some(original.id::<Sha256>()));

        let mut replay = replaying(&f, owner);
        assert!(replay.sign_reserved(&choice).is_err());
        assert!(restore(&mut replay, &choice, Material::None).is_err());
        assert!(restore(&mut replay, &choice, Material::Origin(&alias)).is_err());
        assert!(replay.records().is_empty());
        restore(&mut replay, &choice, Material::Origin(&original)).unwrap();
        assert!(replay.sign_reserved(&choice).is_err());
        replay.finish_replay().unwrap();
        assert_eq!(replay.records(), std::slice::from_ref(&choice));
        assert_eq!(reserve_final(&mut replay, &alias), choice);
        assert_eq!(replay.records(), std::slice::from_ref(&choice));
        assert!(replay.outbox(&choice).is_none());
        let signed = replay.sign_reserved(&choice).unwrap();
        assert!(signed.verify(&mut TestRng::new(2120), &f.verifier, G_LIMITS, &Sequential));

        let foreign = ed25519::fixture(
            &mut TestRng::new(2121),
            b"_COMMONWARE_CONSENSUS_G1_ISSUANCE_FOREIGN_TEST",
            n,
        );
        let mut wrong_roster = replaying(&foreign, owner);
        assert!(restore(&mut wrong_roster, &choice, Material::Origin(&original)).is_err());
        assert!(wrong_roster.records().is_empty());
    }
}

#[test]
fn local_fence_freezes_all_unsigned_choices_without_inventing_a_certificate() {
    for n in [4, 7, 8, 10, 13, 64] {
        let f = fixture(n);
        let original = origin(&f);
        let mut state = local(&f, 0);
        let first = state
            .reserve_first::<Sha256>(None, None, legal_row)
            .unwrap();
        let selection = state
            .reserve_select::<Sha256, _>(
                &mut TestRng::new(2122),
                &original.body,
                legal_row,
                build_policy,
                &Sequential,
            )
            .unwrap();
        let final_choice = reserve_final(&mut state, &original);
        let prior = state.records().to_vec();
        let fence = state
            .fence::<Sha256>(round(5), Participant::new(1))
            .unwrap();
        let frozen = state.snapshot().unwrap().clone();
        assert_eq!(frozen.ballot(), round(5));
        assert_eq!(frozen.leader(), Participant::new(1));
        assert_eq!(frozen.count(), prior.len() as u64);
        let mut head = None;
        for (index, record) in prior.iter().enumerate() {
            let page = state.history_page(index).unwrap();
            assert_eq!(page.record(), record);
            assert_eq!(page.previous(), head);
            head = Some(page.id::<Sha256>());
            assert!(state.outbox(record).is_none());
        }
        assert_eq!(frozen.head(), head);
        assert_eq!(
            state
                .fence::<Sha256>(round(5), Participant::new(1))
                .unwrap(),
            fence
        );
        assert!(
            state
                .fence::<Sha256>(round(5), Participant::new(2))
                .is_err()
        );
        assert_eq!(state.snapshot(), Some(&frozen));
        for record in [&first, &selection, &final_choice, &fence] {
            assert!(state.sign_reserved(record).is_err());
        }
        assert_eq!(state.floor(), round(5));
        assert_eq!(state.records().len(), prior.len() + 1);
        // A local fence is only revocation: it does not create a recovery vote.
        assert!(fence.message().is_none());
    }
}

#[test]
fn synced_native_journal_reopens_unsigned_choices_and_preserves_the_signing_floor() {
    for n in [4, 7, 8, 10, 13, 64] {
        for with_fence in [false, true] {
            let f = fixture(n);
            let original = origin(&f);
            let mut state = local(&f, 0);
            state
                .reserve_first::<Sha256>(None, None, legal_row)
                .unwrap();
            state
                .reserve_select::<Sha256, _>(
                    &mut TestRng::new(2123),
                    &original.body,
                    legal_row,
                    build_policy,
                    &Sequential,
                )
                .unwrap();
            let final_choice = reserve_final(&mut state, &original);
            if with_fence {
                state
                    .fence::<Sha256>(round(5), Participant::new(1))
                    .unwrap();
            }
            let records = state.records().to_vec();
            let written = records.clone();
            let (_, checkpoint) =
                deterministic::Runner::seeded(2124).start_and_recover(move |context| async move {
                    let mut journal = Journal::<_, Record<Digest>>::init(
                        context.child("g1_wal"),
                        JournalConfig {
                            partition: "g1-issuance-replay".into(),
                            compression: None,
                            codec_config: G_LIMITS,
                            page_cache: CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(8)),
                            write_buffer: NZUsize!(1024),
                        },
                    )
                    .await
                    .unwrap();
                    for record in written {
                        journal = journal
                            .append(record.view().get(), &record)
                            .await
                            .unwrap()
                            .0;
                        journal = journal.sync(record.view().get()).await.unwrap();
                    }
                    // No signature was produced before this interruption.
                });
            deterministic::Runner::from(checkpoint).start(move |context| async move {
                let journal = Journal::<_, Record<Digest>>::init(
                    context.child("g1_wal"),
                    JournalConfig {
                        partition: "g1-issuance-replay".into(),
                        compression: None,
                        codec_config: G_LIMITS,
                        page_cache: CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(8)),
                        write_buffer: NZUsize!(1024),
                    },
                )
                .await
                .unwrap();
                let mut stream = journal
                    .replay(0, 0, NZUsize!(1024), ReadOptions::DONT_CACHE)
                    .await
                    .unwrap();
                let mut replay = replaying(&f, 0);
                assert!(replay.sign_reserved(&final_choice).is_err());
                let mut count = 0;
                while let Some(row) = stream.next().await {
                    let record = row.unwrap().3;
                    let material = match record.message().map(|message| &message.kind) {
                        Some(g::Kind::Select { .. }) => Material::Body(&original.body),
                        Some(g::Kind::Phase { .. }) => Material::Origin(&original),
                        _ => Material::None,
                    };
                    restore(&mut replay, &record, material).unwrap();
                    assert!(replay.sign_reserved(&final_choice).is_err());
                    count += 1;
                }
                drop(stream.finish().unwrap());
                replay.finish_replay().unwrap();
                assert_eq!(count, records.len());
                assert_eq!(replay.records(), records.as_slice());
                assert!(replay.outbox(&final_choice).is_none());
                if with_fence {
                    assert_eq!(replay.floor(), round(5));
                    assert!(replay.sign_reserved(&final_choice).is_err());
                } else {
                    let signed = replay.sign_reserved(&final_choice).unwrap();
                    assert!(signed.verify(
                        &mut TestRng::new(2125),
                        &f.verifier,
                        G_LIMITS,
                        &Sequential
                    ));
                }
            });
        }
    }
}

#[test]
fn released_outbox_keeps_exact_bytes_and_rejects_valid_but_unreserved_signatures() {
    for n in [4, 7, 8, 10, 13, 64] {
        let f = fixture(n);
        let original = origin(&f);
        let owner = (n - 1) as usize;
        let mut state = local(&f, owner);
        let choice = reserve_final(&mut state, &original);
        let signed = state.sign_reserved(&choice).unwrap();
        let mut other_round = signed.message.clone();
        other_round.round = round(5);
        other_round.leader = Participant::new(1);
        let wrong_round = g::Signed::sign(&f.schemes[owner], other_round, G_LIMITS).unwrap();
        let wrong_owner = g::Signed::sign(&f.schemes[0], signed.message.clone(), G_LIMITS).unwrap();
        for bad in [wrong_round, wrong_owner] {
            assert!(bad.verify(&mut TestRng::new(2126), &f.verifier, G_LIMITS, &Sequential));
            assert!(
                state
                    .record_signed::<Sha256, _>(
                        &mut TestRng::new(2127),
                        &choice,
                        &bad,
                        &Sequential,
                    )
                    .is_err()
            );
            assert_eq!(state.records(), std::slice::from_ref(&choice));
            assert!(state.outbox(&choice).is_none());
        }
        let released = state
            .record_signed::<Sha256, _>(&mut TestRng::new(2128), &choice, &signed, &Sequential)
            .unwrap();
        let frame = signed.encode();
        assert_eq!(state.outbox(&choice), Some(&frame));
        let fence = state
            .fence::<Sha256>(round(5), Participant::new(1))
            .unwrap();
        assert!(state.sign_reserved(&choice).is_err());
        assert_eq!(state.outbox(&choice), Some(&frame));

        let mut replay = replaying(&f, owner);
        restore(&mut replay, &choice, Material::Origin(&original)).unwrap();
        restore(&mut replay, &released, Material::None).unwrap();
        restore(&mut replay, &fence, Material::None).unwrap();
        replay.finish_replay().unwrap();
        assert!(replay.sign_reserved(&choice).is_err());
        assert_eq!(replay.outbox(&choice), Some(&frame));
        assert_eq!(replay.records(), state.records());
    }
}

#[test]
fn a_local_empty_fence_is_not_a_missing_first_proof_or_recovery_vote() {
    let f = fixture(10);
    let mut state = local(&f, 9);
    let fence = state
        .fence::<Sha256>(round(5), Participant::new(1))
        .unwrap();
    let snapshot = state.snapshot().unwrap();
    assert_eq!(snapshot.count(), 0);
    assert!(snapshot.head().is_none());
    assert!(fence.message().is_none());
    assert!(fence.authority().is_none());
    assert!(state.sign_reserved(&fence).is_err());
    assert!(matches!(fence.action(), Action::Fence { .. }));
    assert_eq!(state.records(), &[fence]);
}

#[test]
fn out_of_range_history_pages_return_none_without_panicking() {
    let f = fixture(10);
    let mut state = local(&f, 9);
    for index in [0, 1, usize::MAX] {
        assert!(state.history_page(index).is_none());
    }
    state.close_first::<Sha256>().unwrap();
    assert!(state.history_page(0).is_some());
    for index in [1, 2, usize::MAX] {
        assert!(state.history_page(index).is_none());
    }
}

#[test]
fn later_outbox_receipt_does_not_rewrite_the_frozen_unsigned_prefix() {
    let f = fixture(10);
    let original = origin(&f);
    let mut state = local(&f, 9);
    let choice = reserve_final(&mut state, &original);
    let signed_before_fence = state.sign_reserved(&choice).unwrap();
    let fence = state
        .fence::<Sha256>(round(5), Participant::new(1))
        .unwrap();
    let frozen = state.snapshot().unwrap().clone();
    assert_eq!(frozen.count(), 1);
    assert!(state.outbox(&choice).is_none());
    assert!(state.sign_reserved(&choice).is_err());
    state
        .record_signed::<Sha256, _>(
            &mut TestRng::new(2134),
            &choice,
            &signed_before_fence,
            &Sequential,
        )
        .unwrap();
    assert_eq!(state.snapshot(), Some(&frozen));
    assert_eq!(
        state
            .fence::<Sha256>(round(5), Participant::new(1))
            .unwrap(),
        fence
    );
    assert_eq!(state.outbox(&choice), Some(&signed_before_fence.encode()));
    assert_eq!(state.records().len(), 3);
}

#[test]
fn frozen_snapshot_replay_rejects_an_omitted_unsigned_choice_or_changed_count() {
    let f = fixture(10);
    let original = origin(&f);
    let mut state = local(&f, 0);
    let first = state
        .reserve_first::<Sha256>(None, None, legal_row)
        .unwrap();
    let selection = state
        .reserve_select::<Sha256, _>(
            &mut TestRng::new(2135),
            &original.body,
            legal_row,
            build_policy,
            &Sequential,
        )
        .unwrap();
    let final_choice = reserve_final(&mut state, &original);
    let fence = state
        .fence::<Sha256>(round(5), Participant::new(1))
        .unwrap();
    let mut replay = replaying(&f, 0);
    restore(&mut replay, &first, Material::None).unwrap();
    restore(&mut replay, &selection, Material::Body(&original.body)).unwrap();
    assert!(restore(&mut replay, &fence, Material::None).is_err());
    assert_eq!(replay.records(), &[first, selection]);
    restore(&mut replay, &final_choice, Material::Origin(&original)).unwrap();
    let mut changed_count = fence.encode().to_vec();
    let count_offset = changed_count.len() - 8;
    changed_count[count_offset..].copy_from_slice(&4u64.to_be_bytes());
    let changed_count = Record::<Digest>::decode_cfg(changed_count, &G_LIMITS).unwrap();
    assert!(restore(&mut replay, &changed_count, Material::None).is_err());
    assert_eq!(replay.records().len(), 3);
    restore(&mut replay, &fence, Material::None).unwrap();
    replay.finish_replay().unwrap();
    assert!(replay.sign_reserved(&final_choice).is_err());
}

#[test]
fn terminal_requires_a_genuine_fast_quorum_and_survives_exact_material_replay() {
    for n in [4, 7, 8, 10, 13, 64] {
        let f = fixture(n);
        let original = origin(&f);
        let alias = alias(&f, &original);
        let q = g::Committee::new(n as usize).unwrap().quorum();
        let fast = phase_quorum(&f, &original, g::Phase::FastFinal, q);
        let prepared = phase_quorum(&f, &original, g::Phase::Prepare, q);
        let mut short = fast.clone();
        short.certificate.signers = commonware_cryptography::certificate::Signers::try_from((
            f.verifier.participants(),
            (0..q - 1)
                .map(|owner| Participant::new(owner as u32))
                .collect::<Vec<_>>(),
        ))
        .unwrap();
        short.certificate.signatures.truncate(q - 1);
        assert!(!short.verify(&mut TestRng::new(2140), &f.verifier, G_LIMITS, &Sequential));
        let mut state = local(&f, (n - 1) as usize);
        let choice = reserve_final(&mut state, &original);
        for bad in [&prepared, &short] {
            assert!(
                state
                    .terminal::<Sha256, _>(
                        &mut TestRng::new(2129),
                        &original,
                        bad,
                        legal_row,
                        build_policy,
                        &Sequential,
                    )
                    .is_err()
            );
        }
        assert_eq!(state.records(), std::slice::from_ref(&choice));
        let terminal = state
            .terminal::<Sha256, _>(
                &mut TestRng::new(2130),
                &original,
                &fast,
                legal_row,
                build_policy,
                &Sequential,
            )
            .unwrap();
        assert!(matches!(terminal.action(), Action::Terminal { .. }));
        assert!(state.sign_reserved(&choice).is_err());
        assert!(state.sign_reserved(&terminal).is_err());
        assert!(
            state
                .fence::<Sha256>(round(5), Participant::new(1))
                .is_err()
        );

        let mut replay = replaying(&f, (n - 1) as usize);
        restore(&mut replay, &choice, Material::Origin(&original)).unwrap();
        assert!(restore(&mut replay, &terminal, Material::None).is_err());
        assert!(
            restore(
                &mut replay,
                &terminal,
                Material::Terminal {
                    origin: &alias,
                    quorum: &fast
                },
            )
            .is_err()
        );
        assert_eq!(replay.records(), std::slice::from_ref(&choice));
        restore(
            &mut replay,
            &terminal,
            Material::Terminal {
                origin: &original,
                quorum: &fast,
            },
        )
        .unwrap();
        replay.finish_replay().unwrap();
        assert!(replay.sign_reserved(&choice).is_err());
        assert_eq!(replay.records(), state.records());
    }
}

fn codec_corpus(f: &Fixture<S>) -> (Vec<Record<Digest>>, Vec<HistoryPage<Digest>>) {
    let original = origin(f);
    let mut state = local(f, 0);
    state
        .retain_origin::<Sha256, _>(
            &mut TestRng::new(2136),
            &original,
            legal_row,
            build_policy,
            &Sequential,
        )
        .unwrap();
    state
        .reserve_first::<Sha256>(None, None, legal_row)
        .unwrap();
    state
        .reserve_select::<Sha256, _>(
            &mut TestRng::new(2131),
            &original.body,
            legal_row,
            build_policy,
            &Sequential,
        )
        .unwrap();
    let choice = reserve_final(&mut state, &original);
    let signed = state.sign_reserved(&choice).unwrap();
    state
        .record_signed::<Sha256, _>(&mut TestRng::new(2132), &choice, &signed, &Sequential)
        .unwrap();
    state
        .fence::<Sha256>(round(5), Participant::new(1))
        .unwrap();
    let quorum = phase_quorum(
        f,
        &original,
        g::Phase::FastFinal,
        g::Committee::new(f.schemes.len()).unwrap().quorum(),
    );
    state
        .terminal::<Sha256, _>(
            &mut TestRng::new(2133),
            &original,
            &quorum,
            legal_row,
            build_policy,
            &Sequential,
        )
        .unwrap();
    let mut records = state.records().to_vec();
    let mut pages: Vec<_> = (0..records.len())
        .map(|index| state.history_page(index).unwrap())
        .collect();
    let mut outside = local(f, f.schemes.len() - 1);
    let closed = outside.close_first::<Sha256>().unwrap();
    assert!(matches!(closed.action(), Action::NoFirst));
    records.push(closed);
    pages.push(outside.history_page(0).unwrap());
    (records, pages)
}

#[test]
fn positive_origins_without_own_votes_keep_both_aliases_and_require_exact_replay_material() {
    for n in [4, 7, 8, 10, 13, 64] {
        let f = fixture(n);
        let original = origin(&f);
        let alias = alias(&f, &original);
        let mut state = local(&f, 1);
        let retained = state
            .retain_origin::<Sha256, _>(
                &mut TestRng::new(2137),
                &original,
                legal_row,
                build_policy,
                &Sequential,
            )
            .unwrap();
        assert!(matches!(retained.action(), Action::RetainOrigin { .. }));
        assert!(retained.message().is_none());
        assert!(state.sign_reserved(&retained).is_err());
        assert!(
            state
                .reserve_fast_final::<Sha256, _>(
                    &mut TestRng::new(2138),
                    &original,
                    legal_row,
                    build_policy,
                    &Sequential,
                )
                .is_err()
        );
        assert_eq!(state.records(), std::slice::from_ref(&retained));
        assert_eq!(
            state
                .retain_origin::<Sha256, _>(
                    &mut TestRng::new(2139),
                    &original,
                    legal_row,
                    build_policy,
                    &Sequential,
                )
                .unwrap(),
            retained
        );
        let other = state
            .retain_origin::<Sha256, _>(
                &mut TestRng::new(2141),
                &alias,
                legal_row,
                build_policy,
                &Sequential,
            )
            .unwrap();
        assert_ne!(retained, other);
        let fence = state
            .fence::<Sha256>(round(5), Participant::new(1))
            .unwrap();
        assert_eq!(state.snapshot().unwrap().count(), 2);
        assert_eq!(state.history_page(0).unwrap().record(), &retained);
        assert_eq!(state.history_page(1).unwrap().record(), &other);

        let mut replay = replaying(&f, 1);
        assert!(restore(&mut replay, &retained, Material::None).is_err());
        assert!(restore(&mut replay, &retained, Material::Origin(&alias)).is_err());
        assert!(replay.records().is_empty());
        restore(&mut replay, &retained, Material::Origin(&original)).unwrap();
        restore(&mut replay, &other, Material::Origin(&alias)).unwrap();
        restore(&mut replay, &fence, Material::None).unwrap();
        replay.finish_replay().unwrap();
        assert_eq!(replay.records(), state.records());
        assert!(replay.sign_reserved(&retained).is_err());
        assert!(replay.outbox(&retained).is_none());
    }
}

#[test]
fn records_and_history_pages_reject_truncation_trailing_version_and_field_bounds() {
    let f = fixture(10);
    let (records, pages) = codec_corpus(&f);
    for record in records {
        let bytes = record.encode();
        assert_eq!(record.encode_size(), bytes.len());
        let decoded = Record::<Digest>::decode_cfg(bytes.clone(), &G_LIMITS).unwrap();
        assert_eq!(decoded, record);
        assert_eq!(decoded.id::<Sha256>(), record.id::<Sha256>());
        for end in 0..bytes.len() {
            assert!(Record::<Digest>::decode_cfg(bytes.slice(..end), &G_LIMITS).is_err());
        }
        let mut trailing = bytes.to_vec();
        trailing.push(0);
        assert!(Record::<Digest>::decode_cfg(trailing, &G_LIMITS).is_err());
        let mut version = bytes.to_vec();
        version[3] = b'9';
        assert!(Record::<Digest>::decode_cfg(version, &G_LIMITS).is_err());
        let mut huge = bytes.to_vec();
        huge[4..8].copy_from_slice(&u32::MAX.to_be_bytes());
        assert!(Record::<Digest>::decode_cfg(huge, &G_LIMITS).is_err());
        let mut action = bytes.to_vec();
        let action_offset = 8 + record.core().encode_size() + 32 + 4;
        action[action_offset] = 255;
        assert!(Record::<Digest>::decode_cfg(action, &G_LIMITS).is_err());
    }
    for page in pages {
        let bytes = page.encode();
        assert_eq!(page.encode_size(), bytes.len());
        let decoded = HistoryPage::<Digest>::decode_cfg(bytes.clone(), &G_LIMITS).unwrap();
        assert_eq!(decoded.record(), page.record());
        assert_eq!(decoded.previous(), page.previous());
        assert_eq!(decoded.id::<Sha256>(), page.id::<Sha256>());
        for end in 0..bytes.len() {
            assert!(HistoryPage::<Digest>::decode_cfg(bytes.slice(..end), &G_LIMITS).is_err());
        }
        let mut trailing = bytes.to_vec();
        trailing.push(0);
        assert!(HistoryPage::<Digest>::decode_cfg(trailing, &G_LIMITS).is_err());
        let mut version = bytes.to_vec();
        version[3] = b'9';
        assert!(HistoryPage::<Digest>::decode_cfg(version, &G_LIMITS).is_err());
        let mut huge = bytes.to_vec();
        huge[4..8].copy_from_slice(&u32::MAX.to_be_bytes());
        assert!(HistoryPage::<Digest>::decode_cfg(huge, &G_LIMITS).is_err());
    }

    let mut follower = local(&f, 1);
    let report = follower
        .reserve_first::<Sha256>(
            Some(Bytes::from_static(b"r")),
            Some(Bytes::from_static(b"AB")),
            legal_row,
        )
        .unwrap();
    let page = follower.history_page(0).unwrap();
    let mut limited = G_LIMITS;
    limited.report_bytes = 0;
    assert!(Record::<Digest>::decode_cfg(report.encode(), &limited).is_err());
    assert!(HistoryPage::<Digest>::decode_cfg(page.encode(), &limited).is_err());
    // Domains are encoded separately even when their remaining fields match.
    assert!(Record::<Digest>::decode_cfg(page.encode(), &G_LIMITS).is_err());
    assert!(HistoryPage::<Digest>::decode_cfg(report.encode(), &G_LIMITS).is_err());

    let mut outside = local(&f, 9);
    outside.close_first::<Sha256>().unwrap();
    outside
        .fence::<Sha256>(round(5), Participant::new(1))
        .unwrap();
    let snapshot = outside.snapshot().unwrap();
    let bytes = snapshot.encode();
    assert_eq!(
        Snapshot::<Digest>::decode(bytes.clone()).unwrap(),
        *snapshot
    );
    assert_eq!(snapshot.encode_size(), bytes.len());
    for end in 0..bytes.len() {
        assert!(Snapshot::<Digest>::decode(bytes.slice(..end)).is_err());
    }
    let mut trailing = bytes.to_vec();
    trailing.push(0);
    assert!(Snapshot::<Digest>::decode(trailing).is_err());
    let mut version = bytes.to_vec();
    version[3] = b'9';
    assert!(Snapshot::<Digest>::decode(version).is_err());
    let mut huge = bytes.to_vec();
    huge[4..8].copy_from_slice(&u32::MAX.to_be_bytes());
    assert!(Snapshot::<Digest>::decode(huge).is_err());
    let mut empty_mismatch = bytes.to_vec();
    let count_offset = empty_mismatch.len() - 8;
    empty_mismatch[count_offset..].copy_from_slice(&0u64.to_be_bytes());
    assert!(Snapshot::<Digest>::decode(empty_mismatch).is_err());
}

#[test]
fn decoded_prepare_and_commit_reservations_never_become_recovery_authority() {
    let f = fixture(10);
    let original = origin(&f);
    let mut state = local(&f, 9);
    let record = reserve_final(&mut state, &original);
    for phase in [g::Phase::Prepare, g::Phase::Commit] {
        let mut message = record.message().unwrap().clone();
        message.kind = g::Kind::Phase {
            phase,
            decision: original.body.decision.id::<Sha256>(),
        };
        let message_bytes = message.encode();
        let mut bytes = record.encode().to_vec();
        let offset = 8 + record.core().encode_size() + 32 + 4 + 1;
        bytes[offset..offset + message_bytes.len()].copy_from_slice(&message_bytes);
        let forged = Record::<Digest>::decode_cfg(bytes, &G_LIMITS).unwrap();
        let mut replay = replaying(&f, 9);
        assert!(restore(&mut replay, &forged, Material::Origin(&original)).is_err());
        assert!(replay.records().is_empty());
        assert!(replay.sign_reserved(&forged).is_err());
    }
}

#[test]
fn replay_rejects_changed_domain_profile_parent_epoch_input_or_owner_without_mutation() {
    let f = fixture(10);
    let original = origin(&f);
    let mut state = local(&f, 9);
    let record = reserve_final(&mut state, &original);
    for variant in 0..6 {
        let mut wrong_core = core(&f);
        let mut wrong_input = input();
        match variant {
            0 => wrong_core.slot.domain = Digest::from([0; 32]),
            1 => wrong_core.slot.profile = Digest::from([0; 32]),
            2 => {
                wrong_core.slot.parent = g::NativeParent::Proposal {
                    round: round(3),
                    digest: Digest::from([0; 32]),
                }
            }
            3 => {
                wrong_core.slot.proposal.round = Round::new(Epoch::new(2), View::new(4));
                wrong_core.slot.parent = g::NativeParent::Proposal {
                    round: Round::new(Epoch::new(2), View::new(3)),
                    digest: Digest::from([73; 32]),
                };
            }
            4 => wrong_input = Digest::from([0; 32]),
            _ => {}
        }
        let owner = if variant == 5 { 8 } else { 9 };
        let mut replay = State::for_replay::<Sha256>(
            f.schemes[owner].clone(),
            wrong_core,
            wrong_input,
            G_LIMITS,
        )
        .unwrap();
        assert!(restore(&mut replay, &record, Material::Origin(&original)).is_err());
        assert!(replay.records().is_empty());
        assert!(replay.sign_reserved(&record).is_err());
    }
}

thread_local! {
    static REPLAY_HASH_FRAME: Cell<Option<[u8; 4]>> = const { Cell::new(None) };
    static REPLAY_HASH_CALLS: Cell<usize> = const { Cell::new(0) };
}

// Preserve real SHA-256 identities while observing material identification.
// Only the requested public frame magic is counted; context hashes are allowed.
#[derive(Default)]
struct ReplayHashProbe(Sha256);
impl commonware_cryptography::Hasher for ReplayHashProbe {
    type Digest = Digest;

    fn hash(parts: &[&[u8]]) -> Self::Digest {
        let target = REPLAY_HASH_FRAME.with(Cell::get);
        if target.is_some_and(|magic| parts.iter().any(|part| part.starts_with(&magic))) {
            REPLAY_HASH_CALLS.with(|calls| calls.set(calls.get() + 1));
        }
        Sha256::hash(parts)
    }

    fn hash_pair(left: &[&[u8]], right: &[&[u8]]) -> (Self::Digest, Self::Digest) {
        (Self::hash(left), Self::hash(right))
    }

    fn update(&mut self, bytes: &[u8]) -> &mut Self {
        self.0.update(bytes);
        self
    }

    fn finalize(self) -> (Self, Self::Digest) {
        let (hasher, digest) = self.0.finalize();
        (Self(hasher), digest)
    }
}

fn assert_oversized_material_is_not_identified(
    state: &mut State<S, Digest>,
    record: &Record<Digest>,
    material: Material<'_, S, Digest>,
    frame: [u8; 4],
) {
    let before = state.records().to_vec();
    let row_calls = Cell::new(0);
    let build_calls = Cell::new(0);
    REPLAY_HASH_FRAME.with(|target| target.set(Some(frame)));
    REPLAY_HASH_CALLS.with(|calls| calls.set(0));
    let result = state.restore::<ReplayHashProbe, _>(
        &mut TestRng::new(2142),
        record,
        material,
        |row| {
            row_calls.set(row_calls.get() + 1);
            legal_row(row)
        },
        |rows, body| {
            build_calls.set(build_calls.get() + 1);
            build_policy(rows, body)
        },
        &Sequential,
    );
    let calls = REPLAY_HASH_CALLS.with(|calls| calls.replace(0));
    REPLAY_HASH_FRAME.with(|target| target.set(None));
    assert_eq!(
        calls, 0,
        "oversized material was identified before rejection: {result:?}"
    );
    assert!(result.is_err());
    assert_eq!(row_calls.get(), 0);
    assert_eq!(build_calls.get(), 0);
    assert_eq!(state.records(), before.as_slice());
}

fn oversized_origin(original: &GOrigin) -> GOrigin {
    let mut oversized = original.clone();
    oversized.body.build = Bytes::from(vec![0; G_LIMITS.build_bytes + 1]);
    assert!(GOrigin::decode_cfg(oversized.encode(), &G_LIMITS).is_err());
    oversized
}

#[test]
fn replay_rejects_oversized_select_body_before_identification() {
    let f = fixture(10);
    let original = origin(&f);
    let mut state = local(&f, 0);
    let first = state
        .reserve_first::<Sha256>(None, None, legal_row)
        .unwrap();
    let selection = state
        .reserve_select::<Sha256, _>(
            &mut TestRng::new(2143),
            &original.body,
            legal_row,
            build_policy,
            &Sequential,
        )
        .unwrap();
    let oversized = oversized_origin(&original);
    let mut replay = replaying(&f, 0);
    restore(&mut replay, &first, Material::None).unwrap();
    assert_oversized_material_is_not_identified(
        &mut replay,
        &selection,
        Material::Body(&oversized.body),
        *b"G1O1",
    );
}

#[test]
fn replay_rejects_oversized_fast_origin_before_identification() {
    let f = fixture(10);
    let original = origin(&f);
    let mut state = local(&f, 9);
    let choice = reserve_final(&mut state, &original);
    let oversized = oversized_origin(&original);
    assert_oversized_material_is_not_identified(
        &mut replaying(&f, 9),
        &choice,
        Material::Origin(&oversized),
        *b"G1E1",
    );
}

#[test]
fn replay_rejects_oversized_retained_origin_before_identification() {
    let f = fixture(10);
    let original = origin(&f);
    let mut state = local(&f, 9);
    let retained = state
        .retain_origin::<Sha256, _>(
            &mut TestRng::new(2144),
            &original,
            legal_row,
            build_policy,
            &Sequential,
        )
        .unwrap();
    let oversized = oversized_origin(&original);
    assert_oversized_material_is_not_identified(
        &mut replaying(&f, 9),
        &retained,
        Material::Origin(&oversized),
        *b"G1E1",
    );
}

fn terminal_record(
    f: &Fixture<S>,
    original: &GOrigin,
    fast: &g::Quorum<S, Digest>,
) -> Record<Digest> {
    local(f, f.schemes.len() - 1)
        .terminal::<Sha256, _>(
            &mut TestRng::new(2145),
            original,
            fast,
            legal_row,
            build_policy,
            &Sequential,
        )
        .unwrap()
}

#[test]
fn replay_rejects_oversized_terminal_origin_before_identification() {
    let f = fixture(10);
    let original = origin(&f);
    let fast = phase_quorum(&f, &original, g::Phase::FastFinal, 7);
    let terminal = terminal_record(&f, &original, &fast);
    let oversized = oversized_origin(&original);
    assert_oversized_material_is_not_identified(
        &mut replaying(&f, 9),
        &terminal,
        Material::Terminal {
            origin: &oversized,
            quorum: &fast,
        },
        *b"G1E1",
    );
}

#[test]
fn replay_rejects_oversized_terminal_quorum_before_identification() {
    let f = fixture(10);
    let original = origin(&f);
    let fast = phase_quorum(&f, &original, g::Phase::FastFinal, 7);
    let terminal = terminal_record(&f, &original, &fast);
    let mut oversized = fast.clone();
    // Quorums have no smaller deployment cap than their 4 MiB frame ceiling.
    // Cloned lazy signatures keep the fixture small until the observed encoding.
    let count = g::MAX_EVIDENCE_BYTES / fast.certificate.signatures[0].encode_size() + 1;
    oversized
        .certificate
        .signatures
        .resize(count, fast.certificate.signatures[0].clone());
    assert!(oversized.encode_size() > g::MAX_EVIDENCE_BYTES);
    assert!(g::Quorum::<S, Digest>::decode_cfg(oversized.encode(), &(G_LIMITS, 10)).is_err());
    assert_oversized_material_is_not_identified(
        &mut replaying(&f, 9),
        &terminal,
        Material::Terminal {
            origin: &original,
            quorum: &oversized,
        },
        *b"G1Q1",
    );
}

#[test]
fn replay_wrong_alias_stays_behind_exact_root_gate_before_application_callbacks() {
    let f = fixture(10);
    let original = origin(&f);
    let alias = alias(&f, &original);
    assert_eq!(
        checked(&f, &original).decision(),
        checked(&f, &alias).decision()
    );
    let mut state = local(&f, 9);
    let choice = reserve_final(&mut state, &original);
    let mut replay = replaying(&f, 9);
    let row_calls = Cell::new(0);
    let build_calls = Cell::new(0);
    let result = replay.restore::<Sha256, _>(
        &mut TestRng::new(2150),
        &choice,
        Material::Origin(&alias),
        |row| {
            row_calls.set(row_calls.get() + 1);
            legal_row(row)
        },
        |rows, body| {
            build_calls.set(build_calls.get() + 1);
            build_policy(rows, body)
        },
        &Sequential,
    );
    assert_eq!(result, Err(g::issuance::Error::Authority));
    assert_eq!(row_calls.get(), 0);
    assert_eq!(build_calls.get(), 0);
    assert!(replay.records().is_empty());
}

#[test]
fn highest_owner_noncontiguous_core_reservations_survive_native_journal_replay() {
    for with_fence in [false, true] {
        let f = fixture(64);
        let mut custom = core(&f);
        custom.leader = Participant::new(63);
        custom.followers = (0..21).chain(22..43).map(Participant::new).collect();
        assert_eq!(custom.followers.len(), 42);
        assert!(!custom.followers.contains(&Participant::new(21)));
        let make_signed = |owner: usize, kind| {
            g::Signed::sign(
                &f.schemes[owner],
                g::Message {
                    slot: custom.slot.id::<Sha256>(),
                    round: custom.slot.proposal.round,
                    leader: custom.leader,
                    kind,
                },
                G_LIMITS,
            )
            .unwrap()
        };
        let firsts: Vec<_> = custom
            .followers
            .iter()
            .copied()
            .chain(std::iter::once(custom.leader))
            .map(|owner| {
                make_signed(
                    usize::from(owner),
                    g::Kind::First(g::First {
                        core: custom.id::<Sha256>(),
                        input: input(),
                        owner,
                        report: (owner != custom.leader)
                            .then(|| Bytes::from(vec![owner.get() as u8])),
                        preference: (owner != custom.leader).then(|| Bytes::from_static(b"AB")),
                    }),
                )
            })
            .collect();
        let body = g::OriginBody {
            decision: g::Decision {
                slot: custom.slot.clone(),
                input: input(),
                order: Bytes::from_static(b"AB"),
            },
            core: custom.clone(),
            population: population(&firsts),
            build: build(&firsts),
            firsts,
            material: Bytes::new(),
        };
        let selection = make_signed(
            63,
            g::Kind::Select {
                body: body.id::<Sha256>(),
                decision: body.decision.id::<Sha256>(),
            },
        );
        let original = g::Origin { body, selection };
        original
            .verify::<Sha256, _>(
                &mut TestRng::new(2146),
                &f.verifier,
                &custom,
                input(),
                G_LIMITS,
                legal_row,
                build_policy,
                &Sequential,
            )
            .unwrap();
        let mut state =
            State::new::<Sha256>(f.schemes[63].clone(), custom.clone(), input(), G_LIMITS).unwrap();
        let first = state
            .reserve_first::<Sha256>(None, None, legal_row)
            .unwrap();
        let selection = state
            .reserve_select::<Sha256, _>(
                &mut TestRng::new(2147),
                &original.body,
                legal_row,
                build_policy,
                &Sequential,
            )
            .unwrap();
        let final_choice = reserve_final(&mut state, &original);
        for record in [&first, &selection, &final_choice] {
            assert_eq!(record.owner(), Participant::new(63));
            assert_eq!(record.core(), &custom);
            assert_eq!(record.message().unwrap().leader, Participant::new(63));
        }
        if with_fence {
            state
                .fence::<Sha256>(round(5), Participant::new(21))
                .unwrap();
            assert_eq!(state.snapshot().unwrap().count(), 3);
        }
        let written = state.records().to_vec();
        let expected = written.clone();
        let (_, checkpoint) =
            deterministic::Runner::seeded(2148).start_and_recover(move |context| async move {
                let mut journal = Journal::<_, Record<Digest>>::init(
                    context.child("custom_core_wal"),
                    JournalConfig {
                        partition: "g1-custom-core-replay".into(),
                        compression: None,
                        codec_config: G_LIMITS,
                        page_cache: CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(8)),
                        write_buffer: NZUsize!(1024),
                    },
                )
                .await
                .unwrap();
                for record in written {
                    journal = journal
                        .append(record.view().get(), &record)
                        .await
                        .unwrap()
                        .0;
                    journal = journal.sync(record.view().get()).await.unwrap();
                }
            });
        deterministic::Runner::from(checkpoint).start(move |context| async move {
            let journal = Journal::<_, Record<Digest>>::init(
                context.child("custom_core_wal"),
                JournalConfig {
                    partition: "g1-custom-core-replay".into(),
                    compression: None,
                    codec_config: G_LIMITS,
                    page_cache: CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(8)),
                    write_buffer: NZUsize!(1024),
                },
            )
            .await
            .unwrap();
            let mut stream = journal
                .replay(0, 0, NZUsize!(1024), ReadOptions::DONT_CACHE)
                .await
                .unwrap();
            let mut replay = State::for_replay::<Sha256>(
                f.schemes[63].clone(),
                custom.clone(),
                input(),
                G_LIMITS,
            )
            .unwrap();
            assert!(replay.sign_reserved(&final_choice).is_err());
            while let Some(row) = stream.next().await {
                let record = row.unwrap().3;
                let material = match record.message().map(|message| &message.kind) {
                    Some(g::Kind::Select { .. }) => Material::Body(&original.body),
                    Some(g::Kind::Phase { .. }) => Material::Origin(&original),
                    _ => Material::None,
                };
                restore(&mut replay, &record, material).unwrap();
            }
            drop(stream.finish().unwrap());
            replay.finish_replay().unwrap();
            assert_eq!(replay.records(), expected.as_slice());
            assert_eq!(replay.core(), &custom);
            assert_eq!(replay.owner(), Participant::new(63));
            for record in [&first, &selection, &final_choice] {
                if with_fence {
                    assert!(replay.sign_reserved(record).is_err());
                } else {
                    let signed = replay.sign_reserved(record).unwrap();
                    assert_eq!(signed.attestation.signer, Participant::new(63));
                    assert_eq!(signed.message, *record.message().unwrap());
                    assert!(signed.verify(
                        &mut TestRng::new(2149),
                        &f.verifier,
                        G_LIMITS,
                        &Sequential,
                    ));
                }
            }
        });
    }
}

struct GeneralIssuanceConformance;
impl Conformance for GeneralIssuanceConformance {
    async fn commit(seed: u64) -> Vec<u8> {
        let f = ed25519::fixture(
            &mut TestRng::new(seed),
            b"_COMMONWARE_CONSENSUS_G1_ISSUANCE_CONFORMANCE",
            10,
        );
        let (records, pages) = codec_corpus(&f);
        let mut encodings: Vec<_> = records.iter().map(|record| record.encode()).collect();
        encodings.extend(records.iter().filter_map(|record| match record.action() {
            Action::Fence { snapshot } => Some(snapshot.encode()),
            _ => None,
        }));
        encodings.extend(pages.iter().map(|page| page.encode()));
        encodings.encode().to_vec()
    }
}
conformance_tests! { GeneralIssuanceConformance => 32 }
