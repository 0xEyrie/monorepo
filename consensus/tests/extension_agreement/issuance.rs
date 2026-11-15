//! Local reservation/WAL controls, separate from full native actor integration.
use super::{
    recovery::{Store, check_root, fresh, leader, phase_quorum, proposal, put, rpc, snapshots},
    *,
};
use commonware_codec::Write as _;
use commonware_consensus::{
    Viewable as _,
    simplex::extension::agreement::{
        issuance::{Action, Error as IssuanceError, Record, State},
        recovery::{Material, Phase},
    },
};
use commonware_runtime::{
    ReadOptions, Runner as _, Supervisor as _, buffer::paged::CacheRef, deterministic,
};
use commonware_storage::journal::segmented::variable::{Config as JournalConfig, Journal};
use commonware_utils::{NZU16, NZUsize};

fn local(f: &Fixture<S>, owner: usize) -> State<S, Digest> {
    State::new::<Sha256>(
        slot(f),
        f.schemes[owner].clone(),
        Participant::new(0),
        LIMITS,
    )
    .unwrap()
}
fn message(f: &Fixture<S>, b: u64, kind: Kind<Digest>) -> Message<Digest> {
    Message {
        slot: slot(f).id::<Sha256>(),
        round: round(b),
        leader: leader(round(b)).unwrap(),
        kind,
    }
}
fn reserve(
    state: &mut State<S, Digest>,
    f: &Fixture<S>,
    b: u64,
    kind: Kind<Digest>,
    authority: Digest,
) -> Result<Record<Digest>, IssuanceError> {
    state.reserve::<Sha256>(message(f, b, kind), Some(authority), None, leader)
}
fn snapshot_body(
    store: &mut Store,
    f: &Fixture<S>,
    state: &mut State<S, Digest>,
    b: u64,
    report: Option<Bytes>,
) -> Digest {
    let plan = state
        .recover::<Sha256>(round(b), leader(round(b)).unwrap(), report, leader)
        .unwrap();
    for p in plan.pages {
        assert_eq!(
            p.id::<Sha256>(),
            Material::<S, Digest>::Page(p.clone()).id::<Sha256>()
        );
        put(store, Material::Page(p));
    }
    // This fixture's caller performs no signer invocation before the reservation.
    let signed = state.sign_reserved(&plan.record).unwrap();
    let root = put(store, Material::Snapshot(signed));
    assert_eq!(check_root(f, store, root).unwrap().phase(), Phase::Snapshot);
    root
}

fn trace(f: &Fixture<S>) -> (State<S, Digest>, Store, Vec<Record<Digest>>, Digest) {
    let p = proof(f);
    let mut store = Store::new();
    let origin = put(&mut store, Material::Origin(p.clone()));
    let mut state = local(f, 0);
    state
        .reserve::<Sha256>(
            p.firsts[0].message.clone(),
            None,
            Some(p.core.clone()),
            leader,
        )
        .unwrap();
    state
        .reserve::<Sha256>(p.selection.message.clone(), Some(origin), None, leader)
        .unwrap();
    reserve(
        &mut state,
        f,
        4,
        Kind::FastFinal(p.value.id::<Sha256>()),
        origin,
    )
    .unwrap();
    let mine = snapshot_body(&mut store, f, &mut state, 5, Some(Bytes::from(vec![0])));
    let mut rows = snapshots(&mut store, f, 5, &[None; 7]);
    rows[0] = mine;
    // The owner's old FAST reservation exposes one origin; conservative carry.
    let p5 = proposal(
        &mut store,
        f,
        5,
        p.value.clone(),
        &rows,
        &[0, 1, 2, 3, 4],
        &[],
        None,
    );
    assert_eq!(check_root(f, &store, p5).unwrap().phase(), Phase::Proposal);
    reserve(&mut state, f, 5, Kind::Prepare(p.value.id::<Sha256>()), p5).unwrap();
    let prepared = rpc(&mut store, f, p5);
    state
        .retain::<Sha256, _>(
            &mut TestRng::new(710),
            prepared,
            |id| store.get(id),
            &Sequential,
            policy,
            leader,
        )
        .unwrap();
    reserve(
        &mut state,
        f,
        5,
        Kind::Commit(p.value.id::<Sha256>()),
        prepared,
    )
    .unwrap();
    snapshot_body(&mut store, f, &mut state, 6, None);
    let records = state.records().to_vec();
    (state, store, records, prepared)
}

#[test]
fn original_core_first_select_and_any_five_final_roles_are_separate() {
    let f = fixture(7);
    let p = proof(&f);
    let mut s = local(&f, 0);
    let first = s
        .reserve::<Sha256>(
            p.firsts[0].message.clone(),
            None,
            Some(p.core.clone()),
            leader,
        )
        .unwrap();
    assert_eq!(
        s.reserve::<Sha256>(
            p.firsts[0].message.clone(),
            None,
            Some(p.core.clone()),
            leader
        )
        .unwrap(),
        first
    );
    let mut changed = p.firsts[0].message.clone();
    let Kind::First { report, .. } = &mut changed.kind else {
        unreachable!()
    };
    *report = None;
    assert_eq!(
        s.reserve::<Sha256>(changed, None, Some(p.core.clone()), leader),
        Err(IssuanceError::Conflict)
    );
    s.reserve::<Sha256>(
        p.selection.message.clone(),
        Some(Digest::from([8; 32])),
        None,
        leader,
    )
    .unwrap();
    let mut other = p.selection.message.clone();
    let Kind::Select { value, .. } = &mut other.kind else {
        unreachable!()
    };
    *value = Digest::from([99; 32]);
    assert_eq!(
        s.reserve::<Sha256>(other, Some(Digest::from([8; 32])), None, leader),
        Err(IssuanceError::Conflict)
    );
    let mut follower = local(&f, 1);
    assert_eq!(
        follower.reserve::<Sha256>(
            p.selection.message.clone(),
            Some(Digest::from([8; 32])),
            None,
            leader
        ),
        Err(IssuanceError::Authority)
    );
    let mut outsider = local(&f, 6);
    assert!(
        outsider
            .reserve::<Sha256>(p.firsts[1].message.clone(), None, Some(p.core), leader)
            .is_err()
    );
    // A non-Core identity can sign FAST_FINAL after the separate full-FPC check.
    let r = reserve(
        &mut outsider,
        &f,
        4,
        Kind::FastFinal(p.value.id::<Sha256>()),
        Digest::from([8; 32]),
    )
    .unwrap();
    assert!(outsider.sign_reserved(&r).is_ok());
    // No FPC/FIRST is required to reserve an independently authorized recovery snapshot.
    let mut no_core = local(&f, 6);
    assert!(
        no_core
            .recover::<Sha256>(round(5), Participant::new(1), None, leader)
            .is_ok()
    );
}

#[test]
fn immutable_snapshot_captures_unsigned_reservations_and_late_positive_custody() {
    let f = fixture(7);
    let (mut s, mut store, records, _) = trace(&f);
    let snapshot5 = &records[3];
    assert!(matches!(
        snapshot5.action(),
        Action::Reserve {
            message: Message {
                kind: Kind::Recover {
                    history: Some(_),
                    ..
                },
                ..
            },
            ..
        }
    ));
    // trace advanced to six; it cannot create a new lower signature.
    assert_eq!(
        s.sign_reserved(snapshot5).unwrap_err(),
        IssuanceError::Floor
    );
    let mut at_five = local(&f, 0);
    for r in &records[..7] {
        at_five.restore::<Sha256>(r, leader).unwrap();
    }
    let repeated = at_five
        .recover::<Sha256>(
            round(5),
            Participant::new(1),
            Some(Bytes::from_static(b"new")),
            leader,
        )
        .unwrap();
    assert_eq!(repeated.record, *snapshot5);
    // The next original snapshot includes PREPARE, COMMIT, and separately received RPC.
    let root = snapshot_body(&mut store, &f, &mut s, 7, None);
    let Material::Snapshot(signed) = &store[&root] else {
        unreachable!()
    };
    let Kind::Recover { history, .. } = &signed.message.kind else {
        unreachable!()
    };
    assert!(history.is_some());
    assert_eq!(check_root(&f, &store, root).unwrap().round(), round(7));
}

#[test]
fn late_lower_proof_is_not_added_to_an_already_frozen_snapshot() {
    let f = fixture(7);
    let mut s = local(&f, 0);
    let before = s
        .recover::<Sha256>(round(6), Participant::new(2), None, leader)
        .unwrap();
    assert!(before.pages.is_empty());
    let mut store = Store::new();
    let origin = put(&mut store, Material::Origin(proof(&f)));
    s.retain::<Sha256, _>(
        &mut TestRng::new(715),
        origin,
        |id| store.get(id),
        &Sequential,
        policy,
        leader,
    )
    .unwrap();
    let repeated = s
        .recover::<Sha256>(round(6), Participant::new(2), None, leader)
        .unwrap();
    assert_eq!(before.record, repeated.record);
    assert!(repeated.pages.is_empty());
    let next = s
        .recover::<Sha256>(round(7), Participant::new(3), None, leader)
        .unwrap();
    assert_eq!(next.pages.len(), 1);
    assert!(matches!(
        next.pages[0].entry,
        commonware_consensus::simplex::extension::agreement::recovery::Entry::Witness(id)
            if id == origin
    ));
    for page in next.pages {
        put(&mut store, Material::Page(page));
    }
    let signed = s.sign_reserved(&next.record).unwrap();
    let root = put(&mut store, Material::Snapshot(signed));
    assert_eq!(
        check_root(&f, &store, root).unwrap().phase(),
        Phase::Snapshot
    );
}

#[test]
fn commit_without_self_recover_or_prepare_is_valid_but_conflicting_own_choices_are_not() {
    let f = fixture(7);
    let mut store = Store::new();
    let rows = snapshots(&mut store, &f, 5, &[None; 7]);
    let v = fresh(&f, 5, &[0, 1, 2, 3, 4]);
    let p = proposal(
        &mut store,
        &f,
        5,
        v.clone(),
        &rows,
        &[0, 1, 2, 3, 4],
        &[],
        None,
    );
    let prepared = rpc(&mut store, &f, p);
    assert_eq!(
        check_root(&f, &store, prepared).unwrap().phase(),
        Phase::Prepared
    );
    let mut s = local(&f, 6);
    reserve(&mut s, &f, 5, Kind::Commit(v.id::<Sha256>()), prepared).unwrap();
    // First RECOVER at b after a local b COMMIT excludes that b authorization.
    let own = s
        .recover::<Sha256>(round(5), Participant::new(1), None, leader)
        .unwrap();
    assert!(own.pages.is_empty());
    let signed = s.sign_reserved(&own.record).unwrap();
    let root = put(&mut store, Material::Snapshot(signed));
    assert!(check_root(&f, &store, root).is_ok());
    assert_eq!(
        reserve(&mut s, &f, 5, Kind::Prepare(Digest::from([88; 32])), p),
        Err(IssuanceError::Conflict)
    );
    reserve(&mut s, &f, 5, Kind::Prepare(v.id::<Sha256>()), p).unwrap();
    assert_eq!(s.floor(), round(5));
    snapshot_body(&mut store, &f, &mut s, 6, None);
}

#[test]
fn elected_leader_proposal_freezes_exact_j_and_agrees_with_own_votes() {
    let f = fixture(7);
    let mut s = local(&f, 1);
    let p = Digest::from([10; 32]);
    let v = Digest::from([20; 32]);
    let r = reserve(
        &mut s,
        &f,
        5,
        Kind::Propose {
            proposal: p,
            value: v,
        },
        p,
    )
    .unwrap();
    let changed = Digest::from([11; 32]);
    assert_eq!(
        reserve(
            &mut s,
            &f,
            5,
            Kind::Propose {
                proposal: changed,
                value: v
            },
            changed
        ),
        Err(IssuanceError::Conflict)
    );
    assert_eq!(
        reserve(&mut s, &f, 5, Kind::Prepare(Digest::from([99; 32])), p),
        Err(IssuanceError::Conflict)
    );
    reserve(&mut s, &f, 5, Kind::Prepare(v), p).unwrap();
    assert!(s.sign_reserved(&r).is_ok());
    let mut other = local(&f, 2);
    assert_eq!(
        reserve(
            &mut other,
            &f,
            5,
            Kind::Propose {
                proposal: p,
                value: v
            },
            p
        ),
        Err(IssuanceError::Authority)
    );
}

// Construct deliberately hostile decoded WAL data without public Record fields.
fn raw(
    f: &Fixture<S>,
    owner: usize,
    m: Message<Digest>,
    authority: Option<Digest>,
    core: Option<Core<Digest>>,
) -> Record<Digest> {
    let mut b = Vec::new();
    1u8.write(&mut b);
    slot(f).write(&mut b);
    Participant::new(owner as u32).write(&mut b);
    0u8.write(&mut b);
    m.write(&mut b);
    authority.write(&mut b);
    core.write(&mut b);
    Record::decode(Bytes::from(b)).unwrap()
}

#[test]
fn incomplete_snapshot_replay_and_wrong_context_fail_without_changing_state() {
    let f = fixture(7);
    let mut s = local(&f, 0);
    let v = Digest::from([9; 32]);
    reserve(&mut s, &f, 4, Kind::FastFinal(v), Digest::from([8; 32])).unwrap();
    let incomplete = raw(
        &f,
        0,
        message(
            &f,
            5,
            Kind::Recover {
                history: None,
                report: None,
            },
        ),
        None,
        None,
    );
    assert_eq!(
        s.restore::<Sha256>(&incomplete, leader),
        Err(IssuanceError::Conflict)
    );
    assert_eq!(s.floor(), round(4));
    assert_eq!(s.records().len(), 1);
    let forged_owner = raw(&f, 1, message(&f, 5, Kind::Prepare(v)), Some(v), None);
    assert_eq!(
        s.restore::<Sha256>(&forged_owner, leader),
        Err(IssuanceError::Context)
    );
    assert!(
        s.recover::<Sha256>(round(5), Participant::new(2), None, leader)
            .is_err()
    );
    assert!(
        s.recover::<Sha256>(round(5), Participant::new(1), None, |_| None)
            .is_err()
    );
    assert!(matches!(
        State::new::<Sha256>(slot(&f), f.verifier.clone(), Participant::new(0), LIMITS),
        Err(IssuanceError::Context)
    ));
}

#[test]
fn terminal_tombstone_survives_replay_and_stops_all_new_signing() {
    let f = fixture(7);
    let (mut state, mut store, _, prepared) = trace(&f);
    let Material::Prepared { quorum, .. } = &store[&prepared] else {
        unreachable!()
    };
    let value = quorum.message.kind.voted_value().unwrap();
    let terminal = put(
        &mut store,
        Material::Terminal {
            authority: prepared,
            quorum: phase_quorum(&f, 5, Kind::Commit(value), &[0, 1, 2, 3, 4]),
        },
    );
    check_root(&f, &store, terminal).unwrap();
    let r = state
        .retain::<Sha256, _>(
            &mut TestRng::new(711),
            terminal,
            |id| store.get(id),
            &Sequential,
            policy,
            leader,
        )
        .unwrap();
    assert!(matches!(r.action(), Action::Decide { .. }));
    let mut replay = local(&f, 0);
    for r in state.records() {
        replay.restore::<Sha256>(r, leader).unwrap();
    }
    assert!(replay.terminal().is_some());
    assert_eq!(
        replay.sign_reserved(&replay.records()[2]).unwrap_err(),
        IssuanceError::Closed
    );
    assert!(matches!(
        replay.recover::<Sha256>(round(7), Participant::new(3), None, leader),
        Err(IssuanceError::Closed)
    ));
    assert!(matches!(
        reserve(&mut replay, &f, 7, Kind::Prepare(value), prepared),
        Err(IssuanceError::Closed)
    ));
    assert_eq!(
        replay
            .retain::<Sha256, _>(
                &mut TestRng::new(712),
                terminal,
                |id| store.get(id),
                &Sequential,
                policy,
                leader,
            )
            .unwrap(),
        r
    );
}

#[test]
fn every_record_codec_is_bounded_and_rejects_truncation_or_unknown_tags() {
    let f = fixture(7);
    let (state, _, _, _) = trace(&f);
    for r in state.records() {
        let bytes = r.encode();
        assert_eq!(r.encode_size(), bytes.len());
        assert_eq!(Record::<Digest>::decode(bytes.clone()).unwrap(), *r);
        for n in 0..bytes.len() {
            assert!(Record::<Digest>::decode(bytes.slice(..n)).is_err());
        }
        let mut bad = bytes.to_vec();
        bad[0] = 99;
        assert!(Record::<Digest>::decode(Bytes::from(bad)).is_err());
        let mut bad = bytes.to_vec();
        bad[1 + r.slot().encode_size() + r.owner().encode_size()] = 99;
        assert!(Record::<Digest>::decode(Bytes::from(bad)).is_err());
    }
    let mut s = local(&f, 0);
    let mut p = proof(&f);
    let mut m = p.firsts[0].message.clone();
    let Kind::First { core, report } = &mut m.kind else {
        unreachable!()
    };
    *report = Some(Bytes::from(vec![1; 64 * 1024 + 1]));
    p.core.leader_report = Core::<Digest>::row::<Sha256>(report);
    *core = p.core.id::<Sha256>();
    assert!(s.reserve::<Sha256>(m, None, Some(p.core), leader).is_err());
    assert!(s.records().is_empty());
}

#[test]
fn configured_report_limit_is_checked_before_freezing_recover() {
    let f = fixture(7);
    let mut s = local(&f, 0);
    assert!(
        s.recover::<Sha256>(
            round(5),
            Participant::new(1),
            Some(Bytes::from(vec![0; LIMITS.report_bytes + 1])),
            leader,
        )
        .is_err()
    );
    assert_eq!(s.floor(), round(4));
    assert!(s.records().is_empty());
    let mut store = Store::new();
    snapshot_body(&mut store, &f, &mut s, 5, None);
}

#[test]
fn configured_namespace_cannot_be_closed_by_a_foreign_terminal() {
    let f = fixture(7);
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
    let p = proof(&foreign);
    let mut store = Store::new();
    let origin = put(&mut store, Material::Origin(p.clone()));
    let terminal = put(
        &mut store,
        Material::Terminal {
            authority: origin,
            quorum: phase_quorum(
                &foreign,
                4,
                Kind::FastFinal(p.value.id::<Sha256>()),
                &[0, 1, 2, 3, 4],
            ),
        },
    );
    check_root(&foreign, &store, terminal).unwrap();
    assert!(check_root(&f, &store, terminal).is_err());
    let mut s = local(&f, 0);
    assert!(
        s.retain::<Sha256, _>(
            &mut TestRng::new(713),
            terminal,
            |id| store.get(id),
            &Sequential,
            policy,
            leader,
        )
        .is_err()
    );
    assert!(s.terminal().is_none());
    assert!(s.records().is_empty());
}

#[test]
fn actual_native_journal_restart_restores_unsigned_choices_and_later_floor() {
    for count in [3usize, 4, 5, 7, 8] {
        let f = fixture(7);
        let (_, _, records, _) = trace(&f);
        let written = records[..count].to_vec();
        let (_, checkpoint) =
            deterministic::Runner::default().start_and_recover(move |context| async move {
                let mut journal = Journal::<_, Record<Digest>>::init(
                    context.child("wal"),
                    JournalConfig {
                        partition: "agreement-issuance".into(),
                        compression: None,
                        codec_config: (),
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
                context.child("wal"),
                JournalConfig {
                    partition: "agreement-issuance".into(),
                    compression: None,
                    codec_config: (),
                    page_cache: CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(8)),
                    write_buffer: NZUsize!(1024),
                },
            )
            .await
            .unwrap();
            let mut replay = journal
                .replay(0, 0, NZUsize!(1024), ReadOptions::DONT_CACHE)
                .await
                .unwrap();
            let mut state = local(&f, 0);
            let mut got = 0;
            while let Some(row) = replay.next().await {
                let row = row.unwrap().3;
                state.restore::<Sha256>(&row, leader).unwrap();
                got += 1;
            }
            drop(replay.finish().unwrap());
            assert_eq!(got, count);
            let original = state.records()[2].clone();
            if count == 3 {
                assert!(state.sign_reserved(&original).is_ok());
            } else {
                assert_eq!(
                    state.sign_reserved(&original).unwrap_err(),
                    IssuanceError::Floor
                );
            }
            assert!(
                reserve(
                    &mut state,
                    &f,
                    4,
                    Kind::FastFinal(Digest::from([99; 32])),
                    Digest::from([8; 32])
                )
                .is_err()
            );
        });
    }
}

struct IssuanceConformance;
impl Conformance for IssuanceConformance {
    async fn commit(seed: u64) -> Vec<u8> {
        let f = ed25519::fixture(
            &mut TestRng::new(seed),
            b"_COMMONWARE_CONSENSUS_ISSUANCE_CONFORMANCE",
            7,
        );
        let (mut state, mut store, _, prepared) = trace(&f);
        let origin = put(&mut store, Material::Origin(proof(&f)));
        state
            .retain::<Sha256, _>(
                &mut TestRng::new(714),
                origin,
                |id| store.get(id),
                &Sequential,
                policy,
                leader,
            )
            .unwrap();
        let Material::Prepared { quorum, .. } = &store[&prepared] else {
            unreachable!()
        };
        let value = quorum.message.kind.voted_value().unwrap();
        let terminal = put(
            &mut store,
            Material::Terminal {
                authority: prepared,
                quorum: phase_quorum(&f, 5, Kind::Commit(value), &[0, 1, 2, 3, 4]),
            },
        );
        state
            .retain::<Sha256, _>(
                &mut TestRng::new(714),
                terminal,
                |id| store.get(id),
                &Sequential,
                policy,
                leader,
            )
            .unwrap();
        // Separate legal issuer for the leader's frozen Propose representation.
        let mut elected = local(&f, 1);
        reserve(
            &mut elected,
            &f,
            5,
            Kind::Propose {
                proposal: prepared,
                value,
            },
            prepared,
        )
        .unwrap();
        state
            .records()
            .iter()
            .chain(elected.records())
            .map(|r| r.encode())
            .collect::<Vec<_>>()
            .encode()
            .to_vec()
    }
}
conformance_tests! {IssuanceConformance=>32}
