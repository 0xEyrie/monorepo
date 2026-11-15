use super::*;
use commonware_consensus::simplex::extension::agreement::recovery::{
    Entry, Error as RecoveryError, Material, Page, Phase, Proposal as RecoveryProposal, Verified,
    Verifier,
};
use std::collections::{BTreeMap, BTreeSet};

pub(super) type Store = BTreeMap<Digest, Material<S, Digest>>;
pub(super) fn put(store: &mut Store, material: Material<S, Digest>) -> Digest {
    let id = material.id::<Sha256>();
    store.insert(id, material);
    id
}
pub(super) fn leader(r: Round) -> Option<Participant> {
    (r.epoch() == Epoch::new(1) && r.view() >= View::new(4))
        .then(|| Participant::new(((r.view().get() - 4) % 7) as u32))
}
pub(super) fn check_root(
    f: &Fixture<S>,
    store: &Store,
    root: Digest,
) -> Result<Verified<Digest>, RecoveryError<Digest>> {
    Verifier::new(&f.verifier, &slot(f), LIMITS, &Sequential, policy, leader).verify::<Sha256, _>(
        &mut TestRng::new(1501),
        root,
        |id| store.get(id),
    )
}
fn page(
    store: &mut Store,
    f: &Fixture<S>,
    owner: usize,
    previous: Option<Digest>,
    entry: Entry<Digest>,
) -> Digest {
    put(
        store,
        Material::Page(Page {
            slot: slot(f).id::<Sha256>(),
            owner: Participant::new(owner as u32),
            previous,
            entry,
        }),
    )
}
fn snapshot(
    store: &mut Store,
    f: &Fixture<S>,
    owner: usize,
    b: u64,
    history: Option<Digest>,
) -> Digest {
    put(
        store,
        Material::Snapshot(
            Signed::sign(
                &f.schemes[owner],
                Message {
                    slot: slot(f).id::<Sha256>(),
                    round: round(b),
                    leader: leader(round(b)).unwrap(),
                    kind: Kind::Recover {
                        history,
                        report: Some(Bytes::from(vec![owner as u8])),
                    },
                },
            )
            .unwrap(),
        ),
    )
}
pub(super) fn snapshots(
    store: &mut Store,
    f: &Fixture<S>,
    b: u64,
    histories: &[Option<Digest>; 7],
) -> [Digest; 7] {
    std::array::from_fn(|id| snapshot(store, f, id, b, histories[id]))
}
pub(super) fn fresh(f: &Fixture<S>, b: u64, ids: &[usize]) -> Value<Digest> {
    let reports: Vec<_> = ids
        .iter()
        .map(|id| Row {
            owner: Participant::new(*id as u32),
            report: Some(Bytes::from(vec![*id as u8])),
        })
        .collect();
    Value {
        slot: slot(f),
        origin: Origin::Recovery {
            round: round(b),
            leader: leader(round(b)).unwrap(),
        },
        direction: direction(&reports),
        reports,
    }
}
// Keep frozen Q, original supplements, and positive evidence distinct in fixtures.
#[allow(clippy::too_many_arguments)]
pub(super) fn proposal(
    store: &mut Store,
    f: &Fixture<S>,
    b: u64,
    value: Value<Digest>,
    rows: &[Digest; 7],
    initial: &[usize],
    extra: &[usize],
    positive: Option<Digest>,
) -> Digest {
    assert_eq!(value.slot, slot(f));
    let proposal = RecoveryProposal {
        round: round(b),
        leader: leader(round(b)).unwrap(),
        value,
        initial: initial.iter().map(|id| rows[*id]).collect(),
        extra: extra.iter().map(|id| rows[*id]).collect(),
        positive,
    };
    let endorsement = Signed::sign(
        &f.schemes[usize::from(proposal.leader)],
        Message {
            slot: slot(f).id::<Sha256>(),
            round: proposal.round,
            leader: proposal.leader,
            kind: Kind::Propose {
                proposal: proposal.id::<Sha256>(),
                value: proposal.value.id::<Sha256>(),
            },
        },
    )
    .unwrap();
    put(
        store,
        Material::Proposal {
            proposal,
            endorsement,
        },
    )
}
pub(super) fn phase_quorum(
    f: &Fixture<S>,
    b: u64,
    kind: Kind<Digest>,
    ids: &[usize],
) -> Quorum<S, Digest> {
    let signed: Vec<_> = ids
        .iter()
        .map(|id| {
            Signed::sign(
                &f.schemes[*id],
                Message {
                    slot: slot(f).id::<Sha256>(),
                    round: round(b),
                    leader: leader(round(b)).unwrap(),
                    kind: kind.clone(),
                },
            )
            .unwrap()
        })
        .collect();
    quorum(f, signed).unwrap()
}
pub(super) fn rpc(store: &mut Store, f: &Fixture<S>, p: Digest) -> Digest {
    rpc_with(store, f, p, &[0, 1, 2, 3, 4])
}
fn rpc_with(store: &mut Store, f: &Fixture<S>, p: Digest, ids: &[usize]) -> Digest {
    let Material::Proposal {
        proposal: p_body, ..
    } = &store[&p]
    else {
        panic!("proposal fixture")
    };
    let q = phase_quorum(
        f,
        p_body.round.view().get(),
        Kind::Prepare(p_body.value.id::<Sha256>()),
        ids,
    );
    put(
        store,
        Material::Prepared {
            proposal: p,
            quorum: q,
        },
    )
}
fn positive(store: &mut Store, evidence: &[Digest]) -> Option<Digest> {
    let mut previous = None;
    for evidence in evidence {
        previous = Some(put(
            store,
            Material::Positive {
                previous,
                evidence: *evidence,
            },
        ));
    }
    previous
}
fn two_origins(store: &mut Store, f: &Fixture<S>) -> [(Digest, Value<Digest>); 2] {
    let a = proof(f);
    let mut b = a.clone();
    b.firsts[2] = Signed::sign(
        &f.schemes[2],
        Message {
            kind: Kind::First {
                core: b.core.id::<Sha256>(),
                report: Some(Bytes::from_static(b"fork")),
            },
            ..b.firsts[2].message.clone()
        },
    )
    .unwrap();
    select(f, &mut b);
    [a, b].map(|p| {
        let value = p.value.clone();
        (put(store, Material::Origin(p)), value)
    })
}
fn fast_authorization(f: &Fixture<S>, origin: &(Digest, Value<Digest>)) -> Entry<Digest> {
    Entry::Authorization {
        message: Message {
            slot: slot(f).id::<Sha256>(),
            round: round(4),
            leader: Participant::new(0),
            kind: Kind::FastFinal(origin.1.id::<Sha256>()),
        },
        evidence: origin.0,
    }
}
fn fork_histories(
    store: &mut Store,
    f: &Fixture<S>,
    origins: &[(Digest, Value<Digest>); 2],
    profile: [Option<usize>; 5],
) -> [Option<Digest>; 7] {
    let mut histories = [None; 7];
    // The signed conflicting origins identify exactly leader 0 and follower 2.
    histories[0] = Some(page(store, f, 0, None, Entry::Witness(origins[0].0)));
    histories[0] = Some(page(
        store,
        f,
        0,
        histories[0],
        Entry::Witness(origins[1].0),
    ));
    for (owner, choice) in [1, 3, 4, 5, 6].into_iter().zip(profile) {
        if let Some(choice) = choice {
            histories[owner] = Some(page(
                store,
                f,
                owner,
                None,
                fast_authorization(f, &origins[choice]),
            ));
        }
    }
    histories
}

#[test]
fn fresh_recovery_prepare_and_commit_require_the_full_admission_dag() {
    let f = fixture(7);
    let mut store = Store::new();
    let rows = snapshots(&mut store, &f, 5, &[None; 7]);
    let value = fresh(&f, 5, &[0, 1, 2, 3, 4]);
    let p = proposal(
        &mut store,
        &f,
        5,
        value.clone(),
        &rows,
        &[0, 1, 2, 3, 4],
        &[],
        None,
    );
    let checked = check_root(&f, &store, p).unwrap();
    assert_eq!(checked.phase(), Phase::Proposal);
    assert_eq!(checked.value(), Some(&value));
    let prepared = rpc(&mut store, &f, p);
    assert_eq!(
        check_root(&f, &store, prepared).unwrap().phase(),
        Phase::Prepared
    );
    let terminal = put(
        &mut store,
        Material::Terminal {
            authority: prepared,
            quorum: phase_quorum(&f, 5, Kind::Commit(value.id::<Sha256>()), &[2, 3, 4, 5, 6]),
        },
    );
    assert_eq!(
        check_root(&f, &store, terminal).unwrap().phase(),
        Phase::Terminal
    );
    // A real five-signature QC cannot bless a missing or altered admission witness.
    let body = store.remove(&p).unwrap();
    assert_eq!(
        check_root(&f, &store, terminal).unwrap_err(),
        RecoveryError::Missing(p)
    );
    let Material::Proposal {
        proposal: mut corrupt,
        endorsement,
    } = body
    else {
        unreachable!()
    };
    corrupt.value.direction = Bytes::from_static(b"invalid selector result");
    store.insert(
        p,
        Material::Proposal {
            proposal: corrupt,
            endorsement,
        },
    );
    assert_eq!(
        check_root(&f, &store, terminal).unwrap_err(),
        RecoveryError::Hash
    );
}

#[test]
fn prepared_is_not_terminal_and_commit_cannot_replace_prepare() {
    let f = fixture(7);
    let mut store = Store::new();
    let rows = snapshots(&mut store, &f, 5, &[None; 7]);
    let value = fresh(&f, 5, &[0, 1, 2, 3, 4]);
    let p = proposal(
        &mut store,
        &f,
        5,
        value.clone(),
        &rows,
        &[0, 1, 2, 3, 4],
        &[],
        None,
    );
    let q = phase_quorum(&f, 5, Kind::Prepare(value.id::<Sha256>()), &[0, 1, 2, 3, 4]);
    let wrong = put(
        &mut store,
        Material::Terminal {
            authority: p,
            quorum: q,
        },
    );
    assert!(check_root(&f, &store, wrong).is_err());
    let wrong = put(
        &mut store,
        Material::Prepared {
            proposal: p,
            quorum: phase_quorum(&f, 5, Kind::Commit(value.id::<Sha256>()), &[0, 1, 2, 3, 4]),
        },
    );
    assert!(check_root(&f, &store, wrong).is_err());
    let prepared = rpc(&mut store, &f, p);
    let wrong = put(
        &mut store,
        Material::Terminal {
            authority: prepared,
            quorum: phase_quorum(&f, 6, Kind::Commit(value.id::<Sha256>()), &[0, 1, 2, 3, 4]),
        },
    );
    assert!(check_root(&f, &store, wrong).is_err());
}

#[test]
fn fork_requires_all_five_honest_original_snapshots_without_changing_fresh_rows() {
    let f = fixture(7);
    let mut store = Store::new();
    let origins = two_origins(&mut store, &f);
    let histories = fork_histories(
        &mut store,
        &f,
        &origins,
        [Some(0), Some(0), Some(1), Some(1), None],
    );
    let rows = snapshots(&mut store, &f, 5, &histories);
    let value = fresh(&f, 5, &[0, 1, 2, 3, 4]);
    let p = proposal(
        &mut store,
        &f,
        5,
        value.clone(),
        &rows,
        &[0, 1, 2, 3, 4],
        &[],
        None,
    );
    assert_eq!(
        check_root(&f, &store, p).unwrap_err(),
        RecoveryError::NeedSnapshots([5, 6].map(Participant::new).to_vec())
    );
    let p = proposal(
        &mut store,
        &f,
        5,
        value,
        &rows,
        &[0, 1, 2, 3, 4],
        &[5, 6],
        None,
    );
    assert_eq!(check_root(&f, &store, p).unwrap().phase(), Phase::Proposal);
    let substituted = fresh(&f, 5, &[1, 3, 4, 5, 6]);
    let p = proposal(
        &mut store,
        &f,
        5,
        substituted,
        &rows,
        &[0, 1, 2, 3, 4],
        &[5, 6],
        None,
    );
    assert!(check_root(&f, &store, p).is_err());
}

#[test]
fn reserved_unpublished_fast_authorizations_force_exact_original_value() {
    let f = fixture(7);
    let mut store = Store::new();
    let origins = two_origins(&mut store, &f);
    let histories = fork_histories(
        &mut store,
        &f,
        &origins,
        [Some(0), Some(0), Some(0), Some(1), None],
    );
    let rows = snapshots(&mut store, &f, 5, &histories);
    let p = proposal(
        &mut store,
        &f,
        5,
        origins[0].1.clone(),
        &rows,
        &[0, 1, 2, 3, 4],
        &[5, 6],
        None,
    );
    assert_eq!(
        check_root(&f, &store, p).unwrap().value(),
        Some(&origins[0].1)
    );
    for bad in [origins[1].1.clone(), fresh(&f, 5, &[0, 1, 2, 3, 4])] {
        let p = proposal(
            &mut store,
            &f,
            5,
            bad,
            &rows,
            &[0, 1, 2, 3, 4],
            &[5, 6],
            None,
        );
        assert!(check_root(&f, &store, p).is_err());
    }
}

#[test]
fn terminal_and_highest_rpc_take_priority_before_fork_complement_wait() {
    let f = fixture(7);
    let mut store = Store::new();
    let origins = two_origins(&mut store, &f);
    let histories = fork_histories(&mut store, &f, &origins, [None; 5]);
    let rows5 = snapshots(&mut store, &f, 5, &[None; 7]);
    let value = fresh(&f, 5, &[0, 1, 2, 3, 4]);
    let p5 = proposal(
        &mut store,
        &f,
        5,
        value.clone(),
        &rows5,
        &[0, 1, 2, 3, 4],
        &[],
        None,
    );
    let prepared = rpc(&mut store, &f, p5);
    let rows6 = snapshots(&mut store, &f, 6, &histories);
    let positives = positive(&mut store, &[prepared]);
    let p6 = proposal(
        &mut store,
        &f,
        6,
        value.clone(),
        &rows6,
        &[0, 1, 2, 3, 4],
        &[],
        positives,
    );
    assert_eq!(check_root(&f, &store, p6).unwrap().value(), Some(&value));
    let terminal = put(
        &mut store,
        Material::Terminal {
            authority: prepared,
            quorum: phase_quorum(&f, 5, Kind::Commit(value.id::<Sha256>()), &[0, 1, 2, 3, 4]),
        },
    );
    let positives = positive(&mut store, &[terminal]);
    let p6 = proposal(
        &mut store,
        &f,
        6,
        value,
        &rows6,
        &[0, 1, 2, 3, 4],
        &[],
        positives,
    );
    assert_eq!(
        check_root(&f, &store, p6).unwrap_err(),
        RecoveryError::Catchup(terminal)
    );
}

#[test]
fn snapshot_owner_carrier_duplicates_and_forged_history_are_rejected() {
    let f = fixture(7);
    let mut store = Store::new();
    let origins = two_origins(&mut store, &f);
    let history = page(&mut store, &f, 1, None, Entry::Witness(origins[0].0));
    let forged = snapshot(&mut store, &f, 3, 5, Some(history));
    assert!(check_root(&f, &store, forged).is_err());
    let mut histories = [None; 7];
    histories[1] = Some(history);
    let rows = snapshots(&mut store, &f, 5, &histories);
    for ids in [[0, 1, 2, 3, 3], [0, 2, 1, 3, 4]] {
        let p = proposal(
            &mut store,
            &f,
            5,
            origins[0].1.clone(),
            &rows,
            &ids,
            &[],
            None,
        );
        assert!(check_root(&f, &store, p).is_err());
    }
    let p = proposal(
        &mut store,
        &f,
        5,
        origins[0].1.clone(),
        &rows,
        &[0, 1, 2, 3, 4],
        &[4],
        None,
    );
    assert!(check_root(&f, &store, p).is_err());
    let p = proposal(
        &mut store,
        &f,
        6,
        origins[0].1.clone(),
        &rows,
        &[0, 1, 2, 3, 4],
        &[],
        None,
    );
    assert!(check_root(&f, &store, p).is_err());
    let mut wrong = phase_quorum(
        &f,
        4,
        Kind::FastFinal(origins[0].1.id::<Sha256>()),
        &[0, 1, 2, 3, 4],
    )
    .message;
    wrong.kind = Kind::Commit(origins[0].1.id::<Sha256>());
    let forged = page(
        &mut store,
        &f,
        1,
        None,
        Entry::Authorization {
            message: wrong,
            evidence: origins[0].0,
        },
    );
    let root = snapshot(&mut store, &f, 1, 5, Some(forged));
    assert!(check_root(&f, &store, root).is_err());
}

#[test]
fn every_honest_fast_profile_matches_independent_possible_certificate_enumeration() {
    let f = fixture(7);
    let honest = [1usize, 3, 4, 5, 6];
    let five_sets: Vec<Vec<usize>> = (0u8..128)
        .filter(|mask| mask.count_ones() == 5)
        .map(|mask| (0..7).filter(|id| mask & (1 << id) != 0).collect())
        .collect();
    for encoded in 0..243usize {
        let mut digits = encoded;
        let profile: [Option<usize>; 5] = std::array::from_fn(|_| {
            let d = digits % 3;
            digits /= 3;
            match d {
                0 => None,
                1 => Some(0),
                _ => Some(1),
            }
        });
        // Independent oracle asks whether any exact quorum can be assembled,
        // treating the two faulty identities as able to sign either old value.
        let possible: Vec<_> = (0..2)
            .filter(|value| {
                five_sets.iter().any(|set| {
                    set.iter().all(|id| {
                        honest
                            .iter()
                            .position(|h| h == id)
                            .is_none_or(|index| profile[index] == Some(*value))
                    })
                })
            })
            .collect();
        assert!(possible.len() <= 1);
        let mut store = Store::new();
        let origins = two_origins(&mut store, &f);
        let histories = fork_histories(&mut store, &f, &origins, profile);
        let rows = snapshots(&mut store, &f, 5, &histories);
        let positive = positive(&mut store, &[origins[0].0, origins[1].0]);
        for initial in &five_sets {
            let extra: Vec<_> = honest
                .iter()
                .copied()
                .filter(|id| !initial.contains(id))
                .collect();
            let expected = possible
                .first()
                .map_or_else(|| fresh(&f, 5, initial), |v| origins[*v].1.clone());
            let p = proposal(
                &mut store,
                &f,
                5,
                expected.clone(),
                &rows,
                initial,
                &extra,
                positive,
            );
            assert_eq!(
                check_root(&f, &store, p).unwrap().value(),
                Some(&expected),
                "profile {encoded}, initial {initial:?}"
            );
        }
    }
}

#[test]
fn history_larger_than_a_megabyte_is_iterative_and_not_silently_truncated() {
    let f = fixture(7);
    let mut store = Store::new();
    let origin = put(&mut store, Material::Origin(proof(&f)));
    let mut history = None;
    for _ in 0..16_384 {
        history = Some(page(&mut store, &f, 1, history, Entry::Witness(origin)));
    }
    let root = snapshot(&mut store, &f, 1, 5, history);
    assert!(store.values().map(EncodeSize::encode_size).sum::<usize>() > 1024 * 1024);
    assert_eq!(
        check_root(&f, &store, root).unwrap().phase(),
        Phase::Snapshot
    );
    let missing = history.unwrap();
    store.remove(&missing);
    assert_eq!(
        check_root(&f, &store, root).unwrap_err(),
        RecoveryError::Missing(missing)
    );
}

#[test]
fn recursive_prior_rpcs_preserve_original_value_across_many_carriers() {
    let f = fixture(7);
    let mut store = Store::new();
    let rows = snapshots(&mut store, &f, 5, &[None; 7]);
    let value = fresh(&f, 5, &[0, 1, 2, 3, 4]);
    let p = proposal(
        &mut store,
        &f,
        5,
        value.clone(),
        &rows,
        &[0, 1, 2, 3, 4],
        &[],
        None,
    );
    let mut prepared = rpc(&mut store, &f, p);
    for b in 6..=133 {
        let history = page(&mut store, &f, 1, None, Entry::Witness(prepared));
        let mut histories = [None; 7];
        histories[1] = Some(history);
        let rows = snapshots(&mut store, &f, b, &histories);
        let p = proposal(
            &mut store,
            &f,
            b,
            value.clone(),
            &rows,
            &[0, 1, 2, 3, 4],
            &[],
            None,
        );
        prepared = rpc(&mut store, &f, p);
    }
    let checked = check_root(&f, &store, prepared).unwrap();
    assert_eq!(checked.round(), round(133));
    assert_eq!(checked.value(), Some(&value));
    assert_eq!(checked.phase(), Phase::Prepared);
    // Every material's exact codec survives without recursive decoding.
    let cfg = (LIMITS, f.verifier.certificate_codec_config());
    let mut ids = BTreeSet::new();
    for (id, body) in &store {
        let bytes = body.encode();
        let decoded = Material::<S, Digest>::decode_cfg(bytes.clone(), &cfg).unwrap();
        assert_eq!(decoded.encode(), bytes);
        assert_eq!(decoded.id::<Sha256>(), *id);
        ids.insert(*id);
    }
    assert_eq!(ids.len(), store.len());
}

#[test]
fn only_five_honest_identities_can_complete_recovery_when_both_faults_are_silent() {
    let f = fixture(7);
    let mut store = Store::new();
    let honest = [1, 3, 4, 5, 6];
    let mut rows = [Digest::from([0; 32]); 7];
    for id in honest {
        rows[id] = snapshot(&mut store, &f, id, 5, None);
    }
    let value = fresh(&f, 5, &honest);
    let p = proposal(&mut store, &f, 5, value.clone(), &rows, &honest, &[], None);
    let prepared = rpc_with(&mut store, &f, p, &honest);
    let terminal = put(
        &mut store,
        Material::Terminal {
            authority: prepared,
            quorum: phase_quorum(&f, 5, Kind::Commit(value.id::<Sha256>()), &honest),
        },
    );
    let checked = check_root(&f, &store, terminal).unwrap();
    assert_eq!(checked.phase(), Phase::Terminal);
    assert_eq!(checked.value(), Some(&value));
    assert!(store.values().all(|body| match body {
        Material::Snapshot(s) => honest.contains(&usize::from(s.attestation.signer)),
        _ => true,
    }));
}

#[test]
fn full_fork_recovery_certificates_need_no_faulty_recovery_signatures() {
    let f = fixture(7);
    let mut store = Store::new();
    let origins = two_origins(&mut store, &f);
    let honest = [1, 3, 4, 5, 6];
    for (profile, carry) in [
        ([Some(0), Some(0), Some(1), Some(1), None], false),
        ([Some(0), Some(0), Some(0), Some(1), None], true),
    ] {
        let histories = fork_histories(&mut store, &f, &origins, profile);
        let mut rows = [Digest::from([0; 32]); 7];
        for id in honest {
            rows[id] = snapshot(&mut store, &f, id, 5, histories[id]);
        }
        let positive = positive(&mut store, &[origins[0].0, origins[1].0]);
        let value = if carry {
            origins[0].1.clone()
        } else {
            fresh(&f, 5, &honest)
        };
        let p = proposal(
            &mut store,
            &f,
            5,
            value.clone(),
            &rows,
            &honest,
            &[],
            positive,
        );
        let prepared = rpc_with(&mut store, &f, p, &honest);
        let terminal = put(
            &mut store,
            Material::Terminal {
                authority: prepared,
                quorum: phase_quorum(&f, 5, Kind::Commit(value.id::<Sha256>()), &honest),
            },
        );
        assert_eq!(
            check_root(&f, &store, terminal).unwrap().phase(),
            Phase::Terminal
        );
    }
}

#[test]
fn highest_of_two_prior_rpcs_is_selected_independent_of_proof_arrival_order() {
    let f = fixture(7);
    let mut store = Store::new();
    let rows5 = snapshots(&mut store, &f, 5, &[None; 7]);
    let value5 = fresh(&f, 5, &[0, 1, 2, 3, 4]);
    let p5 = proposal(
        &mut store,
        &f,
        5,
        value5.clone(),
        &rows5,
        &[0, 1, 2, 3, 4],
        &[],
        None,
    );
    let rpc5 = rpc(&mut store, &f, p5);
    // PREPARE signers retained their own reservations and J, but need not
    // have received the assembled RPC5. No COMMIT exists at carrier five.
    let mut histories = [None; 7];
    for (owner, history) in histories.iter_mut().enumerate().take(5) {
        *history = Some(page(
            &mut store,
            &f,
            owner,
            None,
            Entry::Authorization {
                message: Message {
                    slot: slot(&f).id::<Sha256>(),
                    round: round(5),
                    leader: leader(round(5)).unwrap(),
                    kind: Kind::Prepare(value5.id::<Sha256>()),
                },
                evidence: p5,
            },
        ));
    }
    let rows6 = snapshots(&mut store, &f, 6, &histories);
    let value6 = fresh(&f, 6, &[0, 1, 2, 3, 4]);
    assert_ne!(value5.id::<Sha256>(), value6.id::<Sha256>());
    let p6 = proposal(
        &mut store,
        &f,
        6,
        value6.clone(),
        &rows6,
        &[0, 1, 2, 3, 4],
        &[],
        None,
    );
    let rpc6 = rpc(&mut store, &f, p6);
    for (owner, history) in histories.iter_mut().enumerate().take(5) {
        *history = Some(page(
            &mut store,
            &f,
            owner,
            *history,
            Entry::Authorization {
                message: Message {
                    slot: slot(&f).id::<Sha256>(),
                    round: round(6),
                    leader: leader(round(6)).unwrap(),
                    kind: Kind::Prepare(value6.id::<Sha256>()),
                },
                evidence: p6,
            },
        ));
    }
    let rows7 = snapshots(&mut store, &f, 7, &histories);
    for order in [[rpc5, rpc6], [rpc6, rpc5]] {
        let positive = positive(&mut store, &order);
        let p7 = proposal(
            &mut store,
            &f,
            7,
            value6.clone(),
            &rows7,
            &[0, 1, 2, 3, 4],
            &[],
            positive,
        );
        assert_eq!(check_root(&f, &store, p7).unwrap().value(), Some(&value6));
        let wrong = proposal(
            &mut store,
            &f,
            7,
            value5.clone(),
            &rows7,
            &[0, 1, 2, 3, 4],
            &[],
            positive,
        );
        assert!(check_root(&f, &store, wrong).is_err());
    }
}

#[test]
fn lower_commit_reservation_exposes_rpc_before_late_positive_forwarding() {
    let f = fixture(7);
    let mut store = Store::new();
    let origins = two_origins(&mut store, &f);
    let rows5 = snapshots(&mut store, &f, 5, &[None; 7]);
    let value = fresh(&f, 5, &[0, 1, 2, 3, 4]);
    let p5 = proposal(
        &mut store,
        &f,
        5,
        value.clone(),
        &rows5,
        &[0, 1, 2, 3, 4],
        &[],
        None,
    );
    let prepared = rpc(&mut store, &f, p5);
    let mut histories = [None; 7];
    for (owner, history) in histories.iter_mut().enumerate().take(5) {
        *history = Some(page(
            &mut store,
            &f,
            owner,
            None,
            Entry::Authorization {
                message: Message {
                    slot: slot(&f).id::<Sha256>(),
                    round: round(5),
                    leader: leader(round(5)).unwrap(),
                    kind: Kind::Prepare(value.id::<Sha256>()),
                },
                evidence: p5,
            },
        ));
    }
    histories[1] = Some(page(
        &mut store,
        &f,
        1,
        histories[1],
        Entry::Authorization {
            message: Message {
                slot: slot(&f).id::<Sha256>(),
                round: round(5),
                leader: leader(round(5)).unwrap(),
                kind: Kind::Commit(value.id::<Sha256>()),
            },
            evidence: prepared,
        },
    ));
    let rows6 = snapshots(&mut store, &f, 6, &histories);
    let forks = positive(&mut store, &[origins[0].0, origins[1].0]);
    // This Q includes the honest committer; its own frozen history supplies RPC5.
    let p6 = proposal(
        &mut store,
        &f,
        6,
        value.clone(),
        &rows6,
        &[0, 1, 2, 3, 4],
        &[],
        forks,
    );
    assert_eq!(check_root(&f, &store, p6).unwrap().value(), Some(&value));
    // A different initial Q has no committer or RPC. It cannot skip the missing
    // original honest reply, until a positive RPC is forwarded separately.
    let no_committer = [0, 2, 3, 4, 5];
    let p6 = proposal(
        &mut store,
        &f,
        6,
        value.clone(),
        &rows6,
        &no_committer,
        &[],
        forks,
    );
    assert_eq!(
        check_root(&f, &store, p6).unwrap_err(),
        RecoveryError::NeedSnapshots(vec![Participant::new(1), Participant::new(6)])
    );
    let proofs = positive(&mut store, &[origins[0].0, origins[1].0, prepared]);
    let p6 = proposal(
        &mut store,
        &f,
        6,
        value.clone(),
        &rows6,
        &no_committer,
        &[],
        proofs,
    );
    assert_eq!(check_root(&f, &store, p6).unwrap().value(), Some(&value));
}

#[test]
fn recovery_proposal_requires_elected_leaders_signature_over_exact_frozen_j() {
    let f = fixture(7);
    let mut store = Store::new();
    let rows = snapshots(&mut store, &f, 5, &[None; 7]);
    let value = fresh(&f, 5, &[0, 1, 2, 3, 4]);
    let p = proposal(&mut store, &f, 5, value, &rows, &[0, 1, 2, 3, 4], &[], None);
    let Material::Proposal {
        proposal: original,
        endorsement,
    } = store[&p].clone()
    else {
        unreachable!()
    };
    let wrong_signer = Signed::sign(&f.schemes[0], endorsement.message.clone()).unwrap();
    let wrong = put(
        &mut store,
        Material::Proposal {
            proposal: original.clone(),
            endorsement: wrong_signer,
        },
    );
    assert!(check_root(&f, &store, wrong).is_err());
    let mut changed_j = original.clone();
    changed_j.extra = vec![rows[5]];
    let wrong = put(
        &mut store,
        Material::Proposal {
            proposal: changed_j,
            endorsement: endorsement.clone(),
        },
    );
    assert!(check_root(&f, &store, wrong).is_err());
    let wrong_phase = Signed::sign(
        &f.schemes[1],
        Message {
            kind: Kind::Select {
                core: original.id::<Sha256>(),
                value: original.value.id::<Sha256>(),
            },
            ..endorsement.message
        },
    )
    .unwrap();
    let wrong = put(
        &mut store,
        Material::Proposal {
            proposal: original,
            endorsement: wrong_phase,
        },
    );
    assert!(check_root(&f, &store, wrong).is_err());
}

#[test]
fn new_material_codec_rejects_unknown_versions_tags_and_oversized_snapshot_vectors() {
    let f = fixture(7);
    let mut store = Store::new();
    let rows = snapshots(&mut store, &f, 5, &[None; 7]);
    let value = fresh(&f, 5, &[0, 1, 2, 3, 4]);
    let p = proposal(&mut store, &f, 5, value, &rows, &[0, 1, 2, 3, 4], &[], None);
    let cfg = (LIMITS, f.verifier.certificate_codec_config());
    let bytes = store[&p].encode();
    for end in 0..bytes.len() {
        assert!(Material::<S, Digest>::decode_cfg(bytes.slice(..end), &cfg).is_err());
    }
    for (offset, value) in [(0, 99), (1, 99)] {
        let mut invalid = bytes.to_vec();
        invalid[offset] = value;
        assert!(Material::<S, Digest>::decode_cfg(Bytes::from(invalid), &cfg).is_err());
    }
    let Material::Proposal {
        proposal: mut invalid,
        endorsement,
    } = store[&p].clone()
    else {
        unreachable!()
    };
    invalid.initial = vec![rows[0]; 8];
    let invalid = Material::Proposal {
        proposal: invalid,
        endorsement,
    };
    assert!(Material::<S, Digest>::decode_cfg(invalid.encode(), &cfg).is_err());
}

struct RecoveryEvidenceConformance;
impl Conformance for RecoveryEvidenceConformance {
    async fn commit(seed: u64) -> Vec<u8> {
        let f = ed25519::fixture(
            &mut TestRng::new(seed),
            b"_COMMONWARE_CONSENSUS_AGREEMENT_RECOVERY_TEST",
            7,
        );
        let mut store = Store::new();
        let origins = two_origins(&mut store, &f);
        let histories = fork_histories(
            &mut store,
            &f,
            &origins,
            [Some(0), Some(0), Some(1), Some(1), None],
        );
        let rows = snapshots(&mut store, &f, 5, &histories);
        let value = fresh(&f, 5, &[0, 1, 2, 3, 4]);
        let p = proposal(
            &mut store,
            &f,
            5,
            value.clone(),
            &rows,
            &[0, 1, 2, 3, 4],
            &[5, 6],
            None,
        );
        let prepared = rpc(&mut store, &f, p);
        put(
            &mut store,
            Material::Terminal {
                authority: prepared,
                quorum: phase_quorum(&f, 5, Kind::Commit(value.id::<Sha256>()), &[0, 1, 2, 3, 4]),
            },
        );
        put(
            &mut store,
            Material::Terminal {
                authority: origins[0].0,
                quorum: phase_quorum(
                    &f,
                    4,
                    Kind::FastFinal(origins[0].1.id::<Sha256>()),
                    &[0, 1, 2, 3, 4],
                ),
            },
        );
        positive(&mut store, &[prepared, origins[0].0]);
        store
            .values()
            .map(|m| m.encode())
            .collect::<Vec<_>>()
            .encode()
            .to_vec()
    }
}
conformance_tests! { RecoveryEvidenceConformance => 32 }
