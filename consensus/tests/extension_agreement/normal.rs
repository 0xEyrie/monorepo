//! Joint-owner crypto and journal tests; not an activated native Mode/Actor.
use super::{recovery::leader, *};
use commonware_codec::Write as _;
use commonware_consensus::{
    Viewable as _,
    simplex::extension::{
        agreement::{
            issuance::{Action, Error as IssuanceError, State},
            normal::{self, Reservation, Vote},
            recovery::{Entry, Material, Phase},
        },
        vote,
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
fn reserve(state: &mut State<S, Digest>, p: &Proof) -> Reservation<Digest> {
    state
        .reserve_normal::<Sha256, _>(&mut TestRng::new(910), p, policy, leader, &Sequential)
        .unwrap()
}
fn pair(f: &Fixture<S>, p: &Proof, owner: usize) -> Vote<S, Digest> {
    let mut state = local(f, owner);
    let r = reserve(&mut state, p);
    state.sign_normal::<Sha256>(&r).unwrap()
}
fn check(p: &Vote<S, Digest>, f: &Fixture<S>, origin: &Proof) -> bool {
    p.verify_attestations::<Sha256, _>(&mut TestRng::new(911), &f.verifier, origin, &Sequential)
}

#[test]
fn any_five_complete_pairs_build_both_real_quorums_from_same_owners() {
    let f = fixture(7);
    let p = proof(&f);
    let pairs = [2, 3, 4, 5, 6].map(|owner| pair(&f, &p, owner));
    for pair in &pairs {
        assert!(check(pair, &f, &p));
    }
    let (native, agreement) = normal::assemble::<Sha256, _, _, _>(
        &mut TestRng::new(912),
        &f.verifier,
        &p,
        non_empty![@pairs.into_iter()],
        &Sequential,
    )
    .unwrap();
    assert!(native.verify(&mut TestRng::new(913), &f.verifier, &Sequential));
    assert_eq!(native.statement.extension, p.value.id::<Sha256>());
    assert_eq!(native.statement.parent, slot(&f).parent);
    assert_eq!(native.statement.ballot, round(4));
    p.verify_finalization::<Sha256, _>(
        &mut TestRng::new(914),
        &f.verifier,
        &slot(&f),
        Participant::new(0),
        LIMITS,
        policy,
        &agreement,
        &Sequential,
    )
    .unwrap();
    // The unchanged full proof verifier accepts an actual FAST terminal body.
    let mut store = recovery::Store::new();
    let origin = recovery::put(&mut store, Material::Origin(p));
    let terminal = recovery::put(
        &mut store,
        Material::Terminal {
            authority: origin,
            quorum: agreement,
        },
    );
    assert_eq!(
        recovery::check_root(&f, &store, terminal).unwrap().phase(),
        Phase::Terminal
    );
}

#[test]
fn swapped_owner_or_subject_rejects_even_when_both_signatures_are_valid() {
    let f = fixture(7);
    let p = proof(&f);
    let a = pair(&f, &p, 0);
    let b = pair(&f, &p, 1);
    let swapped = Vote {
        native: a.native.clone(),
        agreement: b.agreement,
        origin: a.origin,
    };
    assert!(
        swapped
            .native
            .verify(&mut TestRng::new(915), &f.verifier, &Sequential)
    );
    assert!(
        swapped
            .agreement
            .verify(&mut TestRng::new(916), &f.verifier, &Sequential)
    );
    assert!(!check(&swapped, &f, &p));
    let mut other = a.native.statement.clone();
    other.extension = Digest::from([99; 32]);
    let other = Vote {
        native: vote::Vote::sign(&f.schemes[0], other).unwrap(),
        agreement: a.agreement.clone(),
        origin: a.origin,
    };
    assert!(
        other
            .native
            .verify(&mut TestRng::new(917), &f.verifier, &Sequential)
    );
    assert!(!check(&other, &f, &p));
    let mut bad_origin = a;
    bad_origin.origin = Digest::from([98; 32]);
    assert!(!check(&bad_origin, &f, &p));
}

#[test]
fn same_keys_in_a_foreign_namespace_cannot_supply_either_half() {
    let f = fixture(7);
    let p = proof(&f);
    let original = pair(&f, &p, 0);
    let foreign = S::signer(
        b"_COMMONWARE_CONSENSUS_NORMAL_FOREIGN_NAMESPACE",
        f.verifier.participants().clone(),
        f.private_keys[0].clone(),
    )
    .unwrap();
    let native = vote::Vote::sign(&foreign, original.native.statement.clone()).unwrap();
    let agreement = Signed::sign(&foreign, original.agreement.message.clone()).unwrap();
    assert!(!check(
        &Vote {
            native: native.clone(),
            agreement: original.agreement.clone(),
            origin: original.origin
        },
        &f,
        &p
    ));
    assert!(!check(
        &Vote {
            native: original.native,
            agreement: agreement.clone(),
            origin: original.origin
        },
        &f,
        &p
    ));
    assert!(!check(
        &Vote {
            native,
            agreement,
            origin: original.origin
        },
        &f,
        &p
    ));
}

#[test]
fn distinct_identity_quorum_and_complete_pairs_are_required() {
    let f = fixture(7);
    let p = proof(&f);
    for ids in [
        &[0, 1, 2, 3][..],
        &[0, 1, 2, 3, 3][..],
        &[0, 1, 2, 3, 4, 5][..],
        &[0, 1, 2, 3, 4, 5, 6][..],
    ] {
        let pairs = ids
            .iter()
            .map(|owner| pair(&f, &p, *owner))
            .collect::<Vec<_>>();
        assert!(
            normal::assemble::<Sha256, _, _, _>(
                &mut TestRng::new(918),
                &f.verifier,
                &p,
                non_empty![@pairs.into_iter()],
                &Sequential,
            )
            .is_err()
        );
    }
    let mut pairs = (0..5).map(|owner| pair(&f, &p, owner)).collect::<Vec<_>>();
    pairs[4].agreement = pairs[3].agreement.clone();
    assert!(
        normal::assemble::<Sha256, _, _, _>(
            &mut TestRng::new(919),
            &f.verifier,
            &p,
            non_empty![@pairs.into_iter()],
            &Sequential,
        )
        .is_err()
    );
}

#[test]
fn malformed_origin_or_policy_never_stages_a_normal_choice() {
    let f = fixture(7);
    let p = proof(&f);
    let mut bads = vec![p.clone(); 4];
    bads[0].value.direction = Bytes::from_static(b"wrong");
    bads[1].firsts[0] = bads[1].firsts[1].clone();
    bads[2].value.slot.parent = Digest::from([93; 32]);
    bads[3].core.leader = Participant::new(1);
    for p in bads {
        let mut state = local(&f, 0);
        assert!(
            state
                .reserve_normal::<Sha256, _>(
                    &mut TestRng::new(920),
                    &p,
                    policy,
                    leader,
                    &Sequential,
                )
                .is_err()
        );
        assert!(state.records().is_empty());
        assert_eq!(state.floor(), round(4));
    }
    for (policy_ok, leader_ok) in [(false, true), (true, false)] {
        let mut state = local(&f, 0);
        assert!(
            state
                .reserve_normal::<Sha256, _>(
                    &mut TestRng::new(921),
                    &p,
                    |_| policy_ok,
                    |r| leader_ok.then(|| leader(r)).flatten(),
                    &Sequential,
                )
                .is_err()
        );
        assert!(state.records().is_empty());
    }
}

#[test]
fn unsigned_normal_reservation_is_already_in_complete_recovery_history() {
    let f = fixture(7);
    let p = proof(&f);
    let mut state = local(&f, 6);
    let r = reserve(&mut state, &p);
    let frozen = state
        .recover::<Sha256>(round(5), Participant::new(1), None, leader)
        .unwrap();
    assert_eq!(frozen.pages.len(), 1);
    assert!(
        matches!(&frozen.pages[0].entry, Entry::Authorization { message, evidence }
            if message.kind == Kind::FastFinal(p.value.id::<Sha256>())
                && Some(*evidence) == match r.agreement().action() {
                    Action::Reserve { authority, .. } => *authority,
                    _ => None,
                }
        )
    );
    assert_eq!(
        state.sign_normal::<Sha256>(&r).unwrap_err(),
        IssuanceError::Floor
    );
    assert!(
        state
            .reserve_normal::<Sha256, _>(&mut TestRng::new(923), &p, policy, leader, &Sequential,)
            .is_err()
    );
    let mut replay = local(&f, 6);
    replay.restore_normal::<Sha256>(&r, leader).unwrap();
    replay.restore::<Sha256>(&frozen.record, leader).unwrap();
    assert_eq!(
        replay.sign_normal::<Sha256>(&r).unwrap_err(),
        IssuanceError::Floor
    );
}

#[test]
fn genuine_terminal_closes_normal_signer_without_relabeling_native_signatures() {
    let f = fixture(7);
    let p = proof(&f);
    let mut state = local(&f, 0);
    let r = reserve(&mut state, &p);
    let mut store = recovery::Store::new();
    let origin = recovery::put(&mut store, Material::Origin(p.clone()));
    let quorum = quorum(
        &f,
        votes(
            &f,
            Kind::FastFinal(p.value.id::<Sha256>()),
            &[0, 1, 2, 3, 4],
        ),
    )
    .unwrap();
    let terminal = recovery::put(
        &mut store,
        Material::Terminal {
            authority: origin,
            quorum,
        },
    );
    let closed = state
        .retain::<Sha256, _>(
            &mut TestRng::new(922),
            terminal,
            |id| store.get(id),
            &Sequential,
            policy,
            leader,
        )
        .unwrap();
    assert_eq!(
        state.sign_normal::<Sha256>(&r).unwrap_err(),
        IssuanceError::Closed
    );
    assert!(
        state
            .reserve_normal::<Sha256, _>(&mut TestRng::new(924), &p, policy, leader, &Sequential,)
            .is_err()
    );
    let mut replay = local(&f, 0);
    replay.restore_normal::<Sha256>(&r, leader).unwrap();
    replay.restore::<Sha256>(&closed, leader).unwrap();
    assert_eq!(
        replay.sign_normal::<Sha256>(&r).unwrap_err(),
        IssuanceError::Closed
    );
}

#[test]
fn retry_cannot_replace_the_retained_origin_authority_or_old_value() {
    let f = fixture(7);
    let p = proof(&f);
    let mut state = local(&f, 0);
    let old = state
        .reserve::<Sha256>(
            Message {
                slot: slot(&f).id::<Sha256>(),
                round: round(4),
                leader: Participant::new(0),
                kind: Kind::FastFinal(p.value.id::<Sha256>()),
            },
            Some(Digest::from([88; 32])),
            None,
            leader,
        )
        .unwrap();
    assert!(matches!(
        state.reserve_normal::<Sha256, _>(&mut TestRng::new(925), &p, policy, leader, &Sequential),
        Err(normal::Error::Issuance(IssuanceError::Authority))
    ));
    assert_eq!(state.records(), &[old]);
    let mut other = local(&f, 1);
    let first = reserve(&mut other, &p);
    assert_eq!(reserve(&mut other, &p), first);
    let mut changed = p.clone();
    let Kind::First { report, .. } = &mut changed.firsts[2].message.kind else {
        unreachable!()
    };
    *report = Some(Bytes::from_static(b"different"));
    changed.firsts[2] = Signed::sign(&f.schemes[2], changed.firsts[2].message.clone()).unwrap();
    select(&f, &mut changed);
    assert!(matches!(
        other.reserve_normal::<Sha256, _>(
            &mut TestRng::new(926),
            &changed,
            policy,
            leader,
            &Sequential,
        ),
        Err(normal::Error::Issuance(IssuanceError::Conflict))
    ));
    assert_eq!(other.records(), &[first.agreement().clone()]);
}

fn decoded(subject: &vote::Statement<Digest>, r: &Reservation<Digest>) -> Reservation<Digest> {
    let mut bytes = Vec::new();
    1u8.write(&mut bytes);
    subject.write(&mut bytes);
    r.agreement().write(&mut bytes);
    Reservation::decode(Bytes::from(bytes)).unwrap()
}

#[test]
fn decoded_joint_mismatch_or_foreign_owner_rejects_before_mutation() {
    let f = fixture(7);
    let p = proof(&f);
    let r = reserve(&mut local(&f, 0), &p);
    let mut subjects = vec![r.subject().clone(); 6];
    subjects[0].extension = Digest::from([80; 32]);
    subjects[1].domain = Digest::from([81; 32]);
    subjects[2].parent = Digest::from([82; 32]);
    subjects[3].ballot = round(5);
    subjects[4].proposal.parent = View::new(2);
    subjects[5].proposal.round = round(3);
    for subject in subjects {
        let bad = decoded(&subject, &r);
        let mut state = local(&f, 0);
        assert!(state.restore_normal::<Sha256>(&bad, leader).is_err());
        assert!(state.records().is_empty());
    }
    let mut other = local(&f, 1);
    assert!(other.restore_normal::<Sha256>(&r, leader).is_err());
    assert!(other.records().is_empty());
    let own = reserve(&mut other, &p);
    // Same native T does not let another owner use the stored M1 half.
    assert_eq!(own.subject(), r.subject());
    assert!(other.sign_normal::<Sha256>(&r).is_err());
}

#[test]
fn normal_codecs_reject_missing_halves_truncation_and_versions() {
    let f = fixture(7);
    let p = proof(&f);
    let mut state = local(&f, 0);
    let r = reserve(&mut state, &p);
    let v = state.sign_normal::<Sha256>(&r).unwrap();
    let bytes = r.encode();
    assert_eq!(bytes.len(), r.encode_size());
    assert_eq!(Reservation::<Digest>::decode(bytes.clone()).unwrap(), r);
    for n in 0..bytes.len() {
        assert!(Reservation::<Digest>::decode(bytes.slice(..n)).is_err());
    }
    let bytes = v.encode();
    assert_eq!(bytes.len(), v.encode_size());
    let decoded = Vote::<S, Digest>::decode(bytes.clone()).unwrap();
    assert!(check(&decoded, &f, &p));
    for n in 0..bytes.len() {
        assert!(Vote::<S, Digest>::decode(bytes.slice(..n)).is_err());
    }
    let mut bad = bytes.to_vec();
    bad[0] = 99;
    assert!(Vote::<S, Digest>::decode(Bytes::from(bad)).is_err());
    let mut bad = r.encode().to_vec();
    bad[0] = 99;
    assert!(Reservation::<Digest>::decode(Bytes::from(bad)).is_err());
    assert!(Vote::<S, Digest>::decode(v.native.encode()).is_err());
}

#[test]
fn joint_wal_restart_after_either_signature_restores_both_unsigned_choices() {
    for signed_halves in 0..=2 {
        let f = fixture(7);
        let p = proof(&f);
        let mut state = local(&f, 0);
        let record = reserve(&mut state, &p);
        let written = record.clone();
        let (_, checkpoint) =
            deterministic::Runner::default().start_and_recover(move |context| async move {
                let mut journal = Journal::<_, Reservation<Digest>>::init(
                    context.child("wal"),
                    JournalConfig {
                        partition: "joint-normal".into(),
                        compression: None,
                        codec_config: (),
                        page_cache: CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(8)),
                        write_buffer: NZUsize!(1024),
                    },
                )
                .await
                .unwrap();
                journal = journal
                    .append(written.view().get(), &written)
                    .await
                    .unwrap()
                    .0;
                let _journal = journal.sync(written.view().get()).await.unwrap();
                // Deliberately interrupt production after the durable joint item,
                // before a complete signed pair has been persisted or published.
                if signed_halves >= 1 {
                    state.sign_reserved(written.agreement()).unwrap();
                }
                if signed_halves >= 2 {
                    vote::Vote::sign(&f.schemes[0], written.subject().clone()).unwrap();
                }
            });
        let f = fixture(7);
        let p = proof(&f);
        deterministic::Runner::from(checkpoint).start(move |context| async move {
            let journal = Journal::<_, Reservation<Digest>>::init(
                context.child("wal"),
                JournalConfig {
                    partition: "joint-normal".into(),
                    compression: None,
                    codec_config: (),
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
            let mut replay = local(&f, 0);
            let got = stream.next().await.unwrap().unwrap().3;
            assert_eq!(got, record);
            replay.restore_normal::<Sha256>(&got, leader).unwrap();
            assert!(stream.next().await.is_none());
            drop(stream.finish().unwrap());
            let pair = replay.sign_normal::<Sha256>(&got).unwrap();
            assert!(check(&pair, &f, &p));
            let snapshot = replay
                .recover::<Sha256>(round(5), Participant::new(1), None, leader)
                .unwrap();
            assert_eq!(snapshot.pages.len(), 1);
            assert_eq!(
                replay.sign_normal::<Sha256>(&got).unwrap_err(),
                IssuanceError::Floor
            );
        });
    }
}

struct NormalConformance;
impl Conformance for NormalConformance {
    async fn commit(seed: u64) -> Vec<u8> {
        let f = ed25519::fixture(
            &mut TestRng::new(seed),
            b"_COMMONWARE_CONSENSUS_NORMAL_CONFORMANCE",
            7,
        );
        let p = proof(&f);
        let mut state = local(&f, 6);
        let r = reserve(&mut state, &p);
        let v = state.sign_normal::<Sha256>(&r).unwrap();
        [r.encode(), v.encode()].concat()
    }
}
conformance_tests! {NormalConformance=>32}
