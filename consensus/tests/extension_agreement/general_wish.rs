//! Native-owner WISH primitives, not an activated timer schedule or pacemaker.
use super::*;
use commonware_consensus::{
    Viewable,
    simplex::{
        extension::agreement::general::{
            self as g, entry,
            issuance::{Action, Material, Record, State, WishCause},
            recovery as r,
        },
        types::Notarization,
    },
};
use commonware_runtime::{
    Clock, ReadOptions, Runner, Supervisor as _, buffer::paged::CacheRef, deterministic,
};
use commonware_storage::journal::segmented::variable::{Config as JournalConfig, Journal};
use commonware_utils::{NZU16, NZUsize};
use std::{cell::Cell, collections::BTreeMap, time::Duration};

const LIMITS: g::Limits = g::Limits {
    report_bytes: 128,
    order_bytes: 128,
    build_bytes: 256,
    material_bytes: 256,
    origin_bytes: g::MAX_EVIDENCE_BYTES,
};
const BOUNDS: entry::Bounds = entry::Bounds {
    nodes: 256,
    encoded_bytes: 16 * 1024 * 1024,
    signatures: 16384,
    depth: 64,
};
type EProof = entry::Proof<S, Digest>;
type Amp = entry::Amplification<S, Digest>;
fn input() -> Digest {
    Digest::from([191; 32])
}
fn core(f: &Fixture<S>) -> g::Core<Digest> {
    let c = g::Committee::new(f.schemes.len()).unwrap();
    g::Core {
        slot: g::Slot {
            profile: Digest::from([192; 32]),
            domain: Digest::from([193; 32]),
            roster: g::Slot::roster::<Sha256, _>(&f.verifier),
            cut: 31,
            proposal: Proposal::new(round(4), View::new(3), Digest::from([194; 32])),
            parent: g::NativeParent::Proposal {
                round: round(3),
                digest: Digest::from([195; 32]),
            },
        },
        leader: Participant::new(c.len() as u32 - 1),
        followers: (0..c.len() as u32 - 1)
            .filter(|p| *p != 1)
            .take(c.quorum() - 1)
            .map(Participant::new)
            .collect(),
    }
}
fn initial(f: &Fixture<S>, c: &g::Core<Digest>, offset: usize) -> EProof {
    let committee = g::Committee::new(f.schemes.len()).unwrap();
    let votes: Vec<_> = f
        .schemes
        .iter()
        .skip(offset)
        .take(committee.quorum())
        .map(|s| Notarize::sign(s, c.slot.proposal.clone()).unwrap())
        .collect();
    EProof::Initial {
        target: entry::Target {
            core: c.id::<Sha256>(),
            input: input(),
            attempt: 0,
            ballot: round(5),
            leader: Participant::new(0),
        },
        notarization: Notarization::from_notarizes(&f.verifier, non_empty![@&votes], &Sequential)
            .unwrap(),
    }
}
fn amplification(f: &Fixture<S>, c: &g::Core<Digest>, a: &EProof, b: &EProof) -> Amp {
    let committee = g::Committee::new(f.schemes.len()).unwrap();
    let target = a.target().successor(committee).unwrap();
    let wishes = f
        .schemes
        .iter()
        .enumerate()
        .skip(committee.len() - (committee.faults() + 1))
        .map(|(i, s)| {
            g::Signed::sign(
                s,
                g::Message {
                    slot: c.slot.id::<Sha256>(),
                    round: target.ballot,
                    leader: target.leader,
                    kind: g::Kind::Wish(entry::Wish {
                        target: target.clone(),
                        predecessor: if i % 2 == 0 {
                            a.artifact_id::<Sha256>()
                        } else {
                            b.artifact_id::<Sha256>()
                        },
                    }),
                },
                LIMITS,
            )
            .unwrap()
        })
        .collect();
    Amp { target, wishes }
}
fn entries(a: &EProof, b: &EProof) -> BTreeMap<Digest, EProof> {
    [
        (a.artifact_id::<Sha256>(), a.clone()),
        (b.artifact_id::<Sha256>(), b.clone()),
    ]
    .into_iter()
    .collect()
}
fn checked_entry<'a>(
    ctx: &g::VerificationContext<S>,
    c: &'a g::Core<Digest>,
    p: &'a EProof,
    all: &'a BTreeMap<Digest, EProof>,
) -> entry::VerifiedEntry<'a, S, Digest> {
    entry::verify::<Sha256, _, _, _>(
        &mut TestRng::new(5101),
        ctx,
        c,
        input(),
        p,
        LIMITS,
        BOUNDS,
        |id| all.get(id),
        &Sequential,
    )
    .unwrap()
}
fn checked_amp<'a>(
    ctx: &g::VerificationContext<S>,
    c: &'a g::Core<Digest>,
    p: &'a Amp,
    all: &'a BTreeMap<Digest, EProof>,
) -> entry::VerifiedAmplification<'a, S, Digest> {
    entry::verify_amplification::<Sha256, _, _, _>(
        &mut TestRng::new(5102),
        ctx,
        c,
        input(),
        p,
        LIMITS,
        BOUNDS,
        |id| all.get(id),
        &Sequential,
    )
    .unwrap()
}
fn restore(
    state: &mut State<S, Digest>,
    record: &Record<Digest>,
    material: Material<'_, S, Digest>,
) {
    state
        .restore::<Sha256, _>(
            &mut TestRng::new(5103),
            record,
            material,
            |_| true,
            |_, _| true,
            &Sequential,
        )
        .unwrap();
}
fn local(f: &Fixture<S>, c: &g::Core<Digest>) -> State<S, Digest> {
    State::new::<Sha256>(
        f.schemes[f.schemes.len() - 1].clone(),
        c.clone(),
        input(),
        LIMITS,
    )
    .unwrap()
}

#[test]
fn f_plus_one_amplification_is_not_entry_and_preserves_exact_own_alias_and_cause() {
    deterministic::Runner::seeded(5116).start(|clock| async move {
    for n in [4, 7, 8, 9, 10, 11, 12, 13, 16, 31, 64] {
        let f = fixture(n);
        let c = core(&f);
        let a = initial(&f, &c, 0);
        let b = initial(&f, &c, 1);
        let all = entries(&a, &b);
        let raw = amplification(&f, &c, &a, &b);
        let committee = g::Committee::new(n as usize).unwrap();
        assert_eq!(raw.wishes.len(), committee.faults() + 1);
        assert!(raw.wishes.len() < committee.quorum());
        assert_eq!(
            raw.wishes.last().unwrap().attestation.signer,
            Participant::new(n - 1)
        );
        assert!(
            EProof::Higher {
                target: raw.target.clone(),
                wishes: raw.wishes.clone()
            }
            .preflight(committee, LIMITS)
            .is_err()
        );
        let mut state = local(&f, &c);
        let ctx = state.verification_context();
        let own = checked_entry(&ctx, &c, &a, &all);
        let alias = checked_entry(&ctx, &c, &b, &all);
        let amp = checked_amp(&ctx, &c, &raw, &all);
        let enter = state.enter::<Sha256>(&own).unwrap();
        let lower = state.reserve_recover::<Sha256>(&own, None).unwrap();
        let before = state.records().len();
        let reserved = state.reserve_amplified_wish::<Sha256>(&own, &amp).unwrap();
        assert_eq!(state.records().len(), before + 1);
        assert_eq!(state.floor(), raw.target.ballot);
        let Action::AdvanceWish {
            snapshot,
            message,
            cause,
        } = reserved.action()
        else {
            panic!("atomic WISH");
        };
        assert_eq!(snapshot.count() as usize, before);
        assert_eq!(
            *cause,
            WishCause::Amplification(raw.artifact_id::<Sha256>())
        );
        assert!(
            matches!(&message.kind,g::Kind::Wish(w) if w.predecessor==a.artifact_id::<Sha256>() && w.target==raw.target)
        );
        assert!(state.sign_reserved(&lower).is_err());
        assert!(state.reserve_recover::<Sha256>(&own, None).is_ok()); // existing exact lower reservation only
        assert!(state.sign_reserved(&lower).is_err());
        let retry = state
            .reserve_amplified_wish::<Sha256>(&alias, &amp)
            .unwrap();
        assert_eq!(retry, reserved);
        assert_eq!(state.records().len(), before + 1);
        let signed = state.sign_reserved(&reserved).unwrap();
        state
            .record_signed::<Sha256, _>(&mut TestRng::new(5104), &reserved, &signed, &Sequential)
            .unwrap();
        let alternate = entry::Amplification {
            target: raw.target.clone(),
            wishes: f.schemes.iter().take(committee.faults() + 1).map(|s|
                g::Signed::sign(s, raw.wishes[0].message.clone(), LIMITS).unwrap()).collect(),
        };
        let alternate = checked_amp(&ctx, &c, &alternate, &all);
        assert_ne!(alternate.artifact_id(), amp.artifact_id());
        let count = state.records().len();
        let outbox = state.outbox(&reserved).unwrap().clone();
        assert_eq!(state.reserve_amplified_wish::<Sha256>(&alias, &alternate).unwrap(), reserved);
        // Receipt retrieval, not a fresh timeout permission or changed cause.
        assert_eq!(state.reserve_timeout_wish::<Sha256>(&clock, &alias).unwrap(), reserved);
        assert_eq!(state.records().len(), count);
        assert_eq!(state.outbox(&reserved), Some(&outbox));
        let mut replay = State::for_replay::<Sha256>(
            f.schemes[n as usize - 1].clone(),
            c.clone(),
            input(),
            LIMITS,
        )
        .unwrap();
        let ctx = replay.verification_context();
        let own2 = checked_entry(&ctx, &c, &a, &all);
        let amp2 = checked_amp(&ctx, &c, &raw, &all);
        for record in state.records() {
            let bytes = record.encode();
            assert_eq!(
                Record::<Digest>::decode_cfg(bytes.clone(), &LIMITS)
                    .unwrap()
                    .encode(),
                bytes
            );
            let m = match record.action() {
                Action::Enter { .. } | Action::Reserve { .. } => Material::Entry(&own2),
                Action::AdvanceWish { .. } => Material::Amplification {
                    predecessor: &own2,
                    amplification: &amp2,
                },
                _ => Material::None,
            };
            restore(&mut replay, record, m);
        }
        replay.finish_replay().unwrap();
        assert_eq!(replay.records(), state.records());
        assert_eq!(replay.outbox(&reserved), state.outbox(&reserved));
        assert!(replay.sign_reserved(&reserved).is_err());
        assert_eq!(enter.authority(), Some(a.artifact_id::<Sha256>()));
    }
    });
}

#[test]
fn amplification_rejects_identity_target_context_missing_and_budget_errors() {
    let f = fixture(10);
    let c = core(&f);
    let a = initial(&f, &c, 0);
    let b = initial(&f, &c, 1);
    let all = entries(&a, &b);
    let raw = amplification(&f, &c, &a, &b);
    let ctx = g::VerificationContext::new(f.verifier.clone());
    for mode in 0..7 {
        let mut bad = raw.clone();
        match mode {
            0 => {
                bad.wishes.pop();
            }
            1 => bad.wishes[1] = bad.wishes[0].clone(),
            2 => bad.wishes.swap(0, 1),
            3 => {
                let g::Kind::Wish(w) = &mut bad.wishes[0].message.kind else {
                    unreachable!()
                };
                w.target.input = Digest::from([0; 32]);
            }
            4 => bad.wishes[0].message.slot = Digest::from([0; 32]),
            5 => bad.wishes[0].attestation.signer = Participant::new(10),
            _ => bad.target.attempt = u64::MAX,
        }
        assert!(
            entry::verify_amplification::<Sha256, _, _, _>(
                &mut TestRng::new(5105),
                &ctx,
                &c,
                input(),
                &bad,
                LIMITS,
                BOUNDS,
                |id| all.get(id),
                &Sequential
            )
            .is_err()
        );
    }
    let calls = Cell::new(0);
    assert!(
        entry::verify_amplification::<Sha256, _, _, _>(
            &mut TestRng::new(5106),
            &ctx,
            &c,
            input(),
            &raw,
            LIMITS,
            entry::Bounds { nodes: 1, ..BOUNDS },
            |_| {
                calls.set(calls.get() + 1);
                None
            },
            &Sequential
        )
        .is_err()
    );
    assert_eq!(calls.get(), 0);
    assert!(
        entry::verify_amplification::<Sha256, _, _, _>(
            &mut TestRng::new(5107),
            &ctx,
            &c,
            input(),
            &raw,
            LIMITS,
            BOUNDS,
            |_| None,
            &Sequential
        )
        .is_err()
    );
    let mut state = local(&f, &c);
    let own_ctx = state.verification_context();
    let own = checked_entry(&own_ctx, &c, &a, &all);
    state.enter::<Sha256>(&own).unwrap();
    let foreign = checked_amp(&ctx, &c, &raw, &all);
    let before = state.records().to_vec();
    assert!(
        state
            .reserve_amplified_wish::<Sha256>(&own, &foreign)
            .is_err()
    );
    assert_eq!(state.records(), before);
}

#[test]
fn actual_clock_first_deadline_atomic_floor_and_same_target_q_entry_catchup() {
    deterministic::Runner::seeded(5108).start(|clock| async move {
        let f = fixture(10);
        let c = core(&f);
        let a = initial(&f, &c, 0);
        let b = initial(&f, &c, 1);
        let all = entries(&a, &b);
        let mut state = local(&f, &c);
        let ctx = state.verification_context();
        let own = checked_entry(&ctx, &c, &a, &all);
        let alias = checked_entry(&ctx, &c, &b, &all);
        let enter = state.enter::<Sha256>(&own).unwrap();
        let mut journal = Journal::<_, Record<Digest>>::init(
            clock.child("wish_wal_open"),
            JournalConfig {
                partition: "g1-wish-owner".into(),
                compression: None,
                codec_config: LIMITS,
                page_cache: CacheRef::from_pooler(&clock, NZU16!(1024), NZUsize!(8)),
                write_buffer: NZUsize!(1024),
            },
        )
        .await
        .unwrap();
        journal = journal.append(enter.view().get(), &enter).await.unwrap().0;
        journal = journal.sync(enter.view().get()).await.unwrap();
        assert!(
            state
                .arm_wish_timeout::<Sha256>(&clock, &own, Duration::ZERO)
                .is_err()
        );
        assert!(
            state
                .arm_wish_timeout::<Sha256>(&clock, &own, Duration::MAX)
                .is_err()
        );
        let deadline = state
            .arm_wish_timeout::<Sha256>(&clock, &own, Duration::from_secs(5))
            .unwrap();
        clock.sleep(Duration::from_secs(2)).await;
        assert_eq!(
            state
                .arm_wish_timeout::<Sha256>(&clock, &own, Duration::from_secs(50))
                .unwrap(),
            deadline
        );
        assert!(state.reserve_timeout_wish::<Sha256>(&clock, &own).is_err());
        clock.sleep_until(deadline).await;
        let wish = state.reserve_timeout_wish::<Sha256>(&clock, &own).unwrap();
        assert!(matches!(
            wish.action(),
            Action::AdvanceWish {
                cause: WishCause::Timeout,
                ..
            }
        ));
        journal = journal.append(wish.view().get(), &wish).await.unwrap().0;
        journal = journal.sync(wish.view().get()).await.unwrap();
        let signed = state.sign_reserved(&wish).unwrap();
        assert!(signed.verify(&mut TestRng::new(5109), &f.verifier, LIMITS, &Sequential));
        assert_eq!(
            state
                .reserve_timeout_wish::<Sha256>(&clock, &alias)
                .unwrap(),
            wish
        );
        let released = state
            .record_signed::<Sha256, _>(&mut TestRng::new(5115), &wish, &signed, &Sequential)
            .unwrap();
        journal = journal
            .append(released.view().get(), &released)
            .await
            .unwrap()
            .0;
        journal = journal.sync(released.view().get()).await.unwrap();
        drop(journal);
        let reopened = Journal::<_, Record<Digest>>::init(
            clock.child("wish_wal_reopen"),
            JournalConfig {
                partition: "g1-wish-owner".into(),
                compression: None,
                codec_config: LIMITS,
                page_cache: CacheRef::from_pooler(&clock, NZU16!(1024), NZUsize!(8)),
                write_buffer: NZUsize!(1024),
            },
        )
        .await
        .unwrap();
        let mut stream = reopened
            .replay(0, 0, NZUsize!(1024), ReadOptions::DONT_CACHE)
            .await
            .unwrap();
        let mut replay =
            State::for_replay::<Sha256>(f.schemes[9].clone(), c.clone(), input(), LIMITS).unwrap();
        let replay_context = replay.verification_context();
        let replay_own = checked_entry(&replay_context, &c, &a, &all);
        let mut persisted = 0;
        while let Some(row) = stream.next().await {
            let record = row.unwrap().3;
            assert!(replay.sign_reserved(&wish).is_err());
            let material = if matches!(record.action(), Action::Released { .. }) {
                Material::None
            } else {
                Material::Entry(&replay_own)
            };
            restore(&mut replay, &record, material);
            persisted += 1;
        }
        drop(stream.finish().unwrap());
        replay.finish_replay().unwrap();
        assert_eq!(persisted, 3);
        assert_eq!(replay.records(), state.records());
        assert_eq!(replay.floor(), wish.message().unwrap().round);
        assert_eq!(replay.outbox(&wish), state.outbox(&wish));
        assert!(replay.sign_reserved(&wish).is_err());
        assert_eq!(
            replay
                .reserve_timeout_wish::<Sha256>(&clock, &replay_own)
                .unwrap(),
            wish
        );
        let committee = g::Committee::new(10).unwrap();
        let target = a.target().successor(committee).unwrap();
        let wishes = f
            .schemes
            .iter()
            .take(committee.quorum())
            .map(|s| g::Signed::sign(s, signed.message.clone(), LIMITS).unwrap())
            .collect();
        let next = EProof::Higher { target, wishes };
        let checked = checked_entry(&ctx, &c, &next, &all);
        assert!(state.reserve_recover::<Sha256>(&checked, None).is_err());
        state.enter::<Sha256>(&checked).unwrap();
        assert!(state.reserve_recover::<Sha256>(&checked, None).is_ok());
    });
}

#[test]
fn restart_does_not_manufacture_elapsed_timer_but_preserves_accepted_reservation() {
    deterministic::Runner::seeded(5110).start(|clock| async move {
        let f = fixture(8);
        let c = core(&f);
        let a = initial(&f, &c, 0);
        let b = initial(&f, &c, 1);
        let all = entries(&a, &b);
        let mut state = local(&f, &c);
        let ctx = state.verification_context();
        let own = checked_entry(&ctx, &c, &a, &all);
        let enter = state.enter::<Sha256>(&own).unwrap();
        let deadline = state
            .arm_wish_timeout::<Sha256>(&clock, &own, Duration::from_secs(1))
            .unwrap();
        clock.sleep_until(deadline).await;
        let mut replay =
            State::for_replay::<Sha256>(f.schemes[7].clone(), c.clone(), input(), LIMITS).unwrap();
        let ctx = replay.verification_context();
        let restored = checked_entry(&ctx, &c, &a, &all);
        restore(&mut replay, &enter, Material::Entry(&restored));
        replay.finish_replay().unwrap();
        assert!(
            replay
                .reserve_timeout_wish::<Sha256>(&clock, &restored)
                .is_err()
        );
        let rearmed = replay
            .arm_wish_timeout::<Sha256>(&clock, &restored, Duration::from_secs(3))
            .unwrap();
        assert!(rearmed > clock.current());
        let reserved = state.reserve_timeout_wish::<Sha256>(&clock, &own).unwrap();
        let mut replay2 =
            State::for_replay::<Sha256>(f.schemes[7].clone(), c.clone(), input(), LIMITS).unwrap();
        let ctx = replay2.verification_context();
        let restored = checked_entry(&ctx, &c, &a, &all);
        restore(&mut replay2, &enter, Material::Entry(&restored));
        restore(&mut replay2, &reserved, Material::Entry(&restored));
        replay2.finish_replay().unwrap();
        assert_eq!(
            replay2
                .reserve_timeout_wish::<Sha256>(&clock, &restored)
                .unwrap(),
            reserved
        );
        assert!(replay2.sign_reserved(&reserved).is_ok());
    });
}

#[test]
fn amplification_and_new_material_codecs_have_strict_caps_and_type_domains() {
    let f = fixture(8);
    let c = core(&f);
    let a = initial(&f, &c, 0);
    let b = initial(&f, &c, 1);
    let raw = amplification(&f, &c, &a, &b);
    let bytes = raw.encode();
    assert_eq!(&bytes[..4], b"G1Y1");
    assert_eq!(
        Amp::decode_cfg(bytes.clone(), &LIMITS).unwrap().encode(),
        bytes
    );
    for cut in 0..bytes.len() {
        assert!(Amp::decode_cfg(bytes.slice(..cut), &LIMITS).is_err());
    }
    for (offset, value) in [(0, b'X'), (3, b'2')] {
        let mut bad = bytes.to_vec();
        bad[offset] = value;
        assert!(Amp::decode_cfg(Bytes::from(bad), &LIMITS).is_err());
    }
    let mut trailing = bytes.to_vec();
    trailing.push(0);
    assert!(Amp::decode_cfg(Bytes::from(trailing), &LIMITS).is_err());
    let mut huge = bytes.to_vec();
    let count = 8 + raw.target.encode_size();
    huge[count..count + 4].copy_from_slice(&u32::MAX.to_be_bytes());
    assert!(Amp::decode_cfg(Bytes::from(huge), &LIMITS).is_err());
    let m = r::Material::Amplification(raw);
    let cfg = (LIMITS, f.verifier.certificate_codec_config());
    let bytes = m.encode();
    assert_eq!(bytes[8], 11);
    assert_eq!(
        r::Material::<S, Digest>::decode_cfg(bytes.clone(), &cfg)
            .unwrap()
            .encode(),
        bytes
    );
    assert_eq!(
        m.id::<Sha256>(),
        if let r::Material::Amplification(a) = &m {
            a.artifact_id::<Sha256>()
        } else {
            unreachable!()
        }
    );
    assert!(EProof::decode_cfg(bytes, &cfg).is_err());
}

struct GeneralWishConformance;
impl Conformance for GeneralWishConformance {
    async fn commit(seed: u64) -> Vec<u8> {
        let f = fixture([4, 7, 8, 9, 10, 11, 12, 13, 16, 31, 64][seed as usize % 11]);
        let c = core(&f);
        let a = initial(&f, &c, 0);
        let b = initial(&f, &c, 1);
        let all = entries(&a, &b);
        let raw = amplification(&f, &c, &a, &b);
        let mut state = local(&f, &c);
        let ctx = state.verification_context();
        let own = checked_entry(&ctx, &c, &a, &all);
        let amp = checked_amp(&ctx, &c, &raw, &all);
        state.enter::<Sha256>(&own).unwrap();
        let reserved = state.reserve_amplified_wish::<Sha256>(&own, &amp).unwrap();
        let signed = state.sign_reserved(&reserved).unwrap();
        let mut frames = vec![
            raw.encode(),
            r::Material::Amplification(raw.clone()).encode(),
            reserved.encode(),
            signed.encode(),
        ];
        // A distinct owner uses a real deterministic clock for the Timeout cause.
        let timeout = deterministic::Runner::seeded(5111).start(move |clock| async move {
            let mut state = local(&f, &c);
            let ctx = state.verification_context();
            let own = checked_entry(&ctx, &c, &a, &all);
            state.enter::<Sha256>(&own).unwrap();
            let deadline = state
                .arm_wish_timeout::<Sha256>(&clock, &own, Duration::from_secs(1))
                .unwrap();
            clock.sleep_until(deadline).await;
            state
                .reserve_timeout_wish::<Sha256>(&clock, &own)
                .unwrap()
                .encode()
        });
        frames.push(timeout);
        frames.encode().to_vec()
    }
}
conformance_tests! {GeneralWishConformance=>32}
#[cfg(feature = "arbitrary")]
mod arbitrary_conformance {
    use super::*;
    use commonware_codec::conformance::CodecConformance;
    conformance_tests! {CodecConformance<Amp>=>32, CodecConformance<Record<Digest>>=>32}
}

#[test]
fn complete_recovery_graph_retains_wish_cause_and_rejects_missing_amplification() {
    for n in [4, 8, 9, 10, 13, 16, 64] {
        let f = fixture(n);
        let c = core(&f);
        let a = initial(&f, &c, 0);
        let b = initial(&f, &c, 1);
        let all = entries(&a, &b);
        let amp = amplification(&f, &c, &a, &b);
        let committee = g::Committee::new(n as usize).unwrap();
        let wishes = f
            .schemes
            .iter()
            .take(committee.quorum())
            .map(|s| g::Signed::sign(s, amp.wishes[0].message.clone(), LIMITS).unwrap())
            .collect();
        let next = EProof::Higher {
            target: amp.target.clone(),
            wishes,
        };
        let mut graph = BTreeMap::new();
        for p in [&a, &b, &next] {
            graph.insert(p.artifact_id::<Sha256>(), r::Material::Entry(p.clone()));
        }
        let amp_id = amp.artifact_id::<Sha256>();
        graph.insert(amp_id, r::Material::Amplification(amp.clone()));
        let mut histories = Vec::new();
        for owner in 0..committee.quorum() {
            let mut state =
                State::new::<Sha256>(f.schemes[owner].clone(), c.clone(), input(), LIMITS).unwrap();
            let ctx = state.verification_context();
            let own = checked_entry(&ctx, &c, &a, &all);
            let checked = checked_amp(&ctx, &c, &amp, &all);
            state.enter::<Sha256>(&own).unwrap();
            let reserved = state
                .reserve_amplified_wish::<Sha256>(&own, &checked)
                .unwrap();
            let signed = state.sign_reserved(&reserved).unwrap();
            state
                .record_signed::<Sha256, _>(
                    &mut TestRng::new(5112),
                    &reserved,
                    &signed,
                    &Sequential,
                )
                .unwrap();
            let entered = checked_entry(&ctx, &c, &next, &all);
            state.enter::<Sha256>(&entered).unwrap();
            let recover = state.reserve_recover::<Sha256>(&entered, None).unwrap();
            let notice = state.sign_reserved(&recover).unwrap();
            let g::Kind::Recover(row) = &notice.message.kind else {
                unreachable!()
            };
            for i in 0..row.snapshot.count() as usize {
                let m = r::Material::Page(state.history_page(i).unwrap());
                graph.insert(m.id::<Sha256>(), m);
            }
            let h = r::Material::History {
                entry: next.artifact_id::<Sha256>(),
                notice,
            };
            let id = h.id::<Sha256>();
            graph.insert(id, h);
            histories.push(id);
        }
        let body = r::ProposalBody {
            value: g::Decision {
                slot: c.slot.clone(),
                input: input(),
                order: Bytes::from_static(b"AB"),
            },
            entry: next.artifact_id::<Sha256>(),
            histories,
            positive: Vec::new(),
            choice: r::Choice::Fresh {
                population: Digest::from([196; 32]),
                build: Bytes::new(),
                material: Bytes::new(),
            },
        };
        let root = body.id::<Sha256>();
        graph.insert(root, r::Material::Admission(body));
        let bounds = r::Bounds {
            nodes: 4096,
            links: 65536,
            encoded_bytes: 64 * 1024 * 1024,
            work: 2000000,
            entry: BOUNDS,
            history: g::issuance::history::Bounds {
                pages: 4096,
                encoded_bytes: 64 * 1024 * 1024,
                material_checks: 4096,
            },
        };
        let context = g::VerificationContext::new(f.verifier.clone());
        let fresh = Cell::new(0);
        let checked = r::verify::<Sha256, _, _, _>(
            &mut TestRng::new(5113),
            &context,
            &c,
            input(),
            root,
            |id| graph.get(id),
            LIMITS,
            bounds,
            |_| true,
            |_, _| true,
            |rows, body| {
                fresh.set(fresh.get() + 1);
                rows.originals().len() == committee.quorum() && body.value.order.as_ref() == b"AB"
            },
            &Sequential,
        )
        .unwrap();
        assert_eq!(checked.role(), r::Role::Admission);
        assert_eq!(fresh.get(), 1);
        graph.remove(&amp_id);
        fresh.set(0);
        assert!(
            r::verify::<Sha256, _, _, _>(
                &mut TestRng::new(5114),
                &context,
                &c,
                input(),
                root,
                |id| graph.get(id),
                LIMITS,
                bounds,
                |_| true,
                |_, _| true,
                |_, _| {
                    fresh.set(fresh.get() + 1);
                    true
                },
                &Sequential
            )
            .is_err()
        );
        assert_eq!(fresh.get(), 0);
    }
}

struct FrameCase {
    name: &'static str,
    bytes: Bytes,
    accepts: Box<dyn Fn(Bytes) -> bool>,
}

// All current public types implementing the private general::Frame contract.
// Inline fields (First, Subject, NativeParent, Choice and WishCause) are not
// independent Frame types. Sample values exercise codec identity, not admission.
fn general_frame_cases() -> Vec<FrameCase> {
    let f = fixture(8);
    let c = core(&f);
    let a = initial(&f, &c, 0);
    let b = initial(&f, &c, 1);
    let all = entries(&a, &b);
    let amp = amplification(&f, &c, &a, &b);
    let mut state = local(&f, &c);
    let context = state.verification_context();
    let checked = checked_entry(&context, &c, &a, &all);
    let record = state.enter::<Sha256>(&checked).unwrap();
    let snapshot = state.snapshot().unwrap().clone();
    let page = state.history_page(0).unwrap();
    let history = state
        .capture_history::<Sha256>(
            checked.target().ballot,
            checked.target().leader,
            checked.id(),
            None,
        )
        .unwrap();
    let g::Kind::Recover(recover) = history.kind else {
        unreachable!()
    };
    let decision = g::Decision {
        slot: c.slot.clone(),
        input: input(),
        order: Bytes::from_static(b"AB"),
    };
    let mut owners = c.followers.clone();
    owners.push(c.leader);
    owners.sort_unstable();
    let firsts = owners
        .into_iter()
        .map(|owner| {
            g::Signed::sign(
                &f.schemes[usize::from(owner)],
                g::Message {
                    slot: c.slot.id::<Sha256>(),
                    round: c.slot.proposal.round,
                    leader: c.leader,
                    kind: g::Kind::First(g::First {
                        core: c.id::<Sha256>(),
                        input: input(),
                        owner,
                        report: None,
                        preference: (owner != c.leader).then(|| decision.order.clone()),
                    }),
                },
                LIMITS,
            )
            .unwrap()
        })
        .collect();
    let body = g::OriginBody {
        decision: decision.clone(),
        core: c.clone(),
        firsts,
        population: Digest::from([197; 32]),
        build: Bytes::new(),
        material: Bytes::new(),
    };
    let selection = g::Signed::sign(
        &f.schemes[usize::from(c.leader)],
        g::Message {
            slot: c.slot.id::<Sha256>(),
            round: c.slot.proposal.round,
            leader: c.leader,
            kind: g::Kind::Select {
                body: body.id::<Sha256>(),
                decision: decision.id::<Sha256>(),
            },
        },
        LIMITS,
    )
    .unwrap();
    let origin = g::Origin {
        body: body.clone(),
        selection,
    };
    let message = g::Message {
        slot: c.slot.id::<Sha256>(),
        round: c.slot.proposal.round,
        leader: c.leader,
        kind: g::Kind::Phase {
            phase: g::Phase::FastFinal,
            decision: decision.id::<Sha256>(),
        },
    };
    let votes: Vec<_> = f
        .schemes
        .iter()
        .take(g::Committee::new(8).unwrap().quorum())
        .map(|s| g::Signed::sign(s, message.clone(), LIMITS).unwrap())
        .collect();
    let quorum = g::Quorum::from_votes(
        &mut TestRng::new(5117),
        &f.verifier,
        &votes,
        LIMITS,
        &Sequential,
    )
    .unwrap();
    let proposal = r::ProposalBody {
        value: decision.clone(),
        entry: a.artifact_id::<Sha256>(),
        histories: Vec::new(),
        positive: Vec::new(),
        choice: r::Choice::Fresh {
            population: Digest::from([198; 32]),
            build: Bytes::new(),
            material: Bytes::new(),
        },
    };
    let material = r::Material::Amplification(amp.clone());
    let g::Kind::Wish(wish) = &amp.wishes[0].message.kind else {
        unreachable!()
    };
    let mut cases = Vec::new();
    macro_rules! frame {
        ($name:literal, $value:expr, $ty:ty, $cfg:expr) => {{
            let cfg = $cfg;
            cases.push(FrameCase {
                name: $name,
                bytes: $value.encode(),
                accepts: Box::new(move |bytes| <$ty>::decode_cfg(bytes, &cfg).is_ok()),
            });
        }};
    }
    frame!("Slot", c.slot, g::Slot<Digest>, ());
    frame!("Core", c, g::Core<Digest>, ());
    frame!("Message", message, g::Message<Digest>, LIMITS);
    frame!("Signed", amp.wishes[0], g::Signed<S,Digest>, LIMITS);
    frame!("Decision", decision, g::Decision<Digest>, LIMITS);
    frame!("OriginBody", body, g::OriginBody<S,Digest>, LIMITS);
    frame!("Origin", origin, g::Origin<S,Digest>, LIMITS);
    frame!("Quorum", quorum, g::Quorum<S,Digest>, (LIMITS, f.verifier.certificate_codec_config()));
    frame!("Target", amp.target, entry::Target<Digest>, ());
    frame!("Wish", wish, entry::Wish<Digest>, ());
    frame!("Amplification", amp, Amp, LIMITS);
    frame!(
        "EntryProof",
        a,
        EProof,
        (LIMITS, f.verifier.certificate_codec_config())
    );
    frame!("Record", record, Record<Digest>, LIMITS);
    frame!("Snapshot", snapshot, g::issuance::Snapshot<Digest>, ());
    frame!(
        "HistoryPage",
        page,
        g::issuance::HistoryPage<Digest>,
        LIMITS
    );
    frame!(
        "Recover",
        recover,
        g::issuance::history::Recover<Digest>,
        LIMITS
    );
    frame!("ProposalBody", proposal, r::ProposalBody<Digest>, LIMITS);
    frame!("Material", material, r::Material<S,Digest>, (LIMITS, f.verifier.certificate_codec_config()));
    let (reservation, vote, released, certificate) = super::general_normal::frame_values();
    let normal_limits = super::general_normal::G_LIMITS;
    frame!(
        "NormalReservation",
        reservation,
        g::normal::Reservation<Digest>,
        normal_limits
    );
    frame!(
        "NormalVote",
        vote,
        g::normal::Vote<S, Digest>,
        normal_limits
    );
    frame!(
        "NormalReleased",
        released,
        g::normal::Released<S, Digest>,
        normal_limits
    );
    frame!(
        "NormalCertificate",
        certificate,
        g::normal::Certificate<S, Digest>,
        (normal_limits, f.verifier.certificate_codec_config())
    );
    assert_eq!(cases.len(), 22);
    cases
}

#[test]
fn public_general_frame_type_version_tags_are_unique() {
    let mut tags = BTreeMap::new();
    for case in general_frame_cases() {
        let tag: [u8; 4] = case.bytes[..4].try_into().unwrap();
        assert!(
            (case.accepts)(case.bytes.clone()),
            "own decoder rejected {}",
            case.name
        );
        assert_eq!(
            tags.insert(tag, case.name),
            None,
            "duplicate public type/version {:?} for {}",
            tag,
            case.name
        );
    }
}

#[test]
fn public_general_frame_decoders_reject_every_other_complete_frame_type() {
    let cases = general_frame_cases();
    for (i, decoder) in cases.iter().enumerate() {
        assert!(
            (decoder.accepts)(decoder.bytes.clone()),
            "own decoder rejected {}",
            decoder.name
        );
        for (j, encoded) in cases.iter().enumerate() {
            if i == j {
                continue;
            }
            assert!(
                !(decoder.accepts)(encoded.bytes.clone()),
                "{} accepted complete {} frame",
                decoder.name,
                encoded.name
            );
        }
    }
}
