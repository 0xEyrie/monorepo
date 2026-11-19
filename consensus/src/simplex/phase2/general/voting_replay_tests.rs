//! Exact receipt-role binding with the actual General adapter and real crypto.
//! This is a replay component test, not native Actor or SDK policy evidence.

use super::*;
use crate::simplex::scheme::ed25519;
use commonware_codec::Write as _;
use commonware_cryptography::{
    certificate::mocks::Fixture,
    sha256::{Digest as D, Sha256},
};
use commonware_utils::{TestRng, test_rng};

type S = ed25519::Scheme;
type M = General<Sha256>;

const LIMITS: g::Limits = g::Limits {
    report_bytes: 128,
    order_bytes: 128,
    build_bytes: 256,
    material_bytes: 128,
    origin_bytes: g::MAX_EVIDENCE_BYTES,
};

struct History {
    signer: S,
    context: Context<S, D>,
    first: Wal<S, D>,
    first_released: Wal<S, D>,
    select: Wal<S, D>,
    select_released: Wal<S, D>,
    wrong_receipt: Wal<S, D>,
}

fn population(rows: &[g::Signed<S, D>]) -> D {
    let mut bytes = Vec::new();
    for row in rows {
        row.write(&mut bytes);
    }
    Sha256::hash(&[
        b"_COMMONWARE_CONSENSUS_G1_SELECT_RECEIPT_TEST_POPULATION_V1",
        &bytes,
    ])
}

fn row_policy(core: &g::Core<D>, input: D, row: &g::First<D>) -> bool {
    row.core == core.id::<Sha256>()
        && row.input == input
        && row.report.is_none()
        && if row.owner == core.leader {
            row.preference.is_none()
        } else {
            core.followers.contains(&row.owner)
                && row.preference.as_deref() == Some(b"AB".as_slice())
        }
}

fn build_policy(rows: &g::VerifiedRows<S, D>, body: &g::OriginBody<S, D>) -> bool {
    rows.core() == &body.core
        && rows.input() == body.decision.input
        && body.decision.slot == body.core.slot
        && body.decision.order.as_ref() == b"AB"
        && body.population == population(rows.originals())
        && body.build.as_ref() == b"test-two-block-build/AB"
        && body.material.is_empty()
}

fn history(n: u32) -> History {
    let mut rng = TestRng::new(15_037 + u64::from(n));
    let fixture: Fixture<S> = ed25519::fixture(
        &mut rng,
        b"_COMMONWARE_CONSENSUS_G1_SELECT_RECEIPT_REPLAY_TEST",
        n,
    );
    let signer = fixture.schemes[0].clone();
    let proposal = Proposal::new(
        Round::new(Epoch::new(1), View::new(5)),
        View::new(4),
        D::from([51; 32]),
    );
    let slot = g::Slot {
        profile: D::from([52; 32]),
        domain: D::from([53; 32]),
        roster: g::Slot::roster::<Sha256, S>(&signer),
        cut: 9,
        proposal: proposal.clone(),
        parent: g::NativeParent::Proposal {
            round: Round::new(Epoch::new(1), View::new(4)),
            digest: D::from([54; 32]),
        },
    };
    let native = NativeContext {
        round: proposal.round,
        leader: fixture.participants[0].clone(),
        parent: (View::new(4), D::from([54; 32])),
    };
    let input = D::from([55; 32]);
    let core = g::Core::derive::<Sha256, S>(&signer, slot.clone(), Participant::new(0)).unwrap();
    let capture = FirstInput::new::<Sha256, S>(
        &signer,
        slot.clone(),
        &native,
        input,
        None,
        None,
        LIMITS,
        |row| row_policy(&core, input, row),
    )
    .unwrap();
    let context = Context::new(
        Epoch::new(1),
        slot.profile,
        slot.domain,
        D::from([0; 32]),
        LIMITS,
        Resources {
            slots: 2,
            handles: 8,
            bytes: 16 * 1024 * 1024,
            records_per_slot: 16,
        },
    )
    .unwrap();
    context.publish_input::<Sha256>(capture.clone()).unwrap();
    let mut issuer =
        g::issuance::State::new::<Sha256>(signer.clone(), core.clone(), input, LIMITS).unwrap();
    let first = issuer
        .reserve_first::<Sha256>(None, None, |row| capture.accepts(row))
        .unwrap();
    let first_signed = issuer.sign_reserved(&first).unwrap();
    assert_eq!(first_signed.attestation.signer, Participant::new(0));
    assert!(first_signed.verify(&mut rng, &signer, LIMITS, &Sequential));
    let first_receipt = issuer
        .record_signed::<Sha256, _>(&mut rng, &first, &first_signed, &Sequential)
        .unwrap();
    let pair = FirstVote::new(
        Notarize::sign(&signer, proposal.clone()).unwrap(),
        Some(first_signed.clone()),
    );
    pair.authenticate(&mut rng, &signer, &Sequential).unwrap();

    let mut owners = core.followers.clone();
    owners.push(core.leader);
    owners.sort_unstable();
    let firsts: Vec<_> = owners
        .into_iter()
        .map(|owner| {
            if owner == core.leader {
                return first_signed.clone();
            }
            let row = g::First {
                core: core.id::<Sha256>(),
                input,
                owner,
                report: None,
                preference: Some(Bytes::from_static(b"AB")),
            };
            assert!(row_policy(&core, input, &row));
            g::Signed::sign(
                &fixture.schemes[usize::from(owner)],
                g::Message {
                    slot: slot.id::<Sha256>(),
                    round: proposal.round,
                    leader: core.leader,
                    kind: g::Kind::First(row),
                },
                LIMITS,
            )
            .unwrap()
        })
        .collect();
    let body = g::OriginBody {
        decision: g::Decision {
            slot,
            input,
            order: Bytes::from_static(b"AB"),
        },
        core: core.clone(),
        population: population(&firsts),
        build: Bytes::from_static(b"test-two-block-build/AB"),
        material: Bytes::new(),
        firsts,
    };
    let checked = body
        .verify::<Sha256, _>(
            &mut rng,
            &signer,
            &core,
            input,
            LIMITS,
            |row| row_policy(&core, input, row),
            build_policy,
            &Sequential,
        )
        .unwrap();
    context
        .publish_selection::<Sha256>(body.clone(), checked.clone())
        .unwrap();
    let select = issuer
        .reserve_select_checked::<Sha256, _>(&mut rng, &body, &checked, &Sequential)
        .unwrap();
    let select_signed = issuer.sign_reserved(&select).unwrap();
    assert_eq!(select_signed.attestation.signer, Participant::new(0));
    assert!(select_signed.verify(&mut rng, &signer, LIMITS, &Sequential));
    let select_receipt = issuer
        .record_signed::<Sha256, _>(&mut rng, &select, &select_signed, &Sequential)
        .unwrap();
    assert_ne!(first.id::<Sha256>(), select.id::<Sha256>());
    assert_eq!(first.owner(), select.owner());
    assert_eq!(first.core(), select.core());
    assert_eq!(first.input(), select.input());

    History {
        signer,
        context,
        first: Wal(Event::First(first.clone())),
        first_released: Wal(Event::FirstReleased {
            reservation: first,
            receipt: Some(first_receipt.clone()),
            vote: pair,
        }),
        select: Wal(Event::Select(select.clone())),
        select_released: Wal(Event::SelectReleased {
            reservation: select.clone(),
            receipt: select_receipt,
        }),
        wrong_receipt: Wal(Event::SelectReleased {
            reservation: select,
            receipt: first_receipt,
        }),
    }
}

fn replay_prefix(history: &History) -> RecoveryState<S, D> {
    let mut state = RecoveryState::EMPTY;
    let mut rng = test_rng();
    for row in [&history.first, &history.first_released] {
        let row = Wal::<S, D>::decode_cfg(row.encode(), &()).unwrap();
        assert!(<M as Voting<S, D>>::replay_notarize(
            &history.signer,
            &history.context,
            &mut rng,
            &mut state,
            &row,
        ));
    }
    let row = Wal::<S, D>::decode_cfg(history.select.encode(), &()).unwrap();
    assert!(<M as Voting<S, D>>::replay_recovery(
        &history.signer,
        &history.context,
        &mut rng,
        &mut state,
        None,
        &row,
    ));
    state
}

#[test]
fn select_release_replay_rejects_a_genuine_first_receipt_without_mutation() {
    for n in [8, 10] {
        let history = history(n);
        let slot = history.select.record().slot().id::<Sha256>();
        let mut rng = test_rng();
        let mut valid = replay_prefix(&history);
        let correct = Wal::<S, D>::decode_cfg(history.select_released.encode(), &()).unwrap();
        assert!(<M as Voting<S, D>>::replay_recovery(
            &history.signer,
            &history.context,
            &mut rng,
            &mut valid,
            None,
            &correct,
        ));
        assert!(
            valid.slots[&slot]
                .ledger
                .outbox(history.select.record())
                .is_some()
        );

        let mut rejected = replay_prefix(&history);
        let records = rejected.slots[&slot].ledger.records().to_vec();
        let pin = rejected.slots[&slot].select.clone();
        assert!(
            rejected.slots[&slot]
                .ledger
                .outbox(history.select.record())
                .is_none()
        );
        let substituted = Wal::<S, D>::decode_cfg(history.wrong_receipt.encode(), &()).unwrap();
        assert!(
            !<M as Voting<S, D>>::replay_recovery(
                &history.signer,
                &history.context,
                &mut rng,
                &mut rejected,
                None,
                &substituted,
            ),
            "a genuine FIRST receipt cannot release SELECT for n={n}"
        );
        assert_eq!(rejected.slots[&slot].ledger.records(), records);
        assert_eq!(rejected.slots[&slot].select, pin);
        assert!(
            rejected.slots[&slot]
                .ledger
                .outbox(history.select.record())
                .is_none()
        );
    }
}

#[test]
fn scoped_leader_replays_select_when_its_first_is_outside_the_quorum() {
    let mut rng = test_rng();
    let f: Fixture<S> = ed25519::fixture(&mut rng, b"route_select_wal", 7);
    let slot = g::Slot {
        profile: D::from([1; 32]),
        domain: D::from([2; 32]),
        roster: g::Slot::roster::<Sha256, S>(&f.verifier),
        cut: 1,
        proposal: Proposal::new(
            Round::new(Epoch::new(1), View::new(1)),
            View::zero(),
            D::from([3; 32]),
        ),
        parent: g::NativeParent::Genesis(D::from([4; 32])),
    };
    let leader = Participant::new(0);
    let core = g::Core::derive::<Sha256, S>(&f.verifier, slot.clone(), leader).unwrap();
    let input = D::from([5; 32]);
    let scope = D::from([6; 32]);
    let row = |owner| g::First {
        owner,
        input,
        core: scope,
        preference: None,
        report: None,
    };
    let subject = g::First::route_slot::<Sha256>(&slot, scope, input);
    let mut issuer =
        g::issuance::State::new::<Sha256>(f.schemes[0].clone(), core.clone(), input, LIMITS)
            .unwrap();
    let first = issuer
        .reserve_route_first::<Sha256>(row(leader), |_| true)
        .unwrap();
    let mut body = g::OriginBody {
        core: core.clone(),
        decision: g::Decision {
            slot: slot.clone(),
            input,
            order: Bytes::from_static(b"BA"),
        },
        population: D::from([7; 32]),
        build: Bytes::from_static(b"build"),
        material: Bytes::new(),
        firsts: (1..=5)
            .map(|i| {
                g::Signed::sign(
                    &f.schemes[i],
                    g::Message {
                        slot: subject,
                        round: slot.proposal.round,
                        leader,
                        kind: g::Kind::First(row(Participant::new(i as u32))),
                    },
                    LIMITS,
                )
                .unwrap()
            })
            .collect(),
    };
    let policy = |b: &g::OriginBody<S, D>| b.decision.order.as_ref() == b"BA";
    let cap = body
        .verify_route_selection::<Sha256, _>(
            &mut rng,
            &f.verifier,
            &core,
            input,
            scope,
            LIMITS,
            policy,
            &Sequential,
        )
        .unwrap();
    assert!(
        body.verify_route_selection::<Sha256, _>(
            &mut rng,
            &f.verifier,
            &core,
            input,
            scope,
            LIMITS,
            |_| false,
            &Sequential
        )
        .is_err()
    );
    assert!(
        body.verify::<Sha256, _>(
            &mut rng,
            &f.verifier,
            &core,
            input,
            LIMITS,
            |_| true,
            |_, _| true,
            &Sequential
        )
        .is_err()
    );
    let select = issuer
        .reserve_select_checked::<Sha256, _>(&mut rng, &body, &cap, &Sequential)
        .unwrap();
    let mut cold =
        g::issuance::State::for_replay::<Sha256>(f.schemes[0].clone(), core, input, LIMITS)
            .unwrap();
    cold.restore::<Sha256, _>(
        &mut rng,
        &first,
        g::issuance::Material::None,
        |r| r == &row(leader),
        |_, _| false,
        &Sequential,
    )
    .unwrap();
    let raw = body.material.clone();
    body.material = Bytes::from_static(b"other");
    assert!(
        cold.restore_select_checked::<Sha256, _>(&mut rng, &select, &body, &cap, &Sequential)
            .is_err()
    );
    body.material = raw;
    cold.restore_select_checked::<Sha256, _>(&mut rng, &select, &body, &cap, &Sequential)
        .unwrap();
    assert_eq!(cold.records(), issuer.records());
    let origin = g::Origin {
        body,
        selection: issuer.sign_reserved(&select).unwrap(),
    };
    let notarizes: Vec<_> = f
        .schemes
        .iter()
        .take(5)
        .map(|s| Notarize::sign(s, slot.proposal.clone()).unwrap())
        .collect();
    let qc = crate::simplex::types::Notarization::from_notarizes(
        &f.verifier,
        commonware_utils::non_empty![@notarizes.iter()],
        &Sequential,
    )
    .unwrap();
    let assembly = g::normal::Assembly::from_route::<Sha256, _>(
        &mut rng,
        &f.verifier,
        origin.clone(),
        qc,
        cap,
        &Sequential,
    )
    .unwrap();
    let reservation = issuer
        .reserve_normal_checked::<Sha256, _>(&mut rng, &assembly, &Sequential)
        .unwrap();
    cold.restore_normal_checked::<Sha256, _>(&mut rng, &reservation, &assembly, &Sequential)
        .unwrap();
    assert_eq!(issuer.records(), cold.records());
    let mut votes = vec![issuer.sign_normal::<Sha256>(&reservation).unwrap()];
    for owner in [1usize, 2, 3, 6] {
        let mut peer = g::issuance::State::new::<Sha256>(
            f.schemes[owner].clone(),
            origin.body.core.clone(),
            input,
            LIMITS,
        )
        .unwrap();
        peer.reserve_route_first::<Sha256>(row(Participant::new(owner as u32)), |_| true)
            .unwrap();
        let reserved = peer
            .reserve_normal_checked::<Sha256, _>(&mut rng, &assembly, &Sequential)
            .unwrap();
        votes.push(peer.sign_normal::<Sha256>(&reserved).unwrap());
    }
    let mut certificate = assembly
        .assemble::<Sha256, _>(&mut rng, &f.verifier, &votes, &Sequential)
        .unwrap();
    certificate
        .authenticate::<Sha256, _>(&mut rng, &f.verifier, LIMITS, &Sequential)
        .unwrap();
    certificate.origin.selection = certificate.origin.body.firsts[0].clone();
    assert!(
        certificate
            .authenticate::<Sha256, _>(&mut rng, &f.verifier, LIMITS, &Sequential)
            .is_err()
    );
}
