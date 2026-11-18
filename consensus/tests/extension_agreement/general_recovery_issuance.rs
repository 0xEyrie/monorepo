//! Inactive entry/phase ledger checks with real public proof verification.
//! These fixtures do not supply native timeout permission, once-WISH ownership,
//! storage synchronization, an operating recovery network, or native finality.
use super::*;
use commonware_consensus::simplex::{
    extension::agreement::general::{
        self as g, entry,
        issuance::{Action, Material, Record, State},
        recovery as r,
    },
    types::Notarization,
};
use std::collections::BTreeMap;

const G_LIMITS: g::Limits = g::Limits {
    report_bytes: 128,
    order_bytes: 128,
    build_bytes: 256,
    material_bytes: 256,
    origin_bytes: g::MAX_EVIDENCE_BYTES,
};
const ENTRY_BOUNDS: entry::Bounds = entry::Bounds {
    nodes: 64,
    encoded_bytes: 4 * 1024 * 1024,
    signatures: 4096,
    depth: 64,
};
type Proof = entry::Proof<S, Digest>;
type Graph = BTreeMap<Digest, r::Material<S, Digest>>;

fn core(f: &Fixture<S>) -> g::Core<Digest> {
    let c = g::Committee::new(f.schemes.len()).unwrap();
    g::Core {
        slot: g::Slot {
            profile: Digest::from([130; 32]),
            domain: Digest::from([131; 32]),
            roster: g::Slot::<Digest>::roster::<Sha256, _>(&f.verifier),
            cut: 9,
            proposal: Proposal::new(round(4), View::new(3), Digest::from([132; 32])),
            parent: g::NativeParent::Proposal {
                round: round(3),
                digest: Digest::from([133; 32]),
            },
        },
        leader: Participant::new(f.schemes.len() as u32 - 1),
        followers: (0..f.schemes.len() as u32 - 1)
            .filter(|p| *p != 1)
            .take(c.quorum() - 1)
            .map(Participant::new)
            .collect(),
    }
}
fn input() -> Digest {
    Digest::from([134; 32])
}
fn target(core: &g::Core<Digest>, n: usize, attempt: u64) -> entry::Target<Digest> {
    entry::Target {
        core: core.id::<Sha256>(),
        input: input(),
        attempt,
        ballot: round(5 + attempt),
        leader: Participant::new((attempt % n as u64) as u32),
    }
}
fn initial(f: &Fixture<S>, core: &g::Core<Digest>, offset: usize) -> Proof {
    let q = g::Committee::new(f.schemes.len()).unwrap().quorum();
    let votes: Vec<_> = f
        .schemes
        .iter()
        .skip(offset)
        .take(q)
        .map(|s| Notarize::sign(s, core.slot.proposal.clone()).unwrap())
        .collect();
    Proof::Initial {
        target: target(core, f.schemes.len(), 0),
        notarization: Notarization::from_notarizes(&f.verifier, non_empty![@&votes], &Sequential)
            .unwrap(),
    }
}
fn higher(f: &Fixture<S>, core: &g::Core<Digest>, previous: &Proof) -> Proof {
    let q = g::Committee::new(f.schemes.len()).unwrap().quorum();
    let target = target(core, f.schemes.len(), previous.target().attempt + 1);
    let wishes = f
        .schemes
        .iter()
        .take(q)
        .map(|s| {
            g::Signed::sign(
                s,
                g::Message {
                    slot: core.slot.id::<Sha256>(),
                    round: target.ballot,
                    leader: target.leader,
                    kind: g::Kind::Wish(entry::Wish {
                        target: target.clone(),
                        predecessor: previous.artifact_id::<Sha256>(),
                    }),
                },
                G_LIMITS,
            )
            .unwrap()
        })
        .collect();
    Proof::Higher { target, wishes }
}
fn entry<'a>(
    context: &g::VerificationContext<S>,
    core: &'a g::Core<Digest>,
    proof: &'a Proof,
    proofs: &'a BTreeMap<Digest, Proof>,
) -> entry::VerifiedEntry<'a, S, Digest> {
    entry::verify::<Sha256, _, _, _>(
        &mut TestRng::new(4101),
        context,
        core,
        input(),
        proof,
        G_LIMITS,
        ENTRY_BOUNDS,
        |id| proofs.get(id),
        &Sequential,
    )
    .unwrap()
}
fn insert(graph: &mut Graph, material: r::Material<S, Digest>) -> Digest {
    let id = material.id::<Sha256>();
    graph.insert(id, material);
    id
}
const fn bounds() -> r::Bounds {
    r::Bounds {
        nodes: 4096,
        links: 65_536,
        encoded_bytes: 16 * 1024 * 1024,
        work: 1_000_000,
        entry: ENTRY_BOUNDS,
        history: g::issuance::history::Bounds {
            pages: 4096,
            encoded_bytes: 16 * 1024 * 1024,
            material_checks: 4096,
        },
    }
}
fn verified(
    context: &g::VerificationContext<S>,
    core: &g::Core<Digest>,
    graph: &Graph,
    root: Digest,
) -> r::Verified<Digest> {
    r::verify::<Sha256, _, _, _>(&mut TestRng::new(4102), context, core, input(), root,
        |id| graph.get(id), G_LIMITS, bounds(), |_| true, |_, _| true,
        |rows, body| {
            rows.originals().iter().all(|s| matches!(&s.message.kind, g::Kind::Recover(row) if row.report.is_none()))
                && body.value.order.as_ref() == b"AB"
                && matches!(&body.choice, r::Choice::Fresh { build, material, .. } if build.is_empty() && material.is_empty())
        }, &Sequential).unwrap()
}
struct Bundle {
    graph: Graph,
    admission: Digest,
    proposal: Digest,
    rpc: Digest,
}
fn bundle(
    f: &Fixture<S>,
    core: &g::Core<Digest>,
    proof: &Proof,
    proofs: &BTreeMap<Digest, Proof>,
    prior: Option<&Bundle>,
) -> Bundle {
    let mut graph = prior.map_or_else(Graph::new, |p| p.graph.clone());
    for proof in proofs.values() {
        insert(&mut graph, r::Material::Entry(proof.clone()));
    }
    let entry_artifact = insert(&mut graph, r::Material::Entry(proof.clone()));
    let q = g::Committee::new(f.schemes.len()).unwrap().quorum();
    let mut histories = Vec::new();
    for owner in 0..q {
        let mut state =
            State::new::<Sha256>(f.schemes[owner].clone(), core.clone(), input(), G_LIMITS)
                .unwrap();
        let context = state.verification_context();
        if let Some(prior) = prior {
            let proposal = verified(&context, core, &prior.graph, prior.proposal);
            let previous = proofs
                .values()
                .find(|p| p.target().attempt + 1 == proof.target().attempt)
                .unwrap();
            let previous = entry(&context, core, previous, proofs);
            state.enter::<Sha256>(&previous).unwrap();
            state.reserve_recover::<Sha256>(&previous, None).unwrap();
            let reserved = state.reserve_prepare::<Sha256>(&proposal).unwrap();
            let signed = state.sign_reserved(&reserved).unwrap();
            state
                .record_signed::<Sha256, _>(
                    &mut TestRng::new(4105),
                    &reserved,
                    &signed,
                    &Sequential,
                )
                .unwrap();
        }
        let entered = entry(&context, core, proof, proofs);
        state.enter::<Sha256>(&entered).unwrap();
        let reservation = state.reserve_recover::<Sha256>(&entered, None).unwrap();
        let notice = state.sign_reserved(&reservation).unwrap();
        let g::Kind::Recover(row) = &notice.message.kind else {
            unreachable!()
        };
        for index in 0..row.snapshot.count() as usize {
            insert(
                &mut graph,
                r::Material::Page(state.history_page(index).unwrap()),
            );
        }
        histories.push(insert(
            &mut graph,
            r::Material::History {
                entry: entry_artifact,
                notice,
            },
        ));
    }
    let body = r::ProposalBody {
        value: g::Decision {
            slot: core.slot.clone(),
            input: input(),
            order: Bytes::from_static(b"AB"),
        },
        entry: entry_artifact,
        histories,
        positive: Vec::new(),
        choice: r::Choice::Fresh {
            population: Digest::from([135; 32]),
            build: Bytes::new(),
            material: Bytes::new(),
        },
    };
    let admission = insert(&mut graph, r::Material::Admission(body.clone()));
    let subject = r::Subject {
        core: core.id::<Sha256>(),
        input: input(),
        entry: proof.target().id::<Sha256>(),
        proposal: body.id::<Sha256>(),
        decision: body.value.id::<Sha256>(),
    };
    let message = |phase| g::Message {
        slot: core.slot.id::<Sha256>(),
        round: proof.target().ballot,
        leader: proof.target().leader,
        kind: g::Kind::Recovery {
            phase,
            subject: subject.clone(),
        },
    };
    let endorsement = g::Signed::sign(
        &f.schemes[usize::from(proof.target().leader)],
        message(r::Phase::Propose),
        G_LIMITS,
    )
    .unwrap();
    let proposal = insert(
        &mut graph,
        r::Material::Proposal {
            admission,
            endorsement,
        },
    );
    let votes: Vec<_> = f
        .schemes
        .iter()
        .take(q)
        .map(|s| g::Signed::sign(s, message(r::Phase::Prepare), G_LIMITS).unwrap())
        .collect();
    let quorum = g::Quorum::from_votes(
        &mut TestRng::new(4103),
        &f.verifier,
        &votes,
        G_LIMITS,
        &Sequential,
    )
    .unwrap();
    let rpc = insert(&mut graph, r::Material::Rpc { proposal, quorum });
    Bundle {
        graph,
        admission,
        proposal,
        rpc,
    }
}

fn restore(
    state: &mut State<S, Digest>,
    record: &Record<Digest>,
    material: Material<'_, S, Digest>,
) {
    state
        .restore::<Sha256, _>(
            &mut TestRng::new(4110),
            record,
            material,
            |_| true,
            |_, _| true,
            &Sequential,
        )
        .unwrap();
}

fn roundtrip(record: &Record<Digest>) {
    let bytes = record.encode();
    assert_eq!(record.encode_size(), bytes.len());
    assert_eq!(
        Record::<Digest>::decode_cfg(bytes.clone(), &G_LIMITS).unwrap(),
        *record
    );
    assert!(Record::<Digest>::decode_cfg(bytes.slice(..bytes.len() - 1), &G_LIMITS).is_err());
    let mut trailing = bytes.to_vec();
    trailing.push(0);
    assert!(Record::<Digest>::decode_cfg(Bytes::from(trailing), &G_LIMITS).is_err());
}

fn rpc_alias(f: &Fixture<S>, graph: &mut Graph, original: Digest) -> Digest {
    let r::Material::Rpc { proposal, quorum } = graph.get(&original).unwrap() else {
        unreachable!()
    };
    let proposal = *proposal;
    let message = quorum.message.clone();
    let q = g::Committee::new(f.schemes.len()).unwrap().quorum();
    let votes: Vec<_> = f.schemes[f.schemes.len() - q..]
        .iter()
        .map(|s| g::Signed::sign(s, message.clone(), G_LIMITS).unwrap())
        .collect();
    let quorum = g::Quorum::from_votes(
        &mut TestRng::new(4111),
        &f.verifier,
        &votes,
        G_LIMITS,
        &Sequential,
    )
    .unwrap();
    insert(graph, r::Material::Rpc { proposal, quorum })
}

#[test]
fn general_roster_recover_is_once_and_replay_preserves_exact_entry_and_prefix() {
    for n in [4, 7, 8, 9, 10, 11, 12, 13, 16, 64] {
        let f = fixture(n);
        let core = core(&f);
        let q = g::Committee::new(f.schemes.len()).unwrap().quorum();
        let first = initial(&f, &core, 0);
        let alias = initial(&f, &core, f.schemes.len() - q);
        let second = higher(&f, &core, &first);
        let proofs = [(first.artifact_id::<Sha256>(), first.clone())]
            .into_iter()
            .collect();
        let owner = f.schemes.len() - 1;
        let mut state =
            State::new::<Sha256>(f.schemes[owner].clone(), core.clone(), input(), G_LIMITS)
                .unwrap();
        let context = state.verification_context();
        let a = entry(&context, &core, &first, &proofs);
        let b = entry(&context, &core, &alias, &proofs);
        let next = entry(&context, &core, &second, &proofs);
        assert_eq!(a.id(), b.id());
        assert_ne!(a.artifact_id(), b.artifact_id());
        assert!(state.reserve_recover::<Sha256>(&a, None).is_err());
        let original = state.reserve_first::<Sha256>(None, None, |_| true).unwrap();
        let original_signed = state.sign_reserved(&original).unwrap();
        let entered = state.enter::<Sha256>(&a).unwrap();
        assert_eq!(entered.authority(), Some(a.artifact_id()));
        assert_eq!(state.enter::<Sha256>(&b).unwrap(), entered);
        let reserved = state.reserve_recover::<Sha256>(&a, None).unwrap();
        let signed = state.sign_reserved(&reserved).unwrap();
        let g::Kind::Recover(row) = &signed.message.kind else {
            unreachable!()
        };
        assert_eq!(row.snapshot.count(), 2);
        assert_eq!(row.snapshot.owner(), Participant::new(owner as u32));
        assert_eq!(reserved.authority(), Some(a.artifact_id()));
        assert_eq!(state.reserve_recover::<Sha256>(&b, None).unwrap(), reserved);
        let before = state.records().to_vec();
        assert!(
            state
                .reserve_recover::<Sha256>(&a, Some(Bytes::new()))
                .is_err()
        );
        assert_eq!(state.records(), before);
        state.enter::<Sha256>(&next).unwrap();
        assert!(state.sign_reserved(&original).is_err());
        assert!(state.sign_reserved(&reserved).is_err());
        state
            .record_signed::<Sha256, _>(
                &mut TestRng::new(4112),
                &original,
                &original_signed,
                &Sequential,
            )
            .unwrap();
        let preceding = state.records().len();
        let current = state.reserve_recover::<Sha256>(&next, None).unwrap();
        let Some(g::Message {
            kind: g::Kind::Recover(current_row),
            ..
        }) = current.message()
        else {
            unreachable!()
        };
        assert_eq!(current_row.snapshot.count(), preceding as u64);
        assert!(
            current_row.snapshot.count() > state.snapshot().unwrap().count(),
            "RECOVER captures the current prefix, including a late accepted receipt"
        );
        state
            .record_signed::<Sha256, _>(&mut TestRng::new(4113), &reserved, &signed, &Sequential)
            .unwrap();
        assert_eq!(
            state.reserve_recover::<Sha256>(&next, None).unwrap(),
            current
        );
        assert!(state.outbox(&original).is_some());
        assert!(state.outbox(&reserved).is_some());
        let mut replay =
            State::for_replay::<Sha256>(f.schemes[owner].clone(), core.clone(), input(), G_LIMITS)
                .unwrap();
        let replay_context = replay.verification_context();
        let replay_a = entry(&replay_context, &core, &first, &proofs);
        let replay_b = entry(&replay_context, &core, &alias, &proofs);
        let replay_next = entry(&replay_context, &core, &second, &proofs);
        assert!(replay.sign_reserved(&current).is_err());
        for record in state.records() {
            roundtrip(record);
            let material = match record.action() {
                Action::Enter { snapshot, .. } if snapshot.ballot() == next.target().ballot => {
                    Material::Entry(&replay_next)
                }
                Action::Enter { .. } => Material::Entry(&replay_a),
                Action::Reserve { message, .. } if matches!(message.kind, g::Kind::Recover(_)) => {
                    if message.round == next.target().ballot {
                        Material::Entry(&replay_next)
                    } else {
                        Material::Entry(&replay_a)
                    }
                }
                _ => Material::None,
            };
            if record.authority() == Some(a.artifact_id()) {
                let before = replay.records().to_vec();
                assert!(
                    replay
                        .restore::<Sha256, _>(
                            &mut TestRng::new(4119),
                            record,
                            Material::Entry(&replay_b),
                            |_| true,
                            |_, _| true,
                            &Sequential,
                        )
                        .is_err()
                );
                assert_eq!(replay.records(), before);
            }
            restore(&mut replay, record, material);
        }
        replay.finish_replay().unwrap();
        assert_eq!(replay.records(), state.records());
        assert_eq!(replay.outbox(&original), state.outbox(&original));
        assert_eq!(replay.outbox(&reserved), state.outbox(&reserved));
        assert!(replay.sign_reserved(&reserved).is_err());
        assert!(replay.sign_reserved(&current).is_ok());
    }
}

#[test]
fn authenticated_entry_with_different_local_limits_cannot_install_permission() {
    let f = fixture(9);
    let core = core(&f);
    let first = initial(&f, &core, 0);
    let different = g::Limits {
        report_bytes: G_LIMITS.report_bytes + 1,
        ..G_LIMITS
    };
    let mut state =
        State::new::<Sha256>(f.schemes[8].clone(), core.clone(), input(), G_LIMITS).unwrap();
    let context = state.verification_context();
    let checked = entry::verify::<Sha256, _, _, _>(
        &mut TestRng::new(4121),
        &context,
        &core,
        input(),
        &first,
        different,
        ENTRY_BOUNDS,
        |_| None,
        &Sequential,
    )
    .unwrap();
    assert!(state.enter::<Sha256>(&checked).is_err());
    assert!(state.records().is_empty());
    assert_eq!(state.floor(), core.slot.proposal.round);
}

#[test]
fn phase_aliases_keep_exact_wal_authority_and_commit_requires_complete_rpc() {
    for n in [4, 8, 9, 10, 13, 16, 64] {
        let f = fixture(n);
        let core = core(&f);
        let first = initial(&f, &core, 0);
        let proofs = BTreeMap::new();
        let mut bundle = bundle(&f, &core, &first, &proofs, None);
        let original_rpc = bundle.rpc;
        let alias_id = rpc_alias(&f, &mut bundle.graph, original_rpc);
        assert_ne!(alias_id, original_rpc);
        let owner = f.schemes.len() - 1;
        let mut state =
            State::new::<Sha256>(f.schemes[owner].clone(), core.clone(), input(), G_LIMITS)
                .unwrap();
        let context = state.verification_context();
        let entered = entry(&context, &core, &first, &proofs);
        let admission = verified(&context, &core, &bundle.graph, bundle.admission);
        let proposal = verified(&context, &core, &bundle.graph, bundle.proposal);
        let rpc = verified(&context, &core, &bundle.graph, original_rpc);
        let alias = verified(&context, &core, &bundle.graph, alias_id);
        state.enter::<Sha256>(&entered).unwrap();
        assert!(state.reserve_propose::<Sha256>(&admission).is_err());
        assert!(state.reserve_prepare::<Sha256>(&admission).is_err());
        assert!(state.reserve_commit::<Sha256>(&proposal).is_err());
        let prepare = state.reserve_prepare::<Sha256>(&proposal).unwrap();
        assert_eq!(prepare.authority(), Some(proposal.evidence()));
        assert!(state.reserve_recover::<Sha256>(&entered, None).is_err());
        let receipt = state.retain_rpc::<Sha256>(&rpc).unwrap();
        let commit = state.reserve_commit::<Sha256>(&rpc).unwrap();
        assert_eq!(commit.authority(), Some(rpc.evidence()));
        assert_eq!(state.reserve_commit::<Sha256>(&alias).unwrap(), commit);
        assert_ne!(rpc.evidence(), alias.evidence());
        assert_eq!(rpc.proposal(), alias.proposal());
        let mut replay =
            State::for_replay::<Sha256>(f.schemes[owner].clone(), core.clone(), input(), G_LIMITS)
                .unwrap();
        assert!(
            replay
                .restore::<Sha256, _>(
                    &mut TestRng::new(4122),
                    &state.records()[0],
                    Material::Entry(&entered),
                    |_| true,
                    |_, _| true,
                    &Sequential,
                )
                .is_err()
        );
        assert!(replay.records().is_empty());
        let stale_proposal = proposal;
        let context = replay.verification_context();
        let entered = entry(&context, &core, &first, &proofs);
        let admission = verified(&context, &core, &bundle.graph, bundle.admission);
        let proposal = verified(&context, &core, &bundle.graph, bundle.proposal);
        let rpc = verified(&context, &core, &bundle.graph, original_rpc);
        let alias = verified(&context, &core, &bundle.graph, alias_id);
        restore(&mut replay, &state.records()[0], Material::Entry(&entered));
        let before = replay.records().to_vec();
        assert!(
            replay
                .restore::<Sha256, _>(
                    &mut TestRng::new(4123),
                    &prepare,
                    Material::Recovery(&stale_proposal),
                    |_| true,
                    |_, _| true,
                    &Sequential,
                )
                .is_err()
        );
        assert_eq!(replay.records(), before);
        assert!(
            replay
                .restore::<Sha256, _>(
                    &mut TestRng::new(4114),
                    &prepare,
                    Material::Recovery(&admission),
                    |_| true,
                    |_, _| true,
                    &Sequential,
                )
                .is_err()
        );
        assert_eq!(replay.records(), before);
        restore(&mut replay, &prepare, Material::Recovery(&proposal));
        restore(&mut replay, &receipt, Material::Recovery(&rpc));
        let before = replay.records().to_vec();
        assert!(
            replay
                .restore::<Sha256, _>(
                    &mut TestRng::new(4115),
                    &commit,
                    Material::Recovery(&alias),
                    |_| true,
                    |_, _| true,
                    &Sequential,
                )
                .is_err()
        );
        assert_eq!(replay.records(), before);
        restore(&mut replay, &commit, Material::Recovery(&rpc));
        replay.finish_replay().unwrap();
        assert_eq!(replay.records(), state.records());
        assert!(replay.sign_reserved(&commit).is_ok());
        for record in state.records() {
            roundtrip(record);
        }
        let mut coordinator = State::new::<Sha256>(
            f.schemes[usize::from(first.target().leader)].clone(),
            core.clone(),
            input(),
            G_LIMITS,
        )
        .unwrap();
        let context = coordinator.verification_context();
        let entered = entry(&context, &core, &first, &proofs);
        let admission = verified(&context, &core, &bundle.graph, bundle.admission);
        coordinator.enter::<Sha256>(&entered).unwrap();
        let propose = coordinator.reserve_propose::<Sha256>(&admission).unwrap();
        assert_eq!(propose.authority(), Some(admission.evidence()));
        assert!(
            coordinator
                .reserve_recover::<Sha256>(&entered, None)
                .is_err()
        );
        assert_eq!(
            coordinator.reserve_propose::<Sha256>(&admission).unwrap(),
            propose
        );
        let signed = coordinator.sign_reserved(&propose).unwrap();
        coordinator
            .record_signed::<Sha256, _>(&mut TestRng::new(4120), &propose, &signed, &Sequential)
            .unwrap();
        let mut replay = State::for_replay::<Sha256>(
            f.schemes[usize::from(first.target().leader)].clone(),
            core.clone(),
            input(),
            G_LIMITS,
        )
        .unwrap();
        let context = replay.verification_context();
        let entered = entry(&context, &core, &first, &proofs);
        let admission = verified(&context, &core, &bundle.graph, bundle.admission);
        for record in coordinator.records() {
            roundtrip(record);
            restore(
                &mut replay,
                record,
                match record.action() {
                    Action::Enter { .. } => Material::Entry(&entered),
                    Action::Reserve { .. } => Material::Recovery(&admission),
                    _ => Material::None,
                },
            );
        }
        replay.finish_replay().unwrap();
        assert_eq!(replay.outbox(&propose), coordinator.outbox(&propose));
        // Identity 1 is outside this original noncontiguous Core, but recovery
        // phases use the full roster rather than the original report cohort.
        let mut outside =
            State::new::<Sha256>(f.schemes[1].clone(), core.clone(), input(), G_LIMITS).unwrap();
        let context = outside.verification_context();
        let entered = entry(&context, &core, &first, &proofs);
        let proposal = verified(&context, &core, &bundle.graph, bundle.proposal);
        let rpc = verified(&context, &core, &bundle.graph, original_rpc);
        outside.enter::<Sha256>(&entered).unwrap();
        let prepared = outside.reserve_prepare::<Sha256>(&proposal).unwrap();
        let committed = outside.reserve_commit::<Sha256>(&rpc).unwrap();
        assert!(outside.sign_reserved(&prepared).is_ok());
        assert!(outside.sign_reserved(&committed).is_ok());
    }
}

#[test]
fn foreign_namespace_recovery_tokens_cannot_authorize_local_state() {
    let local = fixture(10);
    let foreign = ed25519::fixture(
        &mut TestRng::new(101),
        b"_COMMONWARE_CONSENSUS_AGREEMENT_FOREIGN_TEST",
        10,
    );
    let core = core(&local);
    let first = initial(&local, &core, 0);
    let foreign_first = initial(&foreign, &core, 0);
    let proofs = BTreeMap::new();
    let bundle = bundle(&foreign, &core, &foreign_first, &proofs, None);
    let foreign_context = g::VerificationContext::new(foreign.verifier);
    let admission = verified(&foreign_context, &core, &bundle.graph, bundle.admission);
    let proposal = verified(&foreign_context, &core, &bundle.graph, bundle.proposal);
    let rpc = verified(&foreign_context, &core, &bundle.graph, bundle.rpc);
    let mut state =
        State::new::<Sha256>(local.schemes[0].clone(), core.clone(), input(), G_LIMITS).unwrap();
    let context = state.verification_context();
    let entered = entry(&context, &core, &first, &proofs);
    state.enter::<Sha256>(&entered).unwrap();
    let before = state.records().to_vec();
    assert!(state.reserve_propose::<Sha256>(&admission).is_err());
    assert!(state.reserve_prepare::<Sha256>(&proposal).is_err());
    assert!(state.reserve_commit::<Sha256>(&rpc).is_err());
    assert!(state.retain_rpc::<Sha256>(&rpc).is_err());
    assert_eq!(state.records(), before);
}

#[test]
fn same_ballot_rpc_fences_competing_proposal_but_preserves_precreated_receipt() {
    let f = fixture(8);
    let core = core(&f);
    let first = initial(&f, &core, 0);
    let q = g::Committee::new(f.schemes.len()).unwrap().quorum();
    let alias = initial(&f, &core, f.schemes.len() - q);
    let proofs = BTreeMap::new();
    let mut state =
        State::new::<Sha256>(f.schemes[7].clone(), core.clone(), input(), G_LIMITS).unwrap();
    let context = state.verification_context();
    let entered = entry(&context, &core, &first, &proofs);
    let mut bundle = bundle(&f, &core, &first, &proofs, None);
    let rpc = verified(&context, &core, &bundle.graph, bundle.rpc);
    let original = verified(&context, &core, &bundle.graph, bundle.proposal);
    let r::Material::Admission(body) = bundle.graph.get(&bundle.admission).unwrap() else {
        unreachable!()
    };
    let mut body = body.clone();
    body.entry = insert(&mut bundle.graph, r::Material::Entry(alias));
    let admission = insert(&mut bundle.graph, r::Material::Admission(body.clone()));
    let message = g::Message {
        slot: core.slot.id::<Sha256>(),
        round: first.target().ballot,
        leader: first.target().leader,
        kind: g::Kind::Recovery {
            phase: r::Phase::Propose,
            subject: r::Subject {
                core: core.id::<Sha256>(),
                input: input(),
                entry: entered.id(),
                proposal: body.id::<Sha256>(),
                decision: body.value.id::<Sha256>(),
            },
        },
    };
    let endorsement = g::Signed::sign(&f.schemes[0], message, G_LIMITS).unwrap();
    let alternative_id = insert(
        &mut bundle.graph,
        r::Material::Proposal {
            admission,
            endorsement,
        },
    );
    let alternative = verified(&context, &core, &bundle.graph, alternative_id);
    assert_eq!(alternative.entry(), original.entry());
    assert_eq!(alternative.decision(), original.decision());
    assert_ne!(alternative.proposal(), original.proposal());
    state.enter::<Sha256>(&entered).unwrap();
    let reserved = state.reserve_prepare::<Sha256>(&alternative).unwrap();
    let created = state.sign_reserved(&reserved).unwrap();
    state.retain_rpc::<Sha256>(&rpc).unwrap();
    assert!(state.sign_reserved(&reserved).is_err());
    assert!(state.reserve_prepare::<Sha256>(&original).is_err());
    assert!(state.reserve_commit::<Sha256>(&rpc).is_ok());
    state
        .record_signed::<Sha256, _>(&mut TestRng::new(4116), &reserved, &created, &Sequential)
        .unwrap();
    assert_eq!(state.outbox(&reserved), Some(&created.encode()));
    let mut clean =
        State::new::<Sha256>(f.schemes[7].clone(), core.clone(), input(), G_LIMITS).unwrap();
    let context = clean.verification_context();
    let entered = entry(&context, &core, &first, &proofs);
    let rpc = verified(&context, &core, &bundle.graph, bundle.rpc);
    let original = verified(&context, &core, &bundle.graph, bundle.proposal);
    let alternative = verified(&context, &core, &bundle.graph, alternative_id);
    clean.enter::<Sha256>(&entered).unwrap();
    clean.retain_rpc::<Sha256>(&rpc).unwrap();
    let before = clean.records().to_vec();
    assert!(clean.reserve_prepare::<Sha256>(&alternative).is_err());
    assert_eq!(clean.records(), before);
    assert!(clean.reserve_prepare::<Sha256>(&original).is_ok());
}

#[test]
fn recovery_terminal_closes_new_signing_and_replays_late_exact_receipts() {
    let f = fixture(10);
    let core = core(&f);
    let first = initial(&f, &core, 0);
    let second = higher(&f, &core, &first);
    let proofs = [(first.artifact_id::<Sha256>(), first.clone())]
        .into_iter()
        .collect();
    let mut state =
        State::new::<Sha256>(f.schemes[9].clone(), core.clone(), input(), G_LIMITS).unwrap();
    let context = state.verification_context();
    let entered = entry(&context, &core, &first, &proofs);
    let next = entry(&context, &core, &second, &proofs);
    let mut bundle = bundle(&f, &core, &first, &proofs, None);
    let rpc = verified(&context, &core, &bundle.graph, bundle.rpc);
    let r::Material::Rpc { quorum, .. } = bundle.graph.get(&bundle.rpc).unwrap() else {
        unreachable!()
    };
    let mut message = quorum.message.clone();
    let g::Kind::Recovery { phase, .. } = &mut message.kind else {
        unreachable!()
    };
    *phase = r::Phase::Commit;
    let q = g::Committee::new(f.schemes.len()).unwrap().quorum();
    let votes: Vec<_> = f
        .schemes
        .iter()
        .take(q)
        .map(|s| g::Signed::sign(s, message.clone(), G_LIMITS).unwrap())
        .collect();
    let quorum = g::Quorum::from_votes(
        &mut TestRng::new(4117),
        &f.verifier,
        &votes,
        G_LIMITS,
        &Sequential,
    )
    .unwrap();
    let terminal_id = insert(
        &mut bundle.graph,
        r::Material::Terminal {
            rpc: bundle.rpc,
            quorum,
        },
    );
    let terminal = verified(&context, &core, &bundle.graph, terminal_id);
    state.enter::<Sha256>(&entered).unwrap();
    let reserved = state.reserve_commit::<Sha256>(&rpc).unwrap();
    let created = state.sign_reserved(&reserved).unwrap();
    assert!(state.terminal_recovery::<Sha256>(&rpc).is_err());
    let closed = state.terminal_recovery::<Sha256>(&terminal).unwrap();
    assert_eq!(
        state.terminal_recovery::<Sha256>(&terminal).unwrap(),
        closed
    );
    assert!(state.sign_reserved(&reserved).is_err());
    assert!(state.enter::<Sha256>(&next).is_err());
    assert!(
        state
            .capture_history::<Sha256>(
                first.target().ballot,
                first.target().leader,
                entered.id(),
                None
            )
            .is_err()
    );
    state
        .record_signed::<Sha256, _>(&mut TestRng::new(4118), &reserved, &created, &Sequential)
        .unwrap();
    state.retain_rpc::<Sha256>(&rpc).unwrap();
    let mut replay =
        State::for_replay::<Sha256>(f.schemes[9].clone(), core.clone(), input(), G_LIMITS).unwrap();
    let context = replay.verification_context();
    let entered = entry(&context, &core, &first, &proofs);
    let rpc = verified(&context, &core, &bundle.graph, bundle.rpc);
    let terminal = verified(&context, &core, &bundle.graph, terminal_id);
    for record in state.records() {
        roundtrip(record);
        let material = match record.action() {
            Action::Enter { .. } => Material::Entry(&entered),
            Action::Reserve { .. } | Action::RetainRpc { .. } => Material::Recovery(&rpc),
            Action::RecoveryTerminal { .. } => Material::Recovery(&terminal),
            _ => Material::None,
        };
        restore(&mut replay, record, material);
    }
    replay.finish_replay().unwrap();
    assert_eq!(replay.records(), state.records());
    assert_eq!(replay.outbox(&reserved), state.outbox(&reserved));
    assert!(replay.sign_reserved(&reserved).is_err());
}

#[test]
fn higher_rpc_blocks_new_lower_phase_reservation_and_reserved_signer_release() {
    let f = fixture(8);
    let core = core(&f);
    let first = initial(&f, &core, 0);
    let second = higher(&f, &core, &first);
    let proofs = [(first.artifact_id::<Sha256>(), first.clone())]
        .into_iter()
        .collect();
    let lower = bundle(&f, &core, &first, &proofs, None);
    let higher = bundle(&f, &core, &second, &proofs, Some(&lower));
    let mut state =
        State::new::<Sha256>(f.schemes[7].clone(), core.clone(), input(), G_LIMITS).unwrap();
    let context = state.verification_context();
    assert_eq!(
        verified(&context, &core, &lower.graph, lower.admission).role(),
        r::Role::Admission
    );
    let lower_proposal = verified(&context, &core, &lower.graph, lower.proposal);
    let lower_rpc = verified(&context, &core, &lower.graph, lower.rpc);
    let higher_rpc = verified(&context, &core, &higher.graph, higher.rpc);
    let entered = entry(&context, &core, &first, &proofs);
    state.enter::<Sha256>(&entered).unwrap();
    let reserved = state.reserve_prepare::<Sha256>(&lower_proposal).unwrap();
    let created = state.sign_reserved(&reserved).unwrap();
    state.retain_rpc::<Sha256>(&higher_rpc).unwrap();
    assert!(
        state.sign_reserved(&reserved).is_err(),
        "new lower signature must require catch-up"
    );
    assert!(
        state.reserve_commit::<Sha256>(&lower_rpc).is_err(),
        "new lower COMMIT reservation must require catch-up"
    );
    state
        .record_signed::<Sha256, _>(&mut TestRng::new(4104), &reserved, &created, &Sequential)
        .unwrap();
    assert!(state.outbox(&reserved).is_some());
    assert_eq!(
        state.floor(),
        first.target().ballot,
        "positive RPC is not fabricated entry/floor installation"
    );
}

// A separate corpus preserves the new WAL variants without changing the
// historical original-role corpus or treating codec decoding as authority.
struct GeneralRecoveryIssuanceConformance;
impl Conformance for GeneralRecoveryIssuanceConformance {
    async fn commit(seed: u64) -> Vec<u8> {
        let f = ed25519::fixture(
            &mut TestRng::new(seed),
            b"_COMMONWARE_CONSENSUS_G1_RECOVERY_ISSUANCE_CONFORMANCE",
            8,
        );
        let core = core(&f);
        let first = initial(&f, &core, 0);
        let proofs = BTreeMap::new();
        let mut bundle = bundle(&f, &core, &first, &proofs, None);
        let r::Material::Rpc { quorum, .. } = bundle.graph.get(&bundle.rpc).unwrap() else {
            unreachable!()
        };
        let mut message = quorum.message.clone();
        let g::Kind::Recovery { phase, .. } = &mut message.kind else {
            unreachable!()
        };
        *phase = r::Phase::Commit;
        let q = g::Committee::new(f.schemes.len()).unwrap().quorum();
        let votes: Vec<_> = f
            .schemes
            .iter()
            .take(q)
            .map(|s| g::Signed::sign(s, message.clone(), G_LIMITS).unwrap())
            .collect();
        let quorum = g::Quorum::from_votes(
            &mut TestRng::new(4124),
            &f.verifier,
            &votes,
            G_LIMITS,
            &Sequential,
        )
        .unwrap();
        let terminal_id = insert(
            &mut bundle.graph,
            r::Material::Terminal {
                rpc: bundle.rpc,
                quorum,
            },
        );
        let mut state =
            State::new::<Sha256>(f.schemes[0].clone(), core.clone(), input(), G_LIMITS).unwrap();
        let context = state.verification_context();
        let entered = entry(&context, &core, &first, &proofs);
        let admission = verified(&context, &core, &bundle.graph, bundle.admission);
        let proposal = verified(&context, &core, &bundle.graph, bundle.proposal);
        let rpc = verified(&context, &core, &bundle.graph, bundle.rpc);
        let terminal = verified(&context, &core, &bundle.graph, terminal_id);
        state.enter::<Sha256>(&entered).unwrap();
        state.reserve_recover::<Sha256>(&entered, None).unwrap();
        state.reserve_propose::<Sha256>(&admission).unwrap();
        state.reserve_prepare::<Sha256>(&proposal).unwrap();
        state.retain_rpc::<Sha256>(&rpc).unwrap();
        let commit = state.reserve_commit::<Sha256>(&rpc).unwrap();
        let signed = state.sign_reserved(&commit).unwrap();
        state
            .record_signed::<Sha256, _>(&mut TestRng::new(4125), &commit, &signed, &Sequential)
            .unwrap();
        state.terminal_recovery::<Sha256>(&terminal).unwrap();
        assert!(
            state
                .records()
                .iter()
                .any(|r| matches!(r.action(), Action::Enter { .. }))
        );
        assert!(
            state
                .records()
                .iter()
                .any(|r| matches!(r.action(), Action::RetainRpc { .. }))
        );
        assert!(
            state
                .records()
                .iter()
                .any(|r| matches!(r.action(), Action::RecoveryTerminal { .. }))
        );
        let frames: Vec<_> = state
            .records()
            .iter()
            .map(|record| {
                roundtrip(record);
                record.encode()
            })
            .collect();
        frames.encode().to_vec()
    }
}
conformance_tests! { GeneralRecoveryIssuanceConformance => 32 }

#[test]
fn wish_advancement_allows_predecessor_rpc_but_rechecks_target_rpc_and_terminal() {
    for n in [4, 8, 9, 10, 13, 16] {
        let f = fixture(n);
        let core = core(&f);
        let first = initial(&f, &core, 0);
        let second = higher(&f, &core, &first);
        let proofs = [(first.artifact_id::<Sha256>(), first.clone())]
            .into_iter()
            .collect();
        let lower = bundle(&f, &core, &first, &proofs, None);
        let higher = bundle(&f, &core, &second, &proofs, Some(&lower));
        let committee = g::Committee::new(n as usize).unwrap();
        let Proof::Higher { target, wishes } = &second else {
            unreachable!()
        };
        let raw = entry::Amplification {
            target: target.clone(),
            wishes: wishes[..committee.faults() + 1].to_vec(),
        };
        let mut state = State::new::<Sha256>(
            f.schemes[n as usize - 1].clone(),
            core.clone(),
            input(),
            G_LIMITS,
        )
        .unwrap();
        let ctx = state.verification_context();
        let predecessor = entry(&ctx, &core, &first, &proofs);
        let amp = entry::verify_amplification::<Sha256, _, _, _>(
            &mut TestRng::new(4120),
            &ctx,
            &core,
            input(),
            &raw,
            G_LIMITS,
            ENTRY_BOUNDS,
            |id| proofs.get(id),
            &Sequential,
        )
        .unwrap();
        let lower_rpc = verified(&ctx, &core, &lower.graph, lower.rpc);
        let higher_rpc = verified(&ctx, &core, &higher.graph, higher.rpc);
        state.enter::<Sha256>(&predecessor).unwrap();
        state.retain_rpc::<Sha256>(&lower_rpc).unwrap();
        let wish = state
            .reserve_amplified_wish::<Sha256>(&predecessor, &amp)
            .unwrap();
        let already_signed = state.sign_reserved(&wish).unwrap();
        state.retain_rpc::<Sha256>(&higher_rpc).unwrap();
        assert!(state.sign_reserved(&wish).is_err());
        assert_eq!(
            state
                .reserve_amplified_wish::<Sha256>(&predecessor, &amp)
                .unwrap(),
            wish
        );
        state
            .record_signed::<Sha256, _>(
                &mut TestRng::new(4121),
                &wish,
                &already_signed,
                &Sequential,
            )
            .unwrap();
        assert!(state.outbox(&wish).is_some());
        let mut state = State::new::<Sha256>(
            f.schemes[n as usize - 1].clone(),
            core.clone(),
            input(),
            G_LIMITS,
        )
        .unwrap();
        let ctx = state.verification_context();
        let predecessor = entry(&ctx, &core, &first, &proofs);
        let amp = entry::verify_amplification::<Sha256, _, _, _>(
            &mut TestRng::new(4122),
            &ctx,
            &core,
            input(),
            &raw,
            G_LIMITS,
            ENTRY_BOUNDS,
            |id| proofs.get(id),
            &Sequential,
        )
        .unwrap();
        let higher_rpc = verified(&ctx, &core, &higher.graph, higher.rpc);
        state.enter::<Sha256>(&predecessor).unwrap();
        state.retain_rpc::<Sha256>(&higher_rpc).unwrap();
        let before = state.records().to_vec();
        assert!(
            state
                .reserve_amplified_wish::<Sha256>(&predecessor, &amp)
                .is_err()
        );
        assert_eq!(state.records(), before);
        // A lower genuine terminal closes new interpretation signing at every ballot.
        let mut lower = lower;
        let r::Material::Rpc { quorum, .. } = lower.graph.get(&lower.rpc).unwrap() else {
            unreachable!()
        };
        let mut message = quorum.message.clone();
        let g::Kind::Recovery { phase, .. } = &mut message.kind else {
            unreachable!()
        };
        *phase = r::Phase::Commit;
        let votes: Vec<_> = f
            .schemes
            .iter()
            .take(committee.quorum())
            .map(|s| g::Signed::sign(s, message.clone(), G_LIMITS).unwrap())
            .collect();
        let quorum = g::Quorum::from_votes(
            &mut TestRng::new(4123),
            &f.verifier,
            &votes,
            G_LIMITS,
            &Sequential,
        )
        .unwrap();
        let terminal_id = insert(
            &mut lower.graph,
            r::Material::Terminal {
                rpc: lower.rpc,
                quorum,
            },
        );
        let terminal = verified(&ctx, &core, &lower.graph, terminal_id);
        state.terminal_recovery::<Sha256>(&terminal).unwrap();
        assert!(
            state
                .reserve_amplified_wish::<Sha256>(&predecessor, &amp)
                .is_err()
        );
        // Isolate terminal rejection from the positive higher-RPC gate above.
        for reserve_first in [false, true] {
            let mut closed = State::new::<Sha256>(
                f.schemes[n as usize - 1].clone(),
                core.clone(),
                input(),
                G_LIMITS,
            )
            .unwrap();
            let ctx = closed.verification_context();
            let predecessor = entry(&ctx, &core, &first, &proofs);
            let amp = entry::verify_amplification::<Sha256, _, _, _>(
                &mut TestRng::new(4124),
                &ctx,
                &core,
                input(),
                &raw,
                G_LIMITS,
                ENTRY_BOUNDS,
                |id| proofs.get(id),
                &Sequential,
            )
            .unwrap();
            let terminal = verified(&ctx, &core, &lower.graph, terminal_id);
            closed.enter::<Sha256>(&predecessor).unwrap();
            let reserved = reserve_first.then(|| {
                closed
                    .reserve_amplified_wish::<Sha256>(&predecessor, &amp)
                    .unwrap()
            });
            let signed = reserved.as_ref().map(|r| closed.sign_reserved(r).unwrap());
            closed.terminal_recovery::<Sha256>(&terminal).unwrap();
            if let Some(reserved) = reserved {
                assert!(matches!(
                    closed.sign_reserved(&reserved),
                    Err(g::issuance::Error::Closed)
                ));
                // Exact historical receipt retrieval and accepted late outbox are
                // still permitted; neither invokes a signer or changes the cause.
                assert_eq!(
                    closed
                        .reserve_amplified_wish::<Sha256>(&predecessor, &amp)
                        .unwrap(),
                    reserved
                );
                closed
                    .record_signed::<Sha256, _>(
                        &mut TestRng::new(4125),
                        &reserved,
                        &signed.unwrap(),
                        &Sequential,
                    )
                    .unwrap();
                assert!(closed.outbox(&reserved).is_some());
            } else {
                assert_eq!(
                    closed.reserve_amplified_wish::<Sha256>(&predecessor, &amp),
                    Err(g::issuance::Error::Closed)
                );
            }
        }
    }
}
