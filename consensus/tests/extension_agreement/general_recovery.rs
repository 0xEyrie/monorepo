//! Actual signed general-roster recovery evidence and codec checks.
//! These inactive-component fixtures do not establish native P eligibility,
//! deadline permission, Actor/WAL integration, Source delivery or native finality.
use super::*;
use commonware_consensus::simplex::{
    extension::agreement::general::{self as g, entry, issuance::State, recovery as r},
    types::Notarization,
};
use std::{cell::Cell, collections::BTreeMap};

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
fn entry_in<'a>(
    _f: &Fixture<S>,
    core: &'a g::Core<Digest>,
    proof: &'a Proof,
    proofs: &'a BTreeMap<Digest, Proof>,
    context: &g::VerificationContext<S>,
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
fn entry<'a>(
    f: &Fixture<S>,
    core: &'a g::Core<Digest>,
    proof: &'a Proof,
    proofs: &'a BTreeMap<Digest, Proof>,
) -> entry::VerifiedEntry<'a, S, Digest> {
    entry_in(
        f,
        core,
        proof,
        proofs,
        &g::VerificationContext::new(f.verifier.clone()),
    )
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
fn verified_in(
    _f: &Fixture<S>,
    core: &g::Core<Digest>,
    graph: &Graph,
    root: Digest,
    context: &g::VerificationContext<S>,
) -> r::Verified<Digest> {
    r::verify::<Sha256, _, _, _>(&mut TestRng::new(4102), context, core, input(), root,
        |id| graph.get(id), G_LIMITS, bounds(), |_| true, |_, _| true,
        |rows, body| {
            rows.originals().iter().all(|s| matches!(&s.message.kind, g::Kind::Recover(row) if row.report.is_none()))
                && body.value.order.as_ref() == b"AB"
                && matches!(&body.choice, r::Choice::Fresh { population, build, material } if *population==Digest::from([135;32]) && build.is_empty() && material.is_empty())
        }, &Sequential).unwrap()
}
fn verified(
    f: &Fixture<S>,
    core: &g::Core<Digest>,
    graph: &Graph,
    root: Digest,
) -> r::Verified<Digest> {
    verified_in(
        f,
        core,
        graph,
        root,
        &g::VerificationContext::new(f.verifier.clone()),
    )
}
struct Bundle {
    graph: Graph,
    admission: Digest,
    proposal: Digest,
    rpc: Digest,
    records: BTreeMap<usize, Vec<g::issuance::Record<Digest>>>,
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
    let mut records = BTreeMap::new();
    for owner in f.schemes.len() - q..f.schemes.len() {
        let mut state = prior.map_or_else(
            || {
                State::new::<Sha256>(f.schemes[owner].clone(), core.clone(), input(), G_LIMITS)
                    .unwrap()
            },
            |prior| {
                let mut state = State::for_replay::<Sha256>(
                    f.schemes[owner].clone(),
                    core.clone(),
                    input(),
                    G_LIMITS,
                )
                .unwrap();
                for record in &prior.records[&owner] {
                    let authority = match record.action() {
                        g::issuance::Action::Enter { authority, .. } => Some(*authority),
                        g::issuance::Action::Reserve { authority, .. } => *authority,
                        _ => None,
                    };
                    if let Some(authority) = authority {
                        match &prior.graph[&authority] {
                            r::Material::Entry(proof) => {
                                let cap =
                                    entry_in(f, core, proof, proofs, &state.verification_context());
                                state
                                    .restore::<Sha256, _>(
                                        &mut TestRng::new(4106),
                                        record,
                                        g::issuance::Material::Entry(&cap),
                                        |_| true,
                                        |_, _| true,
                                        &Sequential,
                                    )
                                    .unwrap();
                            }
                            _ => {
                                let cap = verified_in(
                                    f,
                                    core,
                                    &prior.graph,
                                    authority,
                                    &state.verification_context(),
                                );
                                state
                                    .restore::<Sha256, _>(
                                        &mut TestRng::new(4107),
                                        record,
                                        g::issuance::Material::Recovery(&cap),
                                        |_| true,
                                        |_, _| true,
                                        &Sequential,
                                    )
                                    .unwrap();
                            }
                        }
                    } else {
                        state
                            .restore::<Sha256, _>(
                                &mut TestRng::new(4108),
                                record,
                                g::issuance::Material::None,
                                |_| true,
                                |_, _| true,
                                &Sequential,
                            )
                            .unwrap();
                    }
                }
                state.finish_replay().unwrap();
                state
            },
        );
        if let Some(prior) = prior {
            let proposal = verified_in(
                f,
                core,
                &prior.graph,
                prior.proposal,
                &state.verification_context(),
            );
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
        let entered = entry_in(f, core, proof, proofs, &state.verification_context());
        state.enter::<Sha256>(&entered).unwrap();
        let reservation = state.reserve_recover::<Sha256>(&entered, None).unwrap();
        let notice = state.sign_reserved(&reservation).unwrap();
        state
            .record_signed::<Sha256, _>(&mut TestRng::new(4109), &reservation, &notice, &Sequential)
            .unwrap();
        let mut owner_records = Vec::new();
        while let Some(page) = state.history_page(owner_records.len()) {
            owner_records.push(page.record().clone());
        }
        records.insert(owner, owner_records);
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
        records,
    }
}

#[test]
fn recovery_subject_is_five_exact_fixed_width_commitments() {
    let subject = r::Subject {
        core: Digest::from([1; 32]),
        input: Digest::from([2; 32]),
        entry: Digest::from([3; 32]),
        proposal: Digest::from([4; 32]),
        decision: Digest::from([5; 32]),
    };
    let bytes = subject.encode();
    let expected = (1..=5).flat_map(|value| [value; 32]).collect::<Vec<u8>>();
    assert_eq!(bytes.as_ref(), expected);
    assert_eq!(
        r::Subject::<Digest>::decode(bytes.clone()).unwrap(),
        subject
    );
    for len in 0..bytes.len() {
        assert!(r::Subject::<Digest>::decode(bytes.slice(..len)).is_err());
    }
    let mut trailing = bytes.to_vec();
    trailing.push(0);
    assert!(r::Subject::<Digest>::decode(Bytes::from(trailing)).is_err());
}

#[test]
fn valid_signed_wrong_propose_body_does_not_invoke_build() {
    let f = fixture(8);
    let core = core(&f);
    let proof = initial(&f, &core, 0);
    let proofs = [(proof.artifact_id::<Sha256>(), proof.clone())]
        .into_iter()
        .collect();
    let mut b = bundle(&f, &core, &proof, &proofs, None);
    let r::Material::Proposal {
        admission,
        endorsement,
    } = b.graph[&b.proposal].clone()
    else {
        unreachable!()
    };
    let mut message = endorsement.message;
    let g::Kind::Recovery { subject, .. } = &mut message.kind else {
        unreachable!()
    };
    subject.proposal = Digest::from([240; 32]);
    let endorsement = g::Signed::sign(
        &f.schemes[usize::from(proof.target().leader)],
        message,
        G_LIMITS,
    )
    .unwrap();
    assert!(endorsement.verify(&mut TestRng::new(4201), &f.verifier, G_LIMITS, &Sequential));
    let wrong = insert(
        &mut b.graph,
        r::Material::Proposal {
            admission,
            endorsement,
        },
    );
    let calls = Cell::new(0);
    let result = r::verify::<Sha256, _, _, _>(
        &mut TestRng::new(4202),
        &g::VerificationContext::new(f.verifier),
        &core,
        input(),
        wrong,
        |id| b.graph.get(id),
        G_LIMITS,
        bounds(),
        |_| true,
        |_, _| true,
        |_, _| {
            calls.set(calls.get() + 1);
            true
        },
        &Sequential,
    );
    assert!(
        result.is_err(),
        "unrelated signed BodyID cannot authenticate this admission"
    );
    assert_eq!(
        calls.get(),
        0,
        "wrong signed BodyID must fail before application Build"
    );
}

fn body(b: &Bundle) -> r::ProposalBody<Digest> {
    let r::Material::Admission(body) = &b.graph[&b.admission] else {
        unreachable!()
    };
    body.clone()
}
fn phase_message(
    core: &g::Core<Digest>,
    proof: &Proof,
    body: &r::ProposalBody<Digest>,
    phase: r::Phase,
) -> g::Message<Digest> {
    g::Message {
        slot: core.slot.id::<Sha256>(),
        round: proof.target().ballot,
        leader: proof.target().leader,
        kind: g::Kind::Recovery {
            phase,
            subject: r::Subject {
                core: core.id::<Sha256>(),
                input: input(),
                entry: proof.target().id::<Sha256>(),
                proposal: body.id::<Sha256>(),
                decision: body.value.id::<Sha256>(),
            },
        },
    }
}
fn phase_quorum(
    f: &Fixture<S>,
    message: g::Message<Digest>,
    offset: usize,
) -> g::Quorum<S, Digest> {
    let q = g::Committee::new(f.schemes.len()).unwrap().quorum();
    let votes: Vec<_> = f
        .schemes
        .iter()
        .skip(offset)
        .take(q)
        .map(|s| g::Signed::sign(s, message.clone(), G_LIMITS).unwrap())
        .collect();
    g::Quorum::from_votes(
        &mut TestRng::new(4210),
        &f.verifier,
        &votes,
        G_LIMITS,
        &Sequential,
    )
    .unwrap()
}
fn seal(
    f: &Fixture<S>,
    core: &g::Core<Digest>,
    proof: &Proof,
    b: &mut Bundle,
    body: r::ProposalBody<Digest>,
) {
    b.admission = insert(&mut b.graph, r::Material::Admission(body.clone()));
    let endorsement = g::Signed::sign(
        &f.schemes[usize::from(proof.target().leader)],
        phase_message(core, proof, &body, r::Phase::Propose),
        G_LIMITS,
    )
    .unwrap();
    b.proposal = insert(
        &mut b.graph,
        r::Material::Proposal {
            admission: b.admission,
            endorsement,
        },
    );
    let quorum = phase_quorum(f, phase_message(core, proof, &body, r::Phase::Prepare), 0);
    b.rpc = insert(
        &mut b.graph,
        r::Material::Rpc {
            proposal: b.proposal,
            quorum,
        },
    );
}
fn terminal(
    f: &Fixture<S>,
    core: &g::Core<Digest>,
    proof: &Proof,
    b: &mut Bundle,
    offset: usize,
) -> Digest {
    let quorum = phase_quorum(
        f,
        phase_message(core, proof, &body(b), r::Phase::Commit),
        offset,
    );
    insert(&mut b.graph, r::Material::Terminal { rpc: b.rpc, quorum })
}
fn with_calls(
    f: &Fixture<S>,
    core: &g::Core<Digest>,
    graph: &Graph,
    root: Digest,
    calls: &Cell<usize>,
) -> Result<r::Verified<Digest>, r::Error<Digest>> {
    r::verify::<Sha256, _, _, _>(
        &mut TestRng::new(4211),
        &g::VerificationContext::new(f.verifier.clone()),
        core,
        input(),
        root,
        |id| graph.get(id),
        G_LIMITS,
        bounds(),
        |_| true,
        |_, _| true,
        |rows, body| {
            calls.set(calls.get() + 1);
            rows.originals()
                .iter()
                .all(|s| matches!(&s.message.kind, g::Kind::Recover(row) if row.report.is_none()))
                && body.value.order.as_ref() == b"AB"
                && matches!(&body.choice, r::Choice::Fresh { population, build, material } if *population==Digest::from([135;32]) && build.is_empty() && material.is_empty())
        },
        &Sequential,
    )
}

#[test]
fn general_rosters_verify_fresh_rpc_terminal_and_later_exact_carry() {
    for n in [4, 7, 8, 9, 10, 11, 12, 13, 16, 31, 64] {
        let f = fixture(n);
        let core = core(&f);
        let first = initial(&f, &core, 0);
        let second = higher(&f, &core, &first);
        let proofs = [(first.artifact_id::<Sha256>(), first.clone())]
            .into_iter()
            .collect();
        let mut lower = bundle(&f, &core, &first, &proofs, None);
        let admission = verified(&f, &core, &lower.graph, lower.admission);
        let proposal = verified(&f, &core, &lower.graph, lower.proposal);
        let rpc = verified(&f, &core, &lower.graph, lower.rpc);
        assert_eq!(admission.role(), r::Role::Admission);
        assert_eq!(proposal.role(), r::Role::Proposal);
        assert_eq!(rpc.role(), r::Role::Rpc);
        assert_eq!(rpc.proposal(), lower.admission);
        assert_eq!(rpc.value().order.as_ref(), b"AB");
        assert_eq!(rpc.limits(), G_LIMITS);
        assert_eq!(rpc.core(), core.id::<Sha256>());
        assert_eq!(rpc.input(), input());
        assert_eq!(rpc.entry(), first.target().id::<Sha256>());
        assert_eq!(
            rpc.encoded_size(),
            lower.graph[&lower.rpc].encode_size() as u64
        );
        let q = g::Committee::new(n as usize).unwrap().quorum();
        assert_eq!(body(&lower).histories.len(), q);
        let last = body(&lower).histories[q - 1];
        let r::Material::History { notice, .. } = &lower.graph[&last] else {
            unreachable!()
        };
        assert_eq!(usize::from(notice.attestation.signer), n as usize - 1);
        let mut upper = bundle(&f, &core, &second, &proofs, Some(&lower));
        let mut carry = body(&upper);
        carry.positive = vec![lower.rpc];
        carry.choice = r::Choice::Carry(lower.rpc);
        seal(&f, &core, &second, &mut upper, carry);
        let carried = verified(&f, &core, &upper.graph, upper.rpc);
        assert_eq!(carried.attempt(), 1);
        assert_eq!(carried.round(), second.target().ballot);
        assert_eq!(carried.decision(), rpc.decision());
        assert_eq!(carried.value(), rpc.value());
        assert_eq!(carried.origin(), lower.proposal);
        let finished = terminal(&f, &core, &first, &mut lower, 1);
        assert_eq!(
            verified(&f, &core, &lower.graph, finished).role(),
            r::Role::Terminal
        );
        assert_eq!(
            verified(&f, &core, &lower.graph, finished).decision(),
            carried.decision()
        );
    }
}

#[test]
fn fence_only_data_histories_cannot_become_authoritative_recover_rows() {
    let f = fixture(8);
    let core = core(&f);
    let proof = initial(&f, &core, 0);
    let proofs = [(proof.artifact_id::<Sha256>(), proof.clone())]
        .into_iter()
        .collect();
    let entered = entry(&f, &core, &proof, &proofs);
    let mut b = bundle(&f, &core, &proof, &proofs, None);
    let q = g::Committee::new(f.schemes.len()).unwrap().quorum();
    let mut histories = Vec::new();
    for owner in f.schemes.len() - q..f.schemes.len() {
        let mut state =
            State::new::<Sha256>(f.schemes[owner].clone(), core.clone(), input(), G_LIMITS)
                .unwrap();
        state
            .fence::<Sha256>(proof.target().ballot, proof.target().leader)
            .unwrap();
        let message = state
            .capture_history::<Sha256>(
                proof.target().ballot,
                proof.target().leader,
                entered.id(),
                None,
            )
            .unwrap();
        let notice = g::Signed::sign(&f.schemes[owner], message, G_LIMITS).unwrap();
        let g::Kind::Recover(row) = &notice.message.kind else {
            unreachable!()
        };
        assert!((0..row.snapshot.count() as usize).all(|index| !matches!(
            state.history_page(index).unwrap().record().action(),
            g::issuance::Action::Enter { .. }
        )));
        for index in 0..row.snapshot.count() as usize {
            insert(
                &mut b.graph,
                r::Material::Page(state.history_page(index).unwrap()),
            );
        }
        histories.push(insert(
            &mut b.graph,
            r::Material::History {
                entry: proof.artifact_id::<Sha256>(),
                notice,
            },
        ));
    }
    let mut candidate = body(&b);
    candidate.histories = histories;
    let root = insert(&mut b.graph, r::Material::Admission(candidate));
    let calls = Cell::new(0);
    let result = with_calls(&f, &core, &b.graph, root, &calls);
    assert!(
        result.is_err(),
        "data-only floor history is not authenticated entered recovery"
    );
    assert_eq!(
        calls.get(),
        0,
        "missing Enter must be rejected before application Build"
    );
}

#[test]
fn valid_signed_wrong_prepare_and_commit_bodies_do_not_invoke_build() {
    let f = fixture(8);
    let core = core(&f);
    let proof = initial(&f, &core, 0);
    let proofs = [(proof.artifact_id::<Sha256>(), proof.clone())]
        .into_iter()
        .collect();
    let mut b = bundle(&f, &core, &proof, &proofs, None);
    for phase in [r::Phase::Prepare, r::Phase::Commit] {
        let mut message = phase_message(&core, &proof, &body(&b), phase);
        let g::Kind::Recovery { subject, .. } = &mut message.kind else {
            unreachable!()
        };
        subject.proposal = Digest::from([241; 32]);
        let quorum = phase_quorum(&f, message, 0);
        assert!(quorum.verify(&mut TestRng::new(4220), &f.verifier, G_LIMITS, &Sequential));
        let material = match phase {
            r::Phase::Prepare => r::Material::Rpc {
                proposal: b.proposal,
                quorum,
            },
            r::Phase::Commit => r::Material::Terminal { rpc: b.rpc, quorum },
            _ => unreachable!(),
        };
        let root = insert(&mut b.graph, material);
        let calls = Cell::new(0);
        assert!(with_calls(&f, &core, &b.graph, root, &calls).is_err());
        assert_eq!(
            calls.get(),
            0,
            "unrelated valid certificate must fail before Build"
        );
    }
}

#[test]
fn missing_material_bad_signatures_and_all_global_budgets_fail_before_build() {
    let f = fixture(10);
    let core = core(&f);
    let proof = initial(&f, &core, 0);
    let proofs = [(proof.artifact_id::<Sha256>(), proof.clone())]
        .into_iter()
        .collect();
    let b = bundle(&f, &core, &proof, &proofs, None);
    let mut absent = vec![proof.artifact_id::<Sha256>(), body(&b).histories[0]];
    absent.push(
        *b.graph
            .iter()
            .find(|(_, m)| matches!(m, r::Material::Page(_)))
            .unwrap()
            .0,
    );
    for missing in absent {
        let mut graph = b.graph.clone();
        graph.remove(&missing);
        let calls = Cell::new(0);
        assert!(
            matches!(with_calls(&f, &core, &graph, b.rpc, &calls), Err(r::Error::Missing(id)) if id == missing)
        );
        assert_eq!(calls.get(), 0);
    }
    let mut graph = b.graph.clone();
    let r::Material::Proposal {
        admission,
        mut endorsement,
    } = graph[&b.proposal].clone()
    else {
        unreachable!()
    };
    endorsement.message.round = round(99);
    let root = insert(
        &mut graph,
        r::Material::Proposal {
            admission,
            endorsement,
        },
    );
    let calls = Cell::new(0);
    assert!(with_calls(&f, &core, &graph, root, &calls).is_err());
    assert_eq!(calls.get(), 0);
    for which in 0..6 {
        let mut budget = bounds();
        match which {
            0 => budget.nodes = 0,
            1 => budget.links = 0,
            2 => budget.encoded_bytes = 0,
            3 => budget.work = 0,
            4 => budget.entry.signatures = 0,
            _ => budget.history.pages = 0,
        }
        let calls = Cell::new(0);
        let result = r::verify::<Sha256, _, _, _>(
            &mut TestRng::new(4221),
            &g::VerificationContext::new(f.verifier.clone()),
            &core,
            input(),
            b.rpc,
            |id| b.graph.get(id),
            G_LIMITS,
            budget,
            |_| true,
            |_, _| true,
            |_, _| {
                calls.set(calls.get() + 1);
                true
            },
            &Sequential,
        );
        assert!(result.is_err(), "budget {which}");
        assert_eq!(calls.get(), 0, "budget {which}");
    }
}

#[test]
fn frozen_population_requires_q_distinct_sorted_matching_original_owners() {
    let f = fixture(9);
    let core = core(&f);
    let proof = initial(&f, &core, 0);
    let proofs = [(proof.artifact_id::<Sha256>(), proof.clone())]
        .into_iter()
        .collect();
    let mut b = bundle(&f, &core, &proof, &proofs, None);
    for which in 0..3 {
        let mut candidate = body(&b);
        match which {
            0 => {
                candidate.histories.pop();
            }
            1 => candidate.histories[1] = candidate.histories[0],
            _ => candidate.histories.reverse(),
        }
        let root = insert(&mut b.graph, r::Material::Admission(candidate));
        let calls = Cell::new(0);
        assert!(with_calls(&f, &core, &b.graph, root, &calls).is_err());
        assert_eq!(calls.get(), 0);
    }
}

#[test]
fn rpc_subset_aliases_share_unsigned_subject_but_different_bodies_do_not() {
    let f = fixture(8);
    let core = core(&f);
    let proof = initial(&f, &core, 0);
    let alias = initial(&f, &core, 1);
    assert_eq!(proof.target(), alias.target());
    assert_ne!(proof.artifact_id::<Sha256>(), alias.artifact_id::<Sha256>());
    let proofs = [(proof.artifact_id::<Sha256>(), proof.clone())]
        .into_iter()
        .collect();
    let mut b = bundle(&f, &core, &proof, &proofs, None);
    let original = verified(&f, &core, &b.graph, b.rpc);
    let quorum = phase_quorum(
        &f,
        phase_message(&core, &proof, &body(&b), r::Phase::Prepare),
        1,
    );
    let alias_rpc = insert(
        &mut b.graph,
        r::Material::Rpc {
            proposal: b.proposal,
            quorum,
        },
    );
    let checked = verified(&f, &core, &b.graph, alias_rpc);
    assert_ne!(alias_rpc, b.rpc);
    assert_eq!(original.proposal(), checked.proposal());
    assert_eq!(original.decision(), checked.decision());
    let finish = terminal(&f, &core, &proof, &mut b, 0);
    let r::Material::Terminal { quorum, .. } = b.graph[&finish].clone() else {
        unreachable!()
    };
    let second_finish = insert(
        &mut b.graph,
        r::Material::Terminal {
            rpc: alias_rpc,
            quorum,
        },
    );
    assert_eq!(
        verified(&f, &core, &b.graph, second_finish).decision(),
        original.decision()
    );
    insert(&mut b.graph, r::Material::Entry(alias.clone()));
    let mut other = body(&b);
    other.entry = alias.artifact_id::<Sha256>();
    let a = phase_message(&core, &proof, &body(&b), r::Phase::Prepare);
    let c = phase_message(&core, &alias, &other, r::Phase::Prepare);
    assert_ne!(a, c);
    assert_eq!(body(&b).value, other.value);
    let q = g::Committee::new(f.schemes.len()).unwrap().quorum();
    let mut votes: Vec<_> = f
        .schemes
        .iter()
        .take(q)
        .enumerate()
        .map(|(owner, s)| {
            g::Signed::sign(s, if owner == 0 { c.clone() } else { a.clone() }, G_LIMITS).unwrap()
        })
        .collect();
    assert!(
        g::Quorum::from_votes(
            &mut TestRng::new(4222),
            &f.verifier,
            &votes,
            G_LIMITS,
            &Sequential
        )
        .is_err()
    );
    votes[0] = votes[1].clone();
    assert!(
        g::Quorum::from_votes(
            &mut TestRng::new(4223),
            &f.verifier,
            &votes,
            G_LIMITS,
            &Sequential
        )
        .is_err()
    );
    votes.pop();
    assert!(
        g::Quorum::from_votes(
            &mut TestRng::new(4224),
            &f.verifier,
            &votes,
            G_LIMITS,
            &Sequential
        )
        .is_err()
    );
}

#[test]
fn higher_entry_witness_alias_preserves_each_owners_exact_enter_authority() {
    let f = fixture(8);
    let core = core(&f);
    let proof = initial(&f, &core, 0);
    let alias = initial(&f, &core, 1);
    let proofs = [(proof.artifact_id::<Sha256>(), proof.clone())]
        .into_iter()
        .collect();
    let mut b = bundle(&f, &core, &proof, &proofs, None);
    let alias_id = insert(&mut b.graph, r::Material::Entry(alias));
    let mut candidate = body(&b);
    candidate.entry = alias_id;
    for id in &candidate.histories {
        let r::Material::History { notice, .. } = &b.graph[id] else {
            unreachable!()
        };
        let g::Kind::Recover(row) = &notice.message.kind else {
            unreachable!()
        };
        let r::Material::Page(page) = &b.graph[&row.snapshot.head().unwrap()] else {
            unreachable!()
        };
        assert!(
            matches!(page.record().action(), g::issuance::Action::Enter { authority, .. } if *authority == proof.artifact_id::<Sha256>())
        );
    }
    let root = insert(&mut b.graph, r::Material::Admission(candidate));
    assert_eq!(
        verified(&f, &core, &b.graph, root).entry(),
        proof.target().id::<Sha256>()
    );
}

#[test]
fn retry_closure_chooses_highest_prior_rpc_and_never_fresh_or_changed_value() {
    let f = fixture(10);
    let core = core(&f);
    let first = initial(&f, &core, 0);
    let second = higher(&f, &core, &first);
    let third = higher(&f, &core, &second);
    let mut proofs = [(first.artifact_id::<Sha256>(), first.clone())]
        .into_iter()
        .collect();
    let lower = bundle(&f, &core, &first, &proofs, None);
    let middle = bundle(&f, &core, &second, &proofs, Some(&lower));
    proofs.insert(second.artifact_id::<Sha256>(), second);
    let mut upper = bundle(&f, &core, &third, &proofs, Some(&middle));
    let mut candidate = body(&upper);
    candidate.positive = vec![lower.rpc, middle.rpc];
    candidate.positive.sort();
    candidate.choice = r::Choice::Carry(middle.rpc);
    let valid = insert(&mut upper.graph, r::Material::Admission(candidate.clone()));
    let carried = verified(&f, &core, &upper.graph, valid);
    assert_eq!(carried.attempt(), 2);
    assert_eq!(
        carried.decision(),
        verified(&f, &core, &middle.graph, middle.rpc).decision()
    );
    candidate.choice = r::Choice::Carry(lower.rpc);
    let wrong = insert(&mut upper.graph, r::Material::Admission(candidate.clone()));
    assert!(with_calls(&f, &core, &upper.graph, wrong, &Cell::new(0)).is_err());
    candidate.choice = r::Choice::Fresh {
        population: Digest::from([135; 32]),
        build: Bytes::new(),
        material: Bytes::new(),
    };
    let fresh = insert(&mut upper.graph, r::Material::Admission(candidate.clone()));
    assert!(with_calls(&f, &core, &upper.graph, fresh, &Cell::new(0)).is_err());
    candidate.choice = r::Choice::Carry(middle.rpc);
    candidate.value.order = Bytes::from_static(b"BA");
    let changed = insert(&mut upper.graph, r::Material::Admission(candidate));
    assert!(with_calls(&f, &core, &upper.graph, changed, &Cell::new(0)).is_err());
}

#[test]
fn complete_terminal_requires_catchup_and_same_ballot_rpc_precludes_fresh() {
    let f = fixture(8);
    let core = core(&f);
    let first = initial(&f, &core, 0);
    let second = higher(&f, &core, &first);
    let proofs = [(first.artifact_id::<Sha256>(), first.clone())]
        .into_iter()
        .collect();
    let mut lower = bundle(&f, &core, &first, &proofs, None);
    let finish = terminal(&f, &core, &first, &mut lower, 0);
    let mut same = body(&lower);
    same.positive = vec![lower.rpc];
    let root = insert(&mut lower.graph, r::Material::Admission(same));
    assert!(
        matches!(with_calls(&f, &core, &lower.graph, root, &Cell::new(0)), Err(r::Error::Stale(id)) if id == lower.rpc)
    );
    let mut upper = bundle(&f, &core, &second, &proofs, Some(&lower));
    let mut candidate = body(&upper);
    candidate.positive = vec![finish];
    let root = insert(&mut upper.graph, r::Material::Admission(candidate));
    assert!(
        matches!(with_calls(&f, &core, &upper.graph, root, &Cell::new(0)), Err(r::Error::Catchup(id)) if id == finish)
    );
    upper.graph.remove(&lower.rpc);
    assert!(
        matches!(with_calls(&f, &core, &upper.graph, root, &Cell::new(0)), Err(r::Error::Missing(id)) if id == lower.rpc)
    );
}

fn fast_origin(f: &Fixture<S>, core: &g::Core<Digest>) -> g::Origin<S, Digest> {
    let mut owners = core.followers.clone();
    owners.push(core.leader);
    owners.sort();
    let firsts = owners
        .into_iter()
        .map(|owner| {
            g::Signed::sign(
                &f.schemes[usize::from(owner)],
                g::Message {
                    slot: core.slot.id::<Sha256>(),
                    round: core.slot.proposal.round,
                    leader: core.leader,
                    kind: g::Kind::First(g::First {
                        core: core.id::<Sha256>(),
                        input: input(),
                        owner,
                        report: (owner != core.leader)
                            .then(|| Bytes::from(vec![owner.get() as u8])),
                        preference: (owner != core.leader).then(|| Bytes::from_static(b"AB")),
                    }),
                },
                G_LIMITS,
            )
            .unwrap()
        })
        .collect();
    let body = g::OriginBody {
        decision: g::Decision {
            slot: core.slot.clone(),
            input: input(),
            order: Bytes::from_static(b"AB"),
        },
        core: core.clone(),
        firsts,
        population: Digest::from([140; 32]),
        build: Bytes::new(),
        material: Bytes::new(),
    };
    let selection = g::Signed::sign(
        &f.schemes[usize::from(core.leader)],
        g::Message {
            slot: core.slot.id::<Sha256>(),
            round: core.slot.proposal.round,
            leader: core.leader,
            kind: g::Kind::Select {
                body: body.id::<Sha256>(),
                decision: body.decision.id::<Sha256>(),
            },
        },
        G_LIMITS,
    )
    .unwrap();
    g::Origin { body, selection }
}
fn fast_quorum(
    f: &Fixture<S>,
    core: &g::Core<Digest>,
    origin: &g::Origin<S, Digest>,
) -> g::Quorum<S, Digest> {
    phase_quorum(
        f,
        g::Message {
            slot: core.slot.id::<Sha256>(),
            round: core.slot.proposal.round,
            leader: core.leader,
            kind: g::Kind::Phase {
                phase: g::Phase::FastFinal,
                decision: origin.body.decision.id::<Sha256>(),
            },
        },
        0,
    )
}

#[test]
fn original_fast_origin_in_frozen_history_is_carried_and_full_terminal_catches_up() {
    for n in [7, 9, 10, 13, 16] {
        let f = fixture(n);
        let core = core(&f);
        let proof = initial(&f, &core, 0);
        let proofs = [(proof.artifact_id::<Sha256>(), proof.clone())]
            .into_iter()
            .collect();
        let mut b = bundle(&f, &core, &proof, &proofs, None);
        let origin = fast_origin(&f, &core);
        let origin_id = insert(&mut b.graph, r::Material::Origin(origin.clone()));
        let q = g::Committee::new(n as usize).unwrap().quorum();
        let mut histories = Vec::new();
        for owner in f.schemes.len() - q..f.schemes.len() {
            let mut state =
                State::new::<Sha256>(f.schemes[owner].clone(), core.clone(), input(), G_LIMITS)
                    .unwrap();
            if owner == f.schemes.len() - q {
                state
                    .retain_origin::<Sha256, _>(
                        &mut TestRng::new(4230),
                        &origin,
                        |_| true,
                        |_, _| true,
                        &Sequential,
                    )
                    .unwrap();
            }
            let entered = entry_in(&f, &core, &proof, &proofs, &state.verification_context());
            state.enter::<Sha256>(&entered).unwrap();
            let reservation = state.reserve_recover::<Sha256>(&entered, None).unwrap();
            let notice = state.sign_reserved(&reservation).unwrap();
            let g::Kind::Recover(row) = &notice.message.kind else {
                unreachable!()
            };
            for index in 0..row.snapshot.count() as usize {
                insert(
                    &mut b.graph,
                    r::Material::Page(state.history_page(index).unwrap()),
                );
            }
            histories.push(insert(
                &mut b.graph,
                r::Material::History {
                    entry: proof.artifact_id::<Sha256>(),
                    notice,
                },
            ));
        }
        let mut candidate = body(&b);
        candidate.histories = histories;
        candidate.choice = r::Choice::Carry(origin_id);
        let root = insert(&mut b.graph, r::Material::Admission(candidate.clone()));
        let checked = verified(&f, &core, &b.graph, root);
        assert_eq!(checked.origin(), origin_id);
        assert_eq!(checked.value(), &origin.body.decision);
        candidate.choice = r::Choice::Fresh {
            population: Digest::from([135; 32]),
            build: Bytes::new(),
            material: Bytes::new(),
        };
        let fresh = insert(&mut b.graph, r::Material::Admission(candidate.clone()));
        assert!(with_calls(&f, &core, &b.graph, fresh, &Cell::new(0)).is_err());
        let quorum = fast_quorum(&f, &core, &origin);
        let terminal = insert(
            &mut b.graph,
            r::Material::FastTerminal {
                origin: origin_id,
                quorum,
            },
        );
        candidate.positive = vec![terminal];
        let root = insert(&mut b.graph, r::Material::Admission(candidate));
        assert!(
            matches!(with_calls(&f, &core, &b.graph, root, &Cell::new(0)), Err(r::Error::Catchup(id)) if id == terminal)
        );
        b.graph.remove(&origin_id);
        assert!(
            matches!(with_calls(&f, &core, &b.graph, root, &Cell::new(0)), Err(r::Error::Missing(id)) if id == origin_id)
        );
    }
}

#[test]
fn recovery_tokens_require_exact_local_verification_context_and_raw_reverification_after_restart() {
    let f = fixture(8);
    let core = core(&f);
    let proof = initial(&f, &core, 0);
    let proofs = [(proof.artifact_id::<Sha256>(), proof.clone())]
        .into_iter()
        .collect();
    let b = bundle(&f, &core, &proof, &proofs, None);
    let mut state =
        State::new::<Sha256>(f.schemes[7].clone(), core.clone(), input(), G_LIMITS).unwrap();
    let ctx = state.verification_context();
    let entered = entry_in(&f, &core, &proof, &proofs, &ctx);
    state.enter::<Sha256>(&entered).unwrap();
    let independent = verified(&f, &core, &b.graph, b.proposal);
    assert!(
        state.reserve_prepare::<Sha256>(&independent).is_err(),
        "equal keys/profile are not shared scope identity"
    );
    let local = verified_in(&f, &core, &b.graph, b.proposal, &ctx.clone());
    let reserved = state.reserve_prepare::<Sha256>(&local).unwrap();
    let foreign = ed25519::fixture(
        &mut TestRng::new(101),
        b"_COMMONWARE_CONSENSUS_G1_FOREIGN_RECOVERY_TEST",
        8,
    );
    assert_eq!(f.verifier.participants(), foreign.verifier.participants());
    let foreign_core = self::core(&foreign);
    assert_eq!(foreign_core, core);
    let foreign_proof = initial(&foreign, &core, 0);
    let foreign_proofs = [(foreign_proof.artifact_id::<Sha256>(), foreign_proof.clone())]
        .into_iter()
        .collect();
    let foreign_bundle = bundle(&foreign, &core, &foreign_proof, &foreign_proofs, None);
    let foreign_checked = verified(&foreign, &core, &foreign_bundle.graph, foreign_bundle.rpc);
    assert!(
        with_calls(
            &f,
            &core,
            &foreign_bundle.graph,
            foreign_bundle.rpc,
            &Cell::new(0)
        )
        .is_err(),
        "local crypto rejects foreign namespace"
    );
    assert!(state.retain_rpc::<Sha256>(&foreign_checked).is_err());
    assert!(
        state.sign_reserved(&reserved).is_ok(),
        "failed foreign receipt must not poison the local choice"
    );
    let mut restarted =
        State::for_replay::<Sha256>(f.schemes[7].clone(), core.clone(), input(), G_LIMITS).unwrap();
    restarted.finish_replay().unwrap();
    assert!(
        restarted.enter::<Sha256>(&entered).is_err(),
        "a fresh replay context cannot consume the pre-crash entry token"
    );
    assert!(
        restarted.reserve_prepare::<Sha256>(&local).is_err(),
        "fresh State must reverify raw evidence in its own context"
    );
    let restarted_context = restarted.verification_context();
    let entry_after = entry_in(&f, &core, &proof, &proofs, &restarted_context);
    restarted.enter::<Sha256>(&entry_after).unwrap();
    let proposal_after = verified_in(&f, &core, &b.graph, b.proposal, &restarted_context);
    assert_eq!(
        restarted
            .reserve_prepare::<Sha256>(&proposal_after)
            .unwrap()
            .message(),
        reserved.message()
    );
}

type CodecCorpus = (
    Vec<r::Material<S, Digest>>,
    r::ProposalBody<Digest>,
    r::ProposalBody<Digest>,
    r::Subject<Digest>,
);
fn codec_corpus(f: &Fixture<S>) -> CodecCorpus {
    let core = core(f);
    let proof = initial(f, &core, 0);
    let proofs = [(proof.artifact_id::<Sha256>(), proof.clone())]
        .into_iter()
        .collect();
    let mut b = bundle(f, &core, &proof, &proofs, None);
    terminal(f, &core, &proof, &mut b, 0);
    let origin = fast_origin(f, &core);
    let original = insert(&mut b.graph, r::Material::Origin(origin.clone()));
    insert(&mut b.graph, r::Material::Body(origin.body.clone()));
    let quorum = fast_quorum(f, &core, &origin);
    insert(&mut b.graph, r::Material::FastQuorum(quorum.clone()));
    insert(
        &mut b.graph,
        r::Material::FastTerminal {
            origin: original,
            quorum,
        },
    );
    insert(&mut b.graph, r::Material::Entry(higher(f, &core, &proof)));
    let fresh = body(&b);
    let mut carried = fresh.clone();
    carried.positive = vec![original];
    carried.choice = r::Choice::Carry(original);
    let g::Kind::Recovery { subject, .. } =
        phase_message(&core, &proof, &fresh, r::Phase::Propose).kind
    else {
        unreachable!()
    };
    (b.graph.into_values().collect(), fresh, carried, subject)
}

#[test]
fn every_material_variant_and_proposal_choice_has_strict_bounded_codec() {
    let f = fixture(8);
    let cfg = (G_LIMITS, f.verifier.certificate_codec_config());
    let (materials, fresh, carried, _) = codec_corpus(&f);
    let tags: std::collections::BTreeSet<_> = materials.iter().map(|m| m.encode()[8]).collect();
    assert_eq!(tags, (0..=10).collect());
    for m in &materials {
        let bytes = m.encode();
        let decoded = r::Material::<S, Digest>::decode_cfg(bytes.clone(), &cfg).unwrap();
        assert_eq!(decoded.encode(), bytes);
        assert_eq!(decoded.id::<Sha256>(), m.id::<Sha256>());
        for cut in 0..bytes.len() {
            assert!(r::Material::<S, Digest>::decode_cfg(bytes.slice(..cut), &cfg).is_err());
        }
        for (offset, value) in [(0, b'X'), (3, b'2'), (8, 255)] {
            let mut bad = bytes.to_vec();
            bad[offset] = value;
            assert!(r::Material::<S, Digest>::decode_cfg(Bytes::from(bad), &cfg).is_err());
        }
        let mut huge = bytes.to_vec();
        huge[4..8].copy_from_slice(&u32::MAX.to_be_bytes());
        assert!(r::Material::<S, Digest>::decode_cfg(Bytes::from(huge), &cfg).is_err());
        let mut trailing = bytes.to_vec();
        trailing.push(0);
        assert!(r::Material::<S, Digest>::decode_cfg(Bytes::from(trailing), &cfg).is_err());
    }
    for proposal in [fresh.clone(), carried] {
        assert_eq!(
            r::ProposalBody::<Digest>::decode_cfg(proposal.encode(), &G_LIMITS).unwrap(),
            proposal
        );
    }
    let mut excess = fresh.clone();
    excess.histories.resize(65, Digest::from([244; 32]));
    assert!(r::ProposalBody::<Digest>::decode_cfg(excess.encode(), &G_LIMITS).is_err());
    for which in 0..3 {
        let mut excess = fresh.clone();
        match which {
            0 => excess.value.order = Bytes::from(vec![0; G_LIMITS.order_bytes + 1]),
            _ => {
                let r::Choice::Fresh {
                    build, material, ..
                } = &mut excess.choice
                else {
                    unreachable!()
                };
                if which == 1 {
                    *build = Bytes::from(vec![0; G_LIMITS.build_bytes + 1]);
                } else {
                    *material = Bytes::from(vec![0; G_LIMITS.material_bytes + 1]);
                }
            }
        }
        assert!(r::ProposalBody::<Digest>::decode_cfg(excess.encode(), &G_LIMITS).is_err());
    }
}

struct GeneralRecoveryConformance;
impl Conformance for GeneralRecoveryConformance {
    async fn commit(seed: u64) -> Vec<u8> {
        let f = ed25519::fixture(
            &mut TestRng::new(seed),
            b"_COMMONWARE_CONSENSUS_G1_RECOVERY_CONFORMANCE",
            8,
        );
        let (materials, fresh, carried, subject) = codec_corpus(&f);
        let mut frames = vec![subject.encode(), fresh.encode(), carried.encode()];
        frames.extend(materials.iter().map(|m| m.encode()));
        frames.encode().to_vec()
    }
}
conformance_tests! { GeneralRecoveryConformance => 32 }

#[cfg(feature = "arbitrary")]
mod arbitrary_conformance {
    use super::*;
    use commonware_codec::conformance::CodecConformance;
    conformance_tests! {
        CodecConformance<r::Subject<Digest>> => 32,
        CodecConformance<r::ProposalBody<Digest>> => 32,
        CodecConformance<r::Material<S,Digest>> => 32,
    }
}

#[test]
fn invalid_root_can_validate_authenticated_dependencies_without_fresh_admission() {
    let f = fixture(8);
    let core = core(&f);
    let proof = initial(&f, &core, 0);
    let proofs = [(proof.artifact_id::<Sha256>(), proof.clone())]
        .into_iter()
        .collect();
    let mut b = bundle(&f, &core, &proof, &proofs, None);
    let origin = fast_origin(&f, &core);
    insert(&mut b.graph, r::Material::Origin(origin.clone()));
    let q = g::Committee::new(f.schemes.len()).unwrap().quorum();
    let mut histories = Vec::new();
    for owner in f.schemes.len() - q..f.schemes.len() {
        let mut state =
            State::new::<Sha256>(f.schemes[owner].clone(), core.clone(), input(), G_LIMITS)
                .unwrap();
        if owner == f.schemes.len() - q {
            state
                .retain_origin::<Sha256, _>(
                    &mut TestRng::new(4240),
                    &origin,
                    |_| true,
                    |_, _| true,
                    &Sequential,
                )
                .unwrap();
        }
        state
            .fence::<Sha256>(proof.target().ballot, proof.target().leader)
            .unwrap();
        let message = state
            .capture_history::<Sha256>(
                proof.target().ballot,
                proof.target().leader,
                proof.target().id::<Sha256>(),
                None,
            )
            .unwrap();
        let notice = g::Signed::sign(&f.schemes[owner], message, G_LIMITS).unwrap();
        let g::Kind::Recover(row) = &notice.message.kind else {
            unreachable!()
        };
        for index in 0..row.snapshot.count() as usize {
            insert(
                &mut b.graph,
                r::Material::Page(state.history_page(index).unwrap()),
            );
        }
        histories.push(insert(
            &mut b.graph,
            r::Material::History {
                entry: proof.artifact_id::<Sha256>(),
                notice,
            },
        ));
    }
    let mut candidate = body(&b);
    candidate.histories = histories;
    let root = insert(&mut b.graph, r::Material::Admission(candidate));
    let original_calls = Cell::new(0);
    let fresh_calls = Cell::new(0);
    let result = r::verify::<Sha256, _, _, _>(
        &mut TestRng::new(4241),
        &g::VerificationContext::new(f.verifier),
        &core,
        input(),
        root,
        |id| b.graph.get(id),
        G_LIMITS,
        bounds(),
        |_| true,
        |_, body| {
            original_calls.set(original_calls.get() + 1);
            body.decision.order.as_ref() == b"AB"
        },
        |_, _| {
            fresh_calls.set(fresh_calls.get() + 1);
            true
        },
        &Sequential,
    );
    assert!(
        result.is_err(),
        "a checked dependency cannot authorize a malformed root"
    );
    assert_eq!(fresh_calls.get(), 0);
    assert!(
        original_calls.get() > 0,
        "bounded dependency replay precedes later semantic root rejection"
    );
}
