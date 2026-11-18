//! Actual crypto for bounded entry provenance, not native deadline/admission.
use super::*;
use commonware_consensus::simplex::{
    extension::agreement::general::{self as g, entry},
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
const BOUNDS: entry::Bounds = entry::Bounds {
    nodes: 256,
    encoded_bytes: 64 * 1024 * 1024,
    signatures: 16_384,
    depth: 64,
};
type EProof = entry::Proof<S, Digest>;

fn core(f: &Fixture<S>) -> g::Core<Digest> {
    let c = g::Committee::new(f.schemes.len()).unwrap();
    let leader = Participant::new(c.len() as u32 - 1);
    g::Core {
        slot: g::Slot {
            profile: Digest::from([130; 32]),
            domain: Digest::from([131; 32]),
            roster: g::Slot::<Digest>::roster::<Sha256, _>(&f.verifier),
            cut: 19,
            proposal: Proposal::new(round(4), View::new(3), Digest::from([132; 32])),
            parent: g::NativeParent::Proposal {
                round: round(3),
                digest: Digest::from([133; 32]),
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
    Digest::from([134; 32])
}

fn target(core: &g::Core<Digest>, n: usize, attempt: u64) -> entry::Target<Digest> {
    entry::Target {
        core: core.id::<Sha256>(),
        input: input(),
        attempt,
        ballot: Round::new(
            core.slot.proposal.round.epoch(),
            View::new(core.slot.proposal.round.view().get() + 1 + attempt),
        ),
        leader: Participant::new((attempt % n as u64) as u32),
    }
}

fn initial(f: &Fixture<S>, core: &g::Core<Digest>, offset: usize) -> EProof {
    let q = g::Committee::new(f.schemes.len()).unwrap().quorum();
    let votes = f.schemes[offset..offset + q]
        .iter()
        .map(|scheme| Notarize::sign(scheme, core.slot.proposal.clone()).unwrap())
        .collect::<Vec<_>>();
    EProof::Initial {
        target: target(core, f.schemes.len(), 0),
        notarization: Notarization::from_notarizes(&f.verifier, non_empty![@&votes], &Sequential)
            .unwrap(),
    }
}

fn higher(
    f: &Fixture<S>,
    core: &g::Core<Digest>,
    attempt: u64,
    predecessors: &[Digest],
    offset: usize,
) -> EProof {
    let q = g::Committee::new(f.schemes.len()).unwrap().quorum();
    let target = target(core, f.schemes.len(), attempt);
    let wishes = f.schemes[offset..offset + q]
        .iter()
        .enumerate()
        .map(|(index, scheme)| {
            g::Signed::sign(
                scheme,
                g::Message {
                    slot: core.slot.id::<Sha256>(),
                    round: target.ballot,
                    leader: target.leader,
                    kind: g::Kind::Wish(entry::Wish {
                        target: target.clone(),
                        predecessor: predecessors[index % predecessors.len()],
                    }),
                },
                G_LIMITS,
            )
            .unwrap()
        })
        .collect();
    EProof::Higher { target, wishes }
}

fn verify<'a>(
    f: &Fixture<S>,
    core: &'a g::Core<Digest>,
    proof: &'a EProof,
    graph: &'a BTreeMap<Digest, EProof>,
    bounds: entry::Bounds,
) -> Result<entry::VerifiedEntry<'a, S, Digest>, entry::Error> {
    entry::verify::<Sha256, _, _, _>(
        &mut TestRng::new(201),
        &g::VerificationContext::new(f.verifier.clone()),
        core,
        input(),
        proof,
        G_LIMITS,
        bounds,
        |id| graph.get(id),
        &Sequential,
    )
}

#[test]
fn native_nqc_and_mixed_predecessor_aliases_verify_with_public_keys_for_general_rosters() {
    for n in [4, 7, 8, 9, 10, 11, 12, 13, 16, 31, 64] {
        let f = fixture(n);
        let core = core(&f);
        let a = initial(&f, &core, 0);
        let b = initial(&f, &core, 1);
        assert_ne!(a.artifact_id::<Sha256>(), b.artifact_id::<Sha256>());
        let empty = BTreeMap::new();
        let checked_a = verify(&f, &core, &a, &empty, BOUNDS).unwrap();
        let checked_b = verify(&f, &core, &b, &empty, BOUNDS).unwrap();
        assert_eq!(checked_a.id(), checked_b.id());
        assert_eq!(checked_a.target().leader, Participant::new(0));
        assert_ne!(core.leader, checked_a.target().leader);
        assert_eq!(checked_a.encoded_size(), a.encode_size());
        assert_eq!(checked_a.verified_bytes(), a.encode_size() as u64);
        assert_eq!(checked_a.limits(), G_LIMITS);
        assert_eq!(checked_a.bounds(), BOUNDS);

        let mut graph = BTreeMap::from([
            (a.artifact_id::<Sha256>(), a),
            (b.artifact_id::<Sha256>(), b),
        ]);
        let predecessor_roots = graph.keys().copied().collect::<Vec<_>>();
        let first = higher(&f, &core, 1, &predecessor_roots, 0);
        let alias = higher(&f, &core, 1, &predecessor_roots, 1);
        let checked = verify(&f, &core, &first, &graph, BOUNDS).unwrap();
        let checked_alias = verify(&f, &core, &alias, &graph, BOUNDS).unwrap();
        assert_eq!(checked.id(), checked_alias.id());
        assert_ne!(checked.artifact_id(), checked_alias.artifact_id());
        assert!(std::ptr::eq(checked.proof(), &first));
        assert_eq!(checked.core(), &core);
        assert_eq!(checked.encoded_size(), first.encode_size());
        assert_eq!(
            checked.verified_bytes(),
            (first.encode_size() + graph.values().map(EncodeSize::encode_size).sum::<usize>())
                as u64
        );
        let first_root = first.artifact_id::<Sha256>();
        graph.insert(first_root, first);
        let second = higher(&f, &core, 2, &[first_root], 0);
        verify(&f, &core, &second, &graph, BOUNDS).unwrap();
    }
}

#[test]
fn complete_coordinator_rotation_reaches_highest_owner_with_flat_bounded_provenance() {
    for n in [4, 8, 64] {
        let f = fixture(n);
        let core = core(&f);
        let first = initial(&f, &core, 0);
        let mut root = first.artifact_id::<Sha256>();
        let mut graph = BTreeMap::from([(root, first)]);
        let c = g::Committee::new(n as usize).unwrap();
        for attempt in 1..u64::from(n) {
            let proof = higher(&f, &core, attempt, &[root], c.len() - c.quorum());
            root = proof.artifact_id::<Sha256>();
            graph.insert(root, proof);
        }
        let proof = &graph[&root];
        let bounds = entry::Bounds {
            nodes: n,
            encoded_bytes: graph.values().map(EncodeSize::encode_size).sum::<usize>() as u64,
            signatures: (c.len() + (c.len() - 1) * c.quorum()) as u32,
            depth: u64::from(n - 1),
        };
        let checked = verify(&f, &core, proof, &graph, bounds).unwrap();
        assert_eq!(checked.target().leader, Participant::new(n - 1));
        assert_eq!(checked.target().attempt, u64::from(n - 1));
        assert_eq!(checked.verified_bytes(), bounds.encoded_bytes);
        let EProof::Higher { wishes, .. } = proof else {
            unreachable!()
        };
        assert_eq!(
            wishes.last().unwrap().attestation.signer,
            Participant::new(n - 1)
        );
    }
}

#[test]
fn exact_q_is_native_n_minus_f_in_slack_rosters_and_duplicate_owners_never_add_support() {
    for n in [8, 9, 11, 12, 14, 64] {
        let f = fixture(n);
        let core = core(&f);
        let initial = initial(&f, &core, 0);
        let initial_root = initial.artifact_id::<Sha256>();
        let graph = BTreeMap::from([(initial_root, initial)]);
        let good = higher(&f, &core, 1, &[initial_root], 0);
        verify(&f, &core, &good, &graph, BOUNDS).unwrap();
        let EProof::Higher { wishes, .. } = &good else {
            unreachable!()
        };
        let c = g::Committee::new(n as usize).unwrap();
        assert!(c.quorum() > 2 * c.faults() + 1 || n == 64);
        let mut short = good.clone();
        let EProof::Higher {
            wishes: short_wishes,
            ..
        } = &mut short
        else {
            unreachable!()
        };
        short_wishes.truncate(2 * c.faults() + 1);
        if short_wishes.len() < wishes.len() {
            assert_eq!(
                verify(&f, &core, &short, &graph, BOUNDS).unwrap_err(),
                entry::Error::Quorum
            );
        }
        let mut duplicate = good.clone();
        {
            let EProof::Higher { wishes, .. } = &mut duplicate else {
                unreachable!()
            };
            wishes[1] = wishes[0].clone();
        }
        assert_eq!(
            verify(&f, &core, &duplicate, &graph, BOUNDS).unwrap_err(),
            entry::Error::Identity
        );
        if let EProof::Higher { wishes, .. } = &mut duplicate {
            wishes.swap(0, 2);
        }
        assert_eq!(
            verify(&f, &core, &duplicate, &graph, BOUNDS).unwrap_err(),
            entry::Error::Identity
        );
    }
}

#[test]
fn initial_nqc_and_expected_core_input_are_not_replaceable_by_peer_context() {
    let f = fixture(10);
    let core = core(&f);
    let good = initial(&f, &core, 0);
    let empty = BTreeMap::new();
    verify(&f, &core, &good, &empty, BOUNDS).unwrap();
    let mut wrong_p = good.clone();
    let EProof::Initial { notarization, .. } = &mut wrong_p else {
        unreachable!()
    };
    notarization.proposal.payload = Digest::from([155; 32]);
    assert_eq!(
        verify(&f, &core, &wrong_p, &empty, BOUNDS).unwrap_err(),
        entry::Error::Context
    );
    let mut invalid_signature = good.clone();
    let EProof::Initial { notarization, .. } = &mut invalid_signature else {
        unreachable!()
    };
    let mut other_core = core.clone();
    other_core.slot.proposal.payload = Digest::from([156; 32]);
    let EProof::Initial {
        notarization: other,
        ..
    } = initial(&f, &other_core, 0)
    else {
        unreachable!()
    };
    notarization.certificate = other.certificate;
    assert_eq!(
        verify(&f, &core, &invalid_signature, &empty, BOUNDS).unwrap_err(),
        entry::Error::Signature
    );
    for field in 0..6 {
        let mut changed = core.clone();
        match field {
            0 => changed.slot.profile = Digest::from([150; 32]),
            1 => changed.slot.domain = Digest::from([151; 32]),
            2 => changed.slot.cut += 1,
            3 => {
                changed.slot.parent = g::NativeParent::Proposal {
                    round: round(3),
                    digest: Digest::from([152; 32]),
                }
            }
            4 => changed.leader = Participant::new(1),
            _ => changed.followers[0] = Participant::new(1),
        }
        assert!(verify(&f, &changed, &good, &empty, BOUNDS).is_err());
    }
    assert!(
        entry::verify::<Sha256, _, _, _>(
            &mut TestRng::new(1),
            &g::VerificationContext::new(f.verifier),
            &core,
            Digest::from([157; 32]),
            &good,
            G_LIMITS,
            BOUNDS,
            |_| None,
            &Sequential
        )
        .is_err()
    );
    let other_roster = ed25519::fixture(
        &mut TestRng::new(999),
        b"_COMMONWARE_CONSENSUS_AGREEMENT_TEST",
        10,
    );
    assert!(
        entry::verify::<Sha256, _, _, _>(
            &mut TestRng::new(1),
            &g::VerificationContext::new(other_roster.verifier),
            &core,
            input(),
            &good,
            G_LIMITS,
            BOUNDS,
            |_| None,
            &Sequential
        )
        .is_err()
    );
}

#[test]
fn foreign_crypto_namespace_entry_token_cannot_authorize_local_state() {
    let local = fixture(10);
    // The same deterministic key generation gives the same ordered roster,
    // while the native signing namespace is a distinct verification scope.
    let foreign = ed25519::fixture(
        &mut TestRng::new(101),
        b"_COMMONWARE_CONSENSUS_AGREEMENT_FOREIGN_TEST",
        10,
    );
    let core = core(&local);
    assert_eq!(
        g::Slot::<Digest>::roster::<Sha256, _>(&local.verifier),
        g::Slot::<Digest>::roster::<Sha256, _>(&foreign.verifier),
    );
    let proof = initial(&foreign, &core, 0);
    let empty = BTreeMap::new();
    let foreign_entry = verify(&foreign, &core, &proof, &empty, BOUNDS).unwrap();
    assert!(verify(&local, &core, &proof, &empty, BOUNDS).is_err());

    let mut local_state = g::issuance::State::new::<Sha256>(
        local.schemes[0].clone(),
        core.clone(),
        input(),
        G_LIMITS,
    )
    .unwrap();
    let before = local_state.records().to_vec();
    assert!(local_state.enter::<Sha256>(&foreign_entry).is_err());
    assert_eq!(local_state.records(), before);
}

#[test]
fn only_the_states_read_only_context_clones_authorize_entry_consumption() {
    let f = fixture(9);
    let core = core(&f);
    let proof = initial(&f, &core, 0);
    let mut state =
        g::issuance::State::new::<Sha256>(f.schemes[0].clone(), core.clone(), input(), G_LIMITS)
            .unwrap();
    let cloned = state.verification_context();
    let checked = entry::verify::<Sha256, _, _, _>(
        &mut TestRng::new(1),
        &cloned,
        &core,
        input(),
        &proof,
        G_LIMITS,
        BOUNDS,
        |_| None,
        &Sequential,
    )
    .unwrap();
    state.enter::<Sha256>(&checked).unwrap();

    // A fresh local context is deliberately a different capability, even when
    // its cryptographic key material and namespace are equivalent.
    let independent = g::VerificationContext::new(f.schemes[0].clone());
    let independent_entry = entry::verify::<Sha256, _, _, _>(
        &mut TestRng::new(2),
        &independent,
        &core,
        input(),
        &proof,
        G_LIMITS,
        BOUNDS,
        |_| None,
        &Sequential,
    )
    .unwrap();
    let before = state.records().to_vec();
    assert!(state.enter::<Sha256>(&independent_entry).is_err());
    assert_eq!(state.records(), before);
}

#[test]
fn missing_wrong_root_cycles_future_and_skipped_predecessors_are_errors() {
    let f = fixture(13);
    let core = core(&f);
    let initial = initial(&f, &core, 0);
    let root = initial.artifact_id::<Sha256>();
    let good = higher(&f, &core, 1, &[root], 0);
    assert_eq!(
        verify(&f, &core, &good, &BTreeMap::new(), BOUNDS).unwrap_err(),
        entry::Error::Missing
    );
    let bad_root = Digest::from([158; 32]);
    let wrong_root = higher(&f, &core, 1, &[bad_root], 0);
    assert_eq!(
        verify(
            &f,
            &core,
            &wrong_root,
            &BTreeMap::from([(bad_root, initial.clone())]),
            BOUNDS
        )
        .unwrap_err(),
        entry::Error::Context
    );
    let graph = BTreeMap::from([(root, initial)]);
    let skipped = higher(&f, &core, 2, &[root], 0);
    assert_eq!(
        verify(&f, &core, &skipped, &graph, BOUNDS).unwrap_err(),
        entry::Error::Context
    );
    let future = higher(&f, &core, 2, &[bad_root], 0);
    let future_root = future.artifact_id::<Sha256>();
    let lower = higher(&f, &core, 1, &[future_root], 0);
    assert_eq!(
        verify(
            &f,
            &core,
            &lower,
            &BTreeMap::from([(future_root, future)]),
            BOUNDS
        )
        .unwrap_err(),
        entry::Error::Context
    );
    let cycle = higher(&f, &core, 1, &[bad_root], 0);
    assert!(
        entry::verify::<Sha256, _, _, _>(
            &mut TestRng::new(1),
            &g::VerificationContext::new(f.verifier),
            &core,
            input(),
            &cycle,
            G_LIMITS,
            BOUNDS,
            |_| Some(&cycle),
            &Sequential
        )
        .is_err()
    );
}

#[test]
fn exact_predecessor_signature_cannot_be_replaced_by_a_valid_semantic_alias() {
    let f = fixture(10);
    let core = core(&f);
    let a = initial(&f, &core, 0);
    let b = initial(&f, &core, 1);
    let a_root = a.artifact_id::<Sha256>();
    let b_root = b.artifact_id::<Sha256>();
    let graph = BTreeMap::from([(a_root, a), (b_root, b)]);
    let mut substituted = higher(&f, &core, 1, &[a_root], 0);
    let EProof::Higher { wishes, .. } = &mut substituted else {
        unreachable!()
    };
    let g::Kind::Wish(wish) = &mut wishes[0].message.kind else {
        unreachable!()
    };
    wish.predecessor = b_root;
    assert_eq!(
        verify(&f, &core, &substituted, &graph, BOUNDS).unwrap_err(),
        entry::Error::Signature
    );
}

#[test]
fn mapping_rejects_wrong_epoch_ballot_coordinator_and_checked_view_exhaustion() {
    let f = fixture(64);
    let core = core(&f);
    let good = initial(&f, &core, 0);
    for field in 0..4 {
        let mut wrong = good.clone();
        let EProof::Initial { target, .. } = &mut wrong else {
            unreachable!()
        };
        match field {
            0 => target.ballot = Round::new(Epoch::new(2), View::new(5)),
            1 => target.ballot = round(6),
            2 => target.leader = Participant::new(63),
            _ => target.input = Digest::from([159; 32]),
        }
        assert_eq!(
            verify(&f, &core, &wrong, &BTreeMap::new(), BOUNDS).unwrap_err(),
            entry::Error::Context
        );
    }
    let mut exhausted = core.clone();
    exhausted.slot.proposal.round = round(u64::MAX);
    let target = entry::Target {
        core: exhausted.id::<Sha256>(),
        input: input(),
        attempt: 0,
        ballot: round(0),
        leader: Participant::new(0),
    };
    let EProof::Initial { notarization, .. } = good else {
        unreachable!()
    };
    let proof = EProof::Initial {
        target,
        notarization,
    };
    assert_eq!(
        verify(&f, &exhausted, &proof, &BTreeMap::new(), BOUNDS).unwrap_err(),
        entry::Error::Context
    );
    let overflow_target = entry::Target {
        core: core.id::<Sha256>(),
        input: input(),
        attempt: u64::MAX,
        ballot: round(1),
        leader: Participant::new(63),
    };
    let mut proof = higher(&f, &core, 1, &[Digest::from([160; 32])], 0);
    let EProof::Higher { target, wishes } = &mut proof else {
        unreachable!()
    };
    *target = overflow_target.clone();
    for signed in wishes {
        signed.message.round = overflow_target.ballot;
        signed.message.leader = overflow_target.leader;
        signed.message.kind = g::Kind::Wish(entry::Wish {
            target: overflow_target.clone(),
            predecessor: Digest::from([160; 32]),
        });
    }
    assert_eq!(
        verify(
            &f,
            &core,
            &proof,
            &BTreeMap::new(),
            entry::Bounds {
                depth: u64::MAX,
                ..BOUNDS
            }
        )
        .unwrap_err(),
        entry::Error::Context
    );
}

#[test]
fn distinct_graph_nodes_bytes_signature_work_and_depth_are_independently_bounded() {
    let f = fixture(10);
    let core = core(&f);
    let initial = initial(&f, &core, 0);
    let initial_root = initial.artifact_id::<Sha256>();
    let proof = higher(&f, &core, 1, &[initial_root], 0);
    let graph = BTreeMap::from([(initial_root, initial)]);
    let c = g::Committee::new(10).unwrap();
    let exact = entry::Bounds {
        nodes: 2,
        encoded_bytes: (proof.encode_size() + graph[&initial_root].encode_size()) as u64,
        signatures: (c.len() + c.quorum()) as u32,
        depth: 1,
    };
    verify(&f, &core, &proof, &graph, exact).unwrap();
    for bounds in [
        entry::Bounds {
            nodes: exact.nodes - 1,
            ..exact
        },
        entry::Bounds {
            encoded_bytes: exact.encoded_bytes - 1,
            ..exact
        },
        entry::Bounds {
            signatures: exact.signatures - 1,
            ..exact
        },
        entry::Bounds { depth: 0, ..exact },
    ] {
        assert_eq!(
            verify(&f, &core, &proof, &graph, bounds).unwrap_err(),
            entry::Error::Limit
        );
    }
    let calls = Cell::new(0);
    assert_eq!(
        entry::verify::<Sha256, _, _, _>(
            &mut TestRng::new(1),
            &g::VerificationContext::new(f.verifier),
            &core,
            input(),
            &proof,
            G_LIMITS,
            entry::Bounds { nodes: 1, ..exact },
            |_| {
                calls.set(calls.get() + 1);
                None
            },
            &Sequential
        )
        .unwrap_err(),
        entry::Error::Limit
    );
    assert_eq!(calls.get(), 0);
}

#[test]
fn entry_closure_has_its_own_budget_and_does_not_reuse_the_origin_envelope_cap() {
    let f = fixture(64);
    let core = core(&f);
    let initial = initial(&f, &core, 0);
    let root = initial.artifact_id::<Sha256>();
    let proof = higher(&f, &core, 1, &[root], 0);
    let graph = BTreeMap::from([(root, initial)]);
    // Zero optional original fields make the complete advertised Origin fit
    // below this q-WISH root. Entry uses an independent explicit byte budget.
    let limits = g::Limits {
        report_bytes: 0,
        order_bytes: 0,
        build_bytes: 0,
        material_bytes: 0,
        origin_bytes: proof.encode_size() - 1,
    };
    limits.validate::<S, Digest>(&core).unwrap();
    let bytes = (proof.encode_size() + graph[&root].encode_size()) as u64;
    let bounds = entry::Bounds {
        encoded_bytes: bytes,
        ..BOUNDS
    };
    let checked = entry::verify::<Sha256, _, _, _>(
        &mut TestRng::new(1),
        &g::VerificationContext::new(f.verifier.clone()),
        &core,
        input(),
        &proof,
        limits,
        bounds,
        |id| graph.get(id),
        &Sequential,
    )
    .unwrap();
    assert!(checked.encoded_size() > checked.limits().origin_bytes);
    assert_eq!(checked.verified_bytes(), bytes);
    assert_eq!(
        entry::verify::<Sha256, _, _, _>(
            &mut TestRng::new(1),
            &g::VerificationContext::new(f.verifier),
            &core,
            input(),
            &proof,
            limits,
            entry::Bounds {
                encoded_bytes: bytes - 1,
                ..bounds
            },
            |id| graph.get(id),
            &Sequential,
        )
        .unwrap_err(),
        entry::Error::Limit
    );
}

#[test]
fn wish_role_domain_is_not_the_original_g1_signed_domain() {
    let f = fixture(10);
    let core = core(&f);
    let initial = initial(&f, &core, 0);
    let root = initial.artifact_id::<Sha256>();
    let graph = BTreeMap::from([(root, initial)]);
    let mut proof = higher(&f, &core, 1, &[root], 0);
    let EProof::Higher { wishes, .. } = &mut proof else {
        unreachable!()
    };
    let encoded = wishes[0].message.encode();
    let bytes = [b"_COMMONWARE_CONSENSUS_G1_SIGNED_V1".as_slice(), &encoded].concat();
    wishes[0].attestation = f.schemes[0]
        .sign::<Digest>(Subject::ExtensionAgreement {
            round: wishes[0].message.round,
            payload: &bytes,
        })
        .unwrap();
    assert_eq!(
        verify(&f, &core, &proof, &graph, BOUNDS).unwrap_err(),
        entry::Error::Signature
    );
}

thread_local! {
    static ENTRY_HASH_CALLS: Cell<usize> = const { Cell::new(0) };
}

#[derive(Default)]
struct EntryHashProbe(Sha256);
impl commonware_cryptography::Hasher for EntryHashProbe {
    type Digest = Digest;
    fn hash(parts: &[&[u8]]) -> Digest {
        ENTRY_HASH_CALLS.with(|calls| calls.set(calls.get() + 1));
        Sha256::hash(parts)
    }
    fn hash_pair(left: &[&[u8]], right: &[&[u8]]) -> (Digest, Digest) {
        (Self::hash(left), Self::hash(right))
    }
    fn update(&mut self, bytes: &[u8]) -> &mut Self {
        self.0.update(bytes);
        self
    }
    fn finalize(self) -> (Self, Digest) {
        let (hasher, digest) = self.0.finalize();
        (Self(hasher), digest)
    }
}

#[test]
fn raw_root_cardinality_signed_field_and_byte_limits_precede_all_hashing() {
    let f = fixture(4);
    let core = core(&f);
    let initial = initial(&f, &core, 0);
    let root = initial.artifact_id::<Sha256>();
    let proof = higher(&f, &core, 1, &[root], 0);
    let mut too_many = proof.clone();
    let EProof::Higher { wishes, .. } = &mut too_many else {
        unreachable!()
    };
    wishes.push(wishes[0].clone());
    let mut bad_field = proof.clone();
    let EProof::Higher { wishes, .. } = &mut bad_field else {
        unreachable!()
    };
    wishes[0].message.kind = g::Kind::First(g::First {
        core: core.id::<Sha256>(),
        input: input(),
        owner: Participant::new(0),
        report: Some(Bytes::from(vec![0; G_LIMITS.report_bytes + 1])),
        preference: None,
    });
    for (candidate, bounds) in [
        (&too_many, BOUNDS),
        (&bad_field, BOUNDS),
        (
            &proof,
            entry::Bounds {
                encoded_bytes: proof.encode_size() as u64 - 1,
                ..BOUNDS
            },
        ),
    ] {
        ENTRY_HASH_CALLS.with(|calls| calls.set(0));
        let lookups = Cell::new(0);
        assert!(
            entry::verify::<EntryHashProbe, _, _, _>(
                &mut TestRng::new(1),
                &g::VerificationContext::new(f.verifier.clone()),
                &core,
                input(),
                candidate,
                G_LIMITS,
                bounds,
                |_| {
                    lookups.set(lookups.get() + 1);
                    None
                },
                &Sequential,
            )
            .is_err()
        );
        assert_eq!(ENTRY_HASH_CALLS.with(Cell::get), 0);
        assert_eq!(lookups.get(), 0);
    }
}

#[test]
fn target_wish_and_flat_proof_codecs_reject_type_version_truncation_and_trailing_data() {
    let f = fixture(8);
    let core = core(&f);
    let initial = initial(&f, &core, 0);
    let root = initial.artifact_id::<Sha256>();
    let higher = higher(&f, &core, 1, &[root], 0);
    let cfg = (G_LIMITS, f.verifier.certificate_codec_config());
    for proof in [&initial, &higher] {
        let bytes = proof.encode();
        assert_eq!(
            EProof::decode_cfg(bytes.clone(), &cfg).unwrap().encode(),
            bytes
        );
        assert_eq!(&bytes[..4], b"G1U1");
        for cut in 0..bytes.len() {
            assert!(EProof::decode_cfg(bytes.slice(..cut), &cfg).is_err());
        }
        let mut trailing = bytes.to_vec();
        trailing.push(0);
        assert!(EProof::decode_cfg(Bytes::from(trailing), &cfg).is_err());
        let mut unknown_version = bytes.to_vec();
        unknown_version[3] = b'2';
        assert!(EProof::decode_cfg(Bytes::from(unknown_version), &cfg).is_err());
        let mut origin_type = bytes.to_vec();
        origin_type[..4].copy_from_slice(b"G1E1");
        assert!(EProof::decode_cfg(Bytes::from(origin_type), &cfg).is_err());
    }
    let target = higher.target();
    assert_eq!(
        entry::Target::<Digest>::decode(target.encode()).unwrap(),
        *target
    );
    let wish = entry::Wish {
        target: target.clone(),
        predecessor: root,
    };
    assert_eq!(entry::Wish::<Digest>::decode(wish.encode()).unwrap(), wish);
    let empty_count = 8 + target.encode_size() + 1;
    let mut too_many = higher.encode().to_vec();
    too_many[empty_count..empty_count + 4].copy_from_slice(&65u32.to_be_bytes());
    assert!(EProof::decode_cfg(Bytes::from(too_many), &cfg).is_err());
}

struct GeneralEntryConformance;
impl Conformance for GeneralEntryConformance {
    async fn commit(seed: u64) -> Vec<u8> {
        let sizes = [4, 7, 8, 9, 10, 11, 12, 13, 16, 31, 64];
        let n = sizes[seed as usize % sizes.len()];
        let f = fixture(n);
        let core = core(&f);
        let a = initial(&f, &core, 0);
        let b = initial(&f, &core, 1);
        let proof = higher(
            &f,
            &core,
            1,
            &[a.artifact_id::<Sha256>(), b.artifact_id::<Sha256>()],
            0,
        );
        let EProof::Higher { wishes, .. } = &proof else {
            unreachable!()
        };
        vec![
            a.target().encode(),
            a.encode(),
            b.encode(),
            proof.encode(),
            wishes[0].encode(),
        ]
        .encode()
        .to_vec()
    }
}
conformance_tests! { GeneralEntryConformance => 32 }

#[cfg(feature = "arbitrary")]
mod arbitrary_conformance {
    use super::*;
    use commonware_codec::conformance::CodecConformance;
    conformance_tests! {
        CodecConformance<entry::Target<Digest>> => 32,
        CodecConformance<entry::Wish<Digest>> => 32,
        CodecConformance<EProof> => 32,
    }
}
