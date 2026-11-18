//! Bounds must precede semantic identity work at the joint-normal replay port.
use super::{general_normal as fixture, *};
use commonware_consensus::simplex::{
    extension::agreement::general::{self as g, issuance::State, normal},
    types::Notarization,
};
use commonware_utils::iter::NonEmpty;
use std::cell::Cell;

thread_local! {
    static WATCH_DECISION: Cell<bool> = const { Cell::new(false) };
    static DECISION_HASHES: Cell<usize> = const { Cell::new(0) };
}

// Keep real SHA-256 identities. Observe only hashing of the public Decision
// frame; bounded fixed context/roster work is not counted as material identity.
#[derive(Default)]
struct DecisionHashProbe(Sha256);

impl commonware_cryptography::Hasher for DecisionHashProbe {
    type Digest = Digest;

    fn hash(parts: &[&[u8]]) -> Self::Digest {
        if WATCH_DECISION.with(Cell::get) && parts.iter().any(|part| part.starts_with(b"G1D1")) {
            DECISION_HASHES.with(|calls| calls.set(calls.get() + 1));
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

fn reject_before_identity(oversize_order: bool, replay: bool) {
    let f = fixture(8);
    let c = fixture::core(&f);
    let original = fixture::origin(&f, &c, b"AB", false);
    let owner = (0..f.schemes.len())
        .find(|owner| {
            let p = Participant::from_usize(*owner);
            p != c.leader && !c.followers.contains(&p)
        })
        .unwrap();
    let mut live = fixture::local(&f, &c, owner);
    let prefix = fixture::prime(&mut live, &c, &original);
    let reservation = fixture::reserve(&mut live, &original);
    let mut oversized = original.clone();
    if oversize_order {
        oversized.body.decision.order = Bytes::from(vec![0; fixture::G_LIMITS.order_bytes + 1]);
    } else {
        oversized.body.build = Bytes::from(vec![0; fixture::G_LIMITS.build_bytes + 1]);
    }
    assert!(g::Origin::<S, Digest>::decode_cfg(oversized.encode(), &fixture::G_LIMITS).is_err());

    // Ensure the observer would detect real identity work with unchanged IDs.
    WATCH_DECISION.set(true);
    DECISION_HASHES.set(0);
    let checked = original.body.decision.id::<DecisionHashProbe>();
    WATCH_DECISION.set(false);
    assert_eq!(DECISION_HASHES.replace(0), 1);
    assert_eq!(checked, original.body.decision.id::<Sha256>());

    let mut state: State<S, Digest> = if replay {
        State::for_replay::<Sha256>(
            f.schemes[owner].clone(),
            c.clone(),
            fixture::input(),
            fixture::G_LIMITS,
        )
        .unwrap()
    } else {
        fixture::local(&f, &c, owner)
    };
    if replay {
        fixture::replay_prime(&mut state, &original, &prefix);
    } else {
        fixture::prime(&mut state, &c, &original);
    }
    let before = state.records().to_vec();
    let row_calls = Cell::new(0);
    let build_calls = Cell::new(0);
    let row = |r: &g::First<Digest>| {
        row_calls.set(row_calls.get() + 1);
        fixture::legal_row(r)
    };
    let build = |rows: &g::VerifiedRows<S, Digest>, body: &g::OriginBody<S, Digest>| {
        build_calls.set(build_calls.get() + 1);
        fixture::build_policy(rows, body)
    };
    WATCH_DECISION.set(true);
    DECISION_HASHES.set(0);
    let result = if replay {
        state.restore_normal::<DecisionHashProbe, _>(
            &mut TestRng::new(11101),
            &reservation,
            &oversized,
            row,
            build,
            &Sequential,
        )
    } else {
        state
            .reserve_normal::<DecisionHashProbe, _>(
                &mut TestRng::new(11102),
                &oversized,
                row,
                build,
                &Sequential,
            )
            .map(|_| ())
    };
    WATCH_DECISION.set(false);
    let identified = DECISION_HASHES.replace(0);
    assert_eq!(
        identified, 0,
        "out-of-profile material was identified before rejection: {result:?}"
    );
    assert_eq!(
        result,
        Err(g::issuance::Error::Verification(g::Error::Limit))
    );
    assert_eq!(row_calls.get(), 0);
    assert_eq!(build_calls.get(), 0);
    assert_eq!(state.records(), before.as_slice());
}

#[test]
fn replay_rejects_oversized_normal_order_before_decision_identification() {
    reject_before_identity(true, true);
}

#[test]
fn replay_rejects_oversized_normal_build_before_decision_identification() {
    reject_before_identity(false, true);
}

#[test]
fn live_reservation_rejects_oversized_normal_material_before_decision_identification() {
    reject_before_identity(true, false);
    reject_before_identity(false, false);
}

#[test]
fn raw_certificate_assembly_rejects_excess_firsts_before_decision_identification() {
    let f = fixture(8);
    let core = fixture::core(&f);
    let origin = fixture::origin(&f, &core, b"AB", false);
    let q = g::Committee::new(f.schemes.len()).unwrap().quorum();
    let firsts: Vec<_> = f
        .schemes
        .iter()
        .take(q)
        .map(|s| Notarize::sign(s, core.slot.proposal.clone()).unwrap())
        .collect();
    let notarization = Notarization::from_notarizes(
        &f.verifier,
        NonEmpty::new(&firsts[0], firsts.iter().skip(1)),
        &Sequential,
    )
    .unwrap();
    let pairs: Vec<_> = (0..q)
        .map(|owner| {
            let mut state = fixture::local(&f, &core, owner);
            fixture::prime(&mut state, &core, &origin);
            let reservation = fixture::reserve(&mut state, &origin);
            state.sign_normal::<Sha256>(&reservation).unwrap()
        })
        .collect();
    // Positive control uses the same real original, NQC, pairs and policy.
    normal::Certificate::assemble::<Sha256, _>(
        &mut TestRng::new(11103),
        &f.verifier,
        &core,
        fixture::input(),
        &origin,
        &notarization,
        &pairs,
        fixture::G_LIMITS,
        fixture::legal_row,
        fixture::build_policy,
        &Sequential,
    )
    .unwrap();

    let mut oversized = origin.clone();
    oversized
        .body
        .firsts
        .resize(65, origin.body.firsts[0].clone());
    assert!(oversized.encode_size() < fixture::G_LIMITS.origin_bytes);
    assert!(
        g::Origin::<S, Digest>::decode_cfg(oversized.encode(), &fixture::G_LIMITS,).is_err(),
        "the raw helper must enforce the decoder's shape ceiling"
    );

    WATCH_DECISION.set(true);
    DECISION_HASHES.set(0);
    let id = origin.body.decision.id::<DecisionHashProbe>();
    WATCH_DECISION.set(false);
    assert_eq!(DECISION_HASHES.replace(0), 1);
    assert_eq!(id, origin.body.decision.id::<Sha256>());

    let row_calls = Cell::new(0);
    let build_calls = Cell::new(0);
    WATCH_DECISION.set(true);
    DECISION_HASHES.set(0);
    let result = normal::Certificate::assemble::<DecisionHashProbe, _>(
        &mut TestRng::new(11104),
        &f.verifier,
        &core,
        fixture::input(),
        &oversized,
        &notarization,
        &pairs,
        fixture::G_LIMITS,
        |first| {
            row_calls.set(row_calls.get() + 1);
            fixture::legal_row(first)
        },
        |rows, body| {
            build_calls.set(build_calls.get() + 1);
            fixture::build_policy(rows, body)
        },
        &Sequential,
    )
    .map(|_| ());
    WATCH_DECISION.set(false);
    let hashes = DECISION_HASHES.replace(0);
    assert_eq!(
        hashes, 0,
        "out-of-shape original was identified before rejection: {result:?}"
    );
    assert_eq!(result, Err(g::Error::Limit));
    assert_eq!(row_calls.get(), 0);
    assert_eq!(build_calls.get(), 0);
}
