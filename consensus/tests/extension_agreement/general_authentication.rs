//! Authentication is distinct from captured context, policy and native admission.
use super::{general_normal as fixture, *};
use commonware_consensus::simplex::{
    extension::{
        agreement::general::{self as g, normal},
        vote,
    },
    scheme::{Scheme as NativeScheme, bls12381_multisig, secp256r1},
    types::Notarization,
};
use commonware_cryptography::{
    bls12381::primitives::variant::{MinPk, MinSig},
    certificate::{self, Scoped},
};
use std::{cell::Cell, sync::Arc};

const WIRE: g::Limits = g::Limits {
    report_bytes: g::MAX_FIRST_BYTES,
    order_bytes: g::MAX_FIRST_BYTES,
    build_bytes: g::MAX_FIRST_BYTES,
    material_bytes: g::MAX_FIRST_BYTES,
    origin_bytes: g::MAX_EVIDENCE_BYTES,
};

struct Bundle<T: certificate::Scheme> {
    core: g::Core<Digest>,
    origin: g::Origin<T, Digest>,
    pairs: Vec<normal::Vote<T, Digest>>,
    certificate: normal::Certificate<T, Digest>,
}

fn bundle<T: NativeScheme<Digest>>(f: &Fixture<T>) -> Bundle<T>
where
    T::Certificate: normal::CertificateSigners,
{
    let core = fixture::core(f);
    let origin = fixture::origin(f, &core, b"AB", false);
    let pairs: Vec<_> = (0..f.schemes.len())
        .map(|owner| {
            let mut state = fixture::local(f, &core, owner);
            fixture::prime(&mut state, &core, &origin);
            let reservation = fixture::reserve(&mut state, &origin);
            state.sign_normal::<Sha256>(&reservation).unwrap()
        })
        .collect();
    let q = g::Committee::new(f.schemes.len()).unwrap().quorum();
    let firsts: Vec<_> = f
        .schemes
        .iter()
        .take(q)
        .map(|s| Notarize::sign(s, core.slot.proposal.clone()).unwrap())
        .collect();
    let notarization =
        Notarization::from_notarizes(&f.verifier, non_empty![@&firsts], &Sequential).unwrap();
    let certificate = normal::Certificate::assemble::<Sha256, _>(
        &mut TestRng::new(13001),
        &f.verifier,
        &core,
        fixture::input(),
        &origin,
        &notarization,
        &pairs[f.schemes.len() - q..],
        fixture::G_LIMITS,
        fixture::legal_row,
        fixture::build_policy,
        &Sequential,
    )
    .unwrap();
    Bundle {
        core,
        origin,
        pairs,
        certificate,
    }
}

fn check<T: NativeScheme<Digest>>(f: Fixture<T>)
where
    T::Certificate: normal::CertificateSigners,
{
    let b = bundle(&f);
    let scoped = Scoped::verifier(Arc::new(f.verifier.clone()));
    let mut rng = TestRng::new(13002);
    b.origin
        .authenticate::<Sha256, _>(&mut rng, &f.verifier, fixture::G_LIMITS, &Sequential)
        .unwrap();
    b.origin
        .authenticate_scoped::<Sha256, _>(&mut rng, &scoped, WIRE, &Sequential)
        .unwrap();
    b.certificate
        .authenticate::<Sha256, _>(&mut rng, &f.verifier, fixture::G_LIMITS, &Sequential)
        .unwrap();
    b.certificate
        .authenticate_scoped::<Sha256, _>(&mut rng, &scoped, WIRE, &Sequential)
        .unwrap();
    let decoded = normal::Certificate::<T, Digest>::decode_cfg(
        b.certificate.encode(),
        &(WIRE, f.verifier.certificate_codec_config()),
    )
    .unwrap();
    decoded
        .authenticate_scoped::<Sha256, _>(&mut rng, &scoped, WIRE, &Sequential)
        .unwrap();
    for pair in &b.pairs {
        pair.authenticate::<Sha256, _>(&mut rng, &f.verifier, fixture::G_LIMITS, &Sequential)
            .unwrap();
        pair.authenticate_scoped::<Sha256, _>(&mut rng, &scoped, WIRE, &Sequential)
            .unwrap();
    }
    assert!(scoped.into_scheme().is_none());
    // Global inbound field ceilings describe actual received frames, rather
    // than promising every simultaneous maximum fits a local issuance profile.
    assert_eq!(WIRE.validate::<T, Digest>(&b.core), Err(g::Error::Limit));
    b.certificate
        .verify::<Sha256, _>(
            &mut rng,
            &f.verifier,
            &b.core,
            fixture::input(),
            fixture::G_LIMITS,
            fixture::legal_row,
            fixture::build_policy,
            &Sequential,
        )
        .unwrap();
    use normal::CertificateSigners as _;
    let owners = b.certificate.native.certificate.signers();
    assert_eq!(
        owners.count(),
        g::Committee::new(f.schemes.len()).unwrap().quorum()
    );
    assert_eq!(owners.len(), f.schemes.len());
    assert!(
        owners
            .iter()
            .any(|owner| usize::from(owner) == f.schemes.len() - 1)
    );
}

#[test]
fn authenticates_attributable_crypto_on_general_and_slack_rosters() {
    for n in [4, 7, 8, 9, 10, 11, 12, 13, 16, 31, 64] {
        check(ed25519::fixture(
            &mut TestRng::new(13003),
            b"g1_auth_ed25519",
            n,
        ));
    }
    for n in [4, 8, 9, 10, 16, 64] {
        check(secp256r1::fixture(
            &mut TestRng::new(13004),
            b"g1_auth_secp256r1",
            n,
        ));
        check(bls12381_multisig::fixture::<MinSig, _>(
            &mut TestRng::new(13005),
            b"g1_auth_minsig",
            n,
        ));
        check(bls12381_multisig::fixture::<MinPk, _>(
            &mut TestRng::new(13006),
            b"g1_auth_minpk",
            n,
        ));
    }
}

fn resign_selection(f: &Fixture<S>, origin: &mut g::Origin<S, Digest>) {
    origin.selection = g::Signed::sign(
        &f.schemes[usize::from(origin.body.core.leader)],
        g::Message {
            slot: origin.body.core.slot.id::<Sha256>(),
            round: origin.body.core.slot.proposal.round,
            leader: origin.body.core.leader,
            kind: g::Kind::Select {
                body: origin.body.id::<Sha256>(),
                decision: origin.body.decision.id::<Sha256>(),
            },
        },
        fixture::G_LIMITS,
    )
    .unwrap();
}

#[test]
fn authenticated_claims_cannot_replace_expected_context_or_build_policy() {
    let f = fixture(8);
    let b = bundle(&f);
    let mut wrong = b.core.clone();
    wrong.slot.profile = Digest::from([230; 32]);
    let calls = Cell::new(0);
    for (expected, input) in [
        (&wrong, fixture::input()),
        (&b.core, Digest::from([231; 32])),
    ] {
        assert_eq!(
            b.certificate.verify::<Sha256, _>(
                &mut TestRng::new(13007),
                &f.verifier,
                expected,
                input,
                fixture::G_LIMITS,
                |row| {
                    calls.set(calls.get() + 1);
                    fixture::legal_row(row)
                },
                fixture::build_policy,
                &Sequential,
            ),
            Err(g::Error::Context)
        );
    }
    assert_eq!(calls.get(), 0);
    let mut changed = b.certificate.clone();
    changed.origin.body.build = Bytes::from_static(b"not-the-prescribed-build");
    resign_selection(&f, &mut changed.origin);
    changed
        .authenticate::<Sha256, _>(
            &mut TestRng::new(13008),
            &f.verifier,
            fixture::G_LIMITS,
            &Sequential,
        )
        .unwrap();
    assert_eq!(
        changed.verify::<Sha256, _>(
            &mut TestRng::new(13009),
            &f.verifier,
            &b.core,
            fixture::input(),
            fixture::G_LIMITS,
            fixture::legal_row,
            fixture::build_policy,
            &Sequential,
        ),
        Err(g::Error::Policy)
    );
}

#[test]
fn origin_authentication_checks_every_original_select_and_fast_gate() {
    let f = fixture(8);
    let b = bundle(&f);
    for mutation in 0..8 {
        let mut bad = b.origin.clone();
        match mutation {
            0 => bad.body.firsts.swap(0, 1),
            1 => {
                bad.body.firsts.pop();
            }
            2 => {
                let g::Kind::First(row) = &mut bad.body.firsts[0].message.kind else {
                    unreachable!()
                };
                row.report = Some(Bytes::from_static(b"tampered"));
            }
            3 => bad.selection.attestation = bad.body.firsts[0].attestation.clone(),
            4 => bad.body.decision.slot.profile = Digest::from([232; 32]),
            5 => {
                bad.selection.message.kind = g::Kind::Phase {
                    phase: g::Phase::FastFinal,
                    decision: bad.body.decision.id::<Sha256>(),
                };
            }
            6 | 7 => {
                for signed in &mut bad.body.firsts {
                    let g::Kind::First(row) = &mut signed.message.kind else {
                        unreachable!()
                    };
                    if mutation == 6 && row.owner != b.core.leader {
                        row.preference = Some(Bytes::from_static(b"BA"));
                    }
                    if mutation == 7 && row.owner == b.core.leader {
                        row.report = Some(Bytes::from_static(b"leader-report"));
                    }
                    *signed = g::Signed::sign(
                        &f.schemes[usize::from(row.owner)],
                        signed.message.clone(),
                        fixture::G_LIMITS,
                    )
                    .unwrap();
                }
                resign_selection(&f, &mut bad);
            }
            _ => unreachable!(),
        }
        assert!(
            bad.authenticate::<Sha256, _>(
                &mut TestRng::new(13010),
                &f.verifier,
                fixture::G_LIMITS,
                &Sequential
            )
            .is_err(),
            "mutation {mutation}"
        );
    }
    // Same keys and roster, but a different signing namespace is not authority.
    let other = ed25519::fixture(&mut TestRng::new(101), b"other_auth_scope", 8);
    assert_eq!(f.participants, other.participants);
    assert!(
        b.origin
            .authenticate::<Sha256, _>(&mut TestRng::new(13011), &other.verifier, WIRE, &Sequential)
            .is_err()
    );
}

#[test]
fn paired_authentication_rejects_role_owner_ballot_and_decision_crossovers() {
    let f = fixture(8);
    let b = bundle(&f);
    for mutation in 0..6 {
        let mut bad = b.pairs[0].clone();
        match mutation {
            0 => bad.agreement = b.pairs[1].agreement.clone(),
            1 => bad.native.statement.extension = Digest::from([233; 32]),
            2 => bad.native.statement.ballot = round(5),
            3 => bad.agreement.message.round = round(5),
            4 => {
                bad.agreement.message.kind = g::Kind::Phase {
                    phase: g::Phase::Prepare,
                    decision: b.origin.body.decision.id::<Sha256>(),
                }
            }
            _ => bad.native.attestation = b.pairs[1].native.attestation.clone(),
        }
        // Give the changed roles genuine signatures where their individual
        // codecs permit them. Pair rejection must not rely on signature damage.
        if matches!(mutation, 1 | 2) {
            bad.native = vote::Vote::sign(&f.schemes[0], bad.native.statement.clone()).unwrap();
            assert!(
                bad.native
                    .verify(&mut TestRng::new(13018), &f.verifier, &Sequential)
            );
        }
        if matches!(mutation, 3 | 4) {
            bad.agreement =
                g::Signed::sign(&f.schemes[0], bad.agreement.message.clone(), WIRE).unwrap();
            assert!(
                bad.agreement
                    .verify(&mut TestRng::new(13019), &f.verifier, WIRE, &Sequential)
            );
        }
        assert!(
            bad.authenticate::<Sha256, _>(&mut TestRng::new(13012), &f.verifier, WIRE, &Sequential)
                .is_err(),
            "mutation {mutation}"
        );
    }
    let mut hint = b.pairs[0].clone();
    hint.origin_hint = Digest::from([234; 32]);
    hint.authenticate::<Sha256, _>(&mut TestRng::new(13013), &f.verifier, WIRE, &Sequential)
        .unwrap();
}

#[test]
fn certificate_authentication_checks_both_quorums_and_original_election_witness() {
    let f = fixture(8);
    let b = bundle(&f);
    let q = g::Committee::new(8).unwrap().quorum();
    for mutation in 0..6 {
        let mut bad = b.certificate.clone();
        match mutation {
            0 => bad.native.statement.extension = Digest::from([235; 32]),
            1 => bad.agreement.message.leader = Participant::new(0),
            2 => {
                let mut proposal = b.core.slot.proposal.clone();
                proposal.payload = Digest::from([236; 32]);
                let votes: Vec<_> = f
                    .schemes
                    .iter()
                    .take(q)
                    .map(|s| Notarize::sign(s, proposal.clone()).unwrap())
                    .collect();
                bad.notarization =
                    Notarization::from_notarizes(&f.verifier, non_empty![@&votes], &Sequential)
                        .unwrap();
                assert!(bad.notarization.verify(
                    &mut TestRng::new(13020),
                    &f.verifier,
                    &Sequential
                ));
            }
            3 => {
                let votes: Vec<_> = b.pairs.iter().take(q).map(|p| p.native.clone()).collect();
                bad.native = vote::Certificate::from_votes(
                    &mut TestRng::new(13014),
                    &f.verifier,
                    non_empty![@votes],
                    &Sequential,
                )
                .unwrap();
            }
            4 => bad.origin.selection.attestation = b.origin.body.firsts[0].attestation.clone(),
            _ => {
                let mut message = bad.agreement.message.clone();
                message.kind = g::Kind::Phase {
                    phase: g::Phase::Prepare,
                    decision: b.origin.body.decision.id::<Sha256>(),
                };
                let votes: Vec<_> = f
                    .schemes
                    .iter()
                    .skip(f.schemes.len() - q)
                    .map(|s| g::Signed::sign(s, message.clone(), WIRE).unwrap())
                    .collect();
                bad.agreement = g::Quorum::from_votes(
                    &mut TestRng::new(13021),
                    &f.verifier,
                    &votes,
                    WIRE,
                    &Sequential,
                )
                .unwrap();
                assert!(bad.agreement.verify(
                    &mut TestRng::new(13022),
                    &f.verifier,
                    WIRE,
                    &Sequential
                ));
            }
        }
        assert!(
            bad.authenticate::<Sha256, _>(&mut TestRng::new(13015), &f.verifier, WIRE, &Sequential)
                .is_err(),
            "mutation {mutation}"
        );
    }
}

thread_local! { static HASHES: Cell<usize> = const { Cell::new(0) }; }
#[derive(Default)]
struct HashProbe(Sha256);
impl commonware_cryptography::Hasher for HashProbe {
    type Digest = Digest;
    fn hash(parts: &[&[u8]]) -> Digest {
        HASHES.set(HASHES.get() + 1);
        Sha256::hash(parts)
    }
    fn hash_pair(a: &[&[u8]], b: &[&[u8]]) -> (Digest, Digest) {
        (Self::hash(a), Self::hash(b))
    }
    fn update(&mut self, bytes: &[u8]) -> &mut Self {
        self.0.update(bytes);
        self
    }
    fn finalize(self) -> (Self, Digest) {
        let (h, d) = self.0.finalize();
        (Self(h), d)
    }
}

#[test]
fn malformed_authentication_bounds_precede_hashes_and_preserve_callback_order() {
    let f = fixture(8);
    let b = bundle(&f);
    HASHES.set(0);
    b.certificate
        .authenticate::<HashProbe, _>(
            &mut TestRng::new(13016),
            &f.verifier,
            fixture::G_LIMITS,
            &Sequential,
        )
        .unwrap();
    assert!(
        HASHES.get() > 0,
        "hash observer must detect actual authentication"
    );
    for mutation in 0..5 {
        let mut bad = b.certificate.clone();
        match mutation {
            0 => bad
                .origin
                .body
                .firsts
                .resize(65, bad.origin.body.firsts[0].clone()),
            1 => bad.origin.body.build = Bytes::from(vec![0; fixture::G_LIMITS.build_bytes + 1]),
            2 => {
                bad.origin.body.decision.order =
                    Bytes::from(vec![0; fixture::G_LIMITS.order_bytes + 1])
            }
            3 => {
                let g::Kind::First(row) = &mut bad.origin.body.firsts[0].message.kind else {
                    unreachable!()
                };
                row.report = Some(Bytes::from(vec![0; fixture::G_LIMITS.report_bytes + 1]));
            }
            _ => bad
                .native
                .certificate
                .signatures
                .resize(300, bad.native.certificate.signatures[0].clone()),
        }
        HASHES.set(0);
        assert_eq!(
            bad.authenticate::<HashProbe, _>(
                &mut TestRng::new(13016),
                &f.verifier,
                fixture::G_LIMITS,
                &Sequential
            ),
            Err(g::Error::Limit)
        );
        assert_eq!(HASHES.get(), 0, "mutation {mutation}");
    }
    let mut bad = b.origin;
    let g::Kind::Select { body, .. } = &mut bad.selection.message.kind else {
        unreachable!()
    };
    *body = Digest::from([237; 32]);
    bad.selection = g::Signed::sign(
        &f.schemes[usize::from(b.core.leader)],
        bad.selection.message.clone(),
        fixture::G_LIMITS,
    )
    .unwrap();
    let build_calls = Cell::new(0);
    assert_eq!(
        bad.authenticate::<Sha256, _>(
            &mut TestRng::new(13023),
            &f.verifier,
            fixture::G_LIMITS,
            &Sequential,
        ),
        Err(g::Error::Context)
    );
    assert!(matches!(
        bad.verify::<Sha256, _>(
            &mut TestRng::new(13017),
            &f.verifier,
            &b.core,
            fixture::input(),
            fixture::G_LIMITS,
            fixture::legal_row,
            |rows, body| {
                build_calls.set(build_calls.get() + 1);
                fixture::build_policy(rows, body)
            },
            &Sequential,
        ),
        Err(g::Error::Context)
    ));
    assert_eq!(build_calls.get(), 0);
}
