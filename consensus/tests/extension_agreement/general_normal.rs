//! Independent joint-final component checks with real attributable signatures.
//!
//! The two-order policy below is deliberately independent of the SDK selector.
//! These tests provide no native Actor sync, Source, Marshal or recovery-network
//! evidence, and do not activate a production G1 Mode.
use super::*;
use commonware_codec::{Read, Write as _};
use commonware_consensus::simplex::{
    extension::agreement::general::{
        self as g,
        issuance::{Action, Material, Record, State},
        normal,
    },
    scheme::Scheme as NativeScheme,
    types::Notarization,
};
use commonware_cryptography::{
    Digest as CryptoDigest, Hasher as _,
    certificate::{self, Attestation, Scoped},
};
use commonware_parallel::Strategy;
use commonware_utils::{iter::NonEmpty, ordered::Set};
use rand_core::CryptoRng;
use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};

pub(super) const G_LIMITS: g::Limits = g::Limits {
    report_bytes: 128,
    order_bytes: 128,
    build_bytes: 256,
    material_bytes: 256,
    origin_bytes: g::MAX_EVIDENCE_BYTES,
};
type GOrigin = g::Origin<S, Digest>;

pub(super) const fn input() -> Digest {
    Digest([211; 32])
}

pub(super) fn core<T: certificate::Scheme>(f: &Fixture<T>) -> g::Core<Digest> {
    g::Core::derive::<Sha256, _>(
        &f.verifier,
        g::Slot {
            profile: Digest::from([212; 32]),
            domain: Digest::from([213; 32]),
            roster: g::Slot::roster::<Sha256, _>(&f.verifier),
            cut: 41,
            proposal: Proposal::new(round(4), View::new(3), Digest::from([214; 32])),
            parent: g::NativeParent::Proposal {
                round: round(3),
                digest: Digest::from([215; 32]),
            },
        },
        Participant::new(f.schemes.len() as u32 - 1),
    )
    .unwrap()
}

fn message(c: &g::Core<Digest>, kind: g::Kind<Digest>) -> g::Message<Digest> {
    g::Message {
        slot: c.slot.id::<Sha256>(),
        round: c.slot.proposal.round,
        leader: c.leader,
        kind,
    }
}

fn population<T: certificate::Scheme>(rows: &[g::Signed<T, Digest>]) -> Digest {
    let mut bytes = Vec::new();
    for row in rows {
        row.write(&mut bytes);
    }
    Sha256::hash(&[b"_COMMONWARE_CONSENSUS_NORMAL_TEST_POPULATION", &bytes])
}

fn build<T: certificate::Scheme>(rows: &[g::Signed<T, Digest>]) -> Bytes {
    rows.iter()
        .flat_map(|signed| {
            let g::Kind::First(row) = &signed.message.kind else {
                panic!("FIRST fixture")
            };
            row.report.iter().flat_map(|bytes| bytes.iter().copied())
        })
        .collect()
}

pub(super) fn legal_row(row: &g::First<Digest>) -> bool {
    row.report.as_ref().is_none_or(|bytes| bytes.len() == 1)
        && row
            .preference
            .as_ref()
            .is_none_or(|bytes| matches!(bytes.as_ref(), b"AB" | b"BA"))
}

pub(super) fn build_policy<T: certificate::Scheme>(
    rows: &g::VerifiedRows<T, Digest>,
    body: &g::OriginBody<T, Digest>,
) -> bool {
    let order = rows.rows().iter().find_map(|row| row.preference.as_ref());
    order == Some(&body.decision.order)
        && rows
            .rows()
            .iter()
            .filter_map(|row| row.preference.as_ref())
            .all(|preference| preference == &body.decision.order)
        && body.population == population(rows.originals())
        && body.build == build(rows.originals())
        && body.material.is_empty()
}

pub(super) fn origin<T: NativeScheme<Digest>>(
    f: &Fixture<T>,
    c: &g::Core<Digest>,
    order: &'static [u8],
    alias: bool,
) -> g::Origin<T, Digest> {
    let mut owners = c.followers.clone();
    owners.push(c.leader);
    owners.sort_unstable();
    let changed = c.followers[0];
    let firsts: Vec<_> = owners
        .into_iter()
        .map(|owner| {
            let follower = owner != c.leader;
            let row = g::First {
                core: c.id::<Sha256>(),
                input: input(),
                owner,
                report: follower
                    .then(|| Bytes::from(vec![if alias && owner == changed { 2 } else { 1 }])),
                preference: follower.then(|| Bytes::from_static(order)),
            };
            g::Signed::sign(
                &f.schemes[usize::from(owner)],
                message(c, g::Kind::First(row)),
                G_LIMITS,
            )
            .unwrap()
        })
        .collect();
    let body = g::OriginBody {
        core: c.clone(),
        decision: g::Decision {
            slot: c.slot.clone(),
            input: input(),
            order: Bytes::from_static(order),
        },
        population: population(&firsts),
        build: build(&firsts),
        firsts,
        material: Bytes::new(),
    };
    let selection = g::Signed::sign(
        &f.schemes[usize::from(c.leader)],
        message(
            c,
            g::Kind::Select {
                body: body.id::<Sha256>(),
                decision: body.decision.id::<Sha256>(),
            },
        ),
        G_LIMITS,
    )
    .unwrap();
    g::Origin { body, selection }
}

fn notarization<T: NativeScheme<Digest>>(
    f: &Fixture<T>,
    c: &g::Core<Digest>,
    offset: usize,
) -> Notarization<T, Digest> {
    let q = g::Committee::new(f.schemes.len()).unwrap().quorum();
    let votes: Vec<_> = f
        .schemes
        .iter()
        .skip(offset)
        .take(q)
        .map(|scheme| Notarize::sign(scheme, c.slot.proposal.clone()).unwrap())
        .collect();
    Notarization::from_notarizes(&f.verifier, non_empty![@&votes], &Sequential).unwrap()
}

pub(super) fn local<T: NativeScheme<Digest>>(
    f: &Fixture<T>,
    c: &g::Core<Digest>,
    owner: usize,
) -> State<T, Digest> {
    State::new::<Sha256>(f.schemes[owner].clone(), c.clone(), input(), G_LIMITS).unwrap()
}

pub(super) fn prime<T: NativeScheme<Digest>>(
    state: &mut State<T, Digest>,
    c: &g::Core<Digest>,
    p: &g::Origin<T, Digest>,
) -> Vec<Record<Digest>> {
    let first = p
        .body
        .firsts
        .iter()
        .find(|signed| signed.attestation.signer == state.owner());
    let first = if let Some(signed) = first {
        let g::Kind::First(row) = &signed.message.kind else {
            unreachable!()
        };
        state
            .reserve_first::<Sha256>(row.report.clone(), row.preference.clone(), legal_row)
            .unwrap()
    } else {
        state.close_first::<Sha256>().unwrap()
    };
    let mut records = vec![first];
    if state.owner() == c.leader {
        records.push(
            state
                .reserve_select::<Sha256, _>(
                    &mut TestRng::new(6101),
                    &p.body,
                    legal_row,
                    build_policy,
                    &Sequential,
                )
                .unwrap(),
        );
    }
    records
}

pub(super) fn replay_prime<T: NativeScheme<Digest>>(
    state: &mut State<T, Digest>,
    p: &g::Origin<T, Digest>,
    records: &[Record<Digest>],
) {
    for record in records {
        let material = if matches!(
            record.action(),
            Action::Reserve {
                message: g::Message {
                    kind: g::Kind::Select { .. },
                    ..
                },
                ..
            }
        ) {
            Material::Body(&p.body)
        } else {
            Material::None
        };
        state
            .restore::<Sha256, _>(
                &mut TestRng::new(6102),
                record,
                material,
                legal_row,
                build_policy,
                &Sequential,
            )
            .unwrap();
    }
}

pub(super) fn reserve<T: NativeScheme<Digest>>(
    state: &mut State<T, Digest>,
    p: &g::Origin<T, Digest>,
) -> normal::Reservation<Digest> {
    state
        .reserve_normal::<Sha256, _>(
            &mut TestRng::new(6103),
            p,
            legal_row,
            build_policy,
            &Sequential,
        )
        .unwrap()
}

fn pair<T: NativeScheme<Digest>>(
    f: &Fixture<T>,
    c: &g::Core<Digest>,
    p: &g::Origin<T, Digest>,
    owner: usize,
) -> normal::Vote<T, Digest> {
    let mut state = local(f, c, owner);
    prime(&mut state, c, p);
    let reservation = reserve(&mut state, p);
    state.sign_normal::<Sha256>(&reservation).unwrap()
}

#[derive(Clone, Debug, Default)]
struct Calls {
    native: Arc<AtomicUsize>,
    agreement: Arc<AtomicUsize>,
}
impl Calls {
    fn clear(&self) {
        self.native.store(0, Ordering::SeqCst);
        self.agreement.store(0, Ordering::SeqCst);
    }
    fn get(&self) -> (usize, usize) {
        (
            self.native.load(Ordering::SeqCst),
            self.agreement.load(Ordering::SeqCst),
        )
    }
}

#[derive(Clone, Debug)]
struct Observed {
    inner: S,
    calls: Calls,
}
impl certificate::Verifier for Observed {
    type Subject<'a, T: CryptoDigest> = Subject<'a, T>;
    type Faults = <S as certificate::Verifier>::Faults;
    type PublicKey = <S as certificate::Verifier>::PublicKey;
    type Certificate = <S as certificate::Verifier>::Certificate;
    fn verify_certificate<R: CryptoRng, T: CryptoDigest>(
        &self,
        rng: &mut R,
        subject: Subject<'_, T>,
        certificate: &Self::Certificate,
        strategy: &impl Strategy,
    ) -> bool {
        self.inner
            .verify_certificate(rng, subject, certificate, strategy)
    }
    fn is_batchable() -> bool {
        S::is_batchable()
    }
    fn certificate_codec_config(&self) -> <Self::Certificate as Read>::Cfg {
        self.inner.certificate_codec_config()
    }
    fn certificate_codec_config_unbounded() -> <Self::Certificate as Read>::Cfg {
        S::certificate_codec_config_unbounded()
    }
}
impl certificate::Scheme for Observed {
    type Signature = <S as certificate::Scheme>::Signature;
    fn me(&self) -> Option<Participant> {
        self.inner.me()
    }
    fn participants(&self) -> &Set<Self::PublicKey> {
        self.inner.participants()
    }
    fn sign<T: CryptoDigest>(&self, subject: Subject<'_, T>) -> Option<Attestation<Self>> {
        match &subject {
            Subject::FinalizeExtension { .. } => {
                self.calls.native.fetch_add(1, Ordering::SeqCst);
            }
            Subject::ExtensionAgreement { .. } => {
                self.calls.agreement.fetch_add(1, Ordering::SeqCst);
            }
            _ => {}
        }
        self.inner.sign(subject).map(|a| Attestation {
            signer: a.signer,
            signature: a.signature,
        })
    }
    fn verify_attestation<R: CryptoRng, T: CryptoDigest>(
        &self,
        rng: &mut R,
        subject: Subject<'_, T>,
        a: &Attestation<Self>,
        strategy: &impl Strategy,
    ) -> bool {
        self.inner.verify_attestation(
            rng,
            subject,
            &Attestation {
                signer: a.signer,
                signature: a.signature.clone(),
            },
            strategy,
        )
    }
    fn optimistic_assemble<'a, R: CryptoRng, T: CryptoDigest, I, J>(
        &self,
        rng: &mut R,
        subject: Subject<'_, T>,
        pending: I,
        verified: J,
        strategy: &impl Strategy,
    ) -> Result<Self::Certificate, certificate::Verification<Self>>
    where
        I: IntoIterator<Item = Attestation<Self>>,
        I::IntoIter: ExactSizeIterator + Send,
        J: IntoIterator<Item = &'a Attestation<Self>>,
        J::IntoIter: Send,
    {
        certificate::optimistic_assemble(self, rng, subject, pending, verified, strategy)
    }
    fn assemble<I: Iterator<Item = Attestation<Self>> + Send>(
        &self,
        attestations: NonEmpty<I>,
        strategy: &impl Strategy,
    ) -> Result<Self::Certificate, certificate::AssemblyError> {
        self.inner.assemble(
            non_empty![@attestations.into_iter().map(|a| Attestation {
                signer: a.signer,
                signature: a.signature,
            })],
            strategy,
        )
    }
    fn is_attributable() -> bool {
        true
    }
}

fn observed(n: u32) -> (Fixture<Observed>, Calls) {
    let f = fixture(n);
    let calls = Calls::default();
    let wrap = |inner| Observed {
        inner,
        calls: calls.clone(),
    };
    (
        Fixture {
            participants: f.participants,
            private_keys: f.private_keys,
            schemes: f.schemes.into_iter().map(wrap).collect(),
            verifier: wrap(f.verifier),
        },
        calls,
    )
}

fn assembled(
    f: &Fixture<S>,
    c: &g::Core<Digest>,
    a: &GOrigin,
    b: &GOrigin,
    owners: impl Iterator<Item = usize>,
) -> normal::Certificate<S, Digest> {
    let changed = usize::from(c.followers[0]);
    let pairs: Vec<_> = owners
        .enumerate()
        .map(|(index, owner)| {
            // An owner whose signed FIRST differs keeps its own exact A.
            let p = if index % 2 == 1 && owner != changed {
                b
            } else {
                a
            };
            let mut pair = pair(f, c, p, owner);
            // Wire hints cannot claim which origin another owner retained.
            pair.origin_hint = Digest::from([index as u8; 32]);
            pair
        })
        .collect();
    normal::Certificate::assemble::<Sha256, _>(
        &mut TestRng::new(6110),
        &f.verifier,
        c,
        input(),
        a,
        &notarization(f, c, 0),
        &pairs,
        G_LIMITS,
        legal_row,
        build_policy,
        &Sequential,
    )
    .unwrap()
}

fn verify(
    f: &Fixture<S>,
    c: &g::Core<Digest>,
    certificate: &normal::Certificate<S, Digest>,
) -> Result<(), g::Error> {
    certificate.verify::<Sha256, _>(
        &mut TestRng::new(6111),
        &f.verifier,
        c,
        input(),
        G_LIMITS,
        legal_row,
        build_policy,
        &Sequential,
    )
}

#[test]
fn general_rosters_join_exact_q_pairs_and_mixed_same_decision_origins() {
    for n in [4, 7, 8, 9, 10, 11, 12, 13, 16, 31, 64] {
        let f = fixture(n);
        let c = core(&f);
        let committee = g::Committee::new(n as usize).unwrap();
        let a = origin(&f, &c, b"AB", false);
        // At n=4 the matrix uses one origin, without implying two distinct
        // equivocating identities fit its one-fault protocol budget.
        let b = origin(&f, &c, b"AB", n != 4);
        assert_eq!(a.body.decision, b.body.decision);
        if n != 4 {
            assert_ne!(a.id::<Sha256>(), b.id::<Sha256>());
        }
        let certificate = assembled(
            &f,
            &c,
            &a,
            &b,
            (n as usize - committee.quorum())..n as usize,
        );
        verify(&f, &c, &certificate).unwrap();
        use normal::CertificateSigners as _;
        let native = certificate.native.certificate.signers();
        assert_eq!(native, certificate.agreement.certificate.signers());
        assert_eq!(native.len(), n as usize);
        assert_eq!(native.count(), committee.quorum());
        assert!(native.iter().any(|owner| owner.get() == n - 1));
        assert_eq!(
            certificate.native.statement.extension,
            a.body.decision.id::<Sha256>()
        );
        assert_eq!(certificate.notarization.proposal, c.slot.proposal);
        let scoped = Scoped::verifier(Arc::new(f.verifier.clone()));
        certificate
            .verify_scoped::<Sha256, _>(
                &mut TestRng::new(6112),
                &scoped,
                &c,
                input(),
                G_LIMITS,
                legal_row,
                build_policy,
                &Sequential,
            )
            .unwrap();
        // Any fully valid same-decision witness works, without rewriting any
        // owner's immutable reservation or claiming a hint is provenance.
        let alternate = normal::Certificate {
            origin: b,
            ..certificate
        };
        verify(&f, &c, &alternate).unwrap();
    }
}

#[test]
fn individual_pair_checks_bind_owner_context_and_decision_but_not_hint() {
    let f = fixture(8);
    let c = core(&f);
    let a = origin(&f, &c, b"AB", false);
    let other = origin(&f, &c, b"BA", false);
    let check = |pair: &normal::Vote<S, Digest>, context: &g::Core<Digest>, value| {
        pair.verify::<Sha256, _>(
            &mut TestRng::new(6113),
            &f.verifier,
            context,
            input(),
            value,
            G_LIMITS,
            &Sequential,
        )
    };
    let mut p = pair(&f, &c, &a, 0);
    let original = p.clone();
    assert!(check(&p, &c, &a.body.decision));
    p.origin_hint = Digest::from([255; 32]);
    assert!(p.same_signed_pair(&original));
    assert_ne!(p, original);
    assert!(check(&p, &c, &a.body.decision));
    assert!(!check(&p, &c, &other.body.decision));
    let mut wrong = c.clone();
    wrong.slot.profile = Digest::from([216; 32]);
    assert!(!check(&p, &wrong, &a.body.decision));
    let q = pair(&f, &c, &a, 1);
    let different = pair(&f, &c, &other, 0);
    for field in 0..4 {
        let mut changed = original.clone();
        match field {
            0 => changed.native.statement = different.native.statement.clone(),
            1 => changed.native.attestation = q.native.attestation.clone(),
            2 => changed.agreement.message = different.agreement.message.clone(),
            _ => changed.agreement.attestation = q.agreement.attestation.clone(),
        }
        assert!(!changed.same_signed_pair(&original));
    }
    p.agreement = q.agreement;
    assert!(
        p.native
            .verify(&mut TestRng::new(6114), &f.verifier, &Sequential)
    );
    assert!(
        p.agreement
            .verify(&mut TestRng::new(6115), &f.verifier, G_LIMITS, &Sequential)
    );
    assert!(!check(&p, &c, &a.body.decision));
}

#[test]
fn individually_valid_different_owner_quorums_and_wrong_nqc_are_rejected() {
    let f = fixture(8);
    let c = core(&f);
    let a = origin(&f, &c, b"AB", false);
    let q = g::Committee::new(8).unwrap().quorum();
    let first = assembled(&f, &c, &a, &a, 0..q);
    let second = assembled(&f, &c, &a, &a, 1..q + 1);
    let mut mismatch = first.clone();
    mismatch.agreement = second.agreement;
    assert!(
        mismatch
            .native
            .verify(&mut TestRng::new(6116), &f.verifier, &Sequential)
    );
    assert!(
        mismatch
            .agreement
            .verify(&mut TestRng::new(6117), &f.verifier, G_LIMITS, &Sequential)
    );
    assert_eq!(verify(&f, &c, &mismatch), Err(g::Error::Identity));
    let mut other_core = c.clone();
    other_core.slot.proposal.payload = Digest::from([217; 32]);
    let wrong = notarization(&f, &other_core, 0);
    assert!(wrong.verify(&mut TestRng::new(6118), &f.verifier, &Sequential));
    mismatch = first.clone();
    mismatch.notarization = wrong;
    assert_eq!(verify(&f, &c, &mismatch), Err(g::Error::Context));
    mismatch = first;
    mismatch.notarization.certificate = mismatch.native.certificate.clone();
    assert!(verify(&f, &c, &mismatch).is_err());
}

#[test]
fn exact_q_distinct_complete_pairs_are_required_before_assembly() {
    let f = fixture(9);
    let c = core(&f);
    let a = origin(&f, &c, b"AB", false);
    let q = g::Committee::new(9).unwrap().quorum();
    let pairs: Vec<_> = (0..q + 1).map(|owner| pair(&f, &c, &a, owner)).collect();
    let assemble = |pairs: &[normal::Vote<S, Digest>]| {
        normal::Certificate::assemble::<Sha256, _>(
            &mut TestRng::new(6119),
            &f.verifier,
            &c,
            input(),
            &a,
            &notarization(&f, &c, 0),
            pairs,
            G_LIMITS,
            legal_row,
            build_policy,
            &Sequential,
        )
    };
    assert!(assemble(&pairs[..q]).is_ok());
    assert!(assemble(&pairs[..q - 1]).is_err());
    assert!(assemble(&pairs).is_err());
    let mut duplicate = pairs[..q].to_vec();
    duplicate[1] = duplicate[0].clone();
    assert!(assemble(&duplicate).is_err());
    let mut invalid = pairs[..q].to_vec();
    invalid[0].agreement = pairs[1].agreement.clone();
    assert!(assemble(&invalid).is_err());
}

#[test]
fn same_decision_retry_preserves_own_origin_and_replay_requires_exact_a() {
    let f = fixture(8);
    let c = core(&f);
    let a = origin(&f, &c, b"AB", false);
    let b = origin(&f, &c, b"AB", true);
    let owner = (0..f.schemes.len())
        .find(|owner| {
            *owner != usize::from(c.leader)
                && !c.followers.contains(&Participant::new(*owner as u32))
        })
        .unwrap();
    let mut state = local(&f, &c, owner);
    let prior = prime(&mut state, &c, &a);
    let reservation = reserve(&mut state, &a);
    assert_eq!(reserve(&mut state, &b), reservation);
    assert_eq!(reservation.agreement().authority(), Some(a.id::<Sha256>()));
    let signed = state.sign_normal::<Sha256>(&reservation).unwrap();
    assert_eq!(signed.origin_hint, a.id::<Sha256>());
    let mut changed = signed.clone();
    changed.origin_hint = b.id::<Sha256>();
    assert!(
        state
            .record_normal_signed::<Sha256, _>(
                &mut TestRng::new(6120),
                &reservation,
                &changed,
                &Sequential,
            )
            .is_err()
    );
    assert!(state.normal_outbox(&reservation).is_none());
    let released = state
        .record_normal_signed::<Sha256, _>(
            &mut TestRng::new(6121),
            &reservation,
            &signed,
            &Sequential,
        )
        .unwrap();
    let mut replay =
        State::for_replay::<Sha256>(f.schemes[owner].clone(), c.clone(), input(), G_LIMITS)
            .unwrap();
    replay_prime(&mut replay, &a, &prior);
    let before = replay.records().to_vec();
    assert!(
        replay
            .restore_normal::<Sha256, _>(
                &mut TestRng::new(6122),
                &reservation,
                &b,
                legal_row,
                build_policy,
                &Sequential,
            )
            .is_err()
    );
    assert_eq!(replay.records(), before);
    replay
        .restore_normal::<Sha256, _>(
            &mut TestRng::new(6123),
            &reservation,
            &a,
            legal_row,
            build_policy,
            &Sequential,
        )
        .unwrap();
    assert!(replay.sign_normal::<Sha256>(&reservation).is_err());
    replay
        .restore_normal_signed::<Sha256, _>(&mut TestRng::new(6124), &released, &Sequential)
        .unwrap();
    replay.finish_replay().unwrap();
    assert_eq!(
        replay.normal_outbox(&reservation).unwrap().encode(),
        signed.encode()
    );
    assert!(replay.sign_normal::<Sha256>(&reservation).is_err());
}

#[test]
fn higher_floor_and_terminal_block_both_signers_but_retain_late_exact_pairs() {
    for n in [4, 8, 9, 10, 13, 16, 64] {
        let (f, calls) = observed(n);
        let c = core(&f);
        let a = origin(&f, &c, b"AB", false);
        let owner = n as usize - 1;
        for close_with_terminal in [false, true] {
            let mut state = local(&f, &c, owner);
            prime(&mut state, &c, &a);
            let reservation = reserve(&mut state, &a);
            calls.clear();
            let signed = state.sign_normal::<Sha256>(&reservation).unwrap();
            assert_eq!(calls.get(), (1, 1));
            if close_with_terminal {
                let q = g::Committee::new(n as usize).unwrap().quorum();
                let votes: Vec<_> = f
                    .schemes
                    .iter()
                    .take(q)
                    .map(|scheme| {
                        g::Signed::sign(scheme, signed.agreement.message.clone(), G_LIMITS).unwrap()
                    })
                    .collect();
                let quorum = g::Quorum::from_votes(
                    &mut TestRng::new(6125),
                    &f.verifier,
                    &votes,
                    G_LIMITS,
                    &Sequential,
                )
                .unwrap();
                state
                    .terminal::<Sha256, _>(
                        &mut TestRng::new(6126),
                        &a,
                        &quorum,
                        legal_row,
                        build_policy,
                        &Sequential,
                    )
                    .unwrap();
            } else {
                state
                    .fence::<Sha256>(round(5), Participant::new(0))
                    .unwrap();
            }
            calls.clear();
            assert!(state.sign_normal::<Sha256>(&reservation).is_err());
            assert_eq!(calls.get(), (0, 0));
            assert_eq!(reserve(&mut state, &a), reservation);
            let released = state
                .record_normal_signed::<Sha256, _>(
                    &mut TestRng::new(6127),
                    &reservation,
                    &signed,
                    &Sequential,
                )
                .unwrap();
            assert_eq!(released.vote().encode(), signed.encode());
            assert_eq!(
                state.normal_outbox(&reservation).unwrap().encode(),
                signed.encode()
            );
            assert_eq!(calls.get(), (0, 0));
        }
    }
}

#[test]
fn replay_restores_later_floor_before_release_and_keeps_complete_pair_receipt() {
    let (f, calls) = observed(9);
    let c = core(&f);
    let a = origin(&f, &c, b"AB", false);
    let mut state = local(&f, &c, 8);
    let prior = prime(&mut state, &c, &a);
    let reservation = reserve(&mut state, &a);
    let signed = state.sign_normal::<Sha256>(&reservation).unwrap();
    let fence = state
        .fence::<Sha256>(round(6), Participant::new(1))
        .unwrap();
    let late = state
        .record_normal_signed::<Sha256, _>(
            &mut TestRng::new(6130),
            &reservation,
            &signed,
            &Sequential,
        )
        .unwrap();
    for has_outbox in [false, true] {
        let mut replay =
            State::for_replay::<Sha256>(f.schemes[8].clone(), c.clone(), input(), G_LIMITS)
                .unwrap();
        replay_prime(&mut replay, &a, &prior);
        replay
            .restore_normal::<Sha256, _>(
                &mut TestRng::new(6131),
                &reservation,
                &a,
                legal_row,
                build_policy,
                &Sequential,
            )
            .unwrap();
        replay
            .restore::<Sha256, _>(
                &mut TestRng::new(6132),
                &fence,
                Material::None,
                legal_row,
                build_policy,
                &Sequential,
            )
            .unwrap();
        if has_outbox {
            replay
                .restore_normal_signed::<Sha256, _>(&mut TestRng::new(6133), &late, &Sequential)
                .unwrap();
        }
        replay.finish_replay().unwrap();
        calls.clear();
        assert!(replay.sign_normal::<Sha256>(&reservation).is_err());
        assert_eq!(calls.get(), (0, 0));
        assert_eq!(replay.floor(), round(6));
        if has_outbox {
            assert_eq!(
                replay.normal_outbox(&reservation).unwrap().encode(),
                signed.encode()
            );
            assert_eq!(calls.get(), (0, 0));
        } else {
            assert!(replay.normal_outbox(&reservation).is_none());
        }
    }
}

fn bad_frames<T: commonware_codec::Decode>(bytes: &Bytes, cfg: &T::Cfg) {
    for length in [0, 4, 7, bytes.len() / 2, bytes.len() - 1] {
        assert!(T::decode_cfg(bytes.slice(..length), cfg).is_err());
    }
    let mut wrong_version = bytes.to_vec();
    wrong_version[3] ^= 1;
    assert!(T::decode_cfg(Bytes::from(wrong_version), cfg).is_err());
    let mut oversized = bytes.to_vec();
    oversized[4..8].copy_from_slice(&u32::MAX.to_be_bytes());
    assert!(T::decode_cfg(Bytes::from(oversized), cfg).is_err());
    let mut trailing = bytes.to_vec();
    trailing.push(0);
    assert!(T::decode_cfg(Bytes::from(trailing), cfg).is_err());
}

#[test]
fn new_joint_frames_are_bounded_canonical_codecs_not_authority() {
    let f = fixture(8);
    let c = core(&f);
    let a = origin(&f, &c, b"AB", false);
    let mut state = local(&f, &c, 7);
    prime(&mut state, &c, &a);
    let reservation = reserve(&mut state, &a);
    let vote = state.sign_normal::<Sha256>(&reservation).unwrap();
    let released = state
        .record_normal_signed::<Sha256, _>(
            &mut TestRng::new(6128),
            &reservation,
            &vote,
            &Sequential,
        )
        .unwrap();
    let certificate = assembled(&f, &c, &a, &a, 0..6);
    let cfg = (G_LIMITS, f.verifier.certificate_codec_config());
    let rb = reservation.encode();
    let vb = vote.encode();
    let xb = released.encode();
    let cb = certificate.encode();
    assert_eq!(
        normal::Reservation::<Digest>::decode_cfg(rb.clone(), &G_LIMITS).unwrap(),
        reservation
    );
    assert_eq!(
        normal::Vote::<S, Digest>::decode_cfg(vb.clone(), &G_LIMITS)
            .unwrap()
            .encode(),
        vb
    );
    assert_eq!(
        normal::Released::<S, Digest>::decode_cfg(xb.clone(), &G_LIMITS)
            .unwrap()
            .encode(),
        xb
    );
    let decoded = normal::Certificate::<S, Digest>::decode_cfg(cb.clone(), &cfg).unwrap();
    assert_eq!(decoded.encode(), cb);
    verify(&f, &c, &decoded).unwrap();
    bad_frames::<normal::Reservation<Digest>>(&rb, &G_LIMITS);
    bad_frames::<normal::Vote<S, Digest>>(&vb, &G_LIMITS);
    bad_frames::<normal::Released<S, Digest>>(&xb, &G_LIMITS);
    bad_frames::<normal::Certificate<S, Digest>>(&cb, &cfg);
    assert!(normal::Vote::<S, Digest>::decode_cfg(rb, &G_LIMITS).is_err());
    assert!(normal::Released::<S, Digest>::decode_cfg(vb, &G_LIMITS).is_err());
    assert!(normal::Certificate::<S, Digest>::decode_cfg(xb, &cfg).is_err());
    let mut invalid = decoded;
    invalid.origin.body.build = Bytes::from_static(b"not-the-policy-build");
    // Re-sign the changed origin, so its rejection exercises application policy
    // rather than just an obsolete SELECT signature.
    invalid.origin.selection = g::Signed::sign(
        &f.schemes[usize::from(c.leader)],
        message(
            &c,
            g::Kind::Select {
                body: invalid.origin.body.id::<Sha256>(),
                decision: invalid.origin.body.decision.id::<Sha256>(),
            },
        ),
        G_LIMITS,
    )
    .unwrap();
    assert_eq!(verify(&f, &c, &invalid), Err(g::Error::Policy));
}

#[test]
fn native_parent_hash_is_tagged_anchor_and_not_parent_interpretation() {
    let f = fixture(4);
    let c = core(&f);
    let mut bytes = Vec::new();
    let g::NativeParent::Proposal {
        round: parent_ballot,
        digest,
    } = c.slot.parent
    else {
        unreachable!()
    };
    1u8.write(&mut bytes);
    let encoded_round = parent_ballot.encode();
    (encoded_round.len() as u32).write(&mut bytes);
    bytes.extend_from_slice(&encoded_round);
    digest.write(&mut bytes);
    let expected = Sha256::hash(&[b"_COMMONWARE_CONSENSUS_G1_NATIVE_PARENT_V1", &bytes]);
    let a = origin(&f, &c, b"AB", false);
    let subject = normal::subject::<Sha256>(&a.body.decision);
    assert_eq!(subject.parent, expected);
    assert_eq!(subject.proposal, c.slot.proposal);
    assert_eq!(subject.ballot, c.slot.proposal.round);
    assert_eq!(subject.domain, c.slot.domain);
    assert_eq!(subject.extension, a.body.decision.id::<Sha256>());
    let g::NativeParent::Proposal { digest, .. } = &c.slot.parent else {
        unreachable!()
    };
    assert_ne!(subject.parent, *digest);
    let mut genesis = a.body.decision;
    genesis.slot.parent = g::NativeParent::Genesis(*digest);
    assert_ne!(normal::subject::<Sha256>(&genesis).parent, expected);
    let mut parent_round = genesis.clone();
    parent_round.slot.parent = g::NativeParent::Proposal {
        round: round(2),
        digest: *digest,
    };
    assert_ne!(normal::subject::<Sha256>(&parent_round).parent, expected);
    assert_ne!(
        normal::subject::<Sha256>(&parent_round).parent,
        normal::subject::<Sha256>(&genesis).parent
    );
    let original = parent_round;
    for field in 0..4 {
        let mut changed = original.clone();
        match field {
            0 => changed.slot.domain = Digest::from([220; 32]),
            1 => changed.slot.profile = Digest::from([221; 32]),
            2 => changed.input = Digest::from([222; 32]),
            _ => changed.order = Bytes::from_static(b"BA"),
        }
        assert_ne!(changed.id::<Sha256>(), original.id::<Sha256>());
        assert_ne!(
            normal::subject::<Sha256>(&changed),
            normal::subject::<Sha256>(&original)
        );
    }
}

type NormalFrames = (
    normal::Reservation<Digest>,
    normal::Vote<S, Digest>,
    normal::Released<S, Digest>,
    normal::Certificate<S, Digest>,
);

pub(super) fn frame_values() -> NormalFrames {
    let f = fixture(8);
    let c = core(&f);
    let a = origin(&f, &c, b"AB", false);
    let mut state = local(&f, &c, 7);
    prime(&mut state, &c, &a);
    let reservation = reserve(&mut state, &a);
    let vote = state.sign_normal::<Sha256>(&reservation).unwrap();
    let released = state
        .record_normal_signed::<Sha256, _>(
            &mut TestRng::new(6134),
            &reservation,
            &vote,
            &Sequential,
        )
        .unwrap();
    let certificate = assembled(&f, &c, &a, &a, 1..7);
    (reservation, vote, released, certificate)
}

struct GeneralNormalConformance;
impl Conformance for GeneralNormalConformance {
    async fn commit(seed: u64) -> Vec<u8> {
        let f = ed25519::fixture(
            &mut TestRng::new(seed),
            b"_COMMONWARE_CONSENSUS_G1_NORMAL_CONFORMANCE",
            8,
        );
        let c = core(&f);
        let order: &'static [u8] = if seed.is_multiple_of(2) { b"AB" } else { b"BA" };
        let a = origin(&f, &c, order, seed.is_multiple_of(3));
        let mut state = local(&f, &c, 7);
        prime(&mut state, &c, &a);
        let reservation = reserve(&mut state, &a);
        let vote = state.sign_normal::<Sha256>(&reservation).unwrap();
        let released = state
            .record_normal_signed::<Sha256, _>(
                &mut TestRng::new(6129),
                &reservation,
                &vote,
                &Sequential,
            )
            .unwrap();
        let certificate = assembled(&f, &c, &a, &a, 1..7);
        let cfg = (G_LIMITS, f.verifier.certificate_codec_config());
        let frames = vec![
            reservation.encode(),
            vote.encode(),
            released.encode(),
            certificate.encode(),
        ];
        assert_eq!(
            normal::Reservation::<Digest>::decode_cfg(frames[0].clone(), &G_LIMITS)
                .unwrap()
                .encode(),
            frames[0]
        );
        assert_eq!(
            normal::Vote::<S, Digest>::decode_cfg(frames[1].clone(), &G_LIMITS)
                .unwrap()
                .encode(),
            frames[1]
        );
        assert_eq!(
            normal::Released::<S, Digest>::decode_cfg(frames[2].clone(), &G_LIMITS)
                .unwrap()
                .encode(),
            frames[2]
        );
        assert_eq!(
            normal::Certificate::<S, Digest>::decode_cfg(frames[3].clone(), &cfg)
                .unwrap()
                .encode(),
            frames[3]
        );
        frames.encode().to_vec()
    }
}
conformance_tests! { GeneralNormalConformance => 32 }
