//! Real-crypto representation controls, without native issuance or app policy.
use super::*;
use crate::{
    simplex::{
        extension::vote,
        scheme::ed25519,
        types::{Notarization, VoteWith},
    },
    types::Round,
};
use bytes::Bytes;
use commonware_codec::{Decode as _, Encode as _};
use commonware_conformance::Conformance;
use commonware_cryptography::{
    certificate::{Verifier as _, mocks::Fixture},
    sha256::{Digest as D, Sha256},
};
use commonware_parallel::Sequential;
use commonware_utils::{TestRng, iter::NonEmpty, non_empty};
use std::sync::Arc;
type S = ed25519::Scheme;
type M = General<Sha256>;

pub(crate) const LIMITS: g::Limits = g::Limits {
    report_bytes: 128,
    order_bytes: 128,
    build_bytes: 256,
    material_bytes: 128,
    origin_bytes: g::MAX_EVIDENCE_BYTES,
};

pub(crate) struct Setup {
    pub(crate) f: Fixture<S>,
    pub(crate) core: g::Core<D>,
    pub(crate) origin: g::Origin<S, D>,
    pub(crate) pairs: Vec<g::normal::Vote<S, D>>,
}
impl Setup {
    pub(crate) fn new(n: usize, seed: u64) -> Self {
        Self::with_leader(n, seed, Participant::new(n as u32 - 1))
    }
    pub(crate) fn with_leader(n: usize, seed: u64, leader: Participant) -> Self {
        Self::with_namespace(
            n,
            seed,
            leader,
            b"_COMMONWARE_CONSENSUS_G1_MODE_REPRESENTATION_TEST",
        )
    }
    pub(crate) fn with_namespace(
        n: usize,
        seed: u64,
        leader: Participant,
        namespace: &[u8],
    ) -> Self {
        let f = ed25519::fixture(&mut TestRng::new(seed), namespace, n as u32);
        let core = g::Core::derive::<Sha256, _>(
            &f.verifier,
            g::Slot {
                profile: D::from([21; 32]),
                domain: D::from([22; 32]),
                roster: g::Slot::roster::<Sha256, _>(&f.verifier),
                cut: 41,
                proposal: Proposal::new(
                    Round::new(Epoch::new(1), View::new(5)),
                    View::new(4),
                    D::from([23; 32]),
                ),
                parent: g::NativeParent::Proposal {
                    round: Round::new(Epoch::new(1), View::new(4)),
                    digest: D::from([24; 32]),
                },
            },
            leader,
        )
        .unwrap();
        let decision = g::Decision {
            slot: core.slot.clone(),
            input: D::from([25; 32]),
            // Intentionally only a declared wire order, not SDK policy evidence.
            order: Bytes::from_static(b"declared-order"),
        };
        let message = |kind| g::Message {
            slot: core.slot.id::<Sha256>(),
            round: core.slot.proposal.round,
            leader: core.leader,
            kind,
        };
        let mut owners = core.followers.clone();
        owners.push(core.leader);
        owners.sort_unstable();
        let firsts = owners
            .into_iter()
            .map(|owner| {
                g::Signed::sign(
                    &f.schemes[usize::from(owner)],
                    message(g::Kind::First(g::First {
                        core: core.id::<Sha256>(),
                        input: decision.input,
                        owner,
                        report: None,
                        preference: (owner != core.leader).then(|| decision.order.clone()),
                    })),
                    WIRE_LIMITS,
                )
                .unwrap()
            })
            .collect();
        let body = g::OriginBody {
            decision,
            core: core.clone(),
            firsts,
            population: D::from([26; 32]),
            build: Bytes::from_static(b"unvalidated-build"),
            material: Bytes::new(),
        };
        let selection = g::Signed::sign(
            &f.schemes[usize::from(core.leader)],
            message(g::Kind::Select {
                body: body.id::<Sha256>(),
                decision: body.decision.id::<Sha256>(),
            }),
            WIRE_LIMITS,
        )
        .unwrap();
        let origin = g::Origin { body, selection };
        let pairs = f
            .schemes
            .iter()
            .map(|scheme| g::normal::Vote {
                native: vote::Vote::sign(
                    scheme,
                    g::normal::subject::<Sha256>(&origin.body.decision),
                )
                .unwrap(),
                agreement: g::Signed::sign(
                    scheme,
                    message(g::Kind::Phase {
                        phase: g::Phase::FastFinal,
                        decision: origin.body.decision.id::<Sha256>(),
                    }),
                    WIRE_LIMITS,
                )
                .unwrap(),
                origin_hint: origin.id::<Sha256>(),
            })
            .collect();
        Self {
            f,
            core,
            origin,
            pairs,
        }
    }
    fn first(&self, owner: usize, signed: bool) -> FirstVote<S, D> {
        FirstVote::new(
            Notarize::sign(&self.f.schemes[owner], self.core.slot.proposal.clone()).unwrap(),
            signed.then(|| {
                self.origin
                    .body
                    .firsts
                    .iter()
                    .find(|first| usize::from(first.attestation.signer) == owner)
                    .unwrap()
                    .clone()
            }),
        )
    }
    pub(crate) fn certificate(&self, start: usize) -> Finalization<S, D> {
        let q = g::Committee::new(self.f.schemes.len()).unwrap().quorum();
        let pairs = &self.pairs[start..start + q];
        let native = vote::Certificate::from_votes(
            &mut TestRng::new(301),
            &self.f.verifier,
            NonEmpty::new(
                pairs[0].native.clone(),
                pairs.iter().skip(1).map(|pair| pair.native.clone()),
            ),
            &Sequential,
        )
        .unwrap();
        let agreement = g::Quorum::from_votes(
            &mut TestRng::new(302),
            &self.f.verifier,
            &pairs
                .iter()
                .map(|pair| pair.agreement.clone())
                .collect::<Vec<_>>(),
            WIRE_LIMITS,
            &Sequential,
        )
        .unwrap();
        Finalization::new(g::normal::Certificate {
            native,
            agreement,
            notarization: self.notarization(),
            origin: self.origin.clone(),
        })
    }
    pub(crate) fn notarization(&self) -> Notarization<S, D> {
        let q = g::Committee::new(self.f.schemes.len()).unwrap().quorum();
        let firsts: Vec<_> = self
            .f
            .schemes
            .iter()
            .take(q)
            .map(|scheme| Notarize::sign(scheme, self.core.slot.proposal.clone()).unwrap())
            .collect();
        Notarization::from_notarizes(&self.f.verifier, non_empty![@firsts.iter()], &Sequential)
            .unwrap()
    }
    pub(crate) fn assembly(&self, origin: g::Origin<S, D>) -> g::normal::Assembly<S, D> {
        // This fixture's trusted policy permits its opaque literals. It does
        // not model the SDK's report/order/Build validation or native admission.
        g::normal::Assembly::new::<Sha256, _>(
            &mut TestRng::new(317),
            &self.f.verifier,
            &self.core,
            origin.body.decision.input,
            origin,
            self.notarization(),
            LIMITS,
            |_| true,
            |_, _| true,
            &Sequential,
        )
        .unwrap()
    }
    pub(crate) fn alias(&self) -> g::Origin<S, D> {
        let mut origin = self.origin.clone();
        origin.body.population = D::from([27; 32]);
        origin.body.build = Bytes::from_static(b"another-accepted-build");
        self.endorse(&mut origin);
        origin
    }
    pub(crate) fn endorse(&self, origin: &mut g::Origin<S, D>) {
        origin.selection = g::Signed::sign(
            &self.f.schemes[usize::from(self.core.leader)],
            g::Message {
                slot: self.core.slot.id::<Sha256>(),
                round: self.core.slot.proposal.round,
                leader: self.core.leader,
                kind: g::Kind::Select {
                    body: origin.body.id::<Sha256>(),
                    decision: origin.body.decision.id::<Sha256>(),
                },
            },
            WIRE_LIMITS,
        )
        .unwrap();
    }
}

#[test]
fn general_mode_authenticates_real_pairs_and_exact_q_on_larger_slack_rosters() {
    for n in [4, 7, 8, 9, 10, 13, 64] {
        let setup = Setup::new(n, 300);
        let certificate = setup.certificate(0);
        assert!(<M as Mode<S, D>>::verify(
            &certificate,
            &mut TestRng::new(303),
            &setup.f.verifier,
            &Sequential
        ));
        let scoped = Scoped::verifier(Arc::new(setup.f.verifier.clone()));
        assert!(<M as Mode<S, D>>::verify_companion(
            &certificate,
            &mut TestRng::new(304),
            &scoped,
            &Sequential
        ));
        assert_eq!(certificate.epoch(), setup.core.slot.proposal.epoch());
        assert_eq!(certificate.view(), setup.core.slot.proposal.view());
        assert_eq!(
            <M as Mode<S, D>>::finalization_certificate(&certificate),
            &certificate.inner().native.certificate
        );
        assert_eq!(
            <M as Mode<S, D>>::finalization_election_certificate(&certificate),
            &certificate.inner().notarization.certificate
        );
        assert_ne!(
            <M as Mode<S, D>>::finalization_certificate(&certificate),
            <M as Mode<S, D>>::finalization_election_certificate(&certificate)
        );
        assert!(
            certificate
                .inner()
                .verify::<Sha256, _>(
                    &mut TestRng::new(305),
                    &setup.f.verifier,
                    &setup.core,
                    setup.origin.body.decision.input,
                    LIMITS,
                    |_| true,
                    |_, _| false,
                    &Sequential
                )
                .is_err(),
            "crypto is not application Build admission"
        );
    }
}

#[test]
fn first_none_and_signed_absence_are_distinct_original_envelopes() {
    let setup = Setup::new(9, 306);
    let leader = usize::from(setup.core.leader);
    let absent = setup.first(leader, false);
    let signed = setup.first(leader, true);
    assert_ne!(absent, signed);
    for first in [absent, signed] {
        first
            .authenticate(&mut TestRng::new(307), &setup.f.verifier, &Sequential)
            .unwrap();
        let decoded = FirstVote::<S, D>::decode(first.encode()).unwrap();
        assert_eq!(decoded, first);
        assert_eq!(decoded.native().encode(), first.native().encode());
    }
    // A None envelope is raw authenticated native data, not proof that a Core
    // owner was allowed to omit FIRST. That admission needs trusted Core.
    let outside = (0..9)
        .find(|owner| {
            *owner != leader
                && !setup
                    .core
                    .followers
                    .contains(&Participant::new(*owner as u32))
        })
        .unwrap();
    assert!(setup.first(outside, false).first().is_none());
    let mut changed = setup.first(leader, true);
    changed.first.as_mut().unwrap().message.round = Round::new(Epoch::new(1), View::new(6));
    assert!(
        changed
            .authenticate(&mut TestRng::new(308), &setup.f.verifier, &Sequential)
            .is_err()
    );
}

fn malformed<T: commonware_codec::Decode>(bytes: Bytes, cfg: &T::Cfg) {
    for len in [0, 4, 7, bytes.len() / 2, bytes.len() - 1] {
        assert!(T::decode_cfg(bytes.slice(..len), cfg).is_err());
    }
    let mut changed = bytes.to_vec();
    changed[3] ^= 1;
    assert!(T::decode_cfg(Bytes::from(changed), cfg).is_err());
    let mut changed = bytes.to_vec();
    changed[4..8].copy_from_slice(&u32::MAX.to_be_bytes());
    assert!(T::decode_cfg(Bytes::from(changed), cfg).is_err());
    let mut changed = bytes.to_vec();
    changed.push(0);
    assert!(T::decode_cfg(Bytes::from(changed), cfg).is_err());
}
#[test]
fn general_wire_adapters_preserve_inner_bytes_and_reject_malformed_frames() {
    let setup = Setup::new(8, 309);
    let first = setup.first(usize::from(setup.core.leader), true);
    let vote = FinalVote::new(setup.pairs[0].clone());
    let certificate = setup.certificate(0);
    let cfg = setup.f.verifier.certificate_codec_config();
    assert_eq!(vote.encode(), vote.inner().encode());
    assert_eq!(certificate.encode(), certificate.inner().encode());
    assert_eq!(FinalVote::<S, D>::decode(vote.encode()).unwrap(), vote);
    assert_eq!(
        Finalization::<S, D>::decode_cfg(certificate.encode(), &cfg).unwrap(),
        certificate
    );
    assert_eq!(
        VoteWith::<S, D, M>::decode(VoteWith::<S, D, M>::Finalize(vote.clone()).encode()).unwrap(),
        VoteWith::<S, D, M>::Finalize(vote.clone())
    );
    malformed::<FirstVote<S, D>>(first.encode(), &());
    malformed::<FinalVote<S, D>>(vote.encode(), &());
    malformed::<Finalization<S, D>>(certificate.encode(), &cfg);
    let mut bad = first.encode().to_vec();
    let tag = 8 + 4 + first.native().encode_size();
    bad[tag] = 2;
    assert!(FirstVote::<S, D>::decode(Bytes::from(bad)).is_err());
    let mut bad = first.encode().to_vec();
    bad[8..12].copy_from_slice(&u32::MAX.to_be_bytes());
    assert!(FirstVote::<S, D>::decode(Bytes::from(bad)).is_err());
    let mut bad = first.encode().to_vec();
    bad.push(0);
    let len = (bad.len() - 8) as u32;
    bad[4..8].copy_from_slice(&len.to_be_bytes());
    assert!(FirstVote::<S, D>::decode(Bytes::from(bad)).is_err());
}

#[test]
fn final_hint_retry_does_not_erase_signed_conflicts_or_change_exact_equality() {
    let setup = Setup::new(10, 310);
    let a = FinalVote::new(setup.pairs[0].clone());
    let mut raw = a.inner().clone();
    raw.origin_hint = D::from([99; 32]);
    let b = FinalVote::new(raw);
    assert_ne!(a, b);
    assert!(<M as Mode<S, D>>::equivalent_finalize(&a, &b));
    assert!(!<M as Mode<S, D>>::conflicting_finalize_subjects(&a, &b));
    assert!(<M as Mode<S, D>>::verify_finalize(
        &b,
        &mut TestRng::new(311),
        &setup.f.verifier,
        &Sequential
    ));
    let mut bad = b.into_inner();
    bad.agreement.message.leader = Participant::new(0);
    let bad = FinalVote::new(bad);
    assert!(<M as Mode<S, D>>::conflicting_finalize_subjects(&a, &bad));
    assert!(!<M as Mode<S, D>>::verify_finalize(
        &bad,
        &mut TestRng::new(312),
        &setup.f.verifier,
        &Sequential
    ));
}

#[test]
fn general_companion_rejects_different_q_owner_sets_and_wrong_nqc() {
    let setup = Setup::new(9, 313);
    let a = setup.certificate(0);
    let b = setup.certificate(1);
    let mut mismatch = a.inner().clone();
    mismatch.agreement = b.into_inner().agreement;
    assert!(!<M as Mode<S, D>>::verify(
        &Finalization::new(mismatch),
        &mut TestRng::new(314),
        &setup.f.verifier,
        &Sequential
    ));
    let q = g::Committee::new(9).unwrap().quorum();
    let mut wrong = setup.core.slot.proposal.clone();
    wrong.payload = D::from([98; 32]);
    let votes: Vec<_> = setup
        .f
        .schemes
        .iter()
        .take(q)
        .map(|s| Notarize::sign(s, wrong.clone()).unwrap())
        .collect();
    let mut mismatch = a.into_inner();
    mismatch.notarization =
        Notarization::from_notarizes(&setup.f.verifier, non_empty![@votes.iter()], &Sequential)
            .unwrap();
    assert!(
        mismatch
            .notarization
            .verify(&mut TestRng::new(315), &setup.f.verifier, &Sequential)
    );
    assert!(!<M as Mode<S, D>>::verify_companion(
        &Finalization::new(mismatch),
        &mut TestRng::new(316),
        &Scoped::verifier(Arc::new(setup.f.verifier)),
        &Sequential
    ));
}

struct GeneralModeConformance;
impl Conformance for GeneralModeConformance {
    async fn commit(seed: u64) -> Vec<u8> {
        let setup = Setup::new(8, seed);
        let first = setup.first(usize::from(setup.core.leader), seed.is_multiple_of(2));
        let vote = FinalVote::new(setup.pairs[seed as usize % setup.pairs.len()].clone());
        let certificate = setup.certificate(usize::from(seed.is_multiple_of(3)));
        let cfg = setup.f.verifier.certificate_codec_config();
        let frames = vec![first.encode(), vote.encode(), certificate.encode()];
        assert_eq!(
            FirstVote::<S, D>::decode(frames[0].clone())
                .unwrap()
                .encode(),
            frames[0]
        );
        assert_eq!(
            FinalVote::<S, D>::decode(frames[1].clone())
                .unwrap()
                .encode(),
            frames[1]
        );
        assert_eq!(
            Finalization::<S, D>::decode_cfg(frames[2].clone(), &cfg)
                .unwrap()
                .encode(),
            frames[2]
        );
        frames.encode().to_vec()
    }
}
commonware_conformance::conformance_tests! { GeneralModeConformance => 16 }

#[cfg(feature = "arbitrary")]
#[test]
fn bounded_arbitrary_wrappers_have_positive_exact_codec_roundtrips() {
    use arbitrary::{Arbitrary as _, Unstructured};
    use rand_core::Rng as _;

    let mut accepted = [0usize; 3];
    for seed in 0..64 {
        let mut bytes = vec![0u8; 32 * 1024];
        TestRng::new(seed).fill_bytes(&mut bytes);
        if let Ok(value) = FirstVote::<S, D>::arbitrary(&mut Unstructured::new(&bytes)) {
            assert!(value.encode_size() <= MAX_FIRST_VOTE_BYTES);
            assert_eq!(FirstVote::<S, D>::decode(value.encode()).unwrap(), value);
            accepted[0] += 1;
        }
        if let Ok(value) = FinalVote::<S, D>::arbitrary(&mut Unstructured::new(&bytes)) {
            assert!(value.encode_size() <= g::MAX_EVIDENCE_BYTES);
            assert_eq!(FinalVote::<S, D>::decode(value.encode()).unwrap(), value);
            accepted[1] += 1;
        }
        if let Ok(value) = Finalization::<S, D>::arbitrary(&mut Unstructured::new(&bytes)) {
            assert!(value.encode_size() <= g::MAX_EVIDENCE_BYTES);
            assert_eq!(
                Finalization::<S, D>::decode_cfg(value.encode(), &64).unwrap(),
                value
            );
            accepted[2] += 1;
        }
    }
    assert!(accepted.into_iter().all(|count| count > 0));
}
