//! Real complete-pair buffer controls, without voter issuance or live SDK policy.
use super::*;
use crate::simplex::{phase2::general::tests::Setup, scheme::ed25519};
use commonware_cryptography::sha256::{Digest as D, Sha256};
use commonware_parallel::Sequential;
use commonware_runtime::{Runner as _, deterministic};
use commonware_utils::TestRng;

type S = ed25519::Scheme;
type Buffer = Groups<S, D, Sha256>;
type M = General<Sha256>;

async fn construct(buffer: &mut Buffer, setup: &Setup) -> Option<Batch<Finalization<S, D>>> {
    buffer
        .construct(
            &Arc::new(setup.f.verifier.clone()),
            setup.core.slot.proposal.round,
            &mut TestRng::new(401),
            &Sequential,
        )
        .await
}

fn authenticated(batch: Batch<Finalization<S, D>>, setup: &Setup) -> Finalization<S, D> {
    assert!(batch.invalid.is_empty());
    let certificate = batch
        .certificate
        .expect("complete exact-q pairs and material");
    assert!(<M as Mode<S, D>>::verify(
        &certificate,
        &mut TestRng::new(402),
        &setup.f.verifier,
        &Sequential,
    ));
    certificate
}

#[test]
fn real_general_buffer_requires_q_and_material_in_either_arrival_order() {
    deterministic::Runner::default().start(|_| async move {
        for n in [4, 7, 8, 9, 10, 13, 64] {
            let setup = Setup::new(n, 400);
            let q = g::Committee::new(n).unwrap().quorum();
            let material = setup.assembly(setup.origin.clone());
            for material_first in [false, true] {
                let mut buffer = Buffer::new(q, n);
                if material_first {
                    assert!(buffer.install_assembly(material.clone()));
                }
                for pair in setup.pairs.iter().take(q - 1) {
                    buffer.push(FinalVote::new(pair.clone()), false);
                }
                let before = construct(&mut buffer, &setup).await.unwrap();
                assert!(before.invalid.is_empty());
                assert!(before.certificate.is_none(), "q-1, n={n}");
                buffer.push(FinalVote::new(setup.pairs[q - 1].clone()), false);
                if !material_first {
                    let without = construct(&mut buffer, &setup).await.unwrap();
                    assert!(without.invalid.is_empty());
                    assert!(without.certificate.is_none(), "missing material, n={n}");
                    assert!(!buffer.has_constructable_quorum());
                    assert!(buffer.install_assembly(material.clone()));
                }
                assert!(buffer.has_constructable_quorum());
                let certificate =
                    authenticated(construct(&mut buffer, &setup).await.unwrap(), &setup);
                assert_eq!(
                    certificate.inner().native.statement,
                    setup.pairs[0].native.statement
                );
                assert!(buffer.is_complete());
                assert_eq!(buffer.bytes, 0);
                assert!(buffer.groups.is_empty() && buffer.material.is_empty());
                assert!(!buffer.install_assembly(material.clone()));
                assert!(construct(&mut buffer, &setup).await.is_none());
            }
        }
    });
}

#[test]
fn exact_alias_duplicates_coalesce_but_distinct_proofs_and_owner_credit_stay_separate() {
    deterministic::Runner::default().start(|_| async move {
        for n in [4, 7, 8, 9, 10, 13, 64] {
            let setup = Setup::new(n, 403);
            let q = g::Committee::new(n).unwrap().quorum();
            let original = setup.assembly(setup.origin.clone());
            let alias_origin = setup.alias();
            let alias_hint = alias_origin.id::<Sha256>();
            let alias = setup.assembly(alias_origin);
            assert_ne!(original, alias);
            assert!(<M as Mode<S, D>>::equivalent_assembly(&original, &alias));
            let mut buffer = Buffer::new(q, n);
            assert!(buffer.install_assembly(original.clone()));
            assert!(buffer.install_assembly(alias.clone()));
            assert!(buffer.install_assembly(original.clone()));
            assert!(buffer.install_assembly(alias.clone()));
            assert_eq!(buffer.material.len(), 2);
            assert_eq!(
                buffer.bytes,
                original.retained_bytes() + alias.retained_bytes()
            );
            for (index, pair) in setup.pairs.iter().take(q - 1).enumerate() {
                let mut pair = pair.clone();
                if index.is_multiple_of(2) {
                    pair.origin_hint = alias_hint;
                }
                buffer.push(FinalVote::new(pair), false);
            }
            let mut retry = setup.pairs[0].clone();
            retry.origin_hint = D::from([199; 32]);
            buffer.push(FinalVote::new(retry), false);
            assert_eq!(
                buffer.groups.iter().map(|g| g.votes.len()).sum::<usize>(),
                q - 1
            );
            let batch = construct(&mut buffer, &setup).await.unwrap();
            assert!(batch.invalid.is_empty() && batch.certificate.is_none());
            buffer.push(FinalVote::new(setup.pairs[q - 1].clone()), false);
            let certificate = authenticated(construct(&mut buffer, &setup).await.unwrap(), &setup);
            assert_eq!(
                certificate.inner().origin.id::<Sha256>(),
                setup.origin.id::<Sha256>()
            );
        }
    });
}

#[test]
fn different_core_material_never_substitutes_for_matching_pairs_or_blames_signers() {
    deterministic::Runner::default().start(|_| async move {
        for n in [4, 7, 8, 9, 10, 13, 64] {
            let setup = Setup::new(n, 404);
            // Both are genuine locally checked declared Cores. Only native
            // admission can choose the actual Core; material itself cannot.
            let other = Setup::with_leader(n, 404, crate::types::Participant::new(0));
            assert_eq!(setup.f.participants, other.f.participants);
            let original = setup.assembly(setup.origin.clone());
            let wrong = other.assembly(other.origin.clone());
            assert_eq!(original.decision(), wrong.decision());
            assert!(!<M as Mode<S, D>>::equivalent_assembly(&original, &wrong));
            let q = g::Committee::new(n).unwrap().quorum();
            let mut buffer = Buffer::new(q, n);
            assert!(buffer.install_assembly(wrong));
            for pair in setup.pairs.iter().take(q) {
                buffer.push(FinalVote::new(pair.clone()), false);
            }
            let batch = construct(&mut buffer, &setup).await.unwrap();
            assert!(batch.certificate.is_none());
            assert!(
                batch.invalid.is_empty(),
                "wrong material is not a signer fault"
            );
            assert!(!buffer.has_constructable_quorum());
            assert!(buffer.install_assembly(original));
            assert!(buffer.has_constructable_quorum());
            authenticated(construct(&mut buffer, &setup).await.unwrap(), &setup);
        }
    });
}

#[test]
fn invalid_pair_is_reported_without_borrowing_its_native_half() {
    deterministic::Runner::default().start(|_| async move {
        let setup = Setup::new(10, 405);
        let q = g::Committee::new(10).unwrap().quorum();
        let mut buffer = Buffer::new(q, 10);
        assert!(buffer.install_assembly(setup.assembly(setup.origin.clone())));
        for pair in setup.pairs.iter().take(q - 1) {
            buffer.push(FinalVote::new(pair.clone()), false);
        }
        let mut invalid = setup.pairs[q - 1].clone();
        invalid.agreement = setup.pairs[q].agreement.clone();
        buffer.push(FinalVote::new(invalid), false);
        let batch = construct(&mut buffer, &setup).await.unwrap();
        assert!(batch.certificate.is_none());
        assert_eq!(
            batch.invalid,
            vec![setup.pairs[q - 1].native.attestation.signer]
        );
        buffer.push(FinalVote::new(setup.pairs[q].clone()), false);
        authenticated(construct(&mut buffer, &setup).await.unwrap(), &setup);
    });
}

#[test]
fn failed_foreign_namespace_material_must_not_leave_immediately_constructable_work() {
    deterministic::Runner::default().start(|_| async move {
        let n = 10;
        let setup = Setup::new(n, 406);
        let foreign = Setup::with_namespace(
            n,
            406,
            setup.core.leader,
            b"_COMMONWARE_CONSENSUS_G1_MODE_FOREIGN_NAMESPACE_TEST",
        );
        assert_eq!(setup.f.participants, foreign.f.participants);
        assert_eq!(setup.core, foreign.core);
        let material = foreign.assembly(foreign.origin.clone());
        let q = g::Committee::new(n).unwrap().quorum();
        let mut buffer = Buffer::new(q, n);
        assert!(buffer.install_assembly(material.clone()));
        for pair in setup.pairs.iter().take(q) {
            buffer.push(FinalVote::new(pair.clone()), false);
        }
        assert!(buffer.has_constructable_quorum());
        let batch = construct(&mut buffer, &setup).await.unwrap();
        assert!(batch.certificate.is_none());
        assert!(
            batch.invalid.is_empty(),
            "material namespace failure is not a vote fault"
        );
        assert!(
            !buffer.has_constructable_quorum(),
            "failed material must not leave an immediately retried zero-progress batch"
        );
        assert!(
            !buffer.install_assembly(material),
            "an exact failed proof stays fused"
        );
        assert!(buffer.install_assembly(setup.assembly(setup.origin.clone())));
        authenticated(construct(&mut buffer, &setup).await.unwrap(), &setup);
    });
}

#[test]
fn valid_and_foreign_material_in_either_arrival_order_preserve_the_valid_alias() {
    deterministic::Runner::default().start(|_| async move {
        let n = 8;
        let setup = Setup::new(n, 408);
        let foreign = Setup::with_namespace(
            n,
            408,
            setup.core.leader,
            b"_COMMONWARE_CONSENSUS_G1_MODE_FOREIGN_NAMESPACE_TEST",
        );
        assert_eq!(setup.f.participants, foreign.f.participants);
        let valid = setup.assembly(setup.origin.clone());
        let invalid = foreign.assembly(foreign.origin.clone());
        assert_ne!(valid, invalid);
        assert!(<M as Mode<S, D>>::equivalent_assembly(&valid, &invalid));
        let q = g::Committee::new(n).unwrap().quorum();
        for foreign_first in [false, true] {
            let mut buffer = Buffer::new(q, n);
            let ordered = if foreign_first {
                [invalid.clone(), valid.clone()]
            } else {
                [valid.clone(), invalid.clone()]
            };
            for material in ordered {
                assert!(buffer.install_assembly(material));
            }
            assert_eq!(
                buffer.material.len(),
                2,
                "no unchecked-scope alias overwrite"
            );
            for pair in setup.pairs.iter().take(q) {
                buffer.push(FinalVote::new(pair.clone()), false);
            }
            let certificate = authenticated(construct(&mut buffer, &setup).await.unwrap(), &setup);
            assert_eq!(
                certificate.inner().origin.id::<Sha256>(),
                setup.origin.id::<Sha256>()
            );
        }
    });
}

#[test]
fn tentative_proposal_filter_must_not_discard_preinstalled_later_authoritative_material() {
    deterministic::Runner::default().start(|_| async move {
        let n = 9;
        let setup = Setup::new(n, 407);
        let q = g::Committee::new(n).unwrap().quorum();
        let mut tentative = setup.core.slot.proposal.clone();
        tentative.payload = D::from([198; 32]);
        let mut buffer = Buffer::new(q, n);
        assert!(buffer.install_assembly(setup.assembly(setup.origin.clone())));
        // A leader's tentative A can be replaced by genuine certificate B.
        // Only B has a QC here; A is merely a proposal value.
        buffer.retain_proposal(&tentative);
        buffer.retain_proposal(&setup.core.slot.proposal);
        for pair in setup.pairs.iter().take(q) {
            buffer.push(FinalVote::new(pair.clone()), false);
        }
        assert!(
            buffer.has_constructable_quorum(),
            "independently retained checked material needs no retransmission"
        );
        authenticated(construct(&mut buffer, &setup).await.unwrap(), &setup);
    });
}
