//! Actual native Verifier wake-up with original paired votes and checked material.
use super::*;
use crate::simplex::{
    phase2::general::{FinalVote, General, tests::Setup},
    scheme::ed25519,
};
use commonware_cryptography::sha256::{Digest as D, Sha256};
use commonware_parallel::Sequential;
use commonware_runtime::{Runner as _, deterministic};
use commonware_utils::TestRng;

type S = ed25519::Scheme;
type M = General<Sha256>;

#[test]
fn unknown_native_proposal_requires_q_pairs_and_material_without_material_selecting_it() {
    deterministic::Runner::default().start(|_| async move {
        for n in [4, 7, 8, 9, 10, 13, 64] {
            let setup = Setup::new(n, 410);
            let q = crate::simplex::extension::agreement::general::Committee::new(n)
                .unwrap()
                .quorum();
            for material_first in [false, true] {
                let mut verifier = VerifierWith::<S, D, M>::new(
                    setup.core.slot.proposal.round,
                    setup.f.verifier.clone(),
                    q as u32,
                );
                assert!(verifier.proposal().is_none());
                let material = setup.assembly(setup.origin.clone());
                if material_first {
                    assert!(verifier.install_assembly(material.clone()));
                    assert!(verifier.proposal().is_none());
                }
                for pair in setup.pairs.iter().take(q - 1) {
                    verifier.add(VoteWith::Finalize(FinalVote::new(pair.clone())), false);
                }
                assert!(
                    verifier
                        .try_construct_finalization(&mut TestRng::new(411), &Sequential)
                        .await
                        .is_none()
                );
                verifier.add(
                    VoteWith::Finalize(FinalVote::new(setup.pairs[q - 1].clone())),
                    false,
                );
                if !material_first {
                    assert!(
                        verifier
                            .try_construct_finalization(&mut TestRng::new(412), &Sequential)
                            .await
                            .is_none()
                    );
                    assert!(verifier.install_assembly(material));
                    assert!(verifier.proposal().is_none());
                }
                let batch = verifier
                    .try_construct_finalization(&mut TestRng::new(413), &Sequential)
                    .await
                    .unwrap();
                assert!(batch.invalid.is_empty());
                let CertificateWith::Finalization(certificate) = batch.certificate.unwrap() else {
                    std::panic!("expected exact paired final certificate");
                };
                assert!(<M as crate::simplex::phase2::Mode<S, D>>::verify(
                    &certificate,
                    &mut TestRng::new(414),
                    &setup.f.verifier,
                    &Sequential,
                ));
                assert!(
                    verifier.proposal().is_none(),
                    "install/assembly never selects a native proposal"
                );
            }
        }
    });
}
