//! Stock seven-validator controls for the interpretation attachment's native boundary.
//!
//! Certificate fixtures supply authenticated first-phase input. Five real epoch states
//! then make the local timeout/final choices; the two other identities remain silent.
//! These are state/eligibility controls, not an actor, journal, or network campaign.
use super::*;
use commonware_consensus::simplex::types::{Finalization as NativeFinalization, Nullification};
use commonware_runtime::Clock as _;

type S = ed25519::Scheme;
type NativeState = StateWith<deterministic::Context, S, RoundRobinElector<S>, Digest, Plain>;

fn fixture() -> Fixture<S> {
    ed25519::fixture(
        &mut TestRng::new(701),
        b"_COMMONWARE_CONSENSUS_NATIVE_POLICY_TEST",
        7,
    )
}

fn native_state(context: deterministic::Context, f: &Fixture<S>, i: usize) -> NativeState {
    let mut s = StateWith::new(context, config(f.schemes[i].clone(), 1));
    s.set_genesis(Digest::from([0; 32]));
    s
}

fn notarized(f: &Fixture<S>, p: &Proposal<Digest>) -> Notarization<S, Digest> {
    let votes: Vec<_> = f
        .schemes
        .iter()
        .take(5)
        .map(|s| Notarize::sign(s, p.clone()).unwrap())
        .collect();
    let qc = Notarization::from_notarizes(&f.verifier, non_empty![@&votes], &Sequential).unwrap();
    assert!(qc.verify(&mut TestRng::new(702), &f.verifier, &Sequential));
    qc
}

fn certify(s: &mut NativeState, p: &Proposal<Digest>) {
    let (ready, fetches) = s.certify_candidates();
    assert_eq!(ready, vec![p.clone()]);
    assert!(fetches.is_empty());
    assert_eq!(s.certified(p.round.view(), true).unwrap().proposal, *p);
}

#[test]
fn tentative_notarization_does_not_pin_input_after_native_nullification() {
    // The two alternatives run in separate executions. They do not create two
    // conflicting second-view certificates in one honest signing history.
    for keep_parent in [false, true] {
        deterministic::Runner::default().start(|context| async move {
            let f = fixture();
            let first = proposal(1);
            let mut states: Vec<_> = (0..5)
                .map(|i| native_state(context.child("voter").with_attribute("i", i), &f, i))
                .collect();
            let first_qc = notarized(&f, &first);
            for s in &mut states {
                assert!(s.add_notarization(first_qc.clone()).0);
                assert_eq!(s.current_view(), View::new(1));
            }

            let mut nullifies = Vec::new();
            for s in &mut states {
                let (deadline, reason) = s.next_timeout();
                context.sleep_until(deadline).await;
                let (retry, vote) = s.construct_nullify(View::new(1), reason).unwrap();
                assert!(!retry);
                nullifies.push(vote);
            }
            let skipped =
                Nullification::from_nullifies(&f.verifier, non_empty![@&nullifies], &Sequential)
                    .unwrap();
            assert!(skipped.verify::<_, Digest>(&mut TestRng::new(703), &f.verifier, &Sequential));

            let mut next = proposal(2);
            if !keep_parent {
                next.parent = View::zero();
            }
            for s in &mut states {
                assert!(s.add_nullification(skipped.clone()));
                assert_eq!(s.current_view(), View::new(2));
                if keep_parent {
                    certify(s, &first);
                }
            }
            // The sibling is built before P1 certifies; the child is built
            // after. Both use the elected leader's real parent-selection path.
            let builds: Vec<_> = states.iter_mut().filter_map(|s| s.try_propose()).collect();
            assert_eq!(builds.len(), 1);
            assert_eq!(builds[0].round, next.round);
            assert_eq!(builds[0].parent.0, next.parent);
            assert_eq!(
                builds[0].parent.1,
                if keep_parent {
                    first.payload
                } else {
                    Digest::from([0; 32])
                }
            );
            let next_qc = notarized(&f, &next);
            let mut finalizes = Vec::new();
            for s in &mut states {
                // Native nullification retains pending certification and the old
                // notarization. It neither deletes P nor forces its inclusion.
                if !keep_parent {
                    certify(s, &first);
                }
                assert_eq!(s.notarization(View::new(1)).unwrap().proposal, first);
                assert!(s.construct_finalize(View::new(1)).is_none());
                assert!(s.add_notarization(next_qc.clone()).0);
                certify(s, &next);
                finalizes.push(s.construct_finalize(View::new(2)).unwrap());
            }
            let finality = NativeFinalization::from_finalizes(
                &f.verifier,
                non_empty![@&finalizes],
                &Sequential,
            )
            .unwrap();
            assert!(finality.verify(&mut TestRng::new(704), &f.verifier, &Sequential));
            assert_eq!(finality.proposal, next);
            for s in &mut states {
                assert!(s.add_finalization(finality.clone()).0);
                assert_eq!(s.last_finalized(), View::new(2));
            }
        });
    }
}

#[test]
fn original_final_nullify_split_heals_through_a_real_native_descendant() {
    deterministic::Runner::default().start(|context| async move {
        let f = fixture();
        let first = proposal(1);
        let child = proposal(2);
        assert_eq!(child.parent, first.round.view());
        let mut states: Vec<_> = (0..5)
            .map(|i| native_state(context.child("voter").with_attribute("i", i), &f, i))
            .collect();
        let first_qc = notarized(&f, &first);
        for s in &mut states {
            assert!(s.add_notarization(first_qc.clone()).0);
        }
        // H0,H1,H2 certify before their first deadline. Their next-view
        // deadline leaves time for H3,H4 to finish the old timed-out view.
        context.sleep(Duration::from_millis(100)).await;
        let mut first_finalizes = Vec::new();
        for s in &mut states[..3] {
            assert!(context.current() < s.next_timeout().0);
            certify(s, &first);
            first_finalizes.push(s.construct_finalize(View::new(1)).unwrap());
        }
        // H3,H4 time out before their certification completes.
        let mut nullifies = Vec::new();
        for s in &mut states[3..] {
            let (deadline, reason) = s.next_timeout();
            context.sleep_until(deadline).await;
            nullifies.push(s.construct_nullify(View::new(1), reason).unwrap().1);
            certify(s, &first);
            assert!(s.construct_finalize(View::new(1)).is_none());
        }
        for s in &states {
            assert_eq!(s.current_view(), View::new(2));
            assert_eq!(s.last_finalized(), View::zero());
        }
        assert!(
            NativeFinalization::from_finalizes(
                &f.verifier,
                non_empty![@&first_finalizes],
                &Sequential,
            )
            .is_err()
        );
        assert!(
            Nullification::from_nullifies(&f.verifier, non_empty![@&nullifies], &Sequential)
                .is_err()
        );

        let child_qc = notarized(&f, &child);
        let mut finalizes = Vec::new();
        for s in &mut states {
            assert!(context.current() < s.next_timeout().0);
            assert!(s.add_notarization(child_qc.clone()).0);
            certify(s, &child);
            finalizes.push(s.construct_finalize(View::new(2)).unwrap());
        }
        let finality =
            NativeFinalization::from_finalizes(&f.verifier, non_empty![@&finalizes], &Sequential)
                .unwrap();
        assert!(finality.verify(&mut TestRng::new(705), &f.verifier, &Sequential));
        assert_eq!(finality.proposal.parent, View::new(1));
        for s in &mut states {
            assert!(s.add_finalization(finality.clone()).0);
            assert_eq!(s.last_finalized(), View::new(2));
            assert!(s.finalization(View::new(1)).is_none());
            assert_eq!(s.notarization(View::new(1)).unwrap().proposal, first);
            // The old P is an ancestor of a finalized child; no old-view QC is
            // fabricated and no local Nullify/FINAL decision is reset.
            assert!(s.construct_finalize(View::new(1)).is_none());
        }
    });
}

#[test]
fn native_proposal_build_keeps_the_certified_parent() {
    deterministic::Runner::default().start(|context| async move {
        let f = fixture();
        let first = proposal(1);
        let mut builders = 0;
        for i in 0..7 {
            let mut s = native_state(context.child("voter").with_attribute("i", i), &f, i);
            s.add_notarization(notarized(&f, &first));
            certify(&mut s, &first);
            assert!(s.nullification(View::new(1)).is_none());
            if let Some(build) = s.try_propose() {
                builders += 1;
                assert!(s.is_me(s.leader_index(View::new(2)).unwrap()));
                assert_eq!(build.round.view(), View::new(2));
                assert_eq!(build.parent, (View::new(1), first.payload));
            }
            assert_eq!(s.last_finalized(), View::zero());
        }
        assert_eq!(builders, 1);
    });
}
