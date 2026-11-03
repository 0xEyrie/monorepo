//! Actual epoch state enforces native eligibility and exact parent interpretation.
use commonware_consensus::{
    simplex::{
        FloorWith,
        elector::{Config as _, RoundRobin, RoundRobinElector},
        extension::{
            certificate::Finalization,
            vote::{Certificate, Statement, Vote},
        },
        phase2::{
            Extended, Plain,
            voting::{ExtendedContext, StateConfig, StateWith},
        },
        scheme::{
            self, bls12381_multisig,
            bls12381_threshold::{standard, vrf},
            ed25519,
        },
        types::{ArtifactWith, Notarization, Notarize, Nullify, Proposal},
    },
    types::{Epoch, Round, TermLength, View, ViewDelta},
};
use commonware_cryptography::{
    bls12381::primitives::variant::MinSig,
    certificate::mocks::Fixture,
    sha256::{Digest, Sha256},
};
use commonware_parallel::Sequential;
use commonware_runtime::{Runner as _, Supervisor as _, deterministic};
use commonware_utils::{TestRng, non_empty};
use std::{num::NonZeroU32, time::Duration};
type State<S> = StateWith<deterministic::Context, S, RoundRobinElector<S>, Digest, Extended>;
fn config<S: scheme::Scheme<Digest>>(scheme: S, term: u32) -> StateConfig<S, RoundRobinElector<S>> {
    let elector = <RoundRobin>::default();
    let elector = if term > 1 {
        elector.with_term(
            TermLength::new(NonZeroU32::new(term).unwrap()),
            Duration::from_secs(10),
            ViewDelta::new(0),
        )
    } else {
        elector
    };
    let elector = elector.build(scheme.participants());
    StateConfig {
        scheme,
        elector,
        epoch: Epoch::new(1),
        view_retention: ViewDelta::new(10),
        leader_timeout: Duration::from_secs(1),
        certification_timeout: Duration::from_secs(1),
        timeout_retry: Duration::from_secs(1),
        skip_budget: 4,
    }
}
fn state<S: scheme::Scheme<Digest>>(
    context: deterministic::Context,
    scheme: S,
    term: u32,
) -> State<S> {
    let mut state = StateWith::new_with(
        context,
        config(scheme, term),
        ExtendedContext::new::<Sha256>(Digest::from([2; 32]), Digest::from([3; 32])),
    );
    state.set_genesis(Digest::from([0; 32]));
    state
}
fn proposal(view: u64) -> Proposal<Digest> {
    Proposal::new(
        Round::new(Epoch::new(1), View::new(view)),
        View::new(view - 1),
        Digest::from([view as u8; 32]),
    )
}
fn subject(view: u64, parent: Digest) -> Statement<Digest> {
    let proposal = proposal(view);
    Statement {
        ballot: proposal.round,
        proposal,
        domain: Digest::from([2; 32]),
        parent,
        extension: Digest::from([view as u8 + 3; 32]),
    }
}
fn notarization<S: scheme::Scheme<Digest>>(
    fixture: &Fixture<S>,
    view: u64,
) -> Notarization<S, Digest> {
    let votes: Vec<_> = fixture
        .schemes
        .iter()
        .take(5)
        .map(|s| Notarize::sign(s, proposal(view)).unwrap())
        .collect();
    Notarization::from_notarizes(&fixture.verifier, non_empty![@&votes], &Sequential).unwrap()
}
fn certificate<S: scheme::Scheme<Digest>>(
    fixture: &Fixture<S>,
    subject: Statement<Digest>,
) -> Finalization<S, Digest> {
    let votes: Vec<_> = fixture
        .schemes
        .iter()
        .take(5)
        .map(|s| Vote::sign(s, subject.clone()).unwrap())
        .collect();
    Finalization::new(
        Certificate::from_votes(
            &mut TestRng::new(11),
            &fixture.verifier,
            non_empty![@votes],
            &Sequential,
        )
        .unwrap(),
    )
    .unwrap()
}
fn exercise<S: scheme::Scheme<Digest>>(fixture: Fixture<S>, term: u32) {
    deterministic::Runner::default().start(|context| async move {
        let mut voter = state(context.child("extended"), fixture.schemes[0].clone(), term);
        let first = subject(1, Digest::from([3; 32]));
        assert!(voter.add_notarization(notarization(&fixture, 1)).0);
        assert!(
            voter
                .construct_finalize_with(first.proposal.round.view(), first.clone())
                .is_none()
        );
        voter.certified(View::new(1), true).unwrap();
        for field in 0..4 {
            let mut invalid = first.clone();
            match field {
                0 => invalid.domain = Digest::from([99; 32]),
                1 => invalid.parent = Digest::from([99; 32]),
                2 => invalid.proposal.payload = Digest::from([99; 32]),
                _ => invalid.ballot = Round::new(Epoch::new(1), View::new(2)),
            }
            assert!(
                voter
                    .construct_finalize_with(invalid.proposal.round.view(), invalid)
                    .is_none()
            );
        }
        let first_vote = voter
            .construct_finalize_with(first.proposal.round.view(), first.clone())
            .unwrap();
        assert!(
            first_vote
                .vote()
                .verify(&mut TestRng::new(12), &fixture.verifier, &Sequential)
        );
        let child = subject(2, first.value::<Sha256>());
        voter.add_notarization(notarization(&fixture, 2));
        voter.certified(View::new(2), true).unwrap();
        assert!(
            voter.current_view() >= View::new(3),
            "native first phase advances before the parent extension QC"
        );
        assert!(
            voter
                .construct_finalize_with(child.proposal.round.view(), child.clone())
                .is_none(),
            "a local parent vote and base certification are not a parent interpretation QC"
        );
        // Identical base inputs permit the stock final vote without this extension gate.
        let mut plain = StateWith::<_, _, _, _, Plain>::new(
            context.child("plain"),
            config(fixture.schemes[0].clone(), term),
        );
        plain.set_genesis(Digest::from([0; 32]));
        for view in 1..=2 {
            plain.add_notarization(notarization(&fixture, view));
            plain.certified(View::new(view), true).unwrap();
        }
        assert!(plain.construct_finalize(View::new(2)).is_some());
        let mut foreign = first.clone();
        foreign.domain = Digest::from([99; 32]);
        assert!(!voter.add_finalization(certificate(&fixture, foreign)).0);
        assert_eq!(voter.last_finalized(), View::zero());
        let parent = certificate(&fixture, first.clone());
        assert!(voter.add_finalization(parent.clone()).0);
        let mut wrong = child.clone();
        wrong.parent = Digest::from([99; 32]);
        assert!(
            voter
                .construct_finalize_with(wrong.proposal.round.view(), wrong)
                .is_none()
        );
        let child_vote = voter
            .construct_finalize_with(child.proposal.round.view(), child.clone())
            .unwrap();
        assert!(
            child_vote
                .vote()
                .verify(&mut TestRng::new(13), &fixture.verifier, &Sequential)
        );
        assert_eq!(child_vote.vote().statement, child);
        assert!(
            voter
                .construct_finalize_with(child.proposal.round.view(), child.clone())
                .is_none()
        );
        // Replay at the real epoch state preserves the round's exact decision.
        let mut replayed = state(context.child("replayed"), fixture.schemes[0].clone(), term);
        for view in 1..=2 {
            replayed.add_notarization(notarization(&fixture, view));
            replayed.certified(View::new(view), true).unwrap();
        }
        replayed.add_finalization(parent.clone());
        replayed.replay(&ArtifactWith::Finalize(first_vote));
        replayed.replay(&ArtifactWith::Finalize(child_vote));
        assert_eq!(replayed.finalization(View::new(1)), Some(&parent));
        let mut anchored = StateWith::<_, _, _, _, Extended>::new_with(
            context.child("floor"),
            config(fixture.schemes[0].clone(), term),
            ExtendedContext::new::<Sha256>(Digest::from([2; 32]), Digest::from([3; 32])),
        );
        assert_eq!(
            anchored.set_floor(FloorWith::Finalized(parent.clone())),
            Some(parent)
        );
        assert_eq!(anchored.last_finalized(), View::new(1));
        anchored.add_notarization(notarization(&fixture, 2));
        anchored.certified(View::new(2), true).unwrap();
        assert_eq!(
            anchored
                .construct_finalize_with(View::new(2), child.clone())
                .unwrap()
                .vote()
                .statement,
            child
        );
        let mut changed = child;
        changed.extension = Digest::from([99; 32]);
        assert!(
            replayed
                .construct_finalize_with(changed.proposal.round.view(), changed)
                .is_none()
        );
        let mut nullified = state(context.child("nullified"), fixture.schemes[0].clone(), term);
        nullified.add_notarization(notarization(&fixture, 1));
        nullified.replay(&ArtifactWith::Nullify(
            Nullify::sign::<Digest>(&fixture.schemes[0], proposal(1).round).unwrap(),
        ));
        nullified.certified(View::new(1), true).unwrap();
        assert!(
            nullified
                .construct_finalize_with(first.proposal.round.view(), first)
                .is_none()
        );
    });
}
const NS: &[u8] = b"_COMMONWARE_CONSENSUS_EXTENSION_VOTER_STATE_TEST";
#[test]
fn ed25519_state_parent_gate() {
    exercise(ed25519::fixture(&mut TestRng::new(1), NS, 6), 5);
}
#[test]
fn multisig_state_parent_gate() {
    exercise(
        bls12381_multisig::fixture::<MinSig, _>(&mut TestRng::new(2), NS, 6),
        5,
    );
}
#[test]
fn threshold_state_parent_gate() {
    exercise(
        standard::fixture::<MinSig, _>(&mut TestRng::new(3), NS, 6),
        5,
    );
}
#[test]
fn vrf_state_parent_gate() {
    exercise(vrf::fixture::<MinSig, _>(&mut TestRng::new(4), NS, 6), 5);
}
#[test]
fn term_boundary_still_requires_parent_interpretation() {
    exercise(ed25519::fixture(&mut TestRng::new(5), NS, 6), 1);
}
#[test]
#[should_panic(expected = "replayed final vote belongs to another interpretation domain")]
fn mismatched_domain_restart_fails_closed() {
    deterministic::Runner::default().start(|context| async move {
        let f = ed25519::fixture(&mut TestRng::new(6), NS, 6);
        let mut voter = state(context, f.schemes[0].clone(), 1);
        let mut s = subject(1, Digest::from([3; 32]));
        s.domain = Digest::from([99; 32]);
        let vote = commonware_consensus::simplex::extension::certificate::Finalize::new(
            Vote::sign(&f.schemes[0], s).unwrap(),
        )
        .unwrap();
        voter.replay(&ArtifactWith::Finalize(vote));
    });
}

#[test]
#[should_panic(expected = "floor belongs to another interpretation domain")]
fn mismatched_floor_domain_fails_closed() {
    deterministic::Runner::default().start(|context| async move {
        let f = ed25519::fixture(&mut TestRng::new(7), NS, 6);
        let mut voter = state(context, f.schemes[0].clone(), 1);
        let mut foreign = subject(1, Digest::from([3; 32]));
        foreign.domain = Digest::from([99; 32]);
        voter.set_floor(FloorWith::Finalized(certificate(&f, foreign)));
    });
}

#[path = "extension_voter_state/recovery.rs"]
mod recovery;

#[path = "extension_voter_state/recovered.rs"]
mod recovered;

#[path = "extension_voter_state/planning.rs"]
mod planning;
