//! Actual voter hook controls with a Plain-shaped test mode, real n7 signatures
//! and an attached journal. These tests do not activate the M1 owner/profile or
//! establish joint-reservation durability, recovery or seven-node support.
use super::*;
use crate::simplex::phase2::companion_probe::{self, Probe};

#[derive(Clone)]
struct Ready(Proposal<D>);
impl<const ACCEPT: bool> Participation<S, D, Probe<ACCEPT>> for Ready {
    fn notarize(&mut self, vote: Notarize<S, D>) -> Notarize<S, D> {
        vote
    }
    fn final_subject(&mut self, proposal: &Proposal<D>) -> Option<()> {
        (proposal == &self.0).then_some(())
    }
    fn accepts_finalization(&mut self, _: &crate::simplex::types::Finalization<S, D>) -> bool {
        // This fixture never ingests final certificates; fail closed.
        false
    }
    fn accepts_replay(&mut self, artifact: &ArtifactWith<S, D, Probe<ACCEPT>>) -> bool {
        match artifact {
            ArtifactWith::Notarization(certificate) => certificate.proposal == self.0,
            ArtifactWith::Certification(round, true) => *round == self.0.round,
            ArtifactWith::Finalize(vote) => vote.proposal == self.0,
            _ => false,
        }
    }
    fn prune(&mut self, _: View) {}
}

#[derive(Clone)]
struct Sink<const ACCEPT: bool>;
impl<const ACCEPT: bool> Reporter for Sink<ACCEPT> {
    type Activity = ActivityWith<S, D, Probe<ACCEPT>>;
    fn report(&mut self, _: Self::Activity) -> Feedback {
        Feedback::Ok
    }
}

fn exercise<const ACCEPT: bool>(certified: bool, release_allowed: bool) {
    deterministic::Runner::timed(Duration::from_secs(20)).start(move |mut context| async move {
        let fixture = ed25519::fixture(
            &mut context,
            b"_COMMONWARE_CONSENSUS_FALLIBLE_FINAL_TEST",
            7,
        );
        let scheme = fixture.schemes[0].clone();
        let cache = CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(10));
        let (mut actor, _input) = ActorWith::new_with(
            context.child("voter"),
            Config {
                scheme: scheme.clone(),
                elector: RoundRobin::<Sha256>::default().build(scheme.participants()),
                blocker: NoopBlocker::default(),
                automaton: App::default(),
                relay: App::default(),
                reporter: Sink::<ACCEPT>,
                partition: "fallible-final".into(),
                epoch: Epoch::new(1),
                floor: FloorWith::Genesis(D::from([0; 32])),
                mailbox_size: NZUsize!(8),
                leader_timeout: Duration::from_secs(10),
                certification_timeout: Duration::from_secs(10),
                timeout_retry: Duration::from_secs(10),
                skip_budget: 7,
                view_retention: ViewDelta::new(10),
                replay_buffer: NZUsize!(4096),
                write_buffer: NZUsize!(4096),
                page_cache: cache.clone(),
            },
            (),
            Ready(proposal(1)),
        );
        actor.state.set_genesis(D::from([0; 32]));
        let certificate = notarization(&fixture, 1);
        assert!(certificate.verify(&mut context, &fixture.verifier, &Sequential));
        actor.state.add_notarization(certificate.clone());
        if certified {
            // Restore certification without advancing the pacemaker. Calling
            // State::certified here would move to view 2 and invalidate a
            // same-view Nullify assertion for an unrelated reason.
            actor
                .state
                .replay(&ArtifactWith::Certification(proposal(1).round, true));
        }
        actor.journal = Some(
            Journal::init(
                actor.context.child("journal"),
                JConfig {
                    partition: "fallible-final".into(),
                    compression: None,
                    codec_config: scheme.certificate_codec_config(),
                    page_cache: cache,
                    write_buffer: NZUsize!(4096),
                },
            )
            .await
            .unwrap(),
        );
        actor = actor
            .append_journal(ArtifactWith::Notarization(certificate))
            .await;
        if certified {
            actor = actor
                .append_journal(ArtifactWith::Certification(proposal(1).round, true))
                .await;
        }
        actor = actor.sync_journal().await;
        assert_eq!(actor.state.current_view(), View::new(1));
        assert!(actor.dirty_section.is_none());
        companion_probe::reset_voting();
        companion_probe::allow_release(release_allowed);

        let (mut actor, vote) = actor.prepare_finalize(View::new(1)).await;
        assert_eq!(actor.state.current_view(), View::new(1));
        if !certified || !ACCEPT {
            assert!(vote.is_none());
            assert_eq!(companion_probe::staged(), usize::from(certified));
            assert_eq!(companion_probe::released(), 0);
            assert!(actor.dirty_section.is_none());
            assert!(!actor.state.allows_reserved_finalize(View::new(1), &()));
            assert!(
                actor
                    .state
                    .construct_nullify(View::new(1), TimeoutReason::CertificationTimeout)
                    .is_some(),
                "a refused extension must leave the current native choice pending"
            );
        } else if !release_allowed {
            assert!(vote.is_none());
            assert_eq!(companion_probe::staged(), 1);
            assert_eq!(companion_probe::released(), 1);
            assert!(actor.dirty_section.is_none());
            assert!(actor.state.allows_reserved_finalize(View::new(1), &()));
            assert!(
                actor
                    .state
                    .construct_nullify(View::new(1), TimeoutReason::CertificationTimeout)
                    .is_none(),
                "the accepted final choice is retained when its current owner refuses release"
            );
            // Exercise the retained-choice release seam directly. This does
            // not journal or publish a vote, and is not a restart/WAL proof.
            companion_probe::allow_release(true);
            let (vote, _) = actor
                .state
                .sign_reserved_finalize(View::new(1), ())
                .unwrap();
            assert_eq!(vote.proposal, proposal(1));
            assert!(vote.verify(&mut context, &fixture.verifier, &Sequential));
            assert_eq!(companion_probe::staged(), 1);
            assert_eq!(companion_probe::released(), 2);
        } else {
            let vote = vote.unwrap();
            assert_eq!(vote.proposal, proposal(1));
            assert!(vote.verify(&mut context, &fixture.verifier, &Sequential));
            assert_eq!(companion_probe::staged(), 1);
            assert_eq!(companion_probe::released(), 1);
            assert_eq!(actor.dirty_section, Some(View::new(1)));
            actor = actor.sync_journal().await;
            assert!(actor.dirty_section.is_none());
            assert!(
                actor
                    .state
                    .construct_nullify(View::new(1), TimeoutReason::CertificationTimeout)
                    .is_none()
            );
            let (actor, duplicate) = actor.prepare_finalize(View::new(1)).await;
            assert!(duplicate.is_none());
            assert_eq!(companion_probe::staged(), 1);
            assert_eq!(companion_probe::released(), 1);
            drop(actor);
        }
        companion_probe::reset_voting();
    });
}

#[test]
fn refused_final_reservation_leaves_same_view_nullify_eligible() {
    exercise::<false>(true, true);
}

#[test]
fn accepted_final_reservation_releases_a_real_vote_and_journals_it() {
    exercise::<true>(true, true);
}

#[test]
fn uncertified_native_proposal_never_calls_extension_reservation() {
    exercise::<true>(false, true);
}

#[test]
fn current_owner_can_refuse_release_after_the_native_choice_is_staged() {
    exercise::<true>(true, false);
}
