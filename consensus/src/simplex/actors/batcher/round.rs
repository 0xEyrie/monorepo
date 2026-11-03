use super::{
    VerifierWith,
    verifier::{Batch, ProposalState},
};
use crate::{
    Reporter,
    simplex::{
        actors::span::ViewSpan,
        phase2::{Plain, aggregation::Aggregation},
        scheme::Scheme,
        types::{
            ActivityWith, CertificateWith, ConflictingFinalizeWith, ConflictingNotarize, Kind,
            NullifyFinalizeWith, ObservedVote, Outcome, Proposal, VoteTrackerWith, VoteWith,
        },
    },
    types::{Attributable, Participant, Round as Rnd},
};
use commonware_cryptography::Digest;
use commonware_p2p::Blocker;
use commonware_parallel::Strategy;
use commonware_utils::{N3f1, ordered::Quorum};
use rand_core::CryptoRng;
use std::sync::Arc;
use tracing::Span;

/// Stock per-view state with native vote and certificate representations.
pub type Round<S, B, D, R> = RoundWith<S, B, D, R, Plain>;

/// Per-view state for mode-specific vote accumulation and certificate tracking.
pub struct RoundWith<
    S: Scheme<D>,
    B: Blocker<PublicKey = S::PublicKey>,
    D: Digest,
    R: Reporter<Activity = ActivityWith<S, D, M>>,
    M: Aggregation<S, D>,
> {
    blocker: B,
    reporter: R,
    /// The verifier attempts to recover notarizations and finalizations only
    /// from votes for one proposal. It initially filters to the first proposal
    /// observed from the known leader. Independently authenticated proposal
    /// evidence is authoritative and switches the filter.
    verifier: VerifierWith<S, D, M>,
    /// At most one vote of each kind per signer.
    ///
    /// Includes locally constructed votes and network votes that may not be
    /// verified. Used for duplicate detection, conflict reporting, and
    /// proposal-switch recovery.
    votes: VoteTrackerWith<S, D, M>,

    /// Whether we've already sent the selected proposal to the voter.
    proposal_sent: bool,

    /// Root span of the view, shared with the voter's round.
    ///
    /// Pending until the voter announces the view via an update.
    span: ViewSpan,
}

impl<
    S: Scheme<D>,
    B: Blocker<PublicKey = S::PublicKey>,
    D: Digest,
    R: Reporter<Activity = ActivityWith<S, D, M>>,
    M: Aggregation<S, D>,
> RoundWith<S, B, D, R, M>
{
    pub fn new(
        round: Rnd,
        scheme: Arc<S>,
        blocker: B,
        reporter: R,
        track_historical_votes: bool,
    ) -> Self {
        let quorum = scheme.participants().quorum::<N3f1>();
        let len = scheme.participants().len();
        Self {
            blocker,
            reporter,
            verifier: VerifierWith::new(round, scheme, quorum),

            votes: VoteTrackerWith::new(len, track_historical_votes),

            proposal_sent: false,

            span: ViewSpan::new(),
        }
    }

    /// Returns the root span of the view.
    pub fn span(&self) -> Span {
        self.span.get()
    }

    /// Adopts the root span of the view from the voter.
    pub fn set_span(&mut self, span: Span) {
        self.span.adopt(span);
    }

    /// Closes the view's root span once the view is decided.
    ///
    /// The round is retained until it is no longer interesting, but its work no
    /// longer anchors a trace.
    pub fn close_span(&mut self) {
        self.span.close();
    }

    /// Returns true if we already have a certificate of `kind` for this view.
    pub(crate) fn has_certificate(&self, kind: Kind) -> bool {
        self.verifier.has_certificate(kind)
    }

    /// Records a verified certificate.
    ///
    /// Completes its verifier phase and applies the configured vote retention
    /// policy. A notarization or finalization also establishes authoritative
    /// proposal evidence. Returns `true` when a notarization selects a new proposal,
    /// making buffered finalize votes eligible for processing.
    pub fn record_certificate(&mut self, certificate: &CertificateWith<S, D, M>) -> bool {
        let process_votes = match certificate {
            CertificateWith::Notarization(notarization) => {
                self.set_authoritative_proposal(&notarization.proposal)
            }
            CertificateWith::Finalization(finalization) => {
                // A finalization may replace the leader-selected proposal, but its
                // certificate makes reprocessing buffered finalize votes unnecessary.
                self.verifier.set_proposal(ProposalState::Certificate(
                    M::finalization_proposal(finalization).clone(),
                ));
                false
            }
            CertificateWith::Nullification(_) => false,
        };
        self.verifier.record_certificate(certificate.kind());
        self.release_votes(certificate.kind());
        process_votes
    }

    /// Applies the configured retention policy to a certified vote phase.
    fn release_votes(&mut self, kind: Kind) {
        match kind {
            Kind::Notarization => {
                let proposal = self
                    .verifier
                    .proposal()
                    .expect("notarization must establish a proposal");
                self.votes.release_notarizes(proposal);
            }
            Kind::Nullification => self.votes.release_nullifies(),
            Kind::Finalization => {
                let proposal = self
                    .verifier
                    .proposal()
                    .expect("finalization must establish a proposal");
                self.votes.release_finalizes(proposal);
            }
        }
    }

    /// Records and reports a vote after source-specific admission checks.
    ///
    /// Retained votes are forwarded to the verifier for certificate assembly.
    /// Compacted phases preserve duplicate suppression and proposal forwarding
    /// without recreating their released vote maps.
    pub(super) fn accept_vote(&mut self, message: VoteWith<S, D, M>, constructed: bool) -> Outcome {
        if constructed && let VoteWith::Finalize(finalize) = &message {
            // The voter only constructs a finalize after independently
            // authenticating the proposal.
            self.set_authoritative_proposal(M::finalize_proposal(finalize));
        }

        let retained = match self.votes.record(&message, self.verifier.proposal()) {
            Outcome::Added { retained } => retained,
            Outcome::Duplicate { retained } => {
                if constructed && retained {
                    // Nullify is reconstructed for each retry. Notarize and finalize
                    // are one-shot local actions, so constructing either twice is a bug.
                    match &message {
                        VoteWith::Notarize(_) => panic!("duplicate notarize"),
                        VoteWith::Nullify(_) => {}
                        VoteWith::Finalize(_) => panic!("duplicate finalize"),
                    }
                }
                return Outcome::Duplicate { retained };
            }
            Outcome::Conflicting => {
                assert!(!constructed, "conflicting constructed vote");
                return Outcome::Conflicting;
            }
        };

        // Retained votes are signer-unique and contribute to certificate
        // assembly. Compacted phases preserve only signer facts, so new activity
        // is reported without forwarding the full vote to the verifier.
        let verifier_message = retained.then(|| message.clone());
        let activity = match message {
            VoteWith::Notarize(notarize) => ActivityWith::Notarize(notarize),
            VoteWith::Nullify(nullify) => ActivityWith::Nullify(nullify),
            VoteWith::Finalize(finalize) => ActivityWith::Finalize(finalize),
        };
        self.reporter.report(activity);
        if let Some(message) = verifier_message {
            self.verifier.add(message, constructed);
        }
        Outcome::Added { retained }
    }

    /// Makes an independently authenticated proposal authoritative, restoring
    /// finalize votes filtered by a conflicting leader proposal.
    ///
    /// Returns whether the selected proposal changed.
    fn set_authoritative_proposal(&mut self, proposal: &Proposal<D>) -> bool {
        let update = self
            .verifier
            .set_proposal(ProposalState::Certificate(proposal.clone()));
        if update.replaced {
            // Matching tracked finalizes are unverified network votes: the conflicting
            // leader proposal filtered them, while constructed finalizes establish the
            // proposal before entering the tracker.
            for finalize in self
                .votes
                .iter_finalizes()
                .filter(|finalize| M::finalize_proposal(finalize) == proposal)
            {
                self.verifier
                    .add(VoteWith::Finalize(finalize.clone()), false);
            }
        }
        update.changed
    }

    /// Adds a vote from the network to this round's verifier.
    pub fn add_network(&mut self, sender: S::PublicKey, message: VoteWith<S, D, M>) -> bool {
        // Check if sender is a participant
        let Some(index) = self.verifier.participants().index(&sender) else {
            commonware_p2p::block!(self.blocker, sender, "unknown participant");
            return false;
        };

        // Attempt to reserve
        match message {
            VoteWith::Notarize(notarize) => {
                // Verify sender is signer
                if index != notarize.signer() {
                    commonware_p2p::block!(self.blocker, sender, "notarize signer mismatch");
                    return false;
                }

                // Try to reserve
                match self.votes.notarize(index) {
                    Some(previous) => {
                        if M::notarize(previous).proposal != M::notarize(&notarize).proposal {
                            let activity = ConflictingNotarize::new(
                                M::notarize(previous).clone(),
                                M::into_notarize(notarize),
                            );
                            self.reporter
                                .report(ActivityWith::ConflictingNotarize(activity));
                            commonware_p2p::block!(self.blocker, sender, "conflicting notarize");
                        } else if M::notarize(previous) != M::notarize(&notarize) {
                            commonware_p2p::block!(self.blocker, sender, "invalid signature");
                        }
                        false
                    }
                    None => match self.accept_vote(VoteWith::Notarize(notarize), false) {
                        Outcome::Added { .. } => true,
                        Outcome::Duplicate { .. } => false,
                        Outcome::Conflicting => {
                            commonware_p2p::block!(self.blocker, sender, "conflicting notarize");
                            false
                        }
                    },
                }
            }
            VoteWith::Nullify(nullify) => {
                // Verify sender is signer
                if index != nullify.signer() {
                    commonware_p2p::block!(self.blocker, sender, "nullify signer mismatch");
                    return false;
                }

                // Check if finalized
                if let Some(previous) = self.votes.saw_finalize(index) {
                    if let ObservedVote::Retained(previous) = previous {
                        let activity =
                            NullifyFinalizeWith::<S, D, M>::new(nullify, previous.clone());
                        self.reporter
                            .report(ActivityWith::NullifyFinalize(activity));
                    }
                    commonware_p2p::block!(self.blocker, sender, "nullify after finalize");
                    return false;
                }

                // Try to reserve
                match self.votes.nullify(index) {
                    Some(previous) => {
                        if previous != &nullify {
                            commonware_p2p::block!(self.blocker, sender, "conflicting nullify");
                        }
                        false
                    }
                    None => match self.accept_vote(VoteWith::Nullify(nullify), false) {
                        Outcome::Added { .. } => true,
                        Outcome::Duplicate { .. } => false,
                        Outcome::Conflicting => {
                            unreachable!("nullify votes do not carry proposals")
                        }
                    },
                }
            }
            VoteWith::Finalize(finalize) => {
                // Verify sender is signer
                if index != finalize.signer() {
                    commonware_p2p::block!(self.blocker, sender, "finalize signer mismatch");
                    return false;
                }

                // Check if nullified
                if let Some(previous) = self.votes.saw_nullify(index) {
                    if let ObservedVote::Retained(previous) = previous {
                        let activity =
                            NullifyFinalizeWith::<S, D, M>::new(previous.clone(), finalize);
                        self.reporter
                            .report(ActivityWith::NullifyFinalize(activity));
                    }
                    commonware_p2p::block!(self.blocker, sender, "finalize after nullify");
                    return false;
                }

                // Try to reserve
                match self.votes.finalize(index) {
                    Some(previous) => {
                        if M::conflicting_finalize_subjects(previous, &finalize) {
                            let activity =
                                ConflictingFinalizeWith::<S, D, M>::new(previous.clone(), finalize);
                            self.reporter
                                .report(ActivityWith::ConflictingFinalize(activity));
                            commonware_p2p::block!(self.blocker, sender, "conflicting finalize");
                        } else if previous != &finalize {
                            commonware_p2p::block!(self.blocker, sender, "invalid signature");
                        }
                        false
                    }
                    None => match self.accept_vote(VoteWith::Finalize(finalize), false) {
                        Outcome::Added { .. } => true,
                        Outcome::Duplicate { .. } => false,
                        Outcome::Conflicting => {
                            commonware_p2p::block!(self.blocker, sender, "conflicting finalize");
                            false
                        }
                    },
                }
            }
        }
    }

    /// Retained first votes in participant order. Entries are source-admitted,
    /// not necessarily signature-verified. The consumer must authenticate the
    /// original report, context and policy independently before counting support.
    pub fn notarizes(&self) -> impl Iterator<Item = &M::Notarize> {
        self.votes.iter_notarizes()
    }

    /// Sets the leader for this view. If the leader's notarize has already
    /// been received, this will also set the leader's proposal (filtering out
    /// votes for other proposals).
    pub fn set_leader(&mut self, leader: Participant) {
        // Certification drops the verifier's buffered notarizes, so read an
        // uncertified leader vote from the tracker.
        self.verifier
            .set_leader(leader, self.votes.notarize(leader).map(M::notarize));
    }

    /// Returns the proposal to forward to the voter, marking it sent (at most
    /// once per round). Returns `None` if we already forwarded one, the
    /// proposal is unknown, or the known leader is us.
    pub fn try_forward_proposal(&mut self, me: Participant) -> Option<Proposal<D>> {
        if self.proposal_sent {
            return None;
        }
        let proposal = self.verifier.proposal()?;
        if self.verifier.leader() == Some(me) {
            return None;
        }
        let proposal = proposal.clone();
        self.proposal_sent = true;
        Some(proposal)
    }

    /// Attempts to construct a certificate from the first ready kind (notarizes,
    /// nullifies, then finalizes), recording it before returning it to the caller.
    ///
    /// Once polled, construction moves the buffered votes into the worker. Do not
    /// cancel unless the round will also be discarded.
    pub async fn try_construct<E: CryptoRng + Send>(
        &mut self,
        rng: &mut E,
        strategy: &impl Strategy,
    ) -> Option<Batch<CertificateWith<S, D, M>>> {
        let result = if let Some(result) = self
            .verifier
            .try_construct_notarization(rng, strategy)
            .await
        {
            result
        } else if let Some(result) = self
            .verifier
            .try_construct_nullification(rng, strategy)
            .await
        {
            result
        } else {
            self.verifier
                .try_construct_finalization(rng, strategy)
                .await?
        };
        if let Some(certificate) = &result.certificate {
            self.record_certificate(certificate);
        }
        Some(result)
    }

    /// Returns whether `signer` has a nullify vote.
    pub fn has_nullify(&self, signer: Participant) -> bool {
        self.votes.has_nullify(signer)
    }

    /// Returns whether `participant` has not voted for `proposal` locally.
    ///
    /// Uses tracker membership, including compact state, because verification stops
    /// after the first quorum. Matching votes received later still inform forwarding.
    ///
    /// Both notarize and finalize votes are checked: a participant who sent
    /// either for the same proposal already has the block and does not need
    /// it forwarded. Votes for a conflicting proposal are treated as missing
    /// because those peers still need the winning block forwarded.
    pub fn is_missing_voter(&self, proposal: &Proposal<D>, participant: Participant) -> bool {
        if self.votes.has_notarize_for(participant, proposal) {
            return false;
        }

        !self.votes.has_finalize_for(participant, proposal)
    }

    /// Returns participant indices for which [`Self::is_missing_voter`] is true.
    pub fn missing_voters(&self, proposal: &Proposal<D>) -> Vec<Participant> {
        (0..self.verifier.participants().len())
            .map(Participant::from_usize)
            .filter(|&p| self.is_missing_voter(proposal, p))
            .collect()
    }
}
