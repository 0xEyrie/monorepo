use crate::{
    Epochable, Viewable,
    simplex::{
        metrics::TimeoutReason,
        phase2::{Mode, Plain},
        types::{CertificateWith, Proposal},
    },
    types::{Round as Rnd, View},
};
use commonware_actor::mailbox::{Overflow, Policy, Sender};
use commonware_cryptography::{Digest, certificate::Scheme};
use commonware_runtime::telemetry::traces::TracedExt as _;
use commonware_utils::channel::oneshot;
use std::collections::VecDeque;
use tracing::{Span, info_span};

/// Messages sent to the [super::actor::ActorWith].
pub enum Message<S: Scheme, D: Digest, M: Mode<S, D> = Plain> {
    /// Local coordinator query; it never authorizes a vote or advances the view.
    #[cfg_attr(
        commonware_stability_BETA,
        expect(dead_code, reason = "recovery coordination is an ALPHA extension API")
    )]
    RecoveryQuery {
        span: Span,
        query: M::RecoveryQuery,
        reply: oneshot::Sender<Option<M::RecoveryRequest>>,
    },
    /// Read-only native eligibility check before application material retention.
    #[cfg_attr(
        commonware_stability_BETA,
        expect(dead_code, reason = "recovery admission is an ALPHA extension API")
    )]
    RecoveryAdmission {
        span: Span,
        request: M::RecoveryRequest,
        reply: oneshot::Sender<bool>,
    },
    /// Signed recovery request; native authentication and sync precede any reply.
    #[cfg_attr(
        commonware_stability_BETA,
        expect(dead_code, reason = "recovery requests are an ALPHA extension API")
    )]
    Recovery {
        span: Span,
        request: M::RecoveryRequest,
        reply: oneshot::Sender<Option<M::RecoveryResponse>>,
    },
    /// Later-ballot parent witness; ACK follows native validation and journal sync.
    #[cfg_attr(
        commonware_stability_BETA,
        expect(
            dead_code,
            reason = "recovered interpretations are an ALPHA extension API"
        )
    )]
    Recovered {
        span: Span,
        certificate: M::Recovered,
        reply: oneshot::Sender<bool>,
    },
    /// Leader's proposal from batcher.
    Proposal {
        /// The span carried with this message.
        span: Span,
        /// The leader's proposal.
        proposal: Proposal<D>,
    },
    /// Signal that the current view should timeout (if not already).
    Timeout {
        /// The span carried with this message.
        span: Span,
        /// The round to timeout.
        round: Rnd,
        /// The reason for the timeout.
        reason: TimeoutReason,
    },
    /// Local evidence became available; the voter must repeat every check.
    #[cfg_attr(
        commonware_stability_BETA,
        expect(dead_code, reason = "local readiness is an ALPHA extension API")
    )]
    InterpretationReady { span: Span, view: View },
    /// Certificate from batcher or resolver.
    Verified {
        /// The span carried with this message.
        span: Span,
        /// The verified certificate.
        certificate: CertificateWith<S, D, M>,
        /// Whether the certificate came from the resolver. When true, the voter
        /// will not send it back to the resolver (to avoid "boomerang").
        from_resolver: bool,
    },
}

impl<S: Scheme, D: Digest, M: Mode<S, D>> Message<S, D, M> {
    /// Returns the message view used for pruning and deduplication.
    pub(crate) fn view(&self) -> View {
        match self {
            Self::RecoveryQuery { query, .. } => M::recovery_query_view(query),
            Self::Recovered { certificate, .. } => certificate.view(),
            Self::Recovery { request, .. } | Self::RecoveryAdmission { request, .. } => {
                M::recovery_view(request)
            }
            Self::InterpretationReady { view, .. } => *view,
            Self::Proposal { proposal, .. } => proposal.view(),
            Self::Timeout { round, .. } => round.view(),
            Self::Verified { certificate, .. } => certificate.view(),
        }
    }

    /// Returns the span carried with this message.
    pub(crate) const fn span(&self) -> &Span {
        match self {
            Self::RecoveryQuery { span, .. }
            | Self::Recovered { span, .. }
            | Self::RecoveryAdmission { span, .. }
            | Self::Recovery { span, .. }
            | Self::InterpretationReady { span, .. }
            | Self::Proposal { span, .. }
            | Self::Timeout { span, .. }
            | Self::Verified { span, .. } => span,
        }
    }

    /// Returns the operation name of this message.
    pub(crate) const fn name(&self) -> &'static str {
        match self {
            Self::RecoveryQuery { .. } => "recovery_query",
            Self::Recovered { .. } => "recovered_interpretation",
            Self::Recovery { .. } => "recovery",
            Self::RecoveryAdmission { .. } => "recovery_admission",
            Self::InterpretationReady { .. } => "interpretation_ready",
            Self::Proposal { .. } => "proposal",
            Self::Timeout { .. } => "timeout",
            Self::Verified { .. } => "verified",
        }
    }
}

/// Pending voter messages retained after the mailbox fills.
pub struct Pending<S: Scheme, D: Digest, M: Mode<S, D> = Plain> {
    finalization: Option<Message<S, D, M>>,
    messages: VecDeque<Message<S, D, M>>,
}

impl<S: Scheme, D: Digest, M: Mode<S, D>> Default for Pending<S, D, M> {
    fn default() -> Self {
        Self {
            finalization: None,
            messages: VecDeque::new(),
        }
    }
}

impl<S: Scheme, D: Digest, M: Mode<S, D>> Overflow<Message<S, D, M>> for Pending<S, D, M> {
    fn is_empty(&self) -> bool {
        self.finalization.is_none() && self.messages.is_empty()
    }

    fn drain<F>(&mut self, mut push: F)
    where
        F: FnMut(Message<S, D, M>) -> Option<Message<S, D, M>>,
    {
        if let Some(finalization) = self.finalization.take()
            && let Some(finalization) = push(finalization)
        {
            self.finalization = Some(finalization);
            return;
        }

        while let Some(message) = self.messages.pop_front() {
            if let Some(message) = push(message) {
                self.messages.push_front(message);
                break;
            }
        }
    }
}

impl<S: Scheme, D: Digest, M: Mode<S, D>> Policy for Message<S, D, M> {
    type Overflow = Pending<S, D, M>;

    fn handle(overflow: &mut Self::Overflow, message: Self) {
        // Recovery requests are retriable and are not accepted until their reply.
        // Bound retained oneshots independently of adversarial view numbers.
        if matches!(
            message,
            Self::RecoveryQuery { .. }
                | Self::RecoveryAdmission { .. }
                | Self::Recovery { .. }
                | Self::Recovered { .. }
        ) && overflow
            .messages
            .iter()
            .filter(|m| {
                matches!(
                    m,
                    Self::RecoveryQuery { .. }
                        | Self::RecoveryAdmission { .. }
                        | Self::Recovery { .. }
                        | Self::Recovered { .. }
                )
            })
            .count()
            >= 16
        {
            return;
        }
        // Ignore the message if there exists a queued finalization
        // with a view greater than or equal to the new view
        let new_view = message.view();
        if !M::RETAIN_INTERPRETATION
            && matches!(
                overflow.finalization.as_ref(),
                Some(Self::Verified { certificate: CertificateWith::Finalization(old_finalized), .. })
                    if old_finalized.view() >= new_view
            )
        {
            return;
        }

        // Retain only the highest-view finalization and any messages with a view greater than the new view
        if !M::RETAIN_INTERPRETATION
            && matches!(
                &message,
                Self::Verified {
                    certificate: CertificateWith::Finalization(_),
                    ..
                }
            )
        {
            overflow
                .messages
                .retain(|old_message| old_message.view() > new_view);
            overflow.finalization = Some(message);
            return;
        }

        // For the same view, LeaderNullify is stronger than Inactivity. A
        // buffered proposal may suppress inactivity, but the leader's explicit
        // refusal must still abandon the view.
        if let Self::Timeout {
            round: new_round,
            reason: new_reason,
            ..
        } = &message
            && let Some(index) = overflow.messages.iter().position(|old_message| {
                matches!(
                    old_message,
                    Self::Timeout { round, .. } if round.view() == new_round.view()
                )
            })
        {
            if *new_reason == TimeoutReason::LeaderNullify
                && matches!(
                    &overflow.messages[index],
                    Self::Timeout {
                        reason: TimeoutReason::Inactivity,
                        ..
                    }
                )
            {
                overflow.messages[index] = message;
            }
            return;
        }

        // Ignore the message if it is a duplicate
        if overflow
            .messages
            .iter()
            .any(|old_message| match (&message, old_message) {
                (
                    Self::InterpretationReady { view: a, .. },
                    Self::InterpretationReady { view: b, .. },
                ) => a == b,
                (
                    Self::Proposal {
                        proposal: new_proposal,
                        ..
                    },
                    Self::Proposal {
                        proposal: old_proposal,
                        ..
                    },
                ) => new_proposal.view() == old_proposal.view(),
                (
                    Self::Verified {
                        certificate: new_certificate,
                        ..
                    },
                    Self::Verified {
                        certificate: old_certificate,
                        ..
                    },
                ) => {
                    if M::RETAIN_INTERPRETATION
                        && let (CertificateWith::Finalization(a), CertificateWith::Finalization(b)) = (new_certificate, old_certificate) {
                        return a == b;
                    }
                    new_certificate.view() == old_certificate.view()
                        && matches!(
                            (new_certificate, old_certificate),
                            (
                                CertificateWith::Notarization(_),
                                CertificateWith::Notarization(_)
                            ) | (
                                CertificateWith::Nullification(_),
                                CertificateWith::Nullification(_)
                            ) | (
                                CertificateWith::Finalization(_),
                                CertificateWith::Finalization(_)
                            )
                        )
                }
                _ => false,
            })
        {
            return;
        }
        overflow.messages.push_back(message);
    }
}

#[derive(Clone)]
pub struct Mailbox<S: Scheme, D: Digest, M: Mode<S, D> = Plain> {
    sender: Sender<Message<S, D, M>>,
}

impl<S: Scheme, D: Digest, M: Mode<S, D>> Mailbox<S, D, M> {
    /// Create a new mailbox.
    pub const fn new(sender: Sender<Message<S, D, M>>) -> Self {
        Self { sender }
    }

    /// Wake local evidence processing without granting finality or voting approval.
    #[commonware_macros::stability(ALPHA)]
    pub fn interpretation_ready(&mut self, view: View) {
        let _ = self.sender.enqueue(Message::InterpretationReady {
            span: info_span!(
                "simplex.voter.mailbox.interpretation_ready",
                view = view.traced()
            ),
            view,
        });
    }

    /// Send a leader's proposal.
    pub fn proposal(&mut self, proposal: Proposal<D>) {
        let _ = self.sender.enqueue(Message::Proposal {
            span: info_span!(
                "simplex.voter.mailbox.proposal",
                epoch = proposal.epoch().traced(),
                view = proposal.view().traced()
            ),
            proposal,
        });
    }

    /// Signal that the given round should timeout (if not already).
    pub fn timeout(&mut self, round: Rnd, reason: TimeoutReason) {
        let _ = self.sender.enqueue(Message::Timeout {
            span: info_span!(
                "simplex.voter.mailbox.timeout",
                epoch = round.epoch().traced(),
                view = round.view().traced(),
                reason = reason.as_str()
            ),
            round,
            reason,
        });
    }

    /// Send a recovered certificate.
    pub fn recovered(&mut self, certificate: CertificateWith<S, D, M>) {
        let _ = self.sender.enqueue(Message::Verified {
            span: info_span!(
                "simplex.voter.mailbox.recovered",
                epoch = certificate.epoch().traced(),
                view = certificate.view().traced(),
                certificate = %certificate.kind()
            ),
            certificate,
            from_resolver: false,
        });
    }

    /// Send a resolved certificate.
    pub fn resolved(&mut self, certificate: CertificateWith<S, D, M>) {
        let _ = self.sender.enqueue(Message::Verified {
            span: info_span!(
                "simplex.voter.mailbox.resolved",
                epoch = certificate.epoch().traced(),
                view = certificate.view().traced(),
                certificate = %certificate.kind()
            ),
            certificate,
            from_resolver: true,
        });
    }
}

commonware_macros::stability_scope!(ALPHA {
impl<S: crate::simplex::scheme::Scheme<D>, D: Digest> Mailbox<S,D,crate::simplex::phase2::Extended> {
    /// Checks native eligibility without mutating recovery state or signing a response.
    pub(crate) fn validate_recovery(&mut self, request: crate::simplex::extension::request::Request<S,D>) -> oneshot::Receiver<bool> {
        let (reply,receiver)=oneshot::channel();
        let _=self.sender.enqueue(Message::RecoveryAdmission {span:info_span!("simplex.voter.recovery_admission",view=request.view().traced()),request,reply});
        receiver
    }
    /// Asks native state to prepare an eligible recovery leader request. This does
    /// not persist a decision; the ordinary recovery request path still must run.
    pub fn prepare_recovery(&mut self, query: crate::simplex::extension::request::Query<S,D>) -> oneshot::Receiver<Option<crate::simplex::extension::request::Request<S,D>>> {
        let (reply,receiver)=oneshot::channel();
        if !query.bounded() { let _=reply.send(None); return receiver; }
        let _=self.sender.enqueue(Message::RecoveryQuery {span:info_span!("simplex.voter.recovery_query",view=query.view().traced()),query,reply});
        receiver
    }
    /// Installs a recovered parent interpretation. True acknowledges durable retention,
    /// never native finality; closure is not an ACK and may be retried.
    pub fn install_recovered(&mut self, certificate: crate::simplex::extension::certificate::Recovered<S,D>) -> oneshot::Receiver<bool> {
        let (reply,receiver)=oneshot::channel();
        let _=self.sender.enqueue(Message::Recovered {span:info_span!("simplex.voter.recovered_interpretation",view=certificate.view().traced()),certificate,reply});
        receiver
    }
    /// Submits a signed native recovery request. Closure or None is not an ACK;
    /// cancellation does not undo a decision already accepted by the voter.
    pub fn recover_extension(&mut self, request: crate::simplex::extension::request::Request<S,D>) -> oneshot::Receiver<Option<crate::simplex::extension::request::Response<S,D>>> {
        let (reply, receiver)=oneshot::channel();
        let _=self.sender.enqueue(Message::Recovery{span:info_span!("simplex.voter.recovery",view=request.view().traced()),request,reply});
        receiver
    }
}
});

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        simplex::{
            scheme::ed25519,
            types::{Certificate, Finalization, Finalize, Nullification, Nullify, Proposal},
        },
        types::{Epoch, Round},
    };
    use commonware_actor::mailbox::Policy;
    use commonware_cryptography::{certificate::mocks::Fixture, sha256::Digest as Sha256Digest};
    use commonware_parallel::Sequential;
    use commonware_utils::{non_empty, test_rng};
    use std::collections::VecDeque;

    type TestScheme = ed25519::Scheme;
    const EPOCH: Epoch = Epoch::new(1);

    fn fixture() -> (Vec<TestScheme>, TestScheme) {
        let mut rng = test_rng();
        let Fixture {
            schemes, verifier, ..
        } = ed25519::fixture(&mut rng, b"voter-policy", 5);
        (schemes, verifier)
    }

    fn proposal(view: View) -> Proposal<Sha256Digest> {
        Proposal::new(
            Round::new(EPOCH, view),
            view.previous().unwrap_or(View::zero()),
            Sha256Digest::from([view.get() as u8; 32]),
        )
    }

    fn nullification(view: View) -> Certificate<TestScheme, Sha256Digest> {
        let (schemes, verifier) = fixture();
        let round = Round::new(EPOCH, view);
        let votes: Vec<_> = schemes
            .iter()
            .map(|scheme| Nullify::sign::<Sha256Digest>(scheme, round).expect("nullify"))
            .collect();
        Certificate::Nullification(
            Nullification::from_nullifies(&verifier, non_empty![@&votes], &Sequential)
                .expect("nullification"),
        )
    }

    fn finalization(view: View) -> Certificate<TestScheme, Sha256Digest> {
        let (schemes, verifier) = fixture();
        let proposal = proposal(view);
        let votes: Vec<_> = schemes
            .iter()
            .map(|scheme| Finalize::sign(scheme, proposal.clone()).expect("finalize"))
            .collect();
        Certificate::Finalization(
            Finalization::from_finalizes(&verifier, non_empty![@&votes], &Sequential)
                .expect("finalization"),
        )
    }

    fn proposal_msg(view: View) -> Message<TestScheme, Sha256Digest> {
        Message::Proposal {
            span: Span::none(),
            proposal: proposal(view),
        }
    }

    fn timeout_msg(view: View, reason: TimeoutReason) -> Message<TestScheme, Sha256Digest> {
        Message::Timeout {
            span: Span::none(),
            round: Round::new(EPOCH, view),
            reason,
        }
    }

    fn verified_msg(
        certificate: Certificate<TestScheme, Sha256Digest>,
        from_resolver: bool,
    ) -> Message<TestScheme, Sha256Digest> {
        Message::Verified {
            span: Span::none(),
            certificate,
            from_resolver,
        }
    }

    fn drain(
        mut overflow: Pending<TestScheme, Sha256Digest>,
    ) -> VecDeque<Message<TestScheme, Sha256Digest>> {
        let mut messages = VecDeque::new();
        Overflow::drain(&mut overflow, |message| {
            messages.push_back(message);
            None
        });
        messages
    }

    #[test]
    fn finalization_prunes_stale_overflow() {
        let mut overflow = Pending::default();
        Message::handle(&mut overflow, proposal_msg(View::new(2)));
        Message::handle(
            &mut overflow,
            timeout_msg(View::new(2), TimeoutReason::LeaderTimeout),
        );
        Message::handle(
            &mut overflow,
            verified_msg(nullification(View::new(2)), false),
        );
        Message::handle(&mut overflow, proposal_msg(View::new(4)));
        Message::handle(
            &mut overflow,
            verified_msg(finalization(View::new(3)), false),
        );

        let mut overflow = drain(overflow);
        assert_eq!(overflow.len(), 2);
        assert!(matches!(
            overflow.pop_front(),
            Some(Message::Verified { certificate: Certificate::Finalization(f), from_resolver: false, .. })
                if f.view() == View::new(3)
        ));
        assert!(matches!(
            overflow.pop_front(),
            Some(Message::Proposal { proposal: p, .. }) if p.view() == View::new(4)
        ));
    }

    #[test]
    fn duplicate_certificate_is_ignored() {
        let mut overflow = Pending::default();
        let certificate = nullification(View::new(5));
        Message::handle(&mut overflow, verified_msg(certificate.clone(), false));
        Message::handle(&mut overflow, verified_msg(certificate, true));

        let mut overflow = drain(overflow);
        assert_eq!(overflow.len(), 1);
        assert!(matches!(
            overflow.pop_front(),
            Some(Message::Verified { certificate: Certificate::Nullification(n), from_resolver: false, .. })
                if n.view() == View::new(5)
        ));
    }

    #[test]
    fn queued_finalization_rejects_covered_messages() {
        let mut overflow = Pending::default();
        Message::handle(
            &mut overflow,
            verified_msg(finalization(View::new(3)), false),
        );

        Message::handle(&mut overflow, proposal_msg(View::new(3)));
        Message::handle(
            &mut overflow,
            timeout_msg(View::new(2), TimeoutReason::LeaderTimeout),
        );
        Message::handle(
            &mut overflow,
            verified_msg(nullification(View::new(2)), false),
        );
        Message::handle(
            &mut overflow,
            verified_msg(finalization(View::new(2)), false),
        );
        Message::handle(&mut overflow, proposal_msg(View::new(4)));

        let mut overflow = drain(overflow);
        assert_eq!(overflow.len(), 2);
        assert!(matches!(
            overflow.pop_front(),
            Some(Message::Verified { certificate: Certificate::Finalization(f), from_resolver: false, .. })
                if f.view() == View::new(3)
        ));
        assert!(matches!(
            overflow.pop_front(),
            Some(Message::Proposal { proposal: p, .. }) if p.view() == View::new(4)
        ));
    }

    #[test]
    fn duplicate_finalization_is_dropped() {
        let mut overflow = Pending::default();
        Message::handle(
            &mut overflow,
            verified_msg(finalization(View::new(3)), false),
        );
        Message::handle(
            &mut overflow,
            verified_msg(finalization(View::new(3)), true),
        );

        let mut overflow = drain(overflow);
        assert_eq!(overflow.len(), 1);
        assert!(matches!(
            overflow.pop_front(),
            Some(Message::Verified { certificate: Certificate::Finalization(f), from_resolver: false, .. })
                if f.view() == View::new(3)
        ));
    }

    #[test]
    fn newer_finalization_replaces_older_pruning_floor() {
        let mut overflow = Pending::default();
        Message::handle(
            &mut overflow,
            verified_msg(finalization(View::new(3)), false),
        );
        Message::handle(&mut overflow, proposal_msg(View::new(4)));
        Message::handle(
            &mut overflow,
            verified_msg(finalization(View::new(5)), false),
        );

        let mut overflow = drain(overflow);
        assert_eq!(overflow.len(), 1);
        assert!(matches!(
            overflow.pop_front(),
            Some(Message::Verified { certificate: Certificate::Finalization(f), from_resolver: false, .. })
                if f.view() == View::new(5)
        ));
    }

    #[test]
    fn duplicate_proposals_and_timeouts_are_deduplicated() {
        let mut overflow = Pending::<TestScheme, Sha256Digest>::default();
        Message::handle(&mut overflow, proposal_msg(View::new(4)));
        Message::handle(&mut overflow, proposal_msg(View::new(4)));
        Message::handle(
            &mut overflow,
            timeout_msg(View::new(4), TimeoutReason::LeaderTimeout),
        );
        Message::handle(
            &mut overflow,
            timeout_msg(View::new(4), TimeoutReason::Inactivity),
        );

        let overflow = drain(overflow);
        assert_eq!(overflow.len(), 2);
    }

    #[test]
    fn leader_nullify_replaces_inactivity_for_same_view() {
        // A leader refusal upgrades an inactivity timeout already in the queue.
        let mut overflow = Pending::<TestScheme, Sha256Digest>::default();
        Message::handle(
            &mut overflow,
            timeout_msg(View::new(4), TimeoutReason::Inactivity),
        );
        Message::handle(
            &mut overflow,
            timeout_msg(View::new(4), TimeoutReason::LeaderNullify),
        );

        let mut overflow = drain(overflow);
        assert!(matches!(
            overflow.pop_front(),
            Some(Message::Timeout {
                round,
                reason: TimeoutReason::LeaderNullify,
                ..
            }) if round.view() == View::new(4)
        ));
        assert!(overflow.is_empty());

        // A later inactivity timeout cannot downgrade a queued leader refusal.
        let mut overflow = Pending::<TestScheme, Sha256Digest>::default();
        Message::handle(
            &mut overflow,
            timeout_msg(View::new(4), TimeoutReason::LeaderNullify),
        );
        Message::handle(
            &mut overflow,
            timeout_msg(View::new(4), TimeoutReason::Inactivity),
        );
        let mut overflow = drain(overflow);
        assert!(matches!(
            overflow.pop_front(),
            Some(Message::Timeout {
                reason: TimeoutReason::LeaderNullify,
                ..
            })
        ));
        assert!(overflow.is_empty());
    }
}
