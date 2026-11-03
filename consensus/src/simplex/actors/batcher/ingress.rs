use crate::{
    Viewable,
    simplex::{
        phase2::{Mode, Plain},
        types::{Proposal, VoteWith},
    },
    types::{Participant, View},
};
use commonware_actor::mailbox::{Overflow, Policy, Sender};
use commonware_cryptography::{Digest, certificate::Scheme};
use std::collections::VecDeque;
use tracing::Span;

/// Messages sent to the [super::actor::ActorWith].
pub enum Message<S: Scheme, D: Digest, M: Mode<S, D> = Plain> {
    /// View update with leader info.
    Update {
        span: Span,
        current: View,
        leader: Participant,
        finalized: View,
        forwardable_proposal: Option<Proposal<D>>,
    },
    /// A durable locally constructed vote for certificate assembly.
    Constructed(VoteWith<S, D, M>),
}

impl<S: Scheme, D: Digest, M: Mode<S, D>> Message<S, D, M> {
    /// Returns the message view used for pruning and span attribution.
    pub(crate) fn view(&self) -> View {
        match self {
            Self::Update { current, .. } => *current,
            Self::Constructed(vote) => vote.view(),
        }
    }

    /// Returns the operation name of this message.
    pub(crate) const fn name(&self) -> &'static str {
        match self {
            Self::Update { .. } => "update",
            Self::Constructed(_) => "constructed",
        }
    }

    // Return whether the retained update makes a constructed vote stale.
    fn prunes(current: View, finalized: View, vote: &VoteWith<S, D, M>) -> bool {
        let view = vote.view();
        match vote {
            // Notarize and nullify votes are only useful for the current view
            VoteWith::Notarize(_) | VoteWith::Nullify(_) => view < current || view <= finalized,
            // Finalize votes are useful in any view that isn't yet finalized
            VoteWith::Finalize(_) => view <= finalized,
        }
    }

    // Return whether two votes would produce the same retained actor action.
    fn similar(a: &VoteWith<S, D, M>, b: &VoteWith<S, D, M>) -> bool {
        if M::RETAIN_INTERPRETATION {
            // Different reports or final interpretations are different actions.
            // The receiving actor must observe them rather than silently erase one.
            return a == b;
        }
        a.view() == b.view()
            && matches!(
                (a, b),
                (VoteWith::Notarize(_), VoteWith::Notarize(_))
                    | (VoteWith::Nullify(_), VoteWith::Nullify(_))
                    | (VoteWith::Finalize(_), VoteWith::Finalize(_))
            )
    }
}

/// Pending batcher messages retained after the mailbox fills.
pub struct Pending<S: Scheme, D: Digest, M: Mode<S, D> = Plain> {
    update: Option<Message<S, D, M>>,
    constructed: VecDeque<VoteWith<S, D, M>>,
}

impl<S: Scheme, D: Digest, M: Mode<S, D>> Default for Pending<S, D, M> {
    fn default() -> Self {
        Self {
            update: None,
            constructed: VecDeque::new(),
        }
    }
}

impl<S: Scheme, D: Digest, M: Mode<S, D>> Overflow<Message<S, D, M>> for Pending<S, D, M> {
    fn is_empty(&self) -> bool {
        self.update.is_none() && self.constructed.is_empty()
    }

    fn drain<F>(&mut self, mut push: F)
    where
        F: FnMut(Message<S, D, M>) -> Option<Message<S, D, M>>,
    {
        if let Some(update) = self.update.take()
            && let Some(update) = push(update)
        {
            self.update = Some(update);
            return;
        }

        while let Some(vote) = self.constructed.pop_front() {
            if let Some(message) = push(Message::Constructed(vote)) {
                let Message::Constructed(vote) = message else {
                    unreachable!("ready returned a different message");
                };
                self.constructed.push_front(vote);
                break;
            }
        }
    }
}

impl<S: Scheme, D: Digest, M: Mode<S, D>> Policy for Message<S, D, M> {
    type Overflow = Pending<S, D, M>;

    fn handle(overflow: &mut Self::Overflow, message: Self) {
        match message {
            update @ Self::Update {
                current: new_current,
                finalized: new_finalized,
                ..
            } => {
                // Ignore the update unless it is newer than the queued update
                if let Some(Self::Update {
                    current: old_current,
                    finalized: old_finalized,
                    ..
                }) = overflow.update.as_ref()
                {
                    let old = (*old_current, *old_finalized);
                    let new = (new_current, new_finalized);
                    if new <= old {
                        return;
                    }
                }
                overflow.update = Some(update);

                // Retain only the newest update and any constructed votes still useful after it
                overflow
                    .constructed
                    .retain(|vote| !Self::prunes(new_current, new_finalized, vote));
            }
            Self::Constructed(new_vote) => {
                // Ignore the constructed vote if it is stale
                if matches!(
                    overflow.update.as_ref(),
                    Some(Self::Update { current: old_current, finalized: old_finalized, .. })
                        if Self::prunes(*old_current, *old_finalized, &new_vote)
                ) {
                    return;
                }

                // Ignore the constructed vote if it is a duplicate
                if overflow
                    .constructed
                    .iter()
                    .any(|old_vote| Self::similar(old_vote, &new_vote))
                {
                    return;
                }
                overflow.constructed.push_back(new_vote);
            }
        }
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

    /// Send an update message.
    pub fn update(
        &mut self,
        span: Span,
        current: View,
        leader: Participant,
        finalized: View,
        forwardable_proposal: Option<Proposal<D>>,
    ) {
        let _ = self.sender.enqueue(Message::Update {
            span,
            current,
            leader,
            finalized,
            forwardable_proposal,
        });
    }

    /// Sends a locally constructed vote after its journal entry is durable.
    pub fn constructed(&mut self, message: VoteWith<S, D, M>) {
        let _ = self.sender.enqueue(Message::Constructed(message));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        simplex::{
            scheme::ed25519,
            types::{Finalize, Notarize, Nullify, Vote},
        },
        types::{Epoch, Round},
    };
    use commonware_actor::mailbox::Policy;
    use commonware_cryptography::{certificate::mocks::Fixture, sha256::Digest as Sha256Digest};
    use commonware_utils::test_rng;
    use std::collections::VecDeque;

    type TestScheme = ed25519::Scheme;
    const EPOCH: Epoch = Epoch::new(1);

    fn scheme() -> TestScheme {
        let mut rng = test_rng();
        let Fixture { schemes, .. } = ed25519::fixture(&mut rng, b"batcher-policy", 5);
        schemes.into_iter().next().expect("missing scheme")
    }

    fn proposal(view: View) -> Proposal<Sha256Digest> {
        Proposal::new(
            Round::new(EPOCH, view),
            view.previous().unwrap_or(View::zero()),
            Sha256Digest::from([view.get() as u8; 32]),
        )
    }

    fn nullify_vote(view: View) -> Vote<TestScheme, Sha256Digest> {
        Vote::Nullify(
            Nullify::sign::<Sha256Digest>(&scheme(), Round::new(EPOCH, view)).expect("nullify"),
        )
    }

    fn notarize_vote(view: View) -> Vote<TestScheme, Sha256Digest> {
        Vote::Notarize(Notarize::sign(&scheme(), proposal(view)).expect("notarize"))
    }

    fn finalize_vote(view: View) -> Vote<TestScheme, Sha256Digest> {
        Vote::Finalize(Finalize::sign(&scheme(), proposal(view)).expect("finalize"))
    }

    fn update(current: View, finalized: View) -> Message<TestScheme, Sha256Digest> {
        Message::Update {
            span: Span::none(),
            current,
            leader: Participant::new(0),
            finalized,
            forwardable_proposal: None,
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
    fn update_prunes_stale_constructed_messages() {
        let mut overflow = Pending::default();
        Message::handle(
            &mut overflow,
            Message::Constructed(nullify_vote(View::new(2))),
        );
        Message::handle(&mut overflow, update(View::new(3), View::new(1)));

        let mut overflow = drain(overflow);
        assert_eq!(overflow.len(), 1);
        assert!(matches!(
            overflow.pop_front(),
            Some(Message::Update {
                current,
                finalized,
                ..
            }) if current == View::new(3) && finalized == View::new(1)
        ));
    }

    #[test]
    fn constructed_message_after_update_is_dropped_when_stale() {
        let mut overflow = Pending::default();
        Message::handle(&mut overflow, update(View::new(3), View::new(1)));
        Message::handle(
            &mut overflow,
            Message::Constructed(nullify_vote(View::new(2))),
        );

        let overflow = drain(overflow);
        assert_eq!(overflow.len(), 1);
    }

    #[test]
    fn update_replaces_older_update_and_keeps_current_constructed_message() {
        let mut overflow = Pending::default();
        Message::handle(&mut overflow, update(View::new(2), View::new(1)));
        Message::handle(
            &mut overflow,
            Message::Constructed(nullify_vote(View::new(3))),
        );
        Message::handle(&mut overflow, update(View::new(3), View::new(1)));

        let mut overflow = drain(overflow);
        assert_eq!(overflow.len(), 2);
        assert!(matches!(
            overflow.pop_front(),
            Some(Message::Update { current, .. }) if current == View::new(3)
        ));
        assert!(matches!(
            overflow.pop_front(),
            Some(Message::Constructed(vote)) if vote.view() == View::new(3)
        ));
    }

    #[test]
    fn stale_update_is_dropped_when_newer_update_is_queued() {
        let mut overflow = Pending::default();
        Message::handle(&mut overflow, update(View::new(5), View::new(4)));
        Message::handle(&mut overflow, update(View::new(4), View::new(3)));

        let mut overflow = drain(overflow);
        assert_eq!(overflow.len(), 1);
        assert!(matches!(
            overflow.pop_front(),
            Some(Message::Update { current, .. }) if current == View::new(5)
        ));
    }

    #[test]
    fn update_replaces_same_current_when_finalized_advances() {
        let mut overflow = Pending::default();
        Message::handle(&mut overflow, update(View::new(5), View::new(3)));
        Message::handle(&mut overflow, update(View::new(5), View::new(4)));

        let mut overflow = drain(overflow);
        assert_eq!(overflow.len(), 1);
        assert!(matches!(
            overflow.pop_front(),
            Some(Message::Update {
                current,
                finalized,
                ..
            }) if current == View::new(5) && finalized == View::new(4)
        ));
    }

    #[test]
    fn duplicate_constructed_message_is_ignored() {
        let mut overflow = Pending::default();
        Message::handle(
            &mut overflow,
            Message::Constructed(nullify_vote(View::new(5))),
        );
        Message::handle(
            &mut overflow,
            Message::Constructed(nullify_vote(View::new(5))),
        );

        let mut overflow = drain(overflow);
        assert_eq!(overflow.len(), 1);
        assert!(matches!(
            overflow.pop_front(),
            Some(Message::Constructed(vote))
                if matches!(vote, Vote::Nullify(_)) && vote.view() == View::new(5)
        ));
    }

    #[test]
    fn lower_current_update_is_dropped_without_merging_finalized() {
        let mut overflow = Pending::default();
        Message::handle(&mut overflow, update(View::new(5), View::zero()));
        Message::handle(
            &mut overflow,
            Message::Constructed(finalize_vote(View::new(3))),
        );
        Message::handle(&mut overflow, update(View::new(4), View::new(4)));

        let mut overflow = drain(overflow);
        assert_eq!(overflow.len(), 2);
        assert!(matches!(
            overflow.pop_front(),
            Some(Message::Update {
                current,
                finalized,
                ..
            }) if current == View::new(5) && finalized == View::zero()
        ));
        assert!(matches!(
            overflow.pop_front(),
            Some(Message::Constructed(vote))
                if matches!(vote, Vote::Finalize(_)) && vote.view() == View::new(3)
        ));
    }

    #[test]
    fn update_keeps_constructed_finalization_above_finalized() {
        let mut overflow = Pending::default();
        Message::handle(
            &mut overflow,
            Message::Constructed(finalize_vote(View::new(4))),
        );
        Message::handle(&mut overflow, update(View::new(5), View::new(3)));

        let mut overflow = drain(overflow);
        assert_eq!(overflow.len(), 2);
        assert!(matches!(
            overflow.pop_front(),
            Some(Message::Update { current, .. }) if current == View::new(5)
        ));
        assert!(matches!(
            overflow.pop_front(),
            Some(Message::Constructed(vote))
                if matches!(vote, Vote::Finalize(_)) && vote.view() == View::new(4)
        ));
    }

    #[test]
    fn constructed_finalizations_remain_in_arrival_order_after_update() {
        let mut overflow = Pending::default();
        Message::handle(
            &mut overflow,
            Message::Constructed(finalize_vote(View::new(4))),
        );
        Message::handle(
            &mut overflow,
            Message::Constructed(finalize_vote(View::new(2))),
        );
        Message::handle(&mut overflow, update(View::new(3), View::new(1)));

        let mut overflow = drain(overflow);
        assert_eq!(overflow.len(), 3);
        assert!(matches!(
            overflow.pop_front(),
            Some(Message::Update { current, .. }) if current == View::new(3)
        ));
        assert!(matches!(
            overflow.pop_front(),
            Some(Message::Constructed(vote))
                if matches!(vote, Vote::Finalize(_)) && vote.view() == View::new(4)
        ));
        assert!(matches!(
            overflow.pop_front(),
            Some(Message::Constructed(vote))
                if matches!(vote, Vote::Finalize(_)) && vote.view() == View::new(2)
        ));
    }

    #[test]
    fn update_prunes_constructed_notarization_below_current() {
        let mut overflow = Pending::default();
        Message::handle(
            &mut overflow,
            Message::Constructed(notarize_vote(View::new(4))),
        );
        Message::handle(&mut overflow, update(View::new(5), View::new(3)));

        let mut overflow = drain(overflow);
        assert_eq!(overflow.len(), 1);
        assert!(matches!(
            overflow.pop_front(),
            Some(Message::Update { current, .. }) if current == View::new(5)
        ));
    }
}

#[cfg(test)]
mod extension_tests {
    use super::*;
    use crate::{
        simplex::{
            extension::{
                certificate::Finalize,
                report::Notarize,
                vote::{Statement, Vote},
            },
            phase2::Extended,
            scheme::ed25519,
            types::Notarize as BaseNotarize,
        },
        types::{Epoch, Round},
    };
    use bytes::Bytes;
    use commonware_cryptography::sha256::Digest as Sha256;
    use commonware_utils::TestRng;

    #[test]
    fn mailbox_overflow_retains_exact_extended_votes_and_prunes_by_native_view() {
        let f = ed25519::fixture(
            &mut TestRng::new(49),
            b"_COMMONWARE_CONSENSUS_INGRESS_EXTENSION_TEST",
            6,
        );
        let round = Round::new(Epoch::new(1), View::new(2));
        let proposal = Proposal::new(round, View::new(1), Sha256::from([1; 32]));
        type Msg = Message<ed25519::Scheme, Sha256, Extended>;
        let mut pending = Pending::default();
        for report in [b"first".as_slice(), b"different", b"first"] {
            let vote = Notarize::new(
                BaseNotarize::sign(&f.schemes[0], proposal.clone()).unwrap(),
                Some(Bytes::copy_from_slice(report)),
            )
            .unwrap();
            Msg::handle(&mut pending, Msg::Constructed(VoteWith::Notarize(vote)));
        }
        for extension in [4, 5, 4] {
            let statement = Statement {
                proposal: proposal.clone(),
                domain: Sha256::from([2; 32]),
                ballot: round,
                parent: Sha256::from([3; 32]),
                extension: Sha256::from([extension; 32]),
            };
            let vote = Finalize::new(Vote::sign(&f.schemes[0], statement).unwrap()).unwrap();
            Msg::handle(&mut pending, Msg::Constructed(VoteWith::Finalize(vote)));
        }
        assert_eq!(pending.constructed.len(), 4); // exact retransmits coalesce only
        let before = pending.constructed.iter().cloned().collect::<Vec<_>>();
        pending.drain(Some); // mailbox remains full: preserve bytes and order
        assert_eq!(
            pending.constructed.iter().cloned().collect::<Vec<_>>(),
            before
        );
        Msg::handle(
            &mut pending,
            Msg::Update {
                span: Span::none(),
                current: View::new(3),
                leader: Participant::new(1),
                finalized: View::new(1),
                forwardable_proposal: None,
            },
        );
        assert_eq!(pending.constructed.len(), 2); // old notarizes pruned, finals retained
        let mut delivered = Vec::new();
        pending.drain(|message| {
            delivered.push(message);
            None
        });
        assert!(pending.is_empty());
        assert!(matches!(delivered.first(), Some(Msg::Update { .. })));
        let values = delivered
            .into_iter()
            .filter_map(|message| match message {
                Msg::Constructed(VoteWith::Finalize(v)) => Some(v.vote().statement.extension),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(values, vec![Sha256::from([4; 32]), Sha256::from([5; 32])]);
    }
}
