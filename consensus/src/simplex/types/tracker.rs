//! Per-view signer tracking and phase-specific evidence retention.

use crate::{
    simplex::{
        phase2::{Mode, Plain},
        types::{Nullify, Proposal, VoteWith},
    },
    types::{Attributable, Participant},
};
use commonware_cryptography::{Digest, certificate::Scheme};

/// A map of [Attributable] items keyed by their signer index.
///
/// The key for each item is automatically inferred from [Attributable::signer()].
/// Each signer can insert at most one item.
pub struct AttributableMap<T: Attributable> {
    participants: usize,
    data: Vec<Option<T>>,
    added: usize,
}

impl<T: Attributable> AttributableMap<T> {
    /// Creates a new [AttributableMap] with the given number of participants.
    pub const fn new(participants: usize) -> Self {
        Self {
            participants,
            data: Vec::new(),
            added: 0,
        }
    }

    /// Clears all existing items and releases their storage.
    pub fn clear(&mut self) {
        self.data = Vec::new();
        self.added = 0;
    }

    /// Inserts an item into the map, using [Attributable::signer()] as the key,
    /// if it has not been added yet.
    ///
    /// Returns `true` if the item was inserted, `false` if an item from this
    /// signer already exists or if the signer index is out of bounds.
    pub fn insert(&mut self, item: T) -> bool {
        let index: usize = item.signer().into();
        if index >= self.participants {
            return false;
        }
        if self.data.is_empty() {
            // `resize_with` avoids requiring `T: Clone` while pre-filling with `None`.
            self.data.reserve_exact(self.participants);
            self.data.resize_with(self.participants, || None);
        }
        if self.data[index].is_some() {
            return false;
        }
        self.data[index] = Some(item);
        self.added += 1;
        true
    }

    /// Returns the number of items in the [AttributableMap].
    pub const fn len(&self) -> usize {
        self.added
    }

    /// Returns `true` if the [AttributableMap] is empty.
    pub const fn is_empty(&self) -> bool {
        self.added == 0
    }

    /// Returns a reference to the item associated with the given signer, if present.
    pub fn get(&self, signer: Participant) -> Option<&T> {
        self.data.get(<usize>::from(signer))?.as_ref()
    }

    /// Returns an iterator over items in the map, ordered by signer index
    /// ([Attributable::signer()]).
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.data.iter().filter_map(|o| o.as_ref())
    }
}

/// Full vote storage for a phase, or a marker that its certificate was recorded.
#[cfg(not(target_arch = "wasm32"))]
enum Phase<T: Attributable> {
    Full(AttributableMap<T>),
    Compacted,
}

#[cfg(not(target_arch = "wasm32"))]
impl<T: Attributable> Phase<T> {
    const fn new(participants: usize) -> Self {
        Self::Full(AttributableMap::new(participants))
    }

    fn insert(&mut self, vote: T) -> bool {
        match self {
            Self::Full(votes) => votes.insert(vote),
            Self::Compacted => false,
        }
    }

    fn get(&self, signer: Participant) -> Option<&T> {
        match self {
            Self::Full(votes) => votes.get(signer),
            Self::Compacted => None,
        }
    }

    fn iter(&self) -> impl Iterator<Item = &T> {
        match self {
            Self::Full(votes) => Some(votes),
            Self::Compacted => None,
        }
        .into_iter()
        .flat_map(AttributableMap::iter)
    }

    const fn len(&self) -> usize {
        match self {
            Self::Full(votes) => votes.len(),
            Self::Compacted => 0,
        }
    }

    fn compact(&mut self) -> Option<AttributableMap<T>> {
        match std::mem::replace(self, Self::Compacted) {
            Self::Full(votes) => Some(votes),
            Self::Compacted => None,
        }
    }

    fn reset(&mut self, participants: usize) {
        *self = Self::new(participants);
    }
}

/// Stock Simplex tracker, preserving its existing compaction behavior.
#[cfg(not(target_arch = "wasm32"))]
pub type VoteTracker<S, D> = VoteTrackerWith<S, D, Plain>;

/// Tracks notarize/nullify/finalize votes for a view.
///
/// Each vote type is stored in its own lazily allocated phase so a validator can
/// contribute at most one vote per phase. After certification, compact signer facts
/// can replace full votes while preserving forwarding, duplicate suppression, and
/// compact conflict detection.
#[cfg(not(target_arch = "wasm32"))]
pub struct VoteTrackerWith<S: Scheme, D: Digest, M: Mode<S, D>> {
    participants: usize,
    retain_votes_after_certification: bool,
    /// Compact state records whether a signer voted and whether the vote carried the
    /// authoritative proposal. The first fact suppresses duplicates and cross-phase
    /// conflicts. The second avoids forwarding a block to validators that already have it.
    compacted: Vec<u8>,
    notarizes: Phase<M::Notarize>,
    nullifies: Phase<Nullify<S>>,
    /// Finalize votes include the proposal digest so the entire certificate can be
    /// reconstructed once the quorum threshold is hit.
    finalizes: Phase<M::Vote>,
}

/// Outcome of recording a vote in its phase-specific lifecycle state.
#[cfg(not(target_arch = "wasm32"))]
pub(crate) enum Outcome {
    /// Newly recorded, with the full vote retained when `retained` is true.
    Added { retained: bool },
    /// Not newly recorded, with full votes still retained when `retained` is true.
    Duplicate { retained: bool },
    /// The compact proposal relation proves a same-phase conflict.
    Conflicting,
}

/// A recorded vote retained in full or represented by compact signer state.
#[cfg(not(target_arch = "wasm32"))]
pub(crate) enum ObservedVote<'a, T> {
    Retained(&'a T),
    Compacted,
}

#[cfg(not(target_arch = "wasm32"))]
impl<S: Scheme, D: Digest, M: Mode<S, D>> VoteTrackerWith<S, D, M> {
    const NOTARIZE_SEEN: u8 = 1 << 0;
    const NOTARIZE_HAS_PROPOSAL: u8 = 1 << 1;
    const NULLIFY_SEEN: u8 = 1 << 2;
    const FINALIZE_SEEN: u8 = 1 << 3;
    const FINALIZE_HAS_PROPOSAL: u8 = 1 << 4;

    /// Creates a tracker sized for `participants` validators.
    ///
    /// When `retain_votes_after_certification` is false, full votes are released
    /// once their phase certifies. Otherwise they remain until explicitly cleared
    /// or the tracker is dropped.
    pub const fn new(participants: usize, retain_votes_after_certification: bool) -> Self {
        Self {
            participants,
            retain_votes_after_certification,
            compacted: Vec::new(),
            notarizes: Phase::new(participants),
            nullifies: Phase::new(participants),
            finalizes: Phase::new(participants),
        }
    }

    /// Records monotonic signer facts after a phase releases its full vote map.
    ///
    /// A later matching vote can record that the signer has the authoritative
    /// proposal even when the signer was already observed.
    fn remember(
        participants: usize,
        compacted: &mut Vec<u8>,
        signer: Participant,
        seen: u8,
        proposal_relation: Option<(u8, bool)>,
    ) -> Outcome {
        let index = usize::from(signer);
        if index >= participants {
            return Outcome::Duplicate { retained: false };
        }

        // Certificate-first rounds remain allocation-free until a vote arrives.
        if compacted.is_empty() {
            compacted.resize(participants, 0);
        }

        let flags = &mut compacted[index];
        let previously_seen = *flags & seen != 0;
        let proposal_conflict = proposal_relation.is_some_and(|(has_proposal, matches)| {
            previously_seen && (*flags & has_proposal != 0) != matches
        });
        *flags |= seen;
        if let Some((has_proposal, true)) = proposal_relation {
            *flags |= has_proposal;
        }
        if !previously_seen {
            Outcome::Added { retained: false }
        } else if proposal_conflict {
            Outcome::Conflicting
        } else {
            Outcome::Duplicate { retained: false }
        }
    }

    /// Records one phase according to its full-to-compact storage lifecycle.
    ///
    /// A full phase owns duplicate detection and full-vote storage. A compacted
    /// phase retains only signer facts until explicitly cleared.
    fn record_phase<T: Attributable + Clone>(
        participants: usize,
        compacted: &mut Vec<u8>,
        phase: &mut Phase<T>,
        vote: &T,
        seen: u8,
        proposal_relation: Option<(u8, bool)>,
    ) -> Outcome {
        match phase {
            Phase::Full(votes) => {
                if votes.insert(vote.clone()) {
                    Outcome::Added { retained: true }
                } else {
                    Outcome::Duplicate { retained: true }
                }
            }
            Phase::Compacted => Self::remember(
                participants,
                compacted,
                vote.signer(),
                seen,
                proposal_relation,
            ),
        }
    }

    fn remembered(&self, signer: Participant, flag: u8) -> bool {
        self.compacted
            .get(usize::from(signer))
            .is_some_and(|flags| flags & flag != 0)
    }

    /// Records a vote in full or as compact post-certificate state.
    ///
    /// `proposal` identifies the authoritative proposal used for compact match state.
    pub(crate) fn record(
        &mut self,
        vote: &VoteWith<S, D, M>,
        proposal: Option<&Proposal<D>>,
    ) -> Outcome {
        match vote {
            VoteWith::Notarize(notarize) => Self::record_phase(
                self.participants,
                &mut self.compacted,
                &mut self.notarizes,
                notarize,
                Self::NOTARIZE_SEEN,
                proposal.map(|proposal| {
                    (
                        Self::NOTARIZE_HAS_PROPOSAL,
                        proposal == &M::notarize(notarize).proposal,
                    )
                }),
            ),
            VoteWith::Nullify(nullify) => Self::record_phase(
                self.participants,
                &mut self.compacted,
                &mut self.nullifies,
                nullify,
                Self::NULLIFY_SEEN,
                None,
            ),
            VoteWith::Finalize(finalize) => Self::record_phase(
                self.participants,
                &mut self.compacted,
                &mut self.finalizes,
                finalize,
                Self::FINALIZE_SEEN,
                proposal.map(|proposal| {
                    (
                        Self::FINALIZE_HAS_PROPOSAL,
                        proposal == M::finalize_proposal(finalize),
                    )
                }),
            ),
        }
    }

    /// Moves a phase from full vote storage to compact signer state.
    ///
    /// Taking the map makes the transition idempotent. Empty phases remain
    /// allocation-free, while existing signer and proposal-match facts survive.
    fn release<T: Attributable>(
        participants: usize,
        compacted: &mut Vec<u8>,
        phase: &mut Phase<T>,
        seen: u8,
        has_proposal: u8,
        carries_proposal: impl Fn(&T) -> bool,
    ) {
        let Some(votes) = phase.compact() else {
            return;
        };

        // A certificate may arrive before any individual votes, in which case there
        // are no signer facts worth allocating a table for.
        if !votes.is_empty() && compacted.is_empty() {
            compacted.resize(participants, 0);
        }

        // Proposal-match bits are relative to the certificate-backed proposal.
        for vote in votes.iter() {
            let flags = &mut compacted[usize::from(vote.signer())];
            *flags |= seen;
            if carries_proposal(vote) {
                *flags |= has_proposal;
            }
        }
    }

    /// Returns the retained or compact state for a previously observed nullify vote.
    pub(crate) fn saw_nullify(&self, signer: Participant) -> Option<ObservedVote<'_, Nullify<S>>> {
        self.nullify(signer)
            .map(ObservedVote::Retained)
            .or_else(|| {
                self.remembered(signer, Self::NULLIFY_SEEN)
                    .then_some(ObservedVote::Compacted)
            })
    }

    /// Returns the retained or compact state for a previously observed finalize vote.
    pub(crate) fn saw_finalize(&self, signer: Participant) -> Option<ObservedVote<'_, M::Vote>> {
        self.finalize(signer)
            .map(ObservedVote::Retained)
            .or_else(|| {
                self.remembered(signer, Self::FINALIZE_SEEN)
                    .then_some(ObservedVote::Compacted)
            })
    }

    /// Returns whether `signer` is known to have the authoritative proposal
    /// from notarizing it.
    pub(crate) fn has_notarize_for(&self, signer: Participant, proposal: &Proposal<D>) -> bool {
        self.remembered(signer, Self::NOTARIZE_HAS_PROPOSAL)
            || self
                .notarize(signer)
                .is_some_and(|vote| &M::notarize(vote).proposal == proposal)
    }

    /// Returns whether `signer` is known to have the authoritative proposal
    /// from finalizing it.
    pub(crate) fn has_finalize_for(&self, signer: Participant, proposal: &Proposal<D>) -> bool {
        self.remembered(signer, Self::FINALIZE_HAS_PROPOSAL)
            || self
                .finalize(signer)
                .is_some_and(|vote| M::finalize_proposal(vote) == proposal)
    }

    /// Releases notarize votes unless full evidence is configured for retention.
    pub(crate) fn release_notarizes(&mut self, proposal: &Proposal<D>) {
        if self.retain_votes_after_certification || M::RETAIN_INTERPRETATION {
            return;
        }
        Self::release(
            self.participants,
            &mut self.compacted,
            &mut self.notarizes,
            Self::NOTARIZE_SEEN,
            Self::NOTARIZE_HAS_PROPOSAL,
            |vote: &M::Notarize| &M::notarize(vote).proposal == proposal,
        );
    }

    /// Releases nullify votes unless full evidence is configured for retention.
    pub(crate) fn release_nullifies(&mut self) {
        if self.retain_votes_after_certification {
            return;
        }
        Self::release(
            self.participants,
            &mut self.compacted,
            &mut self.nullifies,
            Self::NULLIFY_SEEN,
            0,
            |_| false,
        );
    }

    /// Releases finalize votes unless full evidence is configured for retention.
    pub(crate) fn release_finalizes(&mut self, proposal: &Proposal<D>) {
        if self.retain_votes_after_certification || M::RETAIN_INTERPRETATION {
            return;
        }
        Self::release(
            self.participants,
            &mut self.compacted,
            &mut self.finalizes,
            Self::FINALIZE_SEEN,
            Self::FINALIZE_HAS_PROPOSAL,
            |vote: &M::Vote| M::finalize_proposal(vote) == proposal,
        );
    }

    fn clear_compacted(&mut self, cleared: u8) {
        for flags in &mut self.compacted {
            *flags &= !cleared;
        }
        if self.compacted.iter().all(|&flags| flags == 0) {
            self.compacted = Vec::new();
        }
    }

    /// Inserts a notarize vote if the signer has not already voted.
    pub fn insert_notarize(&mut self, vote: M::Notarize) -> bool {
        self.notarizes.insert(vote)
    }

    /// Inserts a nullify vote if the signer has not already voted.
    pub fn insert_nullify(&mut self, vote: Nullify<S>) -> bool {
        self.nullifies.insert(vote)
    }

    /// Inserts a finalize vote if the signer has not already voted.
    pub fn insert_finalize(&mut self, vote: M::Vote) -> bool {
        self.finalizes.insert(vote)
    }

    /// Returns the notarize vote for `signer`, if present.
    pub fn notarize(&self, signer: Participant) -> Option<&M::Notarize> {
        self.notarizes.get(signer)
    }

    /// Returns the nullify vote for `signer`, if present.
    pub fn nullify(&self, signer: Participant) -> Option<&Nullify<S>> {
        self.nullifies.get(signer)
    }

    /// Returns the finalize vote for `signer`, if present.
    pub fn finalize(&self, signer: Participant) -> Option<&M::Vote> {
        self.finalizes.get(signer)
    }

    /// Iterates over notarize votes in signer order.
    pub fn iter_notarizes(&self) -> impl Iterator<Item = &M::Notarize> {
        self.notarizes.iter()
    }

    /// Iterates over nullify votes in signer order.
    pub fn iter_nullifies(&self) -> impl Iterator<Item = &Nullify<S>> {
        self.nullifies.iter()
    }

    /// Iterates over finalize votes in signer order.
    pub fn iter_finalizes(&self) -> impl Iterator<Item = &M::Vote> {
        self.finalizes.iter()
    }

    /// Returns how many notarize votes have been recorded.
    pub fn len_notarizes(&self) -> u32 {
        let len = self.notarizes.len();
        u32::try_from(len).expect("too many notarize votes")
    }

    /// Returns how many nullify votes have been recorded.
    pub fn len_nullifies(&self) -> u32 {
        let len = self.nullifies.len();
        u32::try_from(len).expect("too many nullify votes")
    }

    /// Returns how many finalize votes have been recorded.
    pub fn len_finalizes(&self) -> u32 {
        let len = self.finalizes.len();
        u32::try_from(len).expect("too many finalize votes")
    }

    /// Returns `true` if the given signer has a notarize vote recorded.
    pub fn has_notarize(&self, signer: Participant) -> bool {
        self.notarize(signer).is_some()
    }

    /// Returns `true` if a nullify vote has been recorded for `signer`.
    pub fn has_nullify(&self, signer: Participant) -> bool {
        self.nullify(signer).is_some()
    }

    /// Returns `true` if a finalize vote has been recorded for `signer`.
    pub fn has_finalize(&self, signer: Participant) -> bool {
        self.finalize(signer).is_some()
    }

    /// Clears all notarize votes and releases their storage.
    pub fn clear_notarizes(&mut self) {
        self.notarizes.reset(self.participants);
        self.clear_compacted(Self::NOTARIZE_SEEN | Self::NOTARIZE_HAS_PROPOSAL);
    }

    /// Clears all finalize votes and releases their storage.
    pub fn clear_finalizes(&mut self) {
        self.finalizes.reset(self.participants);
        self.clear_compacted(Self::FINALIZE_SEEN | Self::FINALIZE_HAS_PROPOSAL);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        simplex::{
            scheme::ed25519,
            types::{Finalize, Notarize, Vote},
        },
        types::{Epoch, Round, View},
    };
    use commonware_cryptography::sha256::Digest as Sha256;
    use commonware_utils::test_rng;
    const NAMESPACE: &[u8] = b"test";
    fn sample_digest(v: u8) -> Sha256 {
        Sha256::from([v; 32])
    }
    struct MockAttributable(Participant);

    impl Attributable for MockAttributable {
        fn signer(&self) -> Participant {
            self.0
        }
    }

    #[test]
    fn test_attributable_map() {
        let mut map = AttributableMap::new(5);
        assert_eq!(map.len(), 0);
        assert!(map.is_empty());
        assert_eq!(map.data.capacity(), 0, "empty maps should allocate lazily");

        // Test get on empty map
        for i in 0..5 {
            assert!(map.get(Participant::new(i)).is_none());
        }

        assert!(map.insert(MockAttributable(Participant::new(3))));
        assert!(map.data.capacity() >= 5);
        assert_eq!(map.len(), 1);
        assert!(!map.is_empty());
        let mut iter = map.iter();
        assert!(matches!(iter.next(), Some(a) if a.signer() == Participant::new(3)));
        assert!(iter.next().is_none());
        drop(iter);

        // Test get on existing item
        assert!(
            matches!(map.get(Participant::new(3)), Some(a) if a.signer() == Participant::new(3))
        );

        assert!(map.insert(MockAttributable(Participant::new(1))));
        assert_eq!(map.len(), 2);
        assert!(!map.is_empty());
        let mut iter = map.iter();
        assert!(matches!(iter.next(), Some(a) if a.signer() == Participant::new(1)));
        assert!(matches!(iter.next(), Some(a) if a.signer() == Participant::new(3)));
        assert!(iter.next().is_none());
        drop(iter);

        // Test get on both items
        assert!(
            matches!(map.get(Participant::new(1)), Some(a) if a.signer() == Participant::new(1))
        );
        assert!(
            matches!(map.get(Participant::new(3)), Some(a) if a.signer() == Participant::new(3))
        );

        // Test get on non-existing items
        assert!(map.get(Participant::new(0)).is_none());
        assert!(map.get(Participant::new(2)).is_none());
        assert!(map.get(Participant::new(4)).is_none());

        assert!(!map.insert(MockAttributable(Participant::new(3))));
        assert_eq!(map.len(), 2);
        assert!(!map.is_empty());
        let mut iter = map.iter();
        assert!(matches!(iter.next(), Some(a) if a.signer() == Participant::new(1)));
        assert!(matches!(iter.next(), Some(a) if a.signer() == Participant::new(3)));
        assert!(iter.next().is_none());
        drop(iter);

        // Test out-of-bounds signer indices
        assert!(!map.insert(MockAttributable(Participant::new(5))));
        assert!(!map.insert(MockAttributable(Participant::new(100))));
        assert_eq!(map.len(), 2);

        // Test clear
        map.clear();
        assert_eq!(map.len(), 0);
        assert!(map.is_empty());
        assert!(map.iter().next().is_none());
        assert_eq!(map.data.capacity(), 0, "clear should release vote storage");

        // Verify can insert after clear
        assert!(map.insert(MockAttributable(Participant::new(2))));
        assert_eq!(map.len(), 1);
        let mut iter = map.iter();
        assert!(matches!(iter.next(), Some(a) if a.signer() == Participant::new(2)));
        assert!(iter.next().is_none());
    }

    #[test]
    fn test_vote_tracker_clears_compacted_state() {
        let mut rng = test_rng();
        let fixture = ed25519::fixture(&mut rng, NAMESPACE, 2);
        let round = Round::new(Epoch::new(0), View::new(1));
        let mut tracker = VoteTracker::<ed25519::Scheme, Sha256>::new(2, false);
        let signer = Participant::new(1);
        let scheme = &fixture.schemes[usize::from(signer)];
        let proposal = Proposal::new(round, View::zero(), sample_digest(1));
        let notarize = Vote::Notarize(Notarize::sign(scheme, proposal.clone()).unwrap());
        let finalize = Vote::Finalize(Finalize::sign(scheme, proposal.clone()).unwrap());

        tracker.release_notarizes(&proposal);
        tracker.release_finalizes(&proposal);
        assert!(matches!(
            tracker.record(&notarize, Some(&proposal)),
            Outcome::Added { retained: false }
        ));
        assert!(matches!(
            tracker.record(&finalize, Some(&proposal)),
            Outcome::Added { retained: false }
        ));
        assert!(tracker.has_notarize_for(signer, &proposal));
        assert!(tracker.has_finalize_for(signer, &proposal));

        tracker.clear_notarizes();
        assert!(!tracker.has_notarize_for(signer, &proposal));
        assert!(matches!(
            tracker.record(&notarize, Some(&proposal)),
            Outcome::Added { retained: true }
        ));

        tracker.clear_finalizes();
        assert!(!tracker.has_finalize_for(signer, &proposal));
        assert_eq!(tracker.compacted.capacity(), 0);
        assert!(matches!(
            tracker.record(&finalize, Some(&proposal)),
            Outcome::Added { retained: true }
        ));
    }

    #[test]
    fn test_vote_tracker_insert_and_accessors() {
        let mut rng = test_rng();
        let fixture = ed25519::fixture(&mut rng, NAMESPACE, 2);
        let round = Round::new(Epoch::new(0), View::new(1));
        let proposal = Proposal::new(round, View::zero(), sample_digest(1));
        let scheme = &fixture.schemes[0];
        let signer = Participant::new(0);
        let notarize = Notarize::sign(scheme, proposal.clone()).unwrap();
        let nullify = Nullify::sign::<Sha256>(scheme, round).unwrap();
        let finalize = Finalize::sign(scheme, proposal.clone()).unwrap();
        let mut tracker = VoteTracker::new(2, false);

        assert!(tracker.insert_notarize(notarize.clone()));
        assert!(tracker.insert_nullify(nullify.clone()));
        assert!(tracker.insert_finalize(finalize.clone()));
        assert_eq!(tracker.len_notarizes(), 1);
        assert_eq!(tracker.len_nullifies(), 1);
        assert_eq!(tracker.len_finalizes(), 1);
        assert!(tracker.has_notarize(signer));
        assert!(tracker.has_nullify(signer));
        assert!(tracker.has_finalize(signer));

        tracker.release_notarizes(&proposal);
        tracker.release_nullifies();
        tracker.release_finalizes(&proposal);
        assert_eq!(tracker.len_notarizes(), 0);
        assert_eq!(tracker.len_nullifies(), 0);
        assert_eq!(tracker.len_finalizes(), 0);
        assert!(!tracker.has_notarize(signer));
        assert!(!tracker.has_nullify(signer));
        assert!(!tracker.has_finalize(signer));
        assert!(tracker.iter_notarizes().next().is_none());
        assert!(tracker.iter_nullifies().next().is_none());
        assert!(tracker.iter_finalizes().next().is_none());
        assert!(!tracker.insert_notarize(notarize));
        assert!(!tracker.insert_nullify(nullify));
        assert!(!tracker.insert_finalize(finalize));

        // Releasing a compacted phase is idempotent.
        tracker.release_notarizes(&proposal);
    }

    #[test]
    fn test_vote_tracker_retention_policy() {
        let mut rng = test_rng();
        let fixture = ed25519::fixture(&mut rng, NAMESPACE, 2);
        let proposal = Proposal::new(
            Round::new(Epoch::new(0), View::new(1)),
            View::zero(),
            sample_digest(1),
        );
        let notarize = Notarize::sign(&fixture.schemes[0], proposal.clone()).unwrap();
        let signer = notarize.signer();
        let vote = Vote::Notarize(notarize);

        let mut releasing = VoteTracker::new(2, false);
        assert!(matches!(
            releasing.record(&vote, Some(&proposal)),
            Outcome::Added { retained: true }
        ));
        let Phase::Full(votes) = &releasing.notarizes else {
            panic!("notarize phase compacted before certification");
        };
        assert!(votes.data.capacity() >= 2);
        releasing.release_notarizes(&proposal);
        assert!(matches!(&releasing.notarizes, Phase::Compacted));
        assert!(matches!(
            releasing.record(&vote, Some(&proposal)),
            Outcome::Duplicate { retained: false }
        ));

        // A certificate can arrive before any individual votes. Subsequent votes
        // must use compact storage instead of recreating the released full map.
        let mut certificate_first = VoteTracker::new(2, false);
        certificate_first.release_notarizes(&proposal);
        assert!(matches!(
            certificate_first.record(&vote, Some(&proposal)),
            Outcome::Added { retained: false }
        ));
        assert!(matches!(&certificate_first.notarizes, Phase::Compacted));
        assert!(matches!(
            certificate_first.record(&vote, Some(&proposal)),
            Outcome::Duplicate { retained: false }
        ));

        let mut retaining = VoteTracker::new(2, true);
        assert!(matches!(
            retaining.record(&vote, Some(&proposal)),
            Outcome::Added { retained: true }
        ));
        let Phase::Full(votes) = &retaining.notarizes else {
            panic!("retained notarize phase compacted");
        };
        let retained_capacity = votes.data.capacity();
        retaining.release_notarizes(&proposal);
        let Phase::Full(votes) = &retaining.notarizes else {
            panic!("retained notarize phase compacted");
        };
        assert_eq!(votes.data.capacity(), retained_capacity);
        assert!(retaining.notarize(signer).is_some());
    }
}

#[cfg(test)]
mod extension_tests {
    use super::*;
    use crate::{
        simplex::{
            extension::{
                certificate, report,
                vote::{Statement, Vote as ExtensionVote},
            },
            phase2::Extended,
            scheme::ed25519,
            types::{Notarize, VoteWith},
        },
        types::{Epoch, Round, View},
    };
    use bytes::Bytes;
    use commonware_cryptography::sha256::Digest as Sha256;
    use commonware_utils::TestRng;

    #[test]
    fn extended_tracker_retains_original_reports_and_exact_final_subjects_after_qc() {
        let f = ed25519::fixture(
            &mut TestRng::new(48),
            b"_COMMONWARE_CONSENSUS_TRACKER_EXTENSION_TEST",
            6,
        );
        let round = Round::new(Epoch::new(1), View::new(2));
        let proposal = Proposal::new(round, View::new(1), Sha256::from([1; 32]));
        let mut tracker = VoteTrackerWith::<_, _, Extended>::new(6, false);
        let first = report::Notarize::new(
            Notarize::sign(&f.schemes[0], proposal.clone()).unwrap(),
            Some(Bytes::from_static(b"original report")),
        )
        .unwrap();
        let first = VoteWith::Notarize(first);
        let statement = Statement {
            proposal: proposal.clone(),
            domain: Sha256::from([2; 32]),
            ballot: round,
            parent: Sha256::from([3; 32]),
            extension: Sha256::from([4; 32]),
        };
        let final_vote = certificate::Finalize::new(
            ExtensionVote::sign(&f.schemes[0], statement.clone()).unwrap(),
        )
        .unwrap();
        let final_vote = VoteWith::Finalize(final_vote);
        assert!(matches!(
            tracker.record(&first, Some(&proposal)),
            Outcome::Added { retained: true }
        ));
        assert!(matches!(
            tracker.record(&final_vote, Some(&proposal)),
            Outcome::Added { retained: true }
        ));
        tracker.release_notarizes(&proposal);
        tracker.release_finalizes(&proposal);
        let signer = Participant::new(0);
        assert_eq!(
            tracker.notarize(signer).unwrap().report().unwrap().as_ref(),
            b"original report"
        );
        assert_eq!(
            tracker.finalize(signer).unwrap().vote().statement,
            statement
        );
        assert!(matches!(
            tracker.saw_finalize(signer),
            Some(ObservedVote::Retained(_))
        ));
        assert!(tracker.has_notarize_for(signer, &proposal));
        assert!(tracker.has_finalize_for(signer, &proposal));
        // A different final direction cannot replace the original signer evidence.
        let conflicting = Statement {
            extension: Sha256::from([5; 32]),
            ..statement.clone()
        };
        let vote =
            certificate::Finalize::new(ExtensionVote::sign(&f.schemes[0], conflicting).unwrap())
                .unwrap();
        assert!(matches!(
            tracker.record(&VoteWith::Finalize(vote), Some(&proposal)),
            Outcome::Duplicate { retained: true }
        ));
        assert_eq!(
            tracker.finalize(signer).unwrap().vote().statement,
            statement
        );
        // Nullify remains independent and uses the original compact signer facts.
        let nullify = VoteWith::Nullify(Nullify::sign::<Sha256>(&f.schemes[1], round).unwrap());
        assert!(matches!(
            tracker.record(&nullify, Some(&proposal)),
            Outcome::Added { retained: true }
        ));
        tracker.release_nullifies();
        assert!(matches!(
            tracker.saw_nullify(Participant::new(1)),
            Some(ObservedVote::Compacted)
        ));
        // A certificate before its first report must not prevent retention.
        let mut early = VoteTrackerWith::<_, _, Extended>::new(6, false);
        early.release_notarizes(&proposal);
        early.release_finalizes(&proposal);
        assert!(matches!(
            early.record(&first, Some(&proposal)),
            Outcome::Added { retained: true }
        ));
        assert!(matches!(
            early.record(&final_vote, Some(&proposal)),
            Outcome::Added { retained: true }
        ));
        // Explicit clearing releases both evidence and signer membership.
        tracker.clear_notarizes();
        tracker.clear_finalizes();
        assert!(!tracker.has_notarize(signer));
        assert!(!tracker.has_finalize(signer));
        assert!(matches!(
            tracker.record(&first, Some(&proposal)),
            Outcome::Added { retained: true }
        ));
        assert!(matches!(
            tracker.record(&final_vote, Some(&proposal)),
            Outcome::Added { retained: true }
        ));
    }
}
