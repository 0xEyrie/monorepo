//! Application-defined merging of authenticated producer-chain prefixes.

use crate::{
    multimmit::types::{BlockRef, VoteReports},
    types::Epoch,
};
use bytes::Bytes;
use commonware_codec::{Codec, Decode as _, Error as CodecError};
use commonware_cryptography::Digest;
use std::sync::Arc;

/// Maximum number of blocks in one immutable ordering context.
///
/// Larger history ranges are split into consecutive contexts of this size. The split is
/// independent of storage, delivery, and acknowledgement batch sizes.
pub const MAX_ORDERING_BLOCKS: usize = 1024;

/// Producer-chain inputs and typed policy data shared by local and canonical ordering.
///
/// Marshal supplies authenticated history metadata and chain-indexed, oldest-first prefixes.
/// Speculative contexts contain locally known blocks grouped by chain, without history metadata.
/// Matching prefixes and policy data use the same Ordering implementation; missing local inputs
/// can still change the speculative order. A local context grants no finality or storage authority.
pub struct OrderingContext<D: Digest, T = [u8; 0]> {
    epoch: Option<Epoch>,
    history: Option<D>,
    parent_history: Option<D>,
    base: Option<Arc<[BlockRef<D>]>>,
    prefixes: Arc<[Vec<BlockRef<D>>]>,
    proposal_extension: Option<T>,
    vote_reports: Option<Arc<VoteReports<D>>>,
}

impl<D: Digest> OrderingContext<D> {
    pub(crate) fn new(
        epoch: Epoch,
        history: D,
        base: Vec<BlockRef<D>>,
        prefixes: Vec<Vec<BlockRef<D>>>,
    ) -> Self {
        Self {
            epoch: Some(epoch),
            history: Some(history),
            parent_history: None,
            base: Some(base.into()),
            prefixes: prefixes.into(),
            proposal_extension: None,
            vote_reports: None,
        }
    }
}

impl<D: Digest, T> OrderingContext<D, T> {
    /// Groups local blocks by chain and height without claiming authenticated history.
    ///
    /// Only nonempty prefixes are retained, in ascending chain-ID order. Callers bound the input
    /// size and supply any already-validated typed policy data. No codec or consensus I/O runs.
    pub fn speculative(mut blocks: Vec<BlockRef<D>>, extension: Option<T>) -> Self {
        blocks.sort_by_key(|reference| (reference.chain(), reference.height(), reference.digest()));
        let mut prefixes: Vec<Vec<BlockRef<D>>> = Vec::new();
        for reference in blocks {
            if prefixes
                .last()
                .is_none_or(|prefix| prefix[0].chain() != reference.chain())
            {
                prefixes.push(Vec::new());
            }
            prefixes
                .last_mut()
                .expect("nonempty prefix list")
                .push(reference);
        }
        Self {
            epoch: None,
            history: None,
            parent_history: None,
            base: None,
            prefixes: prefixes.into(),
            proposal_extension: extension,
            vote_reports: None,
        }
    }

    /// Checks a complete lane-order-preserving permutation, without authenticating the inputs.
    pub fn is_valid_order(&self, ordered: &[BlockRef<D>]) -> bool {
        validate(self, ordered).is_ok()
    }

    pub(crate) fn with_proposal_extension<U>(&self, extension: Option<U>) -> OrderingContext<D, U> {
        OrderingContext {
            epoch: self.epoch,
            history: self.history,
            parent_history: self.parent_history,
            base: self.base.as_ref().map(Arc::clone),
            prefixes: Arc::clone(&self.prefixes),
            proposal_extension: extension,
            vote_reports: self.vote_reports.as_ref().map(Arc::clone),
        }
    }

    /// Returns the supplied typed policy data.
    ///
    /// Marshal authenticates this data through the history link; local callers provide their view.
    /// `None` denotes absent data, including genesis.
    pub const fn proposal_extension(&self) -> Option<&T> {
        self.proposal_extension.as_ref()
    }

    /// Returns original ordinary-vote reports authenticated by this history opening.
    ///
    /// Local speculative contexts omit them. The application must check its required quorum,
    /// report codec and exact context; this collection does not attest execution progress.
    pub fn vote_reports(&self) -> Option<&VoteReports<D>> {
        self.vote_reports.as_deref()
    }

    pub(crate) fn with_vote_reports(mut self, reports: Option<Arc<VoteReports<D>>>) -> Self {
        self.vote_reports = reports;
        self
    }

    /// Returns the authenticated producer epoch, absent for speculative inputs.
    pub const fn epoch(&self) -> Option<Epoch> {
        self.epoch
    }

    /// Returns the history commitment, absent for speculative inputs.
    pub const fn history(&self) -> Option<D> {
        self.history
    }

    /// Returns the parent commitment of this authenticated history opening.
    ///
    /// This is the producing proposal's history subject. Consecutive chunks of one opening
    /// share it even as `base()` advances. Local inputs and default final sweeps omit it.
    pub const fn parent_history(&self) -> Option<D> {
        self.parent_history
    }

    pub(crate) const fn with_parent_history(mut self, parent: Option<D>) -> Self {
        self.parent_history = parent;
        self
    }

    /// Returns the authenticated per-chain frontier, absent for speculative inputs.
    pub fn base(&self) -> Option<&[BlockRef<D>]> {
        self.base.as_deref()
    }

    /// Returns inputs grouped by chain ID, oldest first within each chain.
    /// Marshal prefixes are chain-indexed; speculative prefixes omit empty chains.
    pub fn prefixes(&self) -> &[Vec<BlockRef<D>>] {
        &self.prefixes
    }
}

/// Selects the cross-chain order of the supplied inputs.
///
/// Return every input block exactly once, preserving increasing height on each chain. There is
/// no required cross-chain order and no reservation for a block outside the context. Marshal
/// validates the complete result before admitting any canonical outputs.
/// Local pools can call the same policy with speculative contexts and validate its permutation.
///
/// # Protocol contract
///
/// Calls must be bounded, synchronous, and return the same order for the same context on every
/// node, including history catch-up and restart. Use the same policy for the entire epoch and
/// storage namespace. Do not depend on arrival order, local execution progress, acknowledgement
/// timing, or mutable report collection. A report-based adapter must read the same frozen,
/// retained direction for the exact context on all nodes. Proposal extensions are included in
/// each history commitment and supplied as `Option<T>`. Configure the same `T: commonware_codec::Codec`
/// and codec bounds in the engine and Marshal. Callbacks need no serialization code.
///
/// State-sync snapshots must contain a prefix of this same policy's output. Floor verification
/// authenticates a checkpoint boundary; it does not invoke the policy or authenticate snapshot
/// state. On replay, Marshal rejects a policy result that places an already applied block after
/// a new output in the same context.
///
/// Custom policies run on history ranges committed by a finalized leader, not on that leader's
/// locally growing vote pool. Outputs from the latter wait until a subsequent finalized leader
/// authenticates their history. This preserves a common input across different L-QCs.
///
/// # Examples
///
/// Merge complete certified prefixes in ascending chain order:
///
/// ```
/// use commonware_consensus::multimmit::{
///     marshal::{Ordering, OrderingContext}, types::BlockRef,
/// };
/// use commonware_cryptography::Digest;
///
/// struct LaneMajor;
/// impl<D: Digest> Ordering<D> for LaneMajor {
///     fn order(&self, context: &OrderingContext<D>) -> Vec<BlockRef<D>> {
///         context.prefixes().iter().flatten().copied().collect()
///     }
/// }
/// // Install on every node with config.with_ordering(LaneMajor, ()).
/// ```
pub trait Ordering<D: Digest, T = [u8; 0]>: Send + Sync + 'static {
    /// Checks frozen policy constraints before the context can produce any outputs.
    ///
    /// Use only the supplied context and immutable epoch rules. Returning `false` rejects
    /// the opening, including replay; it must not depend on local availability or reports.
    /// Native permutation and lane-order checks run independently after `order`.
    fn validate_context(&self, _context: &OrderingContext<D, T>) -> bool {
        true
    }

    /// Returns a complete chain-order-preserving permutation of the context's blocks.
    fn order(&self, context: &OrderingContext<D, T>) -> Vec<BlockRef<D>>;
}

type Callback<D> =
    dyn Fn(&OrderingContext<D, Bytes>) -> Result<Vec<BlockRef<D>>, CodecError> + Send + Sync;

pub(crate) type Policy<D> = Option<Arc<Callback<D>>>;

pub(crate) fn policy<D, P, T>(ordering: P, codec: T::Cfg) -> Arc<Callback<D>>
where
    D: Digest,
    P: Ordering<D, T>,
    T: Codec + 'static,
    T::Cfg: Send + Sync + 'static,
{
    Arc::new(move |context| {
        let extension = context
            .proposal_extension()
            .map(|bytes| Option::<T>::decode_cfg(bytes.clone(), &codec))
            .transpose()?
            .flatten();
        let context = context.with_proposal_extension(extension);
        if !ordering.validate_context(&context) {
            return Err(CodecError::Invalid(
                "Ordering",
                "policy rejected history context",
            ));
        }
        Ok(ordering.order(&context))
    })
}

/// A policy returned something other than a complete merge of the certified prefixes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub(crate) enum InvalidOrder {
    #[error("ordering policy omitted or added blocks")]
    Length,
    #[error("ordering policy named an unknown producer chain")]
    Chain,
    #[error("ordering policy changed a block or its chain-local order")]
    Block,
}

pub(crate) fn validate<D: Digest, T>(
    context: &OrderingContext<D, T>,
    ordered: &[BlockRef<D>],
) -> Result<(), InvalidOrder> {
    if ordered.len() != context.prefixes.iter().map(Vec::len).sum::<usize>() {
        return Err(InvalidOrder::Length);
    }
    let mut next = vec![0; context.prefixes.len()];
    for reference in ordered {
        let chain = if context.history.is_some() {
            reference.chain().index()
        } else {
            context
                .prefixes
                .binary_search_by_key(&reference.chain(), |prefix| prefix[0].chain())
                .map_err(|_| InvalidOrder::Chain)?
        };
        let prefix = context.prefixes.get(chain).ok_or(InvalidOrder::Chain)?;
        if prefix.get(next[chain]) != Some(reference) {
            return Err(InvalidOrder::Block);
        }
        next[chain] += 1;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{multimmit::types::ChainId, types::Height};
    use commonware_cryptography::{Hasher as _, Sha256, sha256::Digest as Sha256Digest};
    use rstest::rstest;

    fn block(chain: u32, height: u64) -> BlockRef<Sha256Digest> {
        BlockRef::new(
            ChainId::new(chain),
            Height::new(height),
            Sha256::hash(&[&[chain as u8, height as u8]]),
        )
    }

    #[rstest]
    #[case::lane_major(vec![(0, 1), (1, 1), (1, 2)], Ok(()))]
    #[case::reverse_lanes(vec![(1, 1), (1, 2), (0, 1)], Ok(()))]
    #[case::omitted(vec![(0, 1), (1, 1)], Err(InvalidOrder::Length))]
    #[case::extra(vec![(0, 1), (1, 1), (1, 2), (0, 1)], Err(InvalidOrder::Length))]
    #[case::duplicate(vec![(0, 1), (1, 1), (1, 1)], Err(InvalidOrder::Block))]
    #[case::child_first(vec![(1, 2), (1, 1), (0, 1)], Err(InvalidOrder::Block))]
    #[case::unknown_lane(vec![(0, 1), (2, 1), (1, 2)], Err(InvalidOrder::Chain))]
    #[case::unfinalized(vec![(0, 1), (1, 1), (1, 3)], Err(InvalidOrder::Block))]
    fn accepts_only_a_complete_merge_of_certified_lane_prefixes(
        #[case] coordinates: Vec<(u32, u64)>,
        #[case] expected: Result<(), InvalidOrder>,
    ) {
        let context = OrderingContext::new(
            Epoch::new(1),
            Sha256::hash(&[b"history"]),
            vec![block(0, 0), block(1, 0)],
            vec![vec![block(0, 1)], vec![block(1, 1), block(1, 2)]],
        );
        let result = coordinates
            .into_iter()
            .map(|(chain, height)| block(chain, height))
            .collect::<Vec<_>>();
        assert_eq!(validate(&context, &result), expected);
    }

    #[test]
    fn rejects_a_substituted_digest_at_the_right_coordinate() {
        let context = OrderingContext::new(
            Epoch::new(1),
            Sha256::hash(&[b"history"]),
            vec![block(0, 0)],
            vec![vec![block(0, 1)]],
        );
        let substituted = BlockRef::new(
            ChainId::new(0),
            Height::new(1),
            Sha256::hash(&[b"another branch"]),
        );
        assert_eq!(validate(&context, &[substituted]), Err(InvalidOrder::Block));
    }
    #[rstest]
    #[case::plain(None, vec![block(0, 1), block(7, 1), block(7, 2)])]
    #[case::directed(Some(true), vec![block(7, 1), block(7, 2), block(0, 1)])]
    fn local_inputs_reuse_typed_ordering_without_claiming_native_history(
        #[case] extension: Option<bool>,
        #[case] expected: Vec<BlockRef<Sha256Digest>>,
    ) {
        struct Policy;
        impl Ordering<Sha256Digest, bool> for Policy {
            fn order(
                &self,
                context: &OrderingContext<Sha256Digest, bool>,
            ) -> Vec<BlockRef<Sha256Digest>> {
                if context.proposal_extension().copied().unwrap_or(false) {
                    context.prefixes().iter().rev().flatten().copied().collect()
                } else {
                    context.prefixes().iter().flatten().copied().collect()
                }
            }
        }
        let local =
            OrderingContext::speculative(vec![block(7, 2), block(0, 1), block(7, 1)], extension);
        assert_eq!(local.epoch(), None);
        assert_eq!(local.history(), None);
        assert_eq!(local.base(), None);
        let ordered = Policy.order(&local);
        assert_eq!(ordered, expected);
        assert!(local.is_valid_order(&ordered));
        assert!(!local.is_valid_order(&ordered[..2]));
        let bases = (0..8).map(|chain| block(chain, 0)).collect::<Vec<_>>();
        let mut prefixes = vec![Vec::new(); 8];
        prefixes[0] = vec![block(0, 1)];
        prefixes[7] = vec![block(7, 1), block(7, 2)];
        let authenticated = OrderingContext::new(
            Epoch::new(1),
            Sha256::hash(&[b"history"]),
            bases.clone(),
            prefixes,
        )
        .with_proposal_extension(extension);
        assert_eq!(authenticated.epoch(), Some(Epoch::new(1)));
        assert_eq!(authenticated.history(), Some(Sha256::hash(&[b"history"])));
        assert_eq!(authenticated.base(), Some(bases.as_slice()));
        let canonical = Policy.order(&authenticated);
        assert_eq!(canonical, expected);
        assert!(authenticated.is_valid_order(&canonical));
    }
}
