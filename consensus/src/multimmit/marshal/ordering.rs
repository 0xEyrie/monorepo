//! Application-defined merging of authenticated producer-chain prefixes.

use crate::{multimmit::types::BlockRef, types::Epoch};
use commonware_cryptography::Digest;
use std::sync::Arc;

/// Maximum number of blocks in one immutable ordering context.
///
/// Larger history ranges are split into consecutive contexts of this size. The split is
/// independent of storage, delivery, and acknowledgement batch sizes.
pub const MAX_ORDERING_BLOCKS: usize = 1024;

/// An authenticated history range's next bounded set of producer-chain prefixes.
///
/// Prefixes are in chain-ID order, oldest first within each chain. Empty prefixes are permitted.
/// All blocks are authenticated ancestors of the history's tips. `base` is the frontier before
/// this context, including blocks in earlier contexts of the same history, not the node's local
/// acknowledgement or speculative execution position. This makes contexts identical on replay.
pub struct OrderingContext<D: Digest> {
    epoch: Epoch,
    history: D,
    base: Vec<BlockRef<D>>,
    prefixes: Vec<Vec<BlockRef<D>>>,
}

impl<D: Digest> OrderingContext<D> {
    pub(crate) const fn new(
        epoch: Epoch,
        history: D,
        base: Vec<BlockRef<D>>,
        prefixes: Vec<Vec<BlockRef<D>>>,
    ) -> Self {
        Self {
            epoch,
            history,
            base,
            prefixes,
        }
    }

    /// Returns the producer epoch.
    pub const fn epoch(&self) -> Epoch {
        self.epoch
    }

    /// Returns the history commitment authenticating this range.
    pub const fn history(&self) -> D {
        self.history
    }

    /// Returns the per-chain frontier immediately before this context.
    pub fn base(&self) -> &[BlockRef<D>] {
        &self.base
    }

    /// Returns the certified inputs, in chain-ID order and increasing height on each chain.
    pub fn prefixes(&self) -> &[Vec<BlockRef<D>>] {
        &self.prefixes
    }
}

/// Selects the final cross-chain order of an authenticated history context.
///
/// Return every input block exactly once, preserving increasing height on each chain. There is
/// no required cross-chain order and no reservation for a block outside the context. Marshal
/// validates the complete result before admitting any of its outputs.
///
/// # Protocol contract
///
/// Calls must be bounded, synchronous, and return the same order for the same context on every
/// node, including history catch-up and restart. Use the same policy for the entire epoch and
/// storage namespace. Do not depend on arrival order, local execution progress, acknowledgement
/// timing, or mutable report collection. A report-based adapter must read the same frozen,
/// retained direction for the exact context on all nodes. This trait does not authenticate or
/// distribute application policy data.
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
/// // Install on every node with config.with_ordering(LaneMajor).
/// ```
pub trait Ordering<D: Digest>: Send + Sync + 'static {
    /// Returns a complete chain-order-preserving permutation of the context's blocks.
    fn order(&self, context: &OrderingContext<D>) -> Vec<BlockRef<D>>;
}

pub(crate) type Policy<D> = Option<Arc<dyn Ordering<D>>>;

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

pub(crate) fn validate<D: Digest>(
    context: &OrderingContext<D>,
    ordered: &[BlockRef<D>],
) -> Result<(), InvalidOrder> {
    if ordered.len() != context.prefixes.iter().map(Vec::len).sum::<usize>() {
        return Err(InvalidOrder::Length);
    }
    let mut next = vec![0; context.prefixes.len()];
    for reference in ordered {
        let chain = reference.chain().index();
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
}
