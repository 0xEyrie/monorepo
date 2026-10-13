//! Custom delivery ordering implemented through consensus's public interface.

use commonware_consensus::multimmit::{
    marshal::{Ordering, OrderingContext},
    types::BlockRef,
};
use commonware_cryptography::Digest;

/// Reorders lanes while preserving every block and each lane's increasing height.
pub struct ReverseLanes;

impl<D: Digest> Ordering<D> for ReverseLanes {
    fn order(&self, context: &OrderingContext<D>) -> Vec<BlockRef<D>> {
        context.prefixes().iter().rev().flatten().copied().collect()
    }
}
