//! Custom delivery ordering implemented through consensus's public interface.

use commonware_consensus::multimmit::{
    marshal::{Ordering, OrderingContext},
    types::BlockRef,
};
use commonware_cryptography::Digest;
use serde::{Deserialize, Serialize};
use tracing::debug;

/// Delivery policy shared by every node and retained across restarts.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, clap::ValueEnum, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum OrderingMode {
    /// Use marshal's default proposed-first, offset-major traversal.
    #[default]
    Native,
    /// Deliver complete lane prefixes in descending chain-ID order.
    ReverseLanes,
}

/// Reorders lanes while preserving every block and each lane's increasing height.
pub struct ReverseLanes;

impl<D: Digest> Ordering<D> for ReverseLanes {
    fn order(&self, context: &OrderingContext<D>) -> Vec<BlockRef<D>> {
        let ordered = context
            .prefixes()
            .iter()
            .rev()
            .flatten()
            .copied()
            .collect::<Vec<_>>();
        debug!(
            history = %context.history(),
            order = ?ordered.iter().map(|block| (block.chain().get(), block.height().get())).collect::<Vec<_>>(),
            "custom ordering"
        );
        ordered
    }
}
