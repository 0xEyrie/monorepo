//! Experimental persistence for application-defined final-vote extensions.
//!
//! These components do not establish agreement or change the stock engine.
//! The extension voter must verify recovery evidence and ancestry before using
//! them, then sign only after the corresponding durable operation succeeds.

#[cfg(not(target_arch = "wasm32"))]
pub mod fence;
pub mod recovery;
pub mod report;
pub mod request;
pub mod vote;

pub mod certificate;
#[cfg(not(target_arch = "wasm32"))]
pub use crate::simplex::actors::batcher::extensions::{
    Collector, Error as CollectError, Outcome as CollectOutcome,
};

#[cfg(not(target_arch = "wasm32"))]
pub mod coordinator;
pub mod recovery_wire;
