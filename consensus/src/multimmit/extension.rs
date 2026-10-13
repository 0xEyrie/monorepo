//! Application data carried and authenticated by leader proposals.

use crate::{
    multimmit::types::{Artifact, BlockRef, CertificateId, LeaderBlock},
    types::Round,
};
use bytes::Bytes;
use commonware_cryptography::{Digest, Hasher, bls12381::primitives::variant::Variant};
use core::fmt;

/// One producer chain's inputs to an application proposal extension.
pub struct ProposalChain<'a, D: Digest> {
    anchor: BlockRef<D>,
    payloads: &'a [D],
}

impl<'a, D: Digest> ProposalChain<'a, D> {
    /// Returns the explicit or DA-certified base of this chain proposal.
    pub const fn anchor(&self) -> BlockRef<D> {
        self.anchor
    }

    /// Returns the proposed body digests above the anchor, oldest first.
    pub const fn payloads(&self) -> &'a [D] {
        self.payloads
    }
}

/// Immutable native metadata bound to an application proposal extension.
///
/// Payload digests identify application bodies, not producer-header references. The application
/// must bind its extension to this exact round, parent, history and chain inputs.
pub struct ProposalContext<'a, D: Digest> {
    round: Round,
    parent: CertificateId<D>,
    history: D,
    chains: Vec<ProposalChain<'a, D>>,
}

impl<'a, D: Digest> ProposalContext<'a, D> {
    /// Projects a leader proposal using the epoch's configured hasher.
    pub fn new<H: Hasher<Digest = D>, V: Variant>(block: &'a LeaderBlock<V, D>) -> Self {
        Self {
            round: block.round(),
            parent: block.parent(),
            history: block.history(),
            chains: block
                .proposals()
                .iter()
                .map(|proposal| ProposalChain {
                    anchor: proposal.anchor().block_ref::<H>(),
                    payloads: proposal.payloads(),
                })
                .collect(),
        }
    }

    /// Returns the proposal's epoch and view.
    pub const fn round(&self) -> Round {
        self.round
    }

    /// Returns the proposal's parent V-QC identifier.
    pub const fn parent(&self) -> CertificateId<D> {
        self.parent
    }

    /// Returns the history commitment through the parent V-QC.
    pub const fn history(&self) -> D {
        self.history
    }

    /// Returns the proposed producer chains in ascending chain-ID order.
    pub fn chains(&self) -> &[ProposalChain<'a, D>] {
        &self.chains
    }
}

/// Constructs and validates application data authenticated by a leader proposal.
///
/// Use the same extension rules throughout an epoch and storage namespace on every node.
/// Calls must be bounded and synchronous, without I/O or transaction execution. Precompute any
/// reports needed to construct an extension. Verification must depend on the supplied data and
/// immutable protocol rules, never local report arrival or speculative execution progress.
///
/// Extension bytes are included in the leader digest, signatures, votes, certificates and durable
/// proposal records. A V-QC is view-exit evidence; final ordering still requires native L-QC
/// finality. This interface does not choose an ordering policy or implement Baton reports.
///
/// # Examples
///
/// Authenticate a round label alongside the native proposal:
///
/// ```
/// use bytes::Bytes;
/// use commonware_codec::Encode;
/// use commonware_cryptography::Digest;
/// use commonware_consensus::multimmit::{ProposalContext, ProposalExtension};
///
/// struct RoundLabel;
/// impl<D: Digest> ProposalExtension<D> for RoundLabel {
///     fn propose(&self, context: &ProposalContext<'_, D>) -> Option<Bytes> {
///         Some(context.round().encode())
///     }
///     fn verify(&self, context: &ProposalContext<'_, D>, extension: &Bytes) -> bool {
///         *extension == context.round().encode()
///     }
/// }
/// // Configure the epoch's bound, then install with config.with_proposal_extension(RoundLabel).
/// ```
pub trait ProposalExtension<D: Digest>: Send + Sync + 'static {
    /// Returns the extension for this proposal, or declines to propose at this time.
    ///
    /// Returning `None` leaves the normal view timeout active. Returned bytes must fit the
    /// epoch's proposal-extension bound and pass this implementation's verification rules.
    fn propose(&self, context: &ProposalContext<'_, D>) -> Option<Bytes>;

    /// Checks a complete extension against its exact proposal context.
    ///
    /// Returning `false` rejects the proposal or certificate before consensus admission.
    fn verify(&self, context: &ProposalContext<'_, D>, extension: &Bytes) -> bool;
}

impl<D: Digest> fmt::Debug for dyn ProposalExtension<D> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("ProposalExtension")
    }
}

/// Checks the application data in a complete leader proposal.
pub(crate) fn verify<H: Hasher, V: Variant>(
    policy: Option<&dyn ProposalExtension<H::Digest>>,
    block: &LeaderBlock<V, H::Digest>,
) -> bool {
    policy.map_or_else(
        || block.extension().is_empty(),
        |hook| hook.verify(&ProposalContext::new::<H, V>(block), block.extension()),
    )
}

/// Checks the application data carried by a proposal or its quorum certificate.
pub(crate) fn verify_artifact<H: Hasher, V: Variant>(
    policy: Option<&dyn ProposalExtension<H::Digest>>,
    artifact: &Artifact<V, H::Digest>,
) -> bool {
    match artifact {
        Artifact::LeaderBlock(block) => verify::<H, V>(policy, block.block()),
        Artifact::Vqc(certificate) => verify::<H, V>(policy, certificate.leader()),
        Artifact::Lqc(certificate) => verify::<H, V>(policy, certificate.leader()),
        _ => true,
    }
}
