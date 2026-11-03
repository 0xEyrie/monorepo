//! Application data carried and authenticated by leader proposals.

use crate::{
    multimmit::types::{
        Anchor, Artifact, BlockRef, CertificateId, CodecConfig, LeaderBlock, TipRecord, VoteBody,
    },
    types::Round,
};
use bytes::Bytes;
use commonware_codec::{Codec, Decode as _, Encode as _};
use commonware_cryptography::{Digest, Hasher, bls12381::primitives::variant::Variant};
use core::fmt;

/// One producer chain's inputs to an application proposal extension.
pub struct ProposalChain<'a, D: Digest> {
    anchor: BlockRef<D>,
    anchor_parent: Option<BlockRef<D>>,
    payloads: &'a [D],
}

impl<'a, D: Digest> ProposalChain<'a, D> {
    /// Returns the explicit or DA-certified base of this chain proposal.
    pub const fn anchor(&self) -> BlockRef<D> {
        self.anchor
    }

    /// Returns the certified anchor header's exact parent, when the anchor carries a certificate.
    /// An inherited safe tip has no header in this proposal and returns `None`.
    pub const fn anchor_parent(&self) -> Option<BlockRef<D>> {
        self.anchor_parent
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
    parent_tips: Option<&'a [BlockRef<D>]>,
    parent_record: Option<&'a TipRecord<D>>,
}

impl<'a, D: Digest> ProposalContext<'a, D> {
    /// Projects a leader proposal using the epoch's configured hasher.
    pub fn new<H: Hasher<Digest = D>, V: Variant>(block: &'a LeaderBlock<V, D>) -> Self {
        Self {
            round: block.round(),
            parent: block.parent(),
            history: block.history(),
            parent_tips: None,
            parent_record: None,
            chains: block
                .proposals()
                .iter()
                .map(|proposal| ProposalChain {
                    anchor: proposal.anchor().block_ref::<H>(),
                    anchor_parent: match proposal.anchor() {
                        Anchor::Certificate(certificate) => Some(certificate.header().parent_ref()),
                        Anchor::Tip(_) => None,
                    },
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

    /// Returns the authenticated safe frontier of this proposal's parent V-QC.
    ///
    /// Present during local construction, parent-dependent validation and vote reporting. Initial
    /// artifact validation can precede parent resolution and leaves this value absent.
    pub const fn parent_tips(&self) -> Option<&[BlockRef<D>]> {
        self.parent_tips
    }

    /// Returns the exact history opening of the resolved proposal parent.
    ///
    /// Local construction and parent-dependent validation borrow this record from native
    /// certificate validation. Its commitment equals `history()` and its tips equal
    /// `parent_tips()`. Original designated vote reports remain unchanged. Initial artifact
    /// verification and vote-report construction omit it; absence grants no authority.
    pub const fn parent_record(&self) -> Option<&TipRecord<D>> {
        self.parent_record
    }

    pub(crate) fn with_parent_record(mut self, record: &'a TipRecord<D>) -> Self {
        self.parent_tips = Some(record.tips());
        self.parent_record = Some(record);
        self
    }

    pub(crate) const fn with_parent_tips(mut self, tips: &'a [BlockRef<D>]) -> Self {
        self.parent_tips = Some(tips);
        self
    }
}

/// Constructs and validates application data authenticated by a leader proposal.
///
/// Use the same extension rules throughout an epoch and storage namespace on every node.
/// Calls must be bounded and synchronous, without I/O or transaction execution. Precompute any
/// reports needed to construct an extension. Verification must depend on the supplied data and
/// immutable protocol rules, never local report arrival or speculative execution progress.
///
/// Configure the same `T: commonware_codec::Codec` and codec bounds in the engine and Marshal.
/// Builders use its existing codec; callbacks exchange typed values and need no serialization code.
/// The wire value is the codec encoding of `Some(T)`; an empty native extension denotes absence.
///
/// Extension data is included in the leader digest, signatures, votes, certificates and durable
/// proposal records. A V-QC is view-exit evidence; final ordering still requires native L-QC
/// finality. This interface does not choose an ordering policy or implement Baton reports.
///
/// # Examples
///
/// Authenticate a round label alongside the native proposal:
///
/// ```
/// use commonware_cryptography::Digest;
/// use commonware_consensus::multimmit::{ProposalContext, ProposalExtension};
/// use commonware_consensus::types::Round;
///
/// struct RoundLabel;
/// impl<D: Digest> ProposalExtension<D, Round> for RoundLabel {
///     fn propose(&self, context: &ProposalContext<'_, D>) -> Option<Round> {
///         Some(context.round())
///     }
///     fn verify(&self, context: &ProposalContext<'_, D>, extension: &Round) -> bool {
///         *extension == context.round()
///     }
/// }
/// // Configure the epoch's byte bound, then use config.with_proposal_extension(RoundLabel, ()).
/// ```
pub trait ProposalExtension<D: Digest, T = Bytes>: Send + Sync + 'static {
    /// Snapshots an optional local report for the completed ordinary vote body.
    ///
    /// The ordinary signature authenticates these bytes together with the exact round,
    /// leader digest, positions and extensions. This is not approval of a subsequently
    /// selected order. The call must be bounded and synchronous; unavailable or oversize
    /// reports are omitted without delaying native voting. Returned bytes use the
    /// application's report codec, independently of the proposal's `T` codec.
    fn vote(&self, _context: &ProposalContext<'_, D>, _body: &VoteBody<D>) -> Bytes {
        Bytes::new()
    }

    /// Suggests held DA-certified anchors together with their immutable application policy.
    ///
    /// The context describes the default native proposal and its actual parent. Requested
    /// anchors must be in ascending, distinct chain order. Unmentioned chains keep their
    /// native choices. The engine uses only exact parent tips or certificates it already holds;
    /// an unavailable or invalid plan falls back before signing, without fetching or waiting.
    fn plan(&self, _context: &ProposalContext<'_, D>) -> Option<ProposalPlan<D, T>> {
        None
    }

    /// Returns the extension for this proposal, or declines to propose at this time.
    ///
    /// Returning `None` leaves the normal view timeout active. Encoded values must fit the
    /// epoch's proposal-extension bound and pass this implementation's verification rules.
    fn propose(&self, context: &ProposalContext<'_, D>) -> Option<T>;

    /// Checks a complete extension against its exact proposal context.
    ///
    /// Returning `false` rejects the proposal or certificate before consensus admission.
    fn verify(&self, context: &ProposalContext<'_, D>, extension: &T) -> bool;

    /// Checks application constraints against the resolved native parent before a direct vote.
    ///
    /// The context contains the actual safe parent tips, not the proposal's newer anchors.
    /// This bounded check must use only supplied evidence and immutable epoch rules. It runs
    /// after ordinary native parent validation; it cannot replace tip extraction or ancestry
    /// validation. A certified rescue vote relies on the original quorum's direct checks.
    fn verify_parent(&self, _context: &ProposalContext<'_, D>, _extension: &T) -> bool {
        true
    }
}

/// An optional proposal input selection and the policy frozen with that selection.
///
/// This local suggestion grants no finality. The engine resolves native certificates and
/// validates the resulting proposal before signing it. Vote extension and extraction rules
/// remain unchanged.
pub struct ProposalPlan<D: Digest, T> {
    /// Exact requested anchors, in ascending distinct chain order.
    pub anchors: Vec<BlockRef<D>>,
    /// Application data to authenticate with the resulting native proposal.
    pub extension: T,
}

struct Configured<P, T: Codec> {
    extension: P,
    codec: T::Cfg,
}

impl<D, P, T> ProposalExtension<D> for Configured<P, T>
where
    D: Digest,
    P: ProposalExtension<D, T>,
    T: Codec + 'static,
    T::Cfg: Send + Sync + 'static,
{
    fn vote(&self, context: &ProposalContext<'_, D>, body: &VoteBody<D>) -> Bytes {
        self.extension.vote(context, body)
    }

    fn plan(&self, context: &ProposalContext<'_, D>) -> Option<ProposalPlan<D, Bytes>> {
        self.extension.plan(context).map(|plan| ProposalPlan {
            anchors: plan.anchors,
            extension: Some(plan.extension).encode(),
        })
    }

    fn propose(&self, context: &ProposalContext<'_, D>) -> Option<Bytes> {
        self.extension
            .propose(context)
            .map(|value| Some(value).encode())
    }

    fn verify(&self, context: &ProposalContext<'_, D>, extension: &Bytes) -> bool {
        Option::<T>::decode_cfg(extension.clone(), &self.codec)
            .ok()
            .flatten()
            .is_some_and(|value| self.extension.verify(context, &value))
    }

    fn verify_parent(&self, context: &ProposalContext<'_, D>, extension: &Bytes) -> bool {
        Option::<T>::decode_cfg(extension.clone(), &self.codec)
            .ok()
            .flatten()
            .is_some_and(|value| self.extension.verify_parent(context, &value))
    }
}

pub(crate) fn policy<D, P, T>(
    extension: P,
    codec: T::Cfg,
) -> std::sync::Arc<dyn ProposalExtension<D>>
where
    D: Digest,
    P: ProposalExtension<D, T>,
    T: Codec + 'static,
    T::Cfg: Send + Sync + 'static,
{
    std::sync::Arc::new(Configured::<P, T> { extension, codec })
}

impl<D: Digest> fmt::Debug for dyn ProposalExtension<D> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("ProposalExtension")
    }
}

/// Freezes an optional local report with one completed ordinary vote body.
pub(crate) fn vote<H: Hasher, V: Variant>(
    policy: Option<&dyn ProposalExtension<H::Digest>>,
    block: &LeaderBlock<V, H::Digest>,
    parent_tips: Option<&[BlockRef<H::Digest>]>,
    body: VoteBody<H::Digest>,
    codec: CodecConfig,
) -> VoteBody<H::Digest> {
    let Some(policy) = policy else {
        return body;
    };
    let mut context = ProposalContext::new::<H, V>(block);
    if let Some(tips) = parent_tips {
        context = context.with_parent_tips(tips);
    }
    let report = policy.vote(&context, &body);
    // Optional local reporting must not suppress a native vote.
    if report.len() > codec.proposal_extension_bound() {
        return body;
    }
    body.clone().with_application(report, codec).unwrap_or(body)
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
