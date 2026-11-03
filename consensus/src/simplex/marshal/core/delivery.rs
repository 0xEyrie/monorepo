use super::Variant;
use crate::simplex::{
    phase2::{Mode, Plain},
    scheme::Scheme,
    types::Notarization,
};
use commonware_cryptography::certificate::{Scheme as CertificateScheme, Scoped};
use commonware_utils::channel::oneshot;

/// A parsed-but-unverified resolver delivery awaiting batch certificate verification.
///
/// Each item carries the scope it was admitted under so verification does not
/// depend on the provider still serving that epoch.
pub(super) enum PendingVerification<
    S: CertificateScheme,
    V: Variant,
    M: Mode<S, V::Commitment> = Plain,
> where
    S: Scheme<V::Commitment>,
{
    Notarized {
        scoped: Scoped<S>,
        notarization: Notarization<S, V::Commitment>,
        block: V::Block,
        response: oneshot::Sender<bool>,
    },
    Finalized {
        scoped: Scoped<S>,
        finalization: M::Certificate,
        block: V::ApplicationBlock,
        response: oneshot::Sender<bool>,
    },
}

impl<S: CertificateScheme, V: Variant, M: Mode<S, V::Commitment>> PendingVerification<S, V, M>
where
    S: Scheme<V::Commitment>,
{
    /// Returns the scope the delivery was admitted under.
    pub(super) const fn scoped(&self) -> &Scoped<S> {
        match self {
            Self::Notarized { scoped, .. } | Self::Finalized { scoped, .. } => scoped,
        }
    }

    pub(super) fn response_closed(&self) -> bool {
        match self {
            Self::Notarized { response, .. } | Self::Finalized { response, .. } => {
                response.is_closed()
            }
        }
    }
}
