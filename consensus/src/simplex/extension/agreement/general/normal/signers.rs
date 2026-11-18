//! Public signer metadata for the attributable G1 normal certificate profile.
//!
//! A bitmap is a claim until its certificate verifies for the exact signed
//! subject and epoch roster. This capability provides neither verification nor
//! signing, and threshold certificates without attributable owners do not
//! implement it.

use commonware_cryptography::{
    bls12381::{certificate::multisig, primitives::variant::Variant},
    certificate::Signers,
    ed25519, secp256r1,
};

/// Reads the signer bitmap authenticated by successful certificate verification.
///
/// Consumers must first verify the certificate under its exact subject and
/// scope. They then check the bitmap width against the captured roster and its
/// count against the native quorum before comparing two certificate owner sets.
pub trait CertificateSigners {
    /// Claimed signer indices, without granting certificate or signing authority.
    fn signers(&self) -> &Signers;
}

impl CertificateSigners for ed25519::certificate::Certificate {
    fn signers(&self) -> &Signers {
        &self.signers
    }
}

impl CertificateSigners for secp256r1::certificate::Certificate {
    fn signers(&self) -> &Signers {
        &self.signers
    }
}

impl<V: Variant> CertificateSigners for multisig::Certificate<V> {
    fn signers(&self) -> &Signers {
        &self.signers
    }
}
