//! Immutable application-checked material for original paired aggregation.
//!
//! Construction validates the supplied local policy. It grants no native
//! eligibility, signing, custody, finality or delivery permission.

use super::{
    Certificate, CertificateSigners, Core, Decision, Error, First, Limits, Origin, OriginBody,
    Quorum, VerificationSource, VerifiedRows, Vote, message, scheme, subject,
};
use crate::{
    Epochable, Viewable,
    simplex::{
        extension::vote,
        types::{Notarization, Proposal, Subject},
    },
    types::{Epoch, View},
};
use bytes::Bytes;
use commonware_codec::{Decode as _, Encode as _, EncodeSize};
use commonware_cryptography::{
    Digest, Hasher,
    certificate::{Scoped, Verifier as _},
};
use commonware_parallel::Strategy;
use commonware_utils::iter::NonEmpty;
use rand_core::CryptoRng;
use std::{collections::BTreeSet, sync::Arc};

const ID: &[u8] = b"_COMMONWARE_CONSENSUS_G1_NORMAL_ASSEMBLY_V1";

#[derive(Debug)]
struct Material<S: scheme::Scheme<D>, D: Digest> {
    origin: Origin<S, D>,
    notarization: Notarization<S, D>,
    limits: Limits,
    id: D,
    route: Option<super::super::VerifiedBody<D>>,
    origin_bytes: Bytes,
    notarization_bytes: Bytes,
}

/// Private-constructor, immutable application meaning and genuine native NQC.
/// Clones share compact owned material. There is deliberately no wire decoder.
#[derive(Debug)]
pub struct Assembly<S: scheme::Scheme<D>, D: Digest>(Arc<Material<S, D>>);

impl<S: scheme::Scheme<D>, D: Digest> Clone for Assembly<S, D> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<S: scheme::Scheme<D>, D: Digest> PartialEq for Assembly<S, D> {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
            || (self.0.limits == other.0.limits
                && self.0.origin_bytes == other.0.origin_bytes
                && self.0.notarization_bytes == other.0.notarization_bytes)
    }
}
impl<S: scheme::Scheme<D>, D: Digest> Eq for Assembly<S, D> {}

impl<S: scheme::Scheme<D>, D: Digest> Assembly<S, D>
where
    S::Certificate: CertificateSigners,
{
    /// Verifies trusted context, complete application policy and an exact-P NQC,
    /// then detaches retained material from caller-owned capacities/backing.
    #[allow(clippy::too_many_arguments)]
    pub fn new<H: Hasher<Digest = D>, R: CryptoRng>(
        rng: &mut R,
        s: &S,
        core: &Core<D>,
        input: D,
        origin: Origin<S, D>,
        notarization: Notarization<S, D>,
        limits: Limits,
        validate_row: impl FnMut(&First<D>) -> bool,
        validate_build: impl FnOnce(&VerifiedRows<S, D>, &OriginBody<S, D>) -> bool,
        strategy: &impl Strategy,
    ) -> Result<Self, Error> {
        Self::new_with::<H, R>(
            rng,
            &VerificationSource::Scheme(s),
            core,
            origin,
            notarization,
            limits,
            &s.certificate_codec_config(),
            None,
            |rng, source, origin| {
                origin
                    .verify_with::<H, R>(
                        rng,
                        source,
                        core,
                        input,
                        limits,
                        validate_row,
                        validate_build,
                        strategy,
                    )
                    .map(|_| ())
            },
            strategy,
        )
    }

    /// Same application validation through a captured public-only epoch scope.
    #[allow(clippy::too_many_arguments)]
    pub fn new_scoped<H: Hasher<Digest = D>, R: CryptoRng>(
        rng: &mut R,
        s: &Scoped<S>,
        core: &Core<D>,
        input: D,
        origin: Origin<S, D>,
        notarization: Notarization<S, D>,
        limits: Limits,
        validate_row: impl FnMut(&First<D>) -> bool,
        validate_build: impl FnOnce(&VerifiedRows<S, D>, &OriginBody<S, D>) -> bool,
        strategy: &impl Strategy,
    ) -> Result<Self, Error> {
        Self::new_with::<H, R>(
            rng,
            &VerificationSource::Scoped(s),
            core,
            origin,
            notarization,
            limits,
            &s.certificate_codec_config(),
            None,
            |rng, source, origin| {
                origin
                    .verify_with::<H, R>(
                        rng,
                        source,
                        core,
                        input,
                        limits,
                        validate_row,
                        validate_build,
                        strategy,
                    )
                    .map(|_| ())
            },
            strategy,
        )
    }

    /// Build normal vote material from an exact route-policy token, the elected
    /// leader's signed origin and a genuine notarization for its proposal.
    pub fn from_route<H: Hasher<Digest = D>, R: CryptoRng>(
        rng: &mut R,
        scheme: &S,
        origin: Origin<S, D>,
        notarization: Notarization<S, D>,
        cap: super::super::VerifiedBody<D>,
        strategy: &impl Strategy,
    ) -> Result<Self, Error> {
        if cap.route_scope().is_none() {
            return Err(Error::Policy);
        }
        origin.preflight(
            super::super::committee::<S>(&VerificationSource::Scheme(scheme))?,
            cap.limits(),
        )?;
        let core = origin.body.core.clone();
        Self::new_with::<H, R>(
            rng,
            &VerificationSource::Scheme(scheme),
            &core,
            origin,
            notarization,
            cap.limits(),
            &scheme.certificate_codec_config(),
            Some(cap.clone()),
            |rng, _, origin| origin.verify_route_endorsement::<H, R>(rng, scheme, &cap, strategy),
            strategy,
        )
    }

    /// Locally checked original FIRST scope for a route-based assembly.
    pub fn route_authority(&self) -> Option<&super::super::VerifiedBody<D>> {
        self.0.route.as_ref()
    }
    #[allow(clippy::too_many_arguments)]
    fn new_with<H: Hasher<Digest = D>, R: CryptoRng>(
        rng: &mut R,
        s: &VerificationSource<'_, S>,
        core: &Core<D>,
        origin: Origin<S, D>,
        notarization: Notarization<S, D>,
        limits: Limits,
        certificate_cfg: &<S::Certificate as commonware_codec::Read>::Cfg,
        route: Option<super::super::VerifiedBody<D>>,
        verify_origin: impl FnOnce(
            &mut R,
            &VerificationSource<'_, S>,
            &Origin<S, D>,
        ) -> Result<(), Error>,
        strategy: &impl Strategy,
    ) -> Result<Self, Error> {
        // Reject dynamic shape before encode_size, hashing or compact copies.
        let committee = super::super::committee::<S>(s)?;
        if core.followers.len() > 63 || notarization.certificate.signers().len() > 64 {
            return Err(Error::Limit);
        }
        limits.validate::<S, D>(core)?;
        origin.preflight(committee, limits)?;
        if notarization.encode_size() > super::super::NATIVE_BYTES {
            return Err(Error::Limit);
        }
        core.check::<H, S>(s)?;
        if notarization.proposal != core.slot.proposal {
            return Err(Error::Context);
        }
        // A genuine original Notarize subject also authenticates the native
        // election seed; a final-role QC is not a substitute for this witness.
        if !s.verify_certificate::<_, D>(
            rng,
            Subject::Notarize {
                proposal: &notarization.proposal,
            },
            &notarization.certificate,
            strategy,
        ) {
            return Err(Error::Signature);
        }
        verify_origin(rng, s, &origin)?;

        // Fresh exact-size encodings discard oversized Vec capacities and any
        // unrelated backing hidden behind incoming Bytes slices.
        let origin_bytes = origin.encode();
        let notarization_bytes = notarization.encode();
        let origin = Origin::decode_cfg(origin_bytes.clone(), &limits).map_err(|_| Error::Limit)?;
        let notarization = Notarization::decode_cfg(notarization_bytes.clone(), certificate_cfg)
            .map_err(|_| Error::Limit)?;
        let mut encoded_limits = [0u8; 40];
        for (chunk, value) in encoded_limits.chunks_exact_mut(8).zip([
            limits.report_bytes,
            limits.order_bytes,
            limits.build_bytes,
            limits.material_bytes,
            limits.origin_bytes,
        ]) {
            let value = u64::try_from(value).map_err(|_| Error::Limit)?;
            chunk.copy_from_slice(&value.to_be_bytes());
        }
        let nqc_len = u32::try_from(notarization_bytes.len()).map_err(|_| Error::Limit)?;
        let id = H::hash(&[
            ID,
            &encoded_limits,
            &origin_bytes,
            &nqc_len.to_be_bytes(),
            &notarization_bytes,
        ]);
        Ok(Self(Arc::new(Material {
            origin,
            notarization,
            limits,
            id,
            route,
            origin_bytes,
            notarization_bytes,
        })))
    }

    /// Exact trusted original Core whose application meaning was checked.
    pub fn core(&self) -> &Core<D> {
        &self.0.origin.body.core
    }
    /// Exact immutable semantic decision, independent of final signers' hints.
    pub fn decision(&self) -> &Decision<D> {
        &self.0.origin.body.decision
    }
    /// Public input commitment validated during construction.
    pub fn input(&self) -> D {
        self.decision().input
    }
    /// Locally supplied bounds used for the retained validation.
    pub fn limits(&self) -> Limits {
        self.0.limits
    }
    /// Content identity of exact canonical material and all five limits.
    pub fn id(&self) -> D {
        self.0.id
    }
    /// Canonical retained Origin plus NQC byte charge. Decoded containers and
    /// allocator bookkeeping are additionally bounded by their admitted shapes.
    pub fn retained_bytes(&self) -> usize {
        self.0.origin_bytes.len() + self.0.notarization_bytes.len()
    }
    /// Exact original native proposal; this is not a new eligibility verdict.
    pub fn proposal(&self) -> &Proposal<D> {
        &self.core().slot.proposal
    }

    /// Exact retained original authority, including its original SELECT bytes.
    /// Reading this raw material grants no new signing or native eligibility.
    pub fn origin(&self) -> &Origin<S, D> {
        &self.0.origin
    }

    /// Genuine original-P election witness retained by this capability.
    pub fn notarization(&self) -> &Notarization<S, D> {
        &self.0.notarization
    }

    /// Constructs both QCs from exactly q distinct complete same-subject pairs.
    /// Application authority comes from this immutable material's constructor;
    /// no replacement policy callbacks are used during aggregation.
    pub fn assemble<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &S,
        votes: &[Vote<S, D>],
        strategy: &impl Strategy,
    ) -> Result<Certificate<S, D>, Error> {
        let committee = self.core().check::<H, S>(&VerificationSource::Scheme(s))?;
        if votes.len() != committee.quorum() {
            return Err(Error::Quorum);
        }
        let mut owners = BTreeSet::new();
        for pair in votes {
            if !owners.insert(pair.native.attestation.signer) {
                return Err(Error::Identity);
            }
            if !pair.verify::<H, R>(
                rng,
                s,
                self.core(),
                self.input(),
                self.decision(),
                self.limits(),
                strategy,
            ) {
                return Err(Error::Signature);
            }
        }
        let mut native = votes.iter().map(|v| v.native.clone());
        let native = vote::Certificate::from_votes(
            rng,
            s,
            NonEmpty::new(native.next().ok_or(Error::Quorum)?, native),
            strategy,
        )
        .map_err(|_| Error::Signature)?;
        let agreement = Quorum::from_votes(
            rng,
            s,
            &votes
                .iter()
                .map(|v| v.agreement.clone())
                .collect::<Vec<_>>(),
            self.limits(),
            strategy,
        )?;
        let result = Certificate {
            native,
            agreement,
            notarization: self.0.notarization.clone(),
            origin: self.0.origin.clone(),
        };
        if result.native.statement != subject::<H>(self.decision())
            || result.agreement.message != message::<H>(self.core(), self.decision().id::<H>())
        {
            return Err(Error::Context);
        }
        result.authenticate::<H, R>(rng, s, self.limits(), strategy)?;
        Ok(result)
    }
}

impl<S: scheme::Scheme<D>, D: Digest> Epochable for Assembly<S, D> {
    fn epoch(&self) -> Epoch {
        self.0.origin.body.core.slot.proposal.round.epoch()
    }
}
impl<S: scheme::Scheme<D>, D: Digest> Viewable for Assembly<S, D> {
    fn view(&self) -> View {
        self.0.origin.body.core.slot.proposal.round.view()
    }
}
