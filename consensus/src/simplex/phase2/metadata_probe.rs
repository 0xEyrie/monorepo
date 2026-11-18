//! Private duplicate-classification fixture with a genuine native signature.
//!
//! Only the fixed-size hint is unauthenticated. The certificate remains Plain,
//! so this fixture makes no claim about G1 paired-certificate admission.
use super::*;
use crate::types::{Epoch, Participant, Round, View};
use aggregation::{Aggregation, Batch, FinalBuffer};
use bytes::BufMut;
use commonware_codec::{Buf, ReadExt as _};
use std::sync::Arc;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Metadata;
impl sealed::Sealed for Metadata {}

#[derive(Clone, Debug)]
pub(crate) struct Vote<S: Scheme, D: Digest> {
    pub native: Finalize<S, D>,
    pub hint: D,
}
impl<S: Scheme, D: Digest> PartialEq for Vote<S, D> {
    fn eq(&self, other: &Self) -> bool {
        self.native == other.native && self.hint == other.hint
    }
}
impl<S: Scheme, D: Digest> Write for Vote<S, D> {
    fn write(&self, writer: &mut impl BufMut) {
        self.native.write(writer);
        self.hint.write(writer);
    }
}
impl<S: Scheme, D: Digest> EncodeSize for Vote<S, D> {
    fn encode_size(&self) -> usize {
        self.native.encode_size() + self.hint.encode_size()
    }
}
impl<S: Scheme, D: Digest> Read for Vote<S, D> {
    type Cfg = ();
    fn read_cfg(reader: &mut impl Buf, _: &()) -> Result<Self, commonware_codec::Error> {
        Ok(Self {
            native: Finalize::read(reader)?,
            hint: D::read(reader)?,
        })
    }
}
impl<S: Scheme, D: Digest> Attributable for Vote<S, D> {
    fn signer(&self) -> Participant {
        self.native.signer()
    }
}
impl<S: Scheme, D: Digest> Epochable for Vote<S, D> {
    fn epoch(&self) -> Epoch {
        self.native.epoch()
    }
}
impl<S: Scheme, D: Digest> Viewable for Vote<S, D> {
    fn view(&self) -> View {
        self.native.view()
    }
}

impl<S: Scheme, D: Digest> Mode<S, D> for Metadata {
    const RETAIN_INTERPRETATION: bool = true;
    type Assembly = super::recovery::NoRecovery;
    fn assembly_proposal(value: &Self::Assembly) -> &Proposal<D> {
        match *value {}
    }
    fn assembly_size(value: &Self::Assembly) -> usize {
        match *value {}
    }
    type Recovery = recovery::NoRecovery;
    type Recovered = recovery::NoRecovery;
    fn read_recovered(
        reader: &mut impl Buf,
        cfg: &<S::Certificate as Read>::Cfg,
    ) -> Result<Self::Recovered, commonware_codec::Error> {
        <Plain as Mode<S, D>>::read_recovered(reader, cfg)
    }
    fn recovered_proposal(certificate: &Self::Recovered) -> &Proposal<D> {
        <Plain as Mode<S, D>>::recovered_proposal(certificate)
    }
    fn verify_recovered<R: CryptoRng>(
        certificate: &Self::Recovered,
        rng: &mut R,
        scheme: &S,
        strategy: &impl Strategy,
    ) -> bool
    where
        S: scheme::Scheme<D>,
    {
        <Plain as Mode<S, D>>::verify_recovered(certificate, rng, scheme, strategy)
    }
    type QueryResult = Self::RecoveryRequest;
    type RecoveryQuery = recovery::NoRecovery;
    type RecoveryRequest = recovery::NoRecovery;
    type RecoveryResponse = recovery::NoRecovery;
    fn recovery_query_view(query: &Self::RecoveryQuery) -> View {
        <Plain as Mode<S, D>>::recovery_query_view(query)
    }
    fn recovery_view(request: &Self::RecoveryRequest) -> View {
        <Plain as Mode<S, D>>::recovery_view(request)
    }
    fn notarize(vote: &Self::Notarize) -> &Notarize<S, D> {
        vote
    }
    fn into_notarize(vote: Self::Notarize) -> Notarize<S, D> {
        vote
    }
    fn finalize_proposal(vote: &Self::Vote) -> &Proposal<D> {
        &vote.native.proposal
    }
    fn finalization_proposal(certificate: &Self::Certificate) -> &Proposal<D> {
        &certificate.proposal
    }
    fn finalization_certificate(certificate: &Self::Certificate) -> &S::Certificate {
        &certificate.certificate
    }
    fn signed_finalization_subject(certificate: &Self::Certificate) -> Subject<'_, D> {
        <Plain as Mode<S, D>>::signed_finalization_subject(certificate)
    }
    fn verify_companion<R: CryptoRng>(
        certificate: &Self::Certificate,
        rng: &mut R,
        scoped: &Scoped<S>,
        strategy: &impl Strategy,
    ) -> bool
    where
        S: scheme::Scheme<D>,
    {
        <Plain as Mode<S, D>>::verify_companion(certificate, rng, scoped, strategy)
    }
    fn conflicting_finalize_subjects(a: &Self::Vote, b: &Self::Vote) -> bool {
        a.native.proposal != b.native.proposal
    }
    fn equivalent_finalize(a: &Self::Vote, b: &Self::Vote) -> bool {
        a.native == b.native
    }
    fn verify_finalize<R: CryptoRng>(
        vote: &Self::Vote,
        rng: &mut R,
        scheme: &S,
        strategy: &impl Strategy,
    ) -> bool
    where
        S: scheme::Scheme<D>,
    {
        vote.native.verify(rng, scheme, strategy)
    }
    type Notarize = Notarize<S, D>;
    type Vote = Vote<S, D>;
    type Certificate = Finalization<S, D>;
    fn verify<R: CryptoRng>(
        certificate: &Self::Certificate,
        rng: &mut R,
        scheme: &S,
        strategy: &impl Strategy,
    ) -> bool
    where
        S: scheme::Scheme<D>,
    {
        certificate.verify(rng, scheme, strategy)
    }
}

type NativeBuffer<S, D> = <Plain as Aggregation<S, D>>::FinalBuffer;
pub(crate) struct Buffer<S: scheme::Scheme<D>, D: Digest>(NativeBuffer<S, D>);
impl<S: scheme::Scheme<D>, D: Digest> Aggregation<S, D> for Metadata {
    type FinalBuffer = Buffer<S, D>;
}
impl<S: scheme::Scheme<D>, D: Digest> FinalBuffer<S, D> for Buffer<S, D> {
    type Vote = Vote<S, D>;
    type Certificate = Finalization<S, D>;
    type Assembly = super::recovery::NoRecovery;
    fn new(quorum: usize, participants: usize) -> Self {
        Self(<NativeBuffer<S, D> as FinalBuffer<S, D>>::new(
            quorum,
            participants,
        ))
    }
    fn push(&mut self, vote: Self::Vote, verified: bool) {
        self.0.push(vote.native, verified);
    }
    fn retain_proposal(&mut self, proposal: &Proposal<D>) {
        self.0.retain_proposal(proposal);
    }
    fn complete(&mut self) {
        self.0.complete();
    }
    fn is_complete(&self) -> bool {
        self.0.is_complete()
    }
    fn has_constructable_quorum(&self) -> bool {
        self.0.has_constructable_quorum()
    }
    async fn construct<R: CryptoRng + Send>(
        &mut self,
        scheme: &Arc<S>,
        round: Round,
        rng: &mut R,
        strategy: &impl Strategy,
    ) -> Option<Batch<Self::Certificate>> {
        self.0.construct(scheme, round, rng, strategy).await
    }
}
