//! Static vote and certificate representation selection.
//!
//! `Plain` uses the existing vote/certificate types without optional fields,
//! extra allocations or wire changes. The ALPHA extended representation retains
//! its complete signed statement. This selects representation and authentication,
//! not application policy, native eligibility or a live engine configuration.

use super::{
    scheme,
    types::{Finalization, Finalize, Notarize, Proposal, Subject},
};
use crate::{Epochable, Viewable, types::Attributable};
use commonware_codec::{EncodeSize, Read, Write};
use commonware_cryptography::{Digest, certificate::Scheme};
use commonware_parallel::Strategy;
use rand_core::CryptoRng;
use std::fmt::Debug;

pub mod recovery;

mod sealed {
    pub trait Sealed {}
}

/// Native-controlled vote and certificate representations. Applications provide opaque
/// extension policy separately; they cannot replace phase signing domains here.
pub trait Mode<S: Scheme, D: Digest>:
    sealed::Sealed + Clone + Debug + PartialEq + Send + Sync + 'static
{
    /// Keeps report and interpretation evidence until the containing view is pruned.
    /// Compact proposal-match bits alone cannot represent extension subjects.
    const RETAIN_INTERPRETATION: bool;
    /// Local slow-path decision encoded in the native journal; uninhabited in Plain.
    type Recovery: Clone
        + Debug
        + PartialEq
        + Write
        + EncodeSize
        + Read<Cfg = ()>
        + Epochable
        + Viewable
        + Send
        + Sync
        + 'static;
    /// Later-ballot interpretation witness, never an original finalization.
    type Recovered: Clone
        + Debug
        + PartialEq
        + Write
        + EncodeSize
        + Epochable
        + Viewable
        + Send
        + Sync
        + 'static;
    fn read_recovered(
        reader: &mut impl commonware_codec::Buf,
        cfg: &<S::Certificate as Read>::Cfg,
    ) -> Result<Self::Recovered, commonware_codec::Error>;
    fn recovered_proposal(certificate: &Self::Recovered) -> &Proposal<D>;
    /// Checks the native recovery roster and authenticates the quorum certificate.
    fn verify_recovered<R: CryptoRng>(
        certificate: &Self::Recovered,
        rng: &mut R,
        scheme: &S,
        strategy: &impl Strategy,
    ) -> bool
    where
        S: scheme::Scheme<D>;
    /// Native recovery mailbox request; uninhabited in Plain.
    type RecoveryRequest: Send + 'static;
    /// Local coordinator query; uninhabited in Plain.
    type RecoveryQuery: Send + 'static;
    fn recovery_query_view(query: &Self::RecoveryQuery) -> crate::types::View;
    /// Reply released only after the native journal sync barrier.
    type RecoveryResponse: Send + 'static;
    fn recovery_view(request: &Self::RecoveryRequest) -> crate::types::View;
    /// Ordinary notarize subject, without treating report bytes as its signature.
    fn notarize(vote: &Self::Notarize) -> &Notarize<S, D>;
    /// Moves the base vote into native verification; the tracker retains reports.
    fn into_notarize(vote: Self::Notarize) -> Notarize<S, D>;
    /// Original proposal referenced by the exact final vote.
    fn finalize_proposal(vote: &Self::Vote) -> &Proposal<D>;
    /// Original proposal referenced by an original-round certificate.
    fn finalization_proposal(certificate: &Self::Certificate) -> &Proposal<D>;
    /// Native certificate used by the existing leader-election scheme.
    fn finalization_certificate(certificate: &Self::Certificate) -> &S::Certificate;
    /// Exact signed phase-two subject, retaining extension interpretation bytes.
    fn signed_finalization_subject(certificate: &Self::Certificate) -> Subject<'_, D>;
    /// Different signed subjects in the same protocol domain. The evidence
    /// constructor separately checks the same round and participant.
    fn conflicting_finalize_subjects(a: &Self::Vote, b: &Self::Vote) -> bool;
    /// Authenticates an individual final vote over its exact native subject.
    fn verify_finalize<R: CryptoRng>(
        vote: &Self::Vote,
        rng: &mut R,
        scheme: &S,
        strategy: &impl Strategy,
    ) -> bool
    where
        S: scheme::Scheme<D>;
    /// First vote, optionally carrying a separately authenticated report.
    type Notarize: Attributable
        + Clone
        + Debug
        + PartialEq
        + Write
        + EncodeSize
        + Read<Cfg = ()>
        + Epochable
        + Viewable
        + Send
        + Sync
        + 'static;
    /// Individual final vote in this representation.
    type Vote: Attributable
        + Clone
        + Debug
        + PartialEq
        + Write
        + EncodeSize
        + Read<Cfg = ()>
        + Epochable
        + Viewable
        + Send
        + Sync
        + 'static;
    /// Original-round final certificate, never a later-ballot recovery result.
    type Certificate: Clone
        + Debug
        + PartialEq
        + Write
        + EncodeSize
        + Read<Cfg = <S::Certificate as Read>::Cfg>
        + Epochable
        + Viewable
        + Send
        + Sync
        + 'static;
    /// Authenticates the phase-two certificate, not its application or ancestry.
    fn verify<R: CryptoRng>(
        certificate: &Self::Certificate,
        rng: &mut R,
        scheme: &S,
        strategy: &impl Strategy,
    ) -> bool
    where
        S: scheme::Scheme<D>;
}

/// Stock Simplex phase two, with no extension field in either representation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Plain;
impl sealed::Sealed for Plain {}
impl<S: Scheme, D: Digest> Mode<S, D> for Plain {
    const RETAIN_INTERPRETATION: bool = false;
    type Recovery = recovery::NoRecovery;
    type Recovered = recovery::NoRecovery;
    fn read_recovered(
        _: &mut impl commonware_codec::Buf,
        _: &<S::Certificate as Read>::Cfg,
    ) -> Result<Self::Recovered, commonware_codec::Error> {
        Err(commonware_codec::Error::Invalid(
            "simplex recovered",
            "disabled mode",
        ))
    }
    fn recovered_proposal(certificate: &Self::Recovered) -> &Proposal<D> {
        match *certificate {}
    }
    fn verify_recovered<R: CryptoRng>(
        certificate: &Self::Recovered,
        _: &mut R,
        _: &S,
        _: &impl Strategy,
    ) -> bool
    where
        S: scheme::Scheme<D>,
    {
        match *certificate {}
    }
    type RecoveryQuery = recovery::NoRecovery;
    fn recovery_query_view(query: &Self::RecoveryQuery) -> crate::types::View {
        match *query {}
    }
    type RecoveryRequest = recovery::NoRecovery;
    type RecoveryResponse = recovery::NoRecovery;
    fn recovery_view(request: &Self::RecoveryRequest) -> crate::types::View {
        match *request {}
    }
    fn notarize(vote: &Self::Notarize) -> &Notarize<S, D> {
        vote
    }
    fn finalize_proposal(vote: &Self::Vote) -> &Proposal<D> {
        &vote.proposal
    }
    fn into_notarize(vote: Self::Notarize) -> Notarize<S, D> {
        vote
    }
    fn finalization_proposal(certificate: &Self::Certificate) -> &Proposal<D> {
        &certificate.proposal
    }
    fn finalization_certificate(certificate: &Self::Certificate) -> &S::Certificate {
        &certificate.certificate
    }
    fn signed_finalization_subject(certificate: &Self::Certificate) -> Subject<'_, D> {
        Subject::Finalize {
            proposal: &certificate.proposal,
        }
    }
    fn conflicting_finalize_subjects(a: &Self::Vote, b: &Self::Vote) -> bool {
        a.proposal != b.proposal
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
        vote.verify(rng, scheme, strategy)
    }
    type Notarize = Notarize<S, D>;
    type Vote = Finalize<S, D>;
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

commonware_macros::stability_scope!(ALPHA {
    /// Exact original-round extension statements. Recovery statements use the
    /// separate recovery channel and cannot inhabit this phase-two certificate.
    #[derive(Clone,Copy,Debug,PartialEq,Eq)]
    pub struct Extended;
    impl sealed::Sealed for Extended {}
    impl<S:Scheme,D:Digest> Mode<S,D> for Extended {
        const RETAIN_INTERPRETATION: bool = true;
        type Recovery = recovery::Record<D>;
        type Recovered = super::extension::certificate::Recovered<S,D>;
        fn read_recovered(reader:&mut impl commonware_codec::Buf,cfg:&<S::Certificate as Read>::Cfg)->Result<Self::Recovered,commonware_codec::Error>{Self::Recovered::read_cfg(reader,cfg)}
        fn recovered_proposal(certificate:&Self::Recovered)->&Proposal<D>{&certificate.certificate().statement.proposal}
        fn verify_recovered<R:CryptoRng>(certificate:&Self::Recovered,rng:&mut R,scheme:&S,strategy:&impl Strategy)->bool where S:scheme::Scheme<D>{
            use commonware_utils::{Faults as _,N3f1};
            let Ok(n)=u32::try_from(scheme.participants().len()) else {return false;};
            n>0 && u64::from(n)>5*u64::from(N3f1::max_faults(n)) && S::is_attributable() && certificate.certificate().verify(rng,scheme,strategy)
        }
        type RecoveryQuery = super::extension::request::Query<S,D>;
        fn recovery_query_view(query:&Self::RecoveryQuery)->crate::types::View {query.view()}
        type RecoveryRequest = super::extension::request::Request<S,D>;
        type RecoveryResponse = super::extension::request::Response<S,D>;
        fn recovery_view(request:&Self::RecoveryRequest)->crate::types::View {request.view()}
        fn notarize(vote: &Self::Notarize) -> &Notarize<S,D> { vote.vote() }
        fn finalize_proposal(vote: &Self::Vote) -> &Proposal<D> { &vote.vote().statement.proposal }
        fn into_notarize(vote:Self::Notarize)->Notarize<S,D> {vote.into_parts().0}
        fn finalization_proposal(certificate:&Self::Certificate)->&Proposal<D> {&certificate.certificate().statement.proposal}
        fn finalization_certificate(certificate:&Self::Certificate)->&S::Certificate {&certificate.certificate().certificate}
        fn signed_finalization_subject(certificate:&Self::Certificate)->Subject<'_,D> {Subject::FinalizeExtension{statement:&certificate.certificate().statement}}
        fn conflicting_finalize_subjects(a:&Self::Vote,b:&Self::Vote)->bool {
            a.vote().statement.domain==b.vote().statement.domain && a.vote().statement!=b.vote().statement
        }
        fn verify_finalize<R:CryptoRng>(vote:&Self::Vote,rng:&mut R,scheme:&S,strategy:&impl Strategy)->bool
        where S:scheme::Scheme<D> {vote.vote().verify(rng,scheme,strategy)}
        type Notarize=super::extension::report::Notarize<S,D>;
        type Vote=super::extension::certificate::Finalize<S,D>;
        type Certificate=super::extension::certificate::Finalization<S,D>;
        fn verify<R:CryptoRng>(certificate:&Self::Certificate,rng:&mut R,scheme:&S,strategy:&impl Strategy)->bool
        where S:scheme::Scheme<D> {certificate.certificate().verify(rng,scheme,strategy)}
    }
});

#[cfg(not(target_arch = "wasm32"))]
pub mod aggregation;

/// Local vote subject representation and native signing.
pub mod voting;
