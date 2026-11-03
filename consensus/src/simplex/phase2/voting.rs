//! Native final-vote subject retention and signing representation.
//!
//! These operations bind normal-path final subjects to their deployment and
//! exact original-round parent interpretation. Application evidence, leader
//! selection and recovery authority require separate validation. The voter must
//! durably journal its decision before emission.
use super::{Mode, Plain};
#[cfg(not(target_arch = "wasm32"))]
#[commonware_macros::stability(ALPHA)]
pub use crate::simplex::actors::voter::participation::RecoveryChoice;
#[cfg(not(target_arch = "wasm32"))]
pub use crate::simplex::actors::voter::{
    RoundWith, StateConfig, StateWith, VoterRound,
    participation::{NoExtension, Participation},
};
use crate::simplex::{
    scheme,
    types::{Finalize, Proposal},
};
use commonware_cryptography::{Digest, certificate::Scheme};
use std::fmt::Debug;

/// Native-owned local decision representation. Plain retains its unit marker;
/// Extended keeps the exact accepted interpretation for replay and recovery.
pub trait Voting<S: Scheme, D: Digest>: Mode<S, D> {
    /// Requires an exact parent interpretation in addition to native ancestry.
    const REQUIRE_PARENT_INTERPRETATION: bool;
    /// Trusted interpretation configuration for this epoch.
    type Context: Send + Sync + 'static;
    /// Local recovery fence; Plain has no additional state.
    type RecoveryState: Send + Sync + 'static;
    const EMPTY_RECOVERY: Self::RecoveryState;
    fn allows_original(state: &Self::RecoveryState) -> bool;
    fn recovery_proposal(record: &Self::Recovery) -> &Proposal<D>;
    fn recovery_context(context: &Self::Context, record: &Self::Recovery) -> bool;
    fn replay_recovery(
        state: &mut Self::RecoveryState,
        original: Option<&Self::FinalSubject>,
        record: &Self::Recovery,
    ) -> bool;
    /// Checks native request eligibility without staging a decision or requiring custody.
    #[cfg(not(target_arch = "wasm32"))]
    fn validate_recovery_request<E, L>(
        state: &mut StateWith<E, S, L, D, Self>,
        request: &Self::RecoveryRequest,
    ) -> bool
    where
        E: commonware_runtime::Clock + rand_core::CryptoRng + commonware_runtime::Metrics,
        L: crate::simplex::elector::Elector<S>,
        S: scheme::Scheme<D>;
    /// Validates native recovery authority and stages the decision in the live state.
    #[cfg(not(target_arch = "wasm32"))]
    fn stage_recovery_request<E, L>(
        state: &mut StateWith<E, S, L, D, Self>,
        request: &Self::RecoveryRequest,
        evidence: &mut impl Participation<S, D, Self>,
    ) -> Option<Self::Recovery>
    where
        E: commonware_runtime::Clock + rand_core::CryptoRng + commonware_runtime::Metrics,
        L: crate::simplex::elector::Elector<S>,
        S: scheme::Scheme<D>;
    /// Constructs a leader request from native state without accepting or signing a vote.
    #[cfg(not(target_arch = "wasm32"))]
    fn prepare_recovery_request<E, L>(
        state: &mut StateWith<E, S, L, D, Self>,
        query: &Self::RecoveryQuery,
        evidence: &mut impl Participation<S, D, Self>,
    ) -> Option<Self::RecoveryRequest>
    where
        E: commonware_runtime::Clock + rand_core::CryptoRng + commonware_runtime::Metrics,
        L: crate::simplex::elector::Elector<S>,
        S: scheme::Scheme<D>;
    /// Signs a synchronized decision. Calling this before sync is forbidden.
    fn sign_recovery(
        scheme: &S,
        context: &Self::Context,
        record: &Self::Recovery,
    ) -> Option<Self::RecoveryResponse>
    where
        S: scheme::Scheme<D>;
    /// Immutable local final-vote subject, after caller-owned eligibility checks.
    type FinalSubject: Clone + Debug + PartialEq + Send + Sync + 'static;
    /// Whether a subject belongs to this trusted interpretation deployment.
    fn matches_context(context: &Self::Context, subject: &Self::FinalSubject) -> bool;
    /// Whether a subject names this original proposal and original voting round.
    fn matches_subject(proposal: &Proposal<D>, subject: &Self::FinalSubject) -> bool;
    /// Checks an original-round or recovered parent witness, or configured genesis.
    /// Certificate authentication and recovery authority are caller prerequisites.
    fn matches_parent(
        context: &Self::Context,
        subject: &Self::FinalSubject,
        parent: Option<&Self::Certificate>,
        recovered: Option<&Self::Recovered>,
        genesis: bool,
    ) -> bool;
    /// Exact subject of a recovered interpretation, retaining its later ballot.
    fn recovered_subject(certificate: &Self::Recovered) -> Self::FinalSubject;
    /// Exact interpreted value equality; the ballot is not part of the value.
    fn same_interpretation(a: &Self::FinalSubject, b: &Self::FinalSubject) -> bool;
    /// Extracts the complete accepted subject from a durable original-round vote.
    fn final_subject(vote: &Self::Vote) -> Self::FinalSubject;
    /// Exact subject authenticated by a final certificate.
    fn finalization_subject(certificate: &Self::Certificate) -> Self::FinalSubject;
    /// Signs the caller-authorized subject. The caller journals before publishing.
    fn sign_finalize(
        scheme: &S,
        proposal: Proposal<D>,
        subject: Self::FinalSubject,
    ) -> Option<Self::Vote>
    where
        S: scheme::Scheme<D>;
}
impl<S: Scheme, D: Digest> Voting<S, D> for Plain {
    const REQUIRE_PARENT_INTERPRETATION: bool = false;
    type Context = ();
    type RecoveryState = ();
    const EMPTY_RECOVERY: () = ();
    fn allows_original(_: &()) -> bool {
        true
    }
    fn recovery_proposal(record: &Self::Recovery) -> &Proposal<D> {
        match *record {}
    }
    fn recovery_context(_: &(), record: &Self::Recovery) -> bool {
        match *record {}
    }
    fn replay_recovery(_: &mut (), _: Option<&()>, record: &Self::Recovery) -> bool {
        match *record {}
    }
    #[cfg(not(target_arch = "wasm32"))]
    fn validate_recovery_request<E, L>(
        _: &mut StateWith<E, S, L, D, Self>,
        request: &Self::RecoveryRequest,
    ) -> bool
    where
        E: commonware_runtime::Clock + rand_core::CryptoRng + commonware_runtime::Metrics,
        L: crate::simplex::elector::Elector<S>,
        S: scheme::Scheme<D>,
    {
        match *request {}
    }
    #[cfg(not(target_arch = "wasm32"))]
    fn stage_recovery_request<E, L>(
        _: &mut StateWith<E, S, L, D, Self>,
        request: &Self::RecoveryRequest,
        _: &mut impl Participation<S, D, Self>,
    ) -> Option<Self::Recovery>
    where
        E: commonware_runtime::Clock + rand_core::CryptoRng + commonware_runtime::Metrics,
        L: crate::simplex::elector::Elector<S>,
        S: scheme::Scheme<D>,
    {
        match *request {}
    }
    #[cfg(not(target_arch = "wasm32"))]
    fn prepare_recovery_request<E, L>(
        _: &mut StateWith<E, S, L, D, Self>,
        query: &Self::RecoveryQuery,
        _: &mut impl Participation<S, D, Self>,
    ) -> Option<Self::RecoveryRequest>
    where
        E: commonware_runtime::Clock + rand_core::CryptoRng + commonware_runtime::Metrics,
        L: crate::simplex::elector::Elector<S>,
        S: scheme::Scheme<D>,
    {
        match *query {}
    }
    fn sign_recovery(_: &S, _: &(), record: &Self::Recovery) -> Option<Self::RecoveryResponse>
    where
        S: scheme::Scheme<D>,
    {
        match *record {}
    }
    type FinalSubject = ();
    fn matches_context(_: &(), _: &()) -> bool {
        true
    }
    fn matches_subject(_: &Proposal<D>, _: &()) -> bool {
        true
    }
    fn matches_parent(
        _: &(),
        _: &(),
        _: Option<&Self::Certificate>,
        _: Option<&Self::Recovered>,
        _: bool,
    ) -> bool {
        true
    }
    fn recovered_subject(certificate: &Self::Recovered) {
        match *certificate {}
    }
    fn same_interpretation(_: &(), _: &()) -> bool {
        true
    }
    fn final_subject(_: &Self::Vote) {}
    fn finalization_subject(_: &Self::Certificate) {}
    fn sign_finalize(scheme: &S, proposal: Proposal<D>, _: ()) -> Option<Self::Vote>
    where
        S: scheme::Scheme<D>,
    {
        Finalize::sign(scheme, proposal)
    }
}
commonware_macros::stability_scope!(ALPHA {
    /// Trusted deployment binding, supplied before entering an extended epoch.
    #[derive(Clone,Copy,Debug)]
    pub struct ExtendedContext<D:Digest> {
        /// Genesis, runtime and interpretation-version commitment.
        pub domain:D,
        /// Exact interpretation commitment of the configured base genesis.
        pub genesis_interpretation:D,
        commitment:fn(&crate::simplex::extension::vote::Statement<D>)->D,
    }
    impl<D:Digest> ExtendedContext<D> {
        pub(crate) fn value(&self,subject:&crate::simplex::extension::vote::Statement<D>)->D {(self.commitment)(subject)}
        /// Fixes the interpretation hash algorithm for the lifetime of this context.
        /// The domain must bind that algorithm and the deployment configuration.
        pub const fn new<H:commonware_cryptography::Hasher<Digest=D>>(domain:D,genesis_interpretation:D)->Self {
            Self {domain,genesis_interpretation,commitment:crate::simplex::extension::vote::Statement::value::<H>}
        }
    }
    impl<S:Scheme,D:Digest> Voting<S,D> for super::Extended {
        const REQUIRE_PARENT_INTERPRETATION:bool=true;
        type Context=ExtendedContext<D>;
        type RecoveryState=super::recovery::State<D>;
        const EMPTY_RECOVERY:Self::RecoveryState=super::recovery::State::EMPTY;
        fn allows_original(state:&Self::RecoveryState)->bool{state.allows_original()}
        fn recovery_proposal(record:&Self::Recovery)->&Proposal<D>{record.proposal()}
        fn recovery_context(context:&Self::Context,record:&Self::Recovery)->bool{context.domain==record.domain()}
        fn replay_recovery(state:&mut Self::RecoveryState,original:Option<&Self::FinalSubject>,record:&Self::Recovery)->bool{state.apply(original,record)}
        #[cfg(not(target_arch="wasm32"))]
        fn validate_recovery_request<E,L>(state:&mut StateWith<E,S,L,D,Self>,request:&Self::RecoveryRequest)->bool
        where E:commonware_runtime::Clock+rand_core::CryptoRng+commonware_runtime::Metrics,L:crate::simplex::elector::Elector<S>,S:scheme::Scheme<D>{
            matches!(request.command,crate::simplex::extension::request::Command::Accept(_))
                && state.validate_authenticated_recovery(request).is_ok()
        }
        #[cfg(not(target_arch="wasm32"))]
        fn stage_recovery_request<E,L>(state:&mut StateWith<E,S,L,D,Self>,request:&Self::RecoveryRequest,evidence:&mut impl Participation<S,D,Self>)->Option<Self::Recovery>
        where E:commonware_runtime::Clock+rand_core::CryptoRng+commonware_runtime::Metrics,L:crate::simplex::elector::Elector<S>,S:scheme::Scheme<D>{state.stage_authenticated_recovery(request,|subject|evidence.accepts_recovery(subject)).ok()}
        #[cfg(not(target_arch="wasm32"))]
        fn prepare_recovery_request<E,L>(state:&mut StateWith<E,S,L,D,Self>,query:&Self::RecoveryQuery,evidence:&mut impl Participation<S,D,Self>)->Option<Self::RecoveryRequest>
        where E:commonware_runtime::Clock+rand_core::CryptoRng+commonware_runtime::Metrics,L:crate::simplex::elector::Elector<S>,S:scheme::Scheme<D>{
            state.prepare_recovery_request(query,evidence).ok()
        }
        fn sign_recovery(scheme:&S,context:&Self::Context,record:&Self::Recovery)->Option<Self::RecoveryResponse> where S:scheme::Scheme<D> {
            use crate::simplex::extension::{recovery::{Promise,Status},request::Response,vote::Vote};
            match record {
                super::recovery::Record::Promise{proposal,domain,ballot,accepted}=>Some(Response::Status{
                    status:Status::sign(scheme,Promise{proposal:proposal.clone(),domain:*domain,ballot:*ballot,accepted:accepted.as_ref().map(|s|(s.ballot,context.value(s)))}).ok()?,
                    accepted:accepted.clone(),
                }),
                super::recovery::Record::Accept(subject)=>Vote::sign(scheme,subject.clone()).map(Response::Vote),
            }
        }
        type FinalSubject=crate::simplex::extension::vote::Statement<D>;
        fn matches_context(context:&Self::Context,subject:&Self::FinalSubject)->bool {
            context.domain==subject.domain
        }
        fn matches_subject(proposal:&Proposal<D>,subject:&Self::FinalSubject)->bool {
            subject.proposal==*proposal && subject.ballot==proposal.round
        }
        fn matches_parent(context:&Self::Context,subject:&Self::FinalSubject,parent:Option<&Self::Certificate>,recovered:Option<&Self::Recovered>,genesis:bool)->bool {
            if genesis {
                return subject.proposal.parent.is_zero() && subject.parent==context.genesis_interpretation;
            }
            let accepted=match (parent,recovered) {
                (Some(parent),_)=>&parent.certificate().statement,
                (None,Some(parent))=>&parent.certificate().statement,
                _=>return false,
            };
            accepted.domain==context.domain
                && accepted.proposal.round.epoch()==subject.proposal.round.epoch()
                && accepted.proposal.round.view()==subject.proposal.parent
                && subject.parent==(context.commitment)(accepted)
        }
        fn recovered_subject(certificate:&Self::Recovered)->Self::FinalSubject {certificate.certificate().statement.clone()}
        fn same_interpretation(a:&Self::FinalSubject,b:&Self::FinalSubject)->bool {a.proposal==b.proposal && a.domain==b.domain && a.parent==b.parent && a.extension==b.extension}
        fn final_subject(vote:&Self::Vote)->Self::FinalSubject {vote.vote().statement.clone()}
        fn finalization_subject(certificate:&Self::Certificate)->Self::FinalSubject {certificate.certificate().statement.clone()}
        fn sign_finalize(scheme:&S,proposal:Proposal<D>,subject:Self::FinalSubject)->Option<Self::Vote>
        where S:scheme::Scheme<D> {
            if !<Self as Voting<S,D>>::matches_subject(&proposal,&subject) {return None;}
            crate::simplex::extension::certificate::Finalize::new(
                crate::simplex::extension::vote::Vote::sign(scheme,subject)?
            ).ok()
        }
    }
});
