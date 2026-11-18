//! Test-only Plain representation with a discriminating companion verdict.
use super::*;
use std::cell::{Cell, RefCell};

thread_local! {
    static CHECKED: RefCell<Vec<crate::types::Round>> = const { RefCell::new(Vec::new()) };
    static STAGED: Cell<usize> = const { Cell::new(0) };
    static RELEASED: Cell<usize> = const { Cell::new(0) };
    static RELEASE_ALLOWED: Cell<bool> = const { Cell::new(true) };
    static NATIVE_PARENTS: RefCell<std::collections::BTreeMap<crate::types::View, Vec<u8>>> = const { RefCell::new(std::collections::BTreeMap::new()) };
    static NATIVE_CHECKS: Cell<usize> = const { Cell::new(0) };
}
pub(crate) fn reset_checked() {
    CHECKED.with_borrow_mut(Vec::clear);
}
pub(crate) fn checked() -> Vec<crate::types::Round> {
    CHECKED.with_borrow(Clone::clone)
}
pub(crate) fn reset_voting() {
    STAGED.set(0);
    RELEASED.set(0);
    RELEASE_ALLOWED.set(true);
}
pub(crate) fn staged() -> usize {
    STAGED.get()
}
pub(crate) fn released() -> usize {
    RELEASED.get()
}
pub(crate) fn allow_release(allowed: bool) {
    RELEASE_ALLOWED.set(allowed);
}

pub(crate) fn reset_native_parents() {
    NATIVE_PARENTS.with_borrow_mut(std::collections::BTreeMap::clear);
    NATIVE_CHECKS.set(0);
}
pub(crate) fn native_parent(view: crate::types::View, digest: &impl Digest) {
    NATIVE_PARENTS.with_borrow_mut(|parents| {
        parents.insert(view, digest.as_ref().to_vec());
    });
}
pub(crate) fn native_checks() -> usize {
    NATIVE_CHECKS.get()
}
pub(crate) type AdmissionProbe = Probe<true, true>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Probe<const ACCEPT: bool, const ADMISSION: bool = false>;
impl<const ACCEPT: bool, const ADMISSION: bool> sealed::Sealed for Probe<ACCEPT, ADMISSION> {}

impl<S: Scheme, D: Digest, const ACCEPT: bool, const ADMISSION: bool> Mode<S, D>
    for Probe<ACCEPT, ADMISSION>
{
    const RETAIN_INTERPRETATION: bool = false;
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
    type QueryResult = Self::RecoveryRequest;
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
    fn verify_companion<R: CryptoRng>(
        certificate: &Self::Certificate,
        _: &mut R,
        scoped: &Scoped<S>,
        _: &impl Strategy,
    ) -> bool
    where
        S: scheme::Scheme<D>,
    {
        // The probe deliberately accepts verifier-only scopes, so a different
        // item's stronger capability cannot silently substitute for this one.
        CHECKED.with_borrow_mut(|checked| checked.push(certificate.proposal.round));
        ACCEPT
            && scoped.clone().into_scheme().is_none()
            && (ADMISSION || certificate.proposal.round.view().get() % 2 == 1)
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

// Plain-shaped fault injection for the actual voter's extension hooks. This
// intentionally has no M1 ledger, reservation record or recovery capability.
impl<S: Scheme, D: Digest, const ACCEPT: bool, const ADMISSION: bool> voting::Voting<S, D>
    for Probe<ACCEPT, ADMISSION>
{
    type FirstInput = ();
    const REQUIRE_PARENT_INTERPRETATION: bool = false;
    const REQUIRE_FINALIZATION_ADMISSION: bool = ADMISSION;
    fn matches_native_parent(_: &(), _: &(), parent: (crate::types::View, D)) -> bool {
        NATIVE_CHECKS.set(NATIVE_CHECKS.get() + 1);
        NATIVE_PARENTS.with_borrow(|parents| {
            parents
                .get(&parent.0)
                .is_some_and(|expected| expected.as_slice() == parent.1.as_ref())
        })
    }
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
    fn replay_recovery<R: CryptoRng>(
        _: &S,
        _: &(),
        _: &mut R,
        _: &mut (),
        _: Option<&()>,
        record: &Self::Recovery,
    ) -> bool
    where
        S: scheme::Scheme<D>,
    {
        match *record {}
    }
    #[cfg(not(target_arch = "wasm32"))]
    fn validate_recovery_request<E, L>(
        _: &mut voting::StateWith<E, S, L, D, Self>,
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
        _: &mut voting::StateWith<E, S, L, D, Self>,
        request: &Self::RecoveryRequest,
        _: &mut impl voting::Participation<S, D, Self>,
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
        _: &mut voting::StateWith<E, S, L, D, Self>,
        query: &Self::RecoveryQuery,
        _: &mut impl voting::Participation<S, D, Self>,
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
    fn sign_recovery_current<R: rand_core::CryptoRng>(
        _: &S,
        _: &(),
        _: &mut R,
        _: &mut (),
        record: &Self::Recovery,
    ) -> Option<(Self::RecoveryResponse, Option<Self::Recovery>)>
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
        assert!(
            !ADMISSION,
            "native-anchor mode must not request an execution parent"
        );
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
    fn reserve_finalize(_: &()) -> Option<Self::Recovery> {
        None
    }
    #[cfg(not(target_arch = "wasm32"))]
    fn stage_final_reservation<R: CryptoRng>(
        _: &S,
        _: &(),
        _: &mut R,
        _: &mut (),
        _: &Proposal<D>,
        _: Option<&crate::simplex::types::Context<D, S::PublicKey>>,
        _: &(),
    ) -> Option<Option<Self::Recovery>>
    where
        S: scheme::Scheme<D>,
    {
        STAGED.set(STAGED.get() + 1);
        ACCEPT.then_some(None)
    }
    fn reserved_subject(record: &Self::Recovery) -> Option<()> {
        match *record {}
    }
    fn sign_finalize(scheme: &S, proposal: Proposal<D>, subject: ()) -> Option<Self::Vote>
    where
        S: scheme::Scheme<D>,
    {
        <Plain as voting::Voting<S, D>>::sign_finalize(scheme, proposal, subject)
    }
    #[cfg(not(target_arch = "wasm32"))]
    fn sign_finalize_current<R: CryptoRng>(
        scheme: &S,
        _: &(),
        _: &mut R,
        _: &mut (),
        proposal: Proposal<D>,
        _: Option<&crate::simplex::types::Context<D, S::PublicKey>>,
        subject: (),
    ) -> Option<(Self::Vote, Option<Self::Recovery>)>
    where
        S: scheme::Scheme<D>,
    {
        RELEASED.set(RELEASED.get() + 1);
        if !RELEASE_ALLOWED.get() {
            return None;
        }
        <Plain as voting::Voting<S, D>>::sign_finalize(scheme, proposal, subject)
            .map(|vote| (vote, None))
    }
}
