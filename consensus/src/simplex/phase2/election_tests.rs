//! Election dispatch with separately authenticated finality and election witnesses.
use super::*;
use crate::{
    simplex::{
        elector::{Elector, Terms},
        extension::{certificate, vote},
        scheme::ed25519,
        types::Notarization,
    },
    types::{Epoch, Participant, Round, View, ViewDelta},
};
use bytes::BufMut;
use commonware_codec::{Buf, Error};
use commonware_cryptography::{
    certificate::{Verifier, mocks::Fixture},
    sha256::Digest as D,
};
use commonware_parallel::Sequential;
use commonware_runtime::{Runner, Supervisor as _, deterministic};
use commonware_utils::non_empty;
use std::{sync::Arc, time::Duration};

type S = ed25519::Scheme;

#[derive(Clone, Debug, PartialEq)]
struct WithElectionWitness {
    finalization: Finalization<S, D>,
    notarization: Notarization<S, D>,
}
impl Write for WithElectionWitness {
    fn write(&self, writer: &mut impl BufMut) {
        self.finalization.write(writer);
        self.notarization.write(writer);
    }
}
impl EncodeSize for WithElectionWitness {
    fn encode_size(&self) -> usize {
        self.finalization.encode_size() + self.notarization.encode_size()
    }
}
impl Read for WithElectionWitness {
    type Cfg = <<S as Verifier>::Certificate as Read>::Cfg;
    fn read_cfg(reader: &mut impl Buf, cfg: &Self::Cfg) -> Result<Self, Error> {
        Ok(Self {
            finalization: Finalization::read_cfg(reader, cfg)?,
            notarization: Notarization::read_cfg(reader, cfg)?,
        })
    }
}
impl Epochable for WithElectionWitness {
    fn epoch(&self) -> Epoch {
        self.finalization.epoch()
    }
}
impl Viewable for WithElectionWitness {
    fn view(&self) -> View {
        self.finalization.view()
    }
}

// Intake-only fixture: genuine Plain signatures and an authenticated original
// NQC, without a recovery role or any new signing permission.
#[derive(Clone, Debug, PartialEq)]
struct SeparateElection;
impl sealed::Sealed for SeparateElection {}
impl Mode<S, D> for SeparateElection {
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
        _: &mut impl Buf,
        _: &<Self::Certificate as Read>::Cfg,
    ) -> Result<Self::Recovered, Error> {
        Err(Error::Invalid("election probe", "no recovery"))
    }
    fn recovered_proposal(value: &Self::Recovered) -> &Proposal<D> {
        match *value {}
    }
    fn verify_recovered<R: CryptoRng>(
        value: &Self::Recovered,
        _: &mut R,
        _: &S,
        _: &impl Strategy,
    ) -> bool {
        match *value {}
    }
    type RecoveryQuery = recovery::NoRecovery;
    type RecoveryRequest = recovery::NoRecovery;
    type RecoveryResponse = recovery::NoRecovery;
    fn recovery_query_view(value: &Self::RecoveryQuery) -> View {
        match *value {}
    }
    fn recovery_view(value: &Self::RecoveryRequest) -> View {
        match *value {}
    }
    type Notarize = Notarize<S, D>;
    type Vote = Finalize<S, D>;
    type Certificate = WithElectionWitness;
    fn notarize(vote: &Self::Notarize) -> &Notarize<S, D> {
        vote
    }
    fn into_notarize(vote: Self::Notarize) -> Notarize<S, D> {
        vote
    }
    fn finalize_proposal(vote: &Self::Vote) -> &Proposal<D> {
        &vote.proposal
    }
    fn finalization_proposal(value: &Self::Certificate) -> &Proposal<D> {
        &value.finalization.proposal
    }
    fn finalization_certificate(value: &Self::Certificate) -> &<S as Verifier>::Certificate {
        &value.finalization.certificate
    }
    fn finalization_election_certificate(
        value: &Self::Certificate,
    ) -> &<S as Verifier>::Certificate {
        &value.notarization.certificate
    }
    fn signed_finalization_subject(value: &Self::Certificate) -> Subject<'_, D> {
        <Plain as Mode<S, D>>::signed_finalization_subject(&value.finalization)
    }
    fn verify_companion<R: CryptoRng>(
        value: &Self::Certificate,
        rng: &mut R,
        scoped: &Scoped<S>,
        strategy: &impl Strategy,
    ) -> bool {
        value.notarization.proposal == value.finalization.proposal
            && value.notarization.verify(rng, scoped, strategy)
    }
    fn conflicting_finalize_subjects(a: &Self::Vote, b: &Self::Vote) -> bool {
        <Plain as Mode<S, D>>::conflicting_finalize_subjects(a, b)
    }
    fn verify_finalize<R: CryptoRng>(
        value: &Self::Vote,
        rng: &mut R,
        scheme: &S,
        strategy: &impl Strategy,
    ) -> bool {
        value.verify(rng, scheme, strategy)
    }
    fn verify<R: CryptoRng>(
        value: &Self::Certificate,
        rng: &mut R,
        scheme: &S,
        strategy: &impl Strategy,
    ) -> bool {
        value.finalization.verify(rng, scheme, strategy)
    }
}
impl voting::Voting<S, D> for SeparateElection {
    type FirstInput = ();
    const REQUIRE_PARENT_INTERPRETATION: bool = false;
    type Context = ();
    type RecoveryState = ();
    const EMPTY_RECOVERY: () = ();
    fn allows_original(_: &()) -> bool {
        false
    }
    fn recovery_proposal(value: &Self::Recovery) -> &Proposal<D> {
        match *value {}
    }
    fn recovery_context(_: &(), value: &Self::Recovery) -> bool {
        match *value {}
    }
    fn replay_recovery<R: CryptoRng>(
        _: &S,
        _: &(),
        _: &mut R,
        _: &mut (),
        _: Option<&()>,
        value: &Self::Recovery,
    ) -> bool {
        match *value {}
    }
    fn validate_recovery_request<E, L>(
        _: &mut voting::StateWith<E, S, L, D, Self>,
        value: &Self::RecoveryRequest,
    ) -> bool
    where
        E: commonware_runtime::Clock + CryptoRng + commonware_runtime::Metrics,
        L: Elector<S>,
    {
        match *value {}
    }
    fn stage_recovery_request<E, L>(
        _: &mut voting::StateWith<E, S, L, D, Self>,
        value: &Self::RecoveryRequest,
        _: &mut impl voting::Participation<S, D, Self>,
    ) -> Option<Self::Recovery>
    where
        E: commonware_runtime::Clock + CryptoRng + commonware_runtime::Metrics,
        L: Elector<S>,
    {
        match *value {}
    }
    fn prepare_recovery_request<E, L>(
        _: &mut voting::StateWith<E, S, L, D, Self>,
        value: &Self::RecoveryQuery,
        _: &mut impl voting::Participation<S, D, Self>,
    ) -> Option<Self::RecoveryRequest>
    where
        E: commonware_runtime::Clock + CryptoRng + commonware_runtime::Metrics,
        L: Elector<S>,
    {
        match *value {}
    }
    fn sign_recovery(_: &S, _: &(), value: &Self::Recovery) -> Option<Self::RecoveryResponse> {
        match *value {}
    }
    fn sign_recovery_current<R: rand_core::CryptoRng>(
        _: &S,
        _: &(),
        _: &mut R,
        _: &mut (),
        value: &Self::Recovery,
    ) -> Option<(Self::RecoveryResponse, Option<Self::Recovery>)> {
        match *value {}
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
    fn recovered_subject(value: &Self::Recovered) {
        match *value {}
    }
    fn same_interpretation(_: &(), _: &()) -> bool {
        true
    }
    fn final_subject(_: &Self::Vote) {}
    fn finalization_subject(_: &Self::Certificate) {}
    fn reserve_finalize(_: &()) -> Option<Self::Recovery> {
        None
    }
    fn reserved_subject(value: &Self::Recovery) -> Option<()> {
        match *value {}
    }
    fn sign_finalize(_: &S, _: Proposal<D>, _: ()) -> Option<Self::Vote> {
        None
    }
}

// A dispatch probe, not a deployable elector: real electors must be invariant
// across every valid certificate that can unlock a given successor.
#[derive(Clone)]
struct WitnessElector(<S as Verifier>::Certificate);
impl Elector<S> for WitnessElector {
    fn terms(&self) -> Terms {
        Terms::rotating()
    }
    fn elect(
        &self,
        round: Round,
        certificate: Option<&<S as Verifier>::Certificate>,
    ) -> Participant {
        if round.view() == View::new(1) {
            assert!(certificate.is_none());
            return Participant::new(0);
        }
        Participant::new(if certificate == Some(&self.0) { 1 } else { 2 })
    }
}

#[test]
fn finalization_uses_distinct_election_witness_without_replacing_crypto() {
    deterministic::Runner::default().start(|mut context| async move {
        let Fixture {
            schemes, verifier, ..
        } = ed25519::fixture(&mut context, b"election witness", 4);
        let proposal = Proposal::new(
            Round::new(Epoch::new(9), View::new(1)),
            View::zero(),
            D::from([1; 32]),
        );
        let notarizes: Vec<_> = schemes
            .iter()
            .map(|s| Notarize::sign(s, proposal.clone()).unwrap())
            .collect();
        let notarization =
            Notarization::from_notarizes(&verifier, non_empty![@notarizes.iter()], &Sequential)
                .unwrap();
        let finalizes: Vec<_> = schemes
            .iter()
            .map(|s| Finalize::sign(s, proposal.clone()).unwrap())
            .collect();
        let finalization =
            Finalization::from_finalizes(&verifier, non_empty![@finalizes.iter()], &Sequential)
                .unwrap();
        assert_ne!(finalization.certificate, notarization.certificate);
        assert!(std::ptr::eq(
            <Plain as Mode<S, D>>::finalization_certificate(&finalization),
            <Plain as Mode<S, D>>::finalization_election_certificate(&finalization),
        ));
        let witness = WithElectionWitness {
            finalization,
            notarization,
        };
        let scoped = Scoped::verifier(Arc::new(verifier.clone()));
        assert!(SeparateElection::verify(
            &witness,
            &mut context,
            &verifier,
            &Sequential
        ));
        assert!(SeparateElection::verify_companion(
            &witness,
            &mut context,
            &scoped,
            &Sequential
        ));
        assert!(verifier.verify_certificate(
            &mut context,
            SeparateElection::signed_finalization_subject(&witness),
            SeparateElection::finalization_certificate(&witness),
            &Sequential,
        ));
        assert!(!verifier.verify_certificate(
            &mut context,
            SeparateElection::signed_finalization_subject(&witness),
            SeparateElection::finalization_election_certificate(&witness),
            &Sequential,
        ));
        let mut wrong_proposal = witness.clone();
        wrong_proposal.finalization.proposal.payload = D::from([2; 32]);
        assert!(!SeparateElection::verify(
            &wrong_proposal,
            &mut context,
            &verifier,
            &Sequential
        ));
        assert!(!SeparateElection::verify_companion(
            &wrong_proposal,
            &mut context,
            &scoped,
            &Sequential
        ));
        let other_proposal = wrong_proposal.finalization.proposal;
        let other_votes: Vec<_> = schemes
            .iter()
            .map(|s| Notarize::sign(s, other_proposal.clone()).unwrap())
            .collect();
        let mut wrong_witness = witness.clone();
        wrong_witness.notarization =
            Notarization::from_notarizes(&verifier, non_empty![@other_votes.iter()], &Sequential)
                .unwrap();
        assert!(
            wrong_witness
                .notarization
                .verify(&mut context, &verifier, &Sequential)
        );
        assert!(SeparateElection::verify(
            &wrong_witness,
            &mut context,
            &verifier,
            &Sequential
        ));
        assert!(!SeparateElection::verify_companion(
            &wrong_witness,
            &mut context,
            &scoped,
            &Sequential
        ));

        let config = || voting::StateConfig {
            scheme: verifier.clone(),
            elector: WitnessElector(witness.notarization.certificate.clone()),
            epoch: Epoch::new(9),
            view_retention: ViewDelta::new(10),
            leader_timeout: Duration::from_secs(1),
            certification_timeout: Duration::from_secs(2),
            timeout_retry: Duration::from_secs(3),
            skip_budget: 4,
        };
        let mut via_nqc =
            voting::StateWith::<_, _, _, D, Plain>::new_with(context.child("nqc"), config(), ());
        via_nqc.set_genesis(D::from([0; 32]));
        assert!(via_nqc.add_notarization(witness.notarization.clone()).0);
        let mut via_final = voting::StateWith::<_, _, _, D, SeparateElection>::new_with(
            context.child("final"),
            config(),
            (),
        );
        via_final.set_genesis(D::from([0; 32]));
        assert!(via_final.add_finalization(witness.clone()).0);
        assert_eq!(
            via_nqc.leader_index(View::new(2)),
            Some(Participant::new(1))
        );
        assert_eq!(
            via_final.leader_index(View::new(2)),
            via_nqc.leader_index(View::new(2))
        );
        assert_eq!(
            SeparateElection::finalization_certificate(&witness),
            &witness.finalization.certificate
        );
    });
}

#[test]
fn extended_election_witness_defaults_to_exact_signed_certificate() {
    deterministic::Runner::default().start(|mut context| async move {
        let Fixture {
            schemes, verifier, ..
        } = ed25519::fixture(&mut context, b"extended election witness", 4);
        let proposal = Proposal::new(
            Round::new(Epoch::new(9), View::new(1)),
            View::zero(),
            D::from([1; 32]),
        );
        let statement = vote::Statement {
            ballot: proposal.round,
            proposal,
            domain: D::from([2; 32]),
            parent: D::from([3; 32]),
            extension: D::from([4; 32]),
        };
        let votes = schemes
            .iter()
            .map(|s| vote::Vote::sign(s, statement.clone()).unwrap());
        let native =
            vote::Certificate::from_votes(&mut context, &verifier, non_empty![@votes], &Sequential)
                .unwrap();
        let finalization = certificate::Finalization::new(native).unwrap();
        let crypto = <Extended as Mode<S, D>>::finalization_certificate(&finalization);
        let election = <Extended as Mode<S, D>>::finalization_election_certificate(&finalization);
        assert!(std::ptr::eq(crypto, election));
        assert!(verifier.verify_certificate(
            &mut context,
            <Extended as Mode<S, D>>::signed_finalization_subject(&finalization),
            crypto,
            &Sequential,
        ));
        assert!(!verifier.verify_certificate(
            &mut context,
            Subject::Finalize {
                proposal: &statement.proposal,
            },
            crypto,
            &Sequential,
        ));
    });
}
