//! Local extension integration boundary for the native voter.
//!
//! Implementations must authenticate leader selection and retain its evidence
//! durably before returning a final subject. These callbacks confer no native
//! voting authority: the state machine still checks ancestry and vote eligibility.
#[commonware_macros::stability(ALPHA)]
use crate::{
    simplex::extension::recovery::Proof,
    types::{Participant, Round},
};
use crate::{
    simplex::{
        phase2::{Plain, voting::Voting},
        scheme::Scheme,
        types::{ArtifactWith, Notarization, Notarize, Proposal},
    },
    types::View,
};
use commonware_cryptography::Digest;

/// Native-verified opportunity to prepare application material for a free
/// recovery choice. It grants neither a vote nor finality. The callback must
/// return immediately; persistence and dissemination happen outside the voter.
/// There is no public constructor or decoding path for this capability.
#[commonware_macros::stability(ALPHA)]
pub struct RecoveryChoice<'a, S: Scheme<D>, D: Digest> {
    pub(super) proposal: &'a Proposal<D>,
    pub(super) domain: D,
    pub(super) ballot: Round,
    pub(super) parent: D,
    pub(super) leader: Participant,
    pub(super) proof: &'a Proof<S, D>,
}
#[commonware_macros::stability(ALPHA)]
impl<S: Scheme<D>, D: Digest> RecoveryChoice<'_, S, D> {
    /// Original notarized proposal; recovery does not replace its input.
    pub const fn proposal(&self) -> &Proposal<D> {
        self.proposal
    }
    /// Trusted extension deployment.
    pub const fn domain(&self) -> D {
        self.domain
    }
    /// Later ballot authorized by native leader and promise checks.
    pub const fn ballot(&self) -> Round {
        self.ballot
    }
    /// Certified parent interpretation, or configured genesis interpretation.
    pub const fn parent(&self) -> D {
        self.parent
    }
    /// Native-elected replacement leader's participant index.
    pub const fn leader(&self) -> Participant {
        self.leader
    }
    /// Original verified statuses permitting a free choice in this ballot.
    pub const fn proof(&self) -> &Proof<S, D> {
        self.proof
    }
}

/// Trusted application evidence adapter. It must never wait inside a callback;
/// missing material is retrieved asynchronously and announced through the voter mailbox
/// with `interpretation_ready`; that notification carries no approval authority.
///
/// Implementations are trusted policy adapters, not replacements for native
/// certificate verification, quorum or recovery.
pub trait Participation<S: Scheme<D>, D: Digest, M: Voting<S, D>>: Send + 'static {
    /// Observes successful completion of this voter's floor and journal replay.
    /// Called once before live requests. Return immediately; this observation
    /// grants no application readiness, vote, certificate or delivery authority.
    #[commonware_macros::stability(ALPHA)]
    fn replayed(&mut self) {}
    /// Attach the currently available original report without altering the vote.
    fn notarize(&mut self, vote: Notarize<S, D>) -> M::Notarize;
    /// First admission of this native notarization in the current voter instance,
    /// before journal I/O. Close optional application selection without waiting.
    /// Replay may notify again: preserve any already durable selected value.
    fn notarized(&mut self, _certificate: &Notarization<S, D>) {}
    /// Return an authenticated, durable leader selection for this exact proposal.
    fn final_subject(&mut self, proposal: &Proposal<D>) -> Option<M::FinalSubject>;
    /// Check retained application evidence for an already signature-verified QC.
    /// Missing evidence must schedule retrieval and return false, never fallback.
    fn accepts_finalization(&mut self, certificate: &M::Certificate) -> bool;
    /// Check that durable evidence required by this replayed artifact is present.
    fn accepts_replay(&mut self, artifact: &ArtifactWith<S, D, M>) -> bool;
    /// Offers an already durable interpretation when no status proof forces one.
    /// This is advisory evidence only; native checks choose the recovery ballot.
    fn recovery_subject(&mut self, proposal: &Proposal<D>) -> Option<M::FinalSubject> {
        self.final_subject(proposal)
    }
    /// Announces free-choice permission only after native proof, leader, ballot,
    /// promise, deadline and certified-parent checks. May repeat on retry.
    /// Do not replace a retained selection; return it through recovery_subject
    /// only after its material/authorization is durable and independently valid.
    #[commonware_macros::stability(ALPHA)]
    fn recovery_choice(&mut self, _choice: RecoveryChoice<'_, S, D>) {}
    /// Authenticate and retain the exact later-ballot interpretation evidence.
    /// Missing evidence returns false and schedules retrieval outside this callback.
    fn accepts_recovery(&mut self, _subject: &M::FinalSubject) -> bool {
        false
    }
    /// Authenticate durable material for a later-ballot parent interpretation.
    /// Native certificate and ancestry checks precede this callback.
    fn accepts_recovered(&mut self, _certificate: &M::Recovered) -> bool {
        false
    }
    /// Announces a native-verified recovered witness after its journal sync.
    /// Return false if mandatory application notification could not be retained;
    /// the voter stops rather than acknowledging a dropped update. This is not finality.
    fn recovered_installed(&mut self, _certificate: &M::Recovered) -> bool {
        true
    }
    /// Retire volatile work below the voter floor, preserving durable custody.
    fn prune(&mut self, floor: View);
}

/// Stock Simplex needs no extension readiness, evidence or extra wakeup.
#[derive(Default)]
pub struct NoExtension;
impl<S: Scheme<D>, D: Digest> Participation<S, D, Plain> for NoExtension {
    fn notarize(&mut self, vote: Notarize<S, D>) -> Notarize<S, D> {
        vote
    }
    fn final_subject(&mut self, _: &Proposal<D>) -> Option<()> {
        Some(())
    }
    fn accepts_finalization(
        &mut self,
        _: &<Plain as crate::simplex::phase2::Mode<S, D>>::Certificate,
    ) -> bool {
        true
    }
    fn accepts_replay(&mut self, _: &ArtifactWith<S, D, Plain>) -> bool {
        true
    }
    fn prune(&mut self, _: View) {}
}
