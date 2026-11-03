//! Staging for the native voter's single journal. These methods do not publish
//! or sign messages; their records must be synchronized before either action.
use super::*;
use crate::simplex::{
    extension::{
        recovery::{Error, Promise, Proof},
        request::{Command, Query, Request, Response},
        vote::Statement,
    },
    phase2::{Extended, recovery::Record},
};
use commonware_parallel::{Sequential, Strategy};
use commonware_utils::{Faults as _, N3f1};

impl<E: Clock + CryptoRng + Metrics, S: Scheme<D>, L: Elector<S>, D: Digest>
    StateWith<E, S, L, D, Extended>
{
    /// Builds a signed leader request from native eligibility and original evidence.
    /// This is not a local promise or acceptance; only the journaled request path
    /// may release a status or vote. The coordinator retains its selected ballot.
    pub fn prepare_recovery_request(
        &mut self,
        query: &Query<S, D>,
        evidence: &mut impl crate::simplex::phase2::voting::Participation<S, D, Extended>,
    ) -> Result<Request<S, D>, Error> {
        if !query.bounded() {
            return Err(Error::Context);
        }
        let me = self.scheme.me().ok_or(Error::Context)?;
        match query {
            Query::Discover => {
                let ballot = Rnd::new(self.epoch, self.current_view());
                if self.leader_index(ballot.view()) != Some(me) {
                    return Err(Error::Context);
                }
                let proposal = self
                    .views
                    .iter()
                    .find_map(|(view, round)| {
                        let proposal = &self.notarization(*view)?.proposal;
                        (round.is_certified()
                            && self.finalization(*view).is_none()
                            && !self.recovered.contains_key(view)
                            && self.recovery_eligible(proposal, ballot).is_ok()
                            && self
                                .elapsed_since_start(*view)
                                .is_some_and(|elapsed| elapsed >= self.certification_timeout)
                            && (proposal.parent == GENESIS_VIEW && self.genesis.is_some()
                                || self.finalization(proposal.parent).is_some()
                                || self.recovered.contains_key(&proposal.parent)))
                        .then(|| proposal.clone())
                    })
                    .ok_or(Error::Context)?;
                Request::sign(
                    &self.scheme,
                    Command::Promise {
                        proposal,
                        domain: self.mode_context.domain,
                        ballot,
                    },
                    None,
                )
            }
            Query::Accept { promise, responses } => {
                let Command::Promise {
                    proposal,
                    domain,
                    ballot,
                } = &promise.command
                else {
                    return Err(Error::Context);
                };
                self.recovery_eligible(proposal, *ballot)?;
                if *domain != self.mode_context.domain
                    || promise.attestation.signer != me
                    || self.leader_index(ballot.view()) != Some(me)
                    || self
                        .elapsed_since_start(proposal.view())
                        .is_none_or(|elapsed| elapsed < self.certification_timeout)
                    || !promise.verify(&mut self.context, &self.scheme, &Sequential)
                {
                    return Err(Error::Context);
                }
                let round = self.views.get(&proposal.view()).ok_or(Error::Context)?;
                if round
                    .recovery_state()
                    .promise()
                    .is_none_or(|r| r.ballot() != *ballot)
                {
                    return Err(Error::Context);
                }
                let retained = round
                    .recovery_state()
                    .accepted(round.final_subject())
                    .filter(|s| s.ballot == *ballot)
                    .cloned();
                let mut statuses = Vec::with_capacity(responses.len());
                let mut previous = Vec::new();
                for response in responses {
                    let Response::Status { status, accepted } = response else {
                        return Err(Error::Context);
                    };
                    if status.promise.accepted
                        != accepted
                            .as_ref()
                            .map(|s| (s.ballot, self.mode_context.value(s)))
                        || accepted
                            .as_ref()
                            .is_some_and(|s| s.proposal != *proposal || s.domain != *domain)
                    {
                        return Err(Error::Context);
                    }
                    statuses.push(status.clone());
                    if let Some(accepted) = accepted {
                        previous.push(accepted.clone());
                    }
                }
                statuses.sort_by_key(|s| s.attestation.signer);
                let proof = Proof { statuses };
                // Proof verification reads only slot/domain/ballot from this probe;
                // no placeholder interpretation is ever signed or accepted.
                let probe = Statement {
                    proposal: proposal.clone(),
                    domain: *domain,
                    ballot: *ballot,
                    parent: proposal.payload,
                    extension: proposal.payload,
                };
                let verified =
                    proof.verify(&mut self.context, &self.scheme, &probe, &Sequential)?;
                if verified.forced_value().is_none()
                    && retained.is_none()
                    && !self.recovered.contains_key(&proposal.view())
                {
                    let parent = if proposal.parent == GENESIS_VIEW && self.genesis.is_some() {
                        self.mode_context.genesis_interpretation
                    } else {
                        let parent = self
                            .finalization(proposal.parent)
                            .map(|c| &c.certificate().statement)
                            .or_else(|| {
                                self.recovered
                                    .get(&proposal.parent)
                                    .map(|c| &c.certificate().statement)
                            })
                            .ok_or(Error::Context)?;
                        self.mode_context.value(parent)
                    };
                    let mut parent_probe = probe.clone();
                    parent_probe.parent = parent;
                    if !self
                        .views
                        .get(&proposal.view())
                        .is_some_and(|r| r.is_certified())
                        || !<Extended as Voting<S, D>>::matches_parent(
                            &self.mode_context,
                            &parent_probe,
                            self.finalization(proposal.parent),
                            self.recovered.get(&proposal.parent),
                            proposal.parent == GENESIS_VIEW && self.genesis.is_some(),
                        )
                    {
                        return Err(Error::Context);
                    }
                    evidence.recovery_choice(super::super::participation::RecoveryChoice {
                        proposal,
                        domain: *domain,
                        ballot: *ballot,
                        parent,
                        leader: me,
                        proof: &proof,
                    });
                }
                let mut subject = if let Some(forced) = verified.forced_value() {
                    previous
                        .into_iter()
                        .find(|s| self.mode_context.value(s) == forced)
                } else {
                    retained
                        .or_else(|| evidence.recovery_subject(proposal))
                        .or_else(|| previous.into_iter().next())
                }
                .ok_or(Error::Context)?;
                subject.ballot = *ballot;
                self.validate_recovery_accept(&subject, &proof, &Sequential)?;
                let round = self.views.get(&proposal.view()).ok_or(Error::Context)?;
                let mut fence = round.recovery_state().clone();
                if !fence.apply(round.final_subject(), &Record::Accept(subject.clone())) {
                    return Err(Error::Context);
                }
                if !evidence.accepts_recovery(&subject) {
                    return Err(Error::Context);
                }
                Request::sign(&self.scheme, Command::Accept(subject), Some(proof))
            }
        }
    }
    /// Checks current native authority without changing a promise or acceptance.
    /// Successful validation authorizes material admission only; staging must repeat it.
    pub fn validate_authenticated_recovery(
        &mut self,
        request: &Request<S, D>,
    ) -> Result<(), Error> {
        let proposal = request.command.proposal();
        let ballot = request.command.ballot();
        self.recovery_eligible(proposal, ballot)?;
        if self.scheme.me().is_none()
            || request.command.domain() != self.mode_context.domain
            || self.leader_index(ballot.view()) != Some(request.attestation.signer)
            || self
                .elapsed_since_start(proposal.view())
                .is_none_or(|elapsed| elapsed < self.certification_timeout)
        {
            return Err(Error::Context);
        }
        if !request.verify(&mut self.context, &self.scheme, &Sequential) {
            return Err(Error::Signature);
        }
        if let Command::Accept(subject) = &request.command {
            self.validate_recovery_accept(
                subject,
                request.proof.as_ref().ok_or(Error::Context)?,
                &Sequential,
            )?;
            let round = self
                .views
                .get(&subject.proposal.view())
                .ok_or(Error::Context)?;
            let mut fence = round.recovery_state().clone();
            if !fence.apply(round.final_subject(), &Record::Accept(subject.clone())) {
                return Err(Error::Context);
            }
        }
        Ok(())
    }
    /// Authenticates the native replacement leader and local failure deadline before staging.
    /// This returns an unsigned record, never a durable reply or canonical authority.
    pub fn stage_authenticated_recovery(
        &mut self,
        request: &crate::simplex::extension::request::Request<S, D>,
        accepts: impl FnOnce(&Statement<D>) -> bool,
    ) -> Result<Record<D>, Error> {
        self.validate_authenticated_recovery(request)?;
        let proposal = request.command.proposal();
        let ballot = request.command.ballot();
        let artifact = match &request.command {
            Command::Promise { .. } => self.construct_recovery_promise(proposal.view(), ballot)?,
            Command::Accept(subject) => {
                if !accepts(subject) {
                    return Err(Error::Context);
                }
                self.apply_recovery_accept(subject.clone())?
            }
        };
        let ArtifactWith::Recovery(record) = artifact else {
            unreachable!("recovery constructor returned ordinary artifact")
        };
        Ok(record)
    }
    fn recovery_eligible(&self, proposal: &Proposal<D>, ballot: Rnd) -> Result<(), Error> {
        let n = u32::try_from(self.scheme.participants().len())
            .map_err(|_| Error::UnsupportedRoster)?;
        if n == 0 || u64::from(n) <= 5 * u64::from(N3f1::max_faults(n)) {
            return Err(Error::UnsupportedRoster);
        }
        if !S::is_attributable() {
            return Err(Error::Attribution);
        }
        if proposal.round.epoch() != self.epoch
            || ballot.epoch() != self.epoch
            || proposal.view() <= self.last_finalized
            || ballot.view() <= proposal.view()
            || ballot.view() > self.current_view()
            || self.leader_index(ballot.view()).is_none()
            || self
                .notarization(proposal.view())
                .is_none_or(|n| n.proposal != *proposal)
            || self.parent_payload(proposal).is_err()
        {
            return Err(Error::Context);
        }
        Ok(())
    }
    /// Stages a later-ballot promise for a locally notarized, unresolved slot.
    /// Native leader authorization and the failure deadline belong to the actor.
    /// Journal/sync the returned record before exposing its frozen status. A
    /// cancelled/failed persistence operation requires stopping and replaying.
    pub fn construct_recovery_promise(
        &mut self,
        view: View,
        ballot: Rnd,
    ) -> Result<ArtifactWith<S, D, Extended>, Error> {
        let round = self.views.get(&view).ok_or(Error::Context)?;
        let proposal = round.proposal().ok_or(Error::Context)?.clone();
        self.recovery_eligible(&proposal, ballot)?;
        // A retry must retain the status frozen before this ballot's acceptance.
        let record = match round.recovery_state().promise() {
            Some(record) if record.ballot() == ballot => record.clone(),
            _ => Record::Promise {
                proposal,
                domain: self.mode_context.domain,
                ballot,
                accepted: round
                    .recovery_state()
                    .accepted(round.final_subject())
                    .cloned(),
            },
        };
        if !self
            .views
            .get_mut(&view)
            .expect("checked round")
            .stage_recovery(&record)
        {
            return Err(Error::Context);
        }
        Ok(ArtifactWith::Recovery(record))
    }
    /// Returns unsigned status data from the frozen local promise. Availability
    /// in memory does not imply durability; callers must first synchronize its record.
    pub fn recovery_promise(&self, view: View) -> Option<Promise<D>> {
        let Record::Promise {
            proposal,
            domain,
            ballot,
            accepted,
        } = self.views.get(&view)?.recovery_state().promise()?
        else {
            return None;
        };
        Some(Promise {
            proposal: proposal.clone(),
            domain: *domain,
            ballot: *ballot,
            accepted: accepted
                .as_ref()
                .map(|s| (s.ballot, self.mode_context.value(s))),
        })
    }
    /// Stages an acceptance after verifying the status proof with this epoch scheme and an
    /// exact confirmed parent. The actor must also authenticate the replacement
    /// leader, application material and certification, then sync before signing.
    /// This neither advances native finality nor authorizes Executor delivery.
    pub fn construct_recovery_accept(
        &mut self,
        subject: Statement<D>,
        proof: &Proof<S, D>,
        strategy: &impl Strategy,
    ) -> Result<ArtifactWith<S, D, Extended>, Error> {
        self.validate_recovery_accept(&subject, proof, strategy)?;
        self.apply_recovery_accept(subject)
    }
    fn validate_recovery_accept(
        &mut self,
        subject: &Statement<D>,
        proof: &Proof<S, D>,
        strategy: &impl Strategy,
    ) -> Result<(), Error> {
        let view = subject.proposal.view();
        self.recovery_eligible(&subject.proposal, subject.ballot)?;
        let proof = proof.verify(&mut self.context, &self.scheme, subject, strategy)?;
        if !self.matches_recovered(view, subject)
            || subject.domain != self.mode_context.domain
            || !proof.permits_value(subject, self.mode_context.value(subject))
            || !self.views.get(&view).is_some_and(|r| r.is_certified())
            || !<Extended as Voting<S, D>>::matches_parent(
                &self.mode_context,
                subject,
                self.finalization(subject.proposal.parent),
                self.recovered.get(&subject.proposal.parent),
                subject.proposal.parent == GENESIS_VIEW && self.genesis.is_some(),
            )
        {
            return Err(Error::Context);
        }
        Ok(())
    }
    fn apply_recovery_accept(
        &mut self,
        subject: Statement<D>,
    ) -> Result<ArtifactWith<S, D, Extended>, Error> {
        let view = subject.proposal.view();
        let record = Record::Accept(subject);
        if !self
            .views
            .get_mut(&view)
            .expect("checked round")
            .stage_recovery(&record)
        {
            return Err(Error::Context);
        }
        Ok(ArtifactWith::Recovery(record))
    }
}
