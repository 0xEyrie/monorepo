//! Exact-subject groups for the native extended final phase.
use super::{Aggregation, Batch, Certification, FinalBuffer, State};
use crate::{
    simplex::{
        extension::{
            certificate::{Finalization, Finalize},
            vote::{Certificate, Statement},
        },
        phase2::Extended,
        scheme::Scheme,
        types::{Proposal, Subject},
    },
    types::Round,
};
use commonware_cryptography::Digest;
use commonware_parallel::Strategy;
use commonware_runtime::telemetry::traces::TracedExt as _;
use rand_core::CryptoRng;
use std::sync::Arc;
use tracing::info_span;

type Group<S, D> = (Statement<D>, Certification<Statement<D>, S, false>);

/// At most n signer-unique votes and n exact-subject groups in one native view.
/// Subject groups reserve individual entries, avoiding n quorum-sized allocations
/// when adversarial participants all submit different statements.
pub struct Groups<S: Scheme<D>, D: Digest> {
    quorum: usize,
    participants: usize,
    seen: Vec<bool>,
    groups: Vec<Group<S, D>>,
    complete: bool,
}
impl<S: Scheme<D>, D: Digest> Aggregation<S, D> for Extended {
    type FinalBuffer = Groups<S, D>;
}
impl<S: Scheme<D>, D: Digest> FinalBuffer<S, D> for Groups<S, D> {
    type Vote = Finalize<S, D>;
    type Certificate = Finalization<S, D>;
    fn new(quorum: usize, participants: usize) -> Self {
        assert!(
            quorum > 0 && quorum <= participants,
            "invalid native quorum"
        );
        Self {
            quorum,
            participants,
            seen: Vec::new(),
            groups: Vec::new(),
            complete: false,
        }
    }
    fn push(&mut self, vote: Self::Vote, verified: bool) {
        if self.complete {
            return;
        }
        let vote = vote.vote();
        let signer = usize::from(vote.attestation.signer);
        if signer >= self.participants {
            return;
        }
        if self.seen.is_empty() {
            self.seen.resize(self.participants, false);
        }
        if self.seen[signer] {
            return;
        }
        self.seen[signer] = true;
        let index = match self.groups.iter().position(|(s, _)| s == &vote.statement) {
            Some(index) => index,
            None => {
                self.groups
                    .push((vote.statement.clone(), Certification::new(self.quorum)));
                self.groups.len() - 1
            }
        };
        self.groups[index]
            .1
            .add(vote.statement.clone(), vote.attestation.clone(), verified);
    }
    fn retain_proposal(&mut self, proposal: &Proposal<D>) {
        self.groups.retain(|(s, _)| &s.proposal == proposal);
        // Proposal switching can re-admit the same sender's retained matching vote.
        self.seen.fill(false);
        for (_, group) in &self.groups {
            if let State::Incomplete { pending, verified } = &group.state {
                for (_, attestation) in pending.iter().chain(verified) {
                    self.seen[usize::from(attestation.signer)] = true;
                }
            }
        }
    }
    fn complete(&mut self) {
        self.complete = true;
        self.groups = Vec::new();
        self.seen = Vec::new();
    }
    fn is_complete(&self) -> bool {
        self.complete
    }
    fn has_constructable_quorum(&self) -> bool {
        self.groups
            .iter()
            .any(|(_, group)| group.has_constructable_quorum())
    }
    async fn construct<R: CryptoRng + Send>(
        &mut self,
        scheme: &Arc<S>,
        round: Round,
        rng: &mut R,
        strategy: &impl Strategy,
    ) -> Option<Batch<Self::Certificate>> {
        let mut result: Option<Batch<Self::Certificate>> = None;
        for (_, group) in &mut self.groups {
            let Some(batch) = group
                .try_construct(
                    scheme,
                    rng,
                    strategy,
                    || {
                        info_span!(
                            "simplex.batcher.construct.finalization",
                            epoch = round.epoch().traced(),
                            view = round.view().traced()
                        )
                    },
                    |statement| Subject::FinalizeExtension { statement },
                    |statement, certificate| {
                        Finalization::new(Certificate {
                            statement,
                            certificate,
                        })
                        .expect("original-round typed votes cannot form a recovery certificate")
                    },
                )
                .await
            else {
                continue;
            };
            let aggregate = result.get_or_insert_with(|| Batch {
                processed: 0,
                invalid: Vec::new(),
                certificate: None,
                fallback: false,
            });
            aggregate.processed += batch.processed;
            aggregate.invalid.extend(batch.invalid);
            aggregate.fallback |= batch.fallback;
            if batch.certificate.is_some() {
                aggregate.certificate = batch.certificate;
                break;
            }
        }
        if result
            .as_ref()
            .is_some_and(|batch| batch.certificate.is_some())
        {
            self.complete();
        }
        result
    }
}
