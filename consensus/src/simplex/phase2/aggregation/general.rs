//! Bounded complete-pair accumulation with independently checked application material.

use super::{Aggregation, Batch, FinalBuffer, offload};
use crate::{
    simplex::{
        extension::agreement::general::{self as g, normal},
        phase2::{
            Mode,
            general::{FinalVote, Finalization, General, WIRE_LIMITS},
        },
        scheme::Scheme,
        types::Proposal,
    },
    types::{Attributable as _, Round},
};
use commonware_cryptography::{Digest, Hasher};
use commonware_parallel::Strategy;
use rand::rngs::StdRng;
use rand_core::{CryptoRng, SeedableRng};
use std::{marker::PhantomData, mem, sync::Arc};
use tracing::info_span;

struct Group<S: Scheme<D>, D: Digest> {
    votes: Vec<(FinalVote<S, D>, bool)>,
}

/// At most n complete pairs, n groups and a separately bounded material payload.
/// Material is local application authority; hints in peer votes never install it.
pub struct Groups<S: Scheme<D>, D: Digest, H> {
    quorum: usize,
    participants: usize,
    seen: Vec<bool>,
    groups: Vec<Group<S, D>>,
    material: Vec<normal::Assembly<S, D>>,
    failed_material: Vec<D>,
    bytes: usize,
    complete: bool,
    hasher: PhantomData<fn() -> H>,
}

impl<S, D, H> Aggregation<S, D> for General<H>
where
    S: Scheme<D>,
    S::Certificate: normal::CertificateSigners,
    D: Digest,
    H: Hasher<Digest = D>,
{
    type FinalBuffer = Groups<S, D, H>;
}

fn same_subject<S: Scheme<D>, D: Digest>(a: &FinalVote<S, D>, b: &FinalVote<S, D>) -> bool {
    a.inner().native.statement == b.inner().native.statement
        && a.inner().agreement.message == b.inner().agreement.message
}

fn matches<S, D, H>(material: &normal::Assembly<S, D>, vote: &FinalVote<S, D>) -> bool
where
    S: Scheme<D>,
    S::Certificate: normal::CertificateSigners,
    D: Digest,
    H: Hasher<Digest = D>,
{
    let message = &vote.inner().agreement.message;
    vote.inner().native.statement == normal::subject::<H>(material.decision())
        && message.slot == material.core().slot.id::<H>()
        && message.round == material.proposal().round
        && message.leader == material.core().leader
        && matches!(&message.kind, g::Kind::Phase {
            phase: g::Phase::FastFinal, decision
        } if decision == &material.decision().id::<H>())
}

impl<S, D, H> FinalBuffer<S, D> for Groups<S, D, H>
where
    S: Scheme<D>,
    S::Certificate: normal::CertificateSigners,
    D: Digest,
    H: Hasher<Digest = D>,
{
    type Vote = FinalVote<S, D>;
    type Certificate = Finalization<S, D>;
    type Assembly = normal::Assembly<S, D>;

    fn new(quorum: usize, participants: usize) -> Self {
        let committee = g::Committee::new(participants).expect("unsupported G1 roster");
        assert_eq!(quorum, committee.quorum(), "incorrect native G1 quorum");
        Self {
            quorum,
            participants,
            seen: Vec::new(),
            groups: Vec::new(),
            material: Vec::new(),
            failed_material: Vec::new(),
            bytes: 0,
            complete: false,
            hasher: PhantomData,
        }
    }

    fn install_assembly(&mut self, material: Self::Assembly) -> bool {
        if self.complete || material.core().followers.len() + 1 != self.quorum {
            return false;
        }
        if let Some(old) = self.material.iter().find(|old| *old == &material) {
            return !self.failed_material.contains(&old.id());
        }
        if let Some(index) = self.material.iter().position(|old| {
            self.failed_material.contains(&old.id())
                && <General<H> as Mode<S, D>>::equivalent_assembly(old, &material)
        }) {
            let old = &self.material[index];
            let bytes = self.bytes - old.retained_bytes();
            let Some(bytes) = bytes.checked_add(material.retained_bytes()) else {
                return false;
            };
            if bytes > <General<H> as Mode<S, D>>::ASSEMBLY_BUDGET {
                return false;
            }
            self.failed_material.retain(|id| id != &old.id());
            self.material[index] = material;
            self.bytes = bytes;
            return true;
        }
        // Semantic aliases can authenticate under different signing scopes.
        // Preserve bounded distinct proofs until actual assembly checks them.
        let Some(bytes) = self.bytes.checked_add(material.retained_bytes()) else {
            return false;
        };
        if bytes > <General<H> as Mode<S, D>>::ASSEMBLY_BUDGET
            || self.material.len() >= self.participants
        {
            return false;
        }
        self.bytes = bytes;
        self.material.push(material);
        true
    }

    fn push(&mut self, vote: Self::Vote, verified: bool) {
        let owner = usize::from(vote.signer());
        if self.complete || owner >= self.participants {
            return;
        }
        if self.seen.is_empty() {
            self.seen.resize(self.participants, false);
        }
        if self.seen[owner] {
            return;
        }
        self.seen[owner] = true;
        if let Some(group) = self
            .groups
            .iter_mut()
            .find(|group| same_subject(&group.votes[0].0, &vote))
        {
            group.votes.push((vote, verified));
        } else {
            self.groups.push(Group {
                votes: vec![(vote, verified)],
            });
        }
    }

    fn retain_proposal(&mut self, proposal: &Proposal<D>) {
        self.groups
            .retain(|g| &g.votes[0].0.inner().native.statement.proposal == proposal);
        // Tentative native proposal selection can be replaced by an NQC. The
        // tracker restores matching votes, so checked material must survive too.
        // Its independent count/byte bounds still apply until view completion.
        self.seen.fill(false);
        for group in &self.groups {
            for (vote, _) in &group.votes {
                self.seen[usize::from(vote.signer())] = true;
            }
        }
    }

    fn complete(&mut self) {
        self.complete = true;
        self.groups = Vec::new();
        self.material = Vec::new();
        self.failed_material = Vec::new();
        self.seen = Vec::new();
        self.bytes = 0;
    }

    fn is_complete(&self) -> bool {
        self.complete
    }

    fn has_constructable_quorum(&self) -> bool {
        !self.complete
            && self.groups.iter().any(|group| {
                group.votes.len() >= self.quorum
                    && self.material.iter().any(|m| {
                        !self.failed_material.contains(&m.id())
                            && matches::<S, D, H>(m, &group.votes[0].0)
                    })
            })
    }

    async fn construct<R: CryptoRng + Send>(
        &mut self,
        scheme: &Arc<S>,
        round: Round,
        rng: &mut R,
        strategy: &impl Strategy,
    ) -> Option<Batch<Self::Certificate>> {
        if self.complete
            || (!self.has_constructable_quorum()
                && !self
                    .groups
                    .iter()
                    .any(|group| group.votes.iter().any(|(_, verified)| !verified)))
        {
            return None;
        }
        let mut groups = mem::take(&mut self.groups);
        let material: Vec<_> = self
            .material
            .iter()
            .filter(|m| !self.failed_material.contains(&m.id()))
            .cloned()
            .collect();
        let scheme = Arc::clone(scheme);
        let quorum = self.quorum;
        let len = groups.iter().map(|g| g.votes.len()).sum();
        let mut rng = StdRng::from_rng(rng);
        let span = info_span!(
            "simplex.batcher.construct.general",
            epoch = round.epoch().get(),
            view = round.view().get()
        );
        let (groups, batch, failed_material) = offload(len, span, strategy, move |strategy| {
            let mut batch = Batch {
                processed: 0,
                invalid: Vec::new(),
                certificate: None,
                fallback: false,
            };
            let mut failed_material = Vec::new();
            for group in &mut groups {
                group.votes.retain_mut(|(vote, verified)| {
                    if *verified {
                        return true;
                    }
                    batch.processed += 1;
                    if vote.inner().native.statement.proposal.round != round
                        || vote
                            .inner()
                            .authenticate::<H, _>(&mut rng, &scheme, WIRE_LIMITS, &strategy)
                            .is_err()
                    {
                        batch.invalid.push(vote.signer());
                        return false;
                    }
                    *verified = true;
                    true
                });
                if group.votes.len() < quorum {
                    continue;
                }
                let pairs: Vec<_> = group
                    .votes
                    .iter()
                    .take(quorum)
                    .map(|(v, _)| v.inner().clone())
                    .collect();
                for material in material.iter().filter(|m| {
                    m.proposal().round == round && matches::<S, D, H>(m, &group.votes[0].0)
                }) {
                    match material.assemble::<H, _>(&mut rng, &scheme, &pairs, &strategy) {
                        Ok(certificate) => {
                            batch.certificate = Some(Finalization::new(certificate));
                            break;
                        }
                        // A checked capability may belong to another signing scope.
                        // Retain votes and the bounded artifact, but fuse this exact
                        // failed artifact until a different proof alias is supplied.
                        Err(_) => failed_material.push(material.id()),
                    }
                }
                if batch.certificate.is_some() {
                    break;
                }
            }
            groups.retain(|group| !group.votes.is_empty());
            (groups, batch, failed_material)
        })
        .await;
        self.groups = groups;
        self.failed_material.extend(failed_material);
        if batch.certificate.is_some() {
            self.complete();
        }
        Some(batch)
    }
}

#[cfg(test)]
#[path = "general_tests.rs"]
mod tests;
