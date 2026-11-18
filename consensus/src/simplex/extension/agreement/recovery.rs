//! Complete, content-addressed M1 recovery evidence verification.
//!
//! Recovery snapshots authenticate claims about the signer's complete durable
//! lower-ballot authorizations. The voter must construct those claims atomically
//! with its issuance floor. Crypto cannot prove an honest node kept its WAL.
//! All referenced bodies are required; an unavailable body never authorizes a vote.
//! Verification is iterative and has no fixed history-depth or total-history cap.

use super::{
    FastProof, Kind, Limits, Message, Origin, Quorum, Row, Signed, Slot, Value, VerificationSource,
    VerifiedOrigin, scheme,
};
use crate::types::{Participant, Round};
use bytes::BufMut;
use commonware_codec::{
    Buf, Encode as _, EncodeSize, Error as CodecError, Read, ReadExt as _, Write,
};
use commonware_cryptography::{
    Digest, Hasher,
    certificate::{self, Scoped},
};
use commonware_parallel::Strategy;
use rand_core::CryptoRng;
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

const MATERIAL_TAG: &[u8] = b"_COMMONWARE_CONSENSUS_SIMPLEX_AGREEMENT_MATERIAL_V2";
const PROPOSAL_TAG: &[u8] = b"_COMMONWARE_CONSENSUS_SIMPLEX_AGREEMENT_RECOVERY_PROPOSAL_V2";

/// One retained lower-ballot authorization or a separately received positive proof.
#[derive(Clone, Debug)]
pub enum Entry<D: Digest> {
    /// Includes unsigned durable reservations, not only transmitted signatures.
    Authorization { message: Message<D>, evidence: D },
    /// A complete original origin, prepared certificate, or terminal certificate.
    Witness(D),
}
impl<D: Digest> Entry<D> {
    const fn evidence(&self) -> D {
        match self {
            Self::Authorization { evidence, .. } | Self::Witness(evidence) => *evidence,
        }
    }
}
impl<D: Digest> Write for Entry<D> {
    fn write(&self, w: &mut impl BufMut) {
        match self {
            Self::Authorization { message, evidence } => {
                0u8.write(w);
                message.write(w);
                evidence.write(w);
            }
            Self::Witness(evidence) => {
                1u8.write(w);
                evidence.write(w);
            }
        }
    }
}
impl<D: Digest> EncodeSize for Entry<D> {
    fn encode_size(&self) -> usize {
        1 + match self {
            Self::Authorization { message, evidence } => {
                message.encode_size() + evidence.encode_size()
            }
            Self::Witness(evidence) => evidence.encode_size(),
        }
    }
}
impl<D: Digest> Read for Entry<D> {
    type Cfg = usize;
    fn read_cfg(r: &mut impl Buf, limit: &usize) -> Result<Self, CodecError> {
        match u8::read(r)? {
            0 => Ok(Self::Authorization {
                message: Message::read_cfg(r, limit)?,
                evidence: D::read(r)?,
            }),
            1 => Ok(Self::Witness(D::read(r)?)),
            _ => Err(CodecError::Invalid("agreement history", "entry")),
        }
    }
}

/// Immutable linked history page. Its root is signed by the original RECOVER.
#[derive(Clone, Debug)]
pub struct Page<D: Digest> {
    pub slot: D,
    pub owner: Participant,
    pub previous: Option<D>,
    pub entry: Entry<D>,
}
impl<D: Digest> Page<D> {
    /// Same content address as this page wrapped in Material, without a signer type.
    pub fn id<H: Hasher<Digest = D>>(&self) -> D {
        H::hash(&[MATERIAL_TAG, &[2, 1], &self.encode()])
    }
}
impl<D: Digest> Write for Page<D> {
    fn write(&self, w: &mut impl BufMut) {
        self.slot.write(w);
        self.owner.write(w);
        self.previous.write(w);
        self.entry.write(w);
    }
}
impl<D: Digest> EncodeSize for Page<D> {
    fn encode_size(&self) -> usize {
        self.slot.encode_size()
            + self.owner.encode_size()
            + self.previous.encode_size()
            + self.entry.encode_size()
    }
}
impl<D: Digest> Read for Page<D> {
    type Cfg = usize;
    fn read_cfg(r: &mut impl Buf, limit: &usize) -> Result<Self, CodecError> {
        Ok(Self {
            slot: D::read(r)?,
            owner: Participant::read(r)?,
            previous: Option::<D>::read(r)?,
            entry: Entry::read_cfg(r, limit)?,
        })
    }
}

/// Exact carrier proposal and its complete admission witness J.
#[derive(Clone, Debug)]
pub struct Proposal<D: Digest> {
    pub round: Round,
    pub leader: Participant,
    pub value: Value<D>,
    /// Frozen initial five snapshots, sorted by their distinct signer IDs.
    pub initial: Vec<D>,
    /// At most two additional original same-carrier snapshots; never replace Q/R.
    pub extra: Vec<D>,
    /// Linked list of separately forwarded positive proofs.
    pub positive: Option<D>,
}
impl<D: Digest> Proposal<D> {
    pub fn id<H: Hasher<Digest = D>>(&self) -> D {
        H::hash(&[PROPOSAL_TAG, &self.encode()])
    }
}
impl<D: Digest> Write for Proposal<D> {
    fn write(&self, w: &mut impl BufMut) {
        self.round.write(w);
        self.leader.write(w);
        self.value.write(w);
        self.initial.write(w);
        self.extra.write(w);
        self.positive.write(w);
    }
}
impl<D: Digest> EncodeSize for Proposal<D> {
    fn encode_size(&self) -> usize {
        self.round.encode_size()
            + self.leader.encode_size()
            + self.value.encode_size()
            + self.initial.encode_size()
            + self.extra.encode_size()
            + self.positive.encode_size()
    }
}
impl<D: Digest> Read for Proposal<D> {
    type Cfg = Limits;
    fn read_cfg(r: &mut impl Buf, limits: &Limits) -> Result<Self, CodecError> {
        Ok(Self {
            round: Round::read(r)?,
            leader: Participant::read(r)?,
            value: Value::read_cfg(r, limits)?,
            initial: Vec::<D>::read_cfg(r, &((0..=7).into(), ()))?,
            extra: Vec::<D>::read_cfg(r, &((0..=7).into(), ()))?,
            positive: Option::<D>::read(r)?,
        })
    }
}

/// Bodies are referenced by their exact encoded hash, outside semantic Value ID.
/// A signature/proof encoding alias cannot change the original decision identity.
#[derive(Clone, Debug)]
pub enum Material<S: certificate::Scheme, D: Digest> {
    Origin(FastProof<S, D>),
    Page(Page<D>),
    Snapshot(Signed<S, D>),
    Proposal {
        proposal: Proposal<D>,
        endorsement: Signed<S, D>,
    },
    Prepared {
        proposal: D,
        quorum: Quorum<S, D>,
    },
    Terminal {
        authority: D,
        quorum: Quorum<S, D>,
    },
    Positive {
        previous: Option<D>,
        evidence: D,
    },
}
impl<S: certificate::Scheme, D: Digest> Material<S, D> {
    pub fn id<H: Hasher<Digest = D>>(&self) -> D {
        H::hash(&[MATERIAL_TAG, &self.encode()])
    }
    fn links(&self) -> Vec<D> {
        match self {
            Self::Origin(_) => Vec::new(),
            Self::Page(p) => p
                .previous
                .iter()
                .copied()
                .chain([p.entry.evidence()])
                .collect(),
            Self::Snapshot(s) => match &s.message.kind {
                Kind::Recover { history, .. } => history.iter().copied().collect(),
                _ => Vec::new(),
            },
            Self::Proposal { proposal: p, .. } => p
                .initial
                .iter()
                .chain(&p.extra)
                .chain(p.positive.iter())
                .copied()
                .collect(),
            Self::Prepared { proposal, .. } => vec![*proposal],
            Self::Terminal { authority, .. } => vec![*authority],
            Self::Positive { previous, evidence } => {
                previous.iter().copied().chain([*evidence]).collect()
            }
        }
    }
}
impl<S: certificate::Scheme, D: Digest> Write for Material<S, D> {
    fn write(&self, w: &mut impl BufMut) {
        2u8.write(w);
        match self {
            Self::Origin(p) => {
                0u8.write(w);
                p.write(w);
            }
            Self::Page(p) => {
                1u8.write(w);
                p.write(w);
            }
            Self::Snapshot(s) => {
                2u8.write(w);
                s.write(w);
            }
            Self::Proposal {
                proposal,
                endorsement,
            } => {
                3u8.write(w);
                proposal.write(w);
                endorsement.write(w);
            }
            Self::Prepared { proposal, quorum } => {
                4u8.write(w);
                proposal.write(w);
                quorum.write(w);
            }
            Self::Terminal { authority, quorum } => {
                5u8.write(w);
                authority.write(w);
                quorum.write(w);
            }
            Self::Positive { previous, evidence } => {
                6u8.write(w);
                previous.write(w);
                evidence.write(w);
            }
        }
    }
}
impl<S: certificate::Scheme, D: Digest> EncodeSize for Material<S, D> {
    fn encode_size(&self) -> usize {
        2 + match self {
            Self::Origin(p) => p.encode_size(),
            Self::Page(p) => p.encode_size(),
            Self::Snapshot(s) => s.encode_size(),
            Self::Proposal {
                proposal,
                endorsement,
            } => proposal.encode_size() + endorsement.encode_size(),
            Self::Prepared { proposal, quorum } => proposal.encode_size() + quorum.encode_size(),
            Self::Terminal { authority, quorum } => authority.encode_size() + quorum.encode_size(),
            Self::Positive { previous, evidence } => {
                previous.encode_size() + evidence.encode_size()
            }
        }
    }
}
impl<S: certificate::Scheme, D: Digest> Read for Material<S, D> {
    type Cfg = (Limits, <S::Certificate as Read>::Cfg);
    fn read_cfg(r: &mut impl Buf, cfg: &Self::Cfg) -> Result<Self, CodecError> {
        let (limits, cert) = cfg;
        if u8::read(r)? != 2 {
            return Err(CodecError::Invalid("agreement material", "version"));
        }
        match u8::read(r)? {
            0 => Ok(Self::Origin(FastProof::read_cfg(r, limits)?)),
            1 => Ok(Self::Page(Page::read_cfg(r, &limits.report_bytes)?)),
            2 => Ok(Self::Snapshot(Signed::read_cfg(r, &limits.report_bytes)?)),
            3 => Ok(Self::Proposal {
                proposal: Proposal::read_cfg(r, limits)?,
                endorsement: Signed::read_cfg(r, &0)?,
            }),
            4 => Ok(Self::Prepared {
                proposal: D::read(r)?,
                quorum: Quorum::read_cfg(r, cert)?,
            }),
            5 => Ok(Self::Terminal {
                authority: D::read(r)?,
                quorum: Quorum::read_cfg(r, cert)?,
            }),
            6 => Ok(Self::Positive {
                previous: Option::<D>::read(r)?,
                evidence: D::read(r)?,
            }),
            _ => Err(CodecError::Invalid("agreement material", "kind")),
        }
    }
}

/// Checked evidence role. PREPARED is not terminal and SNAPSHOT is not a vote QC.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    Origin,
    Snapshot,
    Proposal,
    Prepared,
    Terminal,
}

/// Private checked capability bound to this exact witness and original Slot.
/// The native owner must recheck live carrier/floor and retain all bodies before signing.
#[derive(Clone, Debug)]
pub struct Verified<D: Digest> {
    evidence: D,
    slot: D,
    round: Round,
    leader: Participant,
    phase: Phase,
    value: Option<Arc<Value<D>>>,
}
impl<D: Digest> Verified<D> {
    pub const fn evidence(&self) -> D {
        self.evidence
    }
    pub const fn slot(&self) -> D {
        self.slot
    }
    pub const fn round(&self) -> Round {
        self.round
    }
    pub const fn leader(&self) -> Participant {
        self.leader
    }
    pub const fn phase(&self) -> Phase {
        self.phase
    }
    pub fn value(&self) -> Option<&Value<D>> {
        self.value.as_deref()
    }
}

/// Verification or missing-material outcome; none permits signing a fallback.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Error<D: Digest> {
    #[error("missing agreement body {0:?}")]
    Missing(D),
    #[error("wrong content-addressed body")]
    Hash,
    #[error("cyclic agreement evidence")]
    Cycle,
    #[error("invalid agreement evidence: {0}")]
    Invalid(&'static str),
    #[error("agreement verification: {0}")]
    Agreement(#[from] super::Error),
    #[error("original recovery snapshots still required: {0:?}")]
    NeedSnapshots(Vec<Participant>),
    #[error("terminal catchup required using evidence {0:?}")]
    Catchup(D),
}

/// Replays the authenticated selector and historical native election context.
/// `authorize` returns a leader only for a native-authorized carrier of this Slot.
pub struct Verifier<'a, S: certificate::Scheme, D: Digest, T, P, L> {
    source: VerificationSource<'a, S>,
    slot: &'a Slot<D>,
    limits: Limits,
    strategy: &'a T,
    policy: P,
    authorize: L,
}
impl<'a, S, D: Digest, T, P, L> Verifier<'a, S, D, T, P, L>
where
    S: scheme::Scheme<D>,
    T: Strategy,
    P: Fn(&Value<D>) -> bool,
    L: Fn(Round) -> Option<Participant>,
{
    pub const fn new(
        scheme: &'a S,
        slot: &'a Slot<D>,
        limits: Limits,
        strategy: &'a T,
        policy: P,
        authorize: L,
    ) -> Self {
        Self {
            source: VerificationSource::Scheme(scheme),
            slot,
            limits,
            strategy,
            policy,
            authorize,
        }
    }

    /// Uses a captured public-only scope for the same complete proof checks.
    /// Exact Slot, selector policy and authorized native carrier context remain
    /// caller inputs. The scope does not grant signing or delivery authority.
    pub const fn new_scoped(
        scoped: &'a Scoped<S>,
        slot: &'a Slot<D>,
        limits: Limits,
        strategy: &'a T,
        policy: P,
        authorize: L,
    ) -> Self {
        Self {
            source: VerificationSource::Scoped(scoped),
            slot,
            limits,
            strategy,
            policy,
            authorize,
        }
    }

    /// Checks all reachable bodies with one roster/namespace/policy configuration.
    /// Callers may retrieve a Missing body and resume; no partial capability is returned.
    pub fn verify<'b, H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        root: D,
        resolve: impl Fn(&D) -> Option<&'b Material<S, D>>,
    ) -> Result<Verified<D>, Error<D>>
    where
        S: 'b,
        D: 'b,
    {
        self.slot.check_roster_with::<H, S>(&self.source)?;
        let mut nodes = BTreeMap::new();
        let mut visiting = BTreeSet::new();
        let mut work = vec![(root, None)];
        while let Some((id, finish)) = work.pop() {
            if nodes.contains_key(&id) {
                continue;
            }
            if let Some(body) = finish {
                let node = self.check::<H, R>(rng, body, &nodes)?;
                nodes.insert(
                    id,
                    Node {
                        kind: node,
                        links: body.links(),
                    },
                );
                visiting.remove(&id);
                continue;
            }
            if !visiting.insert(id) {
                return Err(Error::Cycle);
            }
            let body = resolve(&id).ok_or(Error::Missing(id))?;
            if body.id::<H>() != id {
                return Err(Error::Hash);
            }
            work.push((id, Some(body)));
            for child in body.links().into_iter().rev() {
                if !nodes.contains_key(&child) {
                    work.push((child, None));
                }
            }
        }
        let checked = &nodes.get(&root).ok_or(Error::Missing(root))?.kind;
        let (round, leader, phase, value) = match checked {
            Checked::Origin(_, value) => (
                self.slot.proposal.round,
                self.leader(self.slot.proposal.round)?,
                Phase::Origin,
                Some(value.clone()),
            ),
            Checked::Snapshot(s) => (s.round, s.leader, Phase::Snapshot, None),
            Checked::Proposal(m) => (m.round, m.leader, Phase::Proposal, Some(m.value.clone())),
            Checked::Prepared(m) => (m.round, m.leader, Phase::Prepared, Some(m.value.clone())),
            Checked::Terminal(m) => (m.round, m.leader, Phase::Terminal, Some(m.value.clone())),
            _ => return Err(Error::Invalid("root role")),
        };
        Ok(Verified {
            evidence: root,
            slot: self.slot.id::<H>(),
            round,
            leader,
            phase,
            value,
        })
    }
    fn leader(&self, round: Round) -> Result<Participant, Error<D>> {
        let leader = (self.authorize)(round).ok_or(Error::Invalid("unauthorized carrier"))?;
        if usize::from(leader) >= 7 || round.epoch() != self.slot.proposal.round.epoch() {
            return Err(Error::Invalid("carrier context"));
        }
        Ok(leader)
    }
    fn carrier(&self, round: Round, leader: Participant) -> Result<(), Error<D>> {
        if round <= self.slot.proposal.round || self.leader(round)? != leader {
            return Err(Error::Invalid("recovery carrier"));
        }
        Ok(())
    }
    fn check<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        body: &Material<S, D>,
        nodes: &BTreeMap<D, Node<D>>,
    ) -> Result<Checked<D>, Error<D>> {
        let slot = self.slot.id::<H>();
        Ok(match body {
            Material::Origin(p) => Checked::Origin(
                p.verify_with::<H, R>(
                    rng,
                    &self.source,
                    self.slot,
                    self.leader(self.slot.proposal.round)?,
                    self.limits,
                    &self.policy,
                    self.strategy,
                )?,
                Arc::new(p.value.clone()),
            ),
            Material::Page(p) => {
                if p.slot != slot || usize::from(p.owner) >= 7 {
                    return Err(Error::Invalid("history owner/context"));
                }
                if let Some(previous) = p.previous {
                    let Checked::Page(old) = &node(nodes, previous)?.kind else {
                        return Err(Error::Invalid("history chain"));
                    };
                    if old.owner != p.owner || old.slot != p.slot {
                        return Err(Error::Invalid("history chain owner/context"));
                    }
                }
                let authority = &node(nodes, p.entry.evidence())?.kind;
                match &p.entry {
                    Entry::Authorization { message, .. } => {
                        let (meta, kind) = match authority {
                            Checked::Origin(_, v) => (
                                Meta {
                                    round: self.slot.proposal.round,
                                    leader: self.leader(self.slot.proposal.round)?,
                                    value: v.clone(),
                                },
                                Kind::FastFinal(v.id::<H>()),
                            ),
                            Checked::Proposal(m) => (m.clone(), Kind::Prepare(m.value.id::<H>())),
                            Checked::Prepared(m) => (m.clone(), Kind::Commit(m.value.id::<H>())),
                            _ => return Err(Error::Invalid("authorization evidence role")),
                        };
                        if message
                            != &(Message {
                                slot,
                                round: meta.round,
                                leader: meta.leader,
                                kind,
                            })
                        {
                            return Err(Error::Invalid("authorization subject"));
                        }
                    }
                    Entry::Witness(_) => {
                        if !matches!(
                            authority,
                            Checked::Origin(..) | Checked::Prepared(..) | Checked::Terminal(..)
                        ) {
                            return Err(Error::Invalid("positive witness role"));
                        }
                    }
                }
                Checked::Page(p.clone())
            }
            Material::Snapshot(s) => {
                self.carrier(s.message.round, s.message.leader)?;
                let Kind::Recover { history, report } = &s.message.kind else {
                    return Err(Error::Invalid("snapshot phase"));
                };
                if s.message.slot != slot
                    || report
                        .as_ref()
                        .is_some_and(|r| r.len() > self.limits.report_bytes)
                    || !s.verify_with(rng, &self.source, self.strategy)
                {
                    return Err(Error::Invalid("snapshot authentication"));
                }
                let owner = s.attestation.signer;
                let mut next = *history;
                while let Some(id) = next {
                    let Checked::Page(p) = &node(nodes, id)?.kind else {
                        return Err(Error::Invalid("snapshot history role"));
                    };
                    if p.owner != owner {
                        return Err(Error::Invalid("snapshot history owner"));
                    }
                    if let Entry::Authorization { message, .. } = &p.entry
                        && message.round >= s.message.round
                    {
                        return Err(Error::Invalid("snapshot lower authorization"));
                    }
                    let evidence = node(nodes, p.entry.evidence())?;
                    if let Some(round) = evidence.kind.round()
                        && round >= s.message.round
                    {
                        return Err(Error::Invalid("snapshot lower evidence"));
                    }
                    next = p.previous;
                }
                Checked::Snapshot(Snapshot {
                    owner,
                    round: s.message.round,
                    leader: s.message.leader,
                    history: *history,
                    report: report.clone(),
                })
            }
            Material::Proposal {
                proposal: p,
                endorsement,
            } => {
                self.carrier(p.round, p.leader)?;
                p.value.check(self.limits)?;
                if p.value.slot != *self.slot {
                    return Err(Error::Invalid("proposal Slot"));
                }
                if endorsement.attestation.signer != p.leader
                    || endorsement.message
                        != (Message {
                            slot,
                            round: p.round,
                            leader: p.leader,
                            kind: Kind::Propose {
                                proposal: p.id::<H>(),
                                value: p.value.id::<H>(),
                            },
                        })
                    || !endorsement.verify_with(rng, &self.source, self.strategy)
                {
                    return Err(Error::Invalid("leader proposal endorsement"));
                }
                self.admit::<H>(p, nodes)?;
                Checked::Proposal(Meta {
                    round: p.round,
                    leader: p.leader,
                    value: Arc::new(p.value.clone()),
                })
            }
            Material::Prepared { proposal, quorum } => {
                let Checked::Proposal(m) = &node(nodes, *proposal)?.kind else {
                    return Err(Error::Invalid("RPC admission witness"));
                };
                self.check_quorum::<H, R>(rng, quorum, m, Kind::Prepare(m.value.id::<H>()))?;
                Checked::Prepared(m.clone())
            }
            Material::Terminal { authority, quorum } => {
                let (meta, kind) = match &node(nodes, *authority)?.kind {
                    Checked::Origin(_, value) => (
                        Meta {
                            round: self.slot.proposal.round,
                            leader: self.leader(self.slot.proposal.round)?,
                            value: value.clone(),
                        },
                        Kind::FastFinal(value.id::<H>()),
                    ),
                    Checked::Prepared(m) => (m.clone(), Kind::Commit(m.value.id::<H>())),
                    _ => return Err(Error::Invalid("terminal authority")),
                };
                self.check_quorum::<H, R>(rng, quorum, &meta, kind)?;
                Checked::Terminal(meta)
            }
            Material::Positive { previous, evidence } => {
                if let Some(id) = previous
                    && !matches!(node(nodes, *id)?.kind, Checked::Positive)
                {
                    return Err(Error::Invalid("positive chain"));
                }
                if !matches!(
                    node(nodes, *evidence)?.kind,
                    Checked::Origin(..) | Checked::Prepared(..) | Checked::Terminal(..)
                ) {
                    return Err(Error::Invalid("positive evidence role"));
                }
                Checked::Positive
            }
        })
    }
    fn check_quorum<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        quorum: &Quorum<S, D>,
        meta: &Meta<D>,
        kind: Kind<D>,
    ) -> Result<(), Error<D>> {
        if quorum.message
            != (Message {
                slot: self.slot.id::<H>(),
                round: meta.round,
                leader: meta.leader,
                kind,
            })
            || !quorum.verify_with(rng, &self.source, self.strategy)
        {
            return Err(Error::Invalid("exact phase quorum"));
        }
        Ok(())
    }
    fn admit<H: Hasher<Digest = D>>(
        &self,
        p: &Proposal<D>,
        nodes: &BTreeMap<D, Node<D>>,
    ) -> Result<(), Error<D>> {
        if p.initial.len() != 5 || p.extra.len() > 2 {
            return Err(Error::Invalid("snapshot population"));
        }
        let mut snapshots = BTreeMap::new();
        let mut rows = Vec::new();
        for (initial, ids) in [(true, &p.initial), (false, &p.extra)] {
            let mut previous = None;
            for id in ids {
                let Checked::Snapshot(s) = &node(nodes, *id)?.kind else {
                    return Err(Error::Invalid("snapshot role"));
                };
                if s.round != p.round
                    || s.leader != p.leader
                    || previous.is_some_and(|old| old >= s.owner)
                    || snapshots.insert(s.owner, s).is_some()
                {
                    return Err(Error::Invalid("exact original snapshot population"));
                }
                previous = Some(s.owner);
                if initial {
                    rows.push(Row {
                        owner: s.owner,
                        report: s.report.clone(),
                    });
                }
            }
        }
        if let Some(id) = p.positive
            && !matches!(node(nodes, id)?.kind, Checked::Positive)
        {
            return Err(Error::Invalid("positive list root"));
        }
        let mut reachable = BTreeSet::new();
        let mut work: Vec<_> = p
            .initial
            .iter()
            .chain(&p.extra)
            .chain(p.positive.iter())
            .copied()
            .collect();
        while let Some(id) = work.pop() {
            if reachable.insert(id) {
                work.extend(node(nodes, id)?.links.iter().copied());
            }
        }
        let mut origins = BTreeMap::new();
        let mut prepared_values = BTreeMap::new();
        let mut highest: Option<&Meta<D>> = None;
        let mut terminal = None;
        for id in reachable {
            match &node(nodes, id)?.kind {
                Checked::Origin(origin, value) => {
                    origins.entry(value.id::<H>()).or_insert((origin, value));
                }
                Checked::Prepared(m) => {
                    if m.round >= p.round {
                        return Err(Error::Invalid("RPC is not prior"));
                    }
                    if prepared_values
                        .insert(m.round, m.value.id::<H>())
                        .is_some_and(|old| old != m.value.id::<H>())
                    {
                        return Err(Error::Invalid("conflicting same-carrier RPCs"));
                    }
                    if highest.is_none_or(|old| m.round > old.round) {
                        highest = Some(m);
                    }
                }
                Checked::Terminal(m) => {
                    if m.round >= p.round {
                        return Err(Error::Invalid("terminal is not prior"));
                    }
                    if let Some((_, old)) = terminal
                        && old != m.value.id::<H>()
                    {
                        return Err(Error::Invalid("conflicting terminals"));
                    }
                    terminal = Some((id, m.value.id::<H>()));
                }
                _ => {}
            }
        }
        if let Some((id, _)) = terminal {
            return Err(Error::Catchup(id));
        }
        if let Some(rpc) = highest {
            return exact_value(&p.value, &rpc.value);
        }
        if origins.len() == 1 {
            return exact_value(&p.value, origins.first_key_value().expect("one origin").1.1);
        }
        if origins.is_empty() {
            return self.fresh(p, rows);
        }
        let mut witnesses = origins.values();
        let first = witnesses.next().expect("multiple origins").0;
        let mut faults = None;
        for (origin, _) in witnesses {
            let pair = first
                .faults(origin)?
                .ok_or(Error::Invalid("distinct origin values"))?;
            if faults.is_some_and(|old| old != pair) {
                return Err(Error::Invalid("inconsistent fault attribution"));
            }
            faults = Some(pair);
        }
        let faults = faults.expect("multiple origins");
        let honest: Vec<_> = (0..7)
            .map(Participant::new)
            .filter(|id| !faults.contains(id))
            .collect();
        let missing: Vec<_> = honest
            .iter()
            .copied()
            .filter(|id| !snapshots.contains_key(id))
            .collect();
        if !missing.is_empty() {
            return Err(Error::NeedSnapshots(missing));
        }
        let mut counts = BTreeMap::<D, usize>::new();
        for owner in honest {
            let mut next = snapshots[&owner].history;
            let mut own = None;
            while let Some(id) = next {
                let Checked::Page(page) = &node(nodes, id)?.kind else {
                    return Err(Error::Invalid("honest history"));
                };
                if let Entry::Authorization {
                    message:
                        Message {
                            kind: Kind::FastFinal(value),
                            ..
                        },
                    ..
                } = &page.entry
                {
                    if own.is_some_and(|old| old != *value) {
                        return Err(Error::Invalid("honest FAST fork"));
                    }
                    own = Some(*value);
                }
                next = page.previous;
            }
            if let Some(value) = own {
                *counts.entry(value).or_default() += 1;
            }
        }
        let possible: Vec<_> = counts
            .into_iter()
            .filter(|(_, count)| *count >= 3)
            .map(|(v, _)| v)
            .collect();
        match possible.as_slice() {
            [] => self.fresh(p, rows),
            [v] => exact_value(
                &p.value,
                origins
                    .get(v)
                    .ok_or(Error::Invalid("missing possible FAST origin"))?
                    .1,
            ),
            _ => Err(Error::Invalid("multiple possible FAST terminals")),
        }
    }
    fn fresh(&self, p: &Proposal<D>, rows: Vec<Row>) -> Result<(), Error<D>> {
        if p.value.origin
            != (Origin::Recovery {
                round: p.round,
                leader: p.leader,
            })
            || p.value.reports != rows
            || !(self.policy)(&p.value)
        {
            return Err(Error::Invalid("fresh selector population/result"));
        }
        Ok(())
    }
}

fn exact_value<D: Digest>(actual: &Value<D>, expected: &Value<D>) -> Result<(), Error<D>> {
    if actual != expected {
        return Err(Error::Invalid("carried original Value changed"));
    }
    Ok(())
}
fn node<D: Digest>(nodes: &BTreeMap<D, Node<D>>, id: D) -> Result<&Node<D>, Error<D>> {
    nodes.get(&id).ok_or(Error::Missing(id))
}
struct Node<D: Digest> {
    kind: Checked<D>,
    links: Vec<D>,
}
#[derive(Clone)]
struct Meta<D: Digest> {
    round: Round,
    leader: Participant,
    value: Arc<Value<D>>,
}
struct Snapshot<D: Digest> {
    owner: Participant,
    round: Round,
    leader: Participant,
    history: Option<D>,
    report: Option<bytes::Bytes>,
}
enum Checked<D: Digest> {
    Origin(VerifiedOrigin<D>, Arc<Value<D>>),
    Page(Page<D>),
    Snapshot(Snapshot<D>),
    Proposal(Meta<D>),
    Prepared(Meta<D>),
    Terminal(Meta<D>),
    Positive,
}
impl<D: Digest> Checked<D> {
    fn round(&self) -> Option<Round> {
        match self {
            Self::Origin(_, v) => Some(v.slot.proposal.round),
            Self::Proposal(m) | Self::Prepared(m) | Self::Terminal(m) => Some(m.round),
            _ => None,
        }
    }
}
