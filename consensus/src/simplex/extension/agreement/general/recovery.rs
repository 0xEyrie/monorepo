//! Inactive general-roster interpretation-recovery evidence.
//!
//! Complete closure verification is independent of native P finality, local
//! failure deadlines, journal synchronization and signer release. No decoded
//! frame, data-only history, old phase certificate or application callback alone
//! grants a recovery vote. All required material must be present and checked.

use super::{
    Core, Decision, First, Frame, Kind, Limits, Message, Origin, OriginBody, Quorum, ScopeId,
    Signed, VerificationContext, VerifiedRows, entry, issuance, read_blob, scheme, write_blob,
};
use crate::types::{Participant, Round};
use bytes::{Buf as _, BufMut, Bytes};
use commonware_codec::{
    Buf, Encode as _, EncodeSize, Error as CodecError, Read, ReadExt as _, Write,
};
use commonware_cryptography::{Digest, Hasher, certificate};
use commonware_parallel::Strategy;
use rand_core::CryptoRng;
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

const BODY: &[u8] = b"_COMMONWARE_CONSENSUS_G1_RECOVERY_BODY_V1";
const MATERIAL: &[u8] = b"_COMMONWARE_CONSENSUS_G1_RECOVERY_MATERIAL_V1";
/// Full material wrapper cap, including a maximum-sized existing native object.
pub const MAX_MATERIAL_BYTES: usize = super::MAX_EVIDENCE_BYTES + super::MAX_FIRST_BYTES;
const FAST_CERTIFICATE: &[u8] = b"_COMMONWARE_CONSENSUS_G1_FAST_TERMINAL_V1";

/// New recovery roles. These are not the old decision-only Phase variants.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    /// Coordinator endorsement of one exact unsigned admission body.
    Propose,
    /// One exact proposal/decision preparation.
    Prepare,
    /// Commitment after complete matching RPC verification.
    Commit,
}

/// Exact recovery subject. Certificate aliases do not change this subject.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Subject<D: Digest> {
    /// Original fixed Core identity.
    pub core: D,
    /// Complete immutable input identity.
    pub input: D,
    /// Semantic entry target identity, distinct from its proof artifact.
    pub entry: D,
    /// Canonical unsigned ProposalBody identity, excluding its endorsement.
    pub proposal: D,
    /// Semantic complete Decision identity.
    pub decision: D,
}
impl<D: Digest> Write for Subject<D> {
    fn write(&self, w: &mut impl BufMut) {
        self.core.write(w);
        self.input.write(w);
        self.entry.write(w);
        self.proposal.write(w);
        self.decision.write(w);
    }
}
impl<D: Digest> EncodeSize for Subject<D> {
    fn encode_size(&self) -> usize {
        5 * D::SIZE
    }
}
impl<D: Digest> Read for Subject<D> {
    type Cfg = ();
    fn read_cfg(r: &mut impl Buf, _: &()) -> Result<Self, CodecError> {
        if D::SIZE != 32 {
            return Err(CodecError::Invalid("G1 recovery subject", "digest"));
        }
        Ok(Self {
            core: D::read(r)?,
            input: D::read(r)?,
            entry: D::read(r)?,
            proposal: D::read(r)?,
            decision: D::read(r)?,
        })
    }
}
#[cfg(feature = "arbitrary")]
impl<'a, D: Digest + arbitrary::Arbitrary<'a>> arbitrary::Arbitrary<'a> for Subject<D> {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        Ok(Self {
            core: u.arbitrary()?,
            input: u.arbitrary()?,
            entry: u.arbitrary()?,
            proposal: u.arbitrary()?,
            decision: u.arbitrary()?,
        })
    }
}

/// Choice justified by the complete frozen admission closure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Choice<D: Digest> {
    /// Exact highest prior RPC, or exact original fast origin when no RPC exists.
    Carry(D),
    /// Replay of the configured deterministic Build over these exact RECOVER rows.
    Fresh {
        /// Checked application population identity.
        population: D,
        /// Complete opaque deterministic Build record.
        build: Bytes,
        /// Complete opaque application material catalogue.
        material: Bytes,
    },
}

/// Canonical unsigned coordinator body. Its identity never includes a signature.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProposalBody<D: Digest> {
    /// Exact full semantic value; carried bytes are never recomputed.
    pub value: Decision<D>,
    /// Exact checked entry proof artifact chosen by the coordinator.
    pub entry: D,
    /// Exactly q distinct original notice artifacts, increasing by signer owner.
    pub histories: Vec<D>,
    /// Sorted, distinct separately supplied full origin/RPC/terminal artifacts.
    pub positive: Vec<D>,
    /// Full justification of the chosen value.
    pub choice: Choice<D>,
}
impl<D: Digest> ProposalBody<D> {
    /// Canonical unsigned identity in its fresh type-specific domain.
    pub fn id<H: Hasher<Digest = D>>(&self) -> D {
        H::hash(&[BODY, &self.encode()])
    }
    fn preflight(&self, limits: Limits) -> Result<(), Error<D>> {
        limits.check()?;
        if self.histories.len() > 64
            || self.positive.len() > super::MAX_EVIDENCE_BYTES / D::SIZE
            || self.value.order.len() > limits.order_bytes
        {
            return Err(Error::Limit);
        }
        if let Choice::Fresh {
            build, material, ..
        } = &self.choice
            && (build.len() > limits.build_bytes || material.len() > limits.material_bytes)
        {
            return Err(Error::Limit);
        }
        if self.encode_size() > super::MAX_EVIDENCE_BYTES {
            return Err(Error::Limit);
        }
        Ok(())
    }
}
fn write_ids<D: Digest>(ids: &[D], w: &mut impl BufMut) {
    u32::try_from(ids.len())
        .expect("G1 references exceed u32")
        .write(w);
    for id in ids {
        id.write(w);
    }
}
fn read_ids<D: Digest>(r: &mut impl Buf, cap: usize) -> Result<Vec<D>, CodecError> {
    let n = u32::read(r)? as usize;
    if n > cap || n > r.remaining() / D::SIZE {
        return Err(CodecError::InvalidLength(n));
    }
    (0..n).map(|_| D::read(r)).collect()
}
impl<D: Digest> Frame for ProposalBody<D> {
    const MAGIC: [u8; 4] = *b"G1P1";
    type Cfg = Limits;
    fn body_size(&self) -> usize {
        self.value.encode_size()
            + D::SIZE
            + 8
            + D::SIZE * (self.histories.len() + self.positive.len())
            + 1
            + match &self.choice {
                Choice::Carry(_) => D::SIZE,
                Choice::Fresh {
                    build, material, ..
                } => D::SIZE + super::blob_size(build) + super::blob_size(material),
            }
    }
    fn write_body(&self, w: &mut impl BufMut) {
        self.value.write(w);
        self.entry.write(w);
        write_ids(&self.histories, w);
        write_ids(&self.positive, w);
        match &self.choice {
            Choice::Carry(id) => {
                0u8.write(w);
                id.write(w);
            }
            Choice::Fresh {
                population,
                build,
                material,
            } => {
                1u8.write(w);
                population.write(w);
                write_blob(build, w);
                write_blob(material, w);
            }
        }
    }
    fn read_body(r: &mut impl Buf, limits: &Limits) -> Result<Self, CodecError> {
        limits
            .check()
            .map_err(|_| CodecError::Invalid("G1 recovery body", "limits"))?;
        let value = Decision::read_cfg(r, limits)?;
        let entry = D::read(r)?;
        let histories = read_ids(r, 64)?;
        let positive = read_ids(r, super::MAX_EVIDENCE_BYTES / D::SIZE)?;
        let choice = match u8::read(r)? {
            0 => Choice::Carry(D::read(r)?),
            1 => Choice::Fresh {
                population: D::read(r)?,
                build: read_blob(r, limits.build_bytes)?,
                material: read_blob(r, limits.material_bytes)?,
            },
            _ => return Err(CodecError::Invalid("G1 recovery body", "choice")),
        };
        Ok(Self {
            value,
            entry,
            histories,
            positive,
            choice,
        })
    }
}
frame_codec!(ProposalBody<D>, [D: Digest], Limits);

/// Flat content-addressed evidence. Native objects keep their original IDs.
#[derive(Clone, Debug)]
pub enum Material<S: scheme::Scheme<D>, D: Digest> {
    /// Full entry provenance, never native voting permission.
    Entry(entry::Proof<S, D>),
    /// Original unsigned SELECT authority, not an original fast origin.
    Body(OriginBody<S, D>),
    /// Genuine gated original origin.
    Origin(Origin<S, D>),
    /// Genuine original interpretation terminal, not native P finality.
    FastTerminal { origin: D, quorum: Quorum<S, D> },
    /// One original/per-ballot local journal page.
    Page(issuance::HistoryPage<D>),
    /// Exact original signed notice, joined to one full entry artifact.
    History { entry: D, notice: Signed<S, D> },
    /// Full unsigned body, required before local PROPOSE reservation.
    Admission(ProposalBody<D>),
    /// Complete body plus actual coordinator endorsement.
    Proposal {
        admission: D,
        endorsement: Signed<S, D>,
    },
    /// Genuine q new-role PREPARE signatures and full signed proposal closure.
    Rpc { proposal: D, quorum: Quorum<S, D> },
    /// Genuine q new-role COMMIT signatures and full matching RPC closure.
    Terminal { rpc: D, quorum: Quorum<S, D> },
    /// Exact original q-FAST certificate artifact referenced by an old WAL record.
    FastQuorum(Quorum<S, D>),
    /// Exact f+1 WISH cause with predecessor-entry links only, never an entry.
    Amplification(entry::Amplification<S, D>),
}

/// Finite, explicit resources for complete iterative closure verification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Bounds {
    pub nodes: u32,
    pub links: u64,
    pub encoded_bytes: u64,
    /// Coarse graph/closure/replay work quanta, including repeated admission facts.
    /// Internal WAL searches and application callback work are not metered here.
    pub work: u64,
    /// Per-entry provenance budget; each exact entry artifact is independently checked.
    pub entry: entry::Bounds,
    /// Complete declared-prefix replay budget for each history node.
    pub history: issuance::history::Bounds,
}

/// Evidence role, distinct from its cryptographic wire phase.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Role {
    Admission,
    Proposal,
    Rpc,
    Terminal,
}

/// Private-constructor complete checked authority for native-owned staging.
/// The native owner must still check actual native admission, current entry,
/// floors, once-choice, material custody and WAL barriers before signer release.
#[derive(Clone, Debug)]
pub struct Verified<D: Digest> {
    scope: ScopeId,
    role: Role,
    evidence: D,
    encoded_size: u64,
    limits: Limits,
    slot: D,
    core: D,
    input: D,
    entry: D,
    attempt: u64,
    round: Round,
    leader: Participant,
    proposal: D,
    decision: D,
    value: Arc<Decision<D>>,
    origin: D,
}
impl<D: Digest> Verified<D> {
    /// Whether this receipt belongs to the same local verification context.
    /// Revalidate the original evidence when the signing ledger is reopened.
    pub fn matches_context<S: certificate::Scheme>(
        &self,
        context: &VerificationContext<S>,
    ) -> bool {
        context.matches_scope(&self.scope)
    }
    pub const fn role(&self) -> Role {
        self.role
    }
    pub const fn evidence(&self) -> D {
        self.evidence
    }
    pub const fn encoded_size(&self) -> u64 {
        self.encoded_size
    }
    pub const fn limits(&self) -> Limits {
        self.limits
    }
    pub const fn slot(&self) -> D {
        self.slot
    }
    pub const fn core(&self) -> D {
        self.core
    }
    pub const fn input(&self) -> D {
        self.input
    }
    pub const fn entry(&self) -> D {
        self.entry
    }
    pub const fn attempt(&self) -> u64 {
        self.attempt
    }
    pub const fn round(&self) -> Round {
        self.round
    }
    pub const fn leader(&self) -> Participant {
        self.leader
    }
    pub const fn proposal(&self) -> D {
        self.proposal
    }
    pub const fn decision(&self) -> D {
        self.decision
    }
    pub fn value(&self) -> &Decision<D> {
        &self.value
    }
    pub const fn origin(&self) -> D {
        self.origin
    }
    const fn message(&self, phase: Phase) -> Message<D> {
        Message {
            slot: self.slot,
            round: self.round,
            leader: self.leader,
            kind: Kind::Recovery {
                phase,
                subject: Subject {
                    core: self.core,
                    input: self.input,
                    entry: self.entry,
                    proposal: self.proposal,
                    decision: self.decision,
                },
            },
        }
    }
}

/// Authenticated original RECOVER population for application Build replay.
/// No decoder or external constructor can fabricate checked report provenance.
pub struct VerifiedRecoveryRows<S: certificate::Scheme, D: Digest> {
    core: Core<D>,
    input: D,
    entry: D,
    attempt: u64,
    round: Round,
    leader: Participant,
    originals: Vec<Signed<S, D>>,
    participants: Vec<S::PublicKey>,
}
impl<S: certificate::Scheme, D: Digest> VerifiedRecoveryRows<S, D> {
    pub const fn core(&self) -> &Core<D> {
        &self.core
    }
    pub const fn input(&self) -> D {
        self.input
    }
    pub const fn entry(&self) -> D {
        self.entry
    }
    pub const fn attempt(&self) -> u64 {
        self.attempt
    }
    pub const fn round(&self) -> Round {
        self.round
    }
    pub const fn leader(&self) -> Participant {
        self.leader
    }
    pub fn originals(&self) -> &[Signed<S, D>] {
        &self.originals
    }
    pub fn participants(&self) -> &[S::PublicKey] {
        &self.participants
    }
}

/// Failure grants no partial admission, fallback or terminal installation.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Error<D: Digest> {
    #[error("missing recovery material {0:?}")]
    Missing(D),
    #[error("wrong recovery content address")]
    Hash,
    #[error("cyclic recovery evidence")]
    Cycle,
    #[error("recovery resource limit")]
    Limit,
    #[error("invalid recovery evidence: {0}")]
    Invalid(&'static str),
    /// A fresh proposal cannot supersede this authenticated predecessor.
    /// The caller must submit a new full carry for ordinary admission.
    #[error("carry required: {0:?}")]
    CarryRequired(D),
    #[error("terminal catchup required: {0:?}")]
    Catchup(D),
    #[error("same or higher recovery RPC already exists: {0:?}")]
    Stale(D),
    #[error(transparent)]
    Agreement(#[from] super::Error),
}

impl<S: scheme::Scheme<D>, D: Digest> Material<S, D> {
    /// Exact immutable artifact identity. Preflight externally supplied objects first.
    pub fn id<H: Hasher<Digest = D>>(&self) -> D {
        match self {
            Self::Entry(p) => p.artifact_id::<H>(),
            Self::Amplification(p) => p.artifact_id::<H>(),
            Self::Body(b) => b.id::<H>(),
            Self::Origin(o) => o.id::<H>(),
            Self::Page(p) => p.id::<H>(),
            Self::Admission(b) => b.id::<H>(),
            Self::FastQuorum(q) => H::hash(&[FAST_CERTIFICATE, &q.encode()]),
            _ => H::hash(&[MATERIAL, &self.encode()]),
        }
    }
    /// Direct content-addressed dependencies to retain with this original.
    pub fn links(&self) -> Vec<D> {
        match self {
            Self::Entry(p) => p.dependencies().collect(),
            Self::Amplification(p) => p.dependencies().collect(),
            Self::Body(_) | Self::Origin(_) | Self::FastQuorum(_) => Vec::new(),
            Self::FastTerminal { origin, .. } => vec![*origin],
            Self::Page(p) => {
                let mut ids = p.previous().into_iter().collect::<Vec<_>>();
                use issuance::Action;
                match p.record().action() {
                    Action::Reserve {
                        authority: Some(id),
                        ..
                    } => ids.push(*id),
                    Action::Terminal {
                        origin,
                        certificate,
                        ..
                    } => {
                        ids.push(*origin);
                        ids.push(*certificate);
                    }
                    Action::RetainOrigin { origin, .. } => ids.push(*origin),
                    Action::Enter { authority, .. } => ids.push(*authority),
                    Action::AdvanceWish { message, cause, .. } => {
                        if let Kind::Wish(w) = &message.kind {
                            ids.push(w.predecessor);
                        }
                        if let issuance::WishCause::Amplification(id) = cause {
                            ids.push(*id);
                        }
                    }
                    Action::RetainRpc { proof, .. } | Action::RecoveryTerminal { proof, .. } => {
                        ids.push(*proof)
                    }
                    _ => {}
                }
                ids
            }
            Self::History { entry, notice } => {
                let mut ids = vec![*entry];
                if let Kind::Recover(r) = &notice.message.kind {
                    ids.extend(r.snapshot.head());
                }
                ids
            }
            Self::Admission(b) => std::iter::once(b.entry)
                .chain(b.histories.iter().copied())
                .chain(b.positive.iter().copied())
                .chain(match b.choice {
                    Choice::Carry(id) => Some(id),
                    _ => None,
                })
                .collect(),
            Self::Proposal { admission, .. } => vec![*admission],
            Self::Rpc { proposal, .. } => vec![*proposal],
            Self::Terminal { rpc, .. } => vec![*rpc],
        }
    }
    fn link_count(&self) -> usize {
        match self {
            Self::Entry(p) => p.dependencies().count(),
            Self::Amplification(p) => p.dependencies().count(),
            Self::Body(_) | Self::Origin(_) | Self::FastQuorum(_) => 0,
            Self::Page(p) => {
                usize::from(p.previous().is_some())
                    + match p.record().action() {
                        issuance::Action::Terminal { .. } => 2,
                        issuance::Action::AdvanceWish { cause, .. } => {
                            1 + usize::from(matches!(cause, issuance::WishCause::Amplification(_)))
                        }
                        issuance::Action::Reserve {
                            authority: Some(_), ..
                        }
                        | issuance::Action::RetainOrigin { .. }
                        | issuance::Action::Enter { .. }
                        | issuance::Action::RetainRpc { .. }
                        | issuance::Action::RecoveryTerminal { .. } => 1,
                        _ => 0,
                    }
            }
            Self::History { notice, .. } => {
                1 + usize::from(
                    matches!(&notice.message.kind,Kind::Recover(r) if r.snapshot.head().is_some()),
                )
            }
            Self::Admission(b) => {
                1 + b.histories.len()
                    + b.positive.len()
                    + usize::from(matches!(b.choice, Choice::Carry(_)))
            }
            _ => 1,
        }
    }
    fn preflight(&self, c: super::Committee, l: Limits) -> Result<(), Error<D>> {
        let signed = |s: &Signed<S, D>| -> Result<(), Error<D>> {
            s.message.check(c, l)?;
            if s.encode_size() > super::MAX_FIRST_BYTES {
                return Err(Error::Limit);
            }
            Ok(())
        };
        let body = |b: &OriginBody<S, D>| -> Result<(), Error<D>> {
            if b.core.followers.len() > 63
                || b.firsts.len() > 64
                || b.decision.order.len() > l.order_bytes
                || b.build.len() > l.build_bytes
                || b.material.len() > l.material_bytes
            {
                return Err(Error::Limit);
            }
            for s in &b.firsts {
                signed(s)?;
            }
            if b.encode_size() > l.origin_bytes || b.encode_size() > super::MAX_EVIDENCE_BYTES {
                return Err(Error::Limit);
            }
            Ok(())
        };
        match self {
            Self::Amplification(p) => {
                p.preflight(c, l).map_err(|_| Error::Limit)?;
            }
            Self::Entry(p) => {
                p.preflight(c, l)
                    .map_err(|_| Error::Invalid("entry bounds"))?;
            }
            Self::Body(b) => body(b)?,
            Self::Origin(o) => {
                body(&o.body)?;
                signed(&o.selection)?;
                if o.encode_size() > l.origin_bytes {
                    return Err(Error::Limit);
                }
            }
            Self::FastTerminal { quorum, .. }
            | Self::Rpc { quorum, .. }
            | Self::Terminal { quorum, .. }
            | Self::FastQuorum(quorum) => {
                quorum.message.check(c, l)?;
                super::bounded(quorum)?;
            }
            Self::Page(p) => {
                if p.record().core().followers.len() > 63 {
                    return Err(Error::Limit);
                }
                if let issuance::Action::Reserve { message, .. }
                | issuance::Action::AdvanceWish { message, .. } = p.record().action()
                {
                    message.check(c, l)?;
                }
                if let issuance::Action::Released { frame, .. } = p.record().action()
                    && frame.len() > super::MAX_FIRST_BYTES
                {
                    return Err(Error::Limit);
                }
                if p.encode_size() > <issuance::HistoryPage<D> as Frame>::MAX_BYTES {
                    return Err(Error::Limit);
                }
            }
            Self::History { notice, .. }
            | Self::Proposal {
                endorsement: notice,
                ..
            } => signed(notice)?,
            Self::Admission(b) => b.preflight(l)?,
        }
        if self.encode_size() > MAX_MATERIAL_BYTES {
            return Err(Error::Limit);
        }
        Ok(())
    }
}
impl<S: scheme::Scheme<D>, D: Digest> Frame for Material<S, D> {
    const MAGIC: [u8; 4] = *b"G1Z1";
    const MAX_BYTES: usize = MAX_MATERIAL_BYTES;
    type Cfg = (Limits, <S::Certificate as Read>::Cfg);
    fn body_size(&self) -> usize {
        1 + match self {
            Self::Entry(p) => p.encode_size(),
            Self::Amplification(p) => p.encode_size(),
            Self::Body(b) => b.encode_size(),
            Self::Origin(o) => o.encode_size(),
            Self::Page(p) => p.encode_size(),
            Self::Admission(b) => b.encode_size(),
            Self::History { notice, .. }
            | Self::Proposal {
                endorsement: notice,
                ..
            } => D::SIZE + notice.encode_size(),
            Self::FastTerminal { quorum, .. }
            | Self::Rpc { quorum, .. }
            | Self::Terminal { quorum, .. } => D::SIZE + quorum.encode_size(),
            Self::FastQuorum(q) => q.encode_size(),
        }
    }
    fn write_body(&self, w: &mut impl BufMut) {
        match self {
            Self::Entry(p) => {
                0u8.write(w);
                p.write(w)
            }
            Self::Body(b) => {
                1u8.write(w);
                b.write(w)
            }
            Self::Origin(o) => {
                2u8.write(w);
                o.write(w)
            }
            Self::FastTerminal { origin, quorum } => {
                3u8.write(w);
                origin.write(w);
                quorum.write(w)
            }
            Self::Page(p) => {
                4u8.write(w);
                p.write(w)
            }
            Self::History { entry, notice } => {
                5u8.write(w);
                entry.write(w);
                notice.write(w)
            }
            Self::Admission(b) => {
                6u8.write(w);
                b.write(w)
            }
            Self::Proposal {
                admission,
                endorsement,
            } => {
                7u8.write(w);
                admission.write(w);
                endorsement.write(w)
            }
            Self::Rpc { proposal, quorum } => {
                8u8.write(w);
                proposal.write(w);
                quorum.write(w)
            }
            Self::Terminal { rpc, quorum } => {
                9u8.write(w);
                rpc.write(w);
                quorum.write(w)
            }
            Self::FastQuorum(q) => {
                10u8.write(w);
                q.write(w)
            }
            Self::Amplification(p) => {
                11u8.write(w);
                p.write(w);
            }
        }
    }
    fn read_body(r: &mut impl Buf, cfg: &Self::Cfg) -> Result<Self, CodecError> {
        Ok(match u8::read(r)? {
            0 => Self::Entry(entry::Proof::read_cfg(r, cfg)?),
            1 => Self::Body(OriginBody::read_cfg(r, &cfg.0)?),
            2 => Self::Origin(Origin::read_cfg(r, &cfg.0)?),
            3 => Self::FastTerminal {
                origin: D::read(r)?,
                quorum: Quorum::read_cfg(r, cfg)?,
            },
            4 => Self::Page(issuance::HistoryPage::read_cfg(r, &cfg.0)?),
            5 => Self::History {
                entry: D::read(r)?,
                notice: Signed::read_cfg(r, &cfg.0)?,
            },
            6 => Self::Admission(ProposalBody::read_cfg(r, &cfg.0)?),
            7 => Self::Proposal {
                admission: D::read(r)?,
                endorsement: Signed::read_cfg(r, &cfg.0)?,
            },
            8 => Self::Rpc {
                proposal: D::read(r)?,
                quorum: Quorum::read_cfg(r, cfg)?,
            },
            9 => Self::Terminal {
                rpc: D::read(r)?,
                quorum: Quorum::read_cfg(r, cfg)?,
            },
            10 => Self::FastQuorum(Quorum::read_cfg(r, cfg)?),
            11 => Self::Amplification(entry::Amplification::read_cfg(r, &cfg.0)?),
            _ => return Err(CodecError::Invalid("G1 recovery material", "kind")),
        })
    }
}
frame_codec!(Material<S,D>,[S:scheme::Scheme<D>,D:Digest],(Limits,<S::Certificate as Read>::Cfg));

struct Meter {
    bytes: u64,
    links: u64,
    work: u64,
    bounds: Bounds,
}
impl Meter {
    fn work<D: Digest>(&mut self, n: u64) -> Result<(), Error<D>> {
        self.work = self
            .work
            .checked_add(n)
            .filter(|n| *n <= self.bounds.work)
            .ok_or(Error::Limit)?;
        Ok(())
    }
    fn node<D: Digest>(&mut self, size: usize, links: usize) -> Result<(), Error<D>> {
        self.bytes = self
            .bytes
            .checked_add(u64::try_from(size).map_err(|_| Error::Limit)?)
            .filter(|n| *n <= self.bounds.encoded_bytes)
            .ok_or(Error::Limit)?;
        self.links = self
            .links
            .checked_add(u64::try_from(links).map_err(|_| Error::Limit)?)
            .filter(|n| *n <= self.bounds.links)
            .ok_or(Error::Limit)?;
        self.work::<D>(1 + u64::try_from(links).map_err(|_| Error::Limit)?)
    }
}
enum Checked<'a, S: scheme::Scheme<D>, D: Digest> {
    Entry(entry::VerifiedEntry<'a, S, D>),
    Amplification(entry::VerifiedAmplification<'a, S, D>),
    Body,
    RouteBody(super::VerifiedBody<D>),
    Origin(Arc<Decision<D>>, Option<super::VerifiedBody<D>>),
    Page,
    History {
        entry: entry::Target<D>,
        notice: &'a Signed<S, D>,
    },
    Value(Verified<D>),
    FastTerminal(Arc<Decision<D>>),
    FastQuorum,
}
fn node<'a, 'b, S: scheme::Scheme<D>, D: Digest>(
    nodes: &'b BTreeMap<D, Checked<'a, S, D>>,
    id: D,
) -> Result<&'b Checked<'a, S, D>, Error<D>> {
    nodes.get(&id).ok_or(Error::Missing(id))
}
fn checked_value<'a, 'b, S: scheme::Scheme<D>, D: Digest>(
    nodes: &'b BTreeMap<D, Checked<'a, S, D>>,
    id: D,
    role: Role,
) -> Result<&'b Verified<D>, Error<D>> {
    let Checked::Value(v) = node(nodes, id)? else {
        return Err(Error::Invalid("authority role"));
    };
    if v.role != role {
        return Err(Error::Invalid("authority role"));
    }
    Ok(v)
}

#[allow(clippy::too_many_arguments)]
fn preauthenticate<H: Hasher<Digest = D>, S: scheme::Scheme<D>, D: Digest, R: CryptoRng>(
    rng: &mut R,
    s: &S,
    core: &Core<D>,
    input: D,
    material: &Material<S, D>,
    limits: Limits,
    route_scope: Option<D>,
    strategy: &impl Strategy,
    meter: &mut Meter,
) -> Result<(), Error<D>> {
    let slot = core.slot.id::<H>();
    let mut signature = |signed: &Signed<S, D>, expected_slot: D| -> Result<(), Error<D>> {
        meter.work::<D>(1)?;
        if signed.message.slot != expected_slot || !signed.verify(rng, s, limits, strategy) {
            return Err(super::Error::Signature.into());
        }
        Ok(())
    };
    let first_subject = |signed: &Signed<S, D>| {
        let Some(scope) = route_scope else {
            return Ok(slot);
        };
        let Kind::First(row) = &signed.message.kind else {
            return Err(Error::Invalid("route FIRST role"));
        };
        if !row.matches_route_scope(
            scope,
            First::empty_route_scope::<H>(&core.slot, core.leader, input),
        ) {
            return Err(Error::Invalid("route FIRST scope"));
        }
        Ok(First::route_slot::<H>(&core.slot, row.core, input))
    };
    match material {
        Material::Origin(o) => {
            for first in &o.body.firsts {
                signature(first, first_subject(first)?)?;
            }
            signature(&o.selection, slot)?;
            if o.selection.message
                != (Message {
                    slot: core.slot.id::<H>(),
                    round: core.slot.proposal.round,
                    leader: core.leader,
                    kind: Kind::Select {
                        body: o.body.id::<H>(),
                        decision: o.body.decision.id::<H>(),
                    },
                })
            {
                return Err(Error::Invalid("original SELECT subject"));
            }
        }
        Material::Body(b) => {
            for first in &b.firsts {
                signature(first, first_subject(first)?)?;
            }
        }
        Material::History { notice, .. } => {
            signature(notice, slot)?;
            let Kind::Recover(r) = &notice.message.kind else {
                return Err(Error::Invalid("history notice role"));
            };
            if r.core != core.id::<H>() || r.input != input {
                return Err(Error::Invalid("history notice context"));
            }
        }
        Material::Proposal { endorsement, .. } => {
            signature(endorsement, slot)?;
            if !matches!(&endorsement.message.kind,Kind::Recovery{phase:Phase::Propose,subject} if subject.core==core.id::<H>()&&subject.input==input)
            {
                return Err(Error::Invalid("PROPOSE role/context"));
            }
        }
        Material::Page(p) => {
            if p.record().core() != core || p.record().input() != input {
                return Err(Error::Invalid("page context"));
            }
            if let issuance::Action::Released { frame, .. } = p.record().action() {
                let signed =
                    <Signed<S, D> as commonware_codec::Decode>::decode_cfg(frame.clone(), &limits)
                        .map_err(|_| Error::Invalid("outbox codec"))?;
                // Only the initial route has its own scoped subject. Its native
                // slot, reporter, prior reservation and exact release are checked
                // again when replaying the complete page chain.
                let expected = match &signed.message.kind {
                    Kind::First(row) if row.core != core.id::<H>() && row.input == input => {
                        First::route_slot::<H>(&core.slot, row.core, input)
                    }
                    _ => slot,
                };
                signature(&signed, expected)?;
            }
        }
        Material::Amplification(p) => {
            for original in &p.wishes {
                meter.work::<D>(1)?;
                if !original.verify(rng, s, limits, strategy) {
                    return Err(Error::Invalid("WISH amplification signature"));
                }
                let Kind::Wish(w) = &original.message.kind else {
                    return Err(Error::Invalid("WISH amplification role"));
                };
                if original.message.slot != core.slot.id::<H>()
                    || w.target.core != core.id::<H>()
                    || w.target.input != input
                    || original.message.round != p.target.ballot
                    || original.message.leader != p.target.leader
                {
                    return Err(Error::Invalid("WISH amplification context"));
                }
            }
        }
        Material::Entry(p) => match p {
            entry::Proof::Initial { notarization, .. } => {
                meter.work::<D>(s.participants().len() as u64)?;
                if notarization.proposal != core.slot.proposal
                    || !notarization.verify(rng, s, strategy)
                {
                    return Err(Error::Invalid("initial native NQC"));
                }
            }
            entry::Proof::Higher { wishes, .. } => {
                for wish in wishes {
                    signature(wish, slot)?;
                }
            }
        },
        Material::FastTerminal { quorum, .. }
        | Material::FastQuorum(quorum)
        | Material::Rpc { quorum, .. }
        | Material::Terminal { quorum, .. } => {
            meter.work::<D>(s.participants().len() as u64)?;
            if quorum.message.slot != core.slot.id::<H>()
                || !quorum.verify(rng, s, limits, strategy)
            {
                return Err(Error::Invalid("phase certificate"));
            }
            match material {
                Material::FastTerminal { .. } | Material::FastQuorum(_) => {
                    if !matches!(
                        quorum.message.kind,
                        Kind::Phase {
                            phase: super::Phase::FastFinal,
                            ..
                        }
                    ) {
                        return Err(Error::Invalid("original FAST role"));
                    }
                }
                Material::Rpc { .. } => {
                    if !matches!(&quorum.message.kind,Kind::Recovery{phase:Phase::Prepare,subject} if subject.core==core.id::<H>()&&subject.input==input)
                    {
                        return Err(Error::Invalid("RPC role/context"));
                    }
                }
                Material::Terminal { .. } => {
                    if !matches!(&quorum.message.kind,Kind::Recovery{phase:Phase::Commit,subject} if subject.core==core.id::<H>()&&subject.input==input)
                    {
                        return Err(Error::Invalid("terminal role/context"));
                    }
                }
                _ => unreachable!(),
            }
        }
        Material::Admission(_) => {}
    }
    Ok(())
}

fn original_terminal<S: scheme::Scheme<D>, D: Digest, H: Hasher<Digest = D>>(
    core: &Core<D>,
    value: &Decision<D>,
    quorum: &Quorum<S, D>,
) -> Result<(), Error<D>> {
    if quorum.message
        != (Message {
            slot: core.slot.id::<H>(),
            round: core.slot.proposal.round,
            leader: core.leader,
            kind: Kind::Phase {
                phase: super::Phase::FastFinal,
                decision: value.id::<H>(),
            },
        })
    {
        return Err(Error::Invalid("original terminal subject"));
    }
    Ok(())
}

fn admission_subject<H: Hasher<Digest = D>, S: scheme::Scheme<D>, D: Digest>(
    admission: D,
    phase: Phase,
    raw: &BTreeMap<D, &Material<S, D>>,
    core: &Core<D>,
    input: D,
) -> Result<Message<D>, Error<D>> {
    let Some(Material::Admission(body)) = raw.get(&admission).copied() else {
        return Err(Error::Invalid("signed admission role"));
    };
    let Some(Material::Entry(entry)) = raw.get(&body.entry).copied() else {
        return Err(Error::Invalid("signed admission entry role"));
    };
    let target = entry.target();
    if body.value.slot != core.slot || body.value.input != input {
        return Err(Error::Invalid("signed admission context"));
    }
    Ok(Message {
        slot: core.slot.id::<H>(),
        round: target.ballot,
        leader: target.leader,
        kind: Kind::Recovery {
            phase,
            subject: Subject {
                core: core.id::<H>(),
                input,
                entry: target.id::<H>(),
                proposal: admission,
                decision: body.value.id::<H>(),
            },
        },
    })
}

fn exact_bindings<H: Hasher<Digest = D>, S: scheme::Scheme<D>, D: Digest>(
    raw: &BTreeMap<D, &Material<S, D>>,
    core: &Core<D>,
    input: D,
    meter: &mut Meter,
) -> Result<(), Error<D>> {
    for material in raw.values().copied() {
        meter.work::<D>(1)?;
        let (admission, phase, message) = match material {
            Material::Proposal {
                admission,
                endorsement,
            } => {
                if endorsement.attestation.signer != endorsement.message.leader {
                    return Err(Error::Invalid("coordinator signer"));
                }
                (*admission, Phase::Propose, &endorsement.message)
            }
            Material::Rpc { proposal, quorum } => {
                let Some(Material::Proposal { admission, .. }) = raw.get(proposal).copied() else {
                    return Err(Error::Invalid("RPC signed proposal role"));
                };
                (*admission, Phase::Prepare, &quorum.message)
            }
            Material::Terminal { rpc, quorum } => {
                let Some(Material::Rpc { proposal, .. }) = raw.get(rpc).copied() else {
                    return Err(Error::Invalid("terminal RPC role"));
                };
                let Some(Material::Proposal { admission, .. }) = raw.get(proposal).copied() else {
                    return Err(Error::Invalid("terminal signed proposal role"));
                };
                (*admission, Phase::Commit, &quorum.message)
            }
            _ => continue,
        };
        if *message != admission_subject::<H, S, D>(admission, phase, raw, core, input)? {
            return Err(Error::Invalid("exact signed recovery subject"));
        }
    }
    Ok(())
}

fn replay_material<'n, 'a: 'n, S: scheme::Scheme<D>, D: Digest>(
    record: &issuance::Record<D>,
    raw: &'n BTreeMap<D, &'a Material<S, D>>,
    checked: &'n BTreeMap<D, Checked<'a, S, D>>,
) -> issuance::Material<'n, S, D> {
    use issuance::{Action, Material as M};
    if let Action::AdvanceWish { message, cause, .. } = record.action() {
        let Kind::Wish(w) = &message.kind else {
            return M::None;
        };
        let Some(Checked::Entry(predecessor)) = checked.get(&w.predecessor) else {
            return M::None;
        };
        return match cause {
            issuance::WishCause::Timeout => M::Entry(predecessor),
            issuance::WishCause::Amplification(id) => match checked.get(id) {
                Some(Checked::Amplification(amplification)) => M::Amplification {
                    predecessor,
                    amplification,
                },
                _ => M::None,
            },
        };
    }
    let authority = match record.action() {
        Action::Reserve { authority, .. } => *authority,
        Action::Enter { authority, .. } => Some(*authority),
        Action::RetainOrigin { origin, .. } => Some(*origin),
        Action::RetainRpc { proof, .. } | Action::RecoveryTerminal { proof, .. } => Some(*proof),
        _ => None,
    };
    if let Some(id) = authority {
        match (raw.get(&id).copied(), checked.get(&id)) {
            (Some(Material::Body(b)), Some(Checked::Body)) => return M::Body(b),
            (Some(Material::Body(b)), Some(Checked::RouteBody(cap))) => {
                return M::RouteBody(b, cap);
            }
            (Some(Material::Origin(o)), Some(Checked::Origin(_, Some(cap)))) => {
                return M::RouteOrigin(o, cap);
            }
            (Some(Material::Origin(o)), Some(Checked::Origin(_, None))) => return M::Origin(o),
            (_, Some(Checked::Entry(e))) => return M::Entry(e),
            (_, Some(Checked::Value(v))) => return M::Recovery(v),
            _ => {}
        }
    }
    if let Action::Terminal {
        origin,
        certificate,
        ..
    } = record.action()
        && let (Some(Material::Origin(o)), Some(Material::FastQuorum(q))) =
            (raw.get(origin).copied(), raw.get(certificate).copied())
    {
        return M::Terminal {
            origin: o,
            quorum: q,
        };
    }
    M::None
}

fn history_pages<S: scheme::Scheme<D>, D: Digest>(
    notice: &Signed<S, D>,
    raw: &BTreeMap<D, &Material<S, D>>,
    bounds: issuance::history::Bounds,
    meter: &mut Meter,
) -> Result<Vec<issuance::HistoryPage<D>>, Error<D>> {
    let Kind::Recover(r) = &notice.message.kind else {
        return Err(Error::Invalid("history notice role"));
    };
    if r.snapshot.count() > u64::from(bounds.pages) {
        return Err(Error::Limit);
    }
    let mut pages = Vec::new();
    pages
        .try_reserve_exact(usize::try_from(r.snapshot.count()).map_err(|_| Error::Limit)?)
        .map_err(|_| Error::Limit)?;
    let mut next = r.snapshot.head();
    while let Some(id) = next {
        meter.work::<D>(1)?;
        if pages.len() >= bounds.pages as usize {
            return Err(Error::Limit);
        }
        let Some(Material::Page(p)) = raw.get(&id).copied() else {
            return Err(Error::Missing(id));
        };
        next = p.previous();
        pages.push(p.clone());
    }
    pages.reverse();
    Ok(pages)
}

#[allow(clippy::too_many_arguments)]
fn admission<'a, H: Hasher<Digest = D>, S: scheme::Scheme<D>, D: Digest>(
    id: D,
    body: &ProposalBody<D>,
    root_bytes: u64,
    core: &Core<D>,
    input: D,
    limits: Limits,
    raw: &BTreeMap<D, &'a Material<S, D>>,
    checked: &BTreeMap<D, Checked<'a, S, D>>,
    meter: &mut Meter,
    validate_fresh: &mut impl FnMut(&VerifiedRecoveryRows<S, D>, &ProposalBody<D>) -> bool,
    scheme: &S,
    scope: ScopeId,
) -> Result<Verified<D>, Error<D>> {
    let Checked::Entry(entry) = node(checked, body.entry)? else {
        return Err(Error::Invalid("admission entry role"));
    };
    let target = entry.target();
    let c = super::Committee::new(scheme.participants().len())?;
    if body.value.slot != core.slot
        || body.value.input != input
        || body.histories.len() != c.quorum()
        || body.positive.windows(2).any(|w| w[0] >= w[1])
    {
        return Err(Error::Invalid("admission context/cardinality"));
    }
    let mut previous = None;
    let mut originals = Vec::with_capacity(c.quorum());
    for history in &body.histories {
        let Checked::History { entry: row, notice } = node(checked, *history)? else {
            return Err(Error::Invalid("admission history role"));
        };
        if row != target || previous.is_some_and(|owner| owner >= notice.attestation.signer) {
            return Err(Error::Invalid("frozen RECOVER population"));
        }
        previous = Some(notice.attestation.signer);
        originals.push((*notice).clone());
    }
    for positive in &body.positive {
        if !matches!(
            node(checked, *positive)?,
            Checked::Origin(..)
                | Checked::Value(Verified {
                    role: Role::Rpc | Role::Terminal,
                    ..
                })
                | Checked::FastTerminal(_)
        ) {
            return Err(Error::Invalid("positive evidence role"));
        }
    }
    let mut todo = body
        .histories
        .iter()
        .chain(&body.positive)
        .copied()
        .collect::<Vec<_>>();
    let mut seen = BTreeSet::new();
    let mut origins = BTreeMap::new();
    let mut rpcs = BTreeMap::<Round, (D, D, D)>::new();
    let mut terminals = BTreeMap::new();
    while let Some(evidence) = todo.pop() {
        meter.work::<D>(1)?;
        if !seen.insert(evidence) {
            continue;
        }
        let material = raw.get(&evidence).ok_or(Error::Missing(evidence))?;
        match node(checked, evidence)? {
            Checked::Origin(value, None) => {
                origins.insert(evidence, value.id::<H>());
            }
            Checked::Value(v) if v.role == Role::Rpc => {
                if let Some((old_proposal, old_decision, old_id)) = rpcs.get_mut(&v.round) {
                    if *old_proposal != v.proposal || *old_decision != v.decision {
                        return Err(Error::Invalid("conflicting same-ballot RPCs"));
                    }
                    *old_id = (*old_id).min(evidence);
                } else {
                    rpcs.insert(v.round, (v.proposal, v.decision, evidence));
                }
            }
            Checked::Value(v) if v.role == Role::Terminal => {
                terminals.insert(evidence, v.decision);
            }
            Checked::FastTerminal(value) => {
                terminals.insert(evidence, value.id::<H>());
            }
            Checked::Page => {
                // For the route profile, a SELECT by itself does not require carry.
                // A reserved FINAL is already a possible signature, even before release.
                if let Material::Page(p) = material
                    && let issuance::Action::Reserve {
                        message:
                            Message {
                                kind:
                                    Kind::Phase {
                                        phase: super::Phase::FastFinal,
                                        ..
                                    },
                                ..
                            },
                        authority: Some(origin),
                    } = p.record().action()
                    && let Checked::Origin(value, Some(_)) = node(checked, *origin)?
                {
                    origins.insert(*origin, value.id::<H>());
                }
                if let Material::Page(p) = material
                    && let issuance::Action::Terminal { origin, .. } = p.record().action()
                    && let Checked::Origin(value, _) = node(checked, *origin)?
                {
                    terminals.insert(evidence, value.id::<H>());
                }
            }
            _ => {}
        }
        meter.work::<D>(material.link_count() as u64)?;
        todo.extend(material.links());
    }
    if let Some((&terminal, &value)) = terminals.first_key_value() {
        if terminals.values().any(|other| *other != value) {
            return Err(Error::Invalid("conflicting complete terminals"));
        }
        return Err(Error::Catchup(terminal));
    }
    if let Some((&ballot, &(_, _, rpc))) = rpcs.last_key_value()
        && ballot >= target.ballot
    {
        return Err(Error::Stale(rpc));
    }
    let required = if let Some((_, (_, _, rpc))) = rpcs.last_key_value() {
        Some(*rpc)
    } else {
        if let Some((_, decision)) = origins.first_key_value()
            && origins.values().any(|other| other != decision)
        {
            return Err(Error::Invalid("conflicting gated original decisions"));
        }
        origins.first_key_value().map(|(id, _)| *id)
    };
    let origin = match (required, &body.choice) {
        (Some(required), Choice::Carry(actual)) if required == *actual => {
            match node(checked, required)? {
                Checked::Origin(value, _) if value.as_ref() == &body.value => required,
                Checked::Value(v) if v.role == Role::Rpc && v.value.as_ref() == &body.value => {
                    v.origin
                }
                _ => return Err(Error::Invalid("carried full Decision changed")),
            }
        }
        (Some(authority), Choice::Fresh { .. }) => return Err(Error::CarryRequired(authority)),
        (None, Choice::Fresh { .. }) => {
            let rows = VerifiedRecoveryRows {
                core: core.clone(),
                input,
                entry: entry.id(),
                attempt: target.attempt,
                round: target.ballot,
                leader: target.leader,
                originals,
                participants: scheme.participants().iter().cloned().collect(),
            };
            meter.work::<D>(1)?;
            if !validate_fresh(&rows, body) {
                return Err(super::Error::Policy.into());
            }
            id
        }
        _ => return Err(Error::Invalid("terminal/RPC/original/fresh priority")),
    };
    Ok(Verified {
        scope,
        role: Role::Admission,
        evidence: id,
        encoded_size: root_bytes,
        limits,
        slot: core.slot.id::<H>(),
        core: core.id::<H>(),
        input,
        entry: entry.id(),
        attempt: target.attempt,
        round: target.ballot,
        leader: target.leader,
        proposal: id,
        decision: body.value.id::<H>(),
        value: Arc::new(body.value.clone()),
        origin,
    })
}

/// Verifies the complete flat evidence graph, then returns one exact recovery
/// authority. Signatures and all graph bounds precede application Build calls.
/// Missing material, cycles, stale attempts and terminal catch-up never authorize
/// a fresh fallback. Native eligibility, journal sync and finality are separate.
#[allow(clippy::too_many_arguments)]
pub fn verify<'a, H, S, D, R>(
    rng: &mut R,
    context: &VerificationContext<S>,
    core: &'a Core<D>,
    input: D,
    root: D,
    resolve: impl FnMut(&D) -> Option<&'a Material<S, D>>,
    limits: Limits,
    bounds: Bounds,
    validate_first: impl FnMut(&First<D>) -> bool,
    validate_original_build: impl FnMut(&VerifiedRows<S, D>, &OriginBody<S, D>) -> bool,
    validate_fresh: impl FnMut(&VerifiedRecoveryRows<S, D>, &ProposalBody<D>) -> bool,
    strategy: &impl Strategy,
) -> Result<Verified<D>, Error<D>>
where
    H: Hasher<Digest = D>,
    S: scheme::Scheme<D>,
    D: Digest,
    R: CryptoRng,
{
    match verify_root::<H, S, D, R>(
        rng,
        context,
        core,
        input,
        root,
        resolve,
        limits,
        bounds,
        validate_first,
        validate_original_build,
        validate_fresh,
        strategy,
    )? {
        VerifiedRoot::Authority(value) => Ok(value),
        VerifiedRoot::History => Err(Error::Invalid("recovery authority root role")),
    }
}

/// Result of replaying a complete evidence closure. A verified history alone
/// cannot be used as signing authority.
pub enum VerifiedRoot<D: Digest> {
    History,
    Authority(Verified<D>),
}

/// Replay a peer history before counting it, or verify an authority root.
#[allow(clippy::too_many_arguments)]
pub fn verify_root<'a, H, S, D, R>(
    rng: &mut R,
    context: &VerificationContext<S>,
    core: &'a Core<D>,
    input: D,
    root: D,
    resolve: impl FnMut(&D) -> Option<&'a Material<S, D>>,
    limits: Limits,
    bounds: Bounds,
    validate_first: impl FnMut(&First<D>) -> bool,
    validate_original_build: impl FnMut(&VerifiedRows<S, D>, &OriginBody<S, D>) -> bool,
    validate_fresh: impl FnMut(&VerifiedRecoveryRows<S, D>, &ProposalBody<D>) -> bool,
    strategy: &impl Strategy,
) -> Result<VerifiedRoot<D>, Error<D>>
where
    H: Hasher<Digest = D>,
    S: scheme::Scheme<D>,
    D: Digest,
    R: CryptoRng,
{
    verify_root_with_routes::<H, S, D, R>(
        rng,
        context,
        core,
        input,
        root,
        resolve,
        limits,
        bounds,
        |_| None,
        validate_first,
        validate_original_build,
        validate_fresh,
        strategy,
    )
}

/// Verify a recovery closure with route-only SELECT witnesses. The local policy
/// supplies a scope only for an exact body whose paired native votes, Build and
/// stability condition it has already replayed. FINAL still needs its own origin.
#[allow(clippy::too_many_arguments)]
pub fn verify_root_with_routes<'a, H, S, D, R>(
    rng: &mut R,
    context: &VerificationContext<S>,
    core: &'a Core<D>,
    input: D,
    root: D,
    mut resolve: impl FnMut(&D) -> Option<&'a Material<S, D>>,
    limits: Limits,
    bounds: Bounds,
    route_scope: impl Fn(&OriginBody<S, D>) -> Option<D>,
    mut validate_first: impl FnMut(&First<D>) -> bool,
    mut validate_original_build: impl FnMut(&VerifiedRows<S, D>, &OriginBody<S, D>) -> bool,
    mut validate_fresh: impl FnMut(&VerifiedRecoveryRows<S, D>, &ProposalBody<D>) -> bool,
    strategy: &impl Strategy,
) -> Result<VerifiedRoot<D>, Error<D>>
where
    H: Hasher<Digest = D>,
    S: scheme::Scheme<D>,
    D: Digest,
    R: CryptoRng,
{
    let scheme = context.scheme();
    limits.validate::<S, D>(core)?;
    core.check::<H, S>(&super::VerificationSource::Scheme(scheme))?;
    let c = super::Committee::new(scheme.participants().len())?;
    let mut meter = Meter {
        bytes: 0,
        links: 0,
        work: 0,
        bounds,
    };
    let mut raw = BTreeMap::new();
    let mut active = BTreeSet::new();
    let mut done = BTreeSet::new();
    let mut order = Vec::new();
    let mut todo = vec![(root, false)];
    while let Some((id, finish)) = todo.pop() {
        meter.work::<D>(1)?;
        if done.contains(&id) {
            continue;
        }
        if finish {
            active.remove(&id);
            done.insert(id);
            order.push(id);
            continue;
        }
        if !active.insert(id) {
            return Err(Error::Cycle);
        }
        if raw.len() >= bounds.nodes as usize {
            return Err(Error::Limit);
        }
        let material = resolve(&id).ok_or(Error::Missing(id))?;
        material.preflight(c, limits)?;
        meter.node::<D>(material.encode_size(), material.link_count())?;
        if material.id::<H>() != id {
            return Err(Error::Hash);
        }
        preauthenticate::<H, S, D, R>(
            rng,
            scheme,
            core,
            input,
            material,
            limits,
            match material {
                Material::Body(b) => route_scope(b),
                Material::Origin(o) => route_scope(&o.body),
                _ => None,
            },
            strategy,
            &mut meter,
        )?;
        raw.insert(id, material);
        todo.push((id, true));
        for child in material.links().into_iter().rev() {
            if !done.contains(&child) {
                todo.push((child, false));
            }
        }
    }
    // A genuine signature for another body must not trigger application Build.
    // All raw nodes are bounded and authenticated before these exact joins.
    exact_bindings::<H, S, D>(&raw, core, input, &mut meter)?;
    let mut checked = BTreeMap::new();
    for id in order {
        meter.work::<D>(1)?;
        let material = raw[&id];
        let result = match material {
            Material::Entry(proof) => {
                meter.work::<D>(
                    u64::from(bounds.entry.signatures) + u64::from(bounds.entry.nodes),
                )?;
                let e = entry::verify::<H, S, D, R>(
                    rng,
                    context,
                    core,
                    input,
                    proof,
                    limits,
                    bounds.entry,
                    |id| match raw.get(id).copied() {
                        Some(Material::Entry(p)) => Some(p),
                        _ => None,
                    },
                    strategy,
                )
                .map_err(|_| Error::Invalid("complete entry provenance"))?;
                Checked::Entry(e)
            }
            Material::Amplification(proof) => {
                meter.work::<D>(
                    u64::from(bounds.entry.signatures) + u64::from(bounds.entry.nodes),
                )?;
                let a = entry::verify_amplification::<H, S, D, R>(
                    rng,
                    context,
                    core,
                    input,
                    proof,
                    limits,
                    bounds.entry,
                    |id| match raw.get(id).copied() {
                        Some(Material::Entry(p)) => Some(p),
                        _ => None,
                    },
                    strategy,
                )
                .map_err(|_| Error::Invalid("complete amplification provenance"))?;
                Checked::Amplification(a)
            }
            Material::Body(body) => {
                meter.work::<D>(2 * c.len() as u64)?;
                if let Some(scope) = route_scope(body) {
                    Checked::RouteBody(body.verify_route_selection::<H, R>(
                        rng,
                        scheme,
                        core,
                        input,
                        scope,
                        limits,
                        |_| true,
                        strategy,
                    )?)
                } else {
                    body.verify::<H, R>(
                        rng,
                        scheme,
                        core,
                        input,
                        limits,
                        &mut validate_first,
                        &mut validate_original_build,
                        strategy,
                    )?;
                    Checked::Body
                }
            }
            Material::Origin(origin) => {
                meter.work::<D>(2 * c.len() as u64)?;
                let route = if let Some(scope) = route_scope(&origin.body) {
                    let cap = origin.body.verify_route_selection::<H, R>(
                        rng,
                        scheme,
                        core,
                        input,
                        scope,
                        limits,
                        |_| true,
                        strategy,
                    )?;
                    origin.check_selection::<H, R>(
                        rng,
                        &super::VerificationSource::Scheme(scheme),
                        core,
                        limits,
                        strategy,
                    )?;
                    Some(cap)
                } else {
                    origin.verify::<H, R>(
                        rng,
                        scheme,
                        core,
                        input,
                        limits,
                        &mut validate_first,
                        &mut validate_original_build,
                        strategy,
                    )?;
                    None
                };
                Checked::Origin(Arc::new(origin.body.decision.clone()), route)
            }
            Material::Page(_) => Checked::Page,
            Material::History { entry, notice } => {
                let Checked::Entry(e) = node(&checked, *entry)? else {
                    return Err(Error::Invalid("history entry role"));
                };
                let target = e.target();
                let pages = history_pages(notice, &raw, bounds.history, &mut meter)?;
                meter.work::<D>(pages.len() as u64 * (c.len() as u64 + 1))?;
                issuance::history::verify::<H, S, D, R>(
                    rng,
                    context,
                    core,
                    input,
                    target.ballot,
                    target.leader,
                    e.id(),
                    notice,
                    &pages,
                    limits,
                    bounds.history,
                    |record| replay_material(record, &raw, &checked),
                    &mut validate_first,
                    &mut validate_original_build,
                    strategy,
                )
                .map_err(|_| Error::Invalid("complete authenticated history"))?;
                // Legacy floor snapshots remain useful data, but cannot become
                // recovery originals by attaching an external entry proof.
                // Replay independently checked the owner's exact Enter artifact,
                // which may be a different proof alias for this semantic target.
                if !pages.iter().any(|page| {
                    matches!(page.record().action(), issuance::Action::Enter { snapshot, entry, .. }
                        if snapshot.ballot() == target.ballot
                            && snapshot.leader() == target.leader
                            && *entry == e.id())
                }) {
                    return Err(Error::Invalid("RECOVER lacks authenticated Enter"));
                }
                for page in &pages {
                    if let issuance::Action::Reserve { message, .. } = page.record().action()
                        && message.round >= target.ballot
                        && matches!(message.kind, Kind::Recovery { .. } | Kind::Recover(_))
                    {
                        return Err(Error::Invalid("late RECOVER after same/higher phase"));
                    }
                    if let issuance::Action::RetainRpc { round, proof, .. } = page.record().action()
                        && *round >= target.ballot
                    {
                        return Err(Error::Stale(*proof));
                    }
                }
                Checked::History {
                    entry: target.clone(),
                    notice,
                }
            }
            Material::Admission(body) => Checked::Value(admission::<H, S, D>(
                id,
                body,
                material.encode_size() as u64,
                core,
                input,
                limits,
                &raw,
                &checked,
                &mut meter,
                &mut validate_fresh,
                scheme,
                context.scope(),
            )?),
            Material::Proposal {
                admission,
                endorsement,
            } => {
                let mut v = checked_value(&checked, *admission, Role::Admission)?.clone();
                if endorsement.message != v.message(Phase::Propose)
                    || endorsement.attestation.signer != v.leader
                {
                    return Err(Error::Invalid("exact coordinator endorsement"));
                }
                if let Some(Material::Admission(ProposalBody {
                    choice: Choice::Fresh { .. },
                    ..
                })) = raw.get(admission).copied()
                {
                    v.origin = id;
                }
                v.role = Role::Proposal;
                v.evidence = id;
                v.encoded_size = material.encode_size() as u64;
                Checked::Value(v)
            }
            Material::Rpc { proposal, quorum } => {
                let mut v = checked_value(&checked, *proposal, Role::Proposal)?.clone();
                if quorum.message != v.message(Phase::Prepare) {
                    return Err(Error::Invalid("RPC exact unsigned proposal subject"));
                }
                v.role = Role::Rpc;
                v.evidence = id;
                v.encoded_size = material.encode_size() as u64;
                Checked::Value(v)
            }
            Material::Terminal { rpc, quorum } => {
                let mut v = checked_value(&checked, *rpc, Role::Rpc)?.clone();
                if quorum.message != v.message(Phase::Commit) {
                    return Err(Error::Invalid("COMMIT exact unsigned proposal subject"));
                }
                v.role = Role::Terminal;
                v.evidence = id;
                v.encoded_size = material.encode_size() as u64;
                Checked::Value(v)
            }
            Material::FastQuorum(_) => Checked::FastQuorum,
            Material::FastTerminal { origin, quorum } => {
                let Checked::Origin(value, _) = node(&checked, *origin)? else {
                    return Err(Error::Invalid("original terminal origin role"));
                };
                original_terminal::<S, D, H>(core, value, quorum)?;
                Checked::FastTerminal(value.clone())
            }
        };
        checked.insert(id, result);
    }
    match checked.remove(&root).ok_or(Error::Missing(root))? {
        Checked::History { .. } => Ok(VerifiedRoot::History),
        Checked::Value(value) => Ok(VerifiedRoot::Authority(value)),
        _ => Err(Error::Invalid("recovery authority root role")),
    }
}

#[cfg(feature = "arbitrary")]
fn arbitrary_bytes(u: &mut arbitrary::Unstructured<'_>) -> arbitrary::Result<Bytes> {
    let len = u.int_in_range(0..=u.len().min(128))?;
    Ok(Bytes::copy_from_slice(u.bytes(len)?))
}

#[cfg(feature = "arbitrary")]
impl<'a, D: Digest + arbitrary::Arbitrary<'a>> arbitrary::Arbitrary<'a> for Choice<D> {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        Ok(if u.arbitrary()? {
            Self::Carry(u.arbitrary()?)
        } else {
            Self::Fresh {
                population: u.arbitrary()?,
                build: arbitrary_bytes(u)?,
                material: arbitrary_bytes(u)?,
            }
        })
    }
}

#[cfg(feature = "arbitrary")]
impl<D: Digest> arbitrary::Arbitrary<'_> for ProposalBody<D>
where
    D: for<'a> arbitrary::Arbitrary<'a>,
{
    fn arbitrary(u: &mut arbitrary::Unstructured<'_>) -> arbitrary::Result<Self> {
        let histories = u.int_in_range(0..=8usize)?;
        let positive = u.int_in_range(0..=8usize)?;
        Ok(Self {
            value: Decision {
                slot: super::Slot {
                    profile: u.arbitrary()?,
                    domain: u.arbitrary()?,
                    roster: u.arbitrary()?,
                    cut: u.arbitrary()?,
                    proposal: u.arbitrary()?,
                    parent: super::NativeParent::Genesis(u.arbitrary()?),
                },
                input: u.arbitrary()?,
                order: arbitrary_bytes(u)?,
            },
            entry: u.arbitrary()?,
            histories: (0..histories)
                .map(|_| u.arbitrary())
                .collect::<Result<_, _>>()?,
            positive: (0..positive)
                .map(|_| u.arbitrary())
                .collect::<Result<_, _>>()?,
            choice: u.arbitrary()?,
        })
    }
}

// Generate bounded raw new-role frames, not authenticated capabilities. Original
// envelopes and persisted pages also have deterministic signed corpus coverage.
#[cfg(feature = "arbitrary")]
impl<S: scheme::Scheme<D>, D: Digest> arbitrary::Arbitrary<'_> for Material<S, D>
where
    D: for<'a> arbitrary::Arbitrary<'a>,
    S::Signature: for<'a> arbitrary::Arbitrary<'a>,
    S::Certificate: for<'a> arbitrary::Arbitrary<'a>,
{
    fn arbitrary(u: &mut arbitrary::Unstructured<'_>) -> arbitrary::Result<Self> {
        let tag = u.int_in_range(0..=7u8)?;
        if tag == 0 {
            let proof: entry::Proof<S, D> = u.arbitrary()?;
            if proof.encode_size() > super::MAX_EVIDENCE_BYTES {
                return Err(arbitrary::Error::IncorrectFormat);
            }
            return Ok(Self::Entry(proof));
        }
        if tag == 1 {
            return Ok(Self::Admission(u.arbitrary()?));
        }
        let phase = if tag == 4 {
            Phase::Commit
        } else {
            Phase::Prepare
        };
        let message = Message {
            slot: u.arbitrary()?,
            round: u.arbitrary()?,
            leader: Participant::new(u.int_in_range(0..=63)?),
            kind: if tag == 5 || tag == 6 {
                Kind::Phase {
                    phase: super::Phase::FastFinal,
                    decision: u.arbitrary()?,
                }
            } else if tag == 7 {
                Kind::Recover(u.arbitrary()?)
            } else {
                Kind::Recovery {
                    phase: if tag == 2 { Phase::Propose } else { phase },
                    subject: u.arbitrary()?,
                }
            },
        };
        if tag == 2 || tag == 7 {
            let signed = Signed {
                message,
                attestation: u.arbitrary()?,
            };
            return Ok(if tag == 2 {
                Self::Proposal {
                    admission: u.arbitrary()?,
                    endorsement: signed,
                }
            } else {
                Self::History {
                    entry: u.arbitrary()?,
                    notice: signed,
                }
            });
        }
        let certificate: S::Certificate = u.arbitrary()?;
        if certificate.encode_size() > 4096 {
            return Err(arbitrary::Error::IncorrectFormat);
        }
        let quorum = Quorum {
            message,
            certificate,
        };
        Ok(match tag {
            3 => Self::Rpc {
                proposal: u.arbitrary()?,
                quorum,
            },
            4 => Self::Terminal {
                rpc: u.arbitrary()?,
                quorum,
            },
            5 => Self::FastQuorum(quorum),
            _ => Self::FastTerminal {
                origin: u.arbitrary()?,
                quorum,
            },
        })
    }
}
