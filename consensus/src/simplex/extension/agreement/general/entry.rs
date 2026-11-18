//! Bounded WISH provenance for the inactive general-committee G1 profile.
//!
//! Verification authenticates an entry relative to an already trusted original
//! Core and input. An initial native NQC proves exact P, not the native parent's
//! payload, local certification, an elapsed deadline, or a right to sign. The
//! voter still owns those checks, durable entry/floor installation and timers.
//! Higher entries contain q original WISH signatures. Amplification and once-
//! WISH issuance are separate owner transitions, not inferred by this verifier.

use super::{
    self as g, Committee, Core, Frame, Kind, Limits, ScopeId, Signed, VerificationContext,
    VerificationSource, read_blob, scheme,
};
use crate::{
    simplex::types::Notarization,
    types::{Participant, Round, View},
};
use bytes::{Buf as _, BufMut};
use commonware_codec::{
    Buf, Decode as _, Encode as _, EncodeSize, Error as CodecError, Read, ReadExt as _, Write,
};
use commonware_cryptography::{Digest, Hasher, certificate};
use commonware_parallel::Strategy;
use rand_core::CryptoRng;
use std::collections::{BTreeMap, VecDeque};

const SEMANTIC: &[u8] = b"_COMMONWARE_CONSENSUS_G1_ENTRY_TARGET_V1";
const ARTIFACT: &[u8] = b"_COMMONWARE_CONSENSUS_G1_ENTRY_ARTIFACT_V1";
const AMPLIFICATION: &[u8] = b"_COMMONWARE_CONSENSUS_G1_WISH_AMPLIFICATION_V1";

/// Semantic recovery entry, independent of a proof's signer subset or encoding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Target<D: Digest> {
    /// Exact original Core, which binds the complete Slot and native roster.
    pub core: D,
    /// Exact immutable full-cut public input.
    pub input: D,
    /// Recovery-only attempt, beginning at zero for this original Slot.
    pub attempt: u64,
    /// Original epoch and checked original view + 1 + attempt.
    pub ballot: Round,
    /// Ordered roster index attempt modulo n, not today's native leader.
    pub leader: Participant,
}
impl<D: Digest> Target<D> {
    /// Semantic identity; this is not an exact proof artifact or admission.
    pub fn id<H: Hasher<Digest = D>>(&self) -> D {
        H::hash(&[SEMANTIC, &self.encode()])
    }

    /// Exact next recovery target. This mapping grants no signing permission.
    pub fn successor(&self, c: Committee) -> Result<Self, Error> {
        let attempt = self.attempt.checked_add(1).ok_or(Error::Context)?;
        let view = self
            .ballot
            .view()
            .get()
            .checked_add(1)
            .ok_or(Error::Context)?;
        Ok(Self {
            core: self.core,
            input: self.input,
            attempt,
            ballot: Round::new(self.ballot.epoch(), View::new(view)),
            leader: Participant::new((attempt % c.len() as u64) as u32),
        })
    }

    fn check(&self, core: &Core<D>, core_id: D, input: D, c: Committee) -> Result<(), Error> {
        let view = core
            .slot
            .proposal
            .round
            .view()
            .get()
            .checked_add(1)
            .and_then(|v| v.checked_add(self.attempt))
            .ok_or(Error::Context)?;
        let n = u64::try_from(c.len()).map_err(|_| Error::Limit)?;
        let leader = u32::try_from(self.attempt % n).map_err(|_| Error::Limit)?;
        if self.core != core_id
            || self.input != input
            || self.ballot != Round::new(core.slot.proposal.round.epoch(), View::new(view))
            || self.leader != Participant::new(leader)
        {
            return Err(Error::Context);
        }
        Ok(())
    }
}
impl<D: Digest> Frame for Target<D> {
    const MAGIC: [u8; 4] = *b"G1T1";
    const MAX_BYTES: usize = g::MAX_FIRST_BYTES;
    type Cfg = ();
    fn body_size(&self) -> usize {
        2 * D::SIZE + 8 + g::native_size(&self.ballot) + 4
    }
    fn write_body(&self, w: &mut impl BufMut) {
        self.core.write(w);
        self.input.write(w);
        self.attempt.write(w);
        g::write_native(&self.ballot, w);
        g::write_owner(self.leader, w);
    }
    fn read_body(r: &mut impl Buf, _: &()) -> Result<Self, CodecError> {
        Ok(Self {
            core: D::read(r)?,
            input: D::read(r)?,
            attempt: u64::read(r)?,
            ballot: g::read_native(r)?,
            leader: g::read_owner(r)?,
        })
    }
}
frame_codec!(Target<D>, [D: Digest], ());

/// One owner's exact-target WISH, authenticated by an enclosing G1 Signed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Wish<D: Digest> {
    /// Exact semantic next entry requested by the signer.
    pub target: Target<D>,
    /// Exact retained predecessor entry artifact, not its semantic alias ID.
    pub predecessor: D,
}
impl<D: Digest> Frame for Wish<D> {
    const MAGIC: [u8; 4] = *b"G1W1";
    const MAX_BYTES: usize = g::MAX_FIRST_BYTES;
    type Cfg = ();
    fn body_size(&self) -> usize {
        self.target.encode_size() + D::SIZE
    }
    fn write_body(&self, w: &mut impl BufMut) {
        self.target.write(w);
        self.predecessor.write(w);
    }
    fn read_body(r: &mut impl Buf, _: &()) -> Result<Self, CodecError> {
        Ok(Self {
            target: Target::read(r)?,
            predecessor: D::read(r)?,
        })
    }
}
frame_codec!(Wish<D>, [D: Digest], ());

/// Exactly f+1 original WISHes for amplification, never a q-WISH entry.
/// Referenced predecessor entry artifacts remain separate bounded frames.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Amplification<S: certificate::Scheme, D: Digest> {
    /// One exact semantic successor shared by every signed original.
    pub target: Target<D>,
    /// Strictly ascending distinct roster owners, including outside-Core owners.
    pub wishes: Vec<Signed<S, D>>,
}
impl<S: certificate::Scheme, D: Digest> Amplification<S, D> {
    /// Exact retained witness identity. Apply preflight before hashing raw data.
    pub fn artifact_id<H: Hasher<Digest = D>>(&self) -> D {
        H::hash(&[AMPLIFICATION, &self.encode()])
    }
    /// Exact predecessor roots, preserving repeated references for accounting.
    pub fn dependencies(&self) -> impl Iterator<Item = D> + '_ {
        self.wishes.iter().filter_map(|s| match &s.message.kind {
            Kind::Wish(w) => Some(w.predecessor),
            _ => None,
        })
    }
    /// Callback-free field/cardinality/encoding limits, not authentication.
    pub fn preflight(&self, c: Committee, limits: Limits) -> Result<usize, Error> {
        limits.check()?;
        if self.target.attempt == 0 || self.wishes.len() != c.faults() + 1 {
            return Err(Error::Quorum);
        }
        if D::SIZE != 32 || usize::from(self.target.leader) >= c.len() {
            return Err(Error::Context);
        }
        for s in &self.wishes {
            s.message.check(c, limits)?;
            if usize::from(s.attestation.signer) >= c.len() {
                return Err(Error::Identity);
            }
            if s.encode_size() > g::MAX_FIRST_BYTES {
                return Err(Error::Limit);
            }
            if !matches!(&s.message.kind, Kind::Wish(w) if w.target == self.target) {
                return Err(Error::Context);
            }
        }
        if self
            .wishes
            .windows(2)
            .any(|w| w[0].attestation.signer >= w[1].attestation.signer)
        {
            return Err(Error::Identity);
        }
        let size = self.encode_size();
        if size > g::MAX_EVIDENCE_BYTES {
            return Err(Error::Limit);
        }
        Ok(size)
    }
}
impl<S: certificate::Scheme, D: Digest> Frame for Amplification<S, D> {
    const MAGIC: [u8; 4] = *b"G1Y1";
    type Cfg = Limits;
    fn body_size(&self) -> usize {
        self.target.encode_size()
            + 4
            + self
                .wishes
                .iter()
                .map(EncodeSize::encode_size)
                .sum::<usize>()
    }
    fn write_body(&self, w: &mut impl BufMut) {
        self.target.write(w);
        u32::try_from(self.wishes.len())
            .expect("G1 amplification exceeds u32")
            .write(w);
        for s in &self.wishes {
            s.write(w);
        }
    }
    fn read_body(r: &mut impl Buf, limits: &Limits) -> Result<Self, CodecError> {
        limits
            .check()
            .map_err(|_| CodecError::Invalid("G1 amplification", "limits"))?;
        let target = Target::read(r)?;
        let count = u32::read(r)? as usize;
        if !(1..=22).contains(&count) {
            return Err(CodecError::InvalidLength(count));
        }
        let mut wishes = Vec::with_capacity(count);
        for _ in 0..count {
            wishes.push(Signed::read_cfg(r, limits)?);
        }
        Ok(Self { target, wishes })
    }
}
frame_codec!(Amplification<S, D>, [S: certificate::Scheme, D: Digest], Limits);

/// Locally checked f+1 amplification. It grants neither entry nor native finality.
#[derive(Debug)]
pub struct VerifiedAmplification<'a, S: certificate::Scheme, D: Digest> {
    scope: ScopeId,
    core: &'a Core<D>,
    proof: &'a Amplification<S, D>,
    artifact: D,
    encoded_size: usize,
    verified_bytes: u64,
    limits: Limits,
}
impl<'a, S: certificate::Scheme, D: Digest> VerifiedAmplification<'a, S, D> {
    pub(super) fn matches_context(&self, context: &VerificationContext<S>) -> bool {
        context.matches_scope(&self.scope)
    }
    /// Exact original context.
    pub const fn core(&self) -> &'a Core<D> {
        self.core
    }
    /// Exact next target requested by the f+1 originals.
    pub const fn target(&self) -> &Target<D> {
        &self.proof.target
    }
    /// Exact immutable raw witness, retained with its predecessor closure.
    pub const fn proof(&self) -> &'a Amplification<S, D> {
        self.proof
    }
    /// Exact root artifact, independent of its semantic target.
    pub const fn artifact_id(&self) -> D {
        self.artifact
    }
    /// Root bytes for per-occurrence history accounting.
    pub const fn encoded_size(&self) -> usize {
        self.encoded_size
    }
    /// Complete distinct predecessor closure, including the amplification root.
    pub const fn verified_bytes(&self) -> u64 {
        self.verified_bytes
    }
    /// Exact field limits under which the witness was verified.
    pub const fn limits(&self) -> Limits {
        self.limits
    }
}

/// Checks f+1 exact-target WISHes and the complete predecessor entry DAG.
/// Remote local-clock/WAL claims are not required or inferred. All fields and
/// links are bounded before authentication, and no signer is exposed.
#[allow(clippy::too_many_arguments)]
pub fn verify_amplification<'a, H, S, D, R>(
    rng: &mut R,
    context: &VerificationContext<S>,
    core: &'a Core<D>,
    input: D,
    proof: &'a Amplification<S, D>,
    limits: Limits,
    bounds: Bounds,
    mut resolve: impl FnMut(&D) -> Option<&'a Proof<S, D>>,
    strategy: &impl Strategy,
) -> Result<VerifiedAmplification<'a, S, D>, Error>
where
    H: Hasher<Digest = D>,
    S: scheme::Scheme<D>,
    D: Digest,
    R: CryptoRng,
{
    let scheme = context.scheme();
    if core.followers.len() > 63 || bounds.nodes == 0 || bounds.encoded_bytes == 0 {
        return Err(Error::Limit);
    }
    let c = Committee::new(scheme.participants().len())?;
    let size = proof.preflight(c, limits)?;
    if proof.target.attempt > bounds.depth {
        return Err(Error::Limit);
    }
    let mut budget = Budget {
        nodes: 0,
        bytes: 0,
        signatures: 0,
        bounds,
    };
    budget.charge(size, proof.wishes.len())?;
    core.check::<H, S>(&VerificationSource::Scheme(scheme))?;
    limits.validate::<S, D>(core)?;
    let core_id = core.id::<H>();
    let slot = core.slot.id::<H>();
    proof.target.check(core, core_id, input, c)?;
    let mut material = BTreeMap::new();
    let mut queue = VecDeque::from([(&proof.target, proof.wishes.as_slice())]);
    while let Some((target, wishes)) = queue.pop_front() {
        let previous_attempt = target.attempt.checked_sub(1).ok_or(Error::Context)?;
        for signed in wishes {
            let Kind::Wish(wish) = &signed.message.kind else {
                return Err(Error::Context);
            };
            if signed.message.slot != slot
                || signed.message.round != target.ballot
                || signed.message.leader != target.leader
                || wish.target != *target
            {
                return Err(Error::Context);
            }
            if let Some(previous) = material.get(&wish.predecessor) {
                let previous: &&Proof<S, D> = previous;
                if previous.target().attempt != previous_attempt {
                    return Err(Error::Context);
                }
                continue;
            }
            if budget.nodes >= bounds.nodes {
                return Err(Error::Limit);
            }
            let previous = resolve(&wish.predecessor).ok_or(Error::Missing)?;
            let bytes = previous.preflight(c, limits)?;
            previous.target().check(core, core_id, input, c)?;
            if previous.target().attempt != previous_attempt {
                return Err(Error::Context);
            }
            let work = match previous {
                Proof::Initial { .. } => c.len(),
                Proof::Higher { wishes, .. } => wishes.len(),
            };
            budget.charge(bytes, work)?;
            if previous.artifact_id::<H>() != wish.predecessor {
                return Err(Error::Context);
            }
            match previous {
                Proof::Initial { notarization, .. } => {
                    if notarization.proposal != core.slot.proposal {
                        return Err(Error::Context);
                    }
                }
                Proof::Higher { target, wishes } => queue.push_back((target, wishes.as_slice())),
            }
            material.insert(wish.predecessor, previous);
        }
    }
    for signed in &proof.wishes {
        if !signed.verify(rng, scheme, limits, strategy) {
            return Err(Error::Signature);
        }
    }
    for previous in material.values() {
        match previous {
            Proof::Initial { notarization, .. } => {
                if !notarization.verify(rng, scheme, strategy) {
                    return Err(Error::Signature);
                }
            }
            Proof::Higher { wishes, .. } => {
                for signed in wishes {
                    if !signed.verify(rng, scheme, limits, strategy) {
                        return Err(Error::Signature);
                    }
                }
            }
        }
    }
    Ok(VerifiedAmplification {
        scope: context.scope(),
        core,
        proof,
        artifact: proof.artifact_id::<H>(),
        encoded_size: size,
        verified_bytes: budget.bytes,
        limits,
    })
}

/// Flat entry artifact. Referenced predecessors are separate bounded frames.
/// Decoding this object does not authenticate provenance or native admission.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Proof<S: certificate::Scheme, D: Digest> {
    /// Attempt zero, anchored to one genuine exact original native NQC.
    Initial {
        /// Exact semantic original recovery entry.
        target: Target<D>,
        /// Native notarization, with its original signing subject intact.
        notarization: Notarization<S, D>,
    },
    /// A later entry, supported by q distinct individually signed WISHes.
    Higher {
        /// One exact target shared by all originals in this artifact.
        target: Target<D>,
        /// Strict signer order; no owner is counted more than once.
        wishes: Vec<Signed<S, D>>,
    },
}
impl<S: certificate::Scheme, D: Digest> Proof<S, D> {
    /// Semantic coordinates claimed by this unverified artifact.
    pub const fn target(&self) -> &Target<D> {
        match self {
            Self::Initial { target, .. } | Self::Higher { target, .. } => target,
        }
    }

    /// Exact frame identity, distinct from Target::id. This grants no authority.
    /// Apply preflight before hashing externally supplied in-memory material.
    pub fn artifact_id<H: Hasher<Digest = D>>(&self) -> D {
        H::hash(&[ARTIFACT, &self.encode()])
    }

    /// Exact predecessor roots, including repeated references. Run preflight
    /// before graph admission; a non-WISH child is malformed, not a dependency.
    pub fn dependencies(&self) -> impl Iterator<Item = D> + '_ {
        let wishes = match self {
            Self::Initial { .. } => &[][..],
            Self::Higher { wishes, .. } => wishes.as_slice(),
        };
        wishes
            .iter()
            .filter_map(|signed| match &signed.message.kind {
                Kind::Wish(wish) => Some(wish.predecessor),
                _ => None,
            })
    }

    /// Checks cardinalities and every frame bound without hashing or crypto.
    /// Context, signatures, predecessor links and native admission remain unchecked.
    pub fn preflight(&self, c: Committee, limits: Limits) -> Result<usize, Error> {
        limits.check()?;
        if D::SIZE != 32 || usize::from(self.target().leader) >= c.len() {
            return Err(Error::Context);
        }
        match self {
            Self::Initial {
                target,
                notarization,
            } => {
                if target.attempt != 0 {
                    return Err(Error::Context);
                }
                if notarization.encode_size() > g::NATIVE_BYTES {
                    return Err(Error::Limit);
                }
            }
            Self::Higher { target, wishes } => {
                if target.attempt == 0 || wishes.len() != c.quorum() {
                    return Err(Error::Quorum);
                }
                for signed in wishes {
                    signed.message.check(c, limits)?;
                    if signed.encode_size() > g::MAX_FIRST_BYTES {
                        return Err(Error::Limit);
                    }
                    if usize::from(signed.attestation.signer) >= c.len() {
                        return Err(Error::Identity);
                    }
                    let Kind::Wish(wish) = &signed.message.kind else {
                        return Err(Error::Context);
                    };
                    if wish.target != *target {
                        return Err(Error::Context);
                    }
                }
                if wishes
                    .windows(2)
                    .any(|w| w[0].attestation.signer >= w[1].attestation.signer)
                {
                    return Err(Error::Identity);
                }
            }
        }
        let size = self.encode_size();
        if size > g::MAX_EVIDENCE_BYTES {
            return Err(Error::Limit);
        }
        Ok(size)
    }
}
impl<S: certificate::Scheme, D: Digest> Frame for Proof<S, D> {
    const MAGIC: [u8; 4] = *b"G1U1";
    type Cfg = (Limits, <S::Certificate as Read>::Cfg);
    fn body_size(&self) -> usize {
        self.target().encode_size()
            + 1
            + match self {
                Self::Initial { notarization, .. } => g::native_size(notarization),
                Self::Higher { wishes, .. } => {
                    4 + wishes.iter().map(EncodeSize::encode_size).sum::<usize>()
                }
            }
    }
    fn write_body(&self, w: &mut impl BufMut) {
        self.target().write(w);
        match self {
            Self::Initial { notarization, .. } => {
                0u8.write(w);
                g::write_native(notarization, w);
            }
            Self::Higher { wishes, .. } => {
                1u8.write(w);
                u32::try_from(wishes.len())
                    .expect("G1 entry exceeds u32")
                    .write(w);
                for signed in wishes {
                    signed.write(w);
                }
            }
        }
    }
    fn read_body(r: &mut impl Buf, cfg: &Self::Cfg) -> Result<Self, CodecError> {
        cfg.0
            .check()
            .map_err(|_| CodecError::Invalid("G1 entry", "limits"))?;
        let target = Target::read(r)?;
        match u8::read(r)? {
            0 => {
                let bytes = g::read_blob(r, g::NATIVE_BYTES)?;
                Ok(Self::Initial {
                    target,
                    notarization: Notarization::<S, D>::decode_cfg(bytes, &cfg.1)?,
                })
            }
            1 => {
                let count = u32::read(r)? as usize;
                if !(1..=64).contains(&count) {
                    return Err(CodecError::InvalidLength(count));
                }
                let mut wishes = Vec::with_capacity(count);
                for _ in 0..count {
                    wishes.push(Signed::read_cfg(r, &cfg.0)?);
                }
                Ok(Self::Higher { target, wishes })
            }
            _ => Err(CodecError::Invalid("G1 entry", "kind")),
        }
    }
}
frame_codec!(Proof<S, D>, [S: certificate::Scheme, D: Digest], (Limits, <S::Certificate as Read>::Cfg));

/// Finite limits for the complete flat predecessor DAG, including its root.
/// Exact artifacts are verified once. Limits never authorize truncating a chain.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Bounds {
    /// Maximum distinct resolved proof artifacts, charged before retaining them.
    pub nodes: u32,
    /// Maximum sum of complete distinct proof-frame bytes.
    pub encoded_bytes: u64,
    /// Maximum original signature work: one per WISH and n per native NQC.
    pub signatures: u32,
    /// Maximum predecessor transitions (the root's attempt number).
    pub depth: u64,
}

/// Rejected entry evidence. Missing or bounded-out evidence is never absence.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Error {
    /// The expected original context, mapping, or exact artifact differs.
    #[error("entry context mismatch")]
    Context,
    /// A roster owner is invalid, duplicated, or out of canonical order.
    #[error("entry identity mismatch")]
    Identity,
    /// The proof lacks exactly q original exact-target WISHes.
    #[error("entry quorum mismatch")]
    Quorum,
    /// Required exact predecessor material is unavailable.
    #[error("entry material missing")]
    Missing,
    /// A field, complete frame, or global verification budget is exceeded.
    #[error("entry resource limit")]
    Limit,
    /// A native NQC or original WISH signature failed authentication.
    #[error("entry signature invalid")]
    Signature,
    /// Captured G1 roster or structural verification failed.
    #[error(transparent)]
    Verification(#[from] g::Error),
}

/// Authenticated provenance relative to one trusted Core/Input and profile.
/// This capability grants no deadline, native P admission or signing permission.
/// Its exact proof and complete closure must be retained before journaling entry.
#[derive(Debug)]
pub struct VerifiedEntry<'a, S: certificate::Scheme, D: Digest> {
    scope: ScopeId,
    core: &'a Core<D>,
    proof: &'a Proof<S, D>,
    id: D,
    artifact: D,
    encoded_size: usize,
    verified_bytes: u64,
    limits: Limits,
    bounds: Bounds,
}
impl<'a, S: certificate::Scheme, D: Digest> VerifiedEntry<'a, S, D> {
    pub(super) fn matches_context(&self, context: &VerificationContext<S>) -> bool {
        context.matches_scope(&self.scope)
    }
    /// Exact trusted original Core and Slot.
    pub const fn core(&self) -> &'a Core<D> {
        self.core
    }
    /// Checked semantic target.
    pub const fn target(&self) -> &Target<D> {
        self.proof.target()
    }
    /// Stable semantic EntryID, independent of authentic proof aliases.
    pub const fn id(&self) -> D {
        self.id
    }
    /// Exact retained root artifact identity.
    pub const fn artifact_id(&self) -> D {
        self.artifact
    }
    /// Original immutable raw root proof; no authority is rewritten.
    pub const fn proof(&self) -> &'a Proof<S, D> {
        self.proof
    }
    /// Root-frame bytes only, for per-occurrence parent accounting.
    pub const fn encoded_size(&self) -> usize {
        self.encoded_size
    }
    /// Complete distinct predecessor-DAG bytes charged by this verification.
    pub const fn verified_bytes(&self) -> u64 {
        self.verified_bytes
    }
    /// Exact field limits used with the captured profile.
    pub const fn limits(&self) -> Limits {
        self.limits
    }
    /// Exact global verification budget supplied by the caller.
    pub const fn bounds(&self) -> Bounds {
        self.bounds
    }
}

struct Budget {
    nodes: u32,
    bytes: u64,
    signatures: u32,
    bounds: Bounds,
}
impl Budget {
    fn charge(&mut self, bytes: usize, signatures: usize) -> Result<(), Error> {
        let nodes = self
            .nodes
            .checked_add(1)
            .filter(|n| *n <= self.bounds.nodes)
            .ok_or(Error::Limit)?;
        let bytes = self
            .bytes
            .checked_add(u64::try_from(bytes).map_err(|_| Error::Limit)?)
            .filter(|n| *n <= self.bounds.encoded_bytes)
            .ok_or(Error::Limit)?;
        let signatures = self
            .signatures
            .checked_add(u32::try_from(signatures).map_err(|_| Error::Limit)?)
            .filter(|n| *n <= self.bounds.signatures)
            .ok_or(Error::Limit)?;
        self.nodes = nodes;
        self.bytes = bytes;
        self.signatures = signatures;
        Ok(())
    }
}

/// Authenticates a complete flat entry DAG with one captured verification context.
///
/// All nodes are bounded and exact-root/context checked before signature work.
/// Each WISH must target the enclosing entry and reference an authentic exact
/// predecessor with attempt one lower. Distinct aliases of that predecessor are
/// legal; duplicate owner signatures cannot split or increase one target quorum.
/// Native parent/election/elapsed-time admission and local WISH release remain
/// the voter's responsibility. A high integer or this token alone grants neither.
#[allow(clippy::too_many_arguments)]
pub fn verify<'a, H, S, D, R>(
    rng: &mut R,
    context: &VerificationContext<S>,
    core: &'a Core<D>,
    input: D,
    proof: &'a Proof<S, D>,
    limits: Limits,
    bounds: Bounds,
    mut resolve: impl FnMut(&D) -> Option<&'a Proof<S, D>>,
    strategy: &impl Strategy,
) -> Result<VerifiedEntry<'a, S, D>, Error>
where
    H: Hasher<Digest = D>,
    S: scheme::Scheme<D>,
    D: Digest,
    R: CryptoRng,
{
    let scheme = context.scheme();
    limits.check()?;
    if core.followers.len() > 63 || bounds.nodes == 0 || bounds.encoded_bytes == 0 {
        return Err(Error::Limit);
    }
    let c = Committee::new(scheme.participants().len())?;
    let size = proof.preflight(c, limits)?;
    if proof.target().attempt > bounds.depth {
        return Err(Error::Limit);
    }
    // Preflight raw root material before Core/Slot or artifact hashing.
    let mut budget = Budget {
        nodes: 0,
        bytes: 0,
        signatures: 0,
        bounds,
    };
    let work = match proof {
        Proof::Initial { .. } => c.len(),
        Proof::Higher { wishes, .. } => wishes.len(),
    };
    budget.charge(size, work)?;
    core.check::<H, S>(&VerificationSource::Scheme(scheme))?;
    limits.validate::<S, D>(core)?;
    let core_id = core.id::<H>();
    let slot = core.slot.id::<H>();
    proof.target().check(core, core_id, input, c)?;
    let artifact = proof.artifact_id::<H>();
    let mut material = BTreeMap::from([(artifact, proof)]);
    let mut queue = VecDeque::from([proof]);
    while let Some(current) = queue.pop_front() {
        match current {
            Proof::Initial { notarization, .. } => {
                if notarization.proposal != core.slot.proposal {
                    return Err(Error::Context);
                }
            }
            Proof::Higher { target, wishes } => {
                let previous_attempt = target.attempt.checked_sub(1).ok_or(Error::Context)?;
                for signed in wishes {
                    let Kind::Wish(wish) = &signed.message.kind else {
                        return Err(Error::Context);
                    };
                    if signed.message.slot != slot
                        || signed.message.round != target.ballot
                        || signed.message.leader != target.leader
                        || wish.target != *target
                    {
                        return Err(Error::Context);
                    }
                    if let Some(previous) = material.get(&wish.predecessor) {
                        if previous.target().attempt != previous_attempt {
                            return Err(Error::Context);
                        }
                        continue;
                    }
                    // Do not invoke a resolver when no further node can fit.
                    if budget.nodes >= bounds.nodes {
                        return Err(Error::Limit);
                    }
                    let previous = resolve(&wish.predecessor).ok_or(Error::Missing)?;
                    let bytes = previous.preflight(c, limits)?;
                    previous.target().check(core, core_id, input, c)?;
                    if previous.target().attempt != previous_attempt {
                        return Err(Error::Context);
                    }
                    let work = match previous {
                        Proof::Initial { .. } => c.len(),
                        Proof::Higher { wishes, .. } => wishes.len(),
                    };
                    budget.charge(bytes, work)?;
                    if previous.artifact_id::<H>() != wish.predecessor {
                        return Err(Error::Context);
                    }
                    material.insert(wish.predecessor, previous);
                    queue.push_back(previous);
                }
            }
        }
    }
    for current in material.values() {
        match current {
            Proof::Initial { notarization, .. } => {
                if !notarization.verify(rng, scheme, strategy) {
                    return Err(Error::Signature);
                }
            }
            Proof::Higher { wishes, .. } => {
                for signed in wishes {
                    if !signed.verify(rng, scheme, limits, strategy) {
                        return Err(Error::Signature);
                    }
                }
            }
        }
    }
    Ok(VerifiedEntry {
        scope: context.scope(),
        core,
        proof,
        id: proof.target().id::<H>(),
        artifact,
        encoded_size: size,
        verified_bytes: budget.bytes,
        limits,
        bounds,
    })
}

#[cfg(feature = "arbitrary")]
impl<'a, D: Digest + arbitrary::Arbitrary<'a>> arbitrary::Arbitrary<'a> for Target<D> {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        Ok(Self {
            core: u.arbitrary()?,
            input: u.arbitrary()?,
            attempt: u.arbitrary()?,
            ballot: u.arbitrary()?,
            leader: Participant::new(u.int_in_range(0..=63)?),
        })
    }
}
#[cfg(feature = "arbitrary")]
impl<'a, D: Digest + arbitrary::Arbitrary<'a>> arbitrary::Arbitrary<'a> for Wish<D> {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        Ok(Self {
            target: u.arbitrary()?,
            predecessor: u.arbitrary()?,
        })
    }
}
#[cfg(feature = "arbitrary")]
impl<'a, S: certificate::Scheme, D: Digest> arbitrary::Arbitrary<'a> for Proof<S, D>
where
    D: for<'b> arbitrary::Arbitrary<'b>,
    S::Certificate: for<'b> arbitrary::Arbitrary<'b>,
    S::Signature: for<'b> arbitrary::Arbitrary<'b>,
{
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let target: Target<D> = u.arbitrary()?;
        if u.arbitrary()? {
            return Ok(Self::Initial {
                target,
                notarization: u.arbitrary()?,
            });
        }
        let count = u.int_in_range(1..=8usize)?;
        let mut wishes = Vec::with_capacity(count);
        for _ in 0..count {
            wishes.push(Signed {
                message: g::Message {
                    slot: u.arbitrary()?,
                    round: target.ballot,
                    leader: target.leader,
                    kind: Kind::Wish(Wish {
                        target: target.clone(),
                        predecessor: u.arbitrary()?,
                    }),
                },
                attestation: u.arbitrary()?,
            });
        }
        Ok(Self::Higher { target, wishes })
    }
}

#[cfg(feature = "arbitrary")]
impl<S: certificate::Scheme, D: Digest> arbitrary::Arbitrary<'_> for Amplification<S, D>
where
    D: for<'a> arbitrary::Arbitrary<'a>,
    S::Signature: for<'a> arbitrary::Arbitrary<'a>,
{
    fn arbitrary(u: &mut arbitrary::Unstructured<'_>) -> arbitrary::Result<Self> {
        let target: Target<D> = u.arbitrary()?;
        let count = u.int_in_range(0..=22usize)?;
        let mut wishes = Vec::with_capacity(count);
        for _ in 0..count {
            wishes.push(Signed {
                message: g::Message {
                    slot: u.arbitrary()?,
                    round: target.ballot,
                    leader: target.leader,
                    kind: Kind::Wish(Wish {
                        target: target.clone(),
                        predecessor: u.arbitrary()?,
                    }),
                },
                attestation: u.arbitrary()?,
            });
        }
        Ok(Self { target, wishes })
    }
}
