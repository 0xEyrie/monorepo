//! Cryptographic foundations for the versioned general-committee G1 candidate.
//!
//! This module does not activate a voter Mode. The local issuance component
//! stages records for the native journal; its caller retains
//! native P admission, custody, journal synchronization, and signer ownership.
//! Application callbacks validate exact-P report/order meaning and replay Build.
//!
//! Every public frame is a four-byte type/version magic, a big-endian u32 body
//! length, and that exact body. Integer and vector lengths are fixed-width
//! big-endian. Native objects use their registered codec inside a u32 byte field.
//! The 4..=64 committee ceiling, 64 KiB FIRST ceiling, and 4 MiB evidence ceiling are resource limits,
//! not limits of the fast-consistency argument.

use super::VerificationSource;
use crate::{
    simplex::{
        scheme,
        types::{Proposal, Subject},
    },
    types::{Participant, Round, View},
};
use bytes::{Buf as _, BufMut, Bytes};
use commonware_codec::{
    Buf, DecodeExt as _, Encode as _, EncodeSize, Error as CodecError, FixedSize, Read,
    ReadExt as _, Write,
};
use commonware_cryptography::{
    Digest, Hasher,
    certificate::{self, Attestation, Scoped},
};
use commonware_parallel::Strategy;
use commonware_utils::iter::NonEmpty;
use rand_core::CryptoRng;
use std::{collections::BTreeSet, sync::Arc};

/// Maximum encoded size of one native G1 signed message, including headers.
pub const MAX_FIRST_BYTES: usize = 64 * 1024;
/// Maximum complete origin/evidence size, separate from one native vote envelope.
pub const MAX_EVIDENCE_BYTES: usize = 4 * 1024 * 1024;
const NATIVE_BYTES: usize = 16 * 1024;
const SIGNING: &[u8] = b"_COMMONWARE_CONSENSUS_G1_SIGNED_V1";
const RECOVER_SIGNING: &[u8] = b"_COMMONWARE_CONSENSUS_G1_RECOVER_SIGNED_V1";
const RECOVERY_SIGNING: &[u8] = b"_COMMONWARE_CONSENSUS_G1_RECOVERY_SIGNED_V1";
const WISH_SIGNING: &[u8] = b"_COMMONWARE_CONSENSUS_G1_WISH_SIGNED_V1";
const ROSTER: &[u8] = b"_COMMONWARE_CONSENSUS_G1_ROSTER_V1";
const SLOT: &[u8] = b"_COMMONWARE_CONSENSUS_G1_SLOT_V1";
const CORE: &[u8] = b"_COMMONWARE_CONSENSUS_G1_CORE_V1";
const DECISION: &[u8] = b"_COMMONWARE_CONSENSUS_G1_DECISION_V1";
const BODY: &[u8] = b"_COMMONWARE_CONSENSUS_G1_ORIGIN_BODY_V1";
const ORIGIN: &[u8] = b"_COMMONWARE_CONSENSUS_G1_ORIGIN_ENVELOPE_V1";

/// A failed structural, cryptographic, or application-policy check.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Error {
    /// Unsupported committee or non-attributable scheme.
    #[error("unsupported roster")]
    Roster,
    /// A captured Slot, Core, input, or carrier differs from trusted context.
    #[error("context mismatch")]
    Context,
    /// Duplicate, unordered, missing, or unauthorized owner.
    #[error("invalid owner set")]
    Identity,
    /// Invalid signature or certificate.
    #[error("invalid signature")]
    Signature,
    /// Invalid phase or round.
    #[error("invalid phase")]
    Phase,
    /// A field or complete frame exceeds the resource ceiling.
    #[error("resource limit")]
    Limit,
    /// Application semantics or deterministic Build validation failed.
    #[error("application policy rejected")]
    Policy,
    /// Legal Build output lacks enough matching original follower preferences.
    #[error("fast-ineligible decision")]
    FastIneligible,
    /// Too few distinct attributable phase votes.
    #[error("insufficient quorum")]
    Quorum,
}

/// Read-only verification authority for one locally configured scheme.
///
/// Clones share the same local authority. A separately constructed context is
/// distinct, even when its public roster is identical. Verified capabilities
/// must be re-created with the receiving issuance state's context before use.
/// This local identity is never encoded or signed.
pub struct VerificationContext<S> {
    scheme: Arc<S>,
    scope: ScopeId,
}

impl<S> Clone for VerificationContext<S> {
    fn clone(&self) -> Self {
        Self {
            scheme: self.scheme.clone(),
            scope: self.scope.clone(),
        }
    }
}

impl<S> VerificationContext<S> {
    /// Captures a scheme for standalone verification without exposing signing.
    pub fn new(scheme: S) -> Self {
        Self {
            scheme: Arc::new(scheme),
            scope: ScopeId(Arc::new(())),
        }
    }

    fn scheme(&self) -> &S {
        &self.scheme
    }

    fn scope(&self) -> ScopeId {
        self.scope.clone()
    }

    fn matches_scope(&self, scope: &ScopeId) -> bool {
        Arc::ptr_eq(&self.scope.0, &scope.0)
    }
}

#[derive(Clone, Debug)]
struct ScopeId(Arc<()>);

/// Native general-committee arithmetic within the initial resource ceiling.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Committee(usize);
impl Committee {
    /// Captures a supported roster size. This is not native P admission.
    pub fn new(n: usize) -> Result<Self, Error> {
        if !(4..=64).contains(&n) {
            return Err(Error::Roster);
        }
        Ok(Self(n))
    }
    /// Ordered roster length.
    pub const fn len(self) -> usize {
        self.0
    }
    /// Supported committees are never empty.
    pub const fn is_empty(self) -> bool {
        false
    }
    /// Native fault budget, including oversized 3f+1 rosters.
    pub const fn faults(self) -> usize {
        (self.0 - 1) / 3
    }
    /// Native phase quorum, distinct from an application's planning threshold.
    pub const fn quorum(self) -> usize {
        self.0 - self.faults()
    }
    /// Matching original follower preferences required for fast eligibility.
    pub const fn fast_support(self) -> usize {
        self.0 / 2
    }
}

/// Authenticated deployment field limits. No field is truncated on overflow.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    /// Maximum opaque original report body length.
    pub report_bytes: usize,
    /// Maximum canonical complete-order body length.
    pub order_bytes: usize,
    /// Maximum deterministic Build record length.
    pub build_bytes: usize,
    /// Maximum application material catalogue length.
    pub material_bytes: usize,
    /// Deployment aggregate cap for a complete retained origin envelope.
    pub origin_bytes: usize,
}
impl Limits {
    fn check(self) -> Result<(), Error> {
        if [
            self.report_bytes,
            self.order_bytes,
            self.build_bytes,
            self.material_bytes,
        ]
        .into_iter()
        .any(|n| n > MAX_FIRST_BYTES)
        {
            return Err(Error::Limit);
        }
        if self.origin_bytes == 0 || self.origin_bytes > MAX_EVIDENCE_BYTES {
            return Err(Error::Limit);
        }
        Ok(())
    }
    /// Checks declared worst-case envelopes against individual and aggregate
    /// ceilings before startup. This does not validate Core election or crypto.
    pub fn validate<S: certificate::Scheme, D: Digest>(self, core: &Core<D>) -> Result<(), Error> {
        self.check()?;
        let n = core.followers.len().checked_add(1).ok_or(Error::Limit)?;
        if !(3..=64).contains(&n) || D::SIZE != 32 {
            return Err(Error::Limit);
        }
        // Every native owner occupies at most one byte for the supported roster.
        let attestation = 4usize
            .checked_add(1)
            .and_then(|n| n.checked_add(S::Signature::SIZE))
            .ok_or(Error::Limit)?;
        if attestation - 4 > NATIVE_BYTES {
            return Err(Error::Limit);
        }
        let first = 8usize
            + 8
            + D::SIZE
            + native_size(&core.slot.proposal.round)
            + 4
            + 1
            + 2 * D::SIZE
            + 4
            + 2
            + 8
            + self.report_bytes
            + self.order_bytes
            + attestation;
        if first > MAX_FIRST_BYTES {
            return Err(Error::Limit);
        }
        // A history notice repeats its future carrier round in the snapshot.
        // Budget the largest view encoding in the captured epoch and a nonempty
        // history head, without allocating an advertised maximum-sized report.
        let recovery_round = native_size(&Round::new(
            core.slot.proposal.round.epoch(),
            View::new(u64::MAX),
        ));
        let snapshot = 8 + D::SIZE + 4 + recovery_round + 4 + 1 + D::SIZE + 8;
        let recover = 8
            + 8
            + D::SIZE
            + recovery_round
            + 4
            + 1
            + 8
            + 3 * D::SIZE
            + snapshot
            + 1
            + 4
            + self.report_bytes
            + attestation;
        if recover > MAX_FIRST_BYTES {
            return Err(Error::Limit);
        }
        let decision = 8 + core.slot.encode_size() + D::SIZE + 4 + self.order_bytes;
        let select = 8
            + 8
            + D::SIZE
            + native_size(&core.slot.proposal.round)
            + 4
            + 1
            + 2 * D::SIZE
            + attestation;
        let total = n
            .checked_mul(first)
            .and_then(|n| {
                n.checked_add(
                    8 + 8
                        + decision
                        + core.encode_size()
                        + 4
                        + D::SIZE
                        + 4
                        + self.build_bytes
                        + 4
                        + self.material_bytes
                        + select,
                )
            })
            .ok_or(Error::Limit)?;
        if total > self.origin_bytes {
            return Err(Error::Limit);
        }
        Ok(())
    }
}

const fn blob_size(b: &[u8]) -> usize {
    4 + b.len()
}
fn write_blob(b: &[u8], w: &mut impl BufMut) {
    // Oversized in-memory objects are rejected before signing or acceptance.
    // The size conversion also prevents a truncated length from being emitted.
    u32::try_from(b.len())
        .expect("G1 field exceeds u32")
        .write(w);
    w.put_slice(b);
}
fn read_blob(r: &mut impl Buf, limit: usize) -> Result<Bytes, CodecError> {
    let n = u32::read(r)? as usize;
    if n > limit {
        return Err(CodecError::InvalidLength(n));
    }
    if r.remaining() < n {
        return Err(CodecError::EndOfBuffer);
    }
    Ok(r.copy_to_bytes(n))
}
fn write_native<T: Write + EncodeSize>(v: &T, w: &mut impl BufMut) {
    write_blob(&v.encode(), w);
}
fn native_size<T: EncodeSize>(v: &T) -> usize {
    4 + v.encode_size()
}
fn read_native<T: Read<Cfg = ()>>(r: &mut impl Buf) -> Result<T, CodecError> {
    T::decode(read_blob(r, NATIVE_BYTES)?)
}
fn write_owner(v: Participant, w: &mut impl BufMut) {
    v.get().write(w);
}
fn read_owner(r: &mut impl Buf) -> Result<Participant, CodecError> {
    let n = u32::read(r)?;
    if n >= 64 {
        return Err(CodecError::InvalidLength(n as usize));
    }
    Ok(Participant::new(n))
}
fn option_size(v: &Option<Bytes>) -> usize {
    1 + v.as_ref().map_or(0, |v| blob_size(v))
}
fn write_option(v: &Option<Bytes>, w: &mut impl BufMut) {
    match v {
        None => 0u8.write(w),
        Some(v) => {
            1u8.write(w);
            write_blob(v, w);
        }
    }
}
fn read_option(r: &mut impl Buf, limit: usize) -> Result<Option<Bytes>, CodecError> {
    match u8::read(r)? {
        0 => Ok(None),
        1 => Ok(Some(read_blob(r, limit)?)),
        _ => Err(CodecError::Invalid("G1 optional field", "tag")),
    }
}
trait Frame: Sized {
    const MAGIC: [u8; 4];
    const MAX_BYTES: usize = MAX_EVIDENCE_BYTES;
    type Cfg;
    fn max_bytes(_: &Self::Cfg) -> usize {
        Self::MAX_BYTES
    }
    fn body_size(&self) -> usize;
    fn write_body(&self, w: &mut impl BufMut);
    fn read_body(r: &mut impl Buf, cfg: &Self::Cfg) -> Result<Self, CodecError>;
}
macro_rules! frame_codec {
    ($ty:ty, [$($bounds:tt)*], $cfg:ty) => {
        impl<$($bounds)*> Write for $ty {
            fn write(&self, w: &mut impl BufMut) {
                w.put_slice(&Self::MAGIC);
                u32::try_from(self.body_size()).expect("G1 frame exceeds u32").write(w);
                self.write_body(w);
            }
        }
        impl<$($bounds)*> EncodeSize for $ty {
            fn encode_size(&self) -> usize { 8 + self.body_size() }
        }
        impl<$($bounds)*> Read for $ty {
            type Cfg = $cfg;
            fn read_cfg(r: &mut impl Buf, cfg: &Self::Cfg) -> Result<Self, CodecError> {
                if D::SIZE != 32 {
                    return Err(CodecError::Invalid("G1 frame", "digest size"));
                }
                if <[u8; 4]>::read(r)? != Self::MAGIC {
                    return Err(CodecError::Invalid("G1 frame", "type/version"));
                }
                let max = Self::max_bytes(cfg).checked_sub(8).ok_or(CodecError::Invalid("G1 frame", "limit"))?;
                let mut body = read_blob(r, max)?;
                let value = Self::read_body(&mut body, cfg)?;
                if body.has_remaining() { return Err(CodecError::ExtraData(body.remaining())); }
                Ok(value)
            }
        }
    };
}
fn bounded(v: &impl EncodeSize) -> Result<(), Error> {
    if v.encode_size() > MAX_EVIDENCE_BYTES {
        Err(Error::Limit)
    } else {
        Ok(())
    }
}

/// Native parent identity, never a parent interpretation or execution state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NativeParent<D: Digest> {
    /// Trusted genesis anchor, whose native view is zero.
    Genesis(D),
    /// A genuine native parent round and payload digest.
    Proposal { round: Round, digest: D },
}
impl<D: Digest> NativeParent<D> {
    fn size(&self) -> usize {
        1 + match self {
            Self::Genesis(d) => d.encode_size(),
            Self::Proposal { round, digest } => native_size(round) + digest.encode_size(),
        }
    }
    fn write(&self, w: &mut impl BufMut) {
        match self {
            Self::Genesis(d) => {
                0u8.write(w);
                d.write(w);
            }
            Self::Proposal { round, digest } => {
                1u8.write(w);
                write_native(round, w);
                digest.write(w);
            }
        }
    }
    fn read(r: &mut impl Buf) -> Result<Self, CodecError> {
        match u8::read(r)? {
            0 => Ok(Self::Genesis(D::read(r)?)),
            1 => Ok(Self::Proposal {
                round: read_native(r)?,
                digest: D::read(r)?,
            }),
            _ => Err(CodecError::Invalid("G1 parent", "tag")),
        }
    }
}

/// Captured immutable original cut and native-parent context.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Slot<D: Digest> {
    /// Protocol, selector, codec, limits, and application configuration ID.
    pub profile: D,
    /// Authenticated deployment/genesis/cut domain.
    pub domain: D,
    /// Commitment to the complete ordered native roster.
    pub roster: D,
    /// Stable cut number.
    pub cut: u64,
    /// Exact original native proposal.
    pub proposal: Proposal<D>,
    /// Captured native parent, verified against native ancestry by the caller.
    pub parent: NativeParent<D>,
}
impl<D: Digest> Slot<D> {
    /// Canonical identity in the fresh G1 hash domain.
    pub fn id<H: Hasher<Digest = D>>(&self) -> D {
        H::hash(&[SLOT, &self.encode()])
    }
    /// Ordered roster commitment for this profile.
    pub fn roster<H: Hasher<Digest = D>, S: certificate::Scheme>(s: &S) -> D {
        roster::<H, S>(&VerificationSource::Scheme(s))
    }
    fn check<H: Hasher<Digest = D>, S: certificate::Scheme>(
        &self,
        source: &VerificationSource<'_, S>,
    ) -> Result<Committee, Error> {
        if D::SIZE != 32 {
            return Err(Error::Context);
        }
        let committee = committee::<S>(source)?;
        if self.roster != roster::<H, S>(source) {
            return Err(Error::Context);
        }
        let parent = match self.parent {
            NativeParent::Genesis(_) => View::zero(),
            NativeParent::Proposal { round, .. } => {
                if round.epoch() != self.proposal.round.epoch() {
                    return Err(Error::Context);
                }
                round.view()
            }
        };
        if parent != self.proposal.parent || parent >= self.proposal.round.view() {
            return Err(Error::Context);
        }
        bounded(self)?;
        Ok(committee)
    }
}
fn roster<H: Hasher, S: certificate::Scheme>(s: &VerificationSource<'_, S>) -> H::Digest {
    let mut b = Vec::new();
    (s.participants().len() as u32).write(&mut b);
    for key in s.participants().iter() {
        write_native(key, &mut b);
    }
    H::hash(&[ROSTER, &b])
}
fn committee<S: certificate::Scheme>(s: &VerificationSource<'_, S>) -> Result<Committee, Error> {
    if !S::is_attributable() {
        return Err(Error::Roster);
    }
    Committee::new(s.participants().len())
}
impl<D: Digest> Frame for Slot<D> {
    const MAGIC: [u8; 4] = *b"G1S1";
    type Cfg = ();
    fn body_size(&self) -> usize {
        self.profile.encode_size()
            + self.domain.encode_size()
            + self.roster.encode_size()
            + 8
            + native_size(&self.proposal)
            + self.parent.size()
    }
    fn write_body(&self, w: &mut impl BufMut) {
        self.profile.write(w);
        self.domain.write(w);
        self.roster.write(w);
        self.cut.write(w);
        write_native(&self.proposal, w);
        self.parent.write(w);
    }
    fn read_body(r: &mut impl Buf, _: &()) -> Result<Self, CodecError> {
        Ok(Self {
            profile: D::read(r)?,
            domain: D::read(r)?,
            roster: D::read(r)?,
            cut: u64::read(r)?,
            proposal: read_native(r)?,
            parent: NativeParent::read(r)?,
        })
    }
}
frame_codec!(Slot<D>, [D: Digest], ());

/// Canonical, externally selected original leader and q-1 followers.
/// Verification compares this entire object with the trusted expected Core.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Core<D: Digest> {
    /// Complete original context, including the ordered roster digest.
    pub slot: Slot<D>,
    /// Original native elected leader.
    pub leader: Participant,
    /// Strictly ascending distinct identities excluding the original leader.
    pub followers: Vec<Participant>,
}
impl<D: Digest> Core<D> {
    /// Derives the lexicographic original-view cohort from a captured roster.
    ///
    /// The profile must bind this rule. The caller obtains the original leader,
    /// proposal and parent from native admission, not from a peer-supplied Core.
    /// This checks roster/context structure; it does not prove leader election or
    /// native admission. Recovery never depends on every cohort being visited.
    pub fn derive<H: Hasher<Digest = D>, S: certificate::Scheme>(
        scheme: &S,
        slot: Slot<D>,
        leader: Participant,
    ) -> Result<Self, Error> {
        let c = slot.check::<H, S>(&VerificationSource::Scheme(scheme))?;
        if usize::from(leader) >= c.len() {
            return Err(Error::Identity);
        }
        let candidates: Vec<_> = (0..c.len() as u32)
            .map(Participant::new)
            .filter(|owner| *owner != leader)
            .collect();
        let mut remaining = c.quorum() - 1;
        let count = combinations(candidates.len(), remaining)?;
        let mut rank = slot.proposal.round.view().get() % count;
        let mut followers = Vec::with_capacity(remaining);
        for (i, owner) in candidates.into_iter().enumerate() {
            if remaining == 0 {
                break;
            }
            let suffixes = combinations(c.len() - 2 - i, remaining - 1)?;
            if rank < suffixes {
                followers.push(owner);
                remaining -= 1;
            } else {
                rank -= suffixes;
            }
        }
        if remaining != 0 || rank != 0 {
            return Err(Error::Limit);
        }
        let core = Self {
            slot,
            leader,
            followers,
        };
        core.check::<H, S>(&VerificationSource::Scheme(scheme))?;
        Ok(core)
    }

    /// Canonical identity of the fixed original cohort.
    pub fn id<H: Hasher<Digest = D>>(&self) -> D {
        H::hash(&[CORE, &self.encode()])
    }
    fn check<H: Hasher<Digest = D>, S: certificate::Scheme>(
        &self,
        source: &VerificationSource<'_, S>,
    ) -> Result<Committee, Error> {
        let c = self.slot.check::<H, S>(source)?;
        if usize::from(self.leader) >= c.len()
            || self.followers.len() != c.quorum() - 1
            || self
                .followers
                .iter()
                .any(|p| *p == self.leader || usize::from(*p) >= c.len())
            || self.followers.windows(2).any(|p| p[0] >= p[1])
        {
            return Err(Error::Identity);
        }
        bounded(self)?;
        Ok(c)
    }
}

fn combinations(n: usize, k: usize) -> Result<u64, Error> {
    if k > n {
        return Ok(0);
    }
    let k = k.min(n - k);
    let mut count = 1u128;
    for i in 1..=k {
        count = count.checked_mul((n - k + i) as u128).ok_or(Error::Limit)? / i as u128;
    }
    u64::try_from(count).map_err(|_| Error::Limit)
}

impl<D: Digest> Frame for Core<D> {
    const MAGIC: [u8; 4] = *b"G1K1";
    type Cfg = ();
    fn body_size(&self) -> usize {
        self.slot.encode_size() + 8 + 4 * self.followers.len()
    }
    fn write_body(&self, w: &mut impl BufMut) {
        self.slot.write(w);
        write_owner(self.leader, w);
        (self.followers.len() as u32).write(w);
        for p in &self.followers {
            write_owner(*p, w);
        }
    }
    fn read_body(r: &mut impl Buf, _: &()) -> Result<Self, CodecError> {
        let slot = Slot::read(r)?;
        let leader = read_owner(r)?;
        let n = u32::read(r)? as usize;
        if !(2..=63).contains(&n) {
            return Err(CodecError::InvalidLength(n));
        }
        let mut followers = Vec::with_capacity(n);
        for _ in 0..n {
            followers.push(read_owner(r)?);
        }
        if followers.contains(&leader) || followers.windows(2).any(|p| p[0] >= p[1]) {
            return Err(CodecError::Invalid("G1 Core", "owners"));
        }
        Ok(Self {
            slot,
            leader,
            followers,
        })
    }
}
frame_codec!(Core<D>, [D: Digest], ());

/// An original owner's independently optional report and complete-order intent.
/// `Some(empty)` is distinct from absence and requires application validation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct First<D: Digest> {
    /// Exact immutable original Core ID.
    pub core: D,
    /// Application's exact-P input commitment.
    pub input: D,
    /// Must equal the native attestation signer.
    pub owner: Participant,
    /// Opaque report claim authenticated by this FIRST, with no inner signature.
    pub report: Option<Bytes>,
    /// Opaque canonical complete E for this exact input, or explicit absence.
    pub preference: Option<Bytes>,
}
impl<D: Digest> First<D> {
    fn check(&self, l: Limits) -> Result<(), Error> {
        if usize::from(self.owner) >= 64
            || self
                .report
                .as_ref()
                .is_some_and(|b| b.len() > l.report_bytes)
            || self
                .preference
                .as_ref()
                .is_some_and(|b| b.len() > l.order_bytes)
        {
            return Err(Error::Limit);
        }
        Ok(())
    }
    fn size(&self) -> usize {
        self.core.encode_size()
            + self.input.encode_size()
            + 4
            + option_size(&self.report)
            + option_size(&self.preference)
    }
    fn write(&self, w: &mut impl BufMut) {
        self.core.write(w);
        self.input.write(w);
        write_owner(self.owner, w);
        write_option(&self.report, w);
        write_option(&self.preference, w);
    }
    fn read(r: &mut impl Buf, l: Limits) -> Result<Self, CodecError> {
        Ok(Self {
            core: D::read(r)?,
            input: D::read(r)?,
            owner: read_owner(r)?,
            report: read_option(r, l.report_bytes)?,
            preference: read_option(r, l.order_bytes)?,
        })
    }
}

/// A phase quorum authenticates one exact decision. It is not native inclusion.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    /// Normal interpretation final vote, paired with native finality elsewhere.
    FastFinal,
    /// Crypto-only legacy phase, not general recovery admission.
    Prepare,
    /// Crypto-only legacy phase, not general recovery admission.
    Commit,
}
impl Phase {
    const fn tag(self) -> u8 {
        match self {
            Self::FastFinal => 2,
            Self::Prepare => 3,
            Self::Commit => 4,
        }
    }
}
/// Fresh G1 signed message variants, never aliases of legacy M1 messages.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Kind<D: Digest> {
    /// Original independent report and preference.
    First(First<D>),
    /// Original leader binds an immutable origin body and semantic decision.
    Select { body: D, decision: D },
    /// A single exact-decision phase vote.
    Phase { phase: Phase, decision: D },
    /// Authenticated original-history data, not recovery admission or a vote.
    Recover(issuance::history::Recover<D>),
    /// Recovery role bound to an exact unsigned proposal and entry context.
    Recovery {
        /// Coordinator proposal, prepare, or commit role.
        phase: recovery::Phase,
        /// Exact immutable admission and decision subject.
        subject: recovery::Subject<D>,
    },
    /// Request for a later recovery attempt, retaining exact predecessor proof.
    Wish(entry::Wish<D>),
}
/// Exact signing carrier coordinates and fresh G1 body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Message<D: Digest> {
    /// Original Slot ID, unchanged by a recovery carrier.
    pub slot: D,
    /// Actual signing ballot.
    pub round: Round,
    /// Actual authorized carrier leader, independently checked by the caller.
    pub leader: Participant,
    /// Authenticated G1 role and payload.
    pub kind: Kind<D>,
}
impl<D: Digest> Message<D> {
    fn check(&self, c: Committee, l: Limits) -> Result<(), Error> {
        l.check()?;
        if D::SIZE != 32 {
            return Err(Error::Context);
        }
        if usize::from(self.leader) >= c.len() {
            return Err(Error::Identity);
        }
        if let Kind::First(row) = &self.kind {
            row.check(l)?;
        }
        if let Kind::Recover(recover) = &self.kind {
            recover.check(c, l)?;
            if recover.snapshot.slot() != self.slot
                || recover.snapshot.ballot() != self.round
                || recover.snapshot.leader() != self.leader
            {
                return Err(Error::Context);
            }
        }
        if let Kind::Wish(wish) = &self.kind
            && (wish.target.ballot != self.round
                || wish.target.leader != self.leader
                || usize::from(wish.target.leader) >= c.len())
        {
            return Err(Error::Context);
        }
        if self.encode_size() > MAX_FIRST_BYTES {
            return Err(Error::Limit);
        }
        Ok(())
    }
    fn signed_bytes(&self) -> Vec<u8> {
        let domain = match self.kind {
            Kind::Recover(_) => RECOVER_SIGNING,
            Kind::Recovery { .. } => RECOVERY_SIGNING,
            Kind::Wish(_) => WISH_SIGNING,
            _ => SIGNING,
        };
        [domain, self.encode().as_ref()].concat()
    }
    fn signer_valid(&self, signer: Participant) -> bool {
        match &self.kind {
            Kind::First(row) => row.owner == signer,
            Kind::Select { .. }
            | Kind::Recovery {
                phase: recovery::Phase::Propose,
                ..
            } => self.leader == signer,
            Kind::Recover(recover) => recover.snapshot.owner() == signer,
            _ => true,
        }
    }
    const fn quorum_phase(&self) -> bool {
        matches!(
            self.kind,
            Kind::Phase { .. }
                | Kind::Recovery {
                    phase: recovery::Phase::Prepare | recovery::Phase::Commit,
                    ..
                }
        )
    }
}
impl<D: Digest> Frame for Message<D> {
    const MAGIC: [u8; 4] = *b"G1M1";
    const MAX_BYTES: usize = MAX_FIRST_BYTES;
    type Cfg = Limits;
    fn body_size(&self) -> usize {
        self.slot.encode_size()
            + native_size(&self.round)
            + 5
            + match &self.kind {
                Kind::First(r) => r.size(),
                Kind::Select { body, decision } => body.encode_size() + decision.encode_size(),
                Kind::Phase { decision, .. } => decision.encode_size(),
                Kind::Recover(recover) => recover.encode_size(),
                Kind::Recovery { subject, .. } => subject.encode_size(),
                Kind::Wish(wish) => wish.encode_size(),
            }
    }
    fn write_body(&self, w: &mut impl BufMut) {
        self.slot.write(w);
        write_native(&self.round, w);
        write_owner(self.leader, w);
        match &self.kind {
            Kind::First(r) => {
                0u8.write(w);
                r.write(w);
            }
            Kind::Select { body, decision } => {
                1u8.write(w);
                body.write(w);
                decision.write(w);
            }
            Kind::Phase { phase, decision } => {
                phase.tag().write(w);
                decision.write(w);
            }
            Kind::Recover(recover) => {
                5u8.write(w);
                recover.write(w);
            }
            Kind::Recovery { phase, subject } => {
                match phase {
                    recovery::Phase::Propose => 6u8,
                    recovery::Phase::Prepare => 7u8,
                    recovery::Phase::Commit => 8u8,
                }
                .write(w);
                subject.write(w);
            }
            Kind::Wish(wish) => {
                9u8.write(w);
                wish.write(w);
            }
        }
    }
    fn read_body(r: &mut impl Buf, l: &Limits) -> Result<Self, CodecError> {
        l.check()
            .map_err(|_| CodecError::Invalid("G1 limits", "ceiling"))?;
        let slot = D::read(r)?;
        let round = read_native(r)?;
        let leader = read_owner(r)?;
        let kind = match u8::read(r)? {
            0 => Kind::First(First::read(r, *l)?),
            1 => Kind::Select {
                body: D::read(r)?,
                decision: D::read(r)?,
            },
            tag @ 2..=4 => Kind::Phase {
                phase: match tag {
                    2 => Phase::FastFinal,
                    3 => Phase::Prepare,
                    _ => Phase::Commit,
                },
                decision: D::read(r)?,
            },
            5 => Kind::Recover(issuance::history::Recover::read_cfg(r, l)?),
            tag @ 6..=8 => Kind::Recovery {
                phase: match tag {
                    6 => recovery::Phase::Propose,
                    7 => recovery::Phase::Prepare,
                    _ => recovery::Phase::Commit,
                },
                subject: recovery::Subject::read(r)?,
            },
            9 => Kind::Wish(entry::Wish::read(r)?),
            _ => return Err(CodecError::Invalid("G1 message", "kind")),
        };
        Ok(Self {
            slot,
            round,
            leader,
            kind,
        })
    }
}
frame_codec!(Message<D>, [D: Digest], Limits);

/// Attributable native ExtensionAgreement signature over a fresh G1 message.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signed<S: certificate::Scheme, D: Digest> {
    /// Exact immutable signed message.
    pub message: Message<D>,
    /// Original native signature, retaining its actual signer.
    pub attestation: Attestation<S>,
}
impl<S: scheme::Scheme<D>, D: Digest> Signed<S, D> {
    /// Cryptographic signing only. The native owner must durably reserve and
    /// authorize this exact subject before calling; this method grants no right.
    pub fn sign(s: &S, message: Message<D>, limits: Limits) -> Result<Self, Error> {
        let c = committee::<S>(&VerificationSource::Scheme(s))?;
        message.check(c, limits)?;
        let signer = s.me().ok_or(Error::Signature)?;
        if signer.encode_size() + S::Signature::SIZE > NATIVE_BYTES {
            return Err(Error::Limit);
        }
        if !message.signer_valid(signer) {
            return Err(Error::Identity);
        }
        // Native attestation is a varint owner plus a fixed signature. Check the
        // complete outer frame before invoking even the cryptographic signer.
        if 8 + message.encode_size() + 4 + signer.encode_size() + S::Signature::SIZE
            > MAX_FIRST_BYTES
        {
            return Err(Error::Limit);
        }
        let bytes = message.signed_bytes();
        let attestation = s
            .sign::<D>(Subject::ExtensionAgreement {
                round: message.round,
                payload: &bytes,
            })
            .ok_or(Error::Signature)?;
        if !message.signer_valid(attestation.signer) {
            return Err(Error::Identity);
        }
        let signed = Self {
            message,
            attestation,
        };
        if signed.encode_size() > MAX_FIRST_BYTES {
            return Err(Error::Limit);
        }
        Ok(signed)
    }
    /// Checks signature, scheme, owner role and byte bounds, without granting
    /// native admission, recovery entry or application-policy authority.
    pub fn verify<R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &S,
        limits: Limits,
        strategy: &impl Strategy,
    ) -> bool {
        self.verify_with(rng, &VerificationSource::Scheme(s), limits, strategy)
    }
    /// Identical public-only verification through an immutable captured scope.
    pub fn verify_scoped<R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &Scoped<S>,
        limits: Limits,
        strategy: &impl Strategy,
    ) -> bool {
        self.verify_with(rng, &VerificationSource::Scoped(s), limits, strategy)
    }
    fn verify_with<R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &VerificationSource<'_, S>,
        limits: Limits,
        strategy: &impl Strategy,
    ) -> bool {
        let Ok(c) = committee::<S>(s) else {
            return false;
        };
        if self.message.check(c, limits).is_err()
            || self.encode_size() > MAX_FIRST_BYTES
            || usize::from(self.attestation.signer) >= c.len()
        {
            return false;
        }
        if !self.message.signer_valid(self.attestation.signer) {
            return false;
        }
        let bytes = self.message.signed_bytes();
        s.verify_attestation::<_, D>(
            rng,
            Subject::ExtensionAgreement {
                round: self.message.round,
                payload: &bytes,
            },
            &self.attestation,
            strategy,
        )
    }
}
impl<S: certificate::Scheme, D: Digest> Frame for Signed<S, D> {
    const MAGIC: [u8; 4] = *b"G1A1";
    const MAX_BYTES: usize = MAX_FIRST_BYTES;
    type Cfg = Limits;
    fn body_size(&self) -> usize {
        self.message.encode_size() + native_size(&self.attestation)
    }
    fn write_body(&self, w: &mut impl BufMut) {
        self.message.write(w);
        write_native(&self.attestation, w);
    }
    fn read_body(r: &mut impl Buf, l: &Limits) -> Result<Self, CodecError> {
        Ok(Self {
            message: Message::read_cfg(r, l)?,
            attestation: read_native(r)?,
        })
    }
}
frame_codec!(Signed<S, D>, [S: certificate::Scheme, D: Digest], Limits);

/// Checked original FIRST population available before deterministic Build.
/// Only complete original signature verification constructs this capability.
#[derive(Clone, Debug)]
pub struct VerifiedRows<S: certificate::Scheme, D: Digest> {
    core: Core<D>,
    input: D,
    committee: Committee,
    rows: Vec<First<D>>,
    originals: Vec<Signed<S, D>>,
    participants: Vec<S::PublicKey>,
}
impl<S: certificate::Scheme, D: Digest> VerifiedRows<S, D> {
    /// Owner-ascending complete Core rows. Missing outside-Core owners are not absence.
    pub fn rows(&self) -> &[First<D>] {
        &self.rows
    }
    /// Exact immutable original authenticated envelopes, in the same order.
    pub fn originals(&self) -> &[Signed<S, D>] {
        &self.originals
    }
    /// Captured original native context.
    pub const fn slot(&self) -> &Slot<D> {
        &self.core.slot
    }
    /// Entire trusted original cohort.
    pub const fn core(&self) -> &Core<D> {
        &self.core
    }
    /// Exact-P input commitment shared by every original.
    pub const fn input(&self) -> D {
        self.input
    }
    /// Captured native roster arithmetic.
    pub const fn committee(&self) -> Committee {
        self.committee
    }
    /// Complete ordered verified public roster, with no signing authority.
    pub fn participants(&self) -> &[S::PublicKey] {
        &self.participants
    }
}

/// Authenticates all q original FIRSTs against the trusted native-selected Core.
/// `validate` checks each present report's grammar/context and each present
/// preference's canonical complete exact-P legality. It must not run Build or
/// wait for material. Signature authentication alone does not establish meaning.
#[allow(clippy::too_many_arguments)]
pub fn verify_firsts<H: Hasher, S: scheme::Scheme<H::Digest>, R: CryptoRng>(
    rng: &mut R,
    s: &S,
    expected: &Core<H::Digest>,
    input: H::Digest,
    firsts: &[Signed<S, H::Digest>],
    limits: Limits,
    validate: impl FnMut(&First<H::Digest>) -> bool,
    strategy: &impl Strategy,
) -> Result<VerifiedRows<S, H::Digest>, Error> {
    verify_firsts_with::<H, S, R>(
        rng,
        &VerificationSource::Scheme(s),
        expected,
        input,
        firsts,
        limits,
        validate,
        strategy,
    )
}
/// Same complete-origin-row authentication through a captured public-only scope.
#[allow(clippy::too_many_arguments)]
pub fn verify_firsts_scoped<H: Hasher, S: scheme::Scheme<H::Digest>, R: CryptoRng>(
    rng: &mut R,
    s: &Scoped<S>,
    expected: &Core<H::Digest>,
    input: H::Digest,
    firsts: &[Signed<S, H::Digest>],
    limits: Limits,
    validate: impl FnMut(&First<H::Digest>) -> bool,
    strategy: &impl Strategy,
) -> Result<VerifiedRows<S, H::Digest>, Error> {
    verify_firsts_with::<H, S, R>(
        rng,
        &VerificationSource::Scoped(s),
        expected,
        input,
        firsts,
        limits,
        validate,
        strategy,
    )
}
#[allow(clippy::too_many_arguments)]
fn verify_firsts_with<H: Hasher, S: scheme::Scheme<H::Digest>, R: CryptoRng>(
    rng: &mut R,
    s: &VerificationSource<'_, S>,
    expected: &Core<H::Digest>,
    input: H::Digest,
    firsts: &[Signed<S, H::Digest>],
    limits: Limits,
    mut validate: impl FnMut(&First<H::Digest>) -> bool,
    strategy: &impl Strategy,
) -> Result<VerifiedRows<S, H::Digest>, Error> {
    limits.check()?;
    let c = expected.check::<H, S>(s)?;
    limits.validate::<S, H::Digest>(expected)?;
    let rows =
        authenticate_firsts_with::<H, S, R>(rng, s, expected, input, firsts, c, limits, strategy)?;
    // Only the trusted-context path constructs application-facing checked rows.
    if rows.iter().any(|r| !validate(r)) {
        return Err(Error::Policy);
    }
    Ok(VerifiedRows {
        core: expected.clone(),
        input,
        committee: c,
        rows,
        originals: firsts.to_vec(),
        participants: s.participants().iter().cloned().collect(),
    })
}

#[allow(clippy::too_many_arguments)]
fn authenticate_firsts_with<H: Hasher, S: scheme::Scheme<H::Digest>, R: CryptoRng>(
    rng: &mut R,
    s: &VerificationSource<'_, S>,
    claimed: &Core<H::Digest>,
    input: H::Digest,
    firsts: &[Signed<S, H::Digest>],
    c: Committee,
    limits: Limits,
    strategy: &impl Strategy,
) -> Result<Vec<First<H::Digest>>, Error> {
    if firsts.len() != c.quorum() {
        return Err(Error::Identity);
    }
    for signed in firsts {
        let Kind::First(row) = &signed.message.kind else {
            return Err(Error::Phase);
        };
        row.check(limits)?;
        if signed.encode_size() > MAX_FIRST_BYTES {
            return Err(Error::Limit);
        }
    }
    let size = firsts
        .iter()
        .try_fold(0usize, |size, first| size.checked_add(first.encode_size()))
        .ok_or(Error::Limit)?;
    if size > limits.origin_bytes {
        return Err(Error::Limit);
    }
    let mut rows = Vec::with_capacity(c.quorum());
    let mut previous = None;
    for signed in firsts {
        let Kind::First(row) = &signed.message.kind else {
            return Err(Error::Phase);
        };
        if previous.is_some_and(|p| p >= row.owner)
            || (row.owner != claimed.leader && !claimed.followers.contains(&row.owner))
            || row.owner != signed.attestation.signer
        {
            return Err(Error::Identity);
        }
        previous = Some(row.owner);
        if signed.message.slot != claimed.slot.id::<H>()
            || signed.message.round != claimed.slot.proposal.round
            || signed.message.leader != claimed.leader
            || row.core != claimed.id::<H>()
            || row.input != input
        {
            return Err(Error::Context);
        }
        if row.owner == claimed.leader && (row.report.is_some() || row.preference.is_some()) {
            return Err(Error::Context);
        }
        if !signed.verify_with(rng, s, limits, strategy) {
            return Err(Error::Signature);
        }
        rows.push(row.clone());
    }
    Ok(rows)
}

/// Immutable application decision, independent of proof aliases or carrier ballot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Decision<D: Digest> {
    /// Exact original cut and native parent.
    pub slot: Slot<D>,
    /// Exact bounded P input commitment.
    pub input: D,
    /// Exact canonical complete E bytes; application validates and reconstructs D.
    pub order: Bytes,
}
impl<D: Digest> Decision<D> {
    /// Semantic identity excludes reports, Build diagnostics, SELECT and signatures.
    pub fn id<H: Hasher<Digest = D>>(&self) -> D {
        H::hash(&[DECISION, &self.encode()])
    }
}
impl<D: Digest> Frame for Decision<D> {
    const MAGIC: [u8; 4] = *b"G1D1";
    type Cfg = Limits;
    fn body_size(&self) -> usize {
        self.slot.encode_size() + self.input.encode_size() + blob_size(&self.order)
    }
    fn write_body(&self, w: &mut impl BufMut) {
        self.slot.write(w);
        self.input.write(w);
        write_blob(&self.order, w);
    }
    fn read_body(r: &mut impl Buf, l: &Limits) -> Result<Self, CodecError> {
        l.check()
            .map_err(|_| CodecError::Invalid("G1 limits", "ceiling"))?;
        Ok(Self {
            slot: Slot::read(r)?,
            input: D::read(r)?,
            order: read_blob(r, l.order_bytes)?,
        })
    }
}
frame_codec!(Decision<D>, [D: Digest], Limits);

/// Immutable original fast-origin body. Its identity excludes enclosing SELECT.
#[derive(Clone, Debug)]
pub struct OriginBody<S: certificate::Scheme, D: Digest> {
    /// Exact immutable semantic decision.
    pub decision: Decision<D>,
    /// Fixed original Core, compared with trusted context during verification.
    pub core: Core<D>,
    /// All q exact original owner-ascending FIRST envelopes.
    pub firsts: Vec<Signed<S, D>>,
    /// Application-normalized population commitment, independently replayed.
    pub population: D,
    /// Complete canonical deterministic Build record and authoritative costs.
    pub build: Bytes,
    /// Complete bounded application material catalogue, checked by the callback.
    pub material: Bytes,
}
impl<S: certificate::Scheme, D: Digest> OriginBody<S, D> {
    /// Body identity is available before SELECT signing, avoiding a hash cycle.
    pub fn id<H: Hasher<Digest = D>>(&self) -> D {
        H::hash(&[BODY, &self.encode()])
    }
}
impl<S: scheme::Scheme<D>, D: Digest> OriginBody<S, D> {
    fn preflight(&self, c: Committee, limits: Limits) -> Result<(), Error> {
        limits.check()?;
        if self.core.followers.len() > 63 || self.firsts.len() > 64 {
            return Err(Error::Limit);
        }
        if self.decision.order.len() > limits.order_bytes
            || self.build.len() > limits.build_bytes
            || self.material.len() > limits.material_bytes
        {
            return Err(Error::Limit);
        }
        for signed in &self.firsts {
            if !matches!(signed.message.kind, Kind::First(_)) {
                return Err(Error::Phase);
            }
            signed.message.check(c, limits)?;
            if signed.encode_size() > MAX_FIRST_BYTES {
                return Err(Error::Limit);
            }
        }
        if self.encode_size() > limits.origin_bytes {
            return Err(Error::Limit);
        }
        Ok(())
    }
    /// Checks a body before SELECT exists. This is neither a complete origin nor
    /// native P permission. Callbacks validate exact-P meaning and replay Build.
    #[allow(clippy::too_many_arguments)]
    pub fn verify<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &S,
        expected: &Core<D>,
        input: D,
        limits: Limits,
        validate_row: impl FnMut(&First<D>) -> bool,
        validate_build: impl FnOnce(&VerifiedRows<S, D>, &Self) -> bool,
        strategy: &impl Strategy,
    ) -> Result<VerifiedBody<D>, Error> {
        let rows = self.check_rows::<H, R>(
            rng,
            &VerificationSource::Scheme(s),
            expected,
            input,
            limits,
            validate_row,
            strategy,
        )?;
        self.finish::<H>(&rows, limits, validate_build)
    }
    #[allow(clippy::too_many_arguments)]
    fn check_rows<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &VerificationSource<'_, S>,
        expected: &Core<D>,
        input: D,
        limits: Limits,
        validate_row: impl FnMut(&First<D>) -> bool,
        strategy: &impl Strategy,
    ) -> Result<VerifiedRows<S, D>, Error> {
        limits.check()?;
        if self.encode_size() > limits.origin_bytes {
            return Err(Error::Limit);
        }
        if self.core != *expected
            || self.decision.slot != expected.slot
            || self.decision.input != input
        {
            return Err(Error::Context);
        }
        if self.decision.order.len() > limits.order_bytes
            || self.build.len() > limits.build_bytes
            || self.material.len() > limits.material_bytes
        {
            return Err(Error::Limit);
        }
        verify_firsts_with::<H, S, R>(
            rng,
            s,
            expected,
            input,
            &self.firsts,
            limits,
            validate_row,
            strategy,
        )
    }
    fn finish<H: Hasher<Digest = D>>(
        &self,
        rows: &VerifiedRows<S, D>,
        limits: Limits,
        validate_build: impl FnOnce(&VerifiedRows<S, D>, &Self) -> bool,
    ) -> Result<VerifiedBody<D>, Error> {
        if !validate_build(rows, self) {
            return Err(Error::Policy);
        }
        self.check_fast(&rows.rows, rows.committee)?;
        Ok(VerifiedBody {
            slot: self.core.slot.id::<H>(),
            decision: self.decision.id::<H>(),
            body: self.id::<H>(),
            limits,
        })
    }
    fn check_fast(&self, rows: &[First<D>], committee: Committee) -> Result<(), Error> {
        let support = rows
            .iter()
            .filter(|r| {
                r.owner != self.core.leader && r.preference.as_ref() == Some(&self.decision.order)
            })
            .count();
        if support < committee.fast_support() {
            return Err(Error::FastIneligible);
        }
        Ok(())
    }
}

/// A checked pre-SELECT body, without leader endorsement or native admission.
#[derive(Clone, Debug)]
pub struct VerifiedBody<D: Digest> {
    slot: D,
    decision: D,
    body: D,
    limits: Limits,
}
impl<D: Digest> VerifiedBody<D> {
    /// Exact local field limits under which application meaning was checked.
    pub const fn limits(&self) -> Limits {
        self.limits
    }
    /// Exact original Slot identity.
    pub const fn slot(&self) -> D {
        self.slot
    }
    /// Semantic decision identity.
    pub const fn decision(&self) -> D {
        self.decision
    }
    /// Exact checked original body identity.
    pub const fn body(&self) -> D {
        self.body
    }
}
impl<S: certificate::Scheme, D: Digest> Frame for OriginBody<S, D> {
    const MAGIC: [u8; 4] = *b"G1O1";
    type Cfg = Limits;
    fn max_bytes(l: &Limits) -> usize {
        l.origin_bytes.min(MAX_EVIDENCE_BYTES)
    }
    fn body_size(&self) -> usize {
        self.decision.encode_size()
            + self.core.encode_size()
            + 4
            + self
                .firsts
                .iter()
                .map(EncodeSize::encode_size)
                .sum::<usize>()
            + self.population.encode_size()
            + blob_size(&self.build)
            + blob_size(&self.material)
    }
    fn write_body(&self, w: &mut impl BufMut) {
        self.decision.write(w);
        self.core.write(w);
        (self.firsts.len() as u32).write(w);
        for first in &self.firsts {
            first.write(w);
        }
        self.population.write(w);
        write_blob(&self.build, w);
        write_blob(&self.material, w);
    }
    fn read_body(r: &mut impl Buf, l: &Limits) -> Result<Self, CodecError> {
        let decision = Decision::read_cfg(r, l)?;
        let core = Core::read(r)?;
        let n = u32::read(r)? as usize;
        if !(3..=64).contains(&n) {
            return Err(CodecError::InvalidLength(n));
        }
        let mut firsts = Vec::with_capacity(n);
        for _ in 0..n {
            firsts.push(Signed::read_cfg(r, l)?);
        }
        Ok(Self {
            decision,
            core,
            firsts,
            population: D::read(r)?,
            build: read_blob(r, l.build_bytes)?,
            material: read_blob(r, l.material_bytes)?,
        })
    }
}
frame_codec!(OriginBody<S, D>, [S: certificate::Scheme, D: Digest], Limits);

/// Full fast origin: immutable body plus the original leader's exact SELECT.
#[derive(Clone, Debug)]
pub struct Origin<S: certificate::Scheme, D: Digest> {
    /// Original immutable body.
    pub body: OriginBody<S, D>,
    /// Original leader SELECT binds body ID and semantic DecisionID separately.
    pub selection: Signed<S, D>,
}
impl<S: certificate::Scheme, D: Digest> Origin<S, D> {
    /// Envelope identity retains the exact original proof alias.
    pub fn id<H: Hasher<Digest = D>>(&self) -> D {
        H::hash(&[ORIGIN, &self.encode()])
    }
}
impl<S: scheme::Scheme<D>, D: Digest> Origin<S, D> {
    /// Authenticates bounded, internally consistent wire claims and fast support.
    /// This does not compare native-captured Core/Input or validate report, order
    /// or Build meaning. It creates no application or signing capability.
    pub fn authenticate<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &S,
        limits: Limits,
        strategy: &impl Strategy,
    ) -> Result<(), Error> {
        self.authenticate_with::<H, R>(rng, &VerificationSource::Scheme(s), limits, strategy)
    }
    /// Same wire authentication through a captured public-only verifier.
    pub fn authenticate_scoped<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &Scoped<S>,
        limits: Limits,
        strategy: &impl Strategy,
    ) -> Result<(), Error> {
        self.authenticate_with::<H, R>(rng, &VerificationSource::Scoped(s), limits, strategy)
    }
    fn authenticate_with<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &VerificationSource<'_, S>,
        limits: Limits,
        strategy: &impl Strategy,
    ) -> Result<(), Error> {
        let c = committee::<S>(s)?;
        self.preflight(c, limits)?;
        self.body.core.check::<H, S>(s)?;
        if self.body.decision.slot != self.body.core.slot {
            return Err(Error::Context);
        }
        let rows = authenticate_firsts_with::<H, S, R>(
            rng,
            s,
            &self.body.core,
            self.body.decision.input,
            &self.body.firsts,
            c,
            limits,
            strategy,
        )?;
        self.check_selection::<H, R>(rng, s, &self.body.core, limits, strategy)?;
        self.body.check_fast(&rows, c)
    }
    fn preflight(&self, c: Committee, limits: Limits) -> Result<(), Error> {
        self.body.preflight(c, limits)?;
        if !matches!(&self.selection.message.kind, Kind::Select { .. }) {
            return Err(Error::Phase);
        }
        self.selection.message.check(c, limits)?;
        if self.selection.encode_size() > MAX_FIRST_BYTES
            || self.encode_size() > limits.origin_bytes
        {
            return Err(Error::Limit);
        }
        Ok(())
    }
    fn check_selection<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &VerificationSource<'_, S>,
        core: &Core<D>,
        limits: Limits,
        strategy: &impl Strategy,
    ) -> Result<(D, D), Error> {
        let decision = self.body.decision.id::<H>();
        let body = self.body.id::<H>();
        if self.selection.attestation.signer != core.leader
            || self.selection.message
                != (Message {
                    slot: core.slot.id::<H>(),
                    round: core.slot.proposal.round,
                    leader: core.leader,
                    kind: Kind::Select { body, decision },
                })
        {
            return Err(Error::Context);
        }
        if !self.selection.verify_with(rng, s, limits, strategy) {
            return Err(Error::Signature);
        }
        Ok((decision, body))
    }
    /// Verifies full origin and fast eligibility. The callbacks must validate
    /// complete exact-P semantics and replay all Build/population/cost/catalogue
    /// claims. `expected` is fixed native context, never chosen from this proof.
    #[allow(clippy::too_many_arguments)]
    pub fn verify<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &S,
        expected: &Core<D>,
        input: D,
        limits: Limits,
        validate_row: impl FnMut(&First<D>) -> bool,
        validate_build: impl FnOnce(&VerifiedRows<S, D>, &OriginBody<S, D>) -> bool,
        strategy: &impl Strategy,
    ) -> Result<VerifiedOrigin<D>, Error> {
        self.verify_with::<H, R>(
            rng,
            &VerificationSource::Scheme(s),
            expected,
            input,
            limits,
            validate_row,
            validate_build,
            strategy,
        )
    }
    /// Identical full validation through a public-only captured verifier.
    #[allow(clippy::too_many_arguments)]
    pub fn verify_scoped<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &Scoped<S>,
        expected: &Core<D>,
        input: D,
        limits: Limits,
        validate_row: impl FnMut(&First<D>) -> bool,
        validate_build: impl FnOnce(&VerifiedRows<S, D>, &OriginBody<S, D>) -> bool,
        strategy: &impl Strategy,
    ) -> Result<VerifiedOrigin<D>, Error> {
        self.verify_with::<H, R>(
            rng,
            &VerificationSource::Scoped(s),
            expected,
            input,
            limits,
            validate_row,
            validate_build,
            strategy,
        )
    }
    #[allow(clippy::too_many_arguments)]
    fn verify_with<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &VerificationSource<'_, S>,
        expected: &Core<D>,
        input: D,
        limits: Limits,
        validate_row: impl FnMut(&First<D>) -> bool,
        validate_build: impl FnOnce(&VerifiedRows<S, D>, &OriginBody<S, D>) -> bool,
        strategy: &impl Strategy,
    ) -> Result<VerifiedOrigin<D>, Error> {
        limits.check()?;
        if self.encode_size() > limits.origin_bytes {
            return Err(Error::Limit);
        }
        let rows = self.body.check_rows::<H, R>(
            rng,
            s,
            expected,
            input,
            limits,
            validate_row,
            strategy,
        )?;
        let (decision, body) = self.check_selection::<H, R>(rng, s, expected, limits, strategy)?;
        self.body.finish::<H>(&rows, limits, validate_build)?;
        Ok(VerifiedOrigin {
            slot: expected.slot.id::<H>(),
            decision,
            body,
            origin: self.id::<H>(),
            round: expected.slot.proposal.round,
            leader: expected.leader,
            limits,
        })
    }
}
impl<S: certificate::Scheme, D: Digest> Frame for Origin<S, D> {
    const MAGIC: [u8; 4] = *b"G1E1";
    type Cfg = Limits;
    fn max_bytes(l: &Limits) -> usize {
        l.origin_bytes.min(MAX_EVIDENCE_BYTES)
    }
    fn body_size(&self) -> usize {
        self.body.encode_size() + self.selection.encode_size()
    }
    fn write_body(&self, w: &mut impl BufMut) {
        self.body.write(w);
        self.selection.write(w);
    }
    fn read_body(r: &mut impl Buf, l: &Limits) -> Result<Self, CodecError> {
        Ok(Self {
            body: OriginBody::read_cfg(r, l)?,
            selection: Signed::read_cfg(r, l)?,
        })
    }
}
frame_codec!(Origin<S, D>, [S: certificate::Scheme, D: Digest], Limits);

/// Private-constructor full-origin result, not native P inclusion or delivery.
#[derive(Clone, Debug)]
pub struct VerifiedOrigin<D: Digest> {
    slot: D,
    decision: D,
    body: D,
    origin: D,
    round: Round,
    leader: Participant,
    limits: Limits,
}
impl<D: Digest> VerifiedOrigin<D> {
    /// Exact local field limits under which application meaning was checked.
    pub const fn limits(&self) -> Limits {
        self.limits
    }
    /// Original Slot identity.
    pub const fn slot(&self) -> D {
        self.slot
    }
    /// Semantic decision identity, independent of proof alias.
    pub const fn decision(&self) -> D {
        self.decision
    }
    /// Immutable origin body identity, excluding SELECT.
    pub const fn body(&self) -> D {
        self.body
    }
    /// Complete retained original envelope identity.
    pub const fn origin(&self) -> D {
        self.origin
    }
    /// Original native signing round.
    pub const fn round(&self) -> Round {
        self.round
    }
    /// Original elected leader.
    pub const fn leader(&self) -> Participant {
        self.leader
    }
}

/// A general-q exact-subject phase certificate, not full admission or finality.
#[derive(Clone, Debug)]
pub struct Quorum<S: certificate::Scheme, D: Digest> {
    /// Exact signed phase/carrier/decision.
    pub message: Message<D>,
    /// Native attributable certificate with at least n-f owners.
    pub certificate: S::Certificate,
}
impl<S: scheme::Scheme<D>, D: Digest> Quorum<S, D> {
    /// Assembles only signature-verified, signer-distinct, exact-subject phase votes.
    pub fn from_votes<R: CryptoRng>(
        rng: &mut R,
        s: &S,
        votes: &[Signed<S, D>],
        limits: Limits,
        strategy: &impl Strategy,
    ) -> Result<Self, Error> {
        let c = committee::<S>(&VerificationSource::Scheme(s))?;
        if votes.len() < c.quorum() || votes.len() > c.len() {
            return Err(Error::Quorum);
        }
        let message = &votes[0].message;
        if !message.quorum_phase() {
            return Err(Error::Phase);
        }
        let mut owners = BTreeSet::new();
        for v in votes {
            if v.message != *message || !owners.insert(v.attestation.signer) {
                return Err(Error::Identity);
            }
            if !v.verify(rng, s, limits, strategy) {
                return Err(Error::Signature);
            }
        }
        let mut signatures = votes.iter().map(|v| v.attestation.clone());
        let first = signatures.next().ok_or(Error::Quorum)?;
        let certificate = s
            .assemble(NonEmpty::new(first, signatures), strategy)
            .map_err(|_| Error::Quorum)?;
        let quorum = Self {
            message: message.clone(),
            certificate,
        };
        bounded(&quorum)?;
        if !quorum.verify(rng, s, limits, strategy) {
            return Err(Error::Signature);
        }
        Ok(quorum)
    }
    /// Checks phase certificate crypto and bounds. Caller must additionally match
    /// exact Slot/ballot/leader/decision and verify full phase admission authority.
    /// Recovered-certificate signer uniqueness, current-roster membership and
    /// n-f quorum are delegated to the admitted `simplex::Scheme` verifier's
    /// quorum-authentication contract with its fixed native `N3f1` fault model.
    /// The generic certificate interface exposes no independent signer accessor.
    pub fn verify<R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &S,
        limits: Limits,
        strategy: &impl Strategy,
    ) -> bool {
        self.verify_with(rng, &VerificationSource::Scheme(s), limits, strategy)
    }
    /// Same certificate verification through a captured public-only scope.
    pub fn verify_scoped<R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &Scoped<S>,
        limits: Limits,
        strategy: &impl Strategy,
    ) -> bool {
        self.verify_with(rng, &VerificationSource::Scoped(s), limits, strategy)
    }
    fn verify_with<R: CryptoRng>(
        &self,
        rng: &mut R,
        s: &VerificationSource<'_, S>,
        limits: Limits,
        strategy: &impl Strategy,
    ) -> bool {
        let Ok(c) = committee::<S>(s) else {
            return false;
        };
        if !self.message.quorum_phase()
            || self.message.check(c, limits).is_err()
            || bounded(self).is_err()
        {
            return false;
        }
        let bytes = self.message.signed_bytes();
        s.verify_certificate::<_, D>(
            rng,
            Subject::ExtensionAgreement {
                round: self.message.round,
                payload: &bytes,
            },
            &self.certificate,
            strategy,
        )
    }
}
impl<S: certificate::Scheme, D: Digest> Frame for Quorum<S, D> {
    const MAGIC: [u8; 4] = *b"G1Q1";
    type Cfg = (Limits, <S::Certificate as Read>::Cfg);
    fn body_size(&self) -> usize {
        self.message.encode_size() + native_size(&self.certificate)
    }
    fn write_body(&self, w: &mut impl BufMut) {
        self.message.write(w);
        write_native(&self.certificate, w);
    }
    fn read_body(r: &mut impl Buf, cfg: &Self::Cfg) -> Result<Self, CodecError> {
        let message = Message::read_cfg(r, &cfg.0)?;
        if !message.quorum_phase() {
            return Err(CodecError::Invalid("G1 quorum", "phase"));
        }
        let bytes = read_blob(r, MAX_EVIDENCE_BYTES)?;
        let certificate = <S::Certificate as commonware_codec::Decode>::decode_cfg(bytes, &cfg.1)?;
        Ok(Self {
            message,
            certificate,
        })
    }
}
frame_codec!(Quorum<S, D>, [S: certificate::Scheme, D: Digest], (Limits, <S::Certificate as Read>::Cfg));

commonware_macros::stability_mod!(ALPHA, pub mod entry);
commonware_macros::stability_mod!(ALPHA, pub mod issuance);
commonware_macros::stability_mod!(ALPHA, pub mod normal);
commonware_macros::stability_mod!(ALPHA, pub mod recovery);
