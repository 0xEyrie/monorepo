//! Authenticated, frozen issuance histories for the inactive G1 profile.
//!
//! A notice authenticates one owner's declared complete prefix. Public replay
//! checks that prefix's original choices, exact authorities, outboxes and floors.
//! It cannot prove that a Byzantine owner disclosed every private action. It is
//! not recovery entry, a once-RECOVER reservation, a vote, or native finality.
//! Recovery authorities must come from the bounded closure verifier. This
//! module never recursively verifies graphs or grants recovery entry itself.
//!
//! Capture is memory-only. The native journal owner must retain all referenced
//! material and synchronize the complete prefix before signing or publishing.
//! Network intake, custody reservations and resource configuration remain with
//! that owner. A failed or missing material lookup is an error, never absence.

use super::{Action, HistoryPage, Material, Record, Snapshot, State};
use crate::{
    simplex::extension::agreement::general::{
        self as g, Core, First, Frame, Kind, Limits, Message, OriginBody, Signed,
        VerificationContext, VerifiedRows, read_blob, scheme,
    },
    types::{Participant, Round},
};
use bytes::{Buf as _, BufMut, Bytes};
use commonware_codec::{Buf, EncodeSize, Error as CodecError, Read, ReadExt as _, Write};
use commonware_cryptography::{Digest, Hasher, certificate};
use commonware_parallel::Strategy;
use rand_core::CryptoRng;

/// Declared issuance-history data authenticated by the owner's native signature.
/// Construction or decoding does not grant recovery or signing permission.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Recover<D: Digest> {
    /// Exact trusted original Core identity.
    pub core: D,
    /// Exact immutable public input identity.
    pub input: D,
    /// Caller-authenticated recovery entry identity. This type does not verify it.
    pub entry: D,
    /// Current complete accepted prefix at the already-installed signing floor.
    pub snapshot: Snapshot<D>,
    /// Opaque optional report, not a proof of execution, availability or absence.
    pub report: Option<Bytes>,
}
impl<D: Digest> Recover<D> {
    pub(crate) fn check(&self, c: g::Committee, limits: Limits) -> Result<(), g::Error> {
        limits.check()?;
        if D::SIZE != 32
            || usize::from(self.snapshot.owner) >= c.len()
            || usize::from(self.snapshot.leader) >= c.len()
            || self.snapshot.head.is_none() != (self.snapshot.count == 0)
        {
            return Err(g::Error::Context);
        }
        if self
            .report
            .as_ref()
            .is_some_and(|r| r.len() > limits.report_bytes)
        {
            return Err(g::Error::Limit);
        }
        if self.encode_size() > g::MAX_FIRST_BYTES {
            return Err(g::Error::Limit);
        }
        Ok(())
    }
}
impl<D: Digest> Frame for Recover<D> {
    const MAGIC: [u8; 4] = *b"G1N1";
    const MAX_BYTES: usize = g::MAX_FIRST_BYTES;
    type Cfg = Limits;
    fn body_size(&self) -> usize {
        3 * D::SIZE + self.snapshot.encode_size() + g::option_size(&self.report)
    }
    fn write_body(&self, w: &mut impl BufMut) {
        self.core.write(w);
        self.input.write(w);
        self.entry.write(w);
        self.snapshot.write(w);
        g::write_option(&self.report, w);
    }
    fn read_body(r: &mut impl Buf, limits: &Limits) -> Result<Self, CodecError> {
        limits
            .check()
            .map_err(|_| CodecError::Invalid("G1 history notice", "limits"))?;
        Ok(Self {
            core: D::read(r)?,
            input: D::read(r)?,
            entry: D::read(r)?,
            snapshot: Snapshot::read(r)?,
            report: g::read_option(r, limits.report_bytes)?,
        })
    }
}
frame_codec!(Recover<D>, [D: Digest], Limits);

#[cfg(feature = "arbitrary")]
impl<'a, D: Digest + arbitrary::Arbitrary<'a>> arbitrary::Arbitrary<'a> for Recover<D> {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let head: Option<D> = u.arbitrary()?;
        let count = if head.is_some() {
            u.int_in_range(1..=u64::MAX)?
        } else {
            0
        };
        let report = if u.arbitrary::<bool>()? {
            let len = u.int_in_range(0..=1024usize)?;
            Some(Bytes::copy_from_slice(u.bytes(len)?))
        } else {
            None
        };
        Ok(Self {
            core: u.arbitrary()?,
            input: u.arbitrary()?,
            entry: u.arbitrary()?,
            snapshot: Snapshot {
                slot: u.arbitrary()?,
                owner: Participant::new(u.int_in_range(0..=63)?),
                ballot: u.arbitrary()?,
                leader: Participant::new(u.int_in_range(0..=63)?),
                head,
                count,
            },
            report,
        })
    }
}

/// Finite deployment budget for one complete-prefix verification.
/// A limit failure requires more resources or a different request, never a
/// truncated prefix. Total bytes include the notice, pages and each required
/// exact material occurrence. A terminal consumes two material checks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Bounds {
    /// Maximum complete oldest-first page count.
    pub pages: u32,
    /// Maximum aggregate encoded bytes, counted with checked arithmetic.
    pub encoded_bytes: u64,
    /// Maximum referenced body, origin and certificate validations.
    pub material_checks: u32,
}

/// Rejected history data. No error is evidence of an absent vote or certificate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Error {
    /// A trusted coordinate differs from the signed notice or accepted records.
    #[error("history context mismatch")]
    Context,
    /// The declared prefix is missing, duplicated, reordered or has wrong links.
    #[error("incomplete history chain")]
    Chain,
    /// A frame, aggregate byte budget or validation budget is exceeded.
    #[error("history resource limit")]
    Limit,
    /// A required exact material lookup failed.
    #[error("history material missing")]
    Material,
    /// Structural checks or the owner's native signature failed.
    #[error(transparent)]
    Verification(#[from] g::Error),
    /// Replay failed to reproduce an accepted transition.
    #[error(transparent)]
    Replay(#[from] super::Error),
}

/// Publicly verified declared history, not a recovery-admission capability.
/// The borrowed notice and pages remain the exact authenticated evidence.
/// Missing actions describe only this declared prefix, not Byzantine completeness.
#[derive(Debug)]
pub struct VerifiedHistory<'a, S: certificate::Scheme, D: Digest> {
    core: &'a Core<D>,
    notice: &'a Signed<S, D>,
    pages: &'a [HistoryPage<D>],
}
impl<'a, S: certificate::Scheme, D: Digest> VerifiedHistory<'a, S, D> {
    /// Exact authenticated notice, including its optional raw report.
    pub const fn notice(&self) -> &'a Signed<S, D> {
        self.notice
    }
    /// Captured expected Core, never a peer-selected replacement.
    pub const fn core(&self) -> &'a Core<D> {
        self.core
    }
    const fn recover(&self) -> &Recover<D> {
        let Kind::Recover(recover) = &self.notice.message.kind else {
            unreachable!()
        };
        recover
    }
    /// Exact immutable public input commitment.
    pub const fn input(&self) -> D {
        self.recover().input
    }
    /// Exact caller-authenticated entry commitment.
    pub const fn entry(&self) -> D {
        self.recover().entry
    }
    /// Authenticated remote owner, not the verifier's optional local signer.
    pub const fn owner(&self) -> Participant {
        self.recover().snapshot.owner
    }
    /// Frozen complete prefix claimed in this notice.
    pub const fn snapshot(&self) -> &Snapshot<D> {
        &self.recover().snapshot
    }
    /// Exact oldest-first pages whose transitions were replayed.
    pub const fn pages(&self) -> &'a [HistoryPage<D>] {
        self.pages
    }
    /// Exact records, including unsigned reservations and positive proof receipts.
    /// NoFirst and a signed absent FIRST remain different actions.
    pub fn records(&self) -> impl ExactSizeIterator<Item = &'a Record<D>> + '_ {
        self.pages.iter().map(HistoryPage::record)
    }
}

struct Budget {
    bytes: u64,
    max: u64,
}
impl Budget {
    fn charge(&mut self, bytes: usize) -> Result<(), Error> {
        self.bytes = self
            .bytes
            .checked_add(u64::try_from(bytes).map_err(|_| Error::Limit)?)
            .filter(|total| *total <= self.max)
            .ok_or(Error::Limit)?;
        Ok(())
    }
}

fn preflight_page<D: Digest>(
    page: &HistoryPage<D>,
    c: g::Committee,
    l: Limits,
) -> Result<(), Error> {
    if page.record.core.followers.len() > 63 {
        return Err(Error::Limit);
    }
    match &page.record.action {
        Action::Reserve { message, .. } | Action::AdvanceWish { message, .. } => {
            message.check(c, l)?
        }
        Action::Released { frame, .. } if frame.len() > g::MAX_FIRST_BYTES => {
            return Err(Error::Limit);
        }
        _ => {}
    }
    if page.record.encode_size() > super::MAX_RECORD_BYTES
        || page.encode_size() > <HistoryPage<D> as Frame>::MAX_BYTES
    {
        return Err(Error::Limit);
    }
    Ok(())
}

const fn material_count<D: Digest>(record: &Record<D>) -> u32 {
    match &record.action {
        Action::Reserve {
            message:
                Message {
                    kind:
                        Kind::Select { .. }
                        | Kind::Recover(_)
                        | Kind::Recovery { .. }
                        | Kind::Phase {
                            phase: g::Phase::FastFinal,
                            ..
                        },
                    ..
                },
            ..
        }
        | Action::RetainOrigin { .. }
        | Action::Enter { .. }
        | Action::RetainRpc { .. }
        | Action::RecoveryTerminal { .. } => 1,
        Action::AdvanceWish {
            cause: super::WishCause::Timeout,
            ..
        } => 1,
        Action::AdvanceWish {
            cause: super::WishCause::Amplification(_),
            ..
        } => 2,
        Action::Terminal { .. } => 2,
        _ => 0,
    }
}

/// Verifies one exact declared issuance-history prefix using public keys only.
/// All pages must be supplied oldest first; missing pages/material are errors.
/// The notice signature, context and page budgets are checked before invoking
/// any resolver or application callback. Each required exact material is bounded
/// and charged before identity hashing or replay callbacks. Material is charged
/// on every occurrence, even when two records refer to the same artifact.
///
/// Caller trust supplies the native Core/Input/ballot/leader/entry relationship.
/// This verifies no entry certificate or recovery once-choice, cannot detect
/// undisclosed Byzantine forks, and grants no signer or native P authority.
#[allow(clippy::too_many_arguments)]
pub fn verify<'a, 'm, H, S, D, R>(
    rng: &mut R,
    context: &VerificationContext<S>,
    core: &'a Core<D>,
    input: D,
    ballot: Round,
    leader: Participant,
    entry: D,
    notice: &'a Signed<S, D>,
    pages: &'a [HistoryPage<D>],
    limits: Limits,
    bounds: Bounds,
    mut resolve: impl FnMut(&Record<D>) -> Material<'m, S, D>,
    mut validate_row: impl FnMut(&First<D>) -> bool,
    mut validate_build: impl FnMut(&VerifiedRows<S, D>, &OriginBody<S, D>) -> bool,
    strategy: &impl Strategy,
) -> Result<VerifiedHistory<'a, S, D>, Error>
where
    H: Hasher<Digest = D>,
    S: scheme::Scheme<D>,
    D: Digest,
    R: CryptoRng,
{
    let scheme = context.scheme();
    limits.check()?;
    let c = g::Committee::new(scheme.participants().len())?;
    if core.followers.len() > 63 || pages.len() > bounds.pages as usize || bounds.encoded_bytes == 0
    {
        return Err(Error::Limit);
    }
    notice.message.check(c, limits)?;
    if notice.encode_size() > g::MAX_FIRST_BYTES {
        return Err(Error::Limit);
    }
    let Kind::Recover(recover) = &notice.message.kind else {
        return Err(Error::Context);
    };
    let snapshot = &recover.snapshot;
    if snapshot.count != u64::try_from(pages.len()).map_err(|_| Error::Limit)?
        || snapshot.count == 0
    {
        return Err(Error::Chain);
    }
    let mut budget = Budget {
        bytes: 0,
        max: bounds.encoded_bytes,
    };
    budget.charge(notice.encode_size())?;
    let mut checks = 0u32;
    for page in pages {
        if page.record.core != *core
            || page.record.input != input
            || page.record.owner != snapshot.owner
        {
            return Err(Error::Context);
        }
        preflight_page(page, c, limits)?;
        budget.charge(page.encode_size())?;
        checks = checks
            .checked_add(material_count(&page.record))
            .filter(|n| *n <= bounds.material_checks)
            .ok_or(Error::Limit)?;
    }
    if ballot.epoch() != core.slot.proposal.round.epoch()
        || ballot <= core.slot.proposal.round
        || notice.message.slot != core.slot.id::<H>()
        || notice.message.round != ballot
        || notice.message.leader != leader
        || snapshot.ballot != ballot
        || snapshot.leader != leader
        || recover.core != core.id::<H>()
        || recover.input != input
        || recover.entry != entry
        || snapshot.owner != notice.attestation.signer
    {
        return Err(Error::Context);
    }
    if !notice.verify(rng, scheme, limits, strategy) {
        return Err(g::Error::Signature.into());
    }
    let mut previous = None;
    for page in pages {
        if page.previous != previous {
            return Err(Error::Chain);
        }
        previous = Some(page.id::<H>());
    }
    if previous != snapshot.head {
        return Err(Error::Chain);
    }
    let mut state =
        State::for_history::<H>(context.clone(), core.clone(), input, limits, snapshot.owner)?;
    for page in pages {
        let record = &page.record;
        let material = if material_count(record) == 0 {
            Material::None
        } else {
            resolve(record)
        };
        if !matches!(
            (&record.action, &material),
            (
                Action::Reserve {
                    message: Message {
                        kind: Kind::Select { .. },
                        ..
                    },
                    ..
                },
                Material::Body(_) | Material::RouteBody(_, _)
            ) | (
                Action::Reserve {
                    message: Message {
                        kind: Kind::Phase {
                            phase: g::Phase::FastFinal,
                            ..
                        },
                        ..
                    },
                    ..
                },
                Material::Origin(_)
            ) | (Action::RetainOrigin { .. }, Material::Origin(_))
                | (Action::Terminal { .. }, Material::Terminal { .. })
                | (Action::Enter { .. }, Material::Entry(_))
                | (
                    Action::AdvanceWish {
                        cause: super::WishCause::Timeout,
                        ..
                    },
                    Material::Entry(_)
                )
                | (
                    Action::AdvanceWish {
                        cause: super::WishCause::Amplification(_),
                        ..
                    },
                    Material::Amplification { .. }
                )
                | (
                    Action::Reserve {
                        message: Message {
                            kind: Kind::Recover(_),
                            ..
                        },
                        ..
                    },
                    Material::Entry(_)
                )
                | (
                    Action::Reserve {
                        message: Message {
                            kind: Kind::Recovery { .. },
                            ..
                        },
                        ..
                    },
                    Material::Recovery(_)
                )
                | (
                    Action::RetainRpc { .. } | Action::RecoveryTerminal { .. },
                    Material::Recovery(_)
                )
        ) && material_count(record) != 0
        {
            return Err(Error::Material);
        }
        match &material {
            Material::None if material_count(record) != 0 => return Err(Error::Material),
            Material::None => {}
            Material::Body(body) | Material::RouteBody(body, _) => {
                state.preflight_body(body)?;
                budget.charge(body.encode_size())?;
            }
            Material::Origin(origin) => {
                state.preflight_origin(origin)?;
                budget.charge(origin.encode_size())?;
            }
            Material::Terminal { origin, quorum } => {
                state.preflight_origin(origin)?;
                state.preflight_quorum(quorum)?;
                budget.charge(origin.encode_size())?;
                budget.charge(quorum.encode_size())?;
            }
            Material::Entry(checked) => {
                state.check_entry::<H>(checked)?;
                budget.charge(checked.encoded_size())?;
            }
            Material::Amplification {
                predecessor,
                amplification,
            } => {
                state.check_entry::<H>(predecessor)?;
                state.check_amplification::<H>(predecessor, amplification)?;
                budget.charge(predecessor.encoded_size())?;
                budget.charge(amplification.encoded_size())?;
            }
            Material::Recovery(checked) => {
                state.check_recovery::<H>(checked, checked.role())?;
                budget
                    .charge(usize::try_from(checked.encoded_size()).map_err(|_| Error::Limit)?)?;
            }
        }
        let before = state.records.len();
        state.restore::<H, R>(
            rng,
            record,
            material,
            &mut validate_row,
            &mut validate_build,
            strategy,
        )?;
        if state.records.len() != before + 1 || state.heads.last().copied() != Some(page.id::<H>())
        {
            return Err(Error::Chain);
        }
    }
    let installed = state.snapshot().ok_or(Error::Context)?;
    if state.floor != ballot || installed.ballot != ballot || installed.leader != leader {
        return Err(Error::Context);
    }
    Ok(VerifiedHistory {
        core,
        notice,
        pages,
    })
}
