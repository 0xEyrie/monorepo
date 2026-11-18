//! Local G1 records for the native voter's existing journal, not a storage service.
//!
//! Staging changes memory only. The native owner retains every exact authority,
//! appends and synchronizes each accepted record before signing or publication,
//! and retires the incarnation on storage failure. Native P eligibility and its
//! joint once-choice remain independent caller prerequisites. No Mode is enabled.
//!
//! A local fence only revokes lower signing rights. It is not recovery entry
//! permission and cannot release RECOVER, PREPARE, or COMMIT. A verified entry
//! authenticates proof provenance; the native owner still checks local timeout
//! or amplification permission. WISH advancement atomically reserves its exact
//! subject and raises the lower-signing fence, without installing a target entry.
//! Replay verifies exact referenced material under the captured scheme and restores the complete log
//! before the owner calls `finish_replay`. Historical outbox bytes may still be
//! retransmitted after a fence or interpretation terminal without a signer call.
//! Verified capabilities are local to this state's immutable verification context.
//! After restart, reverify retained raw evidence with the new state's context.

use super::{
    Core, First, Frame, Kind, Limits, Message, Origin, OriginBody, Phase, Quorum, Signed,
    VerificationContext, VerificationSource, VerifiedRows, entry, native_size, read_blob,
    read_native, read_owner, recovery, scheme, write_blob, write_native, write_owner,
};
use crate::{
    Epochable, Viewable,
    types::{Epoch, Participant, Round, View},
};
use bytes::{Buf as _, BufMut, Bytes};
use commonware_codec::{
    Buf, Encode as _, EncodeSize, Error as CodecError, FixedSize as _, Read, ReadExt as _, Write,
};
use commonware_cryptography::{Digest, Hasher, certificate};
use commonware_parallel::Strategy;
use commonware_runtime::Clock;
use rand_core::CryptoRng;
use std::{
    collections::{BTreeMap, BTreeSet},
    time::{Duration, SystemTime},
};

const RECORD: &[u8] = b"_COMMONWARE_CONSENSUS_G1_ISSUANCE_RECORD_V1";
const PAGE: &[u8] = b"_COMMONWARE_CONSENSUS_G1_HISTORY_PAGE_V1";
const TERMINAL: &[u8] = b"_COMMONWARE_CONSENSUS_G1_FAST_TERMINAL_V1";
const MAX_RECORD_BYTES: usize = 2 * super::MAX_FIRST_BYTES;

commonware_macros::stability_mod!(ALPHA, pub mod history);

mod checked;

/// A failed local transition. No error permits discarding accepted journal state.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Error {
    /// Invalid captured context or native carrier coordinates.
    #[error("issuance context mismatch")]
    Context,
    /// A different immutable choice or original authority already exists.
    #[error("issuance choice conflict")]
    Conflict,
    /// A higher local floor prohibits this new lower signing operation.
    #[error("issuance fenced")]
    Floor,
    /// A genuine interpretation terminal has closed local signing.
    #[error("interpretation signing closed")]
    Closed,
    /// Exact retained authority is absent or does not match this record.
    #[error("exact issuance authority missing")]
    Authority,
    /// The exact own unsigned reservation is absent.
    #[error("issuance reservation missing")]
    Reservation,
    /// Retrieve the original outbox instead of invoking a signer again.
    #[error("issuance outbox already recorded")]
    Released,
    /// Replay is incomplete, or restore was called on a live instance.
    #[error("issuance replay state")]
    Replay,
    /// An existing phase or proof requires catch-up instead of a new history row.
    #[error("recovery catch-up required")]
    CatchUp,
    /// The local timer is unarmed, unexpired, zero, or cannot represent a deadline.
    #[error("WISH timeout unavailable")]
    Timeout,
    /// Body, origin, codec bounds, or cryptography failed validation.
    #[error(transparent)]
    Verification(#[from] super::Error),
}

/// Retained local cause of an atomic WISH advance. A timeout is an owner's
/// permission fact, not a portable proof of remote elapsed time or WAL sync.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WishCause<D: Digest> {
    /// The native owner's first immutable local deadline expired.
    Timeout,
    /// Full exact checked f+1 witness, retained with its predecessor closure.
    Amplification(D),
}

/// Immutable local actions. Inspection or decoding does not grant signing rights.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Action<D: Digest> {
    /// Outside-Core native FIRST closure, distinct from a signed absent FIRST.
    NoFirst,
    /// Exact unsigned role and its required retained authority identity.
    Reserve {
        /// Original or per-ballot recovery subject.
        message: Message<D>,
        /// None for FIRST; otherwise the exact entry/body/proposal/RPC artifact.
        authority: Option<D>,
    },
    /// Exact signed outbox, recorded only after its reservation's WAL barrier.
    Released {
        /// Immutable unsigned reservation identity.
        reservation: D,
        /// Exact native signed G1 frame. Never replaced by another signature alias.
        frame: Bytes,
    },
    /// Conservative native-owned local revocation and frozen complete prefix.
    Fence {
        /// All accepted records preceding this floor, including unsigned choices.
        snapshot: Snapshot<D>,
    },
    /// Genuine original q-FAST terminal. This is not native P finality.
    Terminal {
        /// Exact full original authority retained by this local receipt.
        origin: D,
        /// Exact complete original phase certificate artifact identity.
        certificate: D,
        /// Semantic terminal decision, independent of certificate/origin aliases.
        decision: D,
    },
    /// Positive original proof custody, including when this node never voted.
    RetainOrigin {
        /// Exact immutable origin artifact, never replaced by a semantic alias.
        origin: D,
        /// Checked semantic decision of this exact proof.
        decision: D,
    },
    /// Authenticated entry installation, with its exact retained proof artifact.
    Enter {
        /// Complete prefix preceding installation of this floor and permission.
        snapshot: Snapshot<D>,
        /// Semantic entry target, independent of proof aliases.
        entry: D,
        /// Exact entry proof retained by this native owner.
        authority: D,
    },
    /// Positive full RPC custody without a new phase signature.
    RetainRpc {
        /// Exact RPC carrier ballot.
        round: Round,
        /// Exact immutable RPC artifact.
        proof: D,
        /// Shared unsigned proposal body identity.
        proposal: D,
        /// Semantic decision authenticated by the RPC.
        decision: D,
    },
    /// One atomic target-ballot reservation and lower-signing revocation.
    /// The snapshot covers every accepted record BEFORE this reservation.
    AdvanceWish {
        /// Target floor, not an installed target entry or RECOVER permission.
        snapshot: Snapshot<D>,
        /// Exact own retained predecessor remains in Kind::Wish.
        message: Message<D>,
        /// Exact original local cause, never rewritten by retries or aliases.
        cause: WishCause<D>,
    },
    /// Genuine recovery terminal, independent of native P inclusion/finality.
    RecoveryTerminal {
        /// Terminal carrier ballot.
        round: Round,
        /// Exact immutable complete terminal artifact.
        proof: D,
        /// Shared unsigned proposal body identity.
        proposal: D,
        /// Semantic decision fixed by this terminal.
        decision: D,
    },
}

/// A typed item for the existing native voter journal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Record<D: Digest> {
    core: Core<D>,
    input: D,
    owner: Participant,
    action: Action<D>,
}
impl<D: Digest> Record<D> {
    /// Exact record identity in the G1 local-storage domain.
    pub fn id<H: Hasher<Digest = D>>(&self) -> D {
        H::hash(&[RECORD, &self.encode()])
    }
    /// Captured original Slot. Journal retention uses its unresolved original view.
    pub const fn slot(&self) -> &super::Slot<D> {
        &self.core.slot
    }
    /// Captured trusted original Core.
    pub const fn core(&self) -> &Core<D> {
        &self.core
    }
    /// Exact public input commitment.
    pub const fn input(&self) -> D {
        self.input
    }
    /// Native journal owner.
    pub const fn owner(&self) -> Participant {
        self.owner
    }
    /// Immutable action, for retention and replay inspection.
    pub const fn action(&self) -> &Action<D> {
        &self.action
    }
    /// Exact unsigned subject, if this is a reservation.
    pub const fn message(&self) -> Option<&Message<D>> {
        match &self.action {
            Action::Reserve { message, .. } | Action::AdvanceWish { message, .. } => Some(message),
            _ => None,
        }
    }
    /// Exact own reservation/entry authority; aliases never replace it.
    pub const fn authority(&self) -> Option<D> {
        match self.action {
            Action::Reserve { authority, .. } => authority,
            Action::Enter { authority, .. } => Some(authority),
            Action::AdvanceWish {
                message:
                    Message {
                        kind: Kind::Wish(ref wish),
                        ..
                    },
                ..
            } => Some(wish.predecessor),
            _ => None,
        }
    }
}
impl<D: Digest> Epochable for Record<D> {
    fn epoch(&self) -> Epoch {
        self.core.slot.proposal.round.epoch()
    }
}
impl<D: Digest> Viewable for Record<D> {
    fn view(&self) -> View {
        self.core.slot.proposal.round.view()
    }
}
impl<D: Digest> Frame for Record<D> {
    const MAGIC: [u8; 4] = *b"G1J1";
    const MAX_BYTES: usize = MAX_RECORD_BYTES;
    type Cfg = Limits;
    fn body_size(&self) -> usize {
        self.core.encode_size()
            + D::SIZE
            + 5
            + match &self.action {
                Action::NoFirst => 0,
                Action::Reserve { message, authority } => {
                    message.encode_size() + 1 + authority.map_or(0, |_| D::SIZE)
                }
                Action::Released { frame, .. } => D::SIZE + 4 + frame.len(),
                Action::Fence { snapshot } => snapshot.encode_size(),
                Action::AdvanceWish {
                    snapshot,
                    message,
                    cause,
                } => {
                    snapshot.encode_size()
                        + message.encode_size()
                        + 1
                        + if matches!(cause, WishCause::Amplification(_)) {
                            D::SIZE
                        } else {
                            0
                        }
                }
                Action::Terminal { .. } => 3 * D::SIZE,
                Action::RetainOrigin { .. } => 2 * D::SIZE,
                Action::Enter { snapshot, .. } => snapshot.encode_size() + 2 * D::SIZE,
                Action::RetainRpc { round, .. } | Action::RecoveryTerminal { round, .. } => {
                    native_size(round) + 3 * D::SIZE
                }
            }
    }
    fn write_body(&self, w: &mut impl BufMut) {
        self.core.write(w);
        self.input.write(w);
        write_owner(self.owner, w);
        match &self.action {
            Action::NoFirst => 0u8.write(w),
            Action::Reserve { message, authority } => {
                1u8.write(w);
                message.write(w);
                authority.write(w);
            }
            Action::Released { reservation, frame } => {
                2u8.write(w);
                reservation.write(w);
                write_blob(frame, w);
            }
            Action::Fence { snapshot } => {
                3u8.write(w);
                snapshot.write(w);
            }
            Action::AdvanceWish {
                snapshot,
                message,
                cause,
            } => {
                9u8.write(w);
                snapshot.write(w);
                message.write(w);
                match cause {
                    WishCause::Timeout => 0u8.write(w),
                    WishCause::Amplification(id) => {
                        1u8.write(w);
                        id.write(w);
                    }
                }
            }
            Action::Terminal {
                origin,
                certificate,
                decision,
            } => {
                4u8.write(w);
                origin.write(w);
                certificate.write(w);
                decision.write(w);
            }
            Action::RetainOrigin { origin, decision } => {
                5u8.write(w);
                origin.write(w);
                decision.write(w);
            }
            Action::Enter {
                snapshot,
                entry,
                authority,
            } => {
                6u8.write(w);
                snapshot.write(w);
                entry.write(w);
                authority.write(w);
            }
            Action::RetainRpc {
                round,
                proof,
                proposal,
                decision,
            }
            | Action::RecoveryTerminal {
                round,
                proof,
                proposal,
                decision,
            } => {
                if matches!(self.action, Action::RetainRpc { .. }) {
                    7u8
                } else {
                    8u8
                }
                .write(w);
                write_native(round, w);
                proof.write(w);
                proposal.write(w);
                decision.write(w);
            }
        }
    }
    fn read_body(r: &mut impl Buf, limits: &Limits) -> Result<Self, CodecError> {
        limits
            .check()
            .map_err(|_| CodecError::Invalid("G1 record", "limits"))?;
        let core = Core::read(r)?;
        let input = D::read(r)?;
        let owner = read_owner(r)?;
        let action = match u8::read(r)? {
            0 => Action::NoFirst,
            1 => Action::Reserve {
                message: Message::read_cfg(r, limits)?,
                authority: Option::<D>::read(r)?,
            },
            2 => Action::Released {
                reservation: D::read(r)?,
                frame: read_blob(r, super::MAX_FIRST_BYTES)?,
            },
            3 => Action::Fence {
                snapshot: Snapshot::read(r)?,
            },
            4 => Action::Terminal {
                origin: D::read(r)?,
                certificate: D::read(r)?,
                decision: D::read(r)?,
            },
            5 => Action::RetainOrigin {
                origin: D::read(r)?,
                decision: D::read(r)?,
            },
            6 => Action::Enter {
                snapshot: Snapshot::read(r)?,
                entry: D::read(r)?,
                authority: D::read(r)?,
            },
            tag @ 7..=8 => {
                let round = read_native(r)?;
                let proof = D::read(r)?;
                let proposal = D::read(r)?;
                let decision = D::read(r)?;
                if tag == 7 {
                    Action::RetainRpc {
                        round,
                        proof,
                        proposal,
                        decision,
                    }
                } else {
                    Action::RecoveryTerminal {
                        round,
                        proof,
                        proposal,
                        decision,
                    }
                }
            }
            9 => {
                let snapshot = Snapshot::read(r)?;
                let message = Message::read_cfg(r, limits)?;
                if !matches!(message.kind, Kind::Wish(_)) {
                    return Err(CodecError::Invalid("G1 record", "WISH role"));
                }
                let cause = match u8::read(r)? {
                    0 => WishCause::Timeout,
                    1 => WishCause::Amplification(D::read(r)?),
                    _ => return Err(CodecError::Invalid("G1 record", "WISH cause")),
                };
                Action::AdvanceWish {
                    snapshot,
                    message,
                    cause,
                }
            }
            _ => return Err(CodecError::Invalid("G1 record", "action")),
        };
        Ok(Self {
            core,
            input,
            owner,
            action,
        })
    }
}
frame_codec!(Record<D>, [D: Digest], Limits);

/// A frozen local prefix at one conservative signing floor.
/// A Fence retains the prefix before installation. A history notice captures the
/// current prefix at that floor, without rewriting the older Fence snapshot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Snapshot<D: Digest> {
    slot: D,
    owner: Participant,
    ballot: Round,
    leader: Participant,
    head: Option<D>,
    count: u64,
}
impl<D: Digest> Snapshot<D> {
    /// Original Slot identity.
    pub const fn slot(&self) -> D {
        self.slot
    }
    /// Original local history owner.
    pub const fn owner(&self) -> Participant {
        self.owner
    }
    /// Installed local signing floor.
    pub const fn ballot(&self) -> Round {
        self.ballot
    }
    /// Native-owner supplied carrier leader, not an election proof.
    pub const fn leader(&self) -> Participant {
        self.leader
    }
    /// Exact last page of the frozen prefix, or none for an empty prefix.
    pub const fn head(&self) -> Option<D> {
        self.head
    }
    /// Number of pages in this immutable prefix.
    pub const fn count(&self) -> u64 {
        self.count
    }
}
impl<D: Digest> Frame for Snapshot<D> {
    const MAGIC: [u8; 4] = *b"G1L1";
    type Cfg = ();
    fn body_size(&self) -> usize {
        D::SIZE
            + 4
            + super::native_size(&self.ballot)
            + 4
            + 1
            + self.head.map_or(0, |_| D::SIZE)
            + 8
    }
    fn write_body(&self, w: &mut impl BufMut) {
        self.slot.write(w);
        write_owner(self.owner, w);
        write_native(&self.ballot, w);
        write_owner(self.leader, w);
        self.head.write(w);
        self.count.write(w);
    }
    fn read_body(r: &mut impl Buf, _: &()) -> Result<Self, CodecError> {
        let value = Self {
            slot: D::read(r)?,
            owner: read_owner(r)?,
            ballot: read_native(r)?,
            leader: read_owner(r)?,
            head: Option::<D>::read(r)?,
            count: u64::read(r)?,
        };
        if value.head.is_none() != (value.count == 0) {
            return Err(CodecError::Invalid("G1 snapshot", "empty prefix"));
        }
        Ok(value)
    }
}
frame_codec!(Snapshot<D>, [D: Digest], ());

/// One content-addressed history page. Fetching does not require a whole-history allocation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HistoryPage<D: Digest> {
    previous: Option<D>,
    record: Record<D>,
}
impl<D: Digest> HistoryPage<D> {
    /// Exact page identity; links commit to the complete preceding prefix.
    pub fn id<H: Hasher<Digest = D>>(&self) -> D {
        H::hash(&[PAGE, &self.encode()])
    }
    /// Previous accepted local page.
    pub const fn previous(&self) -> Option<D> {
        self.previous
    }
    /// Exact accepted item, including an unsigned reservation or signed outbox.
    pub const fn record(&self) -> &Record<D> {
        &self.record
    }
}
impl<D: Digest> Frame for HistoryPage<D> {
    const MAGIC: [u8; 4] = *b"G1H1";
    const MAX_BYTES: usize = MAX_RECORD_BYTES + 64;
    type Cfg = Limits;
    fn body_size(&self) -> usize {
        1 + self.previous.map_or(0, |_| D::SIZE) + self.record.encode_size()
    }
    fn write_body(&self, w: &mut impl BufMut) {
        self.previous.write(w);
        self.record.write(w);
    }
    fn read_body(r: &mut impl Buf, limits: &Limits) -> Result<Self, CodecError> {
        Ok(Self {
            previous: Option::<D>::read(r)?,
            record: Record::read_cfg(r, limits)?,
        })
    }
}
frame_codec!(HistoryPage<D>, [D: Digest], Limits);

/// Exact referenced replay material. None never substitutes for a missing authority.
pub enum Material<'a, S: certificate::Scheme, D: Digest> {
    /// No authority is needed for this record, or required material is missing.
    None,
    /// Original pre-SELECT body.
    Body(&'a OriginBody<S, D>),
    /// Complete original fast origin.
    Origin(&'a Origin<S, D>),
    /// Complete original fast origin and genuine original q-FAST certificate.
    Terminal {
        origin: &'a Origin<S, D>,
        quorum: &'a Quorum<S, D>,
    },
    /// Exact entry proof, already checked by the bounded entry verifier.
    Entry(&'a entry::VerifiedEntry<'a, S, D>),
    /// Own exact predecessor and exact checked f+1 cause of a WISH reservation.
    Amplification {
        /// Own installed artifact A, not a peer's same-semantic alias B.
        predecessor: &'a entry::VerifiedEntry<'a, S, D>,
        /// Full checked f+1 root retained with the accepted record.
        amplification: &'a entry::VerifiedAmplification<'a, S, D>,
    },
    /// Exact recovery authority, already checked by the bounded closure verifier.
    Recovery(&'a recovery::Verified<D>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Step {
    First,
    Select,
    Final,
    Recover(Round),
    Wish(Round),
    Propose(Round),
    Prepare(Round),
    Commit(Round),
}

/// Native-owned local state. Its accepted records must use the native journal.
/// History has no silent truncation or GC: retention belongs to the native owner.
pub struct State<S: certificate::Scheme, D: Digest> {
    context: VerificationContext<S>,
    core: Core<D>,
    input: D,
    limits: Limits,
    owner: Participant,
    floor: Round,
    replaying: bool,
    verification_only: bool,
    records: Vec<Record<D>>,
    heads: Vec<D>,
    ids: BTreeSet<D>,
    choices: BTreeMap<Step, usize>,
    outboxes: BTreeMap<Step, usize>,
    // The native owner journals the whole pair, not only the G1 signed half.
    normal_outbox: Option<super::normal::Released<S, D>>,
    entries: BTreeMap<Round, usize>,
    rpcs: BTreeMap<Round, Vec<usize>>,
    // Local timers are deliberately not reconstructed from WAL timestamps.
    wish_deadlines: BTreeMap<Round, SystemTime>,
    fence: Option<usize>,
    terminal: Option<usize>,
}
impl<S: scheme::Scheme<D>, D: Digest> State<S, D> {
    /// Starts a fresh local slot after native P/Core/Input admission and an empty
    /// journal check. For an existing journal use `for_replay`, never this path.
    pub fn new<H: Hasher<Digest = D>>(
        scheme: S,
        core: Core<D>,
        input: D,
        limits: Limits,
    ) -> Result<Self, Error> {
        core.check::<H, S>(&VerificationSource::Scheme(&scheme))?;
        limits.validate::<S, D>(&core)?;
        let owner = scheme.me().ok_or(Error::Context)?;
        if usize::from(owner) >= scheme.participants().len() {
            return Err(Error::Context);
        }
        Ok(Self {
            owner,
            floor: core.slot.proposal.round,
            context: VerificationContext::new(scheme),
            core,
            input,
            limits,
            replaying: false,
            verification_only: false,
            records: Vec::new(),
            heads: Vec::new(),
            ids: BTreeSet::new(),
            choices: BTreeMap::new(),
            outboxes: BTreeMap::new(),
            normal_outbox: None,
            entries: BTreeMap::new(),
            rpcs: BTreeMap::new(),
            wish_deadlines: BTreeMap::new(),
            fence: None,
            terminal: None,
        })
    }
    /// Starts with all staging/signing disabled until the native owner has replayed
    /// its complete journal and exact retained material and calls `finish_replay`.
    pub fn for_replay<H: Hasher<Digest = D>>(
        scheme: S,
        core: Core<D>,
        input: D,
        limits: Limits,
    ) -> Result<Self, Error> {
        let mut state = Self::new::<H>(scheme, core, input, limits)?;
        state.replaying = true;
        Ok(state)
    }
    // This state is confined to public verification. It never needs scheme.me(),
    // cannot finish replay, and is dropped without exposing its signer surface.
    fn for_history<H: Hasher<Digest = D>>(
        context: VerificationContext<S>,
        core: Core<D>,
        input: D,
        limits: Limits,
        owner: Participant,
    ) -> Result<Self, Error> {
        core.check::<H, S>(&VerificationSource::Scheme(context.scheme()))?;
        limits.validate::<S, D>(&core)?;
        if usize::from(owner) >= context.scheme().participants().len() {
            return Err(Error::Context);
        }
        Ok(Self {
            owner,
            floor: core.slot.proposal.round,
            context,
            core,
            input,
            limits,
            replaying: true,
            verification_only: true,
            records: Vec::new(),
            heads: Vec::new(),
            ids: BTreeSet::new(),
            choices: BTreeMap::new(),
            outboxes: BTreeMap::new(),
            normal_outbox: None,
            entries: BTreeMap::new(),
            rpcs: BTreeMap::new(),
            wish_deadlines: BTreeMap::new(),
            fence: None,
            terminal: None,
        })
    }

    /// Captures the CURRENT prefix at the exact installed higher floor.
    /// This neither mutates the old Fence snapshot nor stages a RECOVER choice.
    /// It is not durable, once-only, entry permission or finality. Synchronize
    /// and retain the full prefix before the owner's crypto-only Signed::sign.
    /// Terminal, replay, stale and future-floor requests are rejected.
    pub fn capture_history<H: Hasher<Digest = D>>(
        &self,
        ballot: Round,
        leader: Participant,
        entry: D,
        report: Option<Bytes>,
    ) -> Result<Message<D>, Error> {
        self.active()?;
        self.history_message::<H>(ballot, leader, entry, report)
    }
    fn history_message<H: Hasher<Digest = D>>(
        &self,
        ballot: Round,
        leader: Participant,
        entry: D,
        report: Option<Bytes>,
    ) -> Result<Message<D>, Error> {
        if self.terminal.is_some() {
            return Err(Error::Closed);
        }
        let installed = self.snapshot().ok_or(Error::Floor)?;
        if ballot != self.floor || ballot != installed.ballot || leader != installed.leader {
            return Err(Error::Context);
        }
        if report
            .as_ref()
            .is_some_and(|r| r.len() > self.limits.report_bytes)
        {
            return Err(super::Error::Limit.into());
        }
        let message = Message {
            slot: installed.slot,
            round: ballot,
            leader,
            kind: Kind::Recover(history::Recover {
                core: self.core.id::<H>(),
                input: self.input,
                entry,
                snapshot: Snapshot {
                    slot: installed.slot,
                    owner: self.owner,
                    ballot,
                    leader,
                    head: self.heads.last().copied(),
                    count: u64::try_from(self.records.len()).map_err(|_| Error::Context)?,
                },
                report,
            }),
        };
        message.check(
            super::Committee::new(self.context.scheme().participants().len())?,
            self.limits,
        )?;
        if 8 + message.encode_size() + 4 + self.owner.encode_size() + S::Signature::SIZE
            > super::MAX_FIRST_BYTES
        {
            return Err(super::Error::Limit.into());
        }
        Ok(message)
    }

    fn check_entry<H: Hasher<Digest = D>>(
        &self,
        checked: &entry::VerifiedEntry<'_, S, D>,
    ) -> Result<(), Error> {
        let target = checked.target();
        if !checked.matches_context(&self.context)
            || checked.core() != &self.core
            || target.core != self.core.id::<H>()
            || target.input != self.input
            || checked.limits() != self.limits
            || checked.encoded_size() > super::MAX_EVIDENCE_BYTES
            || target.ballot.epoch() != self.core.slot.proposal.round.epoch()
            || target.ballot <= self.core.slot.proposal.round
            || usize::from(target.leader) >= self.context.scheme().participants().len()
        {
            return Err(Error::Context);
        }
        Ok(())
    }
    fn entered(&self, ballot: Round, leader: Participant, entry: D) -> Result<D, Error> {
        let i = self.entries.get(&ballot).ok_or(Error::Authority)?;
        let Action::Enter {
            snapshot,
            entry: old,
            authority,
        } = &self.records[*i].action
        else {
            unreachable!()
        };
        if snapshot.ballot != ballot || snapshot.leader != leader || *old != entry {
            return Err(Error::Context);
        }
        Ok(*authority)
    }
    fn entry_record<H: Hasher<Digest = D>>(
        &self,
        checked: &entry::VerifiedEntry<'_, S, D>,
    ) -> Result<Record<D>, Error> {
        self.check_entry::<H>(checked)?;
        let target = checked.target();
        if let Some(i) = self.entries.get(&target.ballot) {
            self.entered(target.ballot, target.leader, checked.id())?;
            return Ok(self.records[*i].clone());
        }
        if self.terminal.is_some() {
            return Err(Error::Closed);
        }
        if target.ballot < self.floor {
            return Err(Error::Floor);
        }
        if target.ballot == self.floor && self.snapshot().is_some_and(|s| s.leader != target.leader)
        {
            return Err(Error::Conflict);
        }
        Ok(self.record(Action::Enter {
            snapshot: Snapshot {
                slot: self.core.slot.id::<H>(),
                owner: self.owner,
                ballot: target.ballot,
                leader: target.leader,
                head: self.heads.last().copied(),
                count: u64::try_from(self.records.len()).map_err(|_| Error::Context)?,
            },
            entry: checked.id(),
            authority: checked.artifact_id(),
        }))
    }
    /// Installs authenticated entry in the existing journal. Staging is not sync
    /// or proof of the native owner's local deadline/amplification permission.
    /// A matching proof alias returns the original exact entry reservation.
    pub fn enter<H: Hasher<Digest = D>>(
        &mut self,
        checked: &entry::VerifiedEntry<'_, S, D>,
    ) -> Result<Record<D>, Error> {
        self.active()?;
        let record = self.entry_record::<H>(checked)?;
        Ok(self.commit::<H>(record))
    }
    fn wish_target<H: Hasher<Digest = D>>(
        &self,
        predecessor: &entry::VerifiedEntry<'_, S, D>,
    ) -> Result<(entry::Target<D>, D), Error> {
        self.check_entry::<H>(predecessor)?;
        let previous = predecessor.target();
        let own = self.entered(previous.ballot, previous.leader, predecessor.id())?;
        let c = super::Committee::new(self.context.scheme().participants().len())?;
        let target = previous.successor(c).map_err(|_| Error::Context)?;
        Ok((target, own))
    }
    fn check_amplification<H: Hasher<Digest = D>>(
        &self,
        predecessor: &entry::VerifiedEntry<'_, S, D>,
        amplification: &entry::VerifiedAmplification<'_, S, D>,
    ) -> Result<(), Error> {
        let (target, _) = self.wish_target::<H>(predecessor)?;
        if !amplification.matches_context(&self.context)
            || amplification.core() != &self.core
            || amplification.limits() != self.limits
            || amplification.encoded_size() > super::MAX_EVIDENCE_BYTES
            || amplification.target() != &target
        {
            return Err(Error::Context);
        }
        Ok(())
    }
    fn wish_record<H: Hasher<Digest = D>>(
        &self,
        predecessor: &entry::VerifiedEntry<'_, S, D>,
        cause: WishCause<D>,
    ) -> Result<Record<D>, Error> {
        let (target, own) = self.wish_target::<H>(predecessor)?;
        if let Some(old) = self.old(Step::Wish(target.ballot)) {
            return if matches!(old.message(), Some(Message { kind: Kind::Wish(w), .. })
                if w.target == target && w.predecessor == own)
            {
                Ok(old.clone())
            } else {
                Err(Error::Conflict)
            };
        }
        if predecessor.artifact_id() != own {
            return Err(Error::Authority);
        }
        if self.terminal.is_some() {
            return Err(Error::Closed);
        }
        if self.floor != predecessor.target().ballot {
            return Err(Error::Floor);
        }
        let message = Message {
            slot: self.core.slot.id::<H>(),
            round: target.ballot,
            leader: target.leader,
            kind: Kind::Wish(entry::Wish {
                target: target.clone(),
                predecessor: own,
            }),
        };
        self.check_known_rpc(&message)?;
        Ok(self.record(Action::AdvanceWish {
            snapshot: Snapshot {
                slot: message.slot,
                owner: self.owner,
                ballot: target.ballot,
                leader: target.leader,
                head: self.heads.last().copied(),
                count: u64::try_from(self.records.len()).map_err(|_| Error::Context)?,
            },
            message,
            cause,
        }))
    }
    /// Arms the first immutable local deadline from an exact installed predecessor.
    /// The native owner MUST synchronize its Enter and custody before this call.
    /// This method does not assert that memory staging proves a WAL barrier.
    /// Alias retries cannot extend the deadline. Restart has no elapsed authority:
    /// an unreserved timer must be armed anew for the full trusted profile wait.
    pub fn arm_wish_timeout<H: Hasher<Digest = D>>(
        &mut self,
        clock: &impl Clock,
        predecessor: &entry::VerifiedEntry<'_, S, D>,
        wait: Duration,
    ) -> Result<SystemTime, Error> {
        self.active()?;
        let (target, own) = self.wish_target::<H>(predecessor)?;
        if self.terminal.is_some() {
            return Err(Error::Closed);
        }
        if self.floor != predecessor.target().ballot {
            return Err(Error::Floor);
        }
        if predecessor.artifact_id() != own {
            return Err(Error::Authority);
        }
        self.check_known_rpc(&Message {
            slot: self.core.slot.id::<H>(),
            round: target.ballot,
            leader: target.leader,
            kind: Kind::Wish(entry::Wish {
                target,
                predecessor: own,
            }),
        })?;
        if wait.is_zero() {
            return Err(Error::Timeout);
        }
        if let Some(deadline) = self.wish_deadlines.get(&predecessor.target().ballot) {
            return Ok(*deadline);
        }
        let deadline = clock.current().checked_add(wait).ok_or(Error::Timeout)?;
        self.wish_deadlines
            .insert(predecessor.target().ballot, deadline);
        Ok(deadline)
    }
    /// Atomically reserves the exact once-WISH and raises the lower-signing floor.
    /// The configured wait is a native activation prerequisite, not a general
    /// progress theorem. Sync the accepted record before sign_reserved/outbox.
    pub fn reserve_timeout_wish<H: Hasher<Digest = D>>(
        &mut self,
        clock: &impl Clock,
        predecessor: &entry::VerifiedEntry<'_, S, D>,
    ) -> Result<Record<D>, Error> {
        self.active()?;
        let (target, _) = self.wish_target::<H>(predecessor)?;
        if self.old(Step::Wish(target.ballot)).is_none() {
            let deadline = self
                .wish_deadlines
                .get(&predecessor.target().ballot)
                .ok_or(Error::Timeout)?;
            if clock.current() < *deadline {
                return Err(Error::Timeout);
            }
        }
        let record = self.wish_record::<H>(predecessor, WishCause::Timeout)?;
        Ok(self.commit::<H>(record))
    }
    /// Atomically advances from an installed predecessor after checked f+1
    /// amplification. The exact cause and own A are retained; peer aliases do
    /// not replace them. This grants no target entry or RECOVER permission.
    pub fn reserve_amplified_wish<H: Hasher<Digest = D>>(
        &mut self,
        predecessor: &entry::VerifiedEntry<'_, S, D>,
        amplification: &entry::VerifiedAmplification<'_, S, D>,
    ) -> Result<Record<D>, Error> {
        self.active()?;
        self.check_amplification::<H>(predecessor, amplification)?;
        let record = self.wish_record::<H>(
            predecessor,
            WishCause::Amplification(amplification.artifact_id()),
        )?;
        Ok(self.commit::<H>(record))
    }

    fn recover<H: Hasher<Digest = D>>(
        &self,
        checked: &entry::VerifiedEntry<'_, S, D>,
        report: Option<Bytes>,
    ) -> Result<Record<D>, Error> {
        self.check_entry::<H>(checked)?;
        let target = checked.target();
        let authority = self.entered(target.ballot, target.leader, checked.id())?;
        if let Some(old) = self.old(Step::Recover(target.ballot)) {
            let Some(Message {
                kind: Kind::Recover(row),
                ..
            }) = old.message()
            else {
                unreachable!()
            };
            return if row.entry == checked.id() && row.report == report {
                Ok(old.clone())
            } else {
                Err(Error::Conflict)
            };
        }
        if self.terminal.is_some() {
            return Err(Error::Closed);
        }
        if self.floor != target.ballot {
            return Err(Error::Floor);
        }
        if self.rpcs.range(target.ballot..).next().is_some()
            || [
                Step::Propose(target.ballot),
                Step::Prepare(target.ballot),
                Step::Commit(target.ballot),
            ]
            .into_iter()
            .any(|role| self.old(role).is_some())
        {
            return Err(Error::CatchUp);
        }
        let message =
            self.history_message::<H>(target.ballot, target.leader, checked.id(), report)?;
        Ok(self.record(Action::Reserve {
            message,
            authority: Some(authority),
        }))
    }
    /// Freezes one complete prefix before its own RECOVER reservation. Optional
    /// report preparation never waits here; later retries preserve the old row.
    pub fn reserve_recover<H: Hasher<Digest = D>>(
        &mut self,
        checked: &entry::VerifiedEntry<'_, S, D>,
        report: Option<Bytes>,
    ) -> Result<Record<D>, Error> {
        self.active()?;
        let record = self.recover::<H>(checked, report)?;
        Ok(self.commit::<H>(record))
    }
    fn check_recovery<H: Hasher<Digest = D>>(
        &self,
        checked: &recovery::Verified<D>,
        role: recovery::Role,
    ) -> Result<(), Error> {
        if !checked.matches_context(&self.context)
            || checked.role() != role
            || checked.limits() != self.limits
            || checked.encoded_size() > recovery::MAX_MATERIAL_BYTES as u64
            || checked.slot() != self.core.slot.id::<H>()
            || checked.core() != self.core.id::<H>()
            || checked.input() != self.input
            || checked.value().slot != self.core.slot
            || checked.value().input != self.input
            || checked.value().id::<H>() != checked.decision()
            || checked.round().epoch() != self.core.slot.proposal.round.epoch()
            || checked.round() <= self.core.slot.proposal.round
            || usize::from(checked.leader()) >= self.context.scheme().participants().len()
        {
            return Err(Error::Context);
        }
        Ok(())
    }
    fn recovery_record<H: Hasher<Digest = D>>(
        &self,
        checked: &recovery::Verified<D>,
        phase: recovery::Phase,
    ) -> Result<Record<D>, Error> {
        let role = match phase {
            recovery::Phase::Propose => recovery::Role::Admission,
            recovery::Phase::Prepare => recovery::Role::Proposal,
            recovery::Phase::Commit => recovery::Role::Rpc,
        };
        self.check_recovery::<H>(checked, role)?;
        let message = Message {
            slot: checked.slot(),
            round: checked.round(),
            leader: checked.leader(),
            kind: Kind::Recovery {
                phase,
                subject: recovery::Subject {
                    core: checked.core(),
                    input: checked.input(),
                    entry: checked.entry(),
                    proposal: checked.proposal(),
                    decision: checked.decision(),
                },
            },
        };
        let key = step(&message).ok_or(Error::Context)?;
        if let Some(old) = self.old(key) {
            return if old.message() == Some(&message) {
                Ok(old.clone())
            } else {
                Err(Error::Conflict)
            };
        }
        if self.terminal.is_some() {
            return Err(Error::Closed);
        }
        if self.floor != checked.round() {
            return Err(Error::Floor);
        }
        self.entered(checked.round(), checked.leader(), checked.entry())?;
        self.check_known_rpc(&message)?;
        if phase == recovery::Phase::Propose && self.owner != checked.leader() {
            return Err(Error::Context);
        }
        message.check(
            super::Committee::new(self.context.scheme().participants().len())?,
            self.limits,
        )?;
        Ok(self.record(Action::Reserve {
            message,
            authority: Some(checked.evidence()),
        }))
    }
    /// Reserves the coordinator's exact unsigned admitted proposal body.
    pub fn reserve_propose<H: Hasher<Digest = D>>(
        &mut self,
        checked: &recovery::Verified<D>,
    ) -> Result<Record<D>, Error> {
        self.active()?;
        let record = self.recovery_record::<H>(checked, recovery::Phase::Propose)?;
        Ok(self.commit::<H>(record))
    }
    /// Reserves PREPARE only after the complete signed proposal was verified.
    pub fn reserve_prepare<H: Hasher<Digest = D>>(
        &mut self,
        checked: &recovery::Verified<D>,
    ) -> Result<Record<D>, Error> {
        self.active()?;
        let record = self.recovery_record::<H>(checked, recovery::Phase::Prepare)?;
        Ok(self.commit::<H>(record))
    }
    /// Reserves COMMIT only with a complete RPC. A matching alias never replaces
    /// this owner's exact original authority or creates another signer choice.
    pub fn reserve_commit<H: Hasher<Digest = D>>(
        &mut self,
        checked: &recovery::Verified<D>,
    ) -> Result<Record<D>, Error> {
        self.active()?;
        let record = self.recovery_record::<H>(checked, recovery::Phase::Commit)?;
        Ok(self.commit::<H>(record))
    }
    /// Validate both records before advancing the ledger. The actor writes these
    /// together before publishing COMMIT, including an exact repeat after restart.
    #[cfg(not(target_arch = "wasm32"))]
    pub(crate) fn reserve_rpc_commit<H: Hasher<Digest = D>>(
        &mut self,
        checked: &recovery::Verified<D>,
    ) -> Result<(Record<D>, Record<D>), Error> {
        self.active()?;
        let vote = self.recovery_record::<H>(checked, recovery::Phase::Commit)?;
        if vote.authority() != Some(checked.evidence()) {
            return Err(Error::Authority);
        }
        let rpc = self.rpc_record::<H>(checked)?;
        Ok((self.commit::<H>(rpc), self.commit::<H>(vote)))
    }
    fn rpc_record<H: Hasher<Digest = D>>(
        &self,
        checked: &recovery::Verified<D>,
    ) -> Result<Record<D>, Error> {
        self.check_recovery::<H>(checked, recovery::Role::Rpc)?;
        Ok(self.record(Action::RetainRpc {
            round: checked.round(),
            proof: checked.evidence(),
            proposal: checked.proposal(),
            decision: checked.decision(),
        }))
    }
    /// Retains exact positive RPC material, including after a higher floor.
    /// The owner reserves custody and journal capacity before accepting it.
    pub fn retain_rpc<H: Hasher<Digest = D>>(
        &mut self,
        checked: &recovery::Verified<D>,
    ) -> Result<Record<D>, Error> {
        self.active()?;
        let record = self.rpc_record::<H>(checked)?;
        Ok(self.commit::<H>(record))
    }
    fn terminal_decision(&self) -> Option<D> {
        match self.records.get(self.terminal?)?.action {
            Action::Terminal { decision, .. } | Action::RecoveryTerminal { decision, .. } => {
                Some(decision)
            }
            _ => unreachable!(),
        }
    }
    fn recovery_terminal_record<H: Hasher<Digest = D>>(
        &self,
        checked: &recovery::Verified<D>,
    ) -> Result<Record<D>, Error> {
        self.check_recovery::<H>(checked, recovery::Role::Terminal)?;
        if let Some(decision) = self.terminal_decision() {
            return if decision == checked.decision() {
                Ok(self.records[self.terminal.unwrap()].clone())
            } else {
                Err(Error::Conflict)
            };
        }
        Ok(self.record(Action::RecoveryTerminal {
            round: checked.round(),
            proof: checked.evidence(),
            proposal: checked.proposal(),
            decision: checked.decision(),
        }))
    }
    /// Installs an interpretation terminal, never native P inclusion or an ACK.
    pub fn terminal_recovery<H: Hasher<Digest = D>>(
        &mut self,
        checked: &recovery::Verified<D>,
    ) -> Result<Record<D>, Error> {
        self.active()?;
        let record = self.recovery_terminal_record::<H>(checked)?;
        Ok(self.commit::<H>(record))
    }

    /// The native journal owner asserts end-of-log completeness. This is not a
    /// storage sync receipt; failure/loss requires retiring the incarnation.
    pub const fn finish_replay(&mut self) -> Result<(), Error> {
        if !self.replaying || self.verification_only {
            return Err(Error::Replay);
        }
        self.replaying = false;
        Ok(())
    }
    /// Captured original Core.
    pub const fn core(&self) -> &Core<D> {
        &self.core
    }
    /// Captured public input identity.
    pub const fn input(&self) -> D {
        self.input
    }
    /// Local native signer identity.
    pub const fn owner(&self) -> Participant {
        self.owner
    }
    /// Opaque read-only verification scope for this exact local state. Tokens
    /// verified under another context cannot authorize this state's transitions.
    pub fn verification_context(&self) -> VerificationContext<S> {
        self.context.clone()
    }
    /// Current conservative signing floor.
    pub const fn floor(&self) -> Round {
        self.floor
    }
    /// Accepted logical records, including unsigned reservations.
    pub fn records(&self) -> &[Record<D>] {
        &self.records
    }
    /// Latest immutable floor snapshot. Later outboxes cannot rewrite its prefix.
    pub fn snapshot(&self) -> Option<&Snapshot<D>> {
        match &self.records[self.fence?].action {
            Action::Fence { snapshot }
            | Action::Enter { snapshot, .. }
            | Action::AdvanceWish { snapshot, .. } => Some(snapshot),
            _ => unreachable!(),
        }
    }
    /// Retrieves one bounded page without constructing all historical pages.
    pub fn history_page(&self, index: usize) -> Option<HistoryPage<D>> {
        let record = self.records.get(index)?.clone();
        Some(HistoryPage {
            previous: index.checked_sub(1).map(|i| self.heads[i]),
            record,
        })
    }
    const fn active(&self) -> Result<(), Error> {
        if self.replaying {
            Err(Error::Replay)
        } else {
            Ok(())
        }
    }
    fn normal(&self) -> Result<(), Error> {
        if self.terminal.is_some() {
            return Err(Error::Closed);
        }
        if self.floor > self.core.slot.proposal.round {
            return Err(Error::Floor);
        }
        if self.rpcs.last_key_value().is_some() {
            return Err(Error::CatchUp);
        }
        Ok(())
    }
    fn check_known_rpc(&self, message: &Message<D>) -> Result<(), Error> {
        let Some((round, receipts)) = self.rpcs.last_key_value() else {
            return Ok(());
        };
        if *round < message.round {
            return Ok(());
        }
        let Kind::Recovery { subject, .. } = &message.kind else {
            return Err(Error::CatchUp);
        };
        if *round > message.round {
            return Err(Error::CatchUp);
        }
        for i in receipts {
            let Action::RetainRpc {
                proposal, decision, ..
            } = self.records[*i].action
            else {
                unreachable!()
            };
            if proposal != subject.proposal || decision != subject.decision {
                return Err(Error::CatchUp);
            }
        }
        Ok(())
    }
    fn record(&self, action: Action<D>) -> Record<D> {
        Record {
            core: self.core.clone(),
            input: self.input,
            owner: self.owner,
            action,
        }
    }
    fn message<H: Hasher<Digest = D>>(&self, kind: Kind<D>) -> Message<D> {
        Message {
            slot: self.core.slot.id::<H>(),
            round: self.core.slot.proposal.round,
            leader: self.core.leader,
            kind,
        }
    }
    fn in_core(&self) -> bool {
        self.owner == self.core.leader || self.core.followers.contains(&self.owner)
    }
    fn old(&self, step: Step) -> Option<&Record<D>> {
        self.choices.get(&step).map(|i| &self.records[*i])
    }
    fn commit<H: Hasher<Digest = D>>(&mut self, record: Record<D>) -> Record<D> {
        if !self.ids.insert(record.id::<H>()) {
            return record;
        }
        let index = self.records.len();
        match &record.action {
            Action::NoFirst => {
                self.choices.insert(Step::First, index);
            }
            Action::AdvanceWish {
                snapshot, message, ..
            } => {
                self.floor = snapshot.ballot;
                self.fence = Some(index);
                self.choices
                    .insert(step(message).expect("checked WISH"), index);
            }
            Action::Reserve { message, .. } => {
                self.choices
                    .insert(step(message).expect("checked role"), index);
            }
            Action::Released { reservation, .. } => {
                let role = self
                    .choices
                    .iter()
                    .find_map(|(role, i)| {
                        (self.records[*i].id::<H>() == *reservation).then_some(*role)
                    })
                    .expect("checked reservation");
                self.outboxes.insert(role, index);
            }
            Action::Fence { snapshot } | Action::Enter { snapshot, .. } => {
                self.floor = snapshot.ballot;
                self.fence = Some(index);
                if matches!(record.action, Action::Enter { .. }) {
                    self.entries.insert(snapshot.ballot, index);
                }
            }
            Action::Terminal { .. } | Action::RecoveryTerminal { .. } => {
                self.terminal = Some(index);
            }
            Action::RetainRpc { round, .. } => {
                self.rpcs.entry(*round).or_default().push(index);
            }
            Action::RetainOrigin { .. } => {}
        }
        let page = HistoryPage {
            previous: self.heads.last().copied(),
            record: record.clone(),
        };
        self.heads.push(page.id::<H>());
        self.records.push(record.clone());
        record
    }
    fn first<H: Hasher<Digest = D>>(
        &self,
        report: Option<Bytes>,
        preference: Option<Bytes>,
        mut validate: impl FnMut(&First<D>) -> bool,
    ) -> Result<Record<D>, Error> {
        let row = First {
            core: self.core.id::<H>(),
            input: self.input,
            owner: self.owner,
            report,
            preference,
        };
        let record = self.record(Action::Reserve {
            message: self.message::<H>(Kind::First(row.clone())),
            authority: None,
        });
        if let Some(old) = self.old(Step::First) {
            return if *old == record {
                Ok(old.clone())
            } else {
                Err(Error::Conflict)
            };
        }
        self.normal()?;
        if !self.in_core()
            || self.owner == self.core.leader && (row.report.is_some() || row.preference.is_some())
        {
            return Err(Error::Context);
        }
        row.check(self.limits)?;
        self.message::<H>(Kind::First(row.clone())).check(
            super::Committee::new(self.context.scheme().participants().len())?,
            self.limits,
        )?;
        if !validate(&row) {
            return Err(super::Error::Policy.into());
        }
        Ok(record)
    }
    /// Freezes both independently ready fields. Never waits for optional preparation.
    pub fn reserve_first<H: Hasher<Digest = D>>(
        &mut self,
        report: Option<Bytes>,
        preference: Option<Bytes>,
        validate: impl FnMut(&First<D>) -> bool,
    ) -> Result<Record<D>, Error> {
        self.active()?;
        let record = self.first::<H>(report, preference, validate)?;
        Ok(self.commit::<H>(record))
    }
    fn no_first(&self) -> Result<Record<D>, Error> {
        let record = self.record(Action::NoFirst);
        if let Some(old) = self.old(Step::First) {
            return if *old == record {
                Ok(old.clone())
            } else {
                Err(Error::Conflict)
            };
        }
        self.normal()?;
        if self.in_core() {
            return Err(Error::Context);
        }
        Ok(record)
    }
    /// Closes an outside-Core FIRST opportunity. This is not signed absence.
    pub fn close_first<H: Hasher<Digest = D>>(&mut self) -> Result<Record<D>, Error> {
        self.active()?;
        let record = self.no_first()?;
        Ok(self.commit::<H>(record))
    }
    fn own_first(&self, body: &OriginBody<S, D>) -> Result<(), Error> {
        if !self.in_core() {
            return Ok(());
        }
        let old = self
            .old(Step::First)
            .and_then(Record::message)
            .ok_or(Error::Reservation)?;
        let row = body
            .firsts
            .iter()
            .find(|r| r.attestation.signer == self.owner)
            .ok_or(Error::Authority)?;
        if *old != row.message {
            return Err(Error::Conflict);
        }
        Ok(())
    }
    #[allow(clippy::too_many_arguments)]
    fn select<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        body: &OriginBody<S, D>,
        validate_row: impl FnMut(&First<D>) -> bool,
        validate_build: impl FnOnce(&VerifiedRows<S, D>, &OriginBody<S, D>) -> bool,
        strategy: &impl Strategy,
    ) -> Result<Record<D>, Error> {
        if self.owner != self.core.leader {
            return Err(Error::Context);
        }
        let checked = body.verify::<H, R>(
            rng,
            self.context.scheme(),
            &self.core,
            self.input,
            self.limits,
            validate_row,
            validate_build,
            strategy,
        )?;
        if let Some(old) = self.old(Step::Select) {
            return if matches!(old.message().map(|m| &m.kind), Some(Kind::Select { decision, .. }) if *decision == checked.decision())
            {
                Ok(old.clone())
            } else {
                Err(Error::Conflict)
            };
        }
        self.normal()?;
        self.own_first(body)?;
        Ok(self.record(Action::Reserve {
            message: self.message::<H>(Kind::Select {
                body: checked.body(),
                decision: checked.decision(),
            }),
            authority: Some(checked.body()),
        }))
    }
    /// Checks the full body before reserving SELECT. A same-decision retry returns
    /// the original reservation and body authority, never a replacement SELECT.
    #[allow(clippy::too_many_arguments)]
    pub fn reserve_select<H: Hasher<Digest = D>, R: CryptoRng>(
        &mut self,
        rng: &mut R,
        body: &OriginBody<S, D>,
        validate_row: impl FnMut(&First<D>) -> bool,
        validate_build: impl FnOnce(&VerifiedRows<S, D>, &OriginBody<S, D>) -> bool,
        strategy: &impl Strategy,
    ) -> Result<Record<D>, Error> {
        self.active()?;
        let record = self.select::<H, R>(rng, body, validate_row, validate_build, strategy)?;
        Ok(self.commit::<H>(record))
    }
    #[allow(clippy::too_many_arguments)]
    fn final_vote<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        origin: &Origin<S, D>,
        validate_row: impl FnMut(&First<D>) -> bool,
        validate_build: impl FnOnce(&VerifiedRows<S, D>, &OriginBody<S, D>) -> bool,
        strategy: &impl Strategy,
    ) -> Result<Record<D>, Error> {
        let checked = origin.verify::<H, R>(
            rng,
            self.context.scheme(),
            &self.core,
            self.input,
            self.limits,
            validate_row,
            validate_build,
            strategy,
        )?;
        if let Some(old) = self.old(Step::Final) {
            return if matches!(old.message().map(|m| &m.kind), Some(Kind::Phase { phase: Phase::FastFinal, decision }) if *decision == checked.decision())
            {
                Ok(old.clone())
            } else {
                Err(Error::Conflict)
            };
        }
        self.normal()?;
        self.own_first(&origin.body)?;
        if self.owner == self.core.leader
            && self.old(Step::Select).and_then(Record::message) != Some(&origin.selection.message)
        {
            return Err(Error::Reservation);
        }
        Ok(self.record(Action::Reserve {
            message: self.message::<H>(Kind::Phase {
                phase: Phase::FastFinal,
                decision: checked.decision(),
            }),
            authority: Some(checked.origin()),
        }))
    }
    /// Stages both original final subjects as one native-journal authorization.
    /// The native owner checks its eligibility/once-choice first, retains the
    /// exact own authority and synchronizes this whole item before signing.
    #[allow(clippy::too_many_arguments)]
    pub fn reserve_normal<H: Hasher<Digest = D>, R: CryptoRng>(
        &mut self,
        rng: &mut R,
        origin: &Origin<S, D>,
        validate_row: impl FnMut(&First<D>) -> bool,
        validate_build: impl FnOnce(&VerifiedRows<S, D>, &OriginBody<S, D>) -> bool,
        strategy: &impl Strategy,
    ) -> Result<super::normal::Reservation<D>, Error> {
        self.active()?;
        let agreement =
            self.final_vote::<H, R>(rng, origin, validate_row, validate_build, strategy)?;
        let reservation = super::normal::Reservation {
            subject: super::normal::subject::<H>(&origin.body.decision),
            agreement,
        };
        reservation.check::<H>()?;
        super::bounded(&reservation)?;
        self.commit::<H>(reservation.agreement.clone());
        Ok(reservation)
    }

    /// Replays the complete joint item using its exact original authority.
    /// Native once-choice restoration belongs to the same native WAL transition.
    #[allow(clippy::too_many_arguments)]
    pub fn restore_normal<H: Hasher<Digest = D>, R: CryptoRng>(
        &mut self,
        rng: &mut R,
        reservation: &super::normal::Reservation<D>,
        origin: &Origin<S, D>,
        validate_row: impl FnMut(&First<D>) -> bool,
        validate_build: impl FnOnce(&VerifiedRows<S, D>, &OriginBody<S, D>) -> bool,
        strategy: &impl Strategy,
    ) -> Result<(), Error> {
        self.preflight_origin(origin)?;
        reservation.check::<H>()?;
        if reservation.subject != super::normal::subject::<H>(&origin.body.decision) {
            return Err(Error::Context);
        }
        self.restore::<H, R>(
            rng,
            &reservation.agreement,
            Material::Origin(origin),
            validate_row,
            validate_build,
            strategy,
        )
    }

    /// Releases both genuine signatures without an intervening await. The owner
    /// rechecks live native eligibility immediately before calling. A partial
    /// signer failure is fatal to that incarnation; it must not publish a half.
    pub fn sign_normal<H: Hasher<Digest = D>>(
        &self,
        reservation: &super::normal::Reservation<D>,
    ) -> Result<super::normal::Vote<S, D>, Error> {
        reservation.check::<H>()?;
        // This checks all current G1 fences before either signer is invoked.
        let agreement = self.sign_reserved(&reservation.agreement)?;
        let native = crate::simplex::extension::vote::Vote::sign(
            self.context.scheme(),
            reservation.subject.clone(),
        )
        .ok_or(super::Error::Signature)?;
        Ok(super::normal::Vote {
            native,
            agreement,
            origin_hint: reservation.agreement.authority().ok_or(Error::Authority)?,
        })
    }

    fn check_normal_pair<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        reservation: &super::normal::Reservation<D>,
        pair: &super::normal::Vote<S, D>,
        strategy: &impl Strategy,
    ) -> Result<(), Error> {
        reservation.check::<H>()?;
        if self.old(Step::Final) != Some(&reservation.agreement)
            || pair.native.statement != reservation.subject
            || pair.agreement.message
                != *reservation.agreement.message().ok_or(Error::Reservation)?
            || pair.native.attestation.signer != self.owner
            || pair.agreement.attestation.signer != self.owner
            || Some(pair.origin_hint) != reservation.agreement.authority()
        {
            return Err(Error::Reservation);
        }
        if !pair.native.verify(rng, self.context.scheme(), strategy)
            || !pair
                .agreement
                .verify(rng, self.context.scheme(), self.limits, strategy)
        {
            return Err(super::Error::Signature.into());
        }
        Ok(())
    }

    /// Stages the complete paired outbox for native WAL synchronization. An old
    /// floor/terminal permits retention of already-created bytes, never signing.
    pub fn record_normal_signed<H: Hasher<Digest = D>, R: CryptoRng>(
        &mut self,
        rng: &mut R,
        reservation: &super::normal::Reservation<D>,
        pair: &super::normal::Vote<S, D>,
        strategy: &impl Strategy,
    ) -> Result<super::normal::Released<S, D>, Error> {
        self.active()?;
        self.check_normal_pair::<H, R>(rng, reservation, pair, strategy)?;
        let receipt =
            self.released::<H, R>(rng, &reservation.agreement, &pair.agreement, strategy)?;
        let released = super::normal::Released {
            reservation: reservation.clone(),
            receipt,
            vote: pair.clone(),
        };
        super::bounded(&released)?;
        if let Some(old) = &self.normal_outbox {
            return if *old == released {
                Ok(old.clone())
            } else {
                Err(Error::Conflict)
            };
        }
        self.commit::<H>(released.receipt.clone());
        self.normal_outbox = Some(released.clone());
        Ok(released)
    }

    /// Restores exact paired bytes, including after a later signing fence. All
    /// referenced original authority and the reservation must already be replayed.
    pub fn restore_normal_signed<H: Hasher<Digest = D>, R: CryptoRng>(
        &mut self,
        rng: &mut R,
        released: &super::normal::Released<S, D>,
        strategy: &impl Strategy,
    ) -> Result<(), Error> {
        if !self.replaying {
            return Err(Error::Replay);
        }
        self.check_normal_pair::<H, R>(rng, &released.reservation, &released.vote, strategy)?;
        let expected = self.released::<H, R>(
            rng,
            &released.reservation.agreement,
            &released.vote.agreement,
            strategy,
        )?;
        if expected != released.receipt {
            return Err(Error::Reservation);
        }
        if let Some(old) = &self.normal_outbox
            && old != released
        {
            return Err(Error::Conflict);
        }
        self.commit::<H>(released.receipt.clone());
        self.normal_outbox = Some(released.clone());
        Ok(())
    }

    /// Exact retained pair; synchronize its receipt before publication. This
    /// accessor never calls either signer, including after a fence or terminal.
    pub fn normal_outbox(
        &self,
        reservation: &super::normal::Reservation<D>,
    ) -> Option<&super::normal::Vote<S, D>> {
        let released = self.normal_outbox.as_ref()?;
        (released.reservation == *reservation).then_some(&released.vote)
    }

    /// Stages only G1 FAST_FINAL. Native P eligibility and its atomic final choice
    /// must be established by the native owner before either role is released.
    #[allow(clippy::too_many_arguments)]
    pub fn reserve_fast_final<H: Hasher<Digest = D>, R: CryptoRng>(
        &mut self,
        rng: &mut R,
        origin: &Origin<S, D>,
        validate_row: impl FnMut(&First<D>) -> bool,
        validate_build: impl FnOnce(&VerifiedRows<S, D>, &OriginBody<S, D>) -> bool,
        strategy: &impl Strategy,
    ) -> Result<Record<D>, Error> {
        self.active()?;
        let record =
            self.final_vote::<H, R>(rng, origin, validate_row, validate_build, strategy)?;
        Ok(self.commit::<H>(record))
    }
    #[allow(clippy::too_many_arguments)]
    fn origin_record<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        origin: &Origin<S, D>,
        validate_row: impl FnMut(&First<D>) -> bool,
        validate_build: impl FnOnce(&VerifiedRows<S, D>, &OriginBody<S, D>) -> bool,
        strategy: &impl Strategy,
    ) -> Result<Record<D>, Error> {
        let checked = origin.verify::<H, R>(
            rng,
            self.context.scheme(),
            &self.core,
            self.input,
            self.limits,
            validate_row,
            validate_build,
            strategy,
        )?;
        Ok(self.record(Action::RetainOrigin {
            origin: checked.origin(),
            decision: checked.decision(),
        }))
    }
    /// Stages exact positive-origin custody without voting. The caller reserves
    /// retention capacity and material pins before accepting and synchronizing
    /// this receipt. Each accepted alias remains a separate immutable artifact;
    /// this is not an automatic network intake or permission to prune old proofs.
    /// A local floor or terminal does not invalidate positive proof receipt.
    #[allow(clippy::too_many_arguments)]
    pub fn retain_origin<H: Hasher<Digest = D>, R: CryptoRng>(
        &mut self,
        rng: &mut R,
        origin: &Origin<S, D>,
        validate_row: impl FnMut(&First<D>) -> bool,
        validate_build: impl FnOnce(&VerifiedRows<S, D>, &OriginBody<S, D>) -> bool,
        strategy: &impl Strategy,
    ) -> Result<Record<D>, Error> {
        self.active()?;
        let record =
            self.origin_record::<H, R>(rng, origin, validate_row, validate_build, strategy)?;
        Ok(self.commit::<H>(record))
    }
    /// Calls the signer only after caller-owned custody and journal synchronization.
    /// No await may separate the native owner's latest preflight and this call.
    pub fn sign_reserved(&self, record: &Record<D>) -> Result<Signed<S, D>, Error> {
        self.active()?;
        let message = record.message().ok_or(Error::Reservation)?;
        if self.terminal.is_some() {
            return Err(Error::Closed);
        }
        if message.round != self.floor {
            return Err(Error::Floor);
        }
        if let Kind::Wish(wish) = &message.kind {
            let previous_view = message
                .round
                .view()
                .get()
                .checked_sub(1)
                .ok_or(Error::Context)?;
            let previous = Round::new(message.round.epoch(), View::new(previous_view));
            let index = self.entries.get(&previous).ok_or(Error::Authority)?;
            if self.records[*index].authority() != Some(wish.predecessor) {
                return Err(Error::Authority);
            }
        }
        if let Kind::Recover(recover) = &message.kind {
            self.entered(message.round, message.leader, recover.entry)?;
        }
        if let Kind::Recovery { subject, .. } = &message.kind {
            self.entered(message.round, message.leader, subject.entry)?;
        }
        self.check_known_rpc(message)?;
        let role = step(message).ok_or(Error::Reservation)?;
        if self.old(role) != Some(record) {
            return Err(Error::Reservation);
        }
        if self.outboxes.contains_key(&role) {
            return Err(Error::Released);
        }
        Ok(Signed::sign(
            self.context.scheme(),
            message.clone(),
            self.limits,
        )?)
    }
    fn released<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        reservation: &Record<D>,
        signed: &Signed<S, D>,
        strategy: &impl Strategy,
    ) -> Result<Record<D>, Error> {
        let message = reservation.message().ok_or(Error::Reservation)?;
        let role = step(message).ok_or(Error::Reservation)?;
        if self.old(role) != Some(reservation)
            || signed.message != *message
            || signed.attestation.signer != self.owner
        {
            return Err(Error::Reservation);
        }
        if !signed.verify(rng, self.context.scheme(), self.limits, strategy) {
            return Err(super::Error::Signature.into());
        }
        let record = self.record(Action::Released {
            reservation: reservation.id::<H>(),
            frame: signed.encode(),
        });
        if let Some(i) = self.outboxes.get(&role) {
            return if self.records[*i] == record {
                Ok(record)
            } else {
                Err(Error::Conflict)
            };
        }
        Ok(record)
    }
    /// Stages an exact signed outbox receipt. A fence may already exist because
    /// the earlier unsigned reservation covered this possible release. This
    /// retains bytes only and never calls a signer or reopens the old floor.
    pub fn record_signed<H: Hasher<Digest = D>, R: CryptoRng>(
        &mut self,
        rng: &mut R,
        reservation: &Record<D>,
        signed: &Signed<S, D>,
        strategy: &impl Strategy,
    ) -> Result<Record<D>, Error> {
        self.active()?;
        let record = self.released::<H, R>(rng, reservation, signed, strategy)?;
        Ok(self.commit::<H>(record))
    }
    /// Exact accepted signed bytes, including after a higher floor or terminal.
    /// The caller must synchronize the receipt before publishing these bytes.
    pub fn outbox(&self, reservation: &Record<D>) -> Option<&Bytes> {
        let role = step(reservation.message()?)?;
        if self.old(role) != Some(reservation) {
            return None;
        }
        let Action::Released { frame, .. } = &self.records[*self.outboxes.get(&role)?].action
        else {
            unreachable!()
        };
        Some(frame)
    }
    fn floor_record<H: Hasher<Digest = D>>(
        &self,
        ballot: Round,
        leader: Participant,
    ) -> Result<Record<D>, Error> {
        if ballot.epoch() != self.core.slot.proposal.round.epoch()
            || ballot <= self.core.slot.proposal.round
            || usize::from(leader) >= self.context.scheme().participants().len()
        {
            return Err(Error::Context);
        }
        if ballot < self.floor {
            return Err(Error::Floor);
        }
        if ballot == self.floor
            && let Some(i) = self.fence
        {
            let old = &self.records[i];
            let snapshot = match &old.action {
                Action::Fence { snapshot }
                | Action::Enter { snapshot, .. }
                | Action::AdvanceWish { snapshot, .. } => snapshot,
                _ => unreachable!(),
            };
            return if snapshot.leader == leader {
                Ok(old.clone())
            } else {
                Err(Error::Conflict)
            };
        }
        if self.terminal.is_some() {
            return Err(Error::Closed);
        }
        Ok(self.record(Action::Fence {
            snapshot: Snapshot {
                slot: self.core.slot.id::<H>(),
                owner: self.owner,
                ballot,
                leader,
                head: self.heads.last().copied(),
                count: u64::try_from(self.records.len()).map_err(|_| Error::Context)?,
            },
        }))
    }
    /// Stages conservative local revocation only. The native owner separately
    /// authenticates the elected carrier, failure deadline and entry protocol.
    /// It must sync this record before exporting the frozen snapshot. This
    /// method grants no right to sign a recovery message.
    pub fn fence<H: Hasher<Digest = D>>(
        &mut self,
        ballot: Round,
        leader: Participant,
    ) -> Result<Record<D>, Error> {
        self.active()?;
        let record = self.floor_record::<H>(ballot, leader)?;
        Ok(self.commit::<H>(record))
    }
    #[allow(clippy::too_many_arguments)]
    fn terminal_record<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        origin: &Origin<S, D>,
        quorum: &Quorum<S, D>,
        validate_row: impl FnMut(&First<D>) -> bool,
        validate_build: impl FnOnce(&VerifiedRows<S, D>, &OriginBody<S, D>) -> bool,
        strategy: &impl Strategy,
    ) -> Result<Record<D>, Error> {
        let checked = origin.verify::<H, R>(
            rng,
            self.context.scheme(),
            &self.core,
            self.input,
            self.limits,
            validate_row,
            validate_build,
            strategy,
        )?;
        if quorum.message
            != self.message::<H>(Kind::Phase {
                phase: Phase::FastFinal,
                decision: checked.decision(),
            })
            || !quorum.verify(rng, self.context.scheme(), self.limits, strategy)
        {
            return Err(Error::Authority);
        }
        if let Some(i) = self.terminal {
            return if self.terminal_decision() == Some(checked.decision()) {
                Ok(self.records[i].clone())
            } else {
                Err(Error::Conflict)
            };
        }
        Ok(self.record(Action::Terminal {
            origin: checked.origin(),
            certificate: H::hash(&[TERMINAL, &quorum.encode()]),
            decision: checked.decision(),
        }))
    }
    /// Retains a genuine interpretation terminal and closes original G1 signing.
    /// A higher local floor does not make a valid old certificate disappear.
    /// This neither chooses native P nor establishes native finality or delivery.
    #[allow(clippy::too_many_arguments)]
    pub fn terminal<H: Hasher<Digest = D>, R: CryptoRng>(
        &mut self,
        rng: &mut R,
        origin: &Origin<S, D>,
        quorum: &Quorum<S, D>,
        validate_row: impl FnMut(&First<D>) -> bool,
        validate_build: impl FnOnce(&VerifiedRows<S, D>, &OriginBody<S, D>) -> bool,
        strategy: &impl Strategy,
    ) -> Result<Record<D>, Error> {
        self.active()?;
        let record = self.terminal_record::<H, R>(
            rng,
            origin,
            quorum,
            validate_row,
            validate_build,
            strategy,
        )?;
        Ok(self.commit::<H>(record))
    }
    // Replay compares exact authority identities before application callbacks.
    // Bound adversarial in-memory material before identity encoding as well.
    fn preflight_body(&self, body: &OriginBody<S, D>) -> Result<(), Error> {
        self.limits.check()?;
        if body.core.followers.len() > 63 || body.firsts.len() > 64 {
            return Err(super::Error::Limit.into());
        }
        if body.decision.order.len() > self.limits.order_bytes
            || body.build.len() > self.limits.build_bytes
            || body.material.len() > self.limits.material_bytes
        {
            return Err(super::Error::Limit.into());
        }
        let committee = super::Committee::new(self.context.scheme().participants().len())?;
        for signed in &body.firsts {
            signed.message.check(committee, self.limits)?;
            if signed.encode_size() > super::MAX_FIRST_BYTES {
                return Err(super::Error::Limit.into());
            }
        }
        let size = body.encode_size();
        if size > self.limits.origin_bytes || size > super::MAX_EVIDENCE_BYTES {
            return Err(super::Error::Limit.into());
        }
        Ok(())
    }
    fn preflight_origin(&self, origin: &Origin<S, D>) -> Result<(), Error> {
        self.preflight_body(&origin.body)?;
        origin.selection.message.check(
            super::Committee::new(self.context.scheme().participants().len())?,
            self.limits,
        )?;
        let size = origin.encode_size();
        if origin.selection.encode_size() > super::MAX_FIRST_BYTES
            || size > self.limits.origin_bytes
            || size > super::MAX_EVIDENCE_BYTES
        {
            return Err(super::Error::Limit.into());
        }
        Ok(())
    }
    fn preflight_quorum(&self, quorum: &Quorum<S, D>) -> Result<(), Error> {
        self.limits.check()?;
        quorum.message.check(
            super::Committee::new(self.context.scheme().participants().len())?,
            self.limits,
        )?;
        // The certificate's registered codec is opaque. Its complete frame cap
        // is 4 MiB, not the 16 KiB cap used by some other native embeddings.
        super::bounded(quorum)?;
        Ok(())
    }
    /// Replays one exact native-journal record with all referenced authority.
    /// Missing A cannot be replaced with a same-decision B. No mutation occurs
    /// when validation fails. Replay the complete log before `finish_replay`.
    #[allow(clippy::too_many_arguments)]
    pub fn restore<H: Hasher<Digest = D>, R: CryptoRng>(
        &mut self,
        rng: &mut R,
        record: &Record<D>,
        material: Material<'_, S, D>,
        validate_row: impl FnMut(&First<D>) -> bool,
        validate_build: impl FnOnce(&VerifiedRows<S, D>, &OriginBody<S, D>) -> bool,
        strategy: &impl Strategy,
    ) -> Result<(), Error> {
        if !self.replaying {
            return Err(Error::Replay);
        }
        if record.core != self.core || record.input != self.input || record.owner != self.owner {
            return Err(Error::Context);
        }
        let expected = match &record.action {
            Action::NoFirst => self.no_first()?,
            Action::Reserve {
                message:
                    Message {
                        kind: Kind::Recover(row),
                        ..
                    },
                authority,
            } => {
                let Material::Entry(checked) = material else {
                    return Err(Error::Authority);
                };
                self.check_entry::<H>(checked)?;
                if *authority != Some(checked.artifact_id()) {
                    return Err(Error::Authority);
                }
                self.recover::<H>(checked, row.report.clone())?
            }
            Action::Reserve {
                message:
                    Message {
                        kind: Kind::Recovery { phase, .. },
                        ..
                    },
                authority,
            } => {
                let Material::Recovery(checked) = material else {
                    return Err(Error::Authority);
                };
                if *authority != Some(checked.evidence()) {
                    return Err(Error::Authority);
                }
                self.recovery_record::<H>(checked, *phase)?
            }
            Action::Reserve {
                message:
                    Message {
                        kind: Kind::First(row),
                        ..
                    },
                ..
            } => self.first::<H>(row.report.clone(), row.preference.clone(), validate_row)?,
            Action::Reserve {
                message:
                    Message {
                        kind: Kind::Select { .. },
                        ..
                    },
                authority,
            } => {
                let Material::Body(body) = material else {
                    return Err(Error::Authority);
                };
                self.preflight_body(body)?;
                if *authority != Some(body.id::<H>()) {
                    return Err(Error::Authority);
                }
                self.select::<H, R>(rng, body, validate_row, validate_build, strategy)?
            }
            Action::Reserve {
                message:
                    Message {
                        kind:
                            Kind::Phase {
                                phase: Phase::FastFinal,
                                ..
                            },
                        ..
                    },
                authority,
            } => {
                let Material::Origin(origin) = material else {
                    return Err(Error::Authority);
                };
                self.preflight_origin(origin)?;
                if *authority != Some(origin.id::<H>()) {
                    return Err(Error::Authority);
                }
                self.final_vote::<H, R>(rng, origin, validate_row, validate_build, strategy)?
            }
            Action::Reserve { .. } => return Err(Error::Authority),
            Action::Released { reservation, frame } => {
                let old = self
                    .choices
                    .values()
                    .find_map(|i| {
                        (self.records[*i].id::<H>() == *reservation).then_some(&self.records[*i])
                    })
                    .ok_or(Error::Reservation)?;
                let signed = <Signed<S, D> as commonware_codec::Decode>::decode_cfg(
                    frame.clone(),
                    &self.limits,
                )
                .map_err(|_| Error::Authority)?;
                self.released::<H, R>(rng, old, &signed, strategy)?
            }
            Action::Fence { snapshot } => {
                self.floor_record::<H>(snapshot.ballot, snapshot.leader)?
            }
            Action::Enter { authority, .. } => {
                let Material::Entry(checked) = material else {
                    return Err(Error::Authority);
                };
                self.check_entry::<H>(checked)?;
                if *authority != checked.artifact_id() {
                    return Err(Error::Authority);
                }
                self.entry_record::<H>(checked)?
            }
            Action::AdvanceWish { message, cause, .. } => {
                let predecessor = match (cause, material) {
                    (WishCause::Timeout, Material::Entry(p)) => p,
                    (
                        WishCause::Amplification(id),
                        Material::Amplification {
                            predecessor,
                            amplification,
                        },
                    ) => {
                        self.check_amplification::<H>(predecessor, amplification)?;
                        if *id != amplification.artifact_id() {
                            return Err(Error::Authority);
                        }
                        predecessor
                    }
                    _ => return Err(Error::Authority),
                };
                let Kind::Wish(wish) = &message.kind else {
                    return Err(Error::Authority);
                };
                if wish.predecessor != predecessor.artifact_id() {
                    return Err(Error::Authority);
                }
                // Trusted local WAL preserves accepted permission; public-only
                // replay validates data, never grants a timer or signer surface.
                self.wish_record::<H>(predecessor, *cause)?
            }
            Action::RetainRpc { proof, .. } => {
                let Material::Recovery(checked) = material else {
                    return Err(Error::Authority);
                };
                if *proof != checked.evidence() {
                    return Err(Error::Authority);
                }
                self.rpc_record::<H>(checked)?
            }
            Action::RecoveryTerminal { proof, .. } => {
                let Material::Recovery(checked) = material else {
                    return Err(Error::Authority);
                };
                if *proof != checked.evidence() {
                    return Err(Error::Authority);
                }
                self.recovery_terminal_record::<H>(checked)?
            }
            Action::Terminal {
                origin: id,
                certificate: id_q,
                ..
            } => {
                let Material::Terminal { origin, quorum } = material else {
                    return Err(Error::Authority);
                };
                self.preflight_origin(origin)?;
                self.preflight_quorum(quorum)?;
                if *id != origin.id::<H>() || *id_q != H::hash(&[TERMINAL, &quorum.encode()]) {
                    return Err(Error::Authority);
                }
                self.terminal_record::<H, R>(
                    rng,
                    origin,
                    quorum,
                    validate_row,
                    validate_build,
                    strategy,
                )?
            }
            Action::RetainOrigin { origin: id, .. } => {
                let Material::Origin(origin) = material else {
                    return Err(Error::Authority);
                };
                self.preflight_origin(origin)?;
                if *id != origin.id::<H>() {
                    return Err(Error::Authority);
                }
                self.origin_record::<H, R>(rng, origin, validate_row, validate_build, strategy)?
            }
        };
        if expected != *record {
            return Err(Error::Conflict);
        }
        self.commit::<H>(expected);
        Ok(())
    }
}
const fn step<D: Digest>(message: &Message<D>) -> Option<Step> {
    match message.kind {
        Kind::First(_) => Some(Step::First),
        Kind::Select { .. } => Some(Step::Select),
        Kind::Phase {
            phase: Phase::FastFinal,
            ..
        } => Some(Step::Final),
        Kind::Recover(_) => Some(Step::Recover(message.round)),
        Kind::Wish(_) => Some(Step::Wish(message.round)),
        Kind::Recovery { phase, .. } => Some(match phase {
            recovery::Phase::Propose => Step::Propose(message.round),
            recovery::Phase::Prepare => Step::Prepare(message.round),
            recovery::Phase::Commit => Step::Commit(message.round),
        }),
        _ => None,
    }
}

#[cfg(feature = "arbitrary")]
impl<'a, D: Digest + arbitrary::Arbitrary<'a>> arbitrary::Arbitrary<'a> for WishCause<D> {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        Ok(if u.arbitrary()? {
            Self::Timeout
        } else {
            Self::Amplification(u.arbitrary()?)
        })
    }
}

// Bounded raw AdvanceWish records, not accepted local permissions. Historical
// record families retain their existing deterministic conformance generators.
#[cfg(feature = "arbitrary")]
impl<D: Digest> arbitrary::Arbitrary<'_> for Record<D>
where
    D: for<'a> arbitrary::Arbitrary<'a>,
{
    fn arbitrary(u: &mut arbitrary::Unstructured<'_>) -> arbitrary::Result<Self> {
        let target: entry::Target<D> = u.arbitrary()?;
        let owner = Participant::new(u.int_in_range(0..=63)?);
        let slot = super::Slot {
            profile: u.arbitrary()?,
            domain: u.arbitrary()?,
            roster: u.arbitrary()?,
            cut: u.arbitrary()?,
            proposal: u.arbitrary()?,
            parent: super::NativeParent::Genesis(u.arbitrary()?),
        };
        let message = Message {
            slot: u.arbitrary()?,
            round: target.ballot,
            leader: target.leader,
            kind: Kind::Wish(entry::Wish {
                target: target.clone(),
                predecessor: u.arbitrary()?,
            }),
        };
        let head: Option<D> = u.arbitrary()?;
        Ok(Self {
            core: Core {
                slot,
                leader: Participant::new(u.int_in_range(0..=63)?),
                followers: Vec::new(),
            },
            input: u.arbitrary()?,
            owner,
            action: Action::AdvanceWish {
                snapshot: Snapshot {
                    slot: message.slot,
                    owner,
                    ballot: target.ballot,
                    leader: target.leader,
                    count: if head.is_some() {
                        u.int_in_range(1..=u64::MAX)?
                    } else {
                        0
                    },
                    head,
                },
                message,
                cause: u.arbitrary()?,
            },
        })
    }
}
