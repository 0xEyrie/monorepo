//! Local issuance choices for the versioned seven-validator voter.
//!
//! This is the state/record portion of the native journal, not a new database.
//! The owner validates native authority and complete evidence before staging,
//! retains required bodies, appends the returned record to its journal, syncs,
//! then calls `sign_reserved`. Storage failure requires stopping and replaying.
//! Replay restores every retained record before any signer is enabled.

use super::{
    Core, Kind, Limits, Message, Signed, Slot,
    recovery::{self, Entry, Material, Page, Phase, Verified, Verifier},
    scheme,
};
use crate::{
    Epochable, Viewable,
    types::{Epoch, Participant, Round, View},
};
use bytes::BufMut;
use commonware_codec::{Buf, EncodeSize, Error as CodecError, Read, ReadExt as _, Write};
use commonware_cryptography::{Digest, Hasher};
use commonware_parallel::Strategy;
use rand_core::CryptoRng;
use std::collections::BTreeMap;
use thiserror::Error;

/// Original ready reports obey the existing native first-vote transport bound.
const REPORT_LIMIT: usize = crate::simplex::extension::report::MAX_REPORT_BYTES;

/// A retained positive proof. A prepared proof is not a final decision.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Witness {
    Origin,
    Prepared,
}

/// Exact unsigned choice or material receipt, synchronized in the voter journal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Record<D: Digest> {
    slot: Slot<D>,
    owner: Participant,
    action: Action<D>,
}

/// Record contents are public for custody/replay inspection, not vote authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Action<D: Digest> {
    Reserve {
        message: Message<D>,
        /// Exact retained origin, selection input, proposal/J or RPC body.
        authority: Option<D>,
        /// Original Core is retained with FIRST, before a full origin exists.
        core: Option<Core<D>>,
    },
    Retain {
        root: D,
        round: Round,
        leader: Participant,
        value: D,
        kind: Witness,
    },
    Decide {
        root: D,
        round: Round,
        leader: Participant,
        value: D,
    },
}
impl<D: Digest> Record<D> {
    pub const fn slot(&self) -> &Slot<D> {
        &self.slot
    }
    pub const fn owner(&self) -> Participant {
        self.owner
    }
    pub const fn action(&self) -> &Action<D> {
        &self.action
    }
}
impl<D: Digest> Epochable for Record<D> {
    fn epoch(&self) -> Epoch {
        self.slot.proposal.round.epoch()
    }
}
impl<D: Digest> Viewable for Record<D> {
    // Journal retention is anchored at the unresolved original P, not its carrier.
    fn view(&self) -> View {
        self.slot.proposal.round.view()
    }
}
impl<D: Digest> Write for Record<D> {
    fn write(&self, w: &mut impl BufMut) {
        1u8.write(w);
        self.slot.write(w);
        self.owner.write(w);
        match &self.action {
            Action::Reserve {
                message,
                authority,
                core,
            } => {
                0u8.write(w);
                message.write(w);
                authority.write(w);
                core.write(w);
            }
            Action::Retain {
                root,
                round,
                leader,
                value,
                kind,
            } => {
                1u8.write(w);
                root.write(w);
                round.write(w);
                leader.write(w);
                value.write(w);
                match kind {
                    Witness::Origin => 0u8,
                    Witness::Prepared => 1u8,
                }
                .write(w);
            }
            Action::Decide {
                root,
                round,
                leader,
                value,
            } => {
                2u8.write(w);
                root.write(w);
                round.write(w);
                leader.write(w);
                value.write(w);
            }
        }
    }
}
impl<D: Digest> EncodeSize for Record<D> {
    fn encode_size(&self) -> usize {
        2 + self.slot.encode_size()
            + self.owner.encode_size()
            + match &self.action {
                Action::Reserve {
                    message,
                    authority,
                    core,
                } => message.encode_size() + authority.encode_size() + core.encode_size(),
                Action::Retain {
                    root,
                    round,
                    leader,
                    value,
                    ..
                } => {
                    root.encode_size()
                        + round.encode_size()
                        + leader.encode_size()
                        + value.encode_size()
                        + 1
                }
                Action::Decide {
                    root,
                    round,
                    leader,
                    value,
                } => {
                    root.encode_size()
                        + round.encode_size()
                        + leader.encode_size()
                        + value.encode_size()
                }
            }
    }
}
impl<D: Digest> Read for Record<D> {
    type Cfg = ();
    fn read_cfg(r: &mut impl Buf, _: &()) -> Result<Self, CodecError> {
        if u8::read(r)? != 1 {
            return Err(CodecError::Invalid("agreement issuance", "version"));
        }
        let slot = Slot::read(r)?;
        let owner = Participant::read(r)?;
        let action = match u8::read(r)? {
            0 => Action::Reserve {
                message: Message::read_cfg(r, &REPORT_LIMIT)?,
                authority: Option::<D>::read(r)?,
                core: Option::<Core<D>>::read(r)?,
            },
            1 => Action::Retain {
                root: D::read(r)?,
                round: Round::read(r)?,
                leader: Participant::read(r)?,
                value: D::read(r)?,
                kind: match u8::read(r)? {
                    0 => Witness::Origin,
                    1 => Witness::Prepared,
                    _ => return Err(CodecError::Invalid("agreement issuance", "witness")),
                },
            },
            2 => Action::Decide {
                root: D::read(r)?,
                round: Round::read(r)?,
                leader: Participant::read(r)?,
                value: D::read(r)?,
            },
            _ => return Err(CodecError::Invalid("agreement issuance", "action")),
        };
        Ok(Self {
            slot,
            owner,
            action,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum Error {
    #[error("wrong issuance identity or native context")]
    Context,
    #[error("conflicting immutable local choice")]
    Conflict,
    #[error("lower than the local issuance floor")]
    Floor,
    #[error("the logical cut has a terminal decision")]
    Closed,
    #[error("missing or incorrect authority role")]
    Authority,
    #[error("record is not a retained signing reservation")]
    Reservation,
    #[error("native signing failed")]
    Signature,
}

/// Full proof admission errors remain distinct from local issuance rejection.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum RetainError<D: Digest> {
    #[error("agreement proof: {0}")]
    Proof(#[from] recovery::Error<D>),
    #[error("local issuance: {0}")]
    State(#[from] Error),
}

/// Material to retain before synchronizing the atomic floor/snapshot reservation.
pub struct Snapshot<D: Digest> {
    pub record: Record<D>,
    pub pages: Vec<Page<D>>,
}

/// Per-original-Slot choices. No unresolved history is pruned or truncated.
/// Validation/custody and journal sync are owner prerequisites, not inferred here.
/// One authoritative instance owns each identity/Slot. Startup must restore its
/// complete journal; storage loss does not permit reinitializing the same key.
#[derive(Debug)]
pub struct State<S, D: Digest> {
    scheme: S,
    limits: Limits,
    slot: Slot<D>,
    owner: Participant,
    original_leader: Participant,
    floor: Round,
    records: Vec<Record<D>>,
    choices: BTreeMap<(Round, Step), usize>,
    witnesses: BTreeMap<D, usize>,
    terminal: Option<usize>,
}
impl<S: scheme::Scheme<D>, D: Digest> State<S, D> {
    /// `leader` and Slot admission come from the native voter, not peer metadata.
    pub fn new<H: Hasher<Digest = D>>(
        slot: Slot<D>,
        scheme: S,
        leader: Participant,
        limits: Limits,
    ) -> Result<Self, Error> {
        let owner = scheme.me().ok_or(Error::Context)?;
        if usize::from(owner) >= 7
            || usize::from(leader) >= 7
            || limits.report_bytes > REPORT_LIMIT
            || slot.check_roster::<H, S>(&scheme).is_err()
        {
            return Err(Error::Context);
        }
        Ok(Self {
            scheme,
            limits,
            floor: slot.proposal.round,
            slot,
            owner,
            original_leader: leader,
            records: Vec::new(),
            choices: BTreeMap::new(),
            witnesses: BTreeMap::new(),
            terminal: None,
        })
    }
    pub const fn floor(&self) -> Round {
        self.floor
    }
    pub const fn slot(&self) -> &Slot<D> {
        &self.slot
    }
    pub fn records(&self) -> &[Record<D>] {
        &self.records
    }
    pub fn terminal(&self) -> Option<&Record<D>> {
        self.terminal.map(|i| &self.records[i])
    }

    /// Stage an already validated subject and its durably retained authority.
    /// FIRST/SELECT inputs, origin/J/RPC and native eligibility must be verified
    /// by the owner before this call. It grants no native view or finality.
    pub fn reserve<H: Hasher<Digest = D>>(
        &mut self,
        message: Message<D>,
        authority: Option<D>,
        core: Option<Core<D>>,
        authorize: impl Fn(Round) -> Option<Participant>,
    ) -> Result<Record<D>, Error> {
        if matches!(message.kind, Kind::Recover { .. }) {
            return Err(Error::Authority);
        }
        let key = (message.round, phase(&message.kind));
        if let Some(i) = self.choices.get(&key) {
            let old = &self.records[*i];
            if let Action::Reserve {
                message: old_message,
                ..
            } = &old.action
                && old_message == &message
            {
                // Keep the original authority even for a new encoding of the same subject.
                return Ok(old.clone());
            }
            return Err(Error::Conflict);
        }
        let record = Record {
            slot: self.slot.clone(),
            owner: self.owner,
            action: Action::Reserve {
                message,
                authority,
                core,
            },
        };
        self.restore::<H>(&record, authorize)?;
        Ok(record)
    }

    /// Freeze the original response once at b, including all lower reservations.
    /// Calling this after an own b PREPARE/COMMIT excludes those b subjects.
    pub fn recover<H: Hasher<Digest = D>>(
        &mut self,
        round: Round,
        leader: Participant,
        report: Option<bytes::Bytes>,
        authorize: impl Fn(Round) -> Option<Participant>,
    ) -> Result<Snapshot<D>, Error> {
        self.context(round, leader, &authorize)?;
        if self.terminal.is_some() {
            return Err(Error::Closed);
        }
        if round < self.floor {
            return Err(Error::Floor);
        }
        if let Some(i) = self.choices.get(&(round, Step::Recover)) {
            return Ok(Snapshot {
                record: self.records[*i].clone(),
                pages: self.history::<H>(*i, round).1,
            });
        }
        let (history, pages) = self.history::<H>(self.records.len(), round);
        let record = Record {
            slot: self.slot.clone(),
            owner: self.owner,
            action: Action::Reserve {
                message: Message {
                    slot: self.slot.id::<H>(),
                    round,
                    leader,
                    kind: Kind::Recover { history, report },
                },
                authority: None,
                core: None,
            },
        };
        self.restore::<H>(&record, authorize)?;
        Ok(Snapshot { record, pages })
    }

    /// Verify positive evidence with this owner's fixed scheme and field limits.
    /// Complete body custody must be durable before journaling the returned record.
    /// A terminal proof immediately stages an immutable terminal tombstone.
    pub fn retain<'b, H: Hasher<Digest = D>, R: CryptoRng>(
        &mut self,
        rng: &mut R,
        root: D,
        resolve: impl Fn(&D) -> Option<&'b Material<S, D>>,
        strategy: &impl Strategy,
        policy: impl Fn(&super::Value<D>) -> bool,
        authorize: impl Fn(Round) -> Option<Participant>,
    ) -> Result<Record<D>, RetainError<D>>
    where
        S: 'b,
        D: 'b,
    {
        let checked = Verifier::new(
            &self.scheme,
            &self.slot,
            self.limits,
            strategy,
            policy,
            &authorize,
        )
        .verify::<H, _>(rng, root, resolve)?;
        Ok(self.stage_verified::<H>(&checked, authorize)?)
    }

    fn stage_verified<H: Hasher<Digest = D>>(
        &mut self,
        checked: &Verified<D>,
        authorize: impl Fn(Round) -> Option<Participant>,
    ) -> Result<Record<D>, Error> {
        if checked.slot() != self.slot.id::<H>() {
            return Err(Error::Context);
        }
        let value = checked.value().ok_or(Error::Authority)?.id::<H>();
        let root = checked.evidence();
        let round = checked.round();
        let leader = checked.leader();
        let action = match checked.phase() {
            Phase::Origin => Action::Retain {
                root,
                round,
                leader,
                value,
                kind: Witness::Origin,
            },
            Phase::Prepared => Action::Retain {
                root,
                round,
                leader,
                value,
                kind: Witness::Prepared,
            },
            Phase::Terminal => Action::Decide {
                root,
                round,
                leader,
                value,
            },
            _ => return Err(Error::Authority),
        };
        let record = Record {
            slot: self.slot.clone(),
            owner: self.owner,
            action,
        };
        self.restore::<H>(&record, authorize)?;
        Ok(record)
    }

    /// Restore an own journal record after checking its exact material custody.
    /// Replay all records before enabling signing. This does not verify proofs.
    pub fn restore<H: Hasher<Digest = D>>(
        &mut self,
        record: &Record<D>,
        authorize: impl Fn(Round) -> Option<Participant>,
    ) -> Result<(), Error> {
        if record.slot != self.slot || record.owner != self.owner {
            return Err(Error::Context);
        }
        match &record.action {
            Action::Reserve {
                message,
                authority,
                core,
            } => {
                let key = (message.round, phase(&message.kind));
                if let Some(old) = self.choices.get(&key) {
                    return if self.records[*old] == *record {
                        Ok(())
                    } else {
                        Err(Error::Conflict)
                    };
                }
                if self.terminal.is_some() {
                    return Err(Error::Closed);
                }
                self.context(message.round, message.leader, &authorize)?;
                if message.slot != self.slot.id::<H>() {
                    return Err(Error::Context);
                }
                if message.round < self.floor {
                    return Err(Error::Floor);
                }
                if matches!(
                    message.kind,
                    Kind::Prepare(_) | Kind::Commit(_) | Kind::Propose { .. }
                ) {
                    for other in [Step::Prepare, Step::Commit, Step::Propose] {
                        if let Some(i) = self.choices.get(&(message.round, other))
                            && let Action::Reserve {
                                message: previous, ..
                            } = &self.records[*i].action
                            && recovery_value(&previous.kind) != recovery_value(&message.kind)
                        {
                            return Err(Error::Conflict);
                        }
                    }
                }
                match &message.kind {
                    Kind::First { core: id, report } => {
                        let core = core.as_ref().ok_or(Error::Authority)?;
                        if message.round != self.slot.proposal.round
                            || authority.is_some()
                            || core.slot != self.slot
                            || core.leader != self.original_leader
                            || core.id::<H>() != *id
                            || core.followers.windows(2).any(|p| p[0] >= p[1])
                            || core
                                .followers
                                .iter()
                                .any(|p| usize::from(*p) >= 7 || *p == self.original_leader)
                            || self.owner != self.original_leader
                                && !core.followers.contains(&self.owner)
                            || self.owner == self.original_leader
                                && Core::<D>::row::<H>(report) != core.leader_report
                        {
                            return Err(Error::Context);
                        }
                        self.report_bound(report)?;
                    }
                    Kind::Select { core: selected, .. } => {
                        if message.round != self.slot.proposal.round
                            || self.owner != self.original_leader
                            || core.is_some()
                            || authority.is_none()
                        {
                            return Err(Error::Authority);
                        }
                        let Some(i) = self.choices.get(&(message.round, Step::First)) else {
                            return Err(Error::Authority);
                        };
                        if !matches!(&self.records[*i].action, Action::Reserve { message: Message { kind: Kind::First { core, .. }, .. }, .. } if core == selected)
                        {
                            return Err(Error::Conflict);
                        }
                    }
                    Kind::FastFinal(_) => {
                        if message.round != self.slot.proposal.round
                            || core.is_some()
                            || authority.is_none()
                        {
                            return Err(Error::Authority);
                        }
                    }
                    Kind::Propose { proposal, .. } => {
                        if message.round <= self.slot.proposal.round
                            || self.owner != message.leader
                            || core.is_some()
                            || authority != &Some(*proposal)
                        {
                            return Err(Error::Authority);
                        }
                    }
                    Kind::Prepare(_) | Kind::Commit(_) => {
                        if message.round <= self.slot.proposal.round
                            || core.is_some()
                            || authority.is_none()
                        {
                            return Err(Error::Authority);
                        }
                    }
                    Kind::Recover { history, report } => {
                        if message.round <= self.slot.proposal.round
                            || core.is_some()
                            || authority.is_some()
                        {
                            return Err(Error::Authority);
                        }
                        if *history != self.history::<H>(self.records.len(), message.round).0 {
                            return Err(Error::Conflict);
                        }
                        self.report_bound(report)?;
                    }
                }
                self.floor = self.floor.max(message.round);
                self.choices.insert(key, self.records.len());
            }
            Action::Retain {
                root,
                round,
                leader,
                kind,
                ..
            } => {
                self.context(*round, *leader, &authorize)?;
                if matches!(kind, Witness::Origin) != (*round == self.slot.proposal.round) {
                    return Err(Error::Authority);
                }
                if let Some(old) = self.witnesses.get(root) {
                    return if self.records[*old] == *record {
                        Ok(())
                    } else {
                        Err(Error::Conflict)
                    };
                }
                self.witnesses.insert(*root, self.records.len());
            }
            Action::Decide {
                round,
                leader,
                value,
                ..
            } => {
                self.context(*round, *leader, &authorize)?;
                if let Some(old) = self.terminal {
                    return if matches!(&self.records[old].action, Action::Decide { value: previous, .. } if previous == value)
                    {
                        Ok(())
                    } else {
                        Err(Error::Conflict)
                    };
                }
                self.terminal = Some(self.records.len());
            }
        }
        self.records.push(record.clone());
        Ok(())
    }

    /// Caller must sync this exact reservation and all required material first.
    /// Historical bytes may be retransmitted; this rejects new stale signer calls.
    pub fn sign_reserved(&self, record: &Record<D>) -> Result<Signed<S, D>, Error> {
        if self.terminal.is_some() {
            return Err(Error::Closed);
        }
        let Action::Reserve { message, .. } = &record.action else {
            return Err(Error::Reservation);
        };
        let Some(i) = self.choices.get(&(message.round, phase(&message.kind))) else {
            return Err(Error::Reservation);
        };
        if self.records[*i] != *record {
            return Err(Error::Reservation);
        }
        if message.round < self.floor {
            return Err(Error::Floor);
        }
        Signed::sign(&self.scheme, message.clone()).map_err(|_| Error::Signature)
    }

    fn report_bound(&self, report: &Option<bytes::Bytes>) -> Result<(), Error> {
        if report
            .as_ref()
            .is_some_and(|b| b.len() > self.limits.report_bytes)
        {
            Err(Error::Context)
        } else {
            Ok(())
        }
    }

    fn context(
        &self,
        round: Round,
        leader: Participant,
        authorize: &impl Fn(Round) -> Option<Participant>,
    ) -> Result<(), Error> {
        if round.epoch() != self.slot.proposal.round.epoch()
            || round < self.slot.proposal.round
            || usize::from(leader) >= 7
            || authorize(round) != Some(leader)
            || round == self.slot.proposal.round && leader != self.original_leader
        {
            return Err(Error::Context);
        }
        Ok(())
    }
    fn history<H: Hasher<Digest = D>>(
        &self,
        end: usize,
        round: Round,
    ) -> (Option<D>, Vec<Page<D>>) {
        let mut previous = None;
        let mut pages = Vec::new();
        for record in &self.records[..end] {
            let entry = match &record.action {
                Action::Reserve {
                    message,
                    authority: Some(evidence),
                    ..
                } if message.round < round && message.kind.voted_value().is_some() => {
                    Some(Entry::Authorization {
                        message: message.clone(),
                        evidence: *evidence,
                    })
                }
                Action::Retain {
                    root, round: old, ..
                } if *old < round => Some(Entry::Witness(*root)),
                _ => None,
            };
            if let Some(entry) = entry {
                let page = Page {
                    slot: self.slot.id::<H>(),
                    owner: self.owner,
                    previous,
                    entry,
                };
                previous = Some(page.id::<H>());
                pages.push(page);
            }
        }
        (previous, pages)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Step {
    First,
    Select,
    FastFinal,
    Prepare,
    Commit,
    Recover,
    Propose,
}
const fn phase<D: Digest>(kind: &Kind<D>) -> Step {
    match kind {
        Kind::First { .. } => Step::First,
        Kind::Select { .. } => Step::Select,
        Kind::FastFinal(_) => Step::FastFinal,
        Kind::Prepare(_) => Step::Prepare,
        Kind::Commit(_) => Step::Commit,
        Kind::Recover { .. } => Step::Recover,
        Kind::Propose { .. } => Step::Propose,
    }
}
const fn recovery_value<D: Digest>(kind: &Kind<D>) -> Option<D> {
    match kind {
        Kind::Prepare(value) | Kind::Commit(value) | Kind::Propose { value, .. } => Some(*value),
        _ => None,
    }
}
