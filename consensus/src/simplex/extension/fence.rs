//! Durable local signing fences for exact extension interpretations.
//!
//! One journal record contains every ancestor and child fence endorsed by a
//! final vote. No message may be signed before the operation returns success.
//! Cancellation or a storage error poisons the handle until it is reopened and
//! replayed. Recovery may retain an operation whose caller never saw success;
//! that conservatively restricts subsequent signing.
//!
//! This is an anti-equivocation store, not a recovery-proof verifier. Its caller
//! must authenticate the stable slot identities, ballots, complete value
//! commitments and recovery proof before recording a vote. In particular, a
//! higher ballot alone does not authorize changing a previously accepted value.
//! No pruning is exposed until finality and epoch-retirement rules are connected.

use bytes::BufMut;
use commonware_codec::{Buf, EncodeSize, Error as CodecError, Read, ReadExt as _, Write};
use commonware_cryptography::Digest;
use commonware_runtime::{Metrics, ReadOptions, Storage};
use commonware_storage::journal::{
    Error as JournalError,
    segmented::variable::{Config as JournalConfig, Journal},
};
use std::{collections::BTreeMap, num::NonZeroUsize};

// Storage decoding is independent of live admission settings: lowering those
// settings must reject reopening, never repair away an already signed record.
const MAX_BATCH_SLOTS: usize = 4096;

/// A previously persisted vote, not a certificate or authenticated peer status.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Accepted<D> {
    /// Recovery ballot of this vote, mapped from native rounds by the caller.
    pub ballot: u64,
    /// Commitment to the complete interpretation, including its execution parent.
    pub value: D,
}

/// Local status frozen when promising to a particular recovery ballot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Status<D> {
    /// Stable original proposal slot, independent of proposed interpretation.
    pub slot: D,
    /// Ballot to which this status belongs; it must be included in its signature.
    pub ballot: u64,
    /// Last vote before the promise, retained unchanged for retransmission.
    pub accepted: Option<Accepted<D>>,
}

/// An invalid signing transition or an unusable persistent handle.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// Empty, oversized, unsorted or duplicate slot list.
    #[error("invalid extension fence batch")]
    InvalidBatch,
    /// Retained slots exceed the configured bound; none have been evicted.
    #[error("extension fence capacity exhausted")]
    Capacity,
    /// A newer promise or vote forbids signing in this ballot.
    #[error("extension ballot is older than the durable fence")]
    Stale,
    /// A different value was already accepted in this ballot.
    #[error("conflicting extension vote in the same ballot")]
    Conflict,
    /// A status was requested after voting in the same ballot without a promise.
    #[error("extension status was not frozen before this ballot's vote")]
    Unprepared,
    /// An interrupted or failed write requires reopening and replay.
    #[error("extension fence must be reopened")]
    Poisoned,
    /// Storage failures are fatal to this handle.
    #[error(transparent)]
    Storage(#[from] JournalError),
}

#[derive(Clone, Copy, Debug)]
struct State<D> {
    ballot: u64,
    accepted: Option<Accepted<D>>,
    // None means no status was prepared in this ballot, not an empty status.
    frozen: Option<Option<Accepted<D>>>,
}

#[derive(Clone, Debug)]
enum Record<D> {
    Promise { ballot: u64, slots: Vec<D> },
    Vote { ballot: u64, values: Vec<(D, D)> },
}

impl<D: Digest> Write for Record<D> {
    fn write(&self, buf: &mut impl BufMut) {
        1u8.write(buf); // storage format version
        match self {
            Self::Promise { ballot, slots } => {
                0u8.write(buf);
                ballot.write(buf);
                slots.write(buf);
            }
            Self::Vote { ballot, values } => {
                1u8.write(buf);
                ballot.write(buf);
                values.write(buf);
            }
        }
    }
}

impl<D: Digest> EncodeSize for Record<D> {
    fn encode_size(&self) -> usize {
        2 + match self {
            Self::Promise { ballot, slots } => ballot.encode_size() + slots.encode_size(),
            Self::Vote { ballot, values } => ballot.encode_size() + values.encode_size(),
        }
    }
}

impl<D: Digest> Read for Record<D> {
    type Cfg = ();
    fn read_cfg(buf: &mut impl Buf, _: &Self::Cfg) -> Result<Self, CodecError> {
        if u8::read(buf)? != 1 {
            return Err(CodecError::Invalid("extension fence", "unknown version"));
        }
        let kind = u8::read(buf)?;
        let ballot = u64::read(buf)?;
        match kind {
            0 => Ok(Self::Promise {
                ballot,
                slots: Vec::<D>::read_cfg(buf, &((1..=MAX_BATCH_SLOTS).into(), ()))?,
            }),
            1 => Ok(Self::Vote {
                ballot,
                values: Vec::<(D, D)>::read_cfg(buf, &((1..=MAX_BATCH_SLOTS).into(), ((), ())))?,
            }),
            _ => Err(CodecError::Invalid("extension fence", "unknown record")),
        }
    }
}

/// A single-owner journal of local promises and accepted extension values.
///
/// Use a dedicated partition for each validator identity and extension domain.
/// Slot digests must bind that domain, epoch and original proposal. Never reuse
/// a partition with a different identity or erase it while that identity can sign.
pub struct Fence<E: Storage + Metrics, D: Digest> {
    journal: Option<Journal<E, Record<D>>>,
    states: BTreeMap<D, State<D>>,
    max_slots: NonZeroUsize,
    max_batch: NonZeroUsize,
}

impl<E: Storage + Metrics, D: Digest> Fence<E, D> {
    /// Opens and replays every retained record before enabling signing decisions.
    ///
    /// `cfg.codec_config` bounds the number of slots in a single atomic record.
    /// `max_slots` bounds retained slot state; changing it must not discard history.
    pub async fn open(
        context: E,
        cfg: JournalConfig<NonZeroUsize>,
        max_slots: NonZeroUsize,
        replay_buffer: NonZeroUsize,
    ) -> Result<Self, Error> {
        let max_batch = cfg.codec_config;
        if max_batch.get() > MAX_BATCH_SLOTS {
            return Err(Error::InvalidBatch);
        }
        let journal = Journal::init(
            context,
            JournalConfig {
                partition: cfg.partition,
                compression: cfg.compression,
                codec_config: (),
                page_cache: cfg.page_cache,
                write_buffer: cfg.write_buffer,
            },
        )
        .await?;
        let mut replay = journal
            .replay(0, 0, replay_buffer, ReadOptions::DONT_CACHE)
            .await?;
        let mut this = Self {
            journal: None,
            states: BTreeMap::new(),
            max_slots,
            max_batch,
        };
        while let Some(item) = replay.next().await {
            let (section, _, _, record) = item?;
            if section != 0 {
                return Err(Error::InvalidBatch);
            }
            this.validate(&record)?;
            this.apply(&record);
        }
        this.journal = Some(replay.finish()?);
        Ok(this)
    }

    fn validate_slots(&self, slots: impl Iterator<Item = D> + Clone) -> Result<(), Error> {
        let mut previous = None;
        let mut count = 0;
        let mut new = 0;
        for slot in slots {
            if previous.is_some_and(|prev| prev >= slot) {
                return Err(Error::InvalidBatch);
            }
            previous = Some(slot);
            count += 1;
            new += usize::from(!self.states.contains_key(&slot));
        }
        if count == 0 || count > self.max_batch.get() {
            return Err(Error::InvalidBatch);
        }
        if self.states.len().saturating_add(new) > self.max_slots.get() {
            return Err(Error::Capacity);
        }
        Ok(())
    }

    fn validate(&self, record: &Record<D>) -> Result<(), Error> {
        match record {
            Record::Promise { ballot, slots } => {
                if *ballot == 0 {
                    return Err(Error::InvalidBatch);
                }
                self.validate_slots(slots.iter().copied())?;
                for slot in slots {
                    if let Some(state) = self.states.get(slot) {
                        if *ballot < state.ballot {
                            return Err(Error::Stale);
                        }
                        if *ballot == state.ballot && state.frozen.is_none() {
                            return Err(Error::Unprepared);
                        }
                    }
                }
            }
            Record::Vote { ballot, values } => {
                self.validate_slots(values.iter().map(|(slot, _)| *slot))?;
                for (slot, value) in values {
                    if let Some(state) = self.states.get(slot) {
                        if *ballot < state.ballot {
                            return Err(Error::Stale);
                        }
                        if state
                            .accepted
                            .is_some_and(|old| old.ballot == *ballot && old.value != *value)
                        {
                            return Err(Error::Conflict);
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn apply(&mut self, record: &Record<D>) {
        match record {
            Record::Promise { ballot, slots } => {
                for slot in slots {
                    let state = self.states.entry(*slot).or_insert(State {
                        ballot: 0,
                        accepted: None,
                        frozen: None,
                    });
                    if *ballot > state.ballot {
                        state.ballot = *ballot;
                        state.frozen = Some(state.accepted);
                    }
                }
            }
            Record::Vote { ballot, values } => {
                for (slot, value) in values {
                    let state = self.states.entry(*slot).or_insert(State {
                        ballot: *ballot,
                        accepted: None,
                        frozen: None,
                    });
                    if *ballot > state.ballot {
                        state.ballot = *ballot;
                        state.frozen = None;
                    }
                    state.accepted = Some(Accepted {
                        ballot: *ballot,
                        value: *value,
                    });
                }
            }
        }
    }

    async fn persist(&mut self, record: Record<D>) -> Result<(), Error> {
        if self.journal.is_none() {
            return Err(Error::Poisoned);
        }
        self.validate(&record)?;
        // Taking the owned journal also fences cancellation between append and sync.
        let journal = self.journal.take().ok_or(Error::Poisoned)?;
        let (journal, _, _) = journal.append(0, &record).await?;
        let journal = journal.sync(0).await?;
        self.apply(&record);
        self.journal = Some(journal);
        Ok(())
    }

    /// Durably promises against lower ballots, then returns frozen local statuses.
    ///
    /// The caller must bind every returned field, validator identity and domain in
    /// its authenticated response. Repeating a promise returns its original status
    /// even if a vote was subsequently recorded in the same ballot.
    pub async fn promise(&mut self, ballot: u64, slots: Vec<D>) -> Result<Vec<Status<D>>, Error> {
        self.persist(Record::Promise {
            ballot,
            slots: slots.clone(),
        })
        .await?;
        Ok(slots
            .into_iter()
            .map(|slot| Status {
                slot,
                ballot,
                accepted: self.states[&slot].frozen.expect("validated promise"),
            })
            .collect())
    }

    /// Records all interpretations endorsed by one vote before it can be signed.
    ///
    /// All slots use the target ballot of the same signed envelope. Values must
    /// be sorted by stable slot and have no duplicates. The caller
    /// must verify the recovery proof for every changed interpretation and native
    /// ancestry/nullification rules first. Success provides no finality authority.
    pub async fn vote(&mut self, ballot: u64, values: Vec<(D, D)>) -> Result<(), Error> {
        self.persist(Record::Vote { ballot, values }).await
    }
}

#[cfg(test)]
#[path = "fence/tests.rs"]
mod tests;
