//! Native General voter and interpretation-only recovery for included ancestors.

use super::{
    FinalVote, Finalization, FirstVote, General, g,
    voting_wal::{Event, Wal},
};
use crate::{
    Epochable, Viewable,
    simplex::{
        phase2::voting::{Participation, Voting},
        scheme,
        types::{Context as NativeContext, Notarize, Proposal},
    },
    types::{Epoch, Participant, Round, View},
};
use bytes::Bytes;
use commonware_codec::{Decode as _, Encode as _, EncodeSize};
use commonware_cryptography::{Digest, Hasher};
use commonware_parallel::Sequential;
use commonware_utils::sync::Mutex;
use rand_core::CryptoRng;
use std::{
    collections::{BTreeMap, btree_map::Entry},
    sync::Arc,
    time::{Duration, SystemTime},
};

/// Explicit native-adapter retention budgets. Exhaustion retires the owner;
/// accepted authority is never evicted to make room for a new alias.
#[derive(Clone, Copy, Debug)]
pub struct Resources {
    /// Maximum retained exact Slot descriptors and ledgers per native round.
    pub slots: usize,
    /// Total immutable input, checked body and Origin handles in the context.
    pub handles: usize,
    /// Canonical retained bytes; container counts separately bound overhead.
    pub bytes: usize,
    /// Complete logical issuance history, including unsigned choices and receipts.
    pub records_per_slot: usize,
}

/// An exact, application-checked capture. It is not native signing permission.
#[derive(Clone, Debug)]
pub struct FirstInput<D: Digest> {
    core: g::Core<D>,
    input: D,
    owner: Participant,
    row: Option<g::First<D>>,
    route_scope: Option<D>,
    limits: g::Limits,
    id: D,
    bytes: usize,
}
impl<D: Digest> FirstInput<D> {
    /// Validates the already captured optional fields without waiting or sampling
    /// them again. The caller supplies the real native context and SDK predicate.
    #[allow(clippy::too_many_arguments)]
    pub fn new<H: Hasher<Digest = D>, S: scheme::Scheme<D>>(
        scheme: &S,
        slot: g::Slot<D>,
        native: &NativeContext<D, S::PublicKey>,
        input: D,
        report: Option<Bytes>,
        preference: Option<Bytes>,
        limits: g::Limits,
        validate: impl FnOnce(&g::First<D>) -> bool,
    ) -> Result<Self, g::Error> {
        let (core, owner) = Self::context::<H, S>(scheme, slot, native, limits)?;
        if report
            .as_ref()
            .is_some_and(|b| b.len() > limits.report_bytes)
            || preference
                .as_ref()
                .is_some_and(|b| b.len() > limits.order_bytes)
        {
            return Err(g::Error::Limit);
        }
        let in_core = owner == core.leader || core.followers.contains(&owner);
        if (!in_core || owner == core.leader) && (report.is_some() || preference.is_some()) {
            return Err(g::Error::Context);
        }
        let row = in_core.then(|| g::First {
            core: core.id::<H>(),
            input,
            owner,
            report: report.map(|b| Bytes::copy_from_slice(&b)),
            preference: preference.map(|b| Bytes::copy_from_slice(&b)),
        });
        if row.as_ref().is_some_and(|r| !validate(r)) {
            return Err(g::Error::Policy);
        }
        Ok(Self::capture::<H>(core, input, owner, row, limits, None))
    }

    /// Register an application-reserved logical FIRST for any validator,
    /// including a signed absence. The native owner checks the current leader,
    /// proposal and signer independently and journals the exact choice before signing.
    pub fn from_route<H: Hasher<Digest = D>, S: scheme::Scheme<D>>(
        scheme: &S,
        slot: g::Slot<D>,
        native: &NativeContext<D, S::PublicKey>,
        input: D,
        message: g::Message<D>,
        limits: g::Limits,
        validate: impl FnOnce(&g::First<D>) -> bool,
    ) -> Result<Self, g::Error> {
        let (core, owner) = Self::context::<H, S>(scheme, slot, native, limits)?;
        if message.encode_size() > g::MAX_FIRST_BYTES {
            return Err(g::Error::Limit);
        }
        let g::Kind::First(mut row) = message.kind else {
            return Err(g::Error::Context);
        };
        let scope = row.core;
        if scope == core.id::<H>()
            || message.round != core.slot.proposal.round
            || message.leader != core.leader
            || row.input != input
            || row.owner != owner
            || row.preference.is_some()
            || message.slot != g::First::route_slot::<H>(&core.slot, scope, input)
        {
            return Err(g::Error::Context);
        }
        if row
            .report
            .as_ref()
            .is_some_and(|b| b.len() > limits.report_bytes)
        {
            return Err(g::Error::Limit);
        }
        if !validate(&row) {
            return Err(g::Error::Policy);
        }
        row.report = row.report.map(|bytes| Bytes::copy_from_slice(&bytes));
        Ok(Self::capture::<H>(
            core,
            input,
            owner,
            Some(row),
            limits,
            Some(scope),
        ))
    }

    fn context<H: Hasher<Digest = D>, S: scheme::Scheme<D>>(
        scheme: &S,
        slot: g::Slot<D>,
        native: &NativeContext<D, S::PublicKey>,
        limits: g::Limits,
    ) -> Result<(g::Core<D>, Participant), g::Error> {
        let owner = scheme.me().ok_or(g::Error::Identity)?;
        let leader = scheme
            .participants()
            .iter()
            .position(|k| k == &native.leader)
            .ok_or(g::Error::Identity)?;
        let core = g::Core::derive::<H, S>(
            scheme,
            slot,
            Participant::new(u32::try_from(leader).map_err(|_| g::Error::Identity)?),
        )?;
        limits.validate::<S, D>(&core)?;
        if !native_matches::<H, S, D>(&core, scheme, &core.slot.proposal, native) {
            return Err(g::Error::Context);
        }
        Ok((core, owner))
    }

    fn capture<H: Hasher<Digest = D>>(
        core: g::Core<D>,
        input: D,
        owner: Participant,
        row: Option<g::First<D>>,
        limits: g::Limits,
        route_scope: Option<D>,
    ) -> Self {
        let captured = match &row {
            Some(r) => g::Message {
                slot: route_scope.map_or_else(
                    || core.slot.id::<H>(),
                    |scope| g::First::route_slot::<H>(&core.slot, scope, input),
                ),
                round: core.slot.proposal.round,
                leader: core.leader,
                kind: g::Kind::First(r.clone()),
            }
            .encode(),
            None => Bytes::new(),
        };
        let bytes = core.encode_size() + captured.len() + 64;
        let id = H::hash(&[
            b"_COMMONWARE_CONSENSUS_G1_NATIVE_CAPTURE_V1",
            &core.encode(),
            &input.encode(),
            &owner.encode(),
            &[u8::from(row.is_some())],
            &captured,
        ]);
        Self {
            core,
            input,
            owner,
            row,
            route_scope,
            limits,
            id,
            bytes,
        }
    }
    /// Cohort derived from the supplied actual native leader and roster.
    pub const fn core(&self) -> &g::Core<D> {
        &self.core
    }
    /// Exact application input commitment, independently of planner eligibility.
    pub const fn input(&self) -> D {
        self.input
    }
    /// Local signer bound to this capture, including when its FIRST row is absent.
    pub const fn owner(&self) -> Participant {
        self.owner
    }
    /// Frozen checked row, or None only for an outside-Core owner.
    pub const fn row(&self) -> Option<&g::First<D>> {
        self.row.as_ref()
    }
    /// Profile field limits used by the trusted application check.
    pub const fn limits(&self) -> g::Limits {
        self.limits
    }
    fn accepts(&self, row: &g::First<D>) -> bool {
        self.row.as_ref() == Some(row)
    }
}

/// Complete checked pre-SELECT material, shared without a second body store.
#[derive(Clone, Debug)]
pub struct Selection<S: scheme::Scheme<D>, D: Digest> {
    body: g::OriginBody<S, D>,
    checked: g::VerifiedBody<D>,
}
impl<S: scheme::Scheme<D>, D: Digest> Selection<S, D> {
    /// Exact pre-SELECT material, without a fabricated leader endorsement.
    pub const fn body(&self) -> &g::OriginBody<S, D> {
        &self.body
    }
    /// Private-constructor policy result for these exact immutable bytes.
    pub const fn checked(&self) -> &g::VerifiedBody<D> {
        &self.checked
    }
}
#[derive(Clone, Debug)]
enum Command<D: Digest> {
    Select(D),
    Wish {
        slot: D,
        predecessor: D,
    },
    Ballot {
        slot: D,
        evidence: D,
    },
    HigherHistory {
        slot: D,
        entry: D,
        report: Option<Bytes>,
    },
    InitialHistory {
        slot: D,
        input: D,
        owner: Participant,
        report: Option<Bytes>,
    },
}

/// Original SELECT request. The native Readiness handle also uses this envelope
/// internally for an initial recovery history request.
#[derive(Clone, Debug)]
pub struct SelectRequest<D: Digest> {
    command: Command<D>,
    proposal: Proposal<D>,
}
impl<D: Digest> SelectRequest<D> {
    /// References an already retained checked body through the existing mailbox.
    pub fn new<S: scheme::Scheme<D>>(selection: &Selection<S, D>) -> Self {
        Self {
            command: Command::Select(selection.checked.body()),
            proposal: selection.body.core.slot.proposal.clone(),
        }
    }
    pub(crate) fn initial_history<H: Hasher<Digest = D>>(
        capture: &FirstInput<D>,
        report: Option<Bytes>,
    ) -> Option<Self> {
        if report
            .as_ref()
            .is_some_and(|r| r.len() > capture.limits.report_bytes)
        {
            return None;
        }
        Some(Self {
            command: Command::InitialHistory {
                slot: capture.core.slot.id::<H>(),
                input: capture.input,
                owner: capture.owner,
                report,
            },
            proposal: capture.core.slot.proposal.clone(),
        })
    }
    pub(crate) fn higher<H: Hasher<Digest = D>>(
        capture: &FirstInput<D>,
        entry: D,
        report: Option<Bytes>,
    ) -> Option<Self> {
        if report
            .as_ref()
            .is_some_and(|raw| raw.len() > capture.limits.report_bytes)
        {
            return None;
        }
        Some(Self {
            command: Command::HigherHistory {
                slot: capture.core.slot.id::<H>(),
                entry,
                report,
            },
            proposal: capture.core.slot.proposal.clone(),
        })
    }
    pub(crate) fn wish<H: Hasher<Digest = D>>(capture: &FirstInput<D>, predecessor: D) -> Self {
        Self {
            command: Command::Wish {
                slot: capture.core.slot.id::<H>(),
                predecessor,
            },
            proposal: capture.core.slot.proposal.clone(),
        }
    }
    pub(crate) fn ballot<H: Hasher<Digest = D>>(capture: &FirstInput<D>, evidence: D) -> Self {
        Self {
            command: Command::Ballot {
                slot: capture.core.slot.id::<H>(),
                evidence,
            },
            proposal: capture.core.slot.proposal.clone(),
        }
    }
    const fn recovery_slot(&self) -> Option<D> {
        match self.command {
            Command::Select(_) => None,
            Command::HigherHistory { slot, .. }
            | Command::InitialHistory { slot, .. }
            | Command::Wish { slot, .. }
            | Command::Ballot { slot, .. } => Some(slot),
        }
    }
    /// Original native proposal view, not a later recovery ballot.
    pub const fn view(&self) -> View {
        self.proposal.round.view()
    }
}

/// Read one original from the exact published initial RECOVER history.
pub struct HistoryQuery<D: Digest> {
    proposal: Proposal<D>,
    slot: D,
    input: D,
    owner: Participant,
    item: HistoryItem<D>,
}

enum HistoryItem<D> {
    Notice,
    Entry(D),
    Page(D, usize),
    Verification(D),
}
impl<D: Digest> HistoryQuery<D> {
    /// Read a zero-based page, or the exact original entry proof when page is None.
    pub fn new<H: Hasher<Digest = D>>(input: &FirstInput<D>, head: D, page: Option<usize>) -> Self {
        Self {
            proposal: input.core.slot.proposal.clone(),
            slot: input.core.slot.id::<H>(),
            input: input.input,
            owner: input.owner,
            item: page.map_or(HistoryItem::Entry(head), |i| HistoryItem::Page(head, i)),
        }
    }
    /// Look up a previously published notice, including after a lost reply.
    pub fn published<H: Hasher<Digest = D>>(input: &FirstInput<D>) -> Self {
        Self {
            proposal: input.core.slot.proposal.clone(),
            slot: input.core.slot.id::<H>(),
            input: input.input,
            owner: input.owner,
            item: HistoryItem::Notice,
        }
    }
    /// Obtain the read-only verification scope of the local issuance owner for
    /// this published history head. A newly opened voter has a new scope.
    pub fn verification<H: Hasher<Digest = D>>(input: &FirstInput<D>, head: D) -> Self {
        Self {
            item: HistoryItem::Verification(head),
            ..Self::published::<H>(input)
        }
    }
    /// Original native view used for read-only lookup.
    pub const fn view(&self) -> View {
        self.proposal.round.view()
    }
}
/// Original evidence returned from a retained native ledger. Callers verify it
/// against the signed history before making any recovery decision.
pub enum HistoryMaterial<S: commonware_cryptography::certificate::Scheme, D: Digest> {
    /// Previously journaled outbox bytes, decoded without another signer call.
    Notice(g::Signed<S, D>),
    /// Local verification handle only. Never serialized or returned to a peer.
    Verification(g::VerificationContext<S>),
    /// The native NQC and its original recovery entry target.
    Entry(g::entry::Proof<S, D>),
    /// One of the hash-linked pages covered by the signed head.
    Page(g::issuance::HistoryPage<D>),
}

#[derive(Clone)]
struct Bootstrap<D: Digest> {
    route_scope: Option<D>,
    core: g::Core<D>,
    input: D,
    owner: Participant,
}
struct Index<S: scheme::Scheme<D>, D: Digest> {
    slots: BTreeMap<D, Bootstrap<D>>,
    slots_by_view: BTreeMap<View, Vec<D>>,
    firsts: BTreeMap<D, FirstInput<D>>,
    bodies: BTreeMap<D, Arc<Selection<S, D>>>,
    origins: BTreeMap<D, g::normal::Assembly<S, D>>,
    bytes: usize,
}
/// Verify a durably retained recovery graph under the deployment's registered
/// policy in the supplied local scope. The host must hydrate original evidence
/// and replay its application Builds before starting the voter. A cache miss
/// refuses issuance and cannot erase a reservation during journal replay.
pub type RecoveryEvidence<S, D> = dyn Fn(&mut dyn CryptoRng, &g::VerificationContext<S>, D) -> Option<g::recovery::Verified<D>>
    + Send
    + Sync;

/// Durable content-addressed entry provenance supplied by the host. Native
/// authenticates each reachable node under its own verifier and resource limits.
pub type EntryReader<S, D> = dyn Fn(D) -> Option<BTreeMap<D, g::entry::Proof<S, D>>> + Send + Sync;
/// Trusted immutable deployment and a bounded index of checked application
/// handles. The index owns no signer, issuance ledger, body archive or actor.
pub struct Context<S: scheme::Scheme<D>, D: Digest> {
    epoch: Epoch,
    profile: D,
    domain: D,
    genesis: D,
    limits: g::Limits,
    resources: Resources,
    index: Arc<Mutex<Index<S, D>>>,
    recovery_evidence: Option<Arc<RecoveryEvidence<S, D>>>,
    recovery_wait: Option<Duration>,
    entry_reader: Option<(g::entry::Bounds, Arc<EntryReader<S, D>>)>,
}
impl<S: scheme::Scheme<D>, D: Digest> Clone for Context<S, D> {
    fn clone(&self) -> Self {
        Self {
            epoch: self.epoch,
            profile: self.profile,
            domain: self.domain,
            genesis: self.genesis,
            limits: self.limits,
            resources: self.resources,
            index: self.index.clone(),
            recovery_evidence: self.recovery_evidence.clone(),
            recovery_wait: self.recovery_wait,
            entry_reader: self.entry_reader.clone(),
        }
    }
}
impl<S: scheme::Scheme<D>, D: Digest> Context<S, D>
where
    S::Certificate: g::normal::CertificateSigners,
{
    /// Configure before startup. Limits are additionally validated for each
    /// actual derived Core; there is no fixed-seven default configuration.
    pub fn new(
        epoch: Epoch,
        profile: D,
        domain: D,
        genesis: D,
        limits: g::Limits,
        resources: Resources,
    ) -> Result<Self, g::Error> {
        if resources.slots == 0
            || resources.handles == 0
            || resources.bytes == 0
            || resources.records_per_slot < 4
        {
            return Err(g::Error::Limit);
        }
        Ok(Self {
            epoch,
            profile,
            domain,
            genesis,
            limits,
            resources,
            recovery_evidence: None,
            recovery_wait: None,
            entry_reader: None,
            index: Arc::new(Mutex::new(Index {
                slots: BTreeMap::new(),
                slots_by_view: BTreeMap::new(),
                firsts: BTreeMap::new(),
                bodies: BTreeMap::new(),
                origins: BTreeMap::new(),
                bytes: 0,
            })),
        })
    }
    /// Set the trusted first recovery attempt's timeout. The native view timers
    /// are independent. Cold startup arms a new full wait for an unreserved WISH.
    pub fn with_initial_recovery_timeout(mut self, wait: Duration) -> Result<Self, g::Error> {
        if wait.is_zero() {
            return Err(g::Error::Context);
        }
        self.recovery_wait = Some(wait);
        Ok(self)
    }
    /// Install the durable successor-entry resolver used during issuance and WAL replay.
    pub fn with_recovery_entries(
        mut self,
        bounds: g::entry::Bounds,
        reader: Arc<EntryReader<S, D>>,
    ) -> Self {
        self.entry_reader = Some((bounds, reader));
        self
    }
    /// Install the local durable evidence reader before constructing the voter.
    pub fn with_recovery_evidence(mut self, reader: Arc<RecoveryEvidence<S, D>>) -> Self {
        self.recovery_evidence = Some(reader);
        self
    }
    fn slot(&self, slot: &g::Slot<D>) -> bool {
        slot.profile == self.profile
            && slot.domain == self.domain
            && slot.proposal.epoch() == self.epoch
            && match slot.parent {
                g::NativeParent::Genesis(d) => {
                    slot.proposal.parent == View::new(0) && d == self.genesis
                }
                g::NativeParent::Proposal { round, .. } => {
                    round.epoch() == self.epoch && round.view() == slot.proposal.parent
                }
            }
    }
    fn capacity(&self, i: &Index<S, D>, bytes: usize) -> Result<usize, g::Error> {
        let handles = i.firsts.len() + i.bodies.len() + i.origins.len();
        if handles >= self.resources.handles {
            return Err(g::Error::Limit);
        }
        i.bytes
            .checked_add(bytes)
            .filter(|n| *n <= self.resources.bytes)
            .ok_or(g::Error::Limit)
    }
    /// Publish a locally checked exact row/metadata handle. Multiple unchosen
    /// captures may coexist; only the native ledger freezes the once choice.
    pub fn publish_input<H: Hasher<Digest = D>>(
        &self,
        input: FirstInput<D>,
    ) -> Result<(), g::Error> {
        if !self.slot(&input.core.slot) || input.limits != self.limits {
            return Err(g::Error::Context);
        }
        let slot = input.core.slot.id::<H>();
        let mut i = self.index.lock();
        if i.firsts.contains_key(&input.id) {
            return Ok(());
        }
        if let Some(old) = i.slots.get(&slot) {
            if old.core != input.core
                || old.input != input.input
                || old.owner != input.owner
                || old.route_scope != input.route_scope
            {
                return Err(g::Error::Context);
            }
        } else if i.slots.len() >= self.resources.slots {
            return Err(g::Error::Limit);
        }
        let used = self.capacity(&i, input.bytes)?;
        if !i.slots.contains_key(&slot) {
            i.slots_by_view
                .entry(input.core.slot.proposal.view())
                .or_default()
                .push(slot);
        }
        i.slots.entry(slot).or_insert_with(|| Bootstrap {
            route_scope: input.route_scope,
            core: input.core.clone(),
            input: input.input,
            owner: input.owner,
        });
        i.bytes = used;
        i.firsts.insert(input.id, input);
        Ok(())
    }
    /// Retain an exact checked body before local SELECT admission. Raw peer
    /// bytes alone cannot create this entry. Accepted handles are not evicted.
    pub fn publish_selection<H: Hasher<Digest = D>>(
        &self,
        body: g::OriginBody<S, D>,
        checked: g::VerifiedBody<D>,
    ) -> Result<Arc<Selection<S, D>>, g::Error> {
        if body.core.followers.len() > 63
            || body.firsts.len() > 64
            || body.build.len() > self.limits.build_bytes
            || body.material.len() > self.limits.material_bytes
            || body
                .firsts
                .iter()
                .any(|r| r.encode_size() > g::MAX_FIRST_BYTES)
            || body.encode_size() > self.limits.origin_bytes
            || body.encode_size() > g::MAX_EVIDENCE_BYTES
        {
            return Err(g::Error::Limit);
        }
        if !self.slot(&body.core.slot)
            || checked.limits() != self.limits
            || checked.slot() != body.core.slot.id::<H>()
            || checked.body() != body.id::<H>()
            || checked.decision() != body.decision.id::<H>()
        {
            return Err(g::Error::Context);
        }
        // Do bounded copying outside the handle-index lock: published input
        // lookups must not wait for another component's material encoding.
        let compact =
            g::OriginBody::decode_cfg(body.encode(), &self.limits).map_err(|_| g::Error::Limit)?;
        let mut i = self.index.lock();
        let bootstrap = i.slots.get(&checked.slot()).ok_or(g::Error::Context)?;
        if bootstrap.route_scope != checked.route_scope()
            || bootstrap.core != body.core
            || bootstrap.input != body.decision.input
        {
            return Err(g::Error::Context);
        }
        if let Some(old) = i.bodies.get(&checked.body()) {
            return Ok(old.clone());
        }
        let used = self.capacity(&i, body.encode_size())?;
        let value = Arc::new(Selection {
            body: compact,
            checked,
        });
        i.bytes = used;
        i.bodies.insert(value.checked.body(), value.clone());
        Ok(value)
    }
    /// Retain an immutable full-policy Origin/NQC capability. A same-decision
    /// alias never overwrites an existing exact authority handle.
    pub fn publish_assembly<H: Hasher<Digest = D>>(
        &self,
        assembly: g::normal::Assembly<S, D>,
    ) -> Result<(), g::Error> {
        if !self.slot(&assembly.core().slot) || assembly.limits() != self.limits {
            return Err(g::Error::Context);
        }
        let id = assembly.origin().id::<H>();
        let mut i = self.index.lock();
        let b = i
            .slots
            .get(&assembly.core().slot.id::<H>())
            .ok_or(g::Error::Context)?;
        if b.route_scope != assembly.route_authority().and_then(|cap| cap.route_scope())
            || b.core != *assembly.core()
            || b.input != assembly.input()
        {
            return Err(g::Error::Context);
        }
        if i.origins.contains_key(&id) {
            return Ok(());
        }
        i.bytes = self.capacity(&i, assembly.retained_bytes())?;
        i.origins.insert(id, assembly);
        Ok(())
    }
    fn bootstrap(&self, slot: D) -> Option<Bootstrap<D>> {
        self.index.lock().slots.get(&slot).cloned()
    }
    fn first(&self, r: &g::issuance::Record<D>) -> Option<FirstInput<D>> {
        self.index
            .lock()
            .firsts
            .values()
            .find(|i| {
                i.core == *r.core()
                    && i.input == r.input()
                    && i.owner == r.owner()
                    && match r.action() {
                        g::issuance::Action::NoFirst => i.row.is_none(),
                        g::issuance::Action::Reserve {
                            message:
                                g::Message {
                                    kind: g::Kind::First(row),
                                    ..
                                },
                            ..
                        } => i.accepts(row),
                        _ => false,
                    }
            })
            .cloned()
    }
    fn selection(&self, id: D) -> Option<Arc<Selection<S, D>>> {
        self.index.lock().bodies.get(&id).cloned()
    }
    fn assembly(&self, id: D) -> Option<g::normal::Assembly<S, D>> {
        self.index.lock().origins.get(&id).cloned()
    }
}

/// Observable native and G1 signed subjects. Equality excludes Origin aliases
/// and retrieval hints; raw subject extraction grants no fresh signing authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalSubject<D: Digest> {
    native: crate::simplex::extension::vote::Statement<D>,
    agreement: g::Message<D>,
}
impl<D: Digest> FinalSubject<D> {
    /// Extracts the semantic subject from fully checked immutable material.
    pub fn new<H: Hasher<Digest = D>, S: scheme::Scheme<D>>(a: &g::normal::Assembly<S, D>) -> Self
    where
        S::Certificate: g::normal::CertificateSigners,
    {
        Self {
            native: g::normal::subject::<H>(a.decision()),
            agreement: g::Message {
                slot: a.core().slot.id::<H>(),
                round: a.proposal().round,
                leader: a.core().leader,
                kind: g::Kind::Phase {
                    phase: g::Phase::FastFinal,
                    decision: a.decision().id::<H>(),
                },
            },
        }
    }
}

struct SlotLedger<S: scheme::Scheme<D>, D: Digest> {
    ledger: g::issuance::State<S, D>,
    first: Option<g::issuance::Record<D>>,
    first_vote: Option<FirstVote<S, D>>,
    select: Option<g::issuance::Record<D>>,
    history: Option<(Wal<S, D>, g::entry::Proof<S, D>)>,
    history_from_replay: bool,
    replayed_ballots: std::collections::BTreeSet<D>,
    normal: Option<g::normal::Reservation<D>>,
}
/// The sole round-owned collection of actual issuance ledgers, one per exact Slot.
pub struct RecoveryState<S: scheme::Scheme<D>, D: Digest> {
    slots: BTreeMap<D, SlotLedger<S, D>>,
    observed: BTreeMap<D, SystemTime>,
}
impl<S: scheme::Scheme<D>, D: Digest> RecoveryState<S, D> {
    const EMPTY: Self = Self {
        observed: BTreeMap::new(),
        slots: BTreeMap::new(),
    };
}

// A checked body and native context may arrive in either order. Arm once on
// their first joint observation. Queries never postpone an established deadline.
#[allow(clippy::too_many_arguments)]
fn observe_slot<H, S, D>(
    scheme: &S,
    context: &Context<S, D>,
    state: &mut RecoveryState<S, D>,
    p: &Proposal<D>,
    native: &NativeContext<D, S::PublicKey>,
    now: SystemTime,
    timeout: Duration,
    requested: Option<D>,
) -> bool
where
    H: Hasher<Digest = D>,
    S: scheme::Scheme<D>,
    D: Digest,
{
    let candidates: Vec<_> = {
        let registry = context.index.lock();
        let ids = requested.as_ref().map_or_else(
            || {
                registry
                    .slots_by_view
                    .get(&p.view())
                    .map(Vec::as_slice)
                    .unwrap_or_default()
            },
            std::slice::from_ref,
        );
        ids.iter()
            .filter_map(|id| registry.slots.get(id).map(|b| (*id, b.clone())))
            .collect()
    };
    let mut due = false;
    for (id, b) in candidates {
        if scheme.me() != Some(b.owner) || !native_matches::<H, S, D>(&b.core, scheme, p, native) {
            continue;
        }
        let first = *state.observed.entry(id).or_insert(now);
        due |= now
            .duration_since(first)
            .is_ok_and(|elapsed| elapsed >= timeout);
    }
    due
}

fn native_matches<H: Hasher<Digest = D>, S: scheme::Scheme<D>, D: Digest>(
    core: &g::Core<D>,
    s: &S,
    p: &Proposal<D>,
    n: &NativeContext<D, S::PublicKey>,
) -> bool {
    if p != &core.slot.proposal
        || n.round != p.round
        || n.parent.0 != p.parent
        || s.participants().get(usize::from(core.leader)) != Some(&n.leader)
    {
        return false;
    }
    let parent = if p.parent == View::new(0) {
        g::NativeParent::Genesis(n.parent.1)
    } else {
        g::NativeParent::Proposal {
            round: Round::new(p.epoch(), p.parent),
            digest: n.parent.1,
        }
    };
    core.slot.parent == parent
        && g::Core::derive::<H, S>(s, core.slot.clone(), core.leader)
            .is_ok_and(|expected| expected == *core)
}

fn ledger<'a, H: Hasher<Digest = D>, S: scheme::Scheme<D>, D: Digest>(
    s: &S,
    c: &Context<S, D>,
    state: &'a mut RecoveryState<S, D>,
    record: &g::issuance::Record<D>,
    replay: bool,
) -> Option<&'a mut SlotLedger<S, D>>
where
    S::Certificate: g::normal::CertificateSigners,
{
    let id = record.slot().id::<H>();
    let b = c.bootstrap(id)?;
    if b.core != *record.core()
        || b.input != record.input()
        || b.owner != record.owner()
        || s.me() != Some(b.owner)
        || !c.slot(record.slot())
    {
        return None;
    }
    if !state.slots.contains_key(&id) {
        assert!(
            state.slots.len() < c.resources.slots,
            "General ledger capacity exhausted"
        );
        let actual = if replay {
            g::issuance::State::for_replay::<H>(s.clone(), b.core, b.input, c.limits)
        } else {
            g::issuance::State::new::<H>(s.clone(), b.core, b.input, c.limits)
        }
        .ok()?;
        state.slots.insert(
            id,
            SlotLedger {
                ledger: actual,
                first: None,
                first_vote: None,
                select: None,
                history: None,
                history_from_replay: false,
                replayed_ballots: Default::default(),
                normal: None,
            },
        );
    }
    state.slots.get_mut(&id)
}

fn room<S: scheme::Scheme<D>, D: Digest>(c: &Context<S, D>, l: &SlotLedger<S, D>, extra: usize) {
    assert!(
        l.ledger
            .records()
            .len()
            .checked_add(extra)
            .is_some_and(|n| n <= c.resources.records_per_slot),
        "General issuance history capacity exhausted"
    );
}

fn replay_room<S: scheme::Scheme<D>, D: Digest>(
    c: &Context<S, D>,
    l: &SlotLedger<S, D>,
    records: &[&g::issuance::Record<D>],
) {
    let extra = records
        .iter()
        .enumerate()
        .filter(|(index, record)| {
            !l.ledger.records().contains(record) && !records[..*index].contains(record)
        })
        .count();
    room(c, l, extra);
}

impl<S, D, H> Voting<S, D> for General<H>
where
    S: scheme::Scheme<D>,
    S::Certificate: g::normal::CertificateSigners,
    D: Digest,
    H: Hasher<Digest = D>,
{
    const RESERVE_NOTARIZE: bool = true;
    const JOINT_FINALIZE: bool = true;
    const RETAIN_HISTORY: bool = true;
    const REQUIRE_PARENT_INTERPRETATION: bool = false;
    const REQUIRE_FINALIZATION_ADMISSION: bool = true;
    type FirstInput = FirstInput<D>;
    type Context = Context<S, D>;
    type RecoveryState = RecoveryState<S, D>;
    const EMPTY_RECOVERY: Self::RecoveryState = RecoveryState::EMPTY;
    type FinalSubject = FinalSubject<D>;
    fn allows_original(state: &Self::RecoveryState) -> bool {
        state.slots.values().all(|slot| slot.history.is_none())
    }
    fn recovery_proposal(r: &Wal<S, D>) -> &Proposal<D> {
        r.proposal()
    }
    fn recovery_context(c: &Self::Context, r: &Wal<S, D>) -> bool {
        c.slot(r.record().slot())
    }
    fn reserve_notarize(
        s: &S,
        c: &Self::Context,
        state: &mut Self::RecoveryState,
        p: &Proposal<D>,
        native: &NativeContext<D, S::PublicKey>,
        input: FirstInput<D>,
    ) -> Option<Wal<S, D>> {
        if !native_matches::<H, S, D>(&input.core, s, p, native)
            || !c.slot(&input.core.slot)
            || input.limits != c.limits
            || s.me() != Some(input.owner)
        {
            return None;
        }
        c.publish_input::<H>(input.clone())
            .expect("General capture capacity exhausted");
        let id = input.core.slot.id::<H>();
        if let Entry::Vacant(entry) = state.slots.entry(id) {
            let actual =
                g::issuance::State::new::<H>(s.clone(), input.core.clone(), input.input, c.limits)
                    .ok()?;
            entry.insert(SlotLedger {
                ledger: actual,
                first: None,
                first_vote: None,
                select: None,
                history: None,
                history_from_replay: false,
                replayed_ballots: Default::default(),
                normal: None,
            });
        }
        let l = state.slots.get_mut(&id)?;
        room(c, l, usize::from(l.first.is_none()));
        let record = match &input.row {
            Some(row) if input.route_scope.is_some() => l
                .ledger
                .reserve_route_first::<H>(row.clone(), |r| input.accepts(r)),
            Some(row) => {
                l.ledger
                    .reserve_first::<H>(row.report.clone(), row.preference.clone(), |r| {
                        input.accepts(r)
                    })
            }
            None => l.ledger.close_first::<H>(),
        }
        .ok()?;
        l.first = Some(record.clone());
        Some(Wal(Event::First(record)))
    }
    fn notarize_record(r: &Wal<S, D>) -> Option<&Proposal<D>> {
        matches!(r.0, Event::First(_) | Event::FirstReleased { .. }).then(|| r.proposal())
    }
    fn reserved_notarize(r: &Wal<S, D>) -> Option<&Proposal<D>> {
        matches!(r.0, Event::First(_)).then(|| r.proposal())
    }
    fn replay_notarize<R: CryptoRng>(
        s: &S,
        c: &Self::Context,
        rng: &mut R,
        state: &mut Self::RecoveryState,
        r: &Wal<S, D>,
    ) -> bool {
        let Some(input) = c.first(r.record()) else {
            return false;
        };
        let Some(l) = ledger::<H, S, D>(s, c, state, r.record(), true) else {
            return false;
        };
        match &r.0 {
            Event::First(record) => {
                if !matches!(
                    record.action(),
                    g::issuance::Action::NoFirst
                        | g::issuance::Action::Reserve {
                            message: g::Message {
                                kind: g::Kind::First(_),
                                ..
                            },
                            authority: None
                        }
                ) {
                    return false;
                }
                replay_room(c, l, &[record]);
                if l.ledger
                    .restore::<H, R>(
                        rng,
                        record,
                        g::issuance::Material::None,
                        |row| input.accepts(row),
                        |_, _| false,
                        &Sequential,
                    )
                    .is_err()
                {
                    return false;
                }
                l.first = Some(record.clone());
                true
            }
            Event::FirstReleased {
                reservation,
                receipt,
                vote,
            } => {
                if l.first.as_ref() != Some(reservation)
                    || vote.native().proposal != *r.proposal()
                    || vote.native().attestation.signer != input.owner
                    || vote.authenticate(rng, s, &Sequential).is_err()
                {
                    return false;
                }
                match (&input.row, receipt, vote.first()) {
                    (Some(_), Some(receipt), Some(signed)) => {
                        replay_room(c, l, &[receipt]);
                        if receipt.authority().is_some()
                            || !matches!(receipt.action(), g::issuance::Action::Released { .. })
                            || l.ledger
                                .restore::<H, R>(
                                    rng,
                                    receipt,
                                    g::issuance::Material::None,
                                    |row| input.accepts(row),
                                    |_, _| false,
                                    &Sequential,
                                )
                                .is_err()
                            || l.ledger.outbox(reservation) != Some(&signed.encode())
                        {
                            return false;
                        }
                    }
                    (None, None, None) => {}
                    _ => return false,
                }
                if l.first_vote.as_ref().is_some_and(|old| old != vote) {
                    return false;
                }
                l.first_vote = Some(vote.clone());
                true
            }
            _ => false,
        }
    }
    fn finish_notarize_replay(state: &mut Self::RecoveryState) -> bool {
        state
            .slots
            .values_mut()
            .all(|l| l.ledger.finish_replay().is_ok())
    }
    fn replay_notarize_vote(state: &Self::RecoveryState, vote: &FirstVote<S, D>) -> bool {
        state
            .slots
            .values()
            .any(|l| l.first_vote.as_ref() == Some(vote))
    }
    fn sign_notarize_current<R: CryptoRng>(
        s: &S,
        c: &Self::Context,
        rng: &mut R,
        state: &mut Self::RecoveryState,
        p: Proposal<D>,
        native: &NativeContext<D, S::PublicKey>,
        _: &mut impl Participation<S, D, Self>,
    ) -> Option<(FirstVote<S, D>, Option<Wal<S, D>>)> {
        let l = state
            .slots
            .values_mut()
            .find(|l| l.first.as_ref().is_some_and(|r| r.slot().proposal == p))?;
        if !native_matches::<H, S, D>(l.ledger.core(), s, &p, native) {
            return None;
        }
        if let Some(vote) = &l.first_vote {
            return Some((vote.clone(), None));
        }
        let record = l.first.clone()?;
        room(
            c,
            l,
            usize::from(!matches!(record.action(), g::issuance::Action::NoFirst)),
        );
        let signed = match record.action() {
            g::issuance::Action::NoFirst => None,
            _ => Some(l.ledger.sign_reserved(&record).ok()?),
        };
        let native_vote =
            Notarize::sign(s, p).expect("General native first signer failed after companion");
        let receipt = signed.as_ref().map(|signed| {
            l.ledger
                .record_signed::<H, R>(rng, &record, signed, &Sequential)
                .expect("General FIRST receipt failed")
        });
        let vote = FirstVote::new(native_vote, signed);
        l.first_vote = Some(vote.clone());
        Some((
            vote.clone(),
            Some(Wal(Event::FirstReleased {
                reservation: record,
                receipt,
                vote,
            })),
        ))
    }
    fn matches_context(c: &Self::Context, s: &FinalSubject<D>) -> bool {
        s.native.domain == c.domain
            && s.native.proposal.epoch() == c.epoch
            && s.native.ballot == s.native.proposal.round
            && s.agreement.round == s.native.ballot
    }
    fn matches_subject(p: &Proposal<D>, s: &FinalSubject<D>) -> bool {
        s.native.proposal == *p && s.native.ballot == p.round && s.agreement.round == p.round
    }
    fn matches_native_parent(_: &Self::Context, s: &FinalSubject<D>, parent: (View, D)) -> bool {
        let anchor = if parent.0 == View::new(0) {
            g::NativeParent::Genesis(parent.1)
        } else {
            g::NativeParent::Proposal {
                round: Round::new(s.native.proposal.epoch(), parent.0),
                digest: parent.1,
            }
        };
        s.native.proposal.parent == parent.0
            && s.native.parent == g::normal::native_parent::<H>(&anchor)
    }
    fn matches_parent(
        _: &Self::Context,
        _: &FinalSubject<D>,
        _: Option<&Finalization<S, D>>,
        _: Option<&Self::Recovered>,
        _: bool,
    ) -> bool {
        false
    }
    fn recovered_subject(r: &Self::Recovered) -> FinalSubject<D> {
        match *r {}
    }
    fn same_interpretation(a: &FinalSubject<D>, b: &FinalSubject<D>) -> bool {
        a == b
    }
    fn final_subject(v: &FinalVote<S, D>) -> FinalSubject<D> {
        FinalSubject {
            native: v.inner().native.statement.clone(),
            agreement: v.inner().agreement.message.clone(),
        }
    }
    fn finalization_subject(v: &Finalization<S, D>) -> FinalSubject<D> {
        FinalSubject {
            native: v.inner().native.statement.clone(),
            agreement: v.inner().agreement.message.clone(),
        }
    }
    fn reserve_finalize(_: &FinalSubject<D>) -> Option<Wal<S, D>> {
        None
    }
    fn reserved_subject(r: &Wal<S, D>) -> Option<FinalSubject<D>> {
        match &r.0 {
            Event::Normal { reservation, .. } => Some(FinalSubject {
                native: reservation.subject().clone(),
                agreement: reservation.agreement().message()?.clone(),
            }),
            _ => None,
        }
    }
    fn sign_finalize(_: &S, _: Proposal<D>, _: FinalSubject<D>) -> Option<FinalVote<S, D>> {
        None
    }
    fn retained_finalize(
        state: &Self::RecoveryState,
        subject: &FinalSubject<D>,
    ) -> Option<FinalVote<S, D>> {
        let l = state.slots.get(&subject.agreement.slot)?;
        let r = l.normal.as_ref()?;
        let pair = l.ledger.normal_outbox(r)?;
        (Self::final_subject(&FinalVote::new(pair.clone())) == *subject)
            .then(|| FinalVote::new(pair.clone()))
    }
    fn replay_finalize_vote(state: &Self::RecoveryState, vote: &FinalVote<S, D>) -> bool {
        Self::retained_finalize(state, &Self::final_subject(vote)).as_ref() == Some(vote)
    }
    fn stage_final_reservation<R: CryptoRng>(
        s: &S,
        c: &Self::Context,
        rng: &mut R,
        state: &mut Self::RecoveryState,
        p: &Proposal<D>,
        native: Option<&NativeContext<D, S::PublicKey>>,
        subject: &FinalSubject<D>,
    ) -> Option<Option<Wal<S, D>>> {
        let native = native?;
        let boot = c.bootstrap(subject.agreement.slot)?;
        if s.me() != Some(boot.owner) || !native_matches::<H, S, D>(&boot.core, s, p, native) {
            return None;
        }
        let assemblies: Vec<_> = c
            .index
            .lock()
            .origins
            .values()
            .filter(|a| FinalSubject::new::<H, S>(a) == *subject)
            .cloned()
            .collect();
        for assembly in assemblies {
            let id = assembly.core().slot.id::<H>();
            if let Entry::Vacant(entry) = state.slots.entry(id) {
                let actual = g::issuance::State::new::<H>(
                    s.clone(),
                    boot.core.clone(),
                    boot.input,
                    c.limits,
                )
                .ok()?;
                entry.insert(SlotLedger {
                    ledger: actual,
                    first: None,
                    first_vote: None,
                    select: None,
                    history: None,
                    history_from_replay: false,
                    replayed_ballots: Default::default(),
                    normal: None,
                });
            }
            let l = state.slots.get_mut(&id)?;
            if let Some(old) = &l.normal {
                return (old.subject() == &subject.native
                    && old.agreement().message() == Some(&subject.agreement))
                .then(|| {
                    Some(Wal(Event::Normal {
                        no_first: None,
                        reservation: old.clone(),
                    }))
                });
            }
            let needs_closure = l.first.is_none()
                && boot.owner != boot.core.leader
                && !boot.core.followers.contains(&boot.owner);
            room(c, l, 1 + usize::from(needs_closure));
            let Ok(reservation) =
                l.ledger
                    .reserve_normal_checked::<H, R>(rng, &assembly, &Sequential)
            else {
                continue;
            };
            // Both changes form one synchronized native item. Preserve their
            // actual history order: final reservation, then explicit closure.
            let no_first = if needs_closure {
                let n = l
                    .ledger
                    .close_first::<H>()
                    .expect("General outside-Core closure failed");
                l.first = Some(n.clone());
                Some(n)
            } else {
                None
            };
            l.normal = Some(reservation.clone());
            return Some(Some(Wal(Event::Normal {
                no_first,
                reservation,
            })));
        }
        None
    }
    fn sign_finalize_current<R: CryptoRng>(
        s: &S,
        c: &Self::Context,
        rng: &mut R,
        state: &mut Self::RecoveryState,
        p: Proposal<D>,
        native: Option<&NativeContext<D, S::PublicKey>>,
        subject: FinalSubject<D>,
    ) -> Option<(FinalVote<S, D>, Option<Wal<S, D>>)> {
        let l = state.slots.get_mut(&subject.agreement.slot)?;
        if !native_matches::<H, S, D>(l.ledger.core(), s, &p, native?) {
            return None;
        }
        let reservation = l.normal.clone()?;
        if reservation.subject() != &subject.native {
            return None;
        }
        if let Some(pair) = l.ledger.normal_outbox(&reservation) {
            return Some((FinalVote::new(pair.clone()), None));
        }
        room(c, l, 1);
        let pair = l
            .ledger
            .sign_normal::<H>(&reservation)
            .expect("General paired final signer failed");
        let released = l
            .ledger
            .record_normal_signed::<H, R>(rng, &reservation, &pair, &Sequential)
            .expect("General paired final receipt failed");
        Some((
            FinalVote::new(pair),
            Some(Wal(Event::NormalReleased(released))),
        ))
    }
    fn replay_recovery<R: CryptoRng>(
        s: &S,
        c: &Self::Context,
        rng: &mut R,
        state: &mut Self::RecoveryState,
        _: Option<&FinalSubject<D>>,
        r: &Wal<S, D>,
    ) -> bool {
        let Some(l) = ledger::<H, S, D>(s, c, state, r.record(), true) else {
            return false;
        };
        match &r.0 {
            Event::Wish(record) => {
                let Some((_, proof)) = &l.history else {
                    return false;
                };
                let core = l.ledger.core().clone();
                let Some(evidence) = initial_history::entry_evidence::<H, _, _>(s, c, proof) else {
                    return false;
                };
                let Some(checked) = initial_history::verify_entry::<H, _, _, _>(
                    rng, c, &l.ledger, &core, proof, &evidence,
                ) else {
                    return false;
                };
                if !matches!(
                    record.action(),
                    g::issuance::Action::AdvanceWish {
                        cause: g::issuance::WishCause::Timeout,
                        ..
                    }
                ) {
                    return false;
                }
                replay_room(c, l, &[record]);
                if l.ledger
                    .restore::<H, R>(
                        rng,
                        record,
                        g::issuance::Material::Entry(&checked),
                        |_| false,
                        |_, _| false,
                        &Sequential,
                    )
                    .is_err()
                {
                    return false;
                }
                l.replayed_ballots.insert(record.id::<H>());
                true
            }
            Event::Ballot { rpc, reservation } => {
                let Some(id) = reservation.authority() else {
                    return false;
                };
                let Some(authority) = c
                    .recovery_evidence
                    .as_ref()
                    .and_then(|reader| reader(rng, &l.ledger.verification_context(), id))
                else {
                    return false;
                };
                if l.history.is_none() || authority.evidence() != id || !matches!(reservation.message().map(|m| &m.kind), Some(g::Kind::Recovery {..}))
                    || rpc.is_some() != (authority.role() == g::recovery::Role::Rpc)
                    || rpc.as_ref().is_some_and(|r| !matches!(r.action(), g::issuance::Action::RetainRpc { proof,.. } if *proof == id)) {
                    return false;
                }
                for record in rpc.iter().chain(std::iter::once(reservation)) {
                    replay_room(c, l, &[record]);
                    if l.ledger
                        .restore::<H, R>(
                            rng,
                            record,
                            g::issuance::Material::Recovery(&authority),
                            |_| false,
                            |_, _| false,
                            &Sequential,
                        )
                        .is_err()
                    {
                        return false;
                    }
                }
                l.replayed_ballots.insert(reservation.id::<H>());
                true
            }
            Event::HigherHistory { .. } | Event::History { .. } => {
                initial_history::replay::<H, S, D, R>(s, c, rng, l, r)
            }
            Event::Select(record) => {
                replay_room(c, l, &[record]);
                let Some(body) = record.authority().and_then(|id| c.selection(id)) else {
                    return false;
                };
                if l.ledger
                    .restore_select_checked::<H, R>(
                        rng,
                        record,
                        &body.body,
                        &body.checked,
                        &Sequential,
                    )
                    .is_err()
                {
                    return false;
                }
                l.select = Some(record.clone());
                true
            }
            Event::SelectReleased {
                reservation,
                receipt,
            }
            | Event::HistoryReleased {
                reservation,
                receipt,
            }
            | Event::BallotReleased {
                reservation,
                receipt,
            } => {
                let g::issuance::Action::Released {
                    reservation: released,
                    ..
                } = receipt.action()
                else {
                    return false;
                };
                let held = if matches!(&r.0, Event::BallotReleased { .. }) {
                    l.ledger.records().iter().find(|record| {
                        *record == reservation
                            && matches!(
                                record.message().map(|m| &m.kind),
                                Some(g::Kind::Recovery { .. } | g::Kind::Wish(_))
                            )
                    })
                } else if matches!(&r.0, Event::HistoryReleased { .. }) {
                    l.history.as_ref().map(|(wal, _)| wal.record())
                } else {
                    l.select.as_ref()
                };
                if held != Some(reservation) || *released != reservation.id::<H>() {
                    return false;
                }
                replay_room(c, l, &[receipt]);
                l.ledger
                    .restore::<H, R>(
                        rng,
                        receipt,
                        g::issuance::Material::None,
                        |_| false,
                        |_, _| false,
                        &Sequential,
                    )
                    .is_ok()
                    && l.ledger.outbox(reservation).is_some()
            }
            Event::Normal {
                no_first,
                reservation,
            } => {
                let mut records = vec![reservation.agreement()];
                records.extend(no_first);
                replay_room(c, l, &records);
                let Some(a) = reservation
                    .agreement()
                    .authority()
                    .and_then(|id| c.assembly(id))
                else {
                    return false;
                };
                if l.ledger
                    .restore_normal_checked::<H, R>(rng, reservation, &a, &Sequential)
                    .is_err()
                {
                    return false;
                }
                if let Some(n) = no_first {
                    if !matches!(n.action(), g::issuance::Action::NoFirst)
                        || l.ledger
                            .restore::<H, R>(
                                rng,
                                n,
                                g::issuance::Material::None,
                                |_| false,
                                |_, _| false,
                                &Sequential,
                            )
                            .is_err()
                    {
                        return false;
                    }
                    l.first = Some(n.clone());
                }
                l.normal = Some(reservation.clone());
                true
            }
            Event::NormalReleased(released) => {
                replay_room(c, l, &[released.receipt()]);
                l.normal.as_ref() == Some(released.reservation())
                    && l.ledger
                        .restore_normal_signed::<H, R>(rng, released, &Sequential)
                        .is_ok()
            }
            _ => false,
        }
    }
    fn historical_slot(record: &Wal<S, D>) -> Option<D> {
        match record.0 {
            Event::History { .. }
            | Event::HigherHistory { .. }
            | Event::Wish(_)
            | Event::Ballot { .. } => Some(record.record().slot().id::<H>()),
            _ => None,
        }
    }

    fn historical_context<E, L>(
        state: &crate::simplex::actors::voter::StateWith<E, S, L, D, Self>,
        scheme: &S,
        proposal: &Proposal<D>,
        slot: D,
    ) -> Option<NativeContext<D, S::PublicKey>>
    where
        E: commonware_runtime::Clock + CryptoRng + commonware_runtime::Metrics,
        L: crate::simplex::elector::Elector<S>,
    {
        let anchor = state.history_anchor_after(proposal.view())?.inner();
        let mut child = &anchor.origin.body.core.slot;
        // The admitted final certificate binds its parent's native round and
        // payload digest. Each intervening link must have its own original
        // notarization and a locally journaled, native-context-checked FIRST.
        while child.proposal.view() > proposal.view() {
            let g::NativeParent::Proposal { round, digest } = child.parent else {
                return None;
            };
            if round.epoch() != proposal.epoch()
                || round.view() >= child.proposal.view()
                || round.view() < proposal.view()
            {
                return None;
            }
            let parent = state.retained_round(round.view())?;
            let p = &parent.notarization()?.proposal;
            if p.round != round || p.payload != digest {
                return None;
            }
            let mut links = parent.recovery_state().slots.values().filter(|l| {
                let s = &l.ledger.core().slot;
                s.proposal == *p
                    && s.cut.checked_add(1) == Some(child.cut)
                    && s.profile == child.profile
                    && s.domain == child.domain
                    && s.roster == child.roster
                    && l.first_vote
                        .as_ref()
                        .is_some_and(|v| v.native().proposal == *p)
            });
            let core = links.next()?.ledger.core();
            if links.next().is_some() {
                return None;
            }
            child = &core.slot;
            if p == proposal && child.id::<H>() == slot {
                let parent_digest = match child.parent {
                    g::NativeParent::Genesis(d) | g::NativeParent::Proposal { digest: d, .. } => d,
                };
                return Some(NativeContext {
                    round: p.round,
                    leader: scheme.participants().get(usize::from(core.leader))?.clone(),
                    parent: (p.parent, parent_digest),
                });
            }
        }
        None
    }
    fn observe_recovery_nqc<E, L>(
        state: &mut crate::simplex::actors::voter::StateWith<E, S, L, D, Self>,
        view: View,
    ) where
        E: commonware_runtime::Clock + CryptoRng + commonware_runtime::Metrics,
        L: crate::simplex::elector::Elector<S>,
    {
        state.observe_recovery(view, None, |s, c, r, p, n, t, d| {
            observe_slot::<H, _, _>(s, c, r, p, n, t, d, None)
        });
    }
    fn validate_recovery_request<E, L>(
        state: &mut crate::simplex::actors::voter::StateWith<E, S, L, D, Self>,
        request: &SelectRequest<D>,
    ) -> bool
    where
        E: commonware_runtime::Clock + CryptoRng + commonware_runtime::Metrics,
        L: crate::simplex::elector::Elector<S>,
    {
        let c = state.interpretation_context();
        let historical = request.view() <= state.last_finalized();
        if historical
            && state
                .recovery_context_for(request.view(), request.recovery_slot())
                .is_none()
        {
            return false;
        }
        let body_id = match &request.command {
            Command::Select(id) => *id,
            Command::HigherHistory { slot, report, .. } => {
                return c.entry_reader.is_some()
                    && report
                        .as_ref()
                        .is_none_or(|raw| raw.len() <= c.limits.report_bytes)
                    && c.bootstrap(*slot)
                        .is_some_and(|b| b.core.slot.proposal == request.proposal)
                    && state
                        .retained_round(request.proposal.view())
                        .and_then(|r| r.notarization())
                        .is_some_and(|nqc| nqc.proposal == request.proposal);
            }
            Command::Wish { slot, .. } => {
                return c.recovery_wait.is_some()
                    && c.bootstrap(*slot)
                        .is_some_and(|b| b.core.slot.proposal == request.proposal)
                    && state
                        .retained_round(request.proposal.view())
                        .and_then(|r| r.notarization())
                        .is_some_and(|qc| qc.proposal == request.proposal);
            }
            Command::Ballot { slot, .. } => {
                return c.recovery_evidence.is_some()
                    && c.bootstrap(*slot)
                        .is_some_and(|b| b.core.slot.proposal == request.proposal)
                    && state
                        .retained_round(request.proposal.view())
                        .and_then(|r| r.notarization())
                        .is_some_and(|nqc| nqc.proposal == request.proposal);
            }
            Command::InitialHistory {
                slot,
                input,
                owner,
                report,
            } => {
                if !c.bootstrap(*slot).is_some_and(|b| {
                    b.core.slot.proposal == request.proposal
                        && b.input == *input
                        && b.owner == *owner
                }) || report
                    .as_ref()
                    .is_some_and(|r| r.len() > c.limits.report_bytes)
                {
                    return false;
                }
                // Inclusion already supplies historical entry. There is no
                // live native round whose timeout must additionally expire.
                if historical {
                    return true;
                }
                return state
                    .observe_recovery(
                        request.proposal.view(),
                        Some(*slot),
                        |s, c, r, p, n, t, d| {
                            observe_slot::<H, _, _>(s, c, r, p, n, t, d, Some(*slot))
                        },
                    )
                    .unwrap_or(false);
            }
        };
        let Some(body) = c.selection(body_id) else {
            return false;
        };
        body.body.core.slot.proposal == request.proposal
            && request.proposal.view() > state.last_finalized()
            && state.is_me(body.body.core.leader)
            && state
                .notarization(request.proposal.view())
                .is_some_and(|n| n.proposal == request.proposal)
            && state.leader_index(request.proposal.view()) == Some(body.body.core.leader)
    }
    fn stage_recovery_request<E, L>(
        state: &mut crate::simplex::actors::voter::StateWith<E, S, L, D, Self>,
        request: &SelectRequest<D>,
        _: &mut impl Participation<S, D, Self>,
    ) -> Option<Wal<S, D>>
    where
        E: commonware_runtime::Clock + CryptoRng + commonware_runtime::Metrics,
        L: crate::simplex::elector::Elector<S>,
    {
        if !Self::validate_recovery_request(state, request) {
            return None;
        }
        state.stage_mode_recovery(
            request.proposal.view(),
            request.recovery_slot(),
            |s, c, rng, state, p, native, nqc| {
                let body_id = match &request.command {
                    Command::Select(id) => *id,
                    Command::HigherHistory {
                        slot,
                        entry,
                        report,
                    } => {
                        let l = state.slots.get_mut(slot)?;
                        if !native_matches::<H, S, D>(l.ledger.core(), s, p, native) {
                            return None;
                        }
                        return initial_history::stage_higher::<H, _, _, _>(
                            s,
                            c,
                            rng,
                            l,
                            *entry,
                            report.clone(),
                        );
                    }
                    Command::Wish { slot, predecessor } => {
                        let l = state.slots.get_mut(slot)?;
                        if !native_matches::<H, S, D>(l.ledger.core(), s, p, native) {
                            return None;
                        }
                        let (_, proof) = l.history.as_ref()?;
                        if proof.artifact_id::<H>() != *predecessor {
                            return None;
                        }
                        let core = l.ledger.core().clone();
                        let evidence = initial_history::entry_evidence::<H, _, _>(s, c, proof)?;
                        let checked = initial_history::verify_entry::<H, _, _, _>(
                            rng, c, &l.ledger, &core, proof, &evidence,
                        )?;
                        if let Some(old) = l.ledger.records().iter().find(|record| {
                            matches!(record.message().map(|message| &message.kind),
                                Some(g::Kind::Wish(wish)) if wish.predecessor == *predecessor)
                        }) {
                            if l.replayed_ballots.contains(&old.id::<H>())
                                && l.ledger.outbox(old).is_none()
                            {
                                return None;
                            }
                            return Some(Wal(Event::Wish(old.clone())));
                        }
                        if l.ledger.records().len().checked_add(2)? > c.resources.records_per_slot {
                            return None;
                        }
                        l.ledger
                            .arm_wish_timeout::<H>(rng, &checked, c.recovery_wait?)
                            .ok()?;
                        let reservation = l.ledger.reserve_timeout_wish::<H>(rng, &checked).ok()?;
                        return Some(Wal(Event::Wish(reservation)));
                    }
                    Command::Ballot { slot, evidence } => {
                        let l = state.slots.get_mut(slot)?;
                        if !native_matches::<H, S, D>(l.ledger.core(), s, p, native)
                            || l.history.is_none()
                        {
                            return None;
                        }
                        let authority = c.recovery_evidence.as_ref()?(
                            rng,
                            &l.ledger.verification_context(),
                            *evidence,
                        )?;
                        if authority.evidence() != *evidence {
                            return None;
                        }
                        let role = authority.role();
                        if role == g::recovery::Role::Terminal {
                            return None;
                        }
                        // Include release capacity before calling the signer. Once
                        // chosen, aliases cannot replace the retained original.
                        let old = l.ledger.records().iter().find(|r| {
                            r.authority() == Some(*evidence)
                                && matches!(
                                    r.message().map(|m| &m.kind),
                                    Some(g::Kind::Recovery { .. })
                                )
                        });
                        if old.is_none()
                            && l.ledger
                                .records()
                                .len()
                                .checked_add(if role == g::recovery::Role::Rpc { 3 } else { 2 })?
                                > c.resources.records_per_slot
                        {
                            return None;
                        }
                        let (rpc, reservation) = match role {
                            g::recovery::Role::Admission => {
                                (None, l.ledger.reserve_propose::<H>(&authority).ok()?)
                            }
                            g::recovery::Role::Proposal => {
                                (None, l.ledger.reserve_prepare::<H>(&authority).ok()?)
                            }
                            g::recovery::Role::Rpc => {
                                let (rpc, vote) =
                                    l.ledger.reserve_rpc_commit::<H>(&authority).ok()?;
                                (Some(rpc), vote)
                            }
                            g::recovery::Role::Terminal => unreachable!(),
                        };
                        if reservation.authority() != Some(*evidence) {
                            return None;
                        }
                        return Some(Wal(Event::Ballot { rpc, reservation }));
                    }
                    Command::InitialHistory { slot, report, .. } => {
                        let b = c.bootstrap(*slot)?;
                        if s.me() != Some(b.owner)
                            || !native_matches::<H, S, D>(&b.core, s, p, native)
                        {
                            return None;
                        }
                        // This is the current live round after full voter replay.
                        // No lookup miss in archived state may open a signing ledger.
                        if !state.slots.contains_key(slot) && state.slots.len() >= c.resources.slots
                        {
                            return None;
                        }
                        let l = match state.slots.entry(*slot) {
                            Entry::Occupied(old) => old.into_mut(),
                            Entry::Vacant(v) => v.insert(SlotLedger {
                                ledger: g::issuance::State::new::<H>(
                                    s.clone(),
                                    b.core,
                                    b.input,
                                    c.limits,
                                )
                                .ok()?,
                                first: None,
                                first_vote: None,
                                select: None,
                                normal: None,
                                history: None,
                                history_from_replay: false,
                                replayed_ballots: Default::default(),
                            }),
                        };
                        return initial_history::stage::<H, S, D, E>(
                            s,
                            c,
                            rng,
                            l,
                            nqc,
                            report.clone(),
                        );
                    }
                };
                let body = c.selection(body_id)?;
                if s.me() != Some(body.body.core.leader)
                    || !native_matches::<H, S, D>(&body.body.core, s, p, native)
                {
                    return None;
                }
                let id = body.body.core.slot.id::<H>();
                let l = state.slots.get_mut(&id)?;
                room(c, l, usize::from(l.select.is_none()));
                let record = l
                    .ledger
                    .reserve_select_checked::<H, E>(rng, &body.body, &body.checked, &Sequential)
                    .ok()?;
                l.select = Some(record.clone());
                Some(Wal(Event::Select(record)))
            },
        )
    }
    fn prepare_recovery_request<E, L>(
        state: &mut crate::simplex::actors::voter::StateWith<E, S, L, D, Self>,
        query: &Self::RecoveryQuery,
        _: &mut impl Participation<S, D, Self>,
    ) -> Option<Self::QueryResult>
    where
        E: commonware_runtime::Clock + CryptoRng + commonware_runtime::Metrics,
        L: crate::simplex::elector::Elector<S>,
    {
        let round = state.retained_round(query.view())?;
        let ledger = round.recovery_state().slots.get(&query.slot)?;
        initial_history::material(ledger, query)
    }
    fn sign_recovery(_: &S, _: &Self::Context, _: &Wal<S, D>) -> Option<g::Signed<S, D>> {
        None
    }
    fn sign_recovery_current<R: CryptoRng>(
        _: &S,
        c: &Self::Context,
        rng: &mut R,
        state: &mut Self::RecoveryState,
        r: &Wal<S, D>,
    ) -> Option<(g::Signed<S, D>, Option<Wal<S, D>>)> {
        let record = r.record();
        let l = state.slots.get_mut(&record.slot().id::<H>())?;
        let held = match &r.0 {
            Event::Wish(_) | Event::Ballot { .. } => {
                l.ledger.records().iter().find(|r| *r == record)
            }
            Event::Select(_) => l.select.as_ref(),
            Event::HigherHistory { .. } | Event::History { .. } => {
                l.history.as_ref().map(|(wal, _)| wal.record())
            }
            _ => return None,
        };
        if held != Some(record) {
            return None;
        }
        if let Some(frame) = l.ledger.outbox(record) {
            let signed = g::Signed::decode_cfg(frame.clone(), &c.limits).ok()?;
            return Some((signed, None));
        }
        if (matches!(&r.0, Event::History { .. } | Event::HigherHistory { .. })
            && l.history_from_replay)
            || l.replayed_ballots.contains(&record.id::<H>())
        {
            // A reservation without a receipt does not say if the signer ran.
            return None;
        }
        room(c, l, 1);
        let signed = l.ledger.sign_reserved(record).ok()?;
        let receipt = l
            .ledger
            .record_signed::<H, R>(rng, record, &signed, &Sequential)
            .expect("General recovery mailbox receipt failed");
        Some((
            signed,
            Some(Wal(
                if matches!(&r.0, Event::Wish(_) | Event::Ballot { .. }) {
                    Event::BallotReleased {
                        reservation: record.clone(),
                        receipt,
                    }
                } else if matches!(&r.0, Event::History { .. } | Event::HigherHistory { .. }) {
                    Event::HistoryReleased {
                        reservation: record.clone(),
                        receipt,
                    }
                } else {
                    Event::SelectReleased {
                        reservation: record.clone(),
                        receipt,
                    }
                },
            )),
        ))
    }
}

#[cfg(test)]
#[path = "voting_replay_tests.rs"]
mod replay_tests;

#[path = "initial_history.rs"]
mod initial_history;
