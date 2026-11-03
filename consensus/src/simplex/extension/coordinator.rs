//! Native slow-path network coordination. Normal Simplex timers and votes are unchanged.
//! Only the serial voter signs durable statuses/votes and installs recovered parents.
use super::{
    certificate::Recovered,
    recovery_wire::Wire,
    request::{Command, MAX_BYTES, Query, Request, Response},
    vote::{Certificate, Vote},
};
use crate::{
    simplex::{
        AdmittedRecovery, Readiness,
        phase2::{Extended, Mode, voting::ExtendedContext},
        scheme::Scheme,
    },
    types::{Epoch, Participant, View},
};
use commonware_codec::{Decode as _, EncodeSize};
use commonware_cryptography::Digest;
use commonware_macros::select;
use commonware_p2p::{Message, Receiver, Recipients, Sender, utils::codec::WrappedSender};
use commonware_parallel::Strategy;
use commonware_runtime::{BufferPooler, Clock, Handle, Spawner, utils::reschedule};
use commonware_utils::{Faults as _, N3f1, non_empty};
use futures::{FutureExt as _, StreamExt as _, stream::FuturesUnordered};
use rand_core::CryptoRng;
use std::{
    collections::{BTreeMap, BTreeSet},
    future::{Future, pending},
    pin::Pin,
    time::{Duration, SystemTime},
};

/// Explicit slow-path bounds; retry/attempt expiry never delays normal proposals.
#[derive(Clone, Copy)]
pub struct Config<D: Digest> {
    pub epoch: Epoch,
    pub context: ExtendedContext<D>,
    pub retry: Duration,
    pub attempt_timeout: Duration,
    pub pending: usize,
    /// Retained certificates require source-backed retirement before this bound fills.
    /// Exhaustion fails closed rather than silently dropping an unreconciled witness.
    pub retained: usize,
}
#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("invalid recovery coordinator configuration")]
    Configuration,
    #[error("recovery channel closed")]
    Network,
    #[error("recovery retained witness capacity exceeded")]
    Capacity,
    #[error("recovery authorization retention failed")]
    Retention,
}

/// Application evidence retention outcome before native recovery acceptance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RetainError {
    /// Exact evidence is temporarily unavailable; the existing attempt may retry.
    Unavailable,
    /// The supplied evidence is invalid; no request is dispatched to the voter.
    Rejected,
    /// The custody owner failed and its supervised coordinator must stop.
    Failed,
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Phase {
    Promise,
    Statuses,
    Plan,
    Accept,
    Votes,
    Install,
}
struct Attempt<S: Scheme<D>, D: Digest> {
    promise: Request<S, D>,
    accept: Option<Request<S, D>>,
    statuses: BTreeMap<Participant, Response<S, D>>,
    proof: Option<Vec<Response<S, D>>>,
    votes: BTreeMap<Participant, Vote<S, D>>,
    deadline: SystemTime,
    phase: Phase,
}
impl<S: Scheme<D>, D: Digest> Attempt<S, D> {
    fn matches(&self, command: &Command<D>) -> bool {
        self.promise.command.proposal() == command.proposal()
            && self.promise.command.ballot() == command.ballot()
            && self.promise.command.domain() == command.domain()
    }
}
enum Done<S: Scheme<D>, D: Digest> {
    Discover(Option<Request<S, D>>),
    Plan(Command<D>, Option<Request<S, D>>),
    Local(Command<D>, Result<Option<Response<S, D>>, RetainError>),
    Peer(
        S::PublicKey,
        Command<D>,
        Result<Option<Response<S, D>>, RetainError>,
    ),
    Installed(Recovered<S, D>, bool),
}
type Work<S, D> = Pin<Box<dyn Future<Output = Done<S, D>> + Send>>;

/// Starts the native recovery sidecar with the same epoch scheme and interpretation
/// configuration as its Engine. Supervise this handle together with the voter.
///
/// After native admission of a local or peer Accept request, `retain` must make its
/// exact application material and signed authorization durable. The callback
/// runs in the existing bounded work futures; it must not block when called.
/// Promise requests bypass this barrier. Retention never grants native voting
/// authority: the voter independently validates and journals every request.
/// Legacy profiles without authorization custody must opt in to their explicit
/// retention policy; Dependency profiles must supply their durable owner barrier.
pub fn start<E, S, D, T, F, Fut>(
    context: E,
    ready: Readiness<S, D, Extended>,
    scheme: S,
    config: Config<D>,
    network: (
        impl Sender<PublicKey = S::PublicKey>,
        impl Receiver<PublicKey = S::PublicKey>,
    ),
    strategy: T,
    retain: F,
) -> Result<Handle<Result<(), Error>>, Error>
where
    E: Clock + Spawner + BufferPooler + CryptoRng,
    S: Scheme<D>,
    D: Digest,
    T: Strategy,
    F: Fn(AdmittedRecovery<S, D>) -> Fut + Clone + Send + 'static,
    Fut: Future<Output = Result<(), RetainError>> + Send + 'static,
{
    let n = u32::try_from(scheme.participants().len()).map_err(|_| Error::Configuration)?;
    let now = context.current();
    if n == 0
        || u64::from(n) <= 5 * u64::from(N3f1::max_faults(n))
        || !S::is_attributable()
        || scheme.me().is_none()
        || config.retry.is_zero()
        || config.attempt_timeout <= config.retry
        || config.pending < 2
        || config.retained == 0
        || now.checked_add(config.retry).is_none()
        || now.checked_add(config.attempt_timeout).is_none()
    {
        return Err(Error::Configuration);
    }
    Ok(
        context
            .spawn(move |context| run(context, ready, scheme, config, network, strategy, retain)),
    )
}

enum Event<S: Scheme<D>, D: Digest> {
    Local(Done<S, D>),
    Peer(Done<S, D>),
    Packet(Message<S::PublicKey>),
    Tick,
}

// The deterministic clock does not advance inside one task poll. Tests first
// prove public admission of a 1ns retry, then model that deadline already having
// elapsed on its next poll, as a real clock can, without changing validation.
#[cfg(test)]
pub(crate) async fn run_expired_retry_for_test<E, S, D, T, F, Fut>(
    context: E,
    ready: Readiness<S, D, Extended>,
    scheme: S,
    mut config: Config<D>,
    network: (
        impl Sender<PublicKey = S::PublicKey>,
        impl Receiver<PublicKey = S::PublicKey>,
    ),
    strategy: T,
    retain: F,
) -> Result<(), Error>
where
    E: Clock + Spawner + BufferPooler + CryptoRng,
    S: Scheme<D>,
    D: Digest,
    T: Strategy,
    F: Fn(AdmittedRecovery<S, D>) -> Fut + Clone + Send + 'static,
    Fut: Future<Output = Result<(), RetainError>> + Send + 'static,
{
    assert_eq!(config.retry, Duration::from_nanos(1));
    config.retry = Duration::ZERO;
    run(context, ready, scheme, config, network, strategy, retain).await
}
async fn run<E, S, D, T, F, Fut>(
    mut context: E,
    mut ready: Readiness<S, D, Extended>,
    scheme: S,
    config: Config<D>,
    network: (
        impl Sender<PublicKey = S::PublicKey>,
        impl Receiver<PublicKey = S::PublicKey>,
    ),
    strategy: T,
    retain: F,
) -> Result<(), Error>
where
    E: Clock + Spawner + BufferPooler + CryptoRng,
    S: Scheme<D>,
    D: Digest,
    T: Strategy,
    F: Fn(AdmittedRecovery<S, D>) -> Fut + Clone + Send + 'static,
    Fut: Future<Output = Result<(), RetainError>> + Send + 'static,
{
    let (sender, mut receiver) = network;
    let mut sender =
        WrappedSender::<_, Wire<S, D>>::new(context.network_buffer_pool().clone(), sender);
    let codec = (
        scheme.participants().len(),
        scheme.certificate_codec_config(),
    );
    let quorum = N3f1::quorum(scheme.participants().len() as u32) as usize;
    let mut active: Option<Attempt<S, D>> = None;
    let mut observed: Option<(Command<D>, SystemTime)> = None;
    let mut abandoned: Option<Command<D>> = None;
    let mut local: Option<Work<S, D>> = None;
    let mut peers = FuturesUnordered::<Work<S, D>>::new();
    let mut queued = BTreeMap::<View, Recovered<S, D>>::new();
    let mut installed = BTreeMap::<View, Recovered<S, D>>::new();
    let mut installing = BTreeSet::<View>::new();
    let mut tick = context.current();
    let mut turn = 0;
    loop {
        if context.stopped().now_or_never().is_some() {
            return Ok(());
        }
        // One bounded due batch cannot be excluded by ready ingress. Yield
        // before normal arbitration even if a tiny retry has already expired.
        if context.current() >= tick {
            tick = context
                .current()
                .checked_add(config.retry)
                .ok_or(Error::Configuration)?;
            if active
                .as_ref()
                .is_some_and(|a| a.deadline <= context.current())
            {
                abandoned = active.take().map(|a| a.promise.command);
            }
            for (view, c) in &queued {
                if peers.len() >= config.pending {
                    break;
                }
                if installing.insert(*view) {
                    let c = c.clone();
                    let reply = ready.install_recovered(c.clone());
                    peers.push(Box::pin(async move {
                        Done::Installed(c, reply.await.unwrap_or(false))
                    }));
                }
            }
            for c in installed.values() {
                sender.send(Recipients::All, Wire::Recovered(c.clone()), true);
            }
            if local.is_none() {
                if let Some(a) = active.as_mut() {
                    match a.phase {
                        Phase::Promise => {
                            let r = a.promise.clone();
                            let command = r.command.clone();
                            let work = dispatch(ready.clone(), r, retain.clone());
                            local = Some(Box::pin(async move { Done::Local(command, work.await) }));
                        }
                        Phase::Statuses => {
                            if a.statuses.len() >= quorum {
                                a.proof = Some(a.statuses.values().cloned().collect());
                                a.phase = Phase::Plan;
                            } else {
                                sender.send(
                                    Recipients::All,
                                    Wire::Request(a.promise.clone()),
                                    true,
                                );
                            }
                        }
                        Phase::Plan => {
                            let command = a.promise.command.clone();
                            let reply = ready.prepare_recovery(Query::Accept {
                                promise: a.promise.clone(),
                                responses: a.proof.as_ref().unwrap().clone(),
                            });
                            local = Some(Box::pin(async move {
                                Done::Plan(command, reply.await.ok().flatten())
                            }));
                        }
                        Phase::Accept => {
                            let r = a.accept.as_ref().unwrap().clone();
                            let command = r.command.clone();
                            let work = dispatch(ready.clone(), r, retain.clone());
                            local = Some(Box::pin(async move { Done::Local(command, work.await) }));
                        }
                        Phase::Votes => {
                            if a.votes.len() >= quorum {
                                let votes = a.votes.values().cloned().collect::<Vec<_>>();
                                if let Ok(c) = Certificate::from_votes(
                                    &mut context,
                                    &scheme,
                                    non_empty![@votes],
                                    &strategy,
                                ) {
                                    let c = Recovered::new(c).map_err(|_| Error::Configuration)?;
                                    let view = c.certificate().statement.proposal.round.view();
                                    if queued.len() >= config.retained
                                        && !queued.contains_key(&view)
                                    {
                                        return Err(Error::Capacity);
                                    }
                                    queued.entry(view).or_insert(c);
                                    a.phase = Phase::Install;
                                }
                            } else {
                                sender.send(
                                    Recipients::All,
                                    Wire::Request(a.accept.as_ref().unwrap().clone()),
                                    true,
                                );
                            }
                        }
                        Phase::Install => {}
                    }
                } else if observed
                    .as_ref()
                    .is_none_or(|(_, until)| *until <= context.current())
                {
                    let reply = ready.prepare_recovery(Query::Discover);
                    local = Some(Box::pin(async move {
                        Done::Discover(reply.await.ok().flatten())
                    }));
                }
            }

            reschedule().await;
        }
        // Rotate all three existing work sources. In particular, repeated
        // ready Discover(None) replies cannot monopolize an expired timer loop.
        let event = match turn {
            0 => select! {
                _=context.stopped()=>return Ok(()),
                done=async {match local.as_mut(){Some(w)=>w.await,None=>pending().await}}=>Event::Local(done),
                Some(done)=async {if peers.is_empty(){pending().await}else{peers.next().await}}=>Event::Peer(done),
                packet=receiver.recv()=>Event::Packet(packet.map_err(|_|Error::Network)?),
                _=context.sleep_until(tick)=>Event::Tick,
            },
            1 => select! {
                _=context.stopped()=>return Ok(()),
                Some(done)=async {if peers.is_empty(){pending().await}else{peers.next().await}}=>Event::Peer(done),
                packet=receiver.recv()=>Event::Packet(packet.map_err(|_|Error::Network)?),
                done=async {match local.as_mut(){Some(w)=>w.await,None=>pending().await}}=>Event::Local(done),
                _=context.sleep_until(tick)=>Event::Tick,
            },
            _ => select! {
                _=context.stopped()=>return Ok(()),
                packet=receiver.recv()=>Event::Packet(packet.map_err(|_|Error::Network)?),
                done=async {match local.as_mut(){Some(w)=>w.await,None=>pending().await}}=>Event::Local(done),
                Some(done)=async {if peers.is_empty(){pending().await}else{peers.next().await}}=>Event::Peer(done),
                _=context.sleep_until(tick)=>Event::Tick,
            },
        };
        turn = (turn + 1) % 3;
        match event {
            Event::Local(done) => {
                local = None;
                match done {
                    Done::Discover(Some(p)) => {
                        let old = abandoned.as_ref().is_some_and(|c| {
                            c.proposal() == p.command.proposal() && c.ballot() >= p.command.ballot()
                        });
                        if !old
                            && observed
                                .as_ref()
                                .is_none_or(|(_, until)| *until <= context.current())
                        {
                            active = Some(Attempt {
                                promise: p,
                                accept: None,
                                statuses: BTreeMap::new(),
                                proof: None,
                                votes: BTreeMap::new(),
                                deadline: context
                                    .current()
                                    .checked_add(config.attempt_timeout)
                                    .ok_or(Error::Configuration)?,
                                phase: Phase::Promise,
                            });
                        }
                    }
                    Done::Plan(command, Some(request)) => {
                        if let Some(a) = active.as_mut()
                            && a.matches(&command)
                            && a.phase == Phase::Plan
                        {
                            a.accept = Some(request);
                            a.phase = Phase::Accept;
                        }
                    }
                    Done::Local(command, Ok(Some(response))) => {
                        if let Some(a) = active.as_mut()
                            && a.matches(&command)
                        {
                            match (&command, &response) {
                                (Command::Promise { .. }, Response::Status { .. })
                                    if a.phase == Phase::Promise =>
                                {
                                    a.phase = Phase::Statuses;
                                    sender.send(
                                        Recipients::All,
                                        Wire::Request(a.promise.clone()),
                                        true,
                                    );
                                }
                                (Command::Accept(_), Response::Vote(_))
                                    if a.phase == Phase::Accept =>
                                {
                                    a.phase = Phase::Votes;
                                    sender.send(
                                        Recipients::All,
                                        Wire::Request(a.accept.as_ref().unwrap().clone()),
                                        true,
                                    );
                                }
                                _ => {}
                            }
                            admit_response(
                                a,
                                response,
                                &scheme,
                                &config.context,
                                &mut context,
                                &strategy,
                            );
                        }
                    }
                    Done::Local(_, Err(RetainError::Failed)) => return Err(Error::Retention),
                    _ => {}
                }
            }
            Event::Peer(done) => match done {
                Done::Peer(peer, command, Ok(Some(response))) => {
                    if observed
                        .as_ref()
                        .is_none_or(|(old, _)| follow(old, &command))
                    {
                        observed = Some((
                            command.clone(),
                            context
                                .current()
                                .checked_add(config.attempt_timeout)
                                .ok_or(Error::Configuration)?,
                        ));
                    }
                    if active.as_ref().is_some_and(|a| {
                        a.promise.command.proposal() == command.proposal()
                            && a.promise.command.ballot() < command.ballot()
                    }) {
                        active = None;
                    }
                    sender.send(Recipients::One(peer), Wire::Response(response), true);
                }
                Done::Installed(c, true) => {
                    let view = c.certificate().statement.proposal.round.view();
                    installing.remove(&view);
                    queued.remove(&view);
                    if installed.len() >= config.retained && !installed.contains_key(&view) {
                        return Err(Error::Capacity);
                    }
                    installed.entry(view).or_insert_with(|| c.clone());
                    if active.as_ref().is_some_and(|a| {
                        a.promise.command.proposal() == &c.certificate().statement.proposal
                    }) {
                        active = None;
                    }
                    if observed
                        .as_ref()
                        .is_some_and(|(o, _)| o.proposal() == &c.certificate().statement.proposal)
                    {
                        observed = None;
                    }
                    sender.send(Recipients::All, Wire::Recovered(c), true);
                }
                Done::Installed(c, false) => {
                    installing.remove(&c.certificate().statement.proposal.round.view());
                }
                Done::Peer(_, _, Err(RetainError::Failed)) => return Err(Error::Retention),
                _ => {}
            },
            Event::Packet(packet) => {
                let (peer, encoded) = packet;
                let Ok(wire) = Wire::decode_cfg(encoded, &codec) else {
                    continue;
                };
                match wire {
                    Wire::Request(request) => {
                        if peers.len() >= config.pending - 1
                            || request.command.domain() != config.context.domain
                            || request.command.ballot().epoch() != config.epoch
                            || !request.verify(&mut context, &scheme, &strategy)
                            || scheme.participants()[usize::from(request.attestation.signer)]
                                != peer
                        {
                            continue;
                        }
                        if let Some(c) = installed.get(&request.view())
                            && &c.certificate().statement.proposal == request.command.proposal()
                        {
                            sender.send(Recipients::One(peer), Wire::Recovered(c.clone()), true);
                            continue;
                        }
                        let command = request.command.clone();
                        let work = dispatch(ready.clone(), request, retain.clone());
                        peers.push(Box::pin(
                            async move { Done::Peer(peer, command, work.await) },
                        ));
                    }
                    Wire::Response(response) => {
                        if let Some(a) = active.as_mut() {
                            admit_response(
                                a,
                                response,
                                &scheme,
                                &config.context,
                                &mut context,
                                &strategy,
                            );
                        }
                    }
                    Wire::Recovered(c) => {
                        let s = &c.certificate().statement;
                        if s.domain != config.context.domain
                            || s.proposal.round.epoch() != config.epoch
                            || !<Extended as Mode<S, D>>::verify_recovered(
                                &c,
                                &mut context,
                                &scheme,
                                &strategy,
                            )
                        {
                            continue;
                        }
                        let view = s.proposal.round.view();
                        if installed.contains_key(&view) {
                            continue;
                        }
                        if queued.len() >= config.retained && !queued.contains_key(&view) {
                            return Err(Error::Capacity);
                        }
                        queued.entry(view).or_insert(c);
                    }
                }
            }
            Event::Tick => {}
        }
    }
}
// The exact request remains owned here while the callback retains its clone.
// A callback can neither substitute the request nor emit a native response.
async fn dispatch<S, D, F, Fut>(
    mut ready: Readiness<S, D, Extended>,
    request: Request<S, D>,
    retain: F,
) -> Result<Option<Response<S, D>>, RetainError>
where
    S: Scheme<D>,
    D: Digest,
    F: Fn(AdmittedRecovery<S, D>) -> Fut,
    Fut: Future<Output = Result<(), RetainError>>,
{
    if matches!(request.command, Command::Accept(_)) {
        let Some(admission) = ready.admit_recovery(request.clone()).await else {
            return Ok(None);
        };
        retain(admission).await?;
    }
    Ok(ready.request_recovery(request).await.ok().flatten())
}

fn admit_response<S: Scheme<D>, D: Digest>(
    a: &mut Attempt<S, D>,
    response: Response<S, D>,
    scheme: &S,
    config: &ExtendedContext<D>,
    rng: &mut impl CryptoRng,
    strategy: &impl Strategy,
) {
    let quorum = N3f1::quorum(scheme.participants().len() as u32) as usize;
    if response.encode_size() > MAX_BYTES {
        return;
    }
    match &response {
        Response::Status { status, accepted }
            if a.phase == Phase::Statuses && a.statuses.len() < quorum =>
        {
            let p = &status.promise;
            if p.proposal != *a.promise.command.proposal()
                || p.domain != a.promise.command.domain()
                || p.ballot != a.promise.command.ballot()
                || p.accepted != accepted.as_ref().map(|s| (s.ballot, config.value(s)))
                || accepted
                    .as_ref()
                    .is_some_and(|s| s.proposal != p.proposal || s.domain != p.domain)
                || !status.verify(rng, scheme, strategy)
            {
                return;
            }
            a.statuses
                .entry(status.attestation.signer)
                .or_insert(response);
        }
        Response::Vote(v) if a.phase == Phase::Votes && a.votes.len() < quorum => {
            if a.accept.as_ref().and_then(|r| r.command.subject()) != Some(&v.statement)
                || !v.verify(rng, scheme, strategy)
            {
                return;
            }
            a.votes
                .entry(v.attestation.signer)
                .or_insert_with(|| v.clone());
        }
        _ => {}
    }
}

// Retransmissions cannot extend suppression, and unrelated later slots cannot
// postpone recovery of the earliest outstanding parent indefinitely.
fn follow<D: Digest>(old: &Command<D>, new: &Command<D>) -> bool {
    new.proposal().round.view() < old.proposal().round.view()
        || new.proposal() == old.proposal() && new.ballot() > old.ballot()
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::{simplex::types::Proposal, types::Round};
    use commonware_cryptography::sha256::Digest as D;
    fn command(view: u64, ballot: u64) -> Command<D> {
        Command::Promise {
            proposal: Proposal::new(
                Round::new(Epoch::new(1), View::new(view)),
                View::zero(),
                D::from([view as u8; 32]),
            ),
            domain: D::from([1; 32]),
            ballot: Round::new(Epoch::new(1), View::new(ballot)),
        }
    }
    #[test]
    fn valid_request_replays_and_other_slots_cannot_keep_renewing_suppression() {
        let old = command(2, 5);
        assert!(!follow(&old, &command(2, 5)));
        assert!(!follow(&old, &command(2, 4)));
        assert!(!follow(&old, &command(3, 6)));
        assert!(follow(&old, &command(2, 6)));
        assert!(follow(&old, &command(1, 4)));
    }
}
