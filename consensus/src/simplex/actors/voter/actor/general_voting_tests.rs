//! Real General Mode Actor/Journal checks with an explicit empty-cut policy.
//! This is not SDK/host integration, later-ballot recovery or Source delivery.
use super::*;
use crate::{
    simplex::{
        extension::agreement::general as g,
        phase2::{
            Mode,
            general::{
                FirstVote, General,
                voting::{
                    Context as GeneralContext, FinalSubject, FirstInput, Resources, SelectRequest,
                },
                voting_wal::Wal,
            },
        },
    },
    types::Participant,
};
use commonware_codec::Encode as _;
use core::panic;
use std::sync::atomic::{AtomicUsize, Ordering};

type G = General<Sha256>;
type Capture = (FirstInput<D>, Context<D, PublicKey>);
const LIMITS: g::Limits = g::Limits {
    report_bytes: 128,
    order_bytes: 128,
    build_bytes: 128,
    material_bytes: 0,
    origin_bytes: g::MAX_EVIDENCE_BYTES,
};
const INPUT: D = D([31; 32]);
const PROFILE: D = D([32; 32]);
const DOMAIN: D = D([33; 32]);
const POPULATION: D = D([34; 32]);
const EMPTY_ORDER: &[u8] = &[0, 0, 0, 0];
const BUILD: &[u8] = b"declared-empty-cut-policy-v1";

fn context(records: usize) -> GeneralContext<S, D> {
    GeneralContext::new(
        Epoch::new(1),
        PROFILE,
        DOMAIN,
        D([0; 32]),
        LIMITS,
        Resources {
            slots: 2,
            handles: 8,
            bytes: 2 * g::MAX_EVIDENCE_BYTES,
            records_per_slot: records,
        },
    )
    .unwrap()
}

fn row_policy(core: &g::Core<D>, row: &g::First<D>) -> bool {
    row.core == core.id::<Sha256>()
        && row.input == INPUT
        && (row.owner == core.leader || core.followers.contains(&row.owner))
        && row.report.is_none()
        && if row.owner == core.leader {
            row.preference.is_none()
        } else {
            row.preference.as_deref() == Some(EMPTY_ORDER)
        }
}

fn build_policy(
    core: &g::Core<D>,
    rows: &g::VerifiedRows<S, D>,
    body: &g::OriginBody<S, D>,
) -> bool {
    rows.core() == core
        && rows.input() == INPUT
        && body.core == *core
        && body.decision.slot == core.slot
        && body.decision.input == INPUT
        && body.decision.order.as_ref() == EMPTY_ORDER
        && body.population == POPULATION
        && body.build.as_ref() == BUILD
        && body.material.is_empty()
        && body.firsts.len() == rows.originals().len()
        && body
            .firsts
            .iter()
            .zip(rows.originals())
            .all(|(a, b)| a.encode() == b.encode())
}

#[derive(Clone)]
struct Evidence {
    owner: Participant,
    capture: Arc<Mutex<Option<Capture>>>,
    captures: Arc<AtomicUsize>,
    assembly: Arc<Mutex<Option<g::normal::Assembly<S, D>>>>,
}
impl Participation<S, D, G> for Evidence {
    fn capture_notarize(
        &mut self,
        p: &Proposal<D>,
        native: &Context<D, PublicKey>,
    ) -> Option<FirstInput<D>> {
        self.captures.fetch_add(1, Ordering::SeqCst);
        self.capture
            .lock()
            .as_ref()
            .filter(|(input, captured)| input.core().slot.proposal == *p && captured == native)
            .map(|(input, _)| input.clone())
    }
    fn notarize(&mut self, _: Notarize<S, D>) -> FirstVote<S, D> {
        panic!("General must use its pre-sign reservation path")
    }
    fn final_subject(&mut self, p: &Proposal<D>) -> Option<FinalSubject<D>> {
        self.assembly
            .lock()
            .as_ref()
            .filter(|a| a.proposal() == p)
            .map(FinalSubject::new::<Sha256, S>)
    }
    fn accepts_finalization(&mut self, _: &<G as Mode<S, D>>::Certificate) -> bool {
        false // This fixture never supplies a final-certificate delivery policy.
    }
    fn accepts_replay(&mut self, a: &ArtifactWith<S, D, G>) -> bool {
        let captured = self.capture.lock();
        let Some((input, _)) = captured.as_ref() else {
            return false;
        };
        match a {
            ArtifactWith::Recovery(w) => {
                let record = w.agreement();
                record.core() == input.core()
                    && record.input() == input.input()
                    && record.owner() == self.owner
            }
            ArtifactWith::Notarize(v) => v.native().proposal == input.core().slot.proposal,
            ArtifactWith::Notarization(c) => c.proposal == input.core().slot.proposal,
            ArtifactWith::Certification(round, success) => {
                *round == input.core().slot.proposal.round && *success
            }
            ArtifactWith::Finalize(v) => {
                v.inner().native.statement.proposal == input.core().slot.proposal
            }
            _ => false,
        }
    }
    fn prune(&mut self, _: View) {}
}
#[derive(Clone)]
struct Sink;
impl Reporter for Sink {
    type Activity = ActivityWith<S, D, G>;
    fn report(&mut self, _: Self::Activity) -> Feedback {
        Feedback::Ok
    }
}

macro_rules! config {
    ($scheme:expr,$cache:expr,$n:expr) => {
        Config {
            scheme: $scheme.clone(),
            elector: RoundRobin::<Sha256>::default().build($scheme.participants()),
            blocker: NoopBlocker::default(),
            automaton: App::default(),
            relay: App::default(),
            reporter: Sink,
            partition: "general-voting".into(),
            epoch: Epoch::new(1),
            floor: FloorWith::Genesis(D([0; 32])),
            mailbox_size: NZUsize!(16),
            leader_timeout: Duration::from_secs(60),
            certification_timeout: Duration::from_secs(60),
            timeout_retry: Duration::from_secs(60),
            skip_budget: u64::from($n),
            view_retention: ViewDelta::new(10),
            replay_buffer: NZUsize!(4096),
            write_buffer: NZUsize!(4096),
            page_cache: $cache.clone(),
        }
    };
}

// role 0: actual native leader; 1: Core follower; 2: outside-Core validator.
fn run(n: u32, role: u8, normal: bool, records: usize) {
    run_case(n, role, normal, records, true, false, Retry::None);
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Retry {
    None,
    Select,
    InitialHistory,
}

fn run_case(
    n: u32,
    role: u8,
    normal: bool,
    records: usize,
    first_enabled: bool,
    foreign: bool,
    retry: Retry,
) {
    deterministic::Runner::timed(Duration::from_secs(20)).start(move |mut runtime| async move {
        let retry_select = retry == Retry::Select;
        let recover = retry == Retry::InitialHistory;
        assert!(!foreign || (!first_enabled && normal && role == 2));
        assert!(!retry_select || (first_enabled && normal && role == 0 && records == 6));
        let f = ed25519::fixture(&mut runtime, b"_COMMONWARE_CONSENSUS_GENERAL_ACTOR_TEST", n);
        let elector: crate::simplex::elector::RoundRobinElector<S> =
            RoundRobin::<Sha256>::default().build(f.verifier.participants());
        let leader = elector.elect(proposal(1).round, None);
        let slot = g::Slot {
            profile: PROFILE,
            domain: DOMAIN,
            roster: g::Slot::roster::<Sha256, _>(&f.verifier),
            cut: 1,
            proposal: proposal(1),
            parent: g::NativeParent::Genesis(D([0; 32])),
        };
        let core = g::Core::derive::<Sha256, _>(&f.verifier, slot.clone(), leader).unwrap();
        let owner = match role {
            0 => usize::from(leader),
            1 => usize::from(core.followers[0]),
            2 => (0..n as usize)
                .find(|&i| {
                    let p = Participant::new(i as u32);
                    p != leader && !core.followers.contains(&p)
                })
                .unwrap(),
            _ => unreachable!(),
        };
        let scheme = f.schemes[owner].clone();
        let config_context = context(records);
        let evidence = Evidence {
            owner: Participant::new(owner as u32),
            capture: Arc::new(Mutex::new(None)),
            captures: Arc::new(AtomicUsize::new(0)),
            assembly: Arc::new(Mutex::new(None)),
        };
        let cache = CacheRef::from_pooler(&runtime, NZU16!(1024), NZUsize!(10));
        let mut config = config!(scheme, cache, n);
        if recover {
            config.certification_timeout = Duration::from_millis(100);
        }
        let (mut actor, mailbox) = ActorWith::new_with(
            runtime.child("live"),
            config,
            config_context.clone(),
            evidence.clone(),
        );
        let mut readiness = crate::simplex::engine::Readiness::new(mailbox);
        actor.state.set_genesis(D([0; 32]));
        let native = if role == 0 {
            let native = actor.state.try_propose().unwrap();
            let proposed = actor.automaton.propose(native.clone()).await;
            actor
                .automaton
                .0
                .lock()
                .pop()
                .unwrap()
                .send(proposal(1).payload)
                .unwrap();
            assert_eq!(proposed.await.unwrap(), proposal(1).payload);
            assert!(actor.state.proposed(proposal(1)));
            native
        } else {
            assert!(actor.state.set_proposal(View::new(1), proposal(1)));
            let Verify::Ready(native, p) = actor.state.try_verify() else {
                panic!("real native verification must be ready")
            };
            let verdict = actor
                .automaton
                .verify(native.clone(), p.payload)
                .await
                .await;
            assert_eq!(verdict, Ok(true));
            assert!(actor.state.verified(View::new(1)));
            native
        };
        let preference = (role == 1).then(|| Bytes::from_static(EMPTY_ORDER));
        let captured = FirstInput::new::<Sha256, _>(
            &scheme,
            slot,
            &native,
            INPUT,
            None,
            preference,
            LIMITS,
            |row| row_policy(&core, row),
        )
        .unwrap();
        let bootstrap = if foreign {
            let other = (0..n as usize)
                .find(|&i| {
                    let p = Participant::new(i as u32);
                    i != owner && p != leader && !core.followers.contains(&p)
                })
                .unwrap();
            FirstInput::new::<Sha256, _>(
                &f.schemes[other],
                core.slot.clone(),
                &native,
                INPUT,
                None,
                None,
                LIMITS,
                |row| row_policy(&core, row),
            )
            .unwrap()
        } else {
            captured.clone()
        };
        config_context
            .publish_input::<Sha256>(bootstrap.clone())
            .unwrap();
        *evidence.capture.lock() = Some((captured.clone(), native));
        assert!(actor.state.construct_notarize(View::new(1)).is_none());
        let journal_config = JConfig {
            partition: "general-voting".into(),
            compression: None,
            codec_config: scheme.certificate_codec_config(),
            page_cache: cache.clone(),
            write_buffer: NZUsize!(4096),
        };
        actor.journal = Some(
            Journal::init(actor.context.child("journal"), journal_config.clone())
                .await
                .unwrap(),
        );
        let first = if first_enabled {
            let (next, first) = Box::pin(actor.prepare_notarize(View::new(1))).await;
            actor = next.sync_journal().await;
            let first = first.unwrap();
            first
                .authenticate(&mut runtime, &scheme, &Sequential)
                .unwrap();
            assert_eq!(
                first.native().attestation.signer,
                Participant::new(owner as u32)
            );
            assert_eq!(first.first().is_some(), role != 2);
            let (next, duplicate) = Box::pin(actor.prepare_notarize(View::new(1))).await;
            actor = next;
            assert!(duplicate.is_none());
            Some(first)
        } else {
            None
        };
        assert_eq!(
            evidence.captures.load(Ordering::SeqCst),
            usize::from(first_enabled)
        );

        let mut material = None;
        let mut final_vote = None;
        if normal {
            let q = g::Committee::new(n as usize).unwrap().quorum();
            let native_votes: Vec<_> = f
                .schemes
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != owner)
                .take(q)
                .map(|(_, s)| Notarize::sign(s, proposal(1)).unwrap())
                .collect();
            let nqc = Notarization::from_notarizes(
                &f.verifier,
                non_empty![@native_votes.iter()],
                &Sequential,
            )
            .unwrap();
            assert!(nqc.verify(&mut runtime, &f.verifier, &Sequential));
            (actor, _) = Box::pin(actor.process_message(Message::Verified {
                span: tracing::Span::none(),
                certificate: CertificateWith::Notarization(nqc.clone()),
                from_resolver: false,
            }))
            .await;
            actor = actor.sync_journal().await;
            let (ready, fetch) = actor.state.certify_candidates();
            assert_eq!(ready, vec![proposal(1)]);
            assert!(fetch.is_empty());
            let verdict = actor
                .automaton
                .certify(proposal(1).round, proposal(1).payload)
                .await
                .await;
            let (next, live, result) =
                Box::pin(actor.process_certified(proposal(1).round, verdict)).await;
            actor = next.sync_journal().await;
            assert!(live && result.is_some());

            let mut owners = core.followers.clone();
            owners.push(leader);
            owners.sort_unstable();
            let firsts = owners
                .into_iter()
                .map(|owner| {
                    if Some(owner) == scheme.me() {
                        return first.as_ref().unwrap().first().unwrap().clone();
                    }
                    let row = g::First {
                        core: core.id::<Sha256>(),
                        input: INPUT,
                        owner,
                        report: None,
                        preference: (owner != leader).then(|| Bytes::from_static(EMPTY_ORDER)),
                    };
                    g::Signed::sign(
                        &f.schemes[usize::from(owner)],
                        g::Message {
                            slot: core.slot.id::<Sha256>(),
                            round: proposal(1).round,
                            leader,
                            kind: g::Kind::First(row),
                        },
                        LIMITS,
                    )
                    .unwrap()
                })
                .collect();
            let body = g::OriginBody {
                decision: g::Decision {
                    slot: core.slot.clone(),
                    input: INPUT,
                    order: Bytes::from_static(EMPTY_ORDER),
                },
                core: core.clone(),
                firsts,
                population: POPULATION,
                build: Bytes::from_static(BUILD),
                material: Bytes::new(),
            };
            let checked = body
                .verify::<Sha256, _>(
                    &mut runtime,
                    &f.verifier,
                    &core,
                    INPUT,
                    LIMITS,
                    |row| row_policy(&core, row),
                    |rows, body| build_policy(&core, rows, body),
                    &Sequential,
                )
                .unwrap();
            let selection = config_context
                .publish_selection::<Sha256>(body, checked)
                .unwrap();
            assert_eq!(
                <G as crate::simplex::phase2::voting::Voting<S, D>>::validate_recovery_request(
                    &mut actor.state,
                    &SelectRequest::new(&selection),
                ),
                role == 0,
                "SELECT admission belongs to the actual native leader"
            );
            let select = if role == 0 {
                let rx = readiness.request_selection(SelectRequest::new(&selection));
                let live_reply = if retry_select {
                    drop(rx);
                    None
                } else {
                    Some(rx)
                };
                let message = actor.mailbox_receiver.recv().await.unwrap();
                (actor, _) = Box::pin(actor.process_message(message)).await;
                if retry_select {
                    let retried = readiness.request_selection(SelectRequest::new(&selection));
                    let message = actor.mailbox_receiver.recv().await.unwrap();
                    (actor, _) = Box::pin(actor.process_message(message)).await;
                    retried.await.unwrap().unwrap()
                } else {
                    live_reply.unwrap().await.unwrap().unwrap()
                }
            } else {
                g::Signed::sign(
                    &f.schemes[usize::from(leader)],
                    g::Message {
                        slot: core.slot.id::<Sha256>(),
                        round: proposal(1).round,
                        leader,
                        kind: g::Kind::Select {
                            body: selection.checked().body(),
                            decision: selection.checked().decision(),
                        },
                    },
                    LIMITS,
                )
                .unwrap()
            };
            let origin = g::Origin {
                body: selection.body().clone(),
                selection: select,
            };
            let assembly = g::normal::Assembly::new::<Sha256, _>(
                &mut runtime,
                &f.verifier,
                &core,
                INPUT,
                origin,
                nqc,
                LIMITS,
                |row| row_policy(&core, row),
                |rows, body| build_policy(&core, rows, body),
                &Sequential,
            )
            .unwrap();
            config_context
                .publish_assembly::<Sha256>(assembly.clone())
                .unwrap();
            *evidence.assembly.lock() = Some(assembly.clone());
            assert!(actor.state.pending_finalize(View::new(1)).is_none());
            let (next, pair) = Box::pin(actor.prepare_finalize(View::new(1))).await;
            actor = next.sync_journal().await;
            if foreign {
                assert!(
                    pair.is_none(),
                    "foreign bootstrap owner must not authorize local final signing"
                );
                assert!(
                    actor.state.pending_finalize(View::new(1)).is_none(),
                    "foreign bootstrap consumed a native final choice"
                );
            } else {
                let pair = pair.unwrap();
                assert!(G::verify_finalize(
                    &pair,
                    &mut runtime,
                    &scheme,
                    &Sequential
                ));
                final_vote = Some(pair);
            }
            if retry_select {
                let before = evidence.captures.load(Ordering::SeqCst);
                let rx = readiness.request_selection(SelectRequest::new(&selection));
                let message = actor.mailbox_receiver.recv().await.unwrap();
                (actor, _) = Box::pin(actor.process_message(message)).await;
                let retried = rx.await.unwrap().unwrap();
                assert_eq!(retried.encode(), assembly.origin().selection.encode());
                assert_eq!(evidence.captures.load(Ordering::SeqCst), before);
                assert!(actor.dirty_section.is_none());
            }
            material = Some((selection, assembly));
        }
        let mut history = None;
        if recover {
            let votes: Vec<_> = f.schemes.iter().take(g::Committee::new(n as usize).unwrap().quorum())
                .map(|s| Notarize::sign(s, proposal(1)).unwrap()).collect();
            let nqc = Notarization::from_notarizes(&scheme, non_empty![@votes.iter()], &Sequential).unwrap();
            assert!(nqc.verify(&mut runtime, &f.verifier, &Sequential));
            // A stale native view clock cannot authorize recovery on first NQC arrival.
            runtime.sleep(Duration::from_millis(120)).await;
            (actor, _) = Box::pin(actor.process_message(Message::Verified {
                span: tracing::Span::none(), certificate: CertificateWith::Notarization(nqc), from_resolver: false,
            })).await;
            let report = Some(Bytes::from_static(b"ready"));
            let early = readiness.request_initial_history(&captured, report.clone());
            let msg = actor.mailbox_receiver.recv().await.unwrap();
            (actor, _) = Box::pin(actor.process_message(msg)).await;
            assert!(early.await.unwrap().is_none());
            runtime.sleep(Duration::from_millis(101)).await;
            let canceled = readiness.request_initial_history(&captured, report.clone());
            drop(canceled);
            let msg = actor.mailbox_receiver.recv().await.unwrap();
            (actor, _) = Box::pin(actor.process_message(msg)).await;
            let retry = readiness.request_initial_history(&captured, report.clone());
            let msg = actor.mailbox_receiver.recv().await.unwrap();
            (actor, _) = Box::pin(actor.process_message(msg)).await;
            let signed = retry.await.unwrap().unwrap();
            assert!(signed.verify(&mut runtime, &f.verifier, LIMITS, &Sequential));
            assert!(matches!(&signed.message.kind, g::Kind::Recover(row) if row.report == report && row.snapshot.owner() == Participant::new(owner as u32)));
            let g::Kind::Recover(row) = &signed.message.kind else { unreachable!() };
            let head = row.snapshot.head().unwrap();
            use crate::simplex::phase2::general::voting::{HistoryMaterial, HistoryQuery};
            for (digest, index, valid) in [(head, None, true), (head, Some(0), true),
                (head, Some(row.snapshot.count() as usize), false), (INPUT, None, false)] {
                let reply = readiness.history_material(HistoryQuery::new::<Sha256>(&captured, digest, index));
                let msg = actor.mailbox_receiver.recv().await.unwrap();
                (actor, _) = Box::pin(actor.process_message(msg)).await;
                match reply.await.unwrap() {
                    Some(HistoryMaterial::Notice(_)) => panic!("expected a history witness"),
                    Some(HistoryMaterial::Entry(proof)) => {
                        assert!(valid && index.is_none());
                        assert_eq!(proof.target().id::<Sha256>(), row.entry);
                    },
                    Some(HistoryMaterial::Page(page)) => {
                        assert!(valid && index.is_some());
                        assert_eq!(page.record().slot(), &core.slot);
                    },
                    None => assert!(!valid),
                }
            }
            let changed = readiness.request_initial_history(&captured, None);
            let msg = actor.mailbox_receiver.recv().await.unwrap();
            (actor, _) = Box::pin(actor.process_message(msg)).await;
            assert!(changed.await.unwrap().is_none());
            history = Some(signed);
        }
        drop(actor);

        let journal =
            Journal::<_, ArtifactWith<S, D, G>>::init(runtime.child("inspect"), journal_config.clone())
                .await
                .unwrap();
        let mut replay = journal
            .replay(0, 0, NZUsize!(4096), ReadOptions::DONT_CACHE)
            .await
            .unwrap();
        let mut rows = Vec::new();
        while let Some(row) = replay.next().await {
            rows.push(row.unwrap().3);
        }
        drop(replay.finish().unwrap());
        assert_eq!(
            rows.iter()
                .filter(|r| matches!(r, ArtifactWith::Notarize(_)))
                .count(),
            usize::from(first_enabled)
        );
        assert_eq!(
            rows.iter()
                .filter(|r| matches!(r, ArtifactWith::Recovery(_)))
                .count(),
            if foreign {
                0
            } else if recover {
                2 * usize::from(first_enabled) + 3
            } else if !first_enabled {
                2
            } else if normal {
                if role == 0 {
                    6 + 2 * usize::from(retry_select)
                } else {
                    4
                }
            } else {
                2
            }
        );
        if retry_select {
            let recovery: Vec<_> = rows
                .iter()
                .filter_map(|row| match row {
                    ArtifactWith::Recovery(w) => Some(w),
                    _ => None,
                })
                .collect();
            assert_eq!(recovery.iter().filter(|w| w.encode()[8] == 2).count(), 3);
            assert_eq!(
                recovery.iter().filter(|w| w.encode()[8] == 3).count(),
                1,
                "a retained SELECT retry must not persist another release receipt"
            );
            let logical: std::collections::BTreeSet<_> = recovery
                .iter()
                .flat_map(|w| logical_records(w))
                .map(|r| r.id::<Sha256>())
                .collect();
            assert_eq!(logical.len(), 6);
            assert_eq!(
                recovery.len(),
                8,
                "physical WAL may repeat an existing logical record"
            );
        }
        if !first_enabled && !foreign && !recover {
            // Decode the actual optional NoFirst inside the Normal WAL frame.
            // Its tag follows G1W2 + the u32 body length; the native Record
            // decoder validates the closure rather than a fabricated marker.
            let joint = rows
                .iter()
                .find_map(|a| match a {
                    ArtifactWith::Recovery(w) if w.encode()[8] == 4 => Some(w),
                    _ => None,
                })
                .unwrap();
            let mut payload = joint.encode().slice(9..);
            let closure = Option::<g::issuance::Record<D>>::read_cfg(&mut payload, &LIMITS)
                .unwrap()
                .unwrap();
            assert!(matches!(closure.action(), g::issuance::Action::NoFirst));
            assert_eq!(closure.owner(), Participant::new(owner as u32));
            assert_eq!(closure.core(), &core);
        }

        // Reopen the real journal, then drive native State replay explicitly.
        // This is not the Actor startup/network loop.
        let fresh_context = context(records);
        fresh_context.publish_input::<Sha256>(bootstrap.clone()).unwrap();
        if let Some((selection, assembly)) = &material {
            fresh_context
                .publish_selection::<Sha256>(selection.body().clone(), selection.checked().clone())
                .unwrap();
            fresh_context
                .publish_assembly::<Sha256>(assembly.clone())
                .unwrap();
        }
        let (mut fresh, _) = ActorWith::new_with(
            runtime.child("fresh"),
            config!(scheme, cache, n),
            fresh_context,
            evidence.clone(),
        );
        fresh.state.set_genesis(D([0; 32]));
        let mut replayed_final = false;
        let history_record = rows.iter().find_map(|r| match r {
            ArtifactWith::Recovery(w) if w.encode()[8] == 6 => Some(w.clone()),
            _ => None,
        });
        if let Some(record) = &history_record {
            let ctx = context(records);
            ctx.publish_input::<Sha256>(bootstrap.clone()).unwrap();
            let mut cfg = config!(scheme, cache, n);
            cfg.certification_timeout = Duration::from_millis(100);
            let (mut interrupted, retry_box) = ActorWith::new_with(runtime.child("before_receipt"), cfg, ctx, evidence.clone());
            interrupted.state.set_genesis(D([0; 32]));
            for item in &rows {
                if let ArtifactWith::Notarization(nqc) = item { interrupted.state.add_notarization(nqc.clone()); }
                interrupted.state.replay(item);
                if let ArtifactWith::Recovery(w) = item && w == record { break; }
            }
            interrupted.state.finish_notarize_replay();
            assert!(interrupted.state.sign_recovery(record).is_none(), "uncertain signer invocation after crash");
            let mut log_config = journal_config.clone();
            log_config.partition = "interrupted-retry-appends".into();
            interrupted.journal = Some(Journal::init(interrupted.context.child("retry_journal"),log_config).await.unwrap());
            let section = core.slot.proposal.view().get();
            let before = interrupted.journal.as_ref().unwrap().size(section).ok();
            let report = Some(Bytes::from_static(b"ready"));
            runtime.sleep(Duration::from_millis(101)).await;
            assert!(<G as Voting<S,D>>::validate_recovery_request(&mut interrupted.state,
                &SelectRequest::initial_history::<Sha256>(&bootstrap,report.clone()).unwrap()));
            let mut ready = crate::simplex::engine::Readiness::new(retry_box);
            for _ in 0..2 {
                let reply = ready.request_initial_history(&bootstrap, report.clone());
                let message = interrupted.mailbox_receiver.recv().await.unwrap();
                (interrupted, _) = Box::pin(interrupted.process_message(message)).await;
                assert!(reply.await.unwrap().is_none());
                assert_eq!(interrupted.journal.as_ref().unwrap().size(section).ok(),before);
            }
            for item in &rows {
                if let ArtifactWith::Recovery(w) = item {
                    let frame = w.encode();
                    if matches!(frame[8], 6 | 7) {
                        assert!(Wal::<S,D>::decode(frame.slice(..frame.len()-1)).is_err());
                    }
                }
            }
        }
        for row in rows {
            assert!(fresh.participation.accepts_replay(&row));
            if let ArtifactWith::Notarization(c) = &row {
                fresh.state.add_notarization(c.clone());
            }
            if let ArtifactWith::Finalize(persisted) = &row {
                let pair = final_vote.as_ref().unwrap();
                assert_eq!(persisted.encode(), pair.encode());
                let subject = FinalSubject::new::<Sha256, S>(&material.as_ref().unwrap().1);
                assert_eq!(
                    fresh.state.pending_finalize(View::new(1)),
                    Some(subject.clone())
                );
                let (retained, receipt) = fresh
                    .state
                    .sign_reserved_finalize(View::new(1), subject)
                    .unwrap();
                assert!(receipt.is_none());
                assert_eq!(retained.encode(), pair.encode());
                replayed_final = true;
            }
            fresh.state.replay(&row);
        }
        fresh.state.finish_notarize_replay();
        if let Some(signed) = history {
            let record = history_record.expect("durable history was missing");
            let (replayed, receipt) = fresh.state.sign_recovery(&record).expect("restored history outbox");
            assert!(receipt.is_none());
            assert_eq!(replayed.encode(), signed.encode());
            drop(fresh);
            // Reopen the same native partition in the actual voter startup loop.
            // Only the immutable checked application input is supplied again.
            let restored_context = context(records);
            restored_context.publish_input::<Sha256>(bootstrap.clone()).unwrap();
            let (network, oracle) = Network::new_with_peers(runtime.child("history_network"), NConfig {
                max_size: 1024*1024, max_peers_per_set: std::num::NonZeroUsize::new(n as usize).unwrap(),
                disconnect_on_block: true, tracked_peer_sets: NZUsize!(1),
            }, f.participants.clone()).await;
            network.start();
            let me = f.participants[owner].clone();
            let (votes, _) = oracle.control(me.clone()).register(0, Quota::per_second(NZU32!(1000))).await.unwrap();
            let (certificates, _) = oracle.control(me).register(1, Quota::per_second(NZU32!(1000))).await.unwrap();
            let (restored, mailbox) = ActorWith::new_with(runtime.child("restarted_history"),
                config!(scheme, cache, n), restored_context, evidence.clone());
            let mut ready = crate::simplex::engine::Readiness::new(mailbox);
            let (btx, _brx) = mailbox::new(runtime.child("history_batcher"), NZUsize!(32));
            let (rtx, _rrx) = mailbox::new(runtime.child("history_resolver"), NZUsize!(32));
            let handle = restored.start(batcher::Mailbox::new(btx), resolver::Mailbox::new(rtx), votes, certificates);
            use crate::simplex::phase2::general::voting::{HistoryMaterial, HistoryQuery};
            let published = ready.history_material(HistoryQuery::published::<Sha256>(&bootstrap)).await.unwrap();
            let Some(HistoryMaterial::Notice(old)) = published else { panic!("missing published history after startup") };
            assert_eq!(old.encode(), signed.encode());
            handle.abort();
            let _ = handle.await;
            return;
        }
        assert_eq!(replayed_final, final_vote.is_some());
        if final_vote.is_some() {
            assert!(fresh.state.pending_finalize(View::new(1)).is_none());
            let (_, duplicate) = Box::pin(fresh.prepare_finalize(View::new(1))).await;
            assert!(
                duplicate.is_none(),
                "complete replay must not emit another pair"
            );
        }
        assert_eq!(
            evidence.captures.load(Ordering::SeqCst),
            usize::from(first_enabled)
        );
    });
}

#[test]
fn real_general_actor_first_wal_covers_core_and_outside_rosters() {
    for n in [4, 8, 10, 13] {
        for role in [0, 1, 2] {
            run(n, role, false, 16);
        }
    }
}

#[test]
fn general_core_follower_exact_history_capacity_replays_actual_actor_wal() {
    run(8, 1, true, 4);
}

#[test]
fn general_leader_select_and_normal_use_public_readiness_and_journal_across_rosters() {
    for n in [4, 8, 10, 13, 16] {
        run(n, 0, true, 16);
    }
}

#[test]
fn general_outside_core_normal_before_local_first_retains_explicit_closure() {
    for n in [4, 8, 10, 13] {
        run_case(n, 2, true, 4, false, false, Retry::None);
    }
}

#[test]
fn general_foreign_bootstrap_owner_cannot_authorize_local_normal_pair() {
    run_case(8, 2, true, 4, false, true, Retry::None);
}

// Inspect canonical WAL fields with their real decoders. The journal has
// already decoded each complete Wal; here repeated reservations count once.
fn logical_records(w: &Wal<S, D>) -> Vec<g::issuance::Record<D>> {
    let frame = w.encode();
    let mut b = frame.slice(9..);
    let record = |b: &mut Bytes| g::issuance::Record::<D>::read_cfg(b, &LIMITS).unwrap();
    match frame[8] {
        0 | 2 => vec![record(&mut b)],
        1 => {
            let mut records = vec![record(&mut b)];
            records.extend(Option::<g::issuance::Record<D>>::read_cfg(&mut b, &LIMITS).unwrap());
            records
        }
        3 => vec![record(&mut b), record(&mut b)],
        4 => {
            let mut records: Vec<_> = Option::<g::issuance::Record<D>>::read_cfg(&mut b, &LIMITS)
                .unwrap()
                .into_iter()
                .collect();
            let reservation = g::normal::Reservation::<D>::read_cfg(&mut b, &LIMITS).unwrap();
            records.push(reservation.agreement().clone());
            records
        }
        5 => {
            let released = g::normal::Released::<S, D>::read_cfg(&mut b, &LIMITS).unwrap();
            vec![
                released.reservation().agreement().clone(),
                released.receipt().clone(),
            ]
        }
        _ => unreachable!(),
    }
}

#[test]
fn general_at_capacity_select_reply_retry_retains_exact_outbox() {
    // Cancel the first queued reply, then retry before and at logical capacity.
    // Check exact bytes and receipts; signer calls are not independently counted.
    run_case(10, 0, true, 6, true, false, Retry::Select);
}

#[path = "general_history_tests.rs"]
mod history_tests;

#[test]
fn initial_history_fences_journals_and_replays_with_seven_validators() {
    for role in 0..=2 {
        for first in [false, true] {
            run_case(7, role, false, 8, first, false, Retry::InitialHistory);
        }
    }
}
