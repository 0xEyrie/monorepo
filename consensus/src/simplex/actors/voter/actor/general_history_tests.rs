//! Actual General original history across native pruning. The empty-cut policy
//! is independent of the SDK; this is not later-ballot recovery or Source proof.
use super::*;
use crate::simplex::{extension::vote, phase2::general::Finalization as GFinalization};
use core::panic;
use rand_core::CryptoRng;

#[derive(Clone)]
struct HistoryEvidence {
    inner: Evidence,
    finalization: Arc<Mutex<Option<GFinalization<S, D>>>>,
    notarization: Arc<Mutex<Option<Notarization<S, D>>>>,
    completed: Arc<AtomicUsize>,
    restored: Arc<Mutex<Vec<Bytes>>>,
}

impl HistoryEvidence {
    fn for_restart(&self) -> Self {
        Self {
            inner: Evidence {
                owner: self.inner.owner,
                capture: self.inner.capture.clone(),
                captures: Arc::new(AtomicUsize::new(0)),
                assembly: self.inner.assembly.clone(),
            },
            finalization: self.finalization.clone(),
            notarization: self.notarization.clone(),
            completed: Arc::new(AtomicUsize::new(0)),
            restored: Arc::new(Mutex::new(Vec::new())),
        }
    }
}

impl Participation<S, D, G> for HistoryEvidence {
    fn replayed(&mut self) {
        self.completed.fetch_add(1, Ordering::SeqCst);
    }
    fn capture_notarize(
        &mut self,
        proposal: &Proposal<D>,
        native: &Context<D, PublicKey>,
    ) -> Option<FirstInput<D>> {
        self.inner.capture_notarize(proposal, native)
    }
    fn notarize(&mut self, vote: Notarize<S, D>) -> FirstVote<S, D> {
        self.inner.notarize(vote)
    }
    fn final_subject(&mut self, proposal: &Proposal<D>) -> Option<FinalSubject<D>> {
        self.inner.final_subject(proposal)
    }
    fn accepts_finalization(&mut self, certificate: &GFinalization<S, D>) -> bool {
        self.finalization.lock().as_ref() == Some(certificate)
    }
    fn accepts_replay(&mut self, artifact: &ArtifactWith<S, D, G>) -> bool {
        assert_eq!(self.completed.load(Ordering::SeqCst), 0);
        let accepted = match artifact {
            ArtifactWith::Finalization(certificate) => self.accepts_finalization(certificate),
            ArtifactWith::Notarization(certificate) => {
                self.notarization.lock().as_ref() == Some(certificate)
            }
            ArtifactWith::Nullify(vote) => {
                self.inner
                    .capture
                    .lock()
                    .as_ref()
                    .is_some_and(|(input, _)| {
                        vote.round == input.core().slot.proposal.round
                            && vote.attestation.signer == self.inner.owner
                    })
            }
            _ => self.inner.accepts_replay(artifact),
        };
        if accepted && let ArtifactWith::Recovery(record) = artifact {
            self.restored.lock().push(record.encode());
        }
        accepted
    }
    fn prune(&mut self, _: View) {}
}

fn nqc(f: &Fixture<S>, owner: usize, proposal: &Proposal<D>) -> Notarization<S, D> {
    let q = g::Committee::new(f.schemes.len()).unwrap().quorum();
    let votes: Vec<_> = f
        .schemes
        .iter()
        .enumerate()
        .filter(|(i, _)| *i != owner)
        .take(q)
        .map(|(_, s)| Notarize::sign(s, proposal.clone()).unwrap())
        .collect();
    Notarization::from_notarizes(&f.verifier, non_empty![@votes.iter()], &Sequential).unwrap()
}

// The local row, when present, is the exact Actor-produced FIRST envelope.
fn origin_body(
    f: &Fixture<S>,
    core: &g::Core<D>,
    local: Option<&FirstVote<S, D>>,
) -> g::OriginBody<S, D> {
    let mut owners = core.followers.clone();
    owners.push(core.leader);
    owners.sort_unstable();
    let firsts = owners
        .into_iter()
        .map(|owner| {
            if let Some(first) = local
                && first.native().attestation.signer == owner
            {
                return first.first().unwrap().clone();
            }
            g::Signed::sign(
                &f.schemes[usize::from(owner)],
                g::Message {
                    slot: core.slot.id::<Sha256>(),
                    round: core.slot.proposal.round,
                    leader: core.leader,
                    kind: g::Kind::First(g::First {
                        core: core.id::<Sha256>(),
                        input: INPUT,
                        owner,
                        report: None,
                        preference: (owner != core.leader).then(|| Bytes::from_static(EMPTY_ORDER)),
                    }),
                },
                LIMITS,
            )
            .unwrap()
        })
        .collect();
    g::OriginBody {
        core: core.clone(),
        decision: g::Decision {
            slot: core.slot.clone(),
            input: INPUT,
            order: Bytes::from_static(EMPTY_ORDER),
        },
        firsts,
        population: POPULATION,
        build: Bytes::from_static(BUILD),
        material: Bytes::new(),
    }
}

// Every signature in this peer certificate belongs to another validator. The
// local owner is outside the child Core and has not issued its child FIRST.
fn child_certificate<R: CryptoRng>(
    rng: &mut R,
    f: &Fixture<S>,
    owner: usize,
    core: &g::Core<D>,
) -> GFinalization<S, D> {
    assert!(core.leader != Participant::new(owner as u32));
    assert!(!core.followers.contains(&Participant::new(owner as u32)));
    let body = origin_body(f, core, None);
    let origin = g::Origin {
        selection: g::Signed::sign(
            &f.schemes[usize::from(core.leader)],
            g::Message {
                slot: core.slot.id::<Sha256>(),
                round: core.slot.proposal.round,
                leader: core.leader,
                kind: g::Kind::Select {
                    body: body.id::<Sha256>(),
                    decision: body.decision.id::<Sha256>(),
                },
            },
            LIMITS,
        )
        .unwrap(),
        body,
    };
    certificate_for_origin(rng, f, owner, core, &origin)
}

// Only other validators sign the final pairs; the Origin may contain our own
// previously journaled FIRST/SELECT, whose exact bytes are supplied by the Actor.
fn certificate_for_origin<R: CryptoRng>(
    rng: &mut R,
    f: &Fixture<S>,
    owner: usize,
    core: &g::Core<D>,
    origin: &g::Origin<S, D>,
) -> GFinalization<S, D> {
    let q = g::Committee::new(f.schemes.len()).unwrap().quorum();
    let votes: Vec<_> = f
        .schemes
        .iter()
        .enumerate()
        .filter(|(i, _)| *i != owner)
        .take(q)
        .map(|(_, s)| g::normal::Vote {
            native: vote::Vote::sign(s, g::normal::subject::<Sha256>(&origin.body.decision))
                .unwrap(),
            agreement: g::Signed::sign(
                s,
                g::Message {
                    slot: core.slot.id::<Sha256>(),
                    round: core.slot.proposal.round,
                    leader: core.leader,
                    kind: g::Kind::Phase {
                        phase: g::Phase::FastFinal,
                        decision: origin.body.decision.id::<Sha256>(),
                    },
                },
                LIMITS,
            )
            .unwrap(),
            origin_hint: origin.id::<Sha256>(),
        })
        .collect();
    let certificate = g::normal::Certificate::assemble::<Sha256, _>(
        rng,
        &f.verifier,
        core,
        INPUT,
        origin,
        &nqc(f, owner, &core.slot.proposal),
        &votes,
        LIMITS,
        |row| row_policy(core, row),
        |rows, body| build_policy(core, rows, body),
        &Sequential,
    )
    .unwrap();
    certificate
        .verify::<Sha256, _>(
            rng,
            &f.verifier,
            core,
            INPUT,
            LIMITS,
            |row| row_policy(core, row),
            |rows, body| build_policy(core, rows, body),
            &Sequential,
        )
        .unwrap();
    GFinalization::new(certificate)
}

#[derive(Clone, Copy)]
enum Restart {
    No,
    Ready(u64),
    MissingInput,
    Normal,
    MissingAssembly,
    Displaced,
    Nullify,
}

type HistoryActivity = ActivityWith<S, D, G>;
#[derive(Clone, Default)]
struct HistoryReporter(Arc<Mutex<Vec<HistoryActivity>>>);
impl Reporter for HistoryReporter {
    type Activity = HistoryActivity;
    fn report(&mut self, activity: Self::Activity) -> Feedback {
        self.0.lock().push(activity);
        Feedback::Ok
    }
}

fn exercise(n: u32, restart: Restart) {
    let runner = deterministic::Runner::new(
        deterministic::Config::new()
            .with_timeout(Some(Duration::from_secs(20)))
            .with_catch_panics(true),
    );
    runner.start(move |mut runtime| async move {
                let displaced = matches!(restart, Restart::Displaced);
                let normal = matches!(restart, Restart::Normal | Restart::MissingAssembly);
                let nullify = matches!(restart, Restart::Nullify);
                let chosen = if displaced {
                    Proposal { payload: D([91; 32]), ..proposal(1) }
                } else { proposal(1) };
                let f = ed25519::fixture(
                    &mut runtime,
                    b"_COMMONWARE_CONSENSUS_GENERAL_HISTORY_TEST",
                    n,
                );
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
                let original =
                    g::Core::derive::<Sha256, _>(&f.verifier, slot.clone(), leader).unwrap();
                let child = g::Core::derive::<Sha256, _>(
                    &f.verifier,
                    g::Slot {
                        cut: 2,
                        proposal: proposal(2),
                        parent: g::NativeParent::Proposal {
                            round: proposal(1).round,
                            digest: chosen.payload,
                        },
                        ..slot.clone()
                    },
                    elector.elect(proposal(2).round, None),
                )
                .unwrap();
                let owner = original
                    .followers
                    .iter()
                    .find(|owner| **owner != child.leader && !child.followers.contains(owner))
                    .copied()
                    .unwrap();
                let scheme = f.schemes[usize::from(owner)].clone();
                let config_context = context(16);
                let evidence = HistoryEvidence {
                    inner: Evidence {
                        owner,
                        capture: Arc::new(Mutex::new(None)),
                        captures: Arc::new(AtomicUsize::new(0)),
                        assembly: Arc::new(Mutex::new(None)),
                    },
                    finalization: Arc::new(Mutex::new(None)),
                    notarization: Arc::new(Mutex::new(None)),
                    completed: Arc::new(AtomicUsize::new(0)),
                    restored: Arc::new(Mutex::new(Vec::new())),
                };
                let cache = CacheRef::from_pooler(&runtime, NZU16!(1024), NZUsize!(10));
                let mut cfg = config!(scheme, cache, n);
                cfg.view_retention = ViewDelta::new(0);
                let (mut actor, _) = ActorWith::new_with(
                    runtime.child("live"),
                    cfg,
                    config_context.clone(),
                    evidence.clone(),
                );
                actor.state.set_genesis(D([0; 32]));
                assert!(actor.state.set_proposal(View::new(1), proposal(1)));
                let Verify::Ready(native, p) = actor.state.try_verify() else {
                    panic!("original verify")
                };
                assert_eq!(
                    actor
                        .automaton
                        .verify(native.clone(), p.payload)
                        .await
                        .await,
                    Ok(true)
                );
                assert!(actor.state.verified(View::new(1)));
                let captured = FirstInput::new::<Sha256, _>(
                    &scheme,
                    slot,
                    &native,
                    INPUT,
                    None,
                    Some(Bytes::from_static(EMPTY_ORDER)),
                    LIMITS,
                    |row| row_policy(&original, row),
                )
                .unwrap();
                *evidence.inner.capture.lock() = Some((captured.clone(), native));
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
                let (next, first) = Box::pin(actor.prepare_notarize(View::new(1))).await;
                actor = next.sync_journal().await;
                let first = first.unwrap();
                first
                    .authenticate(&mut runtime, &scheme, &Sequential)
                    .unwrap();
                assert!(first.first().is_some());
                if nullify {
                    // Invoke the native local timeout handler; no G1 recovery
                    // phase or peer timeout permission is synthesized here.
                    let (next, skipped) = Box::pin(actor.timeout(crate::simplex::metrics::TimeoutReason::LeaderTimeout)).await;
                    actor = next.sync_journal().await;
                    let (vote, _) = skipped.unwrap();
                    assert_eq!(vote.round, proposal(1).round);
                    assert!(vote.verify::<_, D>(&mut runtime, &scheme, &Sequential));
                }
                let nqc = nqc(&f, usize::from(owner), &chosen);
                *evidence.notarization.lock() = Some(nqc.clone());
                assert!(nqc.verify(&mut runtime, &f.verifier, &Sequential));
                (actor, _) = Box::pin(actor.process_message(Message::Verified {
                    span: tracing::Span::none(),
                    certificate: CertificateWith::Notarization(nqc.clone()),
                    from_resolver: false,
                }))
                .await;
                actor = actor.sync_journal().await;
                let (ready, fetch) = actor.state.certify_candidates();
                assert_eq!(ready, vec![chosen.clone()]);
                assert!(fetch.is_empty());
                let verdict = actor
                    .automaton
                    .certify(chosen.round, chosen.payload)
                    .await
                    .await;
                let (next, live, result) =
                    Box::pin(actor.process_certified(proposal(1).round, verdict)).await;
                actor = next.sync_journal().await;
                assert!(live && result.is_some());
                assert_eq!(actor.state.proposal(View::new(1)), Some(&chosen));
                let mut material = None;
                let mut normal_pair = None;
                if normal || nullify {
                    let body = origin_body(&f, &original, Some(&first));
                    let checked = body.verify::<Sha256, _>(
                        &mut runtime, &f.verifier, &original, INPUT, LIMITS,
                        |row| row_policy(&original, row),
                        |rows, body| build_policy(&original, rows, body), &Sequential,
                    ).unwrap();
                    let selection = config_context.publish_selection::<Sha256>(body, checked).unwrap();
                    let selected = g::Signed::sign(
                        &f.schemes[usize::from(original.leader)],
                        g::Message {
                            slot: original.slot.id::<Sha256>(), round: original.slot.proposal.round,
                            leader: original.leader,
                            kind: g::Kind::Select { body: selection.checked().body(), decision: selection.checked().decision() },
                        }, LIMITS,
                    ).unwrap();
                    let assembly = g::normal::Assembly::new::<Sha256, _>(
                        &mut runtime, &f.verifier, &original, INPUT,
                        g::Origin { body: selection.body().clone(), selection: selected },
                        nqc.clone(), LIMITS, |row| row_policy(&original, row),
                        |rows, body| build_policy(&original, rows, body), &Sequential,
                    ).unwrap();
                    config_context.publish_assembly::<Sha256>(assembly.clone()).unwrap();
                    *evidence.inner.assembly.lock() = Some(assembly.clone());
                    if normal {
                        let (next, pair) = Box::pin(actor.prepare_finalize(View::new(1))).await;
                        actor = next.sync_journal().await;
                        let pair = pair.unwrap();
                        assert!(G::verify_finalize(&pair, &mut runtime, &scheme, &Sequential));
                        normal_pair = Some(pair);
                    }
                    material = Some((selection, assembly));
                }
                let certificate = child_certificate(&mut runtime, &f, usize::from(owner), &child);
                *evidence.finalization.lock() = Some(certificate.clone());
                (actor, _) = Box::pin(actor.process_message(Message::Verified {
                    span: tracing::Span::none(),
                    certificate: CertificateWith::Finalization(certificate.clone()),
                    from_resolver: false,
                }))
                .await;
                actor = actor.sync_journal().await;
                assert_eq!(actor.state.last_finalized(), View::new(2));
                assert_eq!(actor.state.min_active(), View::new(2));
                assert!(actor.state.proposal(View::new(1)).is_some());

                let mut replay = actor
                    .journal
                    .take()
                    .unwrap()
                    .replay(0, 0, NZUsize!(4096), ReadOptions::DONT_CACHE)
                    .await
                    .unwrap();
                let mut original_records = Vec::new();
                while let Some(row) = replay.next().await {
                    if let ArtifactWith::Recovery(w) = row.unwrap().3
                        && w.view() == View::new(1)
                    {
                        original_records.push(w.encode());
                    }
                }
                actor.journal = Some(replay.finish().unwrap());
                assert_eq!(
                    original_records.len(),
                    if normal { 4 } else { 2 },
                    "actual original FIRST and optional normal reservation/receipt"
                );
                actor = Box::pin(actor.prune_views()).await;
                assert!(
                    actor.state.proposal(View::new(1)).is_none(),
                    "native round must really be pruned"
                );
                let retained = actor.state.retained_round(View::new(1)).unwrap();
                assert!(
                    <G as crate::simplex::phase2::voting::Voting<S, D>>::replay_notarize_vote(
                        retained.recovery_state(),
                        &first,
                    ),
                    "inactive retained round lost its exact original outbox"
                );
                if let Some(pair) = &normal_pair {
                    assert!(<G as crate::simplex::phase2::voting::Voting<S,D>>::replay_finalize_vote(retained.recovery_state(), pair));
                }
                assert_eq!(retained.proposal(), Some(&chosen));
                let (next, old_first) = Box::pin(actor.prepare_notarize(View::new(1))).await;
                actor = next;
                assert!(
                    old_first.is_none(),
                    "retention never reopens native first voting"
                );
                let (next, old_final) = Box::pin(actor.prepare_finalize(View::new(1))).await;
                actor = next;
                assert!(
                    old_final.is_none(),
                    "retention never reopens native final voting"
                );
                assert_eq!(evidence.inner.captures.load(Ordering::SeqCst), 1);
                drop(actor);

                let journal = Journal::<_, ArtifactWith<S, D, G>>::init(
                    runtime.child("reopen"),
                    journal_config,
                )
                .await
                .unwrap();
                let mut replay = journal
                    .replay(0, 0, NZUsize!(4096), ReadOptions::DONT_CACHE)
                    .await
                    .unwrap();
                let mut retained = Vec::new();
                let mut rows = Vec::new();
                while let Some(row) = replay.next().await {
                    let artifact = row.unwrap().3;
                    if let ArtifactWith::Recovery(w) = &artifact
                        && w.view() == View::new(1)
                    {
                        retained.push(w.encode());
                    }
                    rows.push(artifact);
                }
                drop(replay.finish().unwrap());
                assert_eq!(
                    retained, original_records,
                    "native pruning lost unresolved original G1 history"
                );
                let retention = match restart {
                    Restart::No => return,
                    Restart::Ready(retention) => retention,
                    Restart::MissingInput | Restart::Normal | Restart::MissingAssembly | Restart::Displaced | Restart::Nullify => 0,
                };
                let missing = matches!(restart, Restart::MissingInput | Restart::MissingAssembly);

                // Seed a genuine typed request only to fence the later live loop.
                // The old proposal is finalized and cannot obtain a new SELECT.
                let body = origin_body(&f, &original, Some(&first));
                let checked = body.verify::<Sha256, _>(
                    &mut runtime, &f.verifier, &original, INPUT, LIMITS,
                    |row| row_policy(&original, row),
                    |rows, body| build_policy(&original, rows, body),
                    &Sequential,
                ).unwrap();
                let selection = config_context.publish_selection::<Sha256>(body, checked).unwrap();
                let request = SelectRequest::new(&selection);

                if !missing {
                    // Exercise the exact Actor helper used by startup, then inspect
                    // the actual owned ledger (the task itself owns its State).
                    let restored_context = context(16);
                    restored_context.publish_input::<Sha256>(captured.clone()).unwrap();
                    if let Some((selection, assembly)) = &material {
                        restored_context.publish_selection::<Sha256>(selection.body().clone(), selection.checked().clone()).unwrap();
                        restored_context.publish_assembly::<Sha256>(assembly.clone()).unwrap();
                    }
                    let restored_evidence = evidence.for_restart();
                    let mut cfg = config!(scheme, cache, n);
                    cfg.floor = FloorWith::Finalized(certificate.clone());
                    cfg.view_retention = ViewDelta::new(retention);
                    let (mut restored_actor, _) = ActorWith::new_with(
                        runtime.child("inspect_retained_owner"), cfg,
                        restored_context, restored_evidence.clone(),
                    );
                    restored_actor.state.set_floor(FloorWith::Finalized(certificate.clone()));
                    let floor_view = restored_actor.state.current_view();
                    for row in &rows {
                        restored_actor.replay_historical(row);
                    }
                    restored_actor.state.finish_notarize_replay();
                    assert_eq!(*restored_evidence.restored.lock(), original_records);
                    let held = restored_actor.state.retained_round(View::new(1)).unwrap();
                    assert!(<G as crate::simplex::phase2::voting::Voting<S,D>>::replay_notarize_vote(
                        held.recovery_state(), &first,
                    ));
                    assert_eq!(held.proposal(), Some(&chosen));
                    if let Some(pair) = &normal_pair {
                        assert!(<G as crate::simplex::phase2::voting::Voting<S,D>>::replay_finalize_vote(held.recovery_state(), pair));
                        assert_eq!(held.final_subject(), Some(&FinalSubject::new::<Sha256,S>(&material.as_ref().unwrap().1)));
                    }
                    if nullify {
                        assert!(rows.iter().any(|row| matches!(row, ArtifactWith::Nullify(_))));
                        assert!(held.notarization().is_some() && held.is_certified() && held.has_unequivocated_proposal());
                        assert!(held.final_subject().is_none());
                        assert!(<G as crate::simplex::phase2::voting::Voting<S,D>>::allows_original(held.recovery_state()));
                        assert!(!held.can_construct_finalize_with(&FinalSubject::new::<Sha256,S>(&material.as_ref().unwrap().1)), "retained local NULLIFY must still deny final choice inside the Round");
                    }
                    assert_eq!(restored_actor.state.current_view(), floor_view);
                    assert_eq!(restored_actor.state.last_finalized(), View::new(2));
                    assert_eq!(restored_actor.state.admits_certificate(View::new(1)), retention > 0);
                    // A duplicate inside the viewport must merge with this same
                    // data Round rather than creating a second G1 ledger.
                    (restored_actor, _) = Box::pin(restored_actor.process_message(Message::Verified {
                        span: tracing::Span::none(),
                        certificate: CertificateWith::Notarization(nqc),
                        from_resolver: false,
                    })).await;
                    let held = restored_actor.state.retained_round(View::new(1)).unwrap();
                    assert!(<G as crate::simplex::phase2::voting::Voting<S,D>>::replay_notarize_vote(
                        held.recovery_state(), &first,
                    ));
                    assert_eq!(held.proposal(), Some(&chosen));
                    if let Some(pair) = &normal_pair {
                        assert!(<G as crate::simplex::phase2::voting::Voting<S,D>>::replay_finalize_vote(held.recovery_state(), pair));
                    }
                    let (restored_actor, old_first) = Box::pin(restored_actor.prepare_notarize(View::new(1))).await;
                    assert!(old_first.is_none());
                    let (restored_actor, old_final) = Box::pin(restored_actor.prepare_finalize(View::new(1))).await;
                    assert!(old_final.is_none());
                    assert_eq!(restored_actor.state.current_view(), floor_view);
                    assert_eq!(restored_evidence.inner.captures.load(Ordering::SeqCst), 0);
                    drop(restored_actor);
                }

                // This is the real Actor.start path over the same on-disk rows,
                // not callback-only reconstruction. No proof is treated as absent.
                let fresh_context = context(16);
                if !matches!(restart, Restart::MissingInput) {
                    fresh_context.publish_input::<Sha256>(captured).unwrap();
                    fresh_context.publish_selection::<Sha256>(selection.body().clone(), selection.checked().clone()).unwrap();
                    if !matches!(restart, Restart::MissingAssembly)
                        && let Some((_, assembly)) = &material {
                        fresh_context.publish_assembly::<Sha256>(assembly.clone()).unwrap();
                    }
                }
                let fresh = evidence.for_restart();
                let reporter = HistoryReporter::default();
                let (network, oracle) = Network::new_with_peers(
                    runtime.child("network"),
                    NConfig {
                        max_size: 1024 * 1024,
                        max_peers_per_set: std::num::NonZeroUsize::new(n as usize).unwrap(),
                        disconnect_on_block: true,
                        tracked_peer_sets: NZUsize!(1),
                    },
                    f.participants.clone(),
                ).await;
                network.start();
                let me = f.participants[usize::from(owner)].clone();
                let (votes, _) = oracle.control(me.clone()).register(0, Quota::per_second(NZU32!(1000))).await.unwrap();
                let (certificates, _) = oracle.control(me).register(1, Quota::per_second(NZU32!(1000))).await.unwrap();
                let (actor, input) = ActorWith::new_with(
                    runtime.child("startup"),
                    Config {
                        scheme: scheme.clone(),
                        elector: RoundRobin::<Sha256>::default().build(scheme.participants()),
                        blocker: NoopBlocker::default(),
                        automaton: App::default(), relay: App::default(), reporter: reporter.clone(),
                        partition: "general-voting".into(), epoch: Epoch::new(1),
                        floor: FloorWith::Finalized(certificate), mailbox_size: NZUsize!(16),
                        leader_timeout: Duration::from_secs(60), certification_timeout: Duration::from_secs(60),
                        timeout_retry: Duration::from_secs(60), skip_budget: u64::from(n),
                        view_retention: ViewDelta::new(retention), replay_buffer: NZUsize!(4096),
                        write_buffer: NZUsize!(4096), page_cache: cache,
                    }, fresh_context, fresh.clone(),
                );
                let mut readiness = crate::simplex::engine::Readiness::new(input);
                let (batcher_tx, mut batcher_rx) = mailbox::new(runtime.child("batcher"), NZUsize!(32));
                let (resolver_tx, _resolver_rx) = mailbox::new(runtime.child("resolver"), NZUsize!(32));
                let handle = actor.start(batcher::Mailbox::new(batcher_tx), resolver::Mailbox::new(resolver_tx), votes, certificates);
                if missing {
                    assert!(matches!(handle.await, Err(commonware_runtime::Error::Exited)));
                    assert_eq!(fresh.completed.load(Ordering::SeqCst), 0);
                } else {
                    assert!(readiness.request_selection(request).await.unwrap().is_none());
                    assert_eq!(fresh.completed.load(Ordering::SeqCst), 1);
                    assert_eq!(*fresh.restored.lock(), original_records);
                    handle.abort();
                    let _ = handle.await;
                }
                assert_eq!(fresh.inner.captures.load(Ordering::SeqCst), 0, "startup must not recapture old FIRST input");
                assert!(reporter.0.lock().iter().all(|activity| activity.view() != View::new(1)), "historical replay published an old activity");
                while let Some(message) = batcher_rx.recv().now_or_never().flatten() {
                    assert!(!matches!(message, batcher::Message::Constructed(vote) if vote.view() == View::new(1)), "historical replay emitted an old vote");
                }
    });
}

#[test]
fn original_history_survives_actual_actor_prune_after_child_finality() {
    for n in [7, 8, 10] {
        exercise(n, Restart::No);
    }
}

#[test]
fn retained_original_history_replays_at_newer_floor_without_old_publication() {
    for n in [7, 8, 10] {
        for retention in [0, 2] {
            exercise(n, Restart::Ready(retention));
        }
    }
}

#[test]
fn retained_original_history_refuses_startup_without_exact_input() {
    exercise(8, Restart::MissingInput);
}

#[test]
fn retained_normal_pair_replays_exact_owned_outbox() {
    for n in [8, 10] {
        exercise(n, Restart::Normal);
    }
}

#[test]
fn retained_normal_pair_refuses_startup_without_exact_assembly() {
    exercise(8, Restart::MissingAssembly);
}

#[test]
fn retained_own_first_keeps_displaced_certificate_proposal_separate() {
    for n in [8, 10] {
        exercise(n, Restart::Displaced);
    }
}

#[test]
fn retained_native_nullify_keeps_first_outbox_without_final_permission() {
    for n in [8, 10] {
        exercise(n, Restart::Nullify);
    }
}

// SELECT replay at a configured finalized anchor is separate from the child
// pruning cases above. It does not require a fabricated local child FIRST.
fn selected_anchor(missing_body: bool, n: u32) {
    let runner = deterministic::Runner::new(
        deterministic::Config::new()
            .with_timeout(Some(Duration::from_secs(20)))
            .with_catch_panics(true),
    );
    runner.start(move |mut runtime| async move {
        let f = ed25519::fixture(&mut runtime, b"_COMMONWARE_CONSENSUS_GENERAL_HISTORY_SELECT_TEST", n);
        let elector: crate::simplex::elector::RoundRobinElector<S> = RoundRobin::<Sha256>::default().build(f.verifier.participants());
        let leader = elector.elect(proposal(1).round, None);
        let scheme = f.schemes[usize::from(leader)].clone();
        let slot = g::Slot {
            profile: PROFILE, domain: DOMAIN,
            roster: g::Slot::roster::<Sha256,_>(&f.verifier), cut: 1,
            proposal: proposal(1), parent: g::NativeParent::Genesis(D([0;32])),
        };
        let core = g::Core::derive::<Sha256,_>(&f.verifier, slot.clone(), leader).unwrap();
        let config_context = context(16);
        let evidence = HistoryEvidence {
            inner: Evidence {
                owner: leader, capture: Arc::new(Mutex::new(None)),
                captures: Arc::new(AtomicUsize::new(0)), assembly: Arc::new(Mutex::new(None)),
            },
            finalization: Arc::new(Mutex::new(None)), notarization: Arc::new(Mutex::new(None)),
            completed: Arc::new(AtomicUsize::new(0)), restored: Arc::new(Mutex::new(Vec::new())),
        };
        let cache = CacheRef::from_pooler(&runtime, NZU16!(1024), NZUsize!(10));
        let (mut actor, input) = ActorWith::new_with(runtime.child("selected_live"), config!(scheme, cache, n), config_context.clone(), evidence.clone());
        let mut readiness = crate::simplex::engine::Readiness::new(input);
        actor.state.set_genesis(D([0;32]));
        let native = actor.state.try_propose().unwrap();
        let proposed = actor.automaton.propose(native.clone()).await;
        actor.automaton.0.lock().pop().unwrap().send(proposal(1).payload).unwrap();
        assert_eq!(proposed.await.unwrap(), proposal(1).payload);
        assert!(actor.state.proposed(proposal(1)));
        let captured = FirstInput::new::<Sha256,_>(&scheme, slot, &native, INPUT, None, None, LIMITS, |row| row_policy(&core,row)).unwrap();
        *evidence.inner.capture.lock() = Some((captured.clone(),native));
        let journal_config = JConfig {
            partition: "general-voting".into(), compression: None,
            codec_config: scheme.certificate_codec_config(), page_cache: cache.clone(), write_buffer: NZUsize!(4096),
        };
        actor.journal = Some(Journal::init(actor.context.child("journal"), journal_config.clone()).await.unwrap());
        let (next, first) = Box::pin(actor.prepare_notarize(View::new(1))).await;
        actor = next.sync_journal().await;
        let first = first.unwrap();
        first.authenticate(&mut runtime, &scheme, &Sequential).unwrap();
        assert!(first.first().is_some(), "the original leader signs its explicit absent FIRST");
        let nqc = nqc(&f, usize::from(leader), &proposal(1));
        *evidence.notarization.lock() = Some(nqc.clone());
        (actor, _) = Box::pin(actor.process_message(Message::Verified {
            span: tracing::Span::none(), certificate: CertificateWith::Notarization(nqc), from_resolver: false,
        })).await;
        actor = actor.sync_journal().await;
        let (ready, fetches) = actor.state.certify_candidates();
        assert_eq!(ready, vec![proposal(1)]);
        assert!(fetches.is_empty());
        let verdict = actor.automaton.certify(proposal(1).round, proposal(1).payload).await.await;
        let (next, live, result) = Box::pin(actor.process_certified(proposal(1).round, verdict)).await;
        actor = next.sync_journal().await;
        assert!(live && result.is_some());
        let body = origin_body(&f, &core, Some(&first));
        let checked = body.verify::<Sha256,_>(&mut runtime, &f.verifier, &core, INPUT, LIMITS,
            |row| row_policy(&core,row), |rows,body| build_policy(&core,rows,body), &Sequential).unwrap();
        let selection = config_context.publish_selection::<Sha256>(body, checked).unwrap();
        let request = SelectRequest::new(&selection);
        let reply = readiness.request_selection(request.clone());
        let message = actor.mailbox_receiver.recv().await.unwrap();
        (actor, _) = Box::pin(actor.process_message(message)).await;
        let selected = reply.await.unwrap().unwrap();
        actor = actor.sync_journal().await;
        let origin = g::Origin { body: selection.body().clone(), selection: selected.clone() };
        let certificate = certificate_for_origin(&mut runtime, &f, usize::from(leader), &core, &origin);
        *evidence.finalization.lock() = Some(certificate.clone());
        (actor, _) = Box::pin(actor.process_message(Message::Verified {
            span: tracing::Span::none(), certificate: CertificateWith::Finalization(certificate.clone()), from_resolver: false,
        })).await;
        actor = actor.sync_journal().await;
        assert_eq!(actor.state.last_finalized(), View::new(1));
        assert_eq!(evidence.inner.captures.load(Ordering::SeqCst),1);
        let mut replay = actor.journal.take().unwrap().replay(0,0,NZUsize!(4096),ReadOptions::DONT_CACHE).await.unwrap();
        let mut rows = Vec::new();
        while let Some(row) = replay.next().await { rows.push(row.unwrap().3); }
        drop(replay.finish().unwrap());
        drop(actor);
        let records: Vec<_> = rows.iter().filter_map(|row| {
            if let ArtifactWith::Recovery(record) = row { Some(record.encode()) } else { None }
        }).collect();
        assert_eq!(records.len(),4, "actual FIRST and SELECT reservation/release pairs");
        assert_eq!(records.iter().map(|frame| frame[8]).collect::<Vec<_>>(), vec![0,1,2,3]);
        let reserved = rows.iter().find_map(|row| {
            if let ArtifactWith::Recovery(record) = row
                && record.encode()[8] == 2 { Some(record.agreement().clone()) } else { None }
        }).unwrap();
        assert_eq!(reserved.authority(), Some(selection.checked().body()));
        assert_eq!(reserved.owner(),leader);
        assert_eq!(reserved.core(),&core);
        let mut release_body = records[3].slice(9..);
        let repeated = g::issuance::Record::<D>::read_cfg(&mut release_body,&LIMITS).unwrap();
        let released = g::issuance::Record::<D>::read_cfg(&mut release_body,&LIMITS).unwrap();
        assert!(release_body.is_empty());
        assert_eq!(repeated,reserved);
        let g::issuance::Action::Released { reservation, frame } = released.action() else { panic!("SELECT signed receipt") };
        assert_eq!(*reservation,reserved.id::<Sha256>());
        assert_eq!(frame,&selected.encode(), "retained SELECT outbox bytes must be exact");

        if !missing_body {
            // This is the actual historical owner, including the SELECT restore
            // branch that checks the exact admitted body and restored outbox.
            let c = context(16);
            c.publish_input::<Sha256>(captured.clone()).unwrap();
            c.publish_selection::<Sha256>(selection.body().clone(),selection.checked().clone()).unwrap();
            let mut cfg = config!(scheme,cache,n);
            cfg.floor = FloorWith::Finalized(certificate.clone());
            cfg.view_retention = ViewDelta::new(0);
            let (mut restored,_) = ActorWith::new_with(runtime.child("selected_owner"),cfg,c,evidence.for_restart());
            restored.state.set_floor(FloorWith::Finalized(certificate.clone()));
            for row in &rows { restored.replay_historical(row); }
            restored.state.finish_notarize_replay();
            let held = restored.state.retained_round(View::new(1)).unwrap();
            assert!(<G as crate::simplex::phase2::voting::Voting<S,D>>::replay_notarize_vote(held.recovery_state(),&first));
            assert!(!<G as crate::simplex::phase2::voting::Voting<S,D>>::validate_recovery_request(&mut restored.state,&request));
            assert_eq!(restored.state.last_finalized(),View::new(1));
            drop(restored);
        }

        let fresh_context = context(16);
        fresh_context.publish_input::<Sha256>(captured).unwrap();
        if !missing_body {
            fresh_context.publish_selection::<Sha256>(selection.body().clone(),selection.checked().clone()).unwrap();
        }
        let fresh = evidence.for_restart();
        let reporter = HistoryReporter::default();
        let (network,oracle) = Network::new_with_peers(runtime.child("selected_network"),NConfig {
            max_size: 1024*1024, max_peers_per_set: std::num::NonZeroUsize::new(n as usize).unwrap(),
            disconnect_on_block: true, tracked_peer_sets: NZUsize!(1),
        },f.participants.clone()).await;
        network.start();
        let me = f.participants[usize::from(leader)].clone();
        let (votes,_) = oracle.control(me.clone()).register(0,Quota::per_second(NZU32!(1000))).await.unwrap();
        let (certificates,_) = oracle.control(me).register(1,Quota::per_second(NZU32!(1000))).await.unwrap();
        let (actor,input) = ActorWith::new_with(runtime.child("selected_startup"),Config {
            scheme: scheme.clone(), elector: RoundRobin::<Sha256>::default().build(scheme.participants()), blocker: NoopBlocker::default(),
            automaton: App::default(), relay: App::default(), reporter: reporter.clone(), partition: "general-voting".into(),
            epoch: Epoch::new(1), floor: FloorWith::Finalized(certificate.clone()), mailbox_size: NZUsize!(16),
            leader_timeout: Duration::from_secs(60), certification_timeout: Duration::from_secs(60), timeout_retry: Duration::from_secs(60),
            skip_budget: u64::from(n),view_retention: ViewDelta::new(0),replay_buffer:NZUsize!(4096),write_buffer:NZUsize!(4096),page_cache:cache,
        },fresh_context,fresh.clone());
        let mut readiness = crate::simplex::engine::Readiness::new(input);
        let (batcher_tx,mut batcher_rx) = mailbox::new(runtime.child("selected_batcher"),NZUsize!(32));
        let (resolver_tx,_resolver_rx) = mailbox::new(runtime.child("selected_resolver"),NZUsize!(32));
        let handle = actor.start(batcher::Mailbox::new(batcher_tx),resolver::Mailbox::new(resolver_tx),votes,certificates);
        if missing_body {
            assert!(matches!(handle.await,Err(commonware_runtime::Error::Exited)));
            assert_eq!(fresh.completed.load(Ordering::SeqCst),0);
        } else {
            assert!(readiness.request_selection(request).await.unwrap().is_none());
            assert_eq!(fresh.completed.load(Ordering::SeqCst),1);
            assert_eq!(*fresh.restored.lock(),records);
            handle.abort(); let _ = handle.await;
        }
        assert_eq!(fresh.inner.captures.load(Ordering::SeqCst),0);
        {
            let activities = reporter.0.lock();
            assert_eq!(activities.iter().filter(|activity| matches!(activity,ActivityWith::Finalization(c) if c == &certificate)).count(),1,"the configured floor is reported once");
            assert!(activities.iter().all(|activity| matches!(activity,ActivityWith::Finalization(c) if c == &certificate) || activity.view() != View::new(1)),"historical SELECT replay must not publish an old activity");
        }
        while let Some(message) = batcher_rx.recv().now_or_never().flatten() {
            assert!(!matches!(message,batcher::Message::Constructed(vote) if vote.view() == View::new(1)));
        }
        let journal = Journal::<_,ArtifactWith<S,D,G>>::init(runtime.child("selected_after_startup"),journal_config).await.unwrap();
        let mut replay = journal.replay(0,0,NZUsize!(4096),ReadOptions::DONT_CACHE).await.unwrap();
        let mut after = Vec::new();
        while let Some(row) = replay.next().await {
            if let ArtifactWith::Recovery(record) = row.unwrap().3 { after.push(record.encode()); }
        }
        drop(replay.finish().unwrap());
        assert_eq!(after,records,"startup/refused old SELECT must not append new issuance");
    });
}

#[test]
fn retained_selected_anchor_replays_exact_body_authority_and_outbox() {
    for n in [8, 10, 13, 16] {
        selected_anchor(false, n);
    }
}

#[test]
fn retained_selected_anchor_refuses_missing_checked_body_handle() {
    selected_anchor(true, 8);
}
