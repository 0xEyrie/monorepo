//! Actual Actor/WAL FIRST barriers with an inactive G1-backed test Mode.
//! These checks do not activate a production G1 mode or connect recovery/Source.
use super::*;
use crate::{
    simplex::{
        extension::agreement::general as g,
        phase2::first_probe::{Capture, FirstContext, FirstProbe, LIMITS, Wal},
        types::Subject,
    },
    types::Participant,
};
use commonware_codec::{Decode as _, Encode as _};
use commonware_cryptography::{
    Digest,
    certificate::{self, Attestation},
};
use commonware_parallel::Strategy;
use commonware_utils::{iter::NonEmpty, ordered::Set};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
#[derive(Clone, Debug)]
struct FirstObserved {
    inner: S,
    native: Arc<AtomicUsize>,
    extension: Arc<AtomicUsize>,
}
impl certificate::Verifier for FirstObserved {
    type Subject<'a, T: Digest> = Subject<'a, T>;
    type Faults = <S as certificate::Verifier>::Faults;
    type PublicKey = PublicKey;
    type Certificate = <S as certificate::Verifier>::Certificate;
    fn verify_certificate<R: CryptoRng, T: Digest>(
        &self,
        rng: &mut R,
        subject: Subject<'_, T>,
        certificate: &Self::Certificate,
        strategy: &impl Strategy,
    ) -> bool {
        self.inner
            .verify_certificate(rng, subject, certificate, strategy)
    }
    fn is_batchable() -> bool {
        S::is_batchable()
    }
    fn certificate_codec_config(&self) -> <Self::Certificate as Read>::Cfg {
        self.inner.certificate_codec_config()
    }
    fn certificate_codec_config_unbounded() -> <Self::Certificate as Read>::Cfg {
        S::certificate_codec_config_unbounded()
    }
}
impl certificate::Scheme for FirstObserved {
    type Signature = <S as certificate::Scheme>::Signature;
    fn me(&self) -> Option<crate::types::Participant> {
        self.inner.me()
    }
    fn participants(&self) -> &Set<PublicKey> {
        self.inner.participants()
    }
    fn sign<T: Digest>(&self, subject: Subject<'_, T>) -> Option<Attestation<Self>> {
        if matches!(subject, Subject::Notarize { .. }) {
            self.native.fetch_add(1, Ordering::SeqCst);
        }
        if matches!(subject, Subject::ExtensionAgreement { .. }) {
            self.extension.fetch_add(1, Ordering::SeqCst);
        }
        self.inner.sign(subject).map(|a| Attestation {
            signer: a.signer,
            signature: a.signature,
        })
    }
    fn verify_attestation<R: CryptoRng, T: Digest>(
        &self,
        rng: &mut R,
        subject: Subject<'_, T>,
        a: &Attestation<Self>,
        strategy: &impl Strategy,
    ) -> bool {
        self.inner.verify_attestation(
            rng,
            subject,
            &Attestation {
                signer: a.signer,
                signature: a.signature.clone(),
            },
            strategy,
        )
    }
    fn optimistic_assemble<'a, R: CryptoRng, T: Digest, I, J>(
        &self,
        rng: &mut R,
        subject: Subject<'_, T>,
        pending: I,
        verified: J,
        strategy: &impl Strategy,
    ) -> Result<Self::Certificate, certificate::Verification<Self>>
    where
        I: IntoIterator<Item = Attestation<Self>>,
        I::IntoIter: ExactSizeIterator + Send,
        J: IntoIterator<Item = &'a Attestation<Self>>,
        J::IntoIter: Send,
    {
        certificate::optimistic_assemble(self, rng, subject, pending, verified, strategy)
    }
    fn assemble<I: Iterator<Item = Attestation<Self>> + Send>(
        &self,
        attestations: NonEmpty<I>,
        strategy: &impl Strategy,
    ) -> Result<Self::Certificate, certificate::AssemblyError> {
        self.inner.assemble(
            non_empty![@attestations.into_iter().map(|a| Attestation {
                signer: a.signer, signature: a.signature,
            })],
            strategy,
        )
    }
    fn is_attributable() -> bool {
        true
    }
}

#[derive(Clone, Default)]
struct FirstEvidence {
    captures: Arc<AtomicUsize>,
    replayed: Arc<AtomicBool>,
}
impl Participation<FirstObserved, D, FirstProbe> for FirstEvidence {
    fn capture_notarize(&mut self, _: &Proposal<D>, _: &Context<D, PublicKey>) -> Option<Capture> {
        self.captures.fetch_add(1, Ordering::SeqCst);
        Some(Capture::default())
    }
    fn replayed(&mut self) {
        self.replayed.store(true, Ordering::SeqCst);
    }
    fn notarize(&mut self, v: Notarize<FirstObserved, D>) -> report::Notarize<FirstObserved, D> {
        v.into()
    }
    fn final_subject(&mut self, _: &Proposal<D>) -> Option<()> {
        None
    }
    fn accepts_finalization(
        &mut self,
        _: &crate::simplex::types::Finalization<FirstObserved, D>,
    ) -> bool {
        false
    }
    fn accepts_replay(&mut self, _: &ArtifactWith<FirstObserved, D, FirstProbe>) -> bool {
        true
    }
    fn prune(&mut self, _: View) {}
}
#[derive(Clone)]
struct FirstSink;
impl Reporter for FirstSink {
    type Activity = ActivityWith<FirstObserved, D, FirstProbe>;
    fn report(&mut self, _: Self::Activity) -> Feedback {
        Feedback::Ok
    }
}
fn first_context() -> FirstContext {
    FirstContext {
        input: D::from([11; 32]),
        profile: D::from([12; 32]),
        domain: D::from([13; 32]),
        ready: Arc::new(AtomicBool::new(true)),
    }
}

fn live_barrier(n: u32, fail_sync: bool, verifier: bool, outside: bool) {
    deterministic::Runner::new(
        deterministic::Config::new()
            .with_timeout(Some(Duration::from_secs(20)))
            .with_catch_panics(true),
    )
    .start(move |mut context| async move {
        let f = ed25519::fixture(&mut context, b"_COMMONWARE_CONSENSUS_FIRST_WAL_TEST", n);
        let native = Arc::new(AtomicUsize::new(0));
        let extension = Arc::new(AtomicUsize::new(0));
        let owner = if outside {
            let elector: crate::simplex::elector::RoundRobinElector<S> =
                RoundRobin::<Sha256>::default().build(f.verifier.participants());
            let leader = elector.elect(proposal(1).round, None);
            let c = first_context();
            let core = g::Core::derive::<Sha256, _>(
                &f.verifier,
                g::Slot {
                    profile: c.profile,
                    domain: c.domain,
                    roster: g::Slot::roster::<Sha256, _>(&f.verifier),
                    cut: 1,
                    proposal: proposal(1),
                    parent: g::NativeParent::Genesis(D::from([0; 32])),
                },
                leader,
            )
            .unwrap();
            (0..n as usize)
                .find(|i| {
                    let owner = Participant::new(*i as u32);
                    owner != core.leader && !core.followers.contains(&owner)
                })
                .unwrap()
        } else {
            0
        };
        let scheme = FirstObserved {
            inner: if verifier {
                f.verifier.clone()
            } else {
                f.schemes[owner].clone()
            },
            native: native.clone(),
            extension: extension.clone(),
        };
        let gates = PendingSyncs::default();
        gates.unblock();
        let actor_context = DelayedSyncContext {
            inner: context.child("voter"),
            pending: gates.clone(),
        };
        let cache = CacheRef::from_pooler(&actor_context, NZU16!(1024), NZUsize!(10));
        let evidence = FirstEvidence::default();
        let (mut actor, _) = ActorWith::new_with(
            actor_context,
            Config {
                scheme: scheme.clone(),
                elector: RoundRobin::<Sha256>::default().build(scheme.participants()),
                blocker: NoopBlocker::default(),
                automaton: App::default(),
                relay: App::default(),
                reporter: FirstSink,
                partition: "first-live".into(),
                epoch: Epoch::new(1),
                floor: FloorWith::Genesis(D::from([0; 32])),
                mailbox_size: NZUsize!(16),
                leader_timeout: Duration::from_secs(60),
                certification_timeout: Duration::from_secs(60),
                timeout_retry: Duration::from_secs(60),
                skip_budget: u64::from(n),
                view_retention: ViewDelta::new(10),
                replay_buffer: NZUsize!(4096),
                write_buffer: NZUsize!(4096),
                page_cache: cache.clone(),
            },
            first_context(),
            evidence.clone(),
        );
        actor.state.set_genesis(D::from([0; 32]));
        assert!(actor.state.proposed(proposal(1)));
        assert!(
            actor.state.construct_notarize(View::new(1)).is_none(),
            "public helper cannot bypass opt-in WAL"
        );
        assert_eq!(native.load(Ordering::SeqCst), 0);
        assert_eq!(extension.load(Ordering::SeqCst), 0);
        actor.journal = Some(
            Journal::init(
                actor.context.child("journal"),
                JConfig {
                    partition: "first-live".into(),
                    compression: None,
                    codec_config: scheme.certificate_codec_config(),
                    page_cache: cache.clone(),
                    write_buffer: NZUsize!(4096),
                },
            )
            .await
            .unwrap(),
        );
        gates.arm();
        let handle = context
            .child("prepare")
            .spawn(|_| actor.prepare_notarize(View::new(1)));
        if verifier {
            let (actor, vote) = handle.await.unwrap();
            assert!(vote.is_none());
            assert_eq!(evidence.captures.load(Ordering::SeqCst), 0);
            assert_eq!(gates.calls(), 0);
            drop(actor);
            return;
        }
        while gates.lock().is_empty() {
            reschedule().await;
        }
        let gate = next_pending_sync(&gates);
        gate.blocked.await.unwrap();
        assert_eq!(
            native.load(Ordering::SeqCst),
            0,
            "native signer escaped before reservation sync"
        );
        assert_eq!(
            extension.load(Ordering::SeqCst),
            0,
            "G1 signer escaped before reservation sync"
        );
        assert_eq!(evidence.captures.load(Ordering::SeqCst), 1);
        if fail_sync {
            drop(gate.release);
            assert!(handle.await.is_err());
            assert_eq!(native.load(Ordering::SeqCst), 0);
            assert_eq!(extension.load(Ordering::SeqCst), 0);
            return;
        }
        gate.release.send(Ok(())).unwrap();
        let (mut actor, vote) = handle.await.unwrap();
        let vote = vote.unwrap();
        assert_eq!(vote.vote().proposal, proposal(1));
        assert!(vote.vote().verify(&mut context, &scheme, &Sequential));
        if outside {
            assert!(vote.report().is_none(), "NoFirst is not signed absence");
        } else {
            let signed =
                g::Signed::<FirstObserved, D>::decode_cfg(vote.report().unwrap().clone(), &LIMITS)
                    .unwrap();
            assert!(signed.verify(&mut context, &scheme, LIMITS, &Sequential));
            assert_eq!(signed.attestation.signer, vote.vote().attestation.signer);
        }
        assert_eq!(native.load(Ordering::SeqCst), 1);
        assert_eq!(extension.load(Ordering::SeqCst), usize::from(!outside));
        assert_eq!(
            actor.dirty_section,
            Some(View::new(1)),
            "complete pair still needs publication sync"
        );
        // arm() gates one operation. The initial unblock remains sticky, so
        // later syncs complete directly while the counter still observes them.
        let synced = gates.calls();
        actor = actor.sync_journal().await;
        assert_eq!(gates.calls(), synced + 1);
        assert!(actor.dirty_section.is_none());
        assert!(
            actor
                .state
                .construct_nullify(View::new(1), TimeoutReason::CertificationTimeout)
                .is_some(),
            "FIRST must not consume native final/nullify choice"
        );
        let (actor, duplicate) = actor.prepare_notarize(View::new(1)).await;
        assert!(duplicate.is_none());
        assert_eq!(evidence.captures.load(Ordering::SeqCst), 1);
        drop(actor);
        let journal = Journal::<_, ArtifactWith<FirstObserved, D, FirstProbe>>::init(
            context.child("inspect"),
            JConfig {
                partition: "first-live".into(),
                compression: None,
                codec_config: scheme.certificate_codec_config(),
                page_cache: cache,
                write_buffer: NZUsize!(4096),
            },
        )
        .await
        .unwrap();
        let mut replay = journal
            .replay(0, 0, NZUsize!(4096), ReadOptions::DONT_CACHE)
            .await
            .unwrap();
        let mut complete = Vec::new();
        let mut records = 0;
        let mut closures = 0;
        while let Some(r) = replay.next().await {
            match r.unwrap().3 {
                ArtifactWith::Notarize(v) => complete.push(v),
                ArtifactWith::Recovery(r) => {
                    records += 1;
                    closures += usize::from(matches!(r.0.action(), g::issuance::Action::NoFirst));
                }
                _ => {}
            }
        }
        assert_eq!(complete, vec![vote]);
        assert_eq!(records, if outside { 1 } else { 2 });
        assert_eq!(closures, usize::from(outside));
        drop(replay.finish().unwrap());
    });
}
#[test]
fn first_native_and_g1_signers_wait_for_real_actor_wal_sync() {
    for n in [7, 8, 10] {
        live_barrier(n, false, false, false);
    }
}
#[test]
fn failed_first_reservation_sync_calls_neither_signer() {
    live_barrier(10, true, false, false);
}
#[test]
fn verifier_only_first_actor_never_captures_or_reserves() {
    live_barrier(10, false, true, false);
}

#[test]
fn outside_core_actor_persists_one_no_first_without_g1_signature() {
    live_barrier(10, false, false, true);
}

// Seed the durable pre-sign cut from actual owner staging, then launch the real
// Actor replay loop. No injected record grants recovery or native finality.
fn restart_first(n: u32, case: u8) {
    deterministic::Runner::new(
        deterministic::Config::new()
            .with_timeout(Some(Duration::from_secs(30)))
            .with_catch_panics(true),
    )
    .start(move |mut context| async move {
        let f = ed25519::fixture(&mut context, b"_COMMONWARE_CONSENSUS_FIRST_RESTART_TEST", n);
        let native = Arc::new(AtomicUsize::new(0));
        let extension = Arc::new(AtomicUsize::new(0));
        let first_context = first_context();
        let owner = if case == 11 {
            let elector: crate::simplex::elector::RoundRobinElector<S> =
                RoundRobin::<Sha256>::default().build(f.verifier.participants());
            let core = g::Core::derive::<Sha256, _>(
                &f.verifier,
                g::Slot {
                    profile: first_context.profile,
                    domain: first_context.domain,
                    roster: g::Slot::roster::<Sha256, _>(&f.verifier),
                    cut: 1,
                    proposal: proposal(1),
                    parent: g::NativeParent::Genesis(D::from([0; 32])),
                },
                elector.elect(proposal(1).round, None),
            )
            .unwrap();
            (0..n as usize)
                .find(|i| {
                    let owner = Participant::new(*i as u32);
                    owner != core.leader && !core.followers.contains(&owner)
                })
                .unwrap()
        } else {
            0
        };
        let scheme = FirstObserved {
            inner: f.schemes[owner].clone(),
            native: native.clone(),
            extension: extension.clone(),
        };
        let cache = CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(10));
        let config = || Config {
            scheme: scheme.clone(),
            elector: RoundRobin::<Sha256>::default().build(scheme.participants()),
            blocker: NoopBlocker::default(),
            automaton: App::default(),
            relay: App::default(),
            reporter: FirstSink,
            partition: "first-restart".into(),
            epoch: Epoch::new(1),
            floor: FloorWith::Genesis(D::from([0; 32])),
            mailbox_size: NZUsize!(16),
            leader_timeout: Duration::from_secs(60),
            certification_timeout: Duration::from_secs(60),
            timeout_retry: Duration::from_secs(60),
            skip_budget: u64::from(n),
            view_retention: ViewDelta::new(10),
            replay_buffer: NZUsize!(4096),
            write_buffer: NZUsize!(4096),
            page_cache: cache.clone(),
        };
        let (mut seed, _) = ActorWith::new_with(
            context.child("seed"),
            config(),
            first_context.clone(),
            FirstEvidence::default(),
        );
        seed.state.set_genesis(D::from([0; 32]));
        let mut records: Vec<ArtifactWith<FirstObserved, D, FirstProbe>> = Vec::new();
        if case == 8 {
            let q = g::Committee::new(n as usize).unwrap().quorum();
            let votes: Vec<_> = f
                .schemes
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != owner)
                .take(q)
                .map(|(_, s)| Notarize::sign(s, proposal(1)).unwrap())
                .collect();
            let cert =
                Notarization::from_notarizes(&f.verifier, non_empty![@votes.iter()], &Sequential)
                    .unwrap();
            let cert = Notarization::<FirstObserved, D> {
                proposal: cert.proposal,
                certificate: cert.certificate,
            };
            seed.state.add_notarization(cert.clone());
            assert!(
                seed.state.verified(View::new(1)),
                "live owner verified A after receiving NQC(A)"
            );
            records.push(ArtifactWith::Notarization(cert));
        } else {
            assert!(seed.state.proposed(proposal(1)));
        }
        let first = seed
            .state
            .stage_notarize_with(View::new(1), &mut seed.participation)
            .unwrap();
        if case == 11 {
            assert!(matches!(first.0.action(), g::issuance::Action::NoFirst));
        } else {
            assert!(matches!(
                first.0.action(),
                g::issuance::Action::Reserve {
                    message: g::Message {
                        kind: g::Kind::First(_),
                        ..
                    },
                    ..
                }
            ), "fixture must be an actual Core owner");
        }
        records.push(ArtifactWith::Recovery(first.clone()));
        if case == 10 {
            let vote = Notarize::sign(&scheme, proposal(1)).unwrap();
            records.push(ArtifactWith::Notarize(vote.into()));
        }
        let mut exact_vote = None;
        if matches!(case, 4..=7 | 11) {
            let (vote, receipt) = seed
                .state
                .sign_reserved_notarize(View::new(1), &mut seed.participation)
                .unwrap();
            if let Some(receipt) = receipt {
                records.push(ArtifactWith::Recovery(receipt));
            }
            if matches!(case, 4 | 7 | 11) {
                records.push(ArtifactWith::Notarize(vote.clone()));
            }
            exact_vote = Some(vote);
        }
        if case == 1 || case == 5 {
            let mut ledger = g::issuance::State::for_replay::<Sha256>(
                scheme.clone(),
                first.0.core().clone(),
                first.0.input(),
                LIMITS,
            )
            .unwrap();
            for record in &records {
                if let ArtifactWith::Recovery(r) = record {
                    ledger
                        .restore::<Sha256, _>(
                            &mut context,
                            &r.0,
                            g::issuance::Material::None,
                            |_| true,
                            |_, _| false,
                            &Sequential,
                        )
                        .unwrap();
                }
            }
            ledger.finish_replay().unwrap();
            records.push(ArtifactWith::Recovery(Wal(ledger
                .fence::<Sha256>(Rnd::new(Epoch::new(1), View::new(2)), Participant::new(0))
                .unwrap())));
        }
        if case == 2 {
            let (_, nullify) = seed
                .state
                .construct_nullify(View::new(1), TimeoutReason::CertificationTimeout)
                .unwrap();
            records.push(ArtifactWith::Nullify(nullify));
        }
        if case == 3 || case == 7 {
            let mut other = proposal(1);
            other.payload = D::from([91; 32]);
            let q = g::Committee::new(n as usize).unwrap().quorum();
            let votes: Vec<_> = f
                .schemes
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != owner)
                .take(q)
                .map(|(_, s)| Notarize::sign(s, other.clone()).unwrap())
                .collect();
            let cert =
                Notarization::from_notarizes(&f.verifier, non_empty![@votes.iter()], &Sequential)
                    .unwrap();
            records.push(ArtifactWith::Notarization(
                Notarization::<FirstObserved, D> {
                    proposal: cert.proposal,
                    certificate: cert.certificate,
                },
            ));
        }
        seed.journal = Some(
            Journal::init(
                seed.context.child("journal"),
                JConfig {
                    partition: "first-restart".into(),
                    compression: None,
                    codec_config: scheme.certificate_codec_config(),
                    page_cache: cache.clone(),
                    write_buffer: NZUsize!(4096),
                },
            )
            .await
            .unwrap(),
        );
        for r in &records {
            seed = seed.append_journal(r.clone()).await;
        }
        seed = seed.sync_journal().await;
        drop(seed);
        native.store(0, Ordering::SeqCst);
        extension.store(0, Ordering::SeqCst);
        let (network, oracle) = Network::new_with_peers(
            context.child("network"),
            NConfig {
                max_size: 1024 * 1024,
                max_peers_per_set: NonZeroUsize::new(n as usize).unwrap(),
                disconnect_on_block: true,
                tracked_peer_sets: NZUsize!(1),
            },
            f.participants.clone(),
        )
        .await;
        network.start();
        let me = f.participants[owner].clone();
        let (votes, _) = oracle
            .control(me.clone())
            .register(0, Quota::per_second(NZU32!(1000)))
            .await
            .unwrap();
        let (certificates, _) = oracle
            .control(me)
            .register(1, Quota::per_second(NZU32!(1000)))
            .await
            .unwrap();
        let evidence = FirstEvidence::default();
        if case == 9 {
            first_context.ready.store(false, Ordering::SeqCst);
        }
        let ready = first_context.ready.clone();
        let (actor, mut input) = ActorWith::new_with(
            context.child("reopen"),
            config(),
            first_context,
            evidence.clone(),
        );
        let (batcher_tx, mut batcher_rx) = mailbox::new(context.child("batcher"), NZUsize!(32));
        let (resolver_tx, _resolver_rx) = mailbox::new(context.child("resolver"), NZUsize!(32));
        let handle = actor.start(
            batcher::Mailbox::new(batcher_tx),
            resolver::Mailbox::new(resolver_tx),
            votes,
            certificates,
        );
        if case == 10 {
            assert!(handle.await.is_err(), "Core FIRST needs its released outbox");
            assert!(!evidence.replayed.load(Ordering::SeqCst));
            assert_eq!(native.load(Ordering::SeqCst), 0);
            assert_eq!(extension.load(Ordering::SeqCst), 0);
            return;
        }
        while !evidence.replayed.load(Ordering::SeqCst) {
            reschedule().await;
        }
        assert_eq!(
            evidence.captures.load(Ordering::SeqCst),
            0,
            "replay must not recapture optional data"
        );
        if case == 8 {
            assert_eq!(
                native.load(Ordering::SeqCst),
                1,
                "exact same-P reservation must restore prior verification on startup"
            );
            assert_eq!(extension.load(Ordering::SeqCst), 1);
        }
        if case == 9 {
            assert_eq!(native.load(Ordering::SeqCst), 0);
            assert_eq!(extension.load(Ordering::SeqCst), 0);
            ready.store(true, Ordering::SeqCst);
            // An actual native certificate event retries the retained pin.
            // Only the Mode refusal/readiness transition is injected.
            let q = g::Committee::new(n as usize).unwrap().quorum();
            let votes: Vec<_> = f
                .schemes
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != owner)
                .take(q)
                .map(|(_, s)| Notarize::sign(s, proposal(1)).unwrap())
                .collect();
            let cert =
                Notarization::from_notarizes(&f.verifier, non_empty![@votes.iter()], &Sequential)
                    .unwrap();
            input.recovered(CertificateWith::Notarization(Notarization {
                proposal: cert.proposal,
                certificate: cert.certificate,
            }));
        }
        if matches!(case, 1..=3 | 5) {
            assert_eq!(native.load(Ordering::SeqCst), 0);
            assert_eq!(extension.load(Ordering::SeqCst), 0);
            while let Some(m) = batcher_rx.recv().now_or_never().flatten() {
                assert!(!matches!(
                    m,
                    batcher::Message::Constructed(VoteWith::Notarize(_))
                ));
            }
        } else {
            let vote = loop {
                if let batcher::Message::Constructed(VoteWith::Notarize(v)) =
                    batcher_rx.recv().await.unwrap()
                {
                    break v;
                }
            };
            assert_eq!(vote.vote().proposal, proposal(1));
            if let Some(old) = exact_vote {
                assert_eq!(vote.report(), old.report());
                if matches!(case, 4 | 7 | 11) {
                    assert_eq!(vote, old);
                }
            }
            assert_eq!(
                native.load(Ordering::SeqCst),
                usize::from(!matches!(case, 4 | 7 | 11))
            );
            assert_eq!(
                extension.load(Ordering::SeqCst),
                usize::from(case == 0 || case == 8 || case == 9)
            );
        }
        handle.abort();
        let _ = handle.await;
        let journal = Journal::<_, ArtifactWith<FirstObserved, D, FirstProbe>>::init(
            context.child("inspect"),
            JConfig {
                partition: "first-restart".into(),
                compression: None,
                codec_config: scheme.certificate_codec_config(),
                page_cache: cache,
                write_buffer: NZUsize!(4096),
            },
        )
        .await
        .unwrap();
        let mut replay = journal
            .replay(0, 0, NZUsize!(4096), ReadOptions::DONT_CACHE)
            .await
            .unwrap();
        let mut retained = Vec::new();
        while let Some(r) = replay.next().await {
            retained.push(r.unwrap().3);
        }
        for (actual, expected) in retained.iter().zip(&records) {
            assert_eq!(
                actual.encode(),
                expected.encode(),
                "accepted prefix is exact"
            );
        }
        assert!(retained.len() >= records.len());
        assert_eq!(evidence.captures.load(Ordering::SeqCst), 0);
        if case == 9 {
            assert_eq!(
                retained
                    .iter()
                    .filter(|a| matches!(a, ArtifactWith::Recovery(r) if <FirstProbe as Voting<FirstObserved, D>>::reserved_notarize(r).is_some()))
                    .count(),
                1,
                "retry must retain one unsigned choice"
            );
            assert_eq!(
                retained.iter().filter(|a| matches!(a, ArtifactWith::Notarize(_))).count(),
                1,
                "retry must finish exactly one native vote"
            );
        }
        drop(replay.finish().unwrap());
    });
}
#[test]
fn unsigned_first_actor_reopens_general_and_slack_rosters() {
    for n in [7, 8, 10] {
        restart_first(n, 0);
    }
}
#[test]
fn replay_reads_later_extension_floor_before_either_first_signer() {
    restart_first(10, 1);
}
#[test]
fn replayed_native_nullify_blocks_new_first_signatures() {
    restart_first(10, 2);
}
#[test]
fn later_nqc_cannot_replace_the_unsigned_own_first_pin() {
    restart_first(10, 3);
}
#[test]
fn complete_first_pair_replays_exact_bytes_without_signers() {
    restart_first(10, 4);
}
#[test]
fn retained_g1_outbox_does_not_reopen_native_signer_after_floor() {
    restart_first(10, 5);
}
#[test]
fn retained_g1_outbox_can_finish_only_the_exact_native_pair() {
    restart_first(10, 6);
}
#[test]
fn complete_original_first_survives_a_later_different_nqc() {
    restart_first(10, 7);
}

#[test]
fn same_nqc_unsigned_first_restores_verified_before_startup_release() {
    restart_first(10, 8);
}

#[test]
fn pending_first_retries_injected_current_readiness_without_recapture() {
    restart_first(10, 9);
}

#[test]
fn core_native_vote_without_released_first_is_rejected_on_replay() {
    restart_first(10, 10);
}

#[test]
fn outside_core_complete_no_first_replays_without_extension_frame() {
    restart_first(10, 11);
}

// The current-hook refusal is injected. Parent A/B, peer verification, native
// certificates, both journal barriers and startup replay use their real owners.
fn replay_pending_child_parent(replace: bool) {
    deterministic::Runner::timed(Duration::from_secs(30)).start(move |mut context| async move {
        let n = 10;
        let f = ed25519::fixture(&mut context, b"_COMMONWARE_CONSENSUS_FIRST_PARENT_TEST", n);
        let first_context = first_context();
        let election = || {
            RoundRobin::<Sha256>::default().with_term(
                crate::types::TermLength::new(NZU32!(5)),
                Duration::from_secs(60),
                ViewDelta::new(2),
            )
        };
        let elector: crate::simplex::elector::RoundRobinElector<S> =
            election().build(f.verifier.participants());
        let leader = elector.elect(proposal(1).round, None);
        let cores: Vec<_> = [proposal(1), proposal(2)]
            .into_iter()
            .map(|p| {
                g::Core::derive::<Sha256, _>(
                    &f.verifier,
                    g::Slot {
                        profile: first_context.profile,
                        domain: first_context.domain,
                        roster: g::Slot::roster::<Sha256, _>(&f.verifier),
                        cut: 1,
                        parent: if p.parent.is_zero() {
                            g::NativeParent::Genesis(D::from([0; 32]))
                        } else {
                            g::NativeParent::Proposal {
                                round: proposal(1).round,
                                digest: proposal(1).payload,
                            }
                        },
                        proposal: p,
                    },
                    leader,
                )
                .unwrap()
            })
            .collect();
        let owner = (0..n as usize)
            .find(|i| {
                let owner = Participant::new(*i as u32);
                owner != leader && cores.iter().all(|c| c.followers.contains(&owner))
            })
            .unwrap();
        let native = Arc::new(AtomicUsize::new(0));
        let extension = Arc::new(AtomicUsize::new(0));
        let scheme = FirstObserved {
            inner: f.schemes[owner].clone(),
            native: native.clone(),
            extension: extension.clone(),
        };
        let cache = CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(10));
        let config = || Config {
            scheme: scheme.clone(),
            elector: election().build(scheme.participants()),
            blocker: NoopBlocker::default(),
            automaton: App::default(),
            relay: App::default(),
            reporter: FirstSink,
            partition: "first-parent".into(),
            epoch: Epoch::new(1),
            floor: FloorWith::Genesis(D::from([0; 32])),
            mailbox_size: NZUsize!(16),
            leader_timeout: Duration::from_secs(60),
            certification_timeout: Duration::from_secs(60),
            timeout_retry: Duration::from_secs(60),
            skip_budget: u64::from(n),
            view_retention: ViewDelta::new(10),
            replay_buffer: NZUsize!(4096),
            write_buffer: NZUsize!(4096),
            page_cache: cache.clone(),
        };
        let evidence = FirstEvidence::default();
        let (mut actor, _) = ActorWith::new_with(
            context.child("seed"),
            config(),
            first_context.clone(),
            evidence.clone(),
        );
        actor.state.set_genesis(D::from([0; 32]));
        assert_eq!(actor.state.leader_index(View::new(1)), Some(leader));
        actor.journal = Some(
            Journal::init(
                actor.context.child("journal"),
                JConfig {
                    partition: "first-parent".into(),
                    compression: None,
                    codec_config: scheme.certificate_codec_config(),
                    page_cache: cache.clone(),
                    write_buffer: NZUsize!(4096),
                },
            )
            .await
            .unwrap(),
        );
        assert!(actor.state.set_proposal(View::new(1), proposal(1)));
        assert!(matches!(actor.state.try_verify(), Verify::Ready(..)));
        assert!(actor.state.verified(View::new(1)));
        let parent;
        (actor, parent) = actor.prepare_notarize(View::new(1)).await;
        assert!(parent.unwrap().report().is_some());
        actor = actor.sync_journal().await;
        assert!(actor.state.set_proposal(View::new(2), proposal(2)));
        let Verify::Ready(child_context, _) = actor.state.try_verify() else {
            std::panic!("child must verify against own completed optimistic parent");
        };
        assert_eq!(child_context.parent, (View::new(1), proposal(1).payload));
        assert!(actor.state.verified(View::new(2)));
        first_context.ready.store(false, Ordering::SeqCst);
        let child;
        (actor, child) = actor.prepare_notarize(View::new(2)).await;
        assert!(child.is_none());
        assert!(
            actor.dirty_section.is_none(),
            "unsigned child pin is synced"
        );
        assert_eq!(evidence.captures.load(Ordering::SeqCst), 2);
        if replace {
            let mut other = proposal(1);
            other.payload = D::from([93; 32]);
            let q = g::Committee::new(n as usize).unwrap().quorum();
            let votes: Vec<_> = f
                .schemes
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != owner)
                .take(q)
                .map(|(_, s)| Notarize::sign(s, other.clone()).unwrap())
                .collect();
            let cert =
                Notarization::from_notarizes(&f.verifier, non_empty![@votes.iter()], &Sequential)
                    .unwrap();
            actor = actor
                .handle_notarization(Notarization {
                    proposal: cert.proposal,
                    certificate: cert.certificate,
                })
                .await;
            actor = actor.sync_journal().await;
            first_context.ready.store(true, Ordering::SeqCst);
            let child;
            (actor, child) = actor.prepare_notarize(View::new(2)).await;
            assert!(
                child.is_none(),
                "live native parent verification stays exact"
            );
        }
        assert_eq!(native.load(Ordering::SeqCst), 1);
        assert_eq!(extension.load(Ordering::SeqCst), 1);
        drop(actor);

        let journal = Journal::<_, ArtifactWith<FirstObserved, D, FirstProbe>>::init(
            context.child("inspect"),
            JConfig {
                partition: "first-parent".into(),
                compression: None,
                codec_config: scheme.certificate_codec_config(),
                page_cache: cache.clone(),
                write_buffer: NZUsize!(4096),
            },
        )
        .await
        .unwrap();
        let mut replay = journal
            .replay(0, 0, NZUsize!(4096), ReadOptions::DONT_CACHE)
            .await
            .unwrap();
        let mut captured = 0;
        while let Some(r) = replay.next().await {
            if let ArtifactWith::Recovery(r) = r.unwrap().3
                && r.view() == View::new(2)
                && <FirstProbe as Voting<FirstObserved, D>>::reserved_notarize(&r).is_some()
            {
                assert_eq!(r.0.slot().parent, cores[1].slot.parent);
                captured += 1;
            }
        }
        assert_eq!(captured, 1);
        drop(replay.finish().unwrap());
        native.store(0, Ordering::SeqCst);
        extension.store(0, Ordering::SeqCst);
        first_context.ready.store(true, Ordering::SeqCst);
        let (network, oracle) = Network::new_with_peers(
            context.child("network"),
            NConfig {
                max_size: 1024 * 1024,
                max_peers_per_set: NZUsize!(10),
                disconnect_on_block: true,
                tracked_peer_sets: NZUsize!(1),
            },
            f.participants.clone(),
        )
        .await;
        network.start();
        let me = f.participants[owner].clone();
        let (votes, _) = oracle
            .control(me.clone())
            .register(0, Quota::per_second(NZU32!(1000)))
            .await
            .unwrap();
        let (certificates, _) = oracle
            .control(me)
            .register(1, Quota::per_second(NZU32!(1000)))
            .await
            .unwrap();
        let evidence = FirstEvidence::default();
        let (actor, _) = ActorWith::new_with(
            context.child("reopen"),
            config(),
            first_context,
            evidence.clone(),
        );
        let (batcher_tx, mut batcher_rx) = mailbox::new(context.child("batcher"), NZUsize!(32));
        let (resolver_tx, _resolver_rx) = mailbox::new(context.child("resolver"), NZUsize!(32));
        let handle = actor.start(
            batcher::Mailbox::new(batcher_tx),
            resolver::Mailbox::new(resolver_tx),
            votes,
            certificates,
        );
        while !evidence.replayed.load(Ordering::SeqCst) {
            reschedule().await;
        }
        let expected = usize::from(!replace);
        assert_eq!(
            native.load(Ordering::SeqCst),
            expected,
            "replay must compare the captured native parent before native signing"
        );
        assert_eq!(
            extension.load(Ordering::SeqCst),
            expected,
            "replay must compare the captured native parent before G1 signing"
        );
        assert_eq!(evidence.captures.load(Ordering::SeqCst), 0);
        if !replace {
            loop {
                if let batcher::Message::Constructed(VoteWith::Notarize(v)) =
                    batcher_rx.recv().await.unwrap()
                    && v.view() == View::new(2)
                {
                    assert_eq!(v.vote().proposal, proposal(2));
                    break;
                }
            }
        }
        handle.abort();
        let _ = handle.await;
    });
}

#[test]
fn replayed_pending_child_rejects_changed_native_parent_before_both_signers() {
    replay_pending_child_parent(true);
}

#[test]
fn replayed_pending_child_accepts_the_exact_unchanged_native_parent() {
    replay_pending_child_parent(false);
}
