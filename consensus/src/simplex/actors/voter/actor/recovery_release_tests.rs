//! Generic receipt/publication ordering with a private mode and genuine signatures.
//! This does not activate General Voting or establish recovery admission/liveness.
use super::*;
use crate::simplex::{
    extension::{
        agreement::general::Committee,
        recovery::{Promise, Status},
    },
    phase2::recovery_probe::{RecoveryContext, RecoveryProbe, Wal},
};
use std::sync::atomic::{AtomicUsize, Ordering};

#[derive(Clone)]
struct ReceiptEvidence(S);
impl Participation<S, D, RecoveryProbe> for ReceiptEvidence {
    fn notarize(&mut self, v: Notarize<S, D>) -> Notarize<S, D> {
        v
    }
    fn final_subject(&mut self, _: &Proposal<D>) -> Option<()> {
        None
    }
    fn accepts_finalization(&mut self, _: &crate::simplex::types::Finalization<S, D>) -> bool {
        false
    }
    fn accepts_replay(&mut self, a: &ArtifactWith<S, D, RecoveryProbe>) -> bool {
        match a {
            ArtifactWith::Recovery(w) if w.kind == 1 => {
                let Ok(s) = Status::<S, D>::decode(w.frame.clone()) else {
                    return false;
                };
                s.promise == w.promise
                    && s.verify(&mut commonware_utils::test_rng(), &self.0, &Sequential)
            }
            _ => true,
        }
    }
    fn prune(&mut self, _: View) {}
}
#[derive(Clone)]
struct ReceiptSink;
impl Reporter for ReceiptSink {
    type Activity = ActivityWith<S, D, RecoveryProbe>;
    fn report(&mut self, _: Self::Activity) -> Feedback {
        Feedback::Ok
    }
}
macro_rules! config {
    ($s:expr,$cache:expr,$partition:expr,$n:expr) => {
        Config {
            scheme: $s.clone(),
            elector: RoundRobin::<Sha256>::default().build($s.participants()),
            blocker: NoopBlocker::default(),
            automaton: App::default(),
            relay: App::default(),
            reporter: ReceiptSink,
            partition: $partition.into(),
            epoch: Epoch::new(1),
            floor: FloorWith::Genesis(D::from([0; 32])),
            mailbox_size: NZUsize!(8),
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
macro_rules! journal_config {
    ($s:expr,$cache:expr,$partition:expr) => {
        JConfig {
            partition: $partition.into(),
            compression: None,
            codec_config: $s.certificate_codec_config(),
            page_cache: $cache.clone(),
            write_buffer: NZUsize!(4096),
        }
    };
}
fn request() -> Wal {
    Wal {
        promise: Promise {
            proposal: proposal(1),
            domain: D::from([8; 32]),
            ballot: Rnd::new(Epoch::new(1), View::new(2)),
            accepted: None,
        },
        kind: 0,
        frame: Bytes::new(),
    }
}
fn certificate(f: &Fixture<S>) -> Notarization<S, D> {
    let q = Committee::new(f.schemes.len()).unwrap().quorum();
    let votes: Vec<_> = f
        .schemes
        .iter()
        .take(q)
        .map(|s| Notarize::sign(s, proposal(1)).unwrap())
        .collect();
    Notarization::from_notarizes(&f.verifier, non_empty![@votes.iter()], &Sequential).unwrap()
}
// 0 success/replay, 1 canceled receiver, 2 failed release sync.
fn release(n: u32, case: u8, hold_reservation: bool) {
    deterministic::Runner::new(
        deterministic::Config::new()
            .with_timeout(Some(Duration::from_secs(20)))
            .with_catch_panics(true),
    )
    .start(move |mut context| async move {
        let f = ed25519::fixture(
            &mut context,
            b"_COMMONWARE_CONSENSUS_RECOVERY_RECEIPT_TEST",
            n,
        );
        let s = f.schemes.last().unwrap().clone();
        let signed = Arc::new(AtomicUsize::new(0));
        let gates = PendingSyncs::default();
        gates.unblock();
        let c = RecoveryContext {
            domain: D::from([8; 32]),
            signed: signed.clone(),
            release_gate: (!hold_reservation).then(|| gates.clone()),
        };
        let actor_context = DelayedSyncContext {
            inner: context.child("voter"),
            pending: gates.clone(),
        };
        let cache = CacheRef::from_pooler(&actor_context, NZU16!(1024), NZUsize!(10));
        let (mut actor, _) = ActorWith::new_with(
            actor_context,
            config!(s, cache, "receipt-live", n),
            c.clone(),
            ReceiptEvidence(f.verifier.clone()),
        );
        actor.state.set_genesis(D::from([0; 32]));
        let cert = certificate(&f);
        actor.state.add_notarization(cert.clone());
        actor.journal = Some(
            Journal::init(
                actor.context.child("journal"),
                journal_config!(s, cache, "receipt-live"),
            )
            .await
            .unwrap(),
        );
        actor = actor.append_journal(ArtifactWith::Notarization(cert)).await;
        actor = actor.sync_journal().await;
        // PendingSyncs gates direct durable writes only after arm(), once per
        // lifetime. Separate runs isolate reservation and receipt barriers.
        if hold_reservation {
            gates.arm();
        }
        let record = request();
        let (tx, rx) = oneshot::channel();
        let mut rx = Some(rx);
        let handle = context.child("request").spawn({
            let record = record.clone();
            move |_| {
                actor.process_message(Message::Recovery {
                    span: tracing::Span::none(),
                    request: record,
                    reply: tx,
                })
            }
        });
        while gates.lock().is_empty() {
            reschedule().await;
        }
        let gate = next_pending_sync(&gates);
        gate.blocked.await.unwrap();
        assert!(
            rx.as_mut().unwrap().now_or_never().is_none(),
            "reply before selected durability barrier"
        );
        assert_eq!(
            signed.load(Ordering::SeqCst),
            usize::from(!hold_reservation),
            "reservation barrier precedes signing, receipt barrier follows staging"
        );
        if case == 1 {
            assert!(!hold_reservation);
            drop(rx.take());
        }
        if case == 2 {
            assert!(!hold_reservation);
            drop(gate.release);
            assert!(
                handle.await.is_err(),
                "failed release sync must retire owner"
            );
            assert!(
                rx.take().unwrap().await.is_err(),
                "response escaped failed receipt sync"
            );
            return;
        }
        gate.release.send(Ok(())).unwrap();
        gates.unblock();
        let (mut actor, _) = handle.await.unwrap();
        assert!(actor.dirty_section.is_none());
        let wire = if let Some(rx) = rx {
            Some(rx.await.unwrap().unwrap())
        } else {
            None
        };
        if let Some(frame) = &wire {
            let response = Status::<S, D>::decode(frame.clone()).unwrap();
            assert_eq!(response.promise, record.promise);
            assert_eq!(
                response.attestation.signer,
                crate::types::Participant::new(n - 1)
            );
            assert!(response.verify(&mut context, &f.verifier, &Sequential));
        }
        // Higher owner fence permits exact retained bytes, never fresh signing.
        let mut fence = record.clone();
        fence.kind = 2;
        fence.promise.ballot = Rnd::new(Epoch::new(1), View::new(3));
        actor.state.replay(&ArtifactWith::Recovery(fence.clone()));
        actor = actor.append_journal(ArtifactWith::Recovery(fence)).await;
        actor = actor.sync_journal().await;
        let (retained, receipt) = actor.state.sign_recovery(&record).unwrap();
        assert!(receipt.is_none());
        if let Some(wire) = wire {
            assert_eq!(retained, wire);
        }
        assert_eq!(
            signed.load(Ordering::SeqCst),
            1,
            "retained retry called signer"
        );
        drop(actor);
        let journal = Journal::<_, ArtifactWith<S, D, RecoveryProbe>>::init(
            context.child("reopen"),
            journal_config!(s, cache, "receipt-live"),
        )
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
        let kinds: Vec<_> = rows
            .iter()
            .filter_map(|a| {
                if let ArtifactWith::Recovery(w) = a {
                    Some(w.kind)
                } else {
                    None
                }
            })
            .collect();
        assert_eq!(
            kinds,
            vec![0, 1, 2],
            "cancellation cannot erase accepted release receipt"
        );
        signed.store(0, Ordering::SeqCst);
        let (mut fresh, _) = ActorWith::new_with(
            context.child("fresh"),
            config!(s, cache, "unused", n),
            c,
            ReceiptEvidence(f.verifier),
        );
        fresh.state.set_genesis(D::from([0; 32]));
        for row in &rows {
            assert!(fresh.participation.accepts_replay(row));
            if let ArtifactWith::Notarization(c) = row {
                fresh.state.add_notarization(c.clone());
            }
            fresh.state.replay(row);
        }
        fresh.state.finish_notarize_replay();
        let (again, receipt) = fresh.state.sign_recovery(&record).unwrap();
        assert_eq!(again, retained);
        assert!(receipt.is_none());
        assert_eq!(
            signed.load(Ordering::SeqCst),
            0,
            "replayed receipt must not re-sign"
        );
        let mut changed = record;
        changed.promise.accepted = Some((proposal(1).round, D::from([9; 32])));
        assert!(fresh.state.sign_recovery(&changed).is_none());
    });
}
#[test]
fn recovery_response_waits_for_release_receipt_and_replays_exactly() {
    for n in [4, 8, 9, 10, 13, 64] {
        release(n, 0, true);
        release(n, 0, false);
    }
}
#[test]
fn canceled_recovery_reply_still_retains_release_receipt() {
    release(10, 1, false);
}
#[test]
fn failed_release_receipt_sync_retires_without_response() {
    release(9, 2, false);
}
#[test]
fn replayed_unsigned_recovery_reservation_is_blocked_by_later_fence() {
    deterministic::Runner::timed(Duration::from_secs(20)).start(|mut context| async move {
        let n = 10u32;
        let f = ed25519::fixture(
            &mut context,
            b"_COMMONWARE_CONSENSUS_RECOVERY_UNSIGNED_REPLAY_TEST",
            n,
        );
        let s = f.schemes[0].clone();
        let signed = Arc::new(AtomicUsize::new(0));
        let c = RecoveryContext {
            domain: D::from([8; 32]),
            signed: signed.clone(),
            release_gate: None,
        };
        let cache = CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(10));
        let (mut actor, _) = ActorWith::new_with(
            context.child("seed"),
            config!(s, cache, "receipt-unsigned", n),
            c.clone(),
            ReceiptEvidence(f.verifier.clone()),
        );
        actor.state.set_genesis(D::from([0; 32]));
        actor.journal = Some(
            Journal::init(
                actor.context.child("journal"),
                journal_config!(s, cache, "receipt-unsigned"),
            )
            .await
            .unwrap(),
        );
        let cert = certificate(&f);
        actor.state.add_notarization(cert.clone());
        actor = actor.append_journal(ArtifactWith::Notarization(cert)).await;
        let record = request();
        actor.state.replay(&ArtifactWith::Recovery(record.clone()));
        actor = actor
            .append_journal(ArtifactWith::Recovery(record.clone()))
            .await;
        let mut fence = record.clone();
        fence.kind = 2;
        fence.promise.ballot = Rnd::new(Epoch::new(1), View::new(3));
        actor.state.replay(&ArtifactWith::Recovery(fence.clone()));
        actor = actor.append_journal(ArtifactWith::Recovery(fence)).await;
        actor = actor.sync_journal().await;
        drop(actor);
        let journal = Journal::<_, ArtifactWith<S, D, RecoveryProbe>>::init(
            context.child("reopen"),
            journal_config!(s, cache, "receipt-unsigned"),
        )
        .await
        .unwrap();
        let mut replay = journal
            .replay(0, 0, NZUsize!(4096), ReadOptions::DONT_CACHE)
            .await
            .unwrap();
        let (mut fresh, _) = ActorWith::new_with(
            context.child("fresh"),
            config!(s, cache, "unused", n),
            c,
            ReceiptEvidence(f.verifier),
        );
        fresh.state.set_genesis(D::from([0; 32]));
        let mut kinds = Vec::new();
        while let Some(row) = replay.next().await {
            let row = row.unwrap().3;
            assert!(fresh.participation.accepts_replay(&row));
            if let ArtifactWith::Notarization(c) = &row {
                fresh.state.add_notarization(c.clone());
            }
            if let ArtifactWith::Recovery(w) = &row {
                kinds.push(w.kind);
            }
            fresh.state.replay(&row);
        }
        drop(replay.finish().unwrap());
        fresh.state.finish_notarize_replay();
        assert_eq!(kinds, vec![0, 2]);
        assert!(fresh.state.sign_recovery(&record).is_none());
        assert_eq!(signed.load(Ordering::SeqCst), 0);
    });
}
