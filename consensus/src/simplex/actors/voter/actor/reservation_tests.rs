//! Observe signer calls, not merely publication, at the native sync barrier.
use super::*;
use crate::simplex::{phase2::recovery::Record, types::Subject};
use commonware_cryptography::{
    Digest,
    certificate::{self, Attestation},
};
use commonware_parallel::Strategy;
use commonware_utils::{iter::NonEmpty, ordered::Set};
use std::sync::atomic::{AtomicUsize, Ordering};

#[derive(Clone, Debug)]
struct Observed {
    inner: S,
    finals: Arc<AtomicUsize>,
}
impl certificate::Verifier for Observed {
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
impl certificate::Scheme for Observed {
    type Signature = <S as certificate::Scheme>::Signature;
    fn me(&self) -> Option<crate::types::Participant> {
        self.inner.me()
    }
    fn participants(&self) -> &Set<PublicKey> {
        self.inner.participants()
    }
    fn sign<T: Digest>(&self, subject: Subject<'_, T>) -> Option<Attestation<Self>> {
        if matches!(subject, Subject::FinalizeExtension { .. }) {
            self.finals.fetch_add(1, Ordering::SeqCst);
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

#[test]
fn recovery_release_never_invokes_the_signer_after_a_later_floor() {
    deterministic::Runner::default().start(|mut context| async move {
        let fixture = ed25519::fixture(
            &mut context,
            b"_COMMONWARE_CONSENSUS_RECOVERY_RELEASE_TEST",
            6,
        );
        let count = Arc::new(AtomicUsize::new(0));
        let scheme = Observed {
            inner: fixture.schemes[5].clone(),
            finals: count.clone(),
        };
        let mut state = StateWith::<_, _, _, D, Extended>::new_with(
            context.child("voter"),
            super::super::super::state::Config {
                scheme: scheme.clone(),
                elector: RoundRobin::<Sha256>::default().build(scheme.participants()),
                epoch: Epoch::new(1),
                view_retention: ViewDelta::new(10),
                leader_timeout: Duration::from_secs(1),
                certification_timeout: Duration::from_secs(1),
                timeout_retry: Duration::from_secs(1),
                skip_budget: 4,
            },
            ExtendedContext::new::<Sha256>(D::from([8; 32]), D::from([9; 32])),
        );
        state.set_genesis(D::from([0; 32]));
        let certificate = notarization(&fixture, 1);
        state.add_notarization(Notarization::<Observed, D> {
            proposal: certificate.proposal,
            certificate: certificate.certificate,
        });
        state.certified(View::new(1), true).unwrap();
        let mut subject = statement(1, D::from([9; 32]));
        subject.ballot = Rnd::new(Epoch::new(1), View::new(2));
        state
            .construct_recovery_promise(View::new(1), subject.ballot)
            .unwrap();
        let proof = crate::simplex::extension::recovery::Proof {
            statuses: fixture.schemes[..5]
                .iter()
                .map(|inner| {
                    crate::simplex::extension::recovery::Status::sign(
                        &Observed {
                            inner: inner.clone(),
                            finals: count.clone(),
                        },
                        crate::simplex::extension::recovery::Promise {
                            proposal: subject.proposal.clone(),
                            domain: subject.domain,
                            ballot: subject.ballot,
                            accepted: None,
                        },
                    )
                    .unwrap()
                })
                .collect(),
        };
        let ArtifactWith::Recovery(acceptance) = state
            .construct_recovery_accept(subject, &proof, &Sequential)
            .unwrap()
        else {
            unreachable!()
        };
        assert_eq!(count.load(Ordering::SeqCst), 0);
        assert!(state.sign_recovery(&acceptance).is_some());
        assert_eq!(count.load(Ordering::SeqCst), 1);
        let certificate = notarization(&fixture, 2);
        state.add_notarization(Notarization::<Observed, D> {
            proposal: certificate.proposal,
            certificate: certificate.certificate,
        });
        state.certified(View::new(2), true).unwrap();
        state
            .construct_recovery_promise(View::new(1), Rnd::new(Epoch::new(1), View::new(3)))
            .unwrap();
        assert!(state.sign_recovery(&acceptance).is_none());
        assert_eq!(count.load(Ordering::SeqCst), 1);
    });
}

#[derive(Clone)]
struct Ready(Statement<D>);
impl Participation<Observed, D, Extended> for Ready {
    fn notarize(&mut self, vote: Notarize<Observed, D>) -> report::Notarize<Observed, D> {
        vote.into()
    }
    fn final_subject(&mut self, p: &Proposal<D>) -> Option<Statement<D>> {
        (p == &self.0.proposal).then(|| self.0.clone())
    }
    fn accepts_finalization(&mut self, _: &Finalization<Observed, D>) -> bool {
        false
    }
    fn accepts_replay(&mut self, a: &ArtifactWith<Observed, D, Extended>) -> bool {
        match a {
            ArtifactWith::Recovery(Record::Reserve(s)) => s == &self.0,
            ArtifactWith::Finalize(v) => v.vote().statement == self.0,
            _ => true,
        }
    }
    fn prune(&mut self, _: View) {}
}
#[derive(Clone)]
struct Sink;
impl Reporter for Sink {
    type Activity = ActivityWith<Observed, D, Extended>;
    fn report(&mut self, _: Self::Activity) -> Feedback {
        Feedback::Ok
    }
}

fn exercise(fail_sync: bool, verifier: bool) {
    deterministic::Runner::new(
        deterministic::Config::new()
            .with_timeout(Some(Duration::from_secs(20)))
            .with_catch_panics(true),
    )
    .start(move |mut context| async move {
        let fixture = ed25519::fixture(
            &mut context,
            b"_COMMONWARE_CONSENSUS_FINAL_RESERVATION_TEST",
            7,
        );
        let count = Arc::new(AtomicUsize::new(0));
        let scheme = Observed {
            inner: if verifier {
                fixture.verifier.clone()
            } else {
                fixture.schemes[0].clone()
            },
            finals: count.clone(),
        };
        let pending = PendingSyncs::default();
        pending.unblock();
        let actor_context = DelayedSyncContext {
            inner: context.child("voter"),
            pending: pending.clone(),
        };
        let cache = CacheRef::from_pooler(&actor_context, NZU16!(1024), NZUsize!(10));
        let first = statement(1, D::from([9; 32]));
        let cfg = Config {
            scheme: scheme.clone(),
            elector: RoundRobin::<Sha256>::default().build(scheme.participants()),
            blocker: NoopBlocker::default(),
            automaton: App::default(),
            relay: App::default(),
            reporter: Sink,
            partition: "reservation".into(),
            epoch: Epoch::new(1),
            floor: FloorWith::Genesis(D::from([0; 32])),
            mailbox_size: NZUsize!(8),
            leader_timeout: Duration::from_secs(10),
            certification_timeout: Duration::from_secs(10),
            timeout_retry: Duration::from_secs(10),
            skip_budget: 7,
            view_retention: ViewDelta::new(10),
            replay_buffer: NZUsize!(4096),
            write_buffer: NZUsize!(4096),
            page_cache: cache.clone(),
        };
        let (mut actor, _input) = ActorWith::new_with(
            actor_context,
            cfg,
            ExtendedContext::new::<Sha256>(D::from([8; 32]), D::from([9; 32])),
            Ready(first.clone()),
        );
        actor.state.set_genesis(D::from([0; 32]));
        let certificate = notarization(&fixture, 1);
        let certificate = Notarization::<Observed, D> {
            proposal: certificate.proposal,
            certificate: certificate.certificate,
        };
        actor.state.add_notarization(certificate.clone());
        actor.state.certified(View::new(1), true).unwrap();
        actor.journal = Some(
            Journal::init(
                actor.context.child("journal"),
                JConfig {
                    partition: "reservation".into(),
                    compression: None,
                    codec_config: scheme.certificate_codec_config(),
                    page_cache: cache,
                    write_buffer: NZUsize!(4096),
                },
            )
            .await
            .unwrap(),
        );
        actor = actor
            .append_journal(ArtifactWith::Notarization(certificate))
            .await;
        actor = actor
            .append_journal(ArtifactWith::Certification(proposal(1).round, true))
            .await;
        actor = actor.sync_journal().await;
        pending.arm();
        let handle = context
            .child("prepare")
            .spawn(|_| actor.prepare_finalize(View::new(1)));
        if verifier {
            let (actor, vote) = handle.await.unwrap();
            assert!(vote.is_none());
            assert!(
                actor.dirty_section.is_none(),
                "a verifier must not reserve signing authority"
            );
            assert_eq!(pending.calls(), 0, "the preinstalled gate must not be used");
            assert_eq!(count.load(Ordering::SeqCst), 0);
            return;
        }
        while pending.lock().is_empty() {
            reschedule().await;
        }
        let sync = next_pending_sync(&pending);
        sync.blocked.await.unwrap();
        assert_eq!(
            count.load(Ordering::SeqCst),
            0,
            "signer permission escaped before sync"
        );
        if fail_sync {
            drop(sync.release);
            assert!(handle.await.is_err());
            assert_eq!(count.load(Ordering::SeqCst), 0);
        } else {
            sync.release.send(Ok(())).unwrap();
            let (actor, vote) = handle.await.unwrap();
            assert_eq!(vote.unwrap().vote().statement, first);
            assert_eq!(count.load(Ordering::SeqCst), 1);
            drop(actor);
        }
    });
}

#[test]
fn original_final_signer_waits_for_native_reservation_sync() {
    exercise(false, false);
}

#[test]
fn original_final_signer_is_never_called_after_failed_reservation_sync() {
    exercise(true, false);
}

#[test]
fn verifier_only_actor_never_reserves_original_signing_authority() {
    exercise(false, true);
}

fn restart_reservation(fenced: bool) {
    deterministic::Runner::timed(Duration::from_secs(20)).start(move |mut context| async move {
        // A legacy recovery promise is exercised only on its supported roster.
        let n = if fenced { 6 } else { 7 };
        let fixture = ed25519::fixture(
            &mut context,
            b"_COMMONWARE_CONSENSUS_RESERVED_RESTART_TEST",
            n,
        );
        let count = Arc::new(AtomicUsize::new(0));
        let scheme = Observed {
            inner: fixture.schemes[0].clone(),
            finals: count.clone(),
        };
        let first = statement(1, D::from([9; 32]));
        let cache = CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(10));
        let mut journal = Journal::<_, ArtifactWith<Observed, D, Extended>>::init(
            context.child("seed"),
            JConfig {
                partition: "reserved-restart".into(),
                compression: None,
                codec_config: scheme.certificate_codec_config(),
                page_cache: cache.clone(),
                write_buffer: NZUsize!(4096),
            },
        )
        .await
        .unwrap();
        let certificate = notarization(&fixture, 1);
        let mut records = vec![
            ArtifactWith::Notarization(Notarization::<Observed, D> {
                proposal: certificate.proposal,
                certificate: certificate.certificate,
            }),
            ArtifactWith::Certification(first.proposal.round, true),
            ArtifactWith::Recovery(Record::Reserve(first.clone())),
        ];
        if fenced {
            records.push(ArtifactWith::Recovery(Record::Promise {
                proposal: first.proposal.clone(),
                domain: first.domain,
                ballot: Rnd::new(Epoch::new(1), View::new(2)),
                accepted: Some(first.clone()),
            }));
        }
        for record in records {
            journal = journal.append(1, &record).await.unwrap().0;
        }
        journal = journal.sync(1).await.unwrap();
        drop(journal);
        assert_eq!(count.load(Ordering::SeqCst), 0);
        let (network, oracle) = Network::new_with_peers(
            context.child("network"),
            NConfig {
                max_size: 1024 * 1024,
                max_peers_per_set: NonZeroUsize::new(n as usize).unwrap(),
                disconnect_on_block: true,
                tracked_peer_sets: NZUsize!(1),
            },
            fixture.participants.clone(),
        )
        .await;
        network.start();
        let me = fixture.participants[0].clone();
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
        let (actor, mut input) = ActorWith::new_with(
            context.child("restarted"),
            Config {
                scheme: scheme.clone(),
                elector: RoundRobin::<Sha256>::default().build(scheme.participants()),
                blocker: NoopBlocker::default(),
                automaton: App::default(),
                relay: App::default(),
                reporter: Sink,
                partition: "reserved-restart".into(),
                epoch: Epoch::new(1),
                floor: FloorWith::Genesis(D::from([0; 32])),
                mailbox_size: NZUsize!(16),
                leader_timeout: Duration::from_secs(10),
                certification_timeout: Duration::from_secs(10),
                timeout_retry: Duration::from_secs(10),
                skip_budget: 7,
                view_retention: ViewDelta::new(10),
                replay_buffer: NZUsize!(4096),
                write_buffer: NZUsize!(4096),
                page_cache: cache,
            },
            ExtendedContext::new::<Sha256>(D::from([8; 32]), D::from([9; 32])),
            Ready(first.clone()),
        );
        let (batcher_tx, mut batcher_rx) = mailbox::new(context.child("batcher"), NZUsize!(16));
        let (resolver_tx, _resolver_rx) = mailbox::new(context.child("resolver"), NZUsize!(16));
        let handle = actor.start(
            batcher::Mailbox::new(batcher_tx),
            resolver::Mailbox::new(resolver_tx),
            votes,
            certificates,
        );
        if fenced {
            let _ = input
                .prepare_recovery(crate::simplex::extension::request::Query::Discover)
                .await
                .unwrap();
            assert_eq!(
                count.load(Ordering::SeqCst),
                0,
                "full replay must fence the old reservation before signing"
            );
            while let Some(message) = batcher_rx.recv().now_or_never().flatten() {
                assert!(!matches!(
                    message,
                    batcher::Message::Constructed(VoteWith::Finalize(_))
                ));
            }
        } else {
            loop {
                if let batcher::Message::Constructed(VoteWith::Finalize(v)) =
                    batcher_rx.recv().await.unwrap()
                {
                    assert_eq!(v.vote().statement, first);
                    break;
                }
            }
            assert_eq!(count.load(Ordering::SeqCst), 1);
        }
        handle.abort();
        let _ = handle.await;
    });
}

#[test]
fn unsigned_final_reservation_restarts_as_the_exact_reserved_vote() {
    restart_reservation(false);
}

#[test]
fn unsigned_final_reservation_replay_reads_the_later_floor_before_signing() {
    restart_reservation(true);
}
