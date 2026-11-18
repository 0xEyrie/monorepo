// Actual Marshal controls: native crypto succeeds; the test Mode decides the companion.
use super::*;
use crate::simplex::{
    marshal::store::Certificates,
    phase2::{Plain, companion_probe::Probe},
};
use std::sync::atomic::{AtomicUsize, Ordering};

#[derive(Clone)]
struct CompanionProvider {
    scheme: Arc<S>,
    calls: Arc<AtomicUsize>,
    limit: usize,
    first_full: bool,
}
impl CompanionProvider {
    fn new(scheme: S, limit: usize, first_full: bool) -> Self {
        Self {
            scheme: Arc::new(scheme),
            calls: Arc::new(AtomicUsize::new(0)),
            limit,
            first_full,
        }
    }
    fn retired(&self) -> bool {
        self.calls.load(Ordering::SeqCst) >= self.limit
    }
}
impl Provider for CompanionProvider {
    type Scope = Epoch;
    type Scheme = S;
    fn scoped(&self, _: Epoch) -> Option<Scoped<S>> {
        let call = self.calls.fetch_add(1, Ordering::SeqCst);
        if call >= self.limit {
            return None;
        }
        Some(if self.first_full && call == 0 {
            Scoped::scheme(self.scheme.clone())
        } else {
            Scoped::verifier(self.scheme.clone())
        })
    }
}

// Delegate actual durable archive operations while selecting the private probe Mode.
struct ProbeCertificates<T, const ACCEPT: bool> {
    inner: T,
    puts: Arc<AtomicUsize>,
}
impl<T, const ACCEPT: bool> Certificates for ProbeCertificates<T, ACCEPT>
where
    T: Certificates<BlockDigest = D, Commitment = D, Scheme = S, Mode = Plain>,
{
    type BlockDigest = D;
    type Commitment = D;
    type Scheme = S;
    type Mode = Probe<ACCEPT>;
    type Error = T::Error;

    async fn put(
        mut self,
        height: Height,
        digest: D,
        finalization: &Finalization<S, D>,
    ) -> Result<Self, Self::Error> {
        self.puts.fetch_add(1, Ordering::SeqCst);
        self.inner = self.inner.put(height, digest, finalization).await?;
        Ok(self)
    }
    async fn sync(mut self) -> Result<Self, Self::Error> {
        self.inner = self.inner.sync().await?;
        Ok(self)
    }
    async fn start_sync(mut self) -> Result<(Self, commonware_runtime::Handle<()>), Self::Error> {
        let handle;
        (self.inner, handle) = self.inner.start_sync().await?;
        Ok((self, handle))
    }
    async fn get(
        &self,
        id: commonware_storage::archive::Identifier<'_, D>,
    ) -> Result<Option<Finalization<S, D>>, Self::Error> {
        self.inner.get(id).await
    }
    async fn has(&self, height: Height) -> Result<bool, Self::Error> {
        self.inner.has(height).await
    }
    async fn prune(mut self, min: Height) -> Result<Self, Self::Error> {
        self.inner = self.inner.prune(min).await?;
        Ok(self)
    }
    fn last_index(&self) -> Option<Height> {
        self.inner.last_index()
    }
    fn ranges_from(&self, from: Height) -> impl Iterator<Item = (Height, Height)> {
        self.inner.ranges_from(from)
    }
}

async fn start_companion_actor<R, Buf, P, const ACCEPT: bool>(
    context: deterministic::Context,
    partition_prefix: &str,
    provider: P,
    application: R,
    buffer: Option<Buf>,
    start: Start<S, D, Arc<B>, Probe<ACCEPT>>,
) -> (
    Mailbox<S, Standard<B>, Probe<ACCEPT>>,
    Option<Buf>,
    RecordingResolver,
    commonware_runtime::Handle<()>,
    Arc<AtomicUsize>,
)
where
    R: Reporter<Activity = Update<B>>,
    P: Provider<Scope = Epoch, Scheme = S>,
    Buf: crate::simplex::marshal::core::Buffer<Standard<B>, PublicKey = PublicKey> + Clone,
{
    let config = Config {
        provider,
        epocher: FixedEpocher::new(BLOCKS_PER_EPOCH),
        start,
        mailbox_size: NZUsize!(100),
        view_retention: ViewDelta::new(10),
        max_repair: NZUsize!(10),
        max_pending_acks: NZUsize!(1),
        block_codec_config: (),
        partition_prefix: partition_prefix.to_string(),
        prunable_items_per_section: NZU64!(10),
        replay_buffer: NZUsize!(1024),
        key_write_buffer: NZUsize!(1024),
        value_write_buffer: NZUsize!(1024),
        page_cache: CacheRef::from_pooler(&context, PAGE_SIZE, PAGE_CACHE_SIZE),
        strategy: Sequential,
    };
    let finalizations_by_height = immutable::Archive::<_, D, Finalization<S, D>>::init(
        context.child("finalizations_by_height"),
        immutable::Config {
            metadata_partition: format!("{partition_prefix}-finalizations-by-height-metadata"),
            freezer_table_partition: format!(
                "{partition_prefix}-finalizations-by-height-freezer-table"
            ),
            freezer_table_initial_size: 64,
            freezer_table_resize_frequency: 10,
            freezer_table_resize_chunk_size: 10,
            freezer_key_partition: format!(
                "{partition_prefix}-finalizations-by-height-freezer-key"
            ),
            freezer_key_page_cache: config.page_cache.clone(),
            freezer_value_partition: format!(
                "{partition_prefix}-finalizations-by-height-freezer-value"
            ),
            freezer_value_target_size: 1024,
            freezer_value_compression: None,
            ordinal_partition: format!("{partition_prefix}-finalizations-by-height-ordinal"),
            items_per_section: NZU64!(10),
            codec_config: S::certificate_codec_config_unbounded(),
            replay_buffer: config.replay_buffer,
            freezer_key_write_buffer: config.key_write_buffer,
            freezer_value_write_buffer: config.value_write_buffer,
            ordinal_write_buffer: config.key_write_buffer,
        },
    )
    .await
    .expect("failed to initialize finalizations by height archive");
    let finalized_blocks = immutable::Archive::init(
        context.child("finalized_blocks"),
        immutable::Config {
            metadata_partition: format!("{partition_prefix}-finalized_blocks-metadata"),
            freezer_table_partition: format!("{partition_prefix}-finalized_blocks-freezer-table"),
            freezer_table_initial_size: 64,
            freezer_table_resize_frequency: 10,
            freezer_table_resize_chunk_size: 10,
            freezer_key_partition: format!("{partition_prefix}-finalized_blocks-freezer-key"),
            freezer_key_page_cache: config.page_cache.clone(),
            freezer_value_partition: format!("{partition_prefix}-finalized_blocks-freezer-value"),
            freezer_value_target_size: 1024,
            freezer_value_compression: None,
            ordinal_partition: format!("{partition_prefix}-finalized_blocks-ordinal"),
            items_per_section: NZU64!(10),
            codec_config: config.block_codec_config,
            replay_buffer: config.replay_buffer,
            freezer_key_write_buffer: config.key_write_buffer,
            freezer_value_write_buffer: config.value_write_buffer,
            ordinal_write_buffer: config.key_write_buffer,
        },
    )
    .await
    .expect("failed to initialize finalized blocks archive");
    let puts = Arc::new(AtomicUsize::new(0));
    let finalizations_by_height = ProbeCertificates::<_, ACCEPT> {
        inner: finalizations_by_height,
        puts: puts.clone(),
    };
    let (actor, mailbox, _) = Actor::init(
        context.child("actor"),
        finalizations_by_height,
        finalized_blocks,
        config,
    )
    .await;
    let (resolver_rx, resolver) = RecordingResolver::holding(context.child("mailbox"));
    let actor_handle = if let Some(buffer) = buffer.clone() {
        actor.start(application, buffer, (resolver_rx, resolver.clone()))
    } else {
        actor.start_unbuffered(application, (resolver_rx, resolver.clone()))
    };
    (mailbox, buffer, resolver, actor_handle, puts)
}

async fn finalized_delivery<const ACCEPT: bool>(mut context: deterministic::Context) {
    let Fixture { schemes, .. } =
        bls12381_threshold_vrf::fixture::<V, _>(&mut context, NAMESPACE, NUM_VALIDATORS);
    let genesis = StandardHarness::genesis_block(NUM_VALIDATORS as u16);
    let height = Height::new(1);
    let round = Round::new(Epoch::zero(), View::new(1));
    let block = make_raw_block(genesis.digest(), height, 100);
    let proposal = Proposal::new(round, View::zero(), StandardHarness::commitment(&block));
    let finalization = StandardHarness::make_finalization(proposal, &schemes, QUORUM);
    assert!(finalization.verify(&mut context, &schemes[0], &Sequential));
    let application = Application::<B>::manual_ack();
    // This is verifier-only and survives exactly the admission lookup. The hook
    // must receive that captured scope after the Provider has retired it.
    let provider = CompanionProvider::new(schemes[0].clone(), 1, false);
    let (mailbox, _buffer, resolver, actor, puts) = start_companion_actor::<_, _, _, ACCEPT>(
        context.child("validator"),
        "companion-finalized-delivery",
        provider.clone(),
        application.clone(),
        Some(RecordingBuffer::default()),
        Start::Genesis(genesis.into()),
    )
    .await;
    assert_eq!(application.acknowledged().await, Height::zero());
    assert!(!provider.retired());
    let (response, response_rx) = oneshot::channel();
    assert!(
        resolver
            .enqueue(handler::Message::Deliver {
                delivery: Delivery {
                    key: handler::Key::Finalized { height },
                    subscribers: NonEmptyVec::new((
                        handler::Annotation::Finalized(handler::Finalized::ByHeight { height }),
                        tracing::Span::none(),
                    )),
                },
                value: (finalization, block.clone()).encode(),
                response,
            })
            .accepted()
    );
    assert_eq!(response_rx.await.expect("delivery reply missing"), ACCEPT);
    assert!(provider.retired());
    if ACCEPT {
        assert_eq!(application.acknowledged().await, height);
        assert_eq!(application.blocks()[&height].digest(), block.digest());
        assert!(mailbox.get_finalization(height).await.is_some());
        assert!(puts.load(Ordering::SeqCst) > 0);
    } else {
        // A processed read also fences any effects of the preceding delivery.
        assert!(mailbox.get_finalization(height).await.is_none());
        assert_eq!(puts.load(Ordering::SeqCst), 0);
        assert!(application.tip().is_none());
        assert!(application.blocks().keys().all(|height| height.is_zero()));
        assert!(application.pending_ack_heights().is_empty());
        assert!(
            mailbox
                .get_processed()
                .await
                .is_none_or(|p| p.height().is_zero())
        );
    }
    actor.abort();
    let _ = actor.await;
}

#[test_traced("WARN")]
fn companion_rejects_valid_native_finalized_delivery() {
    deterministic::Runner::timed(Duration::from_secs(30)).start(finalized_delivery::<false>);
}

#[test_traced("WARN")]
fn companion_accepts_delivery_with_captured_verifier_only_scope() {
    deterministic::Runner::timed(Duration::from_secs(30)).start(finalized_delivery::<true>);
}

#[test_traced("WARN")]
fn companion_uses_each_deliveries_captured_scope_in_one_epoch_batch() {
    deterministic::Runner::timed(Duration::from_secs(30)).start(|mut context| async move {
        let Fixture { schemes, .. } =
            bls12381_threshold_vrf::fixture::<V, _>(&mut context, NAMESPACE, NUM_VALIDATORS);
        let genesis = StandardHarness::genesis_block(NUM_VALIDATORS as u16);
        let accepted = make_raw_block(genesis.digest(), Height::new(1), 100);
        let application = Application::<B>::manual_ack();
        // The notarization captures a full scope; finalizations capture only
        // verifier scopes. All five native certificates share the same roster.
        let provider = CompanionProvider::new(schemes[0].clone(), 5, true);
        let (mailbox, _, resolver, actor, puts) = start_companion_actor::<_, _, _, true>(
            context.child("validator"),
            "companion-mixed-scopes",
            provider.clone(),
            application.clone(),
            Some(RecordingBuffer::default()),
            Start::Genesis(genesis.into()),
        )
        .await;
        assert_eq!(application.acknowledged().await, Height::zero());
        crate::simplex::phase2::companion_probe::reset_checked();
        let mut responses = Vec::new();
        // Queue all without yielding: the actual resolver drains one mixed
        // epoch batch. The ordinary notarization has no companion requirement.
        let block = make_raw_block(accepted.digest(), Height::new(5), 500);
        let notarization = StandardHarness::make_notarization(
            Proposal::new(
                Round::new(Epoch::zero(), View::new(5)),
                View::new(4),
                StandardHarness::commitment(&block),
            ),
            &schemes,
            QUORUM,
        );
        let (response, response_rx) = oneshot::channel();
        assert!(
            resolver
                .enqueue(handler::Message::Deliver {
                    delivery: Delivery {
                        key: handler::Key::Notarized {
                            round: notarization.round(),
                        },
                        subscribers: NonEmptyVec::new((
                            handler::Annotation::Notarization {
                                round: notarization.round(),
                            },
                            tracing::Span::none(),
                        )),
                    },
                    value: (notarization, block).encode(),
                    response,
                })
                .accepted()
        );
        responses.push(response_rx);
        for height in [3, 2, 4, 1].map(Height::new) {
            let block = if height == Height::new(1) {
                accepted.clone()
            } else {
                make_raw_block(accepted.digest(), height, height.get() * 100)
            };
            let height = block.height();
            let mut finalization = StandardHarness::make_finalization(
                Proposal::new(
                    Round::new(Epoch::zero(), View::new(height.get())),
                    View::new(height.get() - 1),
                    StandardHarness::commitment(&block),
                ),
                &schemes,
                QUORUM,
            );
            assert!(finalization.verify(&mut context, &schemes[0], &Sequential));
            if height == Height::new(3) {
                // Keep the requested height/payload binding intact but invalidate
                // the native QC. Its companion callback must never run.
                finalization.proposal.parent = View::zero();
                assert!(!finalization.verify(&mut context, &schemes[0], &Sequential));
            }
            let (response, response_rx) = oneshot::channel();
            assert!(
                resolver
                    .enqueue(handler::Message::Deliver {
                        delivery: Delivery {
                            key: handler::Key::Finalized { height },
                            subscribers: NonEmptyVec::new((
                                handler::Annotation::Finalized(handler::Finalized::ByHeight {
                                    height,
                                }),
                                tracing::Span::none(),
                            )),
                        },
                        value: (finalization, block).encode(),
                        response,
                    })
                    .accepted()
            );
            responses.push(response_rx);
        }
        for (response, expected) in responses.into_iter().zip([true, false, false, false, true]) {
            assert_eq!(response.await.expect("delivery reply missing"), expected);
        }
        assert_eq!(
            crate::simplex::phase2::companion_probe::checked(),
            [2, 4, 1]
                .map(|view| Round::new(Epoch::zero(), View::new(view)))
                .to_vec(),
            "check the exact native-valid finalization once; skip notarization and bad QC"
        );
        assert!(provider.retired());
        assert_eq!(application.acknowledged().await, Height::new(1));
        assert_eq!(
            application.blocks()[&Height::new(1)].digest(),
            accepted.digest()
        );
        assert!(mailbox.get_finalization(Height::new(2)).await.is_none());
        assert!(mailbox.get_finalization(Height::new(3)).await.is_none());
        assert!(mailbox.get_finalization(Height::new(4)).await.is_none());
        assert!(mailbox.get_finalization(Height::new(1)).await.is_some());
        assert_eq!(puts.load(Ordering::SeqCst), 1);
        actor.abort();
        let _ = actor.await;
    });
}

async fn rejected_floor(mut context: deterministic::Context, configured: bool) {
    let Fixture { schemes, .. } =
        bls12381_threshold_vrf::fixture::<V, _>(&mut context, NAMESPACE, NUM_VALIDATORS);
    let genesis = StandardHarness::genesis_block(NUM_VALIDATORS as u16);
    let floor_round = Round::new(Epoch::zero(), View::new(5));
    let floor_block = make_raw_block(Sha256::hash(&[b"floor-parent"]), Height::new(5), 500);
    let finalization = StandardHarness::make_finalization(
        Proposal::new(
            floor_round,
            View::new(4),
            StandardHarness::commitment(&floor_block),
        ),
        &schemes,
        QUORUM,
    );
    assert!(finalization.verify(&mut context, &schemes[0], &Sequential));
    let buffer = RecordingBuffer::default();
    buffer.insert(floor_block);
    let application = Application::<B>::manual_ack();
    let start = if configured {
        Start::Floor(finalization.clone())
    } else {
        Start::Genesis(genesis.into())
    };
    let (mailbox, _, resolver, actor, puts) = start_companion_actor::<_, _, _, false>(
        context.child("validator"),
        "companion-rejected-floor",
        VerifierProvider::new(schemes[0].clone()),
        application.clone(),
        Some(buffer.clone()),
        start,
    )
    .await;
    if !configured {
        assert_eq!(application.acknowledged().await, Height::zero());
        mailbox.set_floor(finalization);
    }
    // Catch the actor's fatal floor rejection while keeping its observers alive.
    // A timeout or a successful floor application cannot satisfy this assertion.
    assert!(actor.await.is_err());
    assert_eq!(puts.load(Ordering::SeqCst), 0);
    assert!(application.tip().is_none());
    assert!(application.blocks().keys().all(|height| height.is_zero()));
    assert!(application.pending_ack_heights().is_empty());
    assert_eq!(buffer.subscription_count(), 0);
    assert!(resolver.fetches.lock().is_empty());
}

#[test_traced("WARN")]
fn companion_rejects_configured_floor_before_finalized_effects() {
    deterministic::Runner::new(
        deterministic::Config::new()
            .with_timeout(Some(Duration::from_secs(30)))
            .with_catch_panics(true),
    )
    .start(|context| rejected_floor(context, true));
}

#[test_traced("WARN")]
fn companion_rejects_set_floor_before_finalized_effects() {
    deterministic::Runner::new(
        deterministic::Config::new()
            .with_timeout(Some(Duration::from_secs(30)))
            .with_catch_panics(true),
    )
    .start(|context| rejected_floor(context, false));
}
