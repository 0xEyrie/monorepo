//! Compile the extension journal and its storage-fault tests without generating
//! the unrelated consensus network-test monomorphizations. The library is still
//! built normally; this target exercises the identical production source.

#[cfg(not(target_arch = "wasm32"))]
#[path = "../src/simplex/extension/fence.rs"]
mod fence;

#[cfg(not(target_arch = "wasm32"))]
#[test]
fn exported_fence_preserves_the_signing_boundary() {
    use commonware_consensus::simplex::extension::fence::{Error, Fence};
    use commonware_cryptography::sha256::Digest;
    use commonware_runtime::{
        Runner as _, Supervisor as _, buffer::paged::CacheRef, deterministic,
    };
    use commonware_storage::journal::segmented::variable::Config;
    use commonware_utils::{NZU16, NZUsize};

    deterministic::Runner::default().start(|context| async move {
        let cfg = Config {
            partition: "exported-fence".into(),
            compression: None,
            codec_config: NZUsize!(4),
            page_cache: CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(8)),
            write_buffer: NZUsize!(1024),
        };
        let slot = Digest::from([1; 32]);
        let value = Digest::from([2; 32]);
        let mut fence = Fence::open(
            context.child("fence"),
            cfg.clone(),
            NZUsize!(8),
            NZUsize!(1024),
        )
        .await
        .unwrap();
        fence.vote(0, vec![(slot, value)]).await.unwrap();
        fence.promise(2, vec![slot]).await.unwrap();
        drop(fence);
        let mut fence = Fence::open(context.child("recovered"), cfg, NZUsize!(8), NZUsize!(1024))
            .await
            .unwrap();
        assert!(matches!(
            fence.vote(0, vec![(slot, value)]).await,
            Err(Error::Stale)
        ));
        assert_eq!(
            fence.promise(2, vec![slot]).await.unwrap()[0]
                .accepted
                .unwrap()
                .value,
            value
        );
    });
}
