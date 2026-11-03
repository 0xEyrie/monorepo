use super::*;
use commonware_codec::{Decode as _, Encode as _};
use commonware_cryptography::sha256::Digest as Hash;
use commonware_runtime::{
    Runner as _, Supervisor as _,
    buffer::paged::CacheRef,
    deterministic,
    mocks::{DelayedSyncContext, PendingSyncs, release_pending_syncs},
};
use commonware_utils::{NZU16, NZUsize};

fn hash(byte: u8) -> Hash {
    Hash::from([byte; 32])
}

fn config(context: &deterministic::Context) -> JournalConfig<NonZeroUsize> {
    JournalConfig {
        partition: "extension-fences".into(),
        compression: None,
        codec_config: NZUsize!(8),
        page_cache: CacheRef::from_pooler(context, NZU16!(1024), NZUsize!(8)),
        write_buffer: NZUsize!(1024),
    }
}

async fn open(context: deterministic::Context) -> Fence<deterministic::Context, Hash> {
    let cfg = config(&context);
    Fence::open(context, cfg, NZUsize!(16), NZUsize!(1024))
        .await
        .unwrap()
}

#[test]
fn restart_retains_votes_promises_and_frozen_statuses() {
    let (_, checkpoint) =
        deterministic::Runner::default().start_and_recover(|context| async move {
            let mut fence = open(context.child("fence")).await;
            fence
                .vote(0, vec![(hash(1), hash(10)), (hash(2), hash(20))])
                .await
                .unwrap();
            let status = fence.promise(3, vec![hash(1), hash(2)]).await.unwrap();
            assert_eq!(
                status[0].accepted,
                Some(Accepted {
                    ballot: 0,
                    value: hash(10)
                })
            );
            // The recovery-proof verifier is outside this local store.
            fence
                .vote(3, vec![(hash(1), hash(11)), (hash(2), hash(21))])
                .await
                .unwrap();
            assert_eq!(
                fence.promise(3, vec![hash(1), hash(2)]).await.unwrap(),
                status
            );
        });
    deterministic::Runner::from(checkpoint).start(|context| async move {
        let mut fence = open(context.child("recovered")).await;
        assert!(matches!(
            fence.vote(0, vec![(hash(1), hash(10))]).await,
            Err(Error::Stale)
        ));
        assert!(matches!(
            fence.vote(3, vec![(hash(2), hash(99))]).await,
            Err(Error::Conflict)
        ));
        let status = fence.promise(3, vec![hash(1), hash(2)]).await.unwrap();
        assert_eq!(
            status[0].accepted,
            Some(Accepted {
                ballot: 0,
                value: hash(10)
            })
        );
        assert_eq!(
            status[1].accepted,
            Some(Accepted {
                ballot: 0,
                value: hash(20)
            })
        );
        let next = fence.promise(4, vec![hash(1), hash(2)]).await.unwrap();
        assert_eq!(
            next[0].accepted,
            Some(Accepted {
                ballot: 3,
                value: hash(11)
            })
        );
        assert_eq!(
            next[1].accepted,
            Some(Accepted {
                ballot: 3,
                value: hash(21)
            })
        );
    });
}

#[test]
fn conflicting_ancestor_rejects_the_whole_child_vote() {
    deterministic::Runner::default().start(|context| async move {
        let mut fence = open(context.child("fence")).await;
        fence.vote(0, vec![(hash(1), hash(10))]).await.unwrap();
        assert!(matches!(
            fence
                .vote(0, vec![(hash(1), hash(99)), (hash(2), hash(20))])
                .await,
            Err(Error::Conflict)
        ));
        // A rejected batch has not fenced the child, including after reopen.
        drop(fence);
        let mut fence = open(context.child("recovered")).await;
        fence.vote(0, vec![(hash(2), hash(21))]).await.unwrap();
        let statuses = fence.promise(1, vec![hash(1), hash(2)]).await.unwrap();
        assert_eq!(statuses[0].accepted.unwrap().value, hash(10));
        assert_eq!(statuses[1].accepted.unwrap().value, hash(21));
    });
}

#[test]
fn malformed_batches_and_capacity_do_not_erase_fences() {
    deterministic::Runner::default().start(|context| async move {
        let cfg = config(&context);
        let mut fence = Fence::open(context.child("fence"), cfg, NZUsize!(2), NZUsize!(1024))
            .await
            .unwrap();
        for values in [
            vec![],
            vec![(hash(1), hash(10)), (hash(1), hash(10))],
            vec![(hash(2), hash(20)), (hash(1), hash(10))],
        ] {
            assert!(matches!(
                fence.vote(0, values).await,
                Err(Error::InvalidBatch)
            ));
        }
        fence
            .vote(0, vec![(hash(1), hash(10)), (hash(2), hash(20))])
            .await
            .unwrap();
        assert!(matches!(
            fence.promise(0, vec![hash(1)]).await,
            Err(Error::InvalidBatch)
        ));
        assert!(matches!(
            fence.promise(1, vec![hash(3)]).await,
            Err(Error::Capacity)
        ));
        fence.vote(0, vec![(hash(1), hash(10))]).await.unwrap();
        fence.vote(2, vec![(hash(1), hash(11))]).await.unwrap();
        assert!(matches!(
            fence.promise(2, vec![hash(1)]).await,
            Err(Error::Unprepared)
        ));
        assert!(matches!(
            fence.promise(1, vec![hash(1)]).await,
            Err(Error::Stale)
        ));
        assert!(matches!(
            fence.vote(2, vec![(hash(1), hash(12))]).await,
            Err(Error::Conflict)
        ));
    });
}

#[test]
fn cancelled_mutation_requires_replay_before_any_further_signing() {
    deterministic::Runner::default().start(|context| async move {
        let pending = PendingSyncs::default();
        let gated = DelayedSyncContext {
            inner: context.child("fence"),
            pending: pending.clone(),
        };
        let mut fence = Fence::open(gated, config(&context), NZUsize!(16), NZUsize!(1024))
            .await
            .unwrap();
        fence.vote(0, vec![(hash(1), hash(10))]).await.unwrap();
        pending.arm();
        {
            let future = fence.promise(1, vec![hash(1)]);
            futures::pin_mut!(future);
            assert!(futures::poll!(future).is_pending());
        }
        release_pending_syncs(&pending);
        assert!(matches!(
            fence.vote(0, vec![(hash(2), hash(20))]).await,
            Err(Error::Poisoned)
        ));
        drop(fence);
        let mut fence = open(context.child("recovered")).await;
        let status = fence.promise(2, vec![hash(1)]).await.unwrap();
        assert_eq!(
            status[0].accepted,
            Some(Accepted {
                ballot: 0,
                value: hash(10)
            })
        );
    });
}

#[test]
fn persisted_conflicting_transition_is_not_silently_replayed() {
    deterministic::Runner::default().start(|context| async move {
        let mut fence = open(context.child("fence")).await;
        fence.vote(0, vec![(hash(1), hash(10))]).await.unwrap();
        let journal = fence.journal.take().unwrap();
        let (journal, _, _) = journal
            .append(
                0,
                &Record::Vote {
                    ballot: 0,
                    values: vec![(hash(1), hash(99))],
                },
            )
            .await
            .unwrap();
        let journal = journal.sync(0).await.unwrap();
        drop(journal);
        drop(fence);
        let result = Fence::<_, Hash>::open(
            context.child("recovered"),
            config(&context),
            NZUsize!(16),
            NZUsize!(1024),
        )
        .await;
        assert!(matches!(result, Err(Error::Conflict)));
    });
}

#[test]
fn storage_codec_is_bounded_and_versioned() {
    let record = Record::Vote {
        ballot: 0x0102030405060708,
        values: vec![(hash(1), hash(2)), (hash(3), hash(4))],
    };
    let bytes = record.encode();
    let mut expected = vec![1, 1, 1, 2, 3, 4, 5, 6, 7, 8, 2];
    for byte in [1, 2, 3, 4] {
        expected.extend([byte; 32]);
    }
    assert_eq!(bytes.as_ref(), expected.as_slice());
    assert_eq!(bytes.len(), record.encode_size());
    assert_eq!(
        Record::<Hash>::decode_cfg(bytes.clone(), &())
            .unwrap()
            .encode(),
        bytes
    );
    let oversize = Record::Promise {
        ballot: 1,
        slots: vec![hash(1); MAX_BATCH_SLOTS + 1],
    }
    .encode();
    assert!(Record::<Hash>::decode_cfg(oversize, &()).is_err());
    for end in 0..bytes.len() {
        assert!(Record::<Hash>::decode_cfg(bytes.slice(..end), &()).is_err());
    }
    let mut invalid = bytes.to_vec();
    invalid[0] = 2;
    assert!(Record::<Hash>::decode_cfg(invalid, &()).is_err());
    let mut invalid = bytes.to_vec();
    invalid[1] = 2;
    assert!(Record::<Hash>::decode_cfg(invalid, &()).is_err());
}

#[test]
fn smaller_limits_cannot_repair_away_a_signed_record() {
    deterministic::Runner::default().start(|context| async move {
        let mut fence = open(context.child("fence")).await;
        fence
            .vote(0, vec![(hash(1), hash(10)), (hash(2), hash(20))])
            .await
            .unwrap();
        drop(fence);
        let mut cfg = config(&context);
        cfg.codec_config = NZUsize!(1);
        let result =
            Fence::<_, Hash>::open(context.child("smaller"), cfg, NZUsize!(16), NZUsize!(1024))
                .await;
        assert!(matches!(result, Err(Error::InvalidBatch)));
        let mut fence = open(context.child("restored")).await;
        assert!(matches!(
            fence.vote(0, vec![(hash(2), hash(21))]).await,
            Err(Error::Conflict)
        ));
    });
}

#[test]
fn cancelled_parent_child_vote_recovers_all_or_neither() {
    deterministic::Runner::default().start(|context| async move {
        let pending = PendingSyncs::default();
        let gated = DelayedSyncContext {
            inner: context.child("fence"),
            pending: pending.clone(),
        };
        let mut fence = Fence::open(gated, config(&context), NZUsize!(16), NZUsize!(1024))
            .await
            .unwrap();
        fence.vote(0, vec![(hash(1), hash(10))]).await.unwrap();
        pending.arm();
        {
            let future = fence.vote(0, vec![(hash(2), hash(20)), (hash(3), hash(30))]);
            futures::pin_mut!(future);
            assert!(futures::poll!(future).is_pending());
        }
        release_pending_syncs(&pending);
        assert!(matches!(
            fence.promise(1, vec![hash(2)]).await,
            Err(Error::Poisoned)
        ));
        drop(fence);
        let mut fence = open(context.child("recovered")).await;
        let statuses = fence
            .promise(1, vec![hash(1), hash(2), hash(3)])
            .await
            .unwrap();
        assert_eq!(statuses[0].accepted.unwrap().value, hash(10));
        assert_eq!(
            statuses[1].accepted.is_some(),
            statuses[2].accepted.is_some()
        );
        if let Some(parent) = statuses[1].accepted {
            assert_eq!(parent.value, hash(20));
            assert_eq!(statuses[2].accepted.unwrap().value, hash(30));
        }
    });
}

#[test]
fn sync_failure_poisoning_survives_until_reopen() {
    deterministic::Runner::default().start(|context| async move {
        let mut fence = open(context.child("fence")).await;
        fence.vote(0, vec![(hash(1), hash(10))]).await.unwrap();
        *context.storage_fault_config().write() = deterministic::FaultConfig {
            sync_rate: Some(commonware_utils::probability!(1.0)),
            ..Default::default()
        };
        assert!(matches!(
            fence.promise(1, vec![hash(1)]).await,
            Err(Error::Storage(_))
        ));
        *context.storage_fault_config().write() = deterministic::FaultConfig::default();
        assert!(matches!(
            fence.vote(0, vec![(hash(2), hash(20))]).await,
            Err(Error::Poisoned)
        ));
        drop(fence);
        let mut fence = open(context.child("recovered")).await;
        let status = fence.promise(2, vec![hash(1)]).await.unwrap();
        assert_eq!(
            status[0].accepted,
            Some(Accepted {
                ballot: 0,
                value: hash(10)
            })
        );
    });
}

#[test]
fn partial_write_crashes_cannot_split_an_ancestry_vote() {
    for seed in 0..32 {
        let (_, checkpoint) =
            deterministic::Runner::seeded(seed).start_and_recover(|context| async move {
                let mut fence = open(context.child("fence")).await;
                fence.vote(0, vec![(hash(1), hash(10))]).await.unwrap();
                *context.storage_fault_config().write() = deterministic::FaultConfig::default()
                    .write(deterministic::WriteConfig {
                        failure_rate: commonware_utils::probability!(1.0),
                        retention_rate: commonware_utils::probability!(1.0),
                        mode: deterministic::PartialWriteMode::Prefix,
                    });
                assert!(matches!(
                    fence
                        .vote(0, vec![(hash(2), hash(20)), (hash(3), hash(30))])
                        .await,
                    Err(Error::Storage(_))
                ));
            });
        deterministic::Runner::from(checkpoint).start(|context| async move {
            *context.storage_fault_config().write() = deterministic::FaultConfig::default();
            let mut fence = open(context.child("recovered")).await;
            let statuses = fence
                .promise(1, vec![hash(1), hash(2), hash(3)])
                .await
                .unwrap();
            assert_eq!(statuses[0].accepted.unwrap().value, hash(10));
            assert_eq!(
                statuses[1].accepted.is_some(),
                statuses[2].accepted.is_some()
            );
            if let Some(parent) = statuses[1].accepted {
                assert_eq!(parent.value, hash(20));
                assert_eq!(statuses[2].accepted.unwrap().value, hash(30));
            }
        });
    }
}
