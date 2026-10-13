//! Custom final-order validation, bounded contexts, and partial-history replay.

use super::*;
use crate::multimmit::marshal::{Ordering as FinalOrdering, OrderingContext};

#[derive(Clone, Copy)]
enum Merge {
    ReverseLanes,
    LaneMajor,
    ChildFirst,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Snapshot {
    epoch: Epoch,
    history: Sha256Digest,
    base: Vec<BlockRef<Sha256Digest>>,
    prefixes: Vec<Vec<BlockRef<Sha256Digest>>>,
}

struct Policy {
    merge: Merge,
    contexts: Arc<Mutex<Vec<Snapshot>>>,
}

impl FinalOrdering<Sha256Digest> for Policy {
    fn order(&self, context: &OrderingContext<Sha256Digest>) -> Vec<BlockRef<Sha256Digest>> {
        self.contexts.lock().push(Snapshot {
            epoch: context.epoch(),
            history: context.history(),
            base: context.base().to_vec(),
            prefixes: context.prefixes().to_vec(),
        });
        match self.merge {
            Merge::ReverseLanes => context.prefixes().iter().rev().flatten().copied().collect(),
            Merge::LaneMajor => context.prefixes().iter().flatten().copied().collect(),
            Merge::ChildFirst => context.prefixes().iter().flatten().rev().copied().collect(),
        }
    }
}

#[rstest]
#[case::fresh(0)]
#[case::partially_published(1)]
#[case::fully_published(3)]
fn receives_the_same_certified_prefixes_after_partial_publication(#[case] published: usize) {
    deterministic::Runner::default().start(|context| async move {
        let committee = committee(170, 2, PathLimits::new(2, 1).unwrap());
        let epoch = committee.config.epoch();
        let bases = vec![base(0, 0), base(1, 0)];
        let blocks = vec![chain(epoch, bases[0], 1), chain(epoch, bases[1], 2)];
        let parent = digest(b"custom history", 0);
        // A2 is outside the certified prefix; B2 is in the extension region. Neither
        // creates a reserved cross-chain position in the custom policy's input.
        let record = Arc::new(
            TipRecord::new(
                parent,
                vec![tip(&blocks[0]), tip(&blocks[1])],
                vec![Height::new(2), Height::new(1)],
            )
            .unwrap(),
        );
        let commitment = record.commitment::<Sha256>();
        let expected = [
            blocks[1][0].reference(),
            blocks[1][1].reference(),
            blocks[0][0].reference(),
        ];
        let mut emitted = bases.clone();
        for reference in &expected[..published] {
            emitted[reference.chain().index()] = *reference;
        }
        let mut actor = actor(
            &context,
            checkpoint(epoch, parent, bases.clone(), emitted),
            blocks.clone(),
            committee.codec(),
            1,
        )
        .await;
        let contexts = Arc::new(Mutex::new(Vec::new()));
        actor.ordering = Some(Arc::new(Policy {
            merge: Merge::ReverseLanes,
            contexts: Arc::clone(&contexts),
        }));
        commit_opening(&mut actor, HistoryLink { commitment, record }).await;
        assert_eq!(actor.catalog.outputs, expected[published..]);
        assert_eq!(actor.catalog.checkpoint.committed(), OutputIndex::new(3));
        assert_eq!(
            *contexts.lock(),
            vec![Snapshot {
                epoch,
                history: commitment,
                base: bases,
                prefixes: blocks
                    .iter()
                    .map(|lane| lane.iter().map(|block| block.reference()).collect())
                    .collect(),
            }]
        );
    });
}

#[rstest]
#[case::child_first(Merge::ChildFirst, false)]
#[case::changed_published_prefix(Merge::LaneMajor, true)]
fn invalid_order_cannot_publish_any_new_output(#[case] merge: Merge, #[case] partial: bool) {
    deterministic::Runner::default().start(|context| async move {
        let committee = committee(171, 2, PathLimits::new(2, 1).unwrap());
        let epoch = committee.config.epoch();
        let bases = vec![base(0, 0), base(1, 0)];
        let blocks = vec![chain(epoch, bases[0], 1), chain(epoch, bases[1], 2)];
        let parent = digest(b"invalid custom history", 0);
        let record =
            Arc::new(TipRecord::at_tips(parent, vec![tip(&blocks[0]), tip(&blocks[1])]).unwrap());
        let commitment = record.commitment::<Sha256>();
        let emitted = if partial {
            vec![bases[0], blocks[1][0].reference()]
        } else {
            bases.clone()
        };
        let mut actor = actor(
            &context,
            checkpoint(epoch, parent, bases, emitted.clone()),
            blocks,
            committee.codec(),
            1,
        )
        .await;
        actor.ordering = Some(Arc::new(Policy {
            merge,
            contexts: Arc::default(),
        }));
        let mut batch = PublicationBatch::new(1, 0);
        assert!(
            actor
                .open(HistoryLink { commitment, record }, &mut batch)
                .await
                .is_err()
        );
        assert!(actor.catalog.outputs.is_empty());
        assert!(batch.outputs.is_empty());
        assert_eq!(actor.state.emitted(), emitted);
    });
}

#[rstest]
#[case::matching_snapshot(Merge::LaneMajor, true)]
#[case::incompatible_snapshot(Merge::ReverseLanes, false)]
fn floor_resume_checks_the_snapshot_prefix_when_ordering_outputs(
    #[case] merge: Merge,
    #[case] compatible: bool,
) {
    deterministic::Runner::default().start(|context| async move {
        let committee = committee(176, 2, PathLimits::new(2, 1).unwrap());
        let genesis = committee.config.genesis();
        let epoch = genesis.epoch();
        let bases = genesis.tips().to_vec();
        let blocks = vec![chain(epoch, bases[0], 1), chain(epoch, bases[1], 2)];
        let floor_history = genesis_record(&committee);
        let emitted = vec![blocks[0][0].reference(), blocks[1][0].reference()];
        let proof = super::floor::anchored_lqc(
            &committee,
            1,
            floor_history.commitment::<Sha256>(),
            emitted.clone(),
            vec![Vec::new(), Vec::new()],
        );
        let current = checkpoint(
            epoch,
            genesis_history::<Sha256>(genesis),
            bases.clone(),
            bases,
        );
        let mut actor = actor(&context, current, blocks.clone(), committee.codec(), 1).await;
        actor.ordering = Some(Arc::new(Policy {
            merge,
            contexts: Arc::default(),
        }));
        actor
            .install_floor(Floor::new(
                proof,
                Arc::clone(&floor_history),
                emitted.clone(),
            ))
            .await
            .unwrap();
        let record = Arc::new(
            TipRecord::new(
                floor_history.commitment::<Sha256>(),
                vec![tip(&blocks[0]), tip(&blocks[1])],
                vec![Height::new(1), Height::new(1)],
            )
            .unwrap(),
        );
        let commitment = record.commitment::<Sha256>();
        let mut batch = PublicationBatch::new(1, 0);
        let result = actor
            .open(HistoryLink { commitment, record }, &mut batch)
            .await;
        if compatible {
            result.unwrap();
            actor.commit_pending(&mut batch).await.unwrap();
            actor.finish_commits().await.unwrap();
            assert_eq!(actor.catalog.outputs, vec![blocks[1][1].reference()]);
            assert_eq!(actor.catalog.checkpoint.committed(), OutputIndex::new(3));
        } else {
            assert!(matches!(
                result,
                Err(Error::Invalid("ordering policy changed a published prefix"))
            ));
            assert!(actor.catalog.outputs.is_empty());
            assert!(batch.outputs.is_empty());
            assert_eq!(actor.state.emitted(), emitted);
            assert_eq!(actor.catalog.checkpoint.committed(), OutputIndex::new(2));
        }
    });
}

#[rstest]
#[case::small_batches(17, false)]
#[case::larger_batches(31, false)]
#[case::partial_second_context_small_batches(17, true)]
#[case::partial_second_context_larger_batches(31, true)]
fn ordering_contexts_are_bounded_independently_of_storage_batches(
    #[case] batch_size: usize,
    #[case] partial: bool,
) {
    deterministic::Runner::default().start(|context| async move {
        let committee = committee(172, 2, PathLimits::new(2, 1).unwrap());
        let epoch = committee.config.epoch();
        let bases = vec![base(0, 0), base(1, 0)];
        let blocks = vec![chain(epoch, bases[0], 513), chain(epoch, bases[1], 513)];
        let parent = digest(b"bounded custom history", 0);
        let record =
            Arc::new(TipRecord::at_tips(parent, vec![tip(&blocks[0]), tip(&blocks[1])]).unwrap());
        let commitment = record.commitment::<Sha256>();
        let emitted = if partial {
            vec![blocks[0][511].reference(), blocks[1][512].reference()]
        } else {
            bases.clone()
        };
        let mut actor = actor(
            &context,
            checkpoint(epoch, parent, bases.clone(), emitted),
            blocks.clone(),
            committee.codec(),
            batch_size,
        )
        .await;
        let contexts = Arc::new(Mutex::new(Vec::new()));
        actor.ordering = Some(Arc::new(Policy {
            merge: Merge::ReverseLanes,
            contexts: Arc::clone(&contexts),
        }));
        commit_opening(&mut actor, HistoryLink { commitment, record }).await;
        let contexts = contexts.lock();
        assert_eq!(
            contexts
                .iter()
                .map(|context| context.prefixes.iter().map(Vec::len).sum::<usize>())
                .collect::<Vec<_>>(),
            vec![1024, 2]
        );
        assert_eq!(
            contexts[1]
                .base
                .iter()
                .map(|reference| reference.height().get())
                .collect::<Vec<_>>(),
            vec![512, 512]
        );
        let expected = blocks[1][..512]
            .iter()
            .chain(&blocks[0][..512])
            .chain(&blocks[1][512..])
            .chain(&blocks[0][512..])
            .map(|block| block.reference())
            .collect::<Vec<_>>();
        let published = if partial { 1025 } else { 0 };
        assert_eq!(actor.catalog.outputs, expected[published..]);
        assert_eq!(
            actor.fetcher.block_calls.load(Ordering::Relaxed),
            if partial { 1 } else { 1026 }
        );
        assert!(
            actor
                .catalog
                .batches
                .iter()
                .all(|count| *count <= batch_size)
        );
    });
}
