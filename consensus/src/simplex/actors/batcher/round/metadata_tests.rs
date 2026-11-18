//! Actual source-admission checks for opt-in unauthenticated vote metadata.
use super::*;
use crate::{
    simplex::{
        phase2::{
            Mode,
            metadata_probe::{Metadata, Vote as MetadataVote},
        },
        scheme::ed25519,
        types::{Finalize, Notarize},
    },
    types::{Epoch, Round, View},
};
use commonware_actor::Feedback;
use commonware_codec::Encode as _;
use commonware_cryptography::{
    Hasher as _, Sha256, certificate::mocks::Fixture, ed25519::PublicKey, sha256::Digest as D,
};
use commonware_parallel::Sequential;
use commonware_runtime::{Runner as _, deterministic};
use commonware_utils::{sync::Mutex, test_rng};

type S = ed25519::Scheme;
type Activity = ActivityWith<S, D, Metadata>;
type Blocks = Arc<Mutex<Vec<PublicKey>>>;
type Activities = Arc<Mutex<Vec<Activity>>>;
type TestRound = RoundWith<S, RecordingBlocker, D, RecordingReporter, Metadata>;

#[derive(Clone)]
struct RecordingBlocker(Blocks);
impl Blocker for RecordingBlocker {
    type PublicKey = PublicKey;
    fn block(&mut self, peer: PublicKey) -> Feedback {
        self.0.lock().push(peer);
        Feedback::Ok
    }
    fn blocked(&mut self) -> commonware_p2p::BlockedSubscription<PublicKey> {
        let (_, receiver) = commonware_utils::channel::ring::channel(commonware_utils::NZUsize!(1));
        receiver
    }
}
#[derive(Clone)]
struct RecordingReporter(Activities);
impl Reporter for RecordingReporter {
    type Activity = Activity;
    fn report(&mut self, activity: Activity) -> Feedback {
        self.0.lock().push(activity);
        Feedback::Ok
    }
}

fn new_round(f: &Fixture<S>) -> (TestRound, Blocks, Activities) {
    let blocks = Arc::new(Mutex::new(Vec::new()));
    let activities = Arc::new(Mutex::new(Vec::new()));
    let round = TestRound::new(
        Round::new(Epoch::new(3), View::new(7)),
        Arc::new(f.verifier.clone()),
        RecordingBlocker(blocks.clone()),
        RecordingReporter(activities.clone()),
        true,
    );
    (round, blocks, activities)
}

fn proposal() -> Proposal<D> {
    Proposal::new(
        Round::new(Epoch::new(3), View::new(7)),
        View::new(6),
        Sha256::hash(&[b"metadata vote proposal"]),
    )
}

fn vote(f: &Fixture<S>, owner: usize, proposal: Proposal<D>, hint: u8) -> MetadataVote<S, D> {
    MetadataVote {
        native: Finalize::sign(&f.schemes[owner], proposal).unwrap(),
        hint: D::from([hint; 32]),
    }
}

fn reported_finalizes(activities: &Activities) -> usize {
    activities
        .lock()
        .iter()
        .filter(|activity| matches!(activity, Activity::Finalize(_)))
        .count()
}

#[test]
fn metadata_hint_retransmission_retains_first_without_extra_credit() {
    deterministic::Runner::default().start(|_| async move {
        let mut rng = test_rng();
        for n in [4, 8, 9, 10, 13, 16, 64] {
            let f = ed25519::fixture(&mut rng, b"batcher_metadata_duplicate", n);
            let (mut round, blocks, activities) = new_round(&f);
            let proposal = proposal();
            round.set_leader(Participant::new(0));
            assert!(round.add_network(
                f.participants[0].clone(),
                VoteWith::Notarize(Notarize::sign(&f.schemes[0], proposal.clone()).unwrap()),
            ));

            let owner = n as usize - 1;
            let first = vote(&f, owner, proposal.clone(), 1);
            let mut alias = first.clone();
            alias.hint = D::from([2; 32]);
            assert_ne!(first, alias);
            assert!(<Metadata as Mode<S, D>>::equivalent_finalize(
                &first, &alias
            ));
            assert!(<Metadata as Mode<S, D>>::verify_finalize(
                &first,
                &mut rng,
                &f.verifier,
                &Sequential,
            ));
            assert!(<Metadata as Mode<S, D>>::verify_finalize(
                &alias,
                &mut rng,
                &f.verifier,
                &Sequential,
            ));
            let exact = first.encode();
            let sender = f.participants[owner].clone();
            assert!(round.add_network(sender.clone(), VoteWith::Finalize(first.clone())));
            assert!(!round.add_network(sender.clone(), VoteWith::Finalize(first)));
            assert!(!round.add_network(sender, VoteWith::Finalize(alias)));
            assert!(
                blocks.lock().is_empty(),
                "hint-only retry must not block n={n}"
            );
            assert_eq!(round.votes.len_finalizes(), 1);
            assert_eq!(reported_finalizes(&activities), 1);
            assert_eq!(
                round
                    .votes
                    .finalize(Participant::from_usize(owner))
                    .unwrap()
                    .encode(),
                exact
            );
            assert!(round.try_construct(&mut rng, &Sequential).await.is_none());

            let quorum = n as usize - (n as usize - 1) / 3;
            for owner in 0..quorum - 2 {
                assert!(round.add_network(
                    f.participants[owner].clone(),
                    VoteWith::Finalize(vote(&f, owner, proposal.clone(), owner as u8)),
                ));
            }
            assert!(round.try_construct(&mut rng, &Sequential).await.is_none());
            let last = quorum - 2;
            assert!(round.add_network(
                f.participants[last].clone(),
                VoteWith::Finalize(vote(&f, last, proposal.clone(), 99)),
            ));
            let batch = round.try_construct(&mut rng, &Sequential).await.unwrap();
            assert_eq!(batch.processed, quorum);
            assert!(batch.invalid.is_empty());
            let CertificateWith::Finalization(certificate) = batch.certificate.unwrap() else {
                panic!("expected finalization")
            };
            assert_eq!(certificate.certificate.signers.count(), quorum);
            assert!(certificate.verify(&mut rng, &f.verifier, &Sequential));
            assert_eq!(round.votes.len_finalizes() as usize, quorum);
            assert_eq!(reported_finalizes(&activities), quorum);
            assert_eq!(
                round
                    .votes
                    .finalize(Participant::from_usize(owner))
                    .unwrap()
                    .encode(),
                exact
            );
            assert!(blocks.lock().is_empty());
        }
    });
}

#[test]
fn metadata_duplicate_preserves_signed_conflict_and_sender_checks() {
    let mut rng = test_rng();
    let f = ed25519::fixture(&mut rng, b"batcher_metadata_conflict", 8);
    let (mut round, blocks, activities) = new_round(&f);
    let owner = 7;
    let sender = f.participants[owner].clone();
    let first = vote(&f, owner, proposal(), 1);
    let exact = first.encode();
    assert!(round.add_network(sender.clone(), VoteWith::Finalize(first.clone())));

    let mut different = proposal();
    different.payload = Sha256::hash(&[b"conflicting signed proposal"]);
    let conflict = vote(&f, owner, different, 2);
    assert!(!<Metadata as Mode<S, D>>::equivalent_finalize(
        &first, &conflict
    ));
    assert!(!round.add_network(sender.clone(), VoteWith::Finalize(conflict)));
    assert_eq!(&*blocks.lock(), &[sender]);
    let reports = activities.lock();
    let [
        Activity::Finalize(_),
        Activity::ConflictingFinalize(evidence),
    ] = &reports[..]
    else {
        panic!("signed conflict must be reported once")
    };
    assert!(evidence.verify(&mut rng, &f.verifier, &Sequential));
    drop(reports);

    let other_sender = f.participants[0].clone();
    assert!(!round.add_network(other_sender.clone(), VoteWith::Finalize(first)));
    assert_eq!(blocks.lock().last(), Some(&other_sender));
    assert_eq!(activities.lock().len(), 2);
    assert_eq!(round.votes.len_finalizes(), 1);
    assert_eq!(
        round
            .votes
            .finalize(Participant::new(owner as u32))
            .unwrap()
            .encode(),
        exact
    );
}

#[test]
fn metadata_duplicate_does_not_ignore_attestation_changes() {
    let mut rng = test_rng();
    let f = ed25519::fixture(&mut rng, b"batcher_metadata_signature", 8);
    let (mut round, blocks, activities) = new_round(&f);
    let first = vote(&f, 7, proposal(), 1);
    let mut invalid = first.clone();
    invalid.native.attestation = vote(&f, 6, proposal(), 1).native.attestation;
    invalid.native.attestation.signer = Participant::new(7);
    assert!(!<Metadata as Mode<S, D>>::conflicting_finalize_subjects(
        &first, &invalid
    ));
    assert!(!<Metadata as Mode<S, D>>::equivalent_finalize(
        &first, &invalid
    ));
    assert!(!<Metadata as Mode<S, D>>::verify_finalize(
        &invalid,
        &mut rng,
        &f.verifier,
        &Sequential,
    ));
    assert!(!<Plain as Mode<S, D>>::equivalent_finalize(
        &first.native,
        &invalid.native
    ));
    let exact = first.encode();
    assert!(round.add_network(f.participants[7].clone(), VoteWith::Finalize(first)));
    assert!(!round.add_network(f.participants[7].clone(), VoteWith::Finalize(invalid)));
    assert_eq!(&*blocks.lock(), &[f.participants[7].clone()]);
    assert_eq!(activities.lock().len(), 1);
    assert_eq!(round.votes.len_finalizes(), 1);
    assert_eq!(
        round.votes.finalize(Participant::new(7)).unwrap().encode(),
        exact
    );
}
