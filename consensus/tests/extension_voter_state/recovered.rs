//! Recovered interpretations authorize parent binding, never native finality.
use super::*;
use commonware_codec::{Decode as _, Encode as _};
use commonware_consensus::{
    Viewable as _,
    simplex::{extension::certificate::Recovered, types::Artifact},
};
use commonware_cryptography::certificate::Verifier as _;
use commonware_runtime::{ReadOptions, buffer::paged::CacheRef};
use commonware_storage::journal::segmented::variable::{Config as JournalConfig, Journal};
use commonware_utils::{NZU16, NZUsize};
type S = ed25519::Scheme;
type A = ArtifactWith<S, Digest, Extended>;
fn fixture() -> Fixture<S> {
    ed25519::fixture(
        &mut TestRng::new(101),
        b"_COMMONWARE_CONSENSUS_RECOVERED_PARENT_TEST",
        6,
    )
}
fn recovered(f: &Fixture<S>, mut s: Statement<Digest>, ballot: u64) -> Recovered<S, Digest> {
    s.ballot = Round::new(s.proposal.round.epoch(), View::new(ballot));
    let votes: Vec<_> = f
        .schemes
        .iter()
        .take(5)
        .map(|signer| Vote::sign(signer, s.clone()).unwrap())
        .collect();
    Recovered::new(
        Certificate::from_votes(
            &mut TestRng::new(12),
            &f.verifier,
            non_empty![@votes],
            &Sequential,
        )
        .unwrap(),
    )
    .unwrap()
}
fn ready(context: deterministic::Context, f: &Fixture<S>) -> State<S> {
    let mut s = state(context, f.schemes[0].clone(), 1);
    for v in 1..=2 {
        s.add_notarization(notarization(f, v));
        s.certified(View::new(v), true).unwrap();
    }
    s
}
#[test]
fn recovered_parent_unblocks_child_without_advancing_view_or_finality() {
    deterministic::Runner::default().start(|context| async move {
        let f = fixture();
        let mut s = ready(context.child("voter"), &f);
        let first = subject(1, Digest::from([3; 32]));
        let child = subject(2, first.value::<Sha256>());
        // A conflicting local first-round decision stays immutable, even when
        // the quorum recovers another interpretation.
        let mut local = first.clone();
        local.extension = Digest::from([77; 32]);
        let original_vote = s
            .construct_finalize_with(View::new(1), local.clone())
            .unwrap();
        assert!(
            s.construct_finalize_with(View::new(2), child.clone())
                .is_none()
        );
        let before = s.current_view();
        let cert = recovered(&f, first.clone(), 20);
        assert_eq!(s.stage_recovered(cert.clone(), |_| false), None);
        assert!(s.recovered_interpretation(View::new(1)).is_none());
        assert_eq!(s.stage_recovered(cert.clone(), |_| true), Some(true));
        assert_eq!(
            s.current_view(),
            before,
            "a quorum's later ballot is not a local view-change certificate"
        );
        assert_eq!(s.last_finalized(), View::zero());
        assert!(
            s.construct_finalize_with(View::new(1), first.clone())
                .is_none()
        );
        assert_eq!(original_vote.vote().statement, local);
        assert_eq!(
            s.stage_recovered(recovered(&f, first, 21), |_| true),
            Some(false)
        );
        assert_eq!(
            s.recovered_interpretation(View::new(1)),
            Some(&cert),
            "retain original full witness on same-value retries"
        );
        assert_eq!(
            s.stage_recovered(recovered(&f, local.clone(), 22), |_| true),
            None
        );
        assert!(
            !s.add_finalization(certificate(&f, local)).0,
            "even authenticated conflicting finality cannot reinterpret the slot"
        );
        assert_eq!(s.last_finalized(), View::zero());
        let mut wrong = child.clone();
        wrong.parent = Digest::from([90; 32]);
        assert!(s.construct_finalize_with(View::new(2), wrong).is_none());
        let vote = s
            .construct_finalize_with(View::new(2), child.clone())
            .unwrap();
        assert_eq!(vote.vote().statement, child);
        assert_eq!(
            s.last_finalized(),
            View::zero(),
            "a local child vote does not finalize anything"
        );
        assert!(s.add_finalization(certificate(&f, child)).0);
        assert_eq!(s.last_finalized(), View::new(2));
        assert_eq!(s.stage_recovered(cert, |_| true), Some(false));
    });
}
#[test]
fn recovered_certificate_rejects_wrong_context_missing_native_ancestry_and_forgery_before_evidence()
{
    deterministic::Runner::default().start(|context| async move {
        let f = fixture();
        let first = subject(1, Digest::from([3; 32]));
        let mut s = ready(context.child("ready"), &f);
        for field in 0..4 {
            let mut invalid = first.clone();
            match field {
                0 => invalid.domain = Digest::from([99; 32]),
                1 => invalid.parent = Digest::from([99; 32]),
                2 => invalid.proposal.payload = Digest::from([99; 32]),
                _ => invalid.proposal.round = Round::new(Epoch::new(2), View::new(1)),
            }
            assert_eq!(
                s.stage_recovered(recovered(&f, invalid, 2), |_| panic!(
                    "invalid native witness reached application"
                )),
                None
            );
        }
        let mut forged = recovered(&f, first.clone(), 2).certificate().clone();
        forged.statement.extension = Digest::from([99; 32]);
        assert_eq!(
            s.stage_recovered(Recovered::new(forged).unwrap(), |_| panic!(
                "forged QC reached application"
            )),
            None
        );
        let mut empty = state(context.child("empty"), f.schemes[0].clone(), 1);
        assert_eq!(
            empty.stage_recovered(recovered(&f, first.clone(), 2), |_| true),
            None
        );
        empty.add_notarization(notarization(&f, 1));
        assert_eq!(
            empty.stage_recovered(recovered(&f, first.clone(), 2), |_| true),
            None,
            "local certification required"
        );
        let child = subject(2, first.value::<Sha256>());
        assert_eq!(
            s.stage_recovered(recovered(&f, child.clone(), 3), |_| true),
            None,
            "parent interpretation absent"
        );
        assert_eq!(
            s.stage_recovered(recovered(&f, first, 2), |_| true),
            Some(true)
        );
        assert_eq!(
            s.stage_recovered(recovered(&f, child, 3), |_| true),
            Some(true)
        );
        assert_eq!(s.last_finalized(), View::zero());
    });
}
#[test]
fn native_journal_restores_recovered_parent_before_dependent_child_vote() {
    let f = fixture();
    let write_f = f.clone();
    let (_, checkpoint) =
        deterministic::Runner::default().start_and_recover(move |context| async move {
            let first = subject(1, Digest::from([3; 32]));
            let records = vec![
                A::Notarization(notarization(&write_f, 1)),
                A::Certification(proposal(1).round, true),
                A::Recovered(recovered(&write_f, first, 2)),
                A::Notarization(notarization(&write_f, 2)),
                A::Certification(proposal(2).round, true),
            ];
            let mut journal = Journal::<_, A>::init(
                context.child("wal"),
                JournalConfig {
                    partition: "recovered-parent".into(),
                    compression: None,
                    codec_config: write_f.verifier.certificate_codec_config(),
                    page_cache: CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(8)),
                    write_buffer: NZUsize!(1024),
                },
            )
            .await
            .unwrap();
            for record in records {
                let bytes = record.encode();
                assert_eq!(
                    A::decode_cfg(bytes.clone(), &write_f.verifier.certificate_codec_config())
                        .unwrap()
                        .encode(),
                    bytes
                );
                if matches!(record, A::Recovered(_)) {
                    assert_eq!(bytes[0], 8);
                    assert!(
                        Artifact::<S, Digest>::decode_cfg(
                            bytes.clone(),
                            &write_f.verifier.certificate_codec_config()
                        )
                        .is_err()
                    );
                    for end in 0..bytes.len() {
                        assert!(
                            A::decode_cfg(
                                bytes.slice(..end),
                                &write_f.verifier.certificate_codec_config()
                            )
                            .is_err()
                        );
                    }
                }
                let section = record.view().get();
                journal = journal.append(section, &record).await.unwrap().0;
                journal = journal.sync(section).await.unwrap();
            }
        });
    deterministic::Runner::from(checkpoint).start(move |context| async move {
        let journal = Journal::<_, A>::init(
            context.child("wal"),
            JournalConfig {
                partition: "recovered-parent".into(),
                compression: None,
                codec_config: f.verifier.certificate_codec_config(),
                page_cache: CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(8)),
                write_buffer: NZUsize!(1024),
            },
        )
        .await
        .unwrap();
        let mut reader = journal
            .replay(0, 0, NZUsize!(1024), ReadOptions::DONT_CACHE)
            .await
            .unwrap();
        let mut s = state(context.child("restored"), f.schemes[0].clone(), 1);
        let mut count = 0;
        while let Some(record) = reader.next().await {
            let record = record.unwrap().3;
            s.replay(&record);
            match record {
                A::Notarization(n) => {
                    s.add_notarization(n);
                }
                A::Certification(r, b) => {
                    s.certified(r.view(), b).unwrap();
                }
                _ => {}
            }
            count += 1;
        }
        drop(reader.finish().unwrap());
        assert_eq!(count, 5);
        assert_eq!(s.last_finalized(), View::zero());
        let first = subject(1, Digest::from([3; 32]));
        assert!(
            s.construct_finalize_with(View::new(2), subject(2, first.value::<Sha256>()))
                .is_some()
        );
    });
}

#[test]
fn recovered_interpretation_does_not_force_native_ancestry_to_include_skipped_proposal() {
    deterministic::Runner::default().start(|context| async move {
        let f = fixture();
        let mut s = state(context, f.schemes[0].clone(), 1);
        s.add_notarization(notarization(&f, 1));
        s.certified(View::new(1), true).unwrap();
        let first = subject(1, Digest::from([3; 32]));
        assert_eq!(
            s.stage_recovered(recovered(&f, first, 2), |_| true),
            Some(true)
        );
        let votes: Vec<_> = f
            .schemes
            .iter()
            .take(5)
            .map(|signer| Nullify::sign::<Digest>(signer, proposal(1).round).unwrap())
            .collect();
        let nullification = commonware_consensus::simplex::types::Nullification::from_nullifies(
            &f.verifier,
            non_empty![@&votes],
            &Sequential,
        )
        .unwrap();
        s.add_nullification(nullification);
        let mut skip = proposal(2);
        skip.parent = View::zero();
        let votes: Vec<_> = f
            .schemes
            .iter()
            .take(5)
            .map(|signer| Notarize::sign(signer, skip.clone()).unwrap())
            .collect();
        s.add_notarization(
            Notarization::from_notarizes(&f.verifier, non_empty![@&votes], &Sequential).unwrap(),
        );
        s.certified(View::new(2), true).unwrap();
        let mut second = subject(2, Digest::from([3; 32]));
        second.proposal = skip;
        assert!(
            s.construct_finalize_with(View::new(2), second.clone())
                .is_some()
        );
        assert!(s.add_finalization(certificate(&f, second)).0);
        assert_eq!(s.last_finalized(), View::new(2));
        assert!(
            s.finalization(View::new(1)).is_none(),
            "the retained interpretation did not finalize excluded input"
        );
    });
}
