use super::*;
use commonware_codec::{Decode as _, Encode as _};
use commonware_consensus::{
    Viewable as _,
    simplex::{
        extension::recovery::{Proof, Status},
        phase2::recovery::Record,
        types::Artifact,
    },
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
        b"_COMMONWARE_CONSENSUS_RECOVERY_JOURNAL_TEST",
        6,
    )
}
const fn ballot(v: u64) -> Round {
    Round::new(Epoch::new(1), View::new(v))
}
fn original(i: usize) -> Statement<Digest> {
    let mut s = subject(1, Digest::from([3; 32]));
    if i >= 3 {
        s.extension = Digest::from([9; 32]);
    }
    s
}
fn ready(context: deterministic::Context, f: &Fixture<S>, i: usize) -> State<S> {
    let mut s = state(context, f.schemes[i].clone(), 1);
    s.add_notarization(notarization(f, 1));
    s.certified(View::new(1), true).unwrap();
    s
}
fn proof(
    f: &Fixture<S>,
    target: &Statement<Digest>,
    ids: impl Iterator<Item = usize>,
) -> Proof<S, Digest> {
    Proof {
        statuses: ids
            .map(|i| {
                Status::sign(
                    &f.schemes[i],
                    commonware_consensus::simplex::extension::recovery::Promise {
                        proposal: target.proposal.clone(),
                        domain: target.domain,
                        ballot: target.ballot,
                        accepted: Some((ballot(1), original(i).value::<Sha256>())),
                    },
                )
                .unwrap()
            })
            .collect(),
    }
}
#[test]
fn native_state_fences_original_and_conflicting_later_votes_without_granting_finality() {
    deterministic::Runner::default().start(|context| async move {
        let f = fixture();
        let mut x = original(0);
        x.ballot = ballot(2);
        let checked = proof(&f, &x, 0..5);
        let mut y = original(5);
        y.ballot = ballot(2);
        let other = proof(&f, &y, 1..6);
        for i in 0..6 {
            let mut s = ready(context.child("node").with_attribute("index", i), &f, i);
            s.construct_finalize_with(View::new(1), original(i))
                .unwrap();
            assert!(
                s.construct_recovery_promise(View::new(1), ballot(3))
                    .is_err(),
                "unknown future ballot"
            );
            let frozen = s
                .construct_recovery_promise(View::new(1), ballot(2))
                .unwrap();
            assert!(
                s.construct_finalize_with(View::new(1), original(i))
                    .is_none()
            );
            assert!(
                s.construct_recovery_accept(y.clone(), &checked, &Sequential)
                    .is_err(),
                "forced X cannot be replaced"
            );
            let mut forged = proof(&f, &x, 0..5);
            forged.statuses[0].promise.accepted = None;
            assert!(
                s.construct_recovery_accept(x.clone(), &forged, &Sequential)
                    .is_err()
            );
            s.construct_recovery_accept(x.clone(), &checked, &Sequential)
                .unwrap();
            assert!(
                s.construct_recovery_accept(y.clone(), &other, &Sequential)
                    .is_err(),
                "different valid proof cannot change same-ballot vote"
            );
            assert_eq!(
                s.construct_recovery_promise(View::new(1), ballot(2))
                    .unwrap()
                    .encode(),
                frozen.encode()
            );
            assert_eq!(
                s.recovery_promise(View::new(1)).unwrap().accepted,
                Some((ballot(1), original(i).value::<Sha256>()))
            );
            assert_eq!(s.last_finalized(), View::zero());
            s.add_notarization(notarization(&f, 2));
            assert_eq!(s.current_view(), View::new(2));
            assert!(
                s.construct_recovery_promise(View::new(1), ballot(3))
                    .is_err(),
                "notarization alone does not admit the next ballot"
            );
            s.certified(View::new(2), true).unwrap();
            assert_eq!(s.current_view(), View::new(3));
            s.construct_recovery_promise(View::new(1), ballot(3))
                .unwrap();
            assert_eq!(
                s.recovery_promise(View::new(1)).unwrap().accepted,
                Some((ballot(2), x.value::<Sha256>()))
            );
            assert!(
                s.construct_recovery_accept(x.clone(), &checked, &Sequential)
                    .is_err(),
                "stale ballot"
            );
        }
        // Even a validator that never made an original final vote is fenced.
        let mut s = ready(context.child("no_original_vote"), &f, 0);
        s.construct_recovery_promise(View::new(1), ballot(2))
            .unwrap();
        assert!(
            s.construct_finalize_with(View::new(1), original(0))
                .is_none()
        );
    });
}
#[test]
fn real_native_journal_restart_restores_promise_and_acceptance_boundaries() {
    for after_accept in [false, true] {
        let f = fixture();
        let writer_fixture = f.clone();
        let (_, checkpoint) =
            deterministic::Runner::default().start_and_recover(move |context| async move {
                let f = writer_fixture;
                let mut s = ready(context.child("voter"), &f, 5);
                let vote = s
                    .construct_finalize_with(View::new(1), original(5))
                    .unwrap();
                let promise = s
                    .construct_recovery_promise(View::new(1), ballot(2))
                    .unwrap();
                let mut x = original(0);
                x.ballot = ballot(2);
                let checked = proof(&f, &x, 0..5);
                let acceptance = s
                    .construct_recovery_accept(x, &checked, &Sequential)
                    .unwrap();
                let mut records = vec![
                    A::Notarization(notarization(&f, 1)),
                    A::Certification(ballot(1), true),
                    A::Finalize(vote),
                    promise,
                ];
                if after_accept {
                    records.push(acceptance);
                }
                let mut journal = Journal::<_, A>::init(
                    context.child("wal"),
                    JournalConfig {
                        partition: "native-recovery-staging".into(),
                        compression: None,
                        codec_config: f.verifier.certificate_codec_config(),
                        page_cache: CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(8)),
                        write_buffer: NZUsize!(1024),
                    },
                )
                .await
                .unwrap();
                for record in records {
                    let bytes = record.encode();
                    assert_eq!(
                        A::decode_cfg(bytes.clone(), &f.verifier.certificate_codec_config())
                            .unwrap()
                            .encode(),
                        bytes
                    );
                    if matches!(record, A::Recovery(_)) {
                        assert!(
                            Artifact::<S, Digest>::decode_cfg(
                                bytes.clone(),
                                &f.verifier.certificate_codec_config()
                            )
                            .is_err()
                        );
                        for end in 0..bytes.len() {
                            assert!(
                                A::decode_cfg(
                                    bytes.slice(..end),
                                    &f.verifier.certificate_codec_config()
                                )
                                .is_err()
                            );
                        }
                    }
                    journal = journal
                        .append(record.view().get(), &record)
                        .await
                        .unwrap()
                        .0;
                    journal = journal.sync(1).await.unwrap();
                }
            });
        deterministic::Runner::from(checkpoint).start(move |context| async move {
            let journal = Journal::<_, A>::init(
                context.child("wal"),
                JournalConfig {
                    partition: "native-recovery-staging".into(),
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
            let mut s = state(context.child("restored"), f.schemes[5].clone(), 1);
            let mut count = 0;
            while let Some(record) = reader.next().await {
                let record = record.unwrap().3;
                if let A::Finalize(v) = &record {
                    assert!(
                        v.vote()
                            .verify(&mut TestRng::new(1), &f.verifier, &Sequential)
                    );
                }
                s.replay(&record);
                // Mirror the native actor's epoch-level replay side effects;
                // State::replay deliberately restores local fences without advancing views.
                match &record {
                    A::Notarization(n) => {
                        s.add_notarization(n.clone());
                    }
                    A::Certification(round, success) => {
                        s.certified(round.view(), *success).unwrap();
                    }
                    _ => {}
                }
                count += 1;
            }
            drop(reader.finish().unwrap());
            assert_eq!(count, if after_accept { 5 } else { 4 });
            assert_eq!(s.last_finalized(), View::zero());
            assert!(
                s.construct_finalize_with(View::new(1), original(5))
                    .is_none()
            );
            assert_eq!(
                s.recovery_promise(View::new(1)).unwrap().accepted,
                Some((ballot(1), original(5).value::<Sha256>()))
            );
            s.add_notarization(notarization(&f, 2));
            assert_eq!(s.current_view(), View::new(2));
            assert!(
                s.construct_recovery_promise(View::new(1), ballot(3))
                    .is_err(),
                "notarization alone does not admit the next ballot"
            );
            s.certified(View::new(2), true).unwrap();
            assert_eq!(s.current_view(), View::new(3));
            s.construct_recovery_promise(View::new(1), ballot(3))
                .unwrap();
            let expected = if after_accept {
                (ballot(2), original(0).value::<Sha256>())
            } else {
                (ballot(1), original(5).value::<Sha256>())
            };
            assert_eq!(
                s.recovery_promise(View::new(1)).unwrap().accepted,
                Some(expected)
            );
        });
    }
}
#[test]
fn forged_frozen_acceptance_and_foreign_proposal_fail_closed() {
    deterministic::Runner::default().start(|context| async move {
        let f = fixture();
        let mut s = ready(context.child("voter"), &f, 5);
        s.construct_finalize_with(View::new(1), original(5))
            .unwrap();
        let record = Record::Promise {
            proposal: proposal(1),
            domain: Digest::from([2; 32]),
            ballot: ballot(2),
            accepted: Some(original(0)),
        };
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(
                || s.replay(&A::Recovery(record))
            ))
            .is_err()
        );
        let mut s = ready(context.child("foreign"), &f, 0);
        let mut foreign = proposal(1);
        foreign.payload = Digest::from([55; 32]);
        let record = Record::Promise {
            proposal: foreign,
            domain: Digest::from([2; 32]),
            ballot: ballot(2),
            accepted: None,
        };
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(
                || s.replay(&A::Recovery(record))
            ))
            .is_err()
        );
    });
}

#[test]
fn signed_requests_enforce_native_leader_timeout_and_application_evidence() {
    use commonware_consensus::simplex::extension::request::{Command, Request};
    use commonware_runtime::Clock as _;
    deterministic::Runner::default().start(|context| async move {
        let f = fixture();
        let mut s = ready(context.child("request"), &f, 0);
        s.construct_finalize_with(View::new(1), original(0))
            .unwrap();
        let leader = s.leader_index(View::new(2)).unwrap();
        let scheme = &f.schemes[usize::from(leader)];
        let command = Command::Promise {
            proposal: proposal(1),
            domain: original(0).domain,
            ballot: ballot(2),
        };
        let request = Request::sign(scheme, command.clone(), None).unwrap();
        assert!(
            s.stage_authenticated_recovery(&request, |_| panic!(
                "promise has no application subject"
            ))
            .is_err(),
            "deadline not elapsed"
        );
        assert!(s.recovery_promise(View::new(1)).is_none());
        context.sleep(Duration::from_secs(2)).await;
        let wrong =
            Request::sign(&f.schemes[(usize::from(leader) + 1) % 6], command, None).unwrap();
        assert!(
            s.stage_authenticated_recovery(&wrong, |_| panic!(
                "unverified leader cannot invoke application"
            ))
            .is_err()
        );
        let bytes = request.encode();
        let decoded = Request::<S, Digest>::decode_cfg(bytes.clone(), &6).unwrap();
        assert!(decoded.verify(&mut TestRng::new(22), &f.verifier, &Sequential));
        for end in 0..bytes.len() {
            assert!(Request::<S, Digest>::decode_cfg(bytes.slice(..end), &6).is_err());
        }
        let mut forged = decoded.clone();
        if let Command::Promise { domain, .. } = &mut forged.command {
            *domain = Digest::from([77; 32]);
        }
        assert!(!forged.verify(&mut TestRng::new(22), &f.verifier, &Sequential));
        s.stage_authenticated_recovery(&decoded, |_| panic!("promise has no application subject"))
            .unwrap();
        let mut x = original(0);
        x.ballot = ballot(2);
        let request = Request::sign(
            scheme,
            Command::Accept(x.clone()),
            Some(proof(&f, &x, 0..5)),
        )
        .unwrap();
        let mut forged = request.clone();
        forged.proof.as_mut().unwrap().statuses[0].promise.accepted = None;
        assert!(
            s.stage_authenticated_recovery(&forged, |_| panic!(
                "unverified proof bytes cannot invoke application"
            ))
            .is_err()
        );
        let mut forged_proof = request.proof.clone().unwrap();
        forged_proof.statuses[0].promise.accepted = None;
        let leader_signed_forgery =
            Request::sign(scheme, Command::Accept(x.clone()), Some(forged_proof)).unwrap();
        assert!(
            s.stage_authenticated_recovery(&leader_signed_forgery, |_| panic!(
                "invalid original statuses cannot invoke application"
            ))
            .is_err()
        );
        assert!(
            s.stage_authenticated_recovery(&request, |_| false).is_err(),
            "missing application evidence"
        );
        let record = s
            .stage_authenticated_recovery(&request, |subject| subject == &x)
            .unwrap();
        assert_eq!(record, Record::Accept(x));
        assert_eq!(s.last_finalized(), View::zero());
    });
}
