//! Native coordinator planning retains authority, original evidence and ballot fences.
use super::*;
use commonware_consensus::simplex::{
    elector::Elector as _,
    extension::{
        certificate::Recovered,
        recovery::{Promise, Status},
        report,
        request::{Command, Query, Request, Response},
    },
    phase2::voting::Participation,
};
use commonware_cryptography::certificate::Scheme as _;
use commonware_runtime::Clock as _;
type S = ed25519::Scheme;
#[derive(Default)]
struct Evidence {
    candidate: Option<Statement<Digest>>,
    calls: usize,
}
impl Participation<S, Digest, Extended> for Evidence {
    fn notarize(&mut self, v: Notarize<S, Digest>) -> report::Notarize<S, Digest> {
        report::Notarize::new(v, None).unwrap()
    }
    fn final_subject(&mut self, _: &Proposal<Digest>) -> Option<Statement<Digest>> {
        self.calls += 1;
        self.candidate.clone()
    }
    fn accepts_finalization(&mut self, _: &Finalization<S, Digest>) -> bool {
        false
    }
    fn accepts_replay(&mut self, _: &ArtifactWith<S, Digest, Extended>) -> bool {
        false
    }
    fn accepts_recovery(&mut self, _: &Statement<Digest>) -> bool {
        self.calls += 1;
        true
    }
    fn accepts_recovered(&mut self, _: &Recovered<S, Digest>) -> bool {
        false
    }
    fn prune(&mut self, _: View) {}
}
fn fixture() -> Fixture<S> {
    ed25519::fixture(
        &mut TestRng::new(101),
        b"_COMMONWARE_CONSENSUS_RECOVERY_PLANNING_TEST",
        6,
    )
}
fn leader(f: &Fixture<S>, view: u64) -> usize {
    let elector: RoundRobinElector<S> =
        RoundRobin::<Sha256>::default().build(f.schemes[0].participants());
    usize::from(elector.elect(Round::new(Epoch::new(1), View::new(view)), None))
}
fn x() -> Statement<Digest> {
    subject(1, Digest::from([3; 32]))
}
fn y() -> Statement<Digest> {
    let mut s = x();
    s.extension = Digest::from([99; 32]);
    s
}
fn responses(
    f: &Fixture<S>,
    p: &Request<S, Digest>,
    ids: std::ops::Range<usize>,
) -> Vec<Response<S, Digest>> {
    ids.map(|i| {
        let accepted = if i < 3 { x() } else { y() };
        Response::Status {
            status: Status::sign(
                &f.schemes[i],
                Promise {
                    proposal: p.command.proposal().clone(),
                    domain: p.command.domain(),
                    ballot: p.command.ballot(),
                    accepted: Some((accepted.ballot, accepted.value::<Sha256>())),
                },
            )
            .unwrap(),
            accepted: Some(accepted),
        }
    })
    .collect()
}
#[test]
fn discovery_requires_native_leader_certification_deadline_and_unresolved_input() {
    deterministic::Runner::default().start(|context| async move {
        let f = fixture();
        let me = leader(&f, 2);
        let mut s = state(context.child("leader"), f.schemes[me].clone(), 1);
        let mut other = state(
            context.child("follower"),
            f.schemes[(me + 1) % 6].clone(),
            1,
        );
        let mut evidence = Evidence::default();
        assert!(
            s.prepare_recovery_request(&Query::Discover, &mut evidence)
                .is_err()
        );
        s.add_notarization(notarization(&f, 1));
        other.add_notarization(notarization(&f, 1));
        assert!(
            s.prepare_recovery_request(&Query::Discover, &mut evidence)
                .is_err()
        );
        s.certified(View::new(1), true).unwrap();
        other.certified(View::new(1), true).unwrap();
        assert!(
            s.prepare_recovery_request(&Query::Discover, &mut evidence)
                .is_err()
        );
        context.sleep(Duration::from_millis(1100)).await;
        assert!(
            other
                .prepare_recovery_request(&Query::Discover, &mut evidence)
                .is_err()
        );
        let p = s
            .prepare_recovery_request(&Query::Discover, &mut evidence)
            .unwrap();
        assert_eq!(p.command.proposal(), &proposal(1));
        assert_eq!(p.command.ballot().view(), View::new(2));
        assert!(p.verify(&mut TestRng::new(17), &f.verifier, &Sequential));
        assert!(
            s.recovery_promise(View::new(1)).is_none(),
            "planning cannot accept/fence locally"
        );
        assert_eq!(s.last_finalized(), View::zero());
        assert_eq!(evidence.calls, 0);
        s.add_finalization(certificate(&f, x()));
        assert!(
            s.prepare_recovery_request(&Query::Discover, &mut evidence)
                .is_err()
        );
    });
}
#[test]
fn accept_planning_authenticates_original_quorum_preimages_before_application() {
    deterministic::Runner::default().start(|context| async move {
        let f = fixture();
        let me = leader(&f, 2);
        let mut s = state(context.child("leader"), f.schemes[me].clone(), 1);
        s.add_notarization(notarization(&f, 1));
        s.certified(View::new(1), true).unwrap();
        context.sleep(Duration::from_millis(1100)).await;
        let mut evidence = Evidence {
            candidate: Some(y()),
            calls: 0,
        };
        let p = s
            .prepare_recovery_request(&Query::Discover, &mut evidence)
            .unwrap();
        let valid = Query::Accept {
            promise: p.clone(),
            responses: responses(&f, &p, 0..5),
        };
        assert!(
            s.prepare_recovery_request(&valid, &mut evidence).is_err(),
            "own promise is required before accepting"
        );
        s.stage_authenticated_recovery(&p, |_| unreachable!())
            .unwrap();
        for kind in 0..6 {
            let mut q = valid.clone();
            let Query::Accept { promise, responses } = &mut q else {
                unreachable!()
            };
            match kind {
                0 => {
                    responses.pop();
                }
                1 => {
                    responses[1] = responses[0].clone();
                }
                2 => {
                    if let Response::Status { accepted, .. } = &mut responses[0] {
                        *accepted = Some(y());
                    }
                }
                3 => {
                    if let Response::Status { status, .. } = &mut responses[0] {
                        status.promise.ballot = Round::new(Epoch::new(1), View::new(3));
                    }
                }
                4 => {
                    *promise =
                        Request::sign(&f.schemes[(me + 1) % 6], p.command.clone(), None).unwrap();
                }
                _ => {
                    if let Response::Status { status, accepted } = &mut responses[0] {
                        status.promise.accepted = None;
                        *accepted = None;
                    }
                }
            }
            evidence.calls = 0;
            assert!(s.prepare_recovery_request(&q, &mut evidence).is_err());
            assert_eq!(
                evidence.calls, 0,
                "invalid peer proof reached application policy"
            );
        }
        let accepted = s.prepare_recovery_request(&valid, &mut evidence).unwrap();
        let Command::Accept(chosen) = &accepted.command else {
            unreachable!()
        };
        assert_eq!(
            chosen.extension,
            x().extension,
            "quorum forces X despite local preference Y"
        );
        assert_eq!(chosen.ballot, p.command.ballot());
        assert_eq!(
            s.recovery_promise(View::new(1)).unwrap().accepted,
            None,
            "query did not stage acceptance"
        );
        assert!(s.stage_authenticated_recovery(&accepted, |_| true).is_ok());
        let contrary = Query::Accept {
            promise: p.clone(),
            responses: responses(&f, &p, 1..6),
        };
        assert!(
            s.prepare_recovery_request(&contrary, &mut evidence)
                .is_err(),
            "cannot propose conflicting value in own accepted ballot"
        );
    });
}
#[test]
fn selected_recovery_ballot_survives_native_view_advancement() {
    deterministic::Runner::default().start(|context| async move {
        let f = fixture();
        let me = leader(&f, 2);
        let mut s = state(context.child("leader"), f.schemes[me].clone(), 1);
        s.add_notarization(notarization(&f, 1));
        s.certified(View::new(1), true).unwrap();
        context.sleep(Duration::from_millis(1100)).await;
        let mut evidence = Evidence::default();
        let p = s
            .prepare_recovery_request(&Query::Discover, &mut evidence)
            .unwrap();
        s.stage_authenticated_recovery(&p, |_| unreachable!())
            .unwrap();
        s.add_notarization(notarization(&f, 2));
        s.certified(View::new(2), true).unwrap();
        assert_eq!(s.current_view(), View::new(3));
        let a = s
            .prepare_recovery_request(
                &Query::Accept {
                    promise: p.clone(),
                    responses: responses(&f, &p, 0..5),
                },
                &mut evidence,
            )
            .unwrap();
        assert_eq!(a.command.ballot().view(), View::new(2));
        assert!(s.stage_authenticated_recovery(&a, |_| true).is_ok());
        assert_eq!(s.current_view(), View::new(3));
        assert_eq!(s.last_finalized(), View::zero());
        let mut unknown = p;
        unknown.command = Command::Promise {
            proposal: proposal(1),
            domain: x().domain,
            ballot: Round::new(Epoch::new(1), View::new(99)),
        };
        assert!(
            s.prepare_recovery_request(
                &Query::Accept {
                    responses: responses(&f, &unknown, 0..5),
                    promise: unknown
                },
                &mut evidence
            )
            .is_err()
        );
    });
}

#[test]
fn unforced_retry_preserves_own_accepted_value_and_bounds_query_material() {
    deterministic::Runner::default().start(|context| async move {
        let f = fixture();
        let mut s = state(context.child("leader"), f.schemes[leader(&f, 2)].clone(), 1);
        s.add_notarization(notarization(&f, 1));
        s.certified(View::new(1), true).unwrap();
        context.sleep(Duration::from_millis(1100)).await;
        let mut evidence = Evidence {
            candidate: Some(y()),
            calls: 0,
        };
        let p = s
            .prepare_recovery_request(&Query::Discover, &mut evidence)
            .unwrap();
        s.stage_authenticated_recovery(&p, |_| unreachable!())
            .unwrap();
        let empty = f
            .schemes
            .iter()
            .take(5)
            .map(|scheme| Response::Status {
                status: Status::sign(
                    scheme,
                    Promise {
                        proposal: p.command.proposal().clone(),
                        domain: p.command.domain(),
                        ballot: p.command.ballot(),
                        accepted: None,
                    },
                )
                .unwrap(),
                accepted: None,
            })
            .collect::<Vec<_>>();
        let query = Query::Accept {
            promise: p.clone(),
            responses: empty.clone(),
        };
        let a = s.prepare_recovery_request(&query, &mut evidence).unwrap();
        assert_eq!(a.command.subject().unwrap().extension, y().extension);
        s.stage_authenticated_recovery(&a, |_| true).unwrap();
        evidence.candidate = Some(x());
        evidence.calls = 0;
        let retry = s.prepare_recovery_request(&query, &mut evidence).unwrap();
        assert_eq!(retry.command.subject(), a.command.subject());
        assert_eq!(
            evidence.calls, 1,
            "only check retained material; do not select a different candidate"
        );
        let oversized = Query::Accept {
            promise: p,
            responses: vec![empty[0].clone(); 4097],
        };
        assert!(!oversized.bounded());
        evidence.calls = 0;
        assert!(
            s.prepare_recovery_request(&oversized, &mut evidence)
                .is_err()
        );
        assert_eq!(evidence.calls, 0);
    });
}
