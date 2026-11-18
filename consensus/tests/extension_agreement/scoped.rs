//! Public-only verification retains full origins, policy, carrier and custody checks.
use super::*;
use commonware_consensus::simplex::extension::agreement::{
    VerifiedOrigin,
    recovery::{Error as RecoveryError, Material, Phase, Verified, Verifier},
};
use commonware_cryptography::certificate::Scoped;
use std::sync::Arc;

fn scope(f: &Fixture<S>) -> Scoped<S> {
    Scoped::verifier(Arc::new(f.verifier.clone()))
}

fn check_scoped(
    scoped: &Scoped<S>,
    p: &Proof,
    expected: &Slot<Digest>,
    leader: Participant,
) -> Result<VerifiedOrigin<Digest>, Error> {
    p.verify_scoped::<Sha256, _>(
        &mut TestRng::new(9101),
        scoped,
        expected,
        leader,
        LIMITS,
        policy,
        &Sequential,
    )
}

fn check_root_scoped(
    scoped: &Scoped<S>,
    expected: &Slot<Digest>,
    store: &recovery::Store,
    root: Digest,
) -> Result<Verified<Digest>, RecoveryError<Digest>> {
    Verifier::new_scoped(
        scoped,
        expected,
        LIMITS,
        &Sequential,
        policy,
        recovery::leader,
    )
    .verify::<Sha256, _>(&mut TestRng::new(9102), root, |id| store.get(id))
}

fn fresh_recovery(f: &Fixture<S>) -> (recovery::Store, Digest, Digest, Digest, Digest) {
    let mut store = recovery::Store::new();
    let rows = recovery::snapshots(&mut store, f, 5, &[None; 7]);
    let value = recovery::fresh(f, 5, &[0, 1, 2, 3, 4]);
    let proposal = recovery::proposal(
        &mut store,
        f,
        5,
        value.clone(),
        &rows,
        &[0, 1, 2, 3, 4],
        &[],
        None,
    );
    let prepared = recovery::rpc(&mut store, f, proposal);
    let terminal = recovery::put(
        &mut store,
        Material::Terminal {
            authority: prepared,
            quorum: recovery::phase_quorum(
                f,
                5,
                Kind::Commit(value.id::<Sha256>()),
                &[2, 3, 4, 5, 6],
            ),
        },
    );
    (store, proposal, prepared, terminal, rows[0])
}

#[test]
fn verify_only_scope_checks_full_origin_and_exact_fast_final_certificate() {
    let f = fixture(7);
    let scoped = scope(&f);
    let p = proof(&f);
    let origin = check_scoped(&scoped, &p, &slot(&f), Participant::new(0)).unwrap();
    assert_eq!(origin.core(), p.core.id::<Sha256>());
    assert_eq!(origin.slot(), slot(&f).id::<Sha256>());
    assert_eq!(origin.value(), p.value.id::<Sha256>());
    let q = quorum(
        &f,
        votes(&f, Kind::FastFinal(origin.value()), &[2, 3, 4, 5, 6]),
    )
    .unwrap();
    let verify = |q: &Quorum<S, Digest>| {
        p.verify_finalization_scoped::<Sha256, _>(
            &mut TestRng::new(9103),
            &scoped,
            &slot(&f),
            Participant::new(0),
            LIMITS,
            policy,
            q,
            &Sequential,
        )
    };
    let terminal = verify(&q).unwrap();
    assert_eq!(terminal.slot(), origin.slot());
    assert_eq!(terminal.value(), origin.value());
    let prepare = quorum(
        &f,
        votes(&f, Kind::Prepare(origin.value()), &[2, 3, 4, 5, 6]),
    )
    .unwrap();
    assert!(matches!(verify(&prepare), Err(Error::Context)));
    let substituted = Quorum {
        certificate: prepare.certificate,
        ..q
    };
    assert!(matches!(verify(&substituted), Err(Error::Signature)));
}

#[test]
fn scoped_origin_rejects_missing_duplicate_and_altered_original_signatures() {
    let f = fixture(7);
    let scoped = scope(&f);
    let p = proof(&f);
    let check = |p: &Proof| check_scoped(&scoped, p, &slot(&f), Participant::new(0));
    let mut missing = p.clone();
    missing.firsts.pop();
    assert!(matches!(check(&missing), Err(Error::Context)));
    let mut duplicate = p.clone();
    duplicate.firsts[4] = duplicate.firsts[3].clone();
    // Keep the declared rows valid so the original-signature identity check is exercised.
    assert!(matches!(check(&duplicate), Err(Error::Identity)));
    let mut changed = p.clone();
    let Kind::First { report, .. } = &mut changed.firsts[2].message.kind else {
        panic!("FIRST fixture")
    };
    *report = Some(Bytes::from_static(b"changed"));
    // Rebind the leader selection; the original reporter still did not sign this report.
    select(&f, &mut changed);
    assert!(matches!(check(&changed), Err(Error::Signature)));
    let mut selection = p.clone();
    selection.selection.attestation = selection.firsts[0].attestation.clone();
    assert!(matches!(check(&selection), Err(Error::Signature)));
    assert!(matches!(
        p.verify_scoped::<Sha256, _>(
            &mut TestRng::new(9104),
            &scoped,
            &slot(&f),
            Participant::new(0),
            LIMITS,
            |_| false,
            &Sequential,
        ),
        Err(Error::Policy)
    ));
}

#[test]
fn scoped_origin_preserves_expected_slot_and_actual_native_leader_checks() {
    let f = fixture(7);
    let scoped = scope(&f);
    let p = proof(&f);
    let mut wrong = vec![slot(&f); 8];
    wrong[0].domain = Digest::from([90; 32]);
    wrong[1].roster = Digest::from([91; 32]);
    wrong[2].selector = Digest::from([92; 32]);
    wrong[3].cut += 1;
    wrong[4].parent = Digest::from([93; 32]);
    wrong[5].proposal.round = Round::new(Epoch::new(2), View::new(4));
    wrong[6].proposal.parent = View::new(2);
    wrong[7].proposal.payload = Digest::from([94; 32]);
    for expected in wrong {
        assert!(matches!(
            check_scoped(&scoped, &p, &expected, Participant::new(0)),
            Err(Error::Context)
        ));
    }
    assert!(matches!(
        check_scoped(&scoped, &p, &slot(&f), Participant::new(1)),
        Err(Error::Context)
    ));
}

#[test]
fn scoped_origin_rejects_foreign_roster_namespace_and_population() {
    let f = fixture(7);
    let p = proof(&f);
    let other = ed25519::fixture(
        &mut TestRng::new(9105),
        b"_COMMONWARE_CONSENSUS_AGREEMENT_TEST",
        7,
    );
    assert!(matches!(
        check_scoped(&scope(&other), &p, &slot(&f), Participant::new(0)),
        Err(Error::Context)
    ));
    let foreign = Scoped::verifier(Arc::new(S::verifier(
        b"_COMMONWARE_CONSENSUS_SCOPED_FOREIGN_NAMESPACE",
        f.verifier.participants().clone(),
    )));
    assert!(matches!(
        check_scoped(&foreign, &p, &slot(&f), Participant::new(0)),
        Err(Error::Signature)
    ));
    assert!(matches!(
        check_scoped(&scope(&fixture(6)), &p, &slot(&f), Participant::new(0)),
        Err(Error::Roster)
    ));
}

#[test]
fn scoped_recovery_requires_complete_fast_origin_before_terminal_authority() {
    let f = fixture(7);
    let scoped = scope(&f);
    let p = proof(&f);
    let value = p.value.clone();
    let mut store = recovery::Store::new();
    let origin = recovery::put(&mut store, Material::Origin(p));
    let terminal = recovery::put(
        &mut store,
        Material::Terminal {
            authority: origin,
            quorum: quorum(
                &f,
                votes(&f, Kind::FastFinal(value.id::<Sha256>()), &[2, 3, 4, 5, 6]),
            )
            .unwrap(),
        },
    );
    let verified = check_root_scoped(&scoped, &slot(&f), &store, terminal).unwrap();
    assert_eq!(verified.phase(), Phase::Terminal);
    assert_eq!(verified.value(), Some(&value));
    store.remove(&origin);
    assert!(matches!(
        check_root_scoped(&scoped, &slot(&f), &store, terminal),
        Err(RecoveryError::Missing(id)) if id == origin
    ));
}

#[test]
fn scoped_recovery_checks_admission_dag_and_exact_prepare_commit_subjects() {
    let f = fixture(7);
    let scoped = scope(&f);
    let (mut store, proposal, prepared, terminal, row) = fresh_recovery(&f);
    for (root, phase) in [
        (proposal, Phase::Proposal),
        (prepared, Phase::Prepared),
        (terminal, Phase::Terminal),
    ] {
        assert_eq!(
            check_root_scoped(&scoped, &slot(&f), &store, root)
                .unwrap()
                .phase(),
            phase
        );
    }
    let Material::Prepared { quorum, .. } = store[&prepared].clone() else {
        panic!("prepared fixture")
    };
    let wrong_phase = recovery::put(
        &mut store,
        Material::Terminal {
            authority: prepared,
            quorum,
        },
    );
    assert!(matches!(
        check_root_scoped(&scoped, &slot(&f), &store, wrong_phase),
        Err(RecoveryError::Invalid("exact phase quorum"))
    ));
    let body = store.remove(&row).unwrap();
    assert!(matches!(
        check_root_scoped(&scoped, &slot(&f), &store, terminal),
        Err(RecoveryError::Missing(id)) if id == row
    ));
    // A body at a requested key is insufficient without its exact content hash.
    store.insert(row, store[&proposal].clone());
    assert!(matches!(
        check_root_scoped(&scoped, &slot(&f), &store, terminal),
        Err(RecoveryError::Hash)
    ));
    store.insert(row, body);
    assert!(check_root_scoped(&scoped, &slot(&f), &store, terminal).is_ok());
}

#[test]
fn scoped_recovery_rejects_policy_election_epoch_roster_and_namespace_mismatch() {
    let f = fixture(7);
    let scoped = scope(&f);
    let expected = slot(&f);
    let (store, _, _, terminal, _) = fresh_recovery(&f);
    assert!(
        Verifier::new_scoped(
            &scoped,
            &expected,
            LIMITS,
            &Sequential,
            |_| false,
            recovery::leader
        )
        .verify::<Sha256, _>(&mut TestRng::new(9106), terminal, |id| store.get(id))
        .is_err()
    );
    assert!(matches!(
        Verifier::new_scoped(&scoped, &expected, LIMITS, &Sequential, policy, |_| Some(
            Participant::new(0)
        ),)
        .verify::<Sha256, _>(&mut TestRng::new(9107), terminal, |id| store.get(id)),
        Err(RecoveryError::Invalid("recovery carrier"))
    ));
    assert!(matches!(
        Verifier::new_scoped(&scoped, &expected, LIMITS, &Sequential, policy, |_| None)
            .verify::<Sha256, _>(&mut TestRng::new(9108), terminal, |id| store.get(id)),
        Err(RecoveryError::Invalid("unauthorized carrier"))
    ));
    let mut epoch = expected.clone();
    epoch.proposal.round = Round::new(Epoch::new(2), View::new(4));
    assert!(check_root_scoped(&scoped, &epoch, &store, terminal).is_err());
    assert!(check_root_scoped(&scope(&fixture(6)), &expected, &store, terminal).is_err());
    let other = ed25519::fixture(
        &mut TestRng::new(9109),
        b"_COMMONWARE_CONSENSUS_AGREEMENT_TEST",
        7,
    );
    assert!(check_root_scoped(&scope(&other), &expected, &store, terminal).is_err());
    let foreign = Scoped::verifier(Arc::new(S::verifier(
        b"_COMMONWARE_CONSENSUS_SCOPED_FOREIGN_NAMESPACE",
        f.verifier.participants().clone(),
    )));
    assert!(matches!(
        check_root_scoped(&foreign, &expected, &store, terminal),
        Err(RecoveryError::Invalid("snapshot authentication"))
    ));
}

#[test]
fn scoped_recovery_individually_authenticates_snapshot_report_bytes() {
    let f = fixture(7);
    let scoped = scope(&f);
    let (mut store, _, _, _, row) = fresh_recovery(&f);
    let Material::Snapshot(mut signed) = store[&row].clone() else {
        panic!("snapshot fixture")
    };
    let Kind::Recover { report, .. } = &mut signed.message.kind else {
        panic!("RECOVER fixture")
    };
    *report = Some(Bytes::from_static(b"unsigned report"));
    let altered = recovery::put(&mut store, Material::Snapshot(signed));
    assert!(matches!(
        check_root_scoped(&scoped, &slot(&f), &store, altered),
        Err(RecoveryError::Invalid("snapshot authentication"))
    ));
}
