//! Signing roles, producer ownership, and domain separation.

use super::*;

fn application_reports_are_authenticated_in_votes_and_qcs<V: Variant>() {
    let committee = Committee::<V>::builder(77, 6)
        .proposal_extension_bound(32)
        .build();
    let codec = committee.codec();
    let leader = committee.leader_block(View::new(1));
    let votes = (0..codec.view_quorum())
        .map(|signer| {
            let original = committee.vote(Participant::from_usize(signer), &leader);
            let body = original
                .body()
                .clone()
                .with_application(bytes::Bytes::from(vec![signer as u8; 3]), codec)
                .unwrap();
            committee.signers[signer].sign_vote(body).unwrap()
        })
        .collect::<Vec<_>>();
    let lqc = committee
        .verifier
        .assemble_lqc::<Sha256, _>(leader.block().clone(), &votes, &Sequential)
        .unwrap();
    let messages = votes
        .iter()
        .cloned()
        .map(ViewMessage::Vote)
        .collect::<Vec<_>>();
    let vqc = committee
        .verifier
        .assemble_vqc::<Sha256, _>(leader.block().clone(), &messages, &Sequential)
        .unwrap();
    let lqc = Lqc::<V, Digest>::decode_cfg(lqc.encode(), &codec).unwrap();
    let vqc = Vqc::<V, Digest>::decode_cfg(vqc.encode(), &codec).unwrap();
    let digested = DigestedLeader::new::<Sha256>(leader.block());
    for vote in &votes {
        assert_eq!(
            lqc.tally().vote(digested, vote.signer(), codec).unwrap(),
            *vote.body()
        );
        assert_eq!(
            vqc.tally().vote(digested, vote.signer(), codec).unwrap(),
            *vote.body()
        );
    }
    let altered = Vote::new(
        votes[0]
            .body()
            .clone()
            .with_application(bytes::Bytes::from_static(b"altered"), codec)
            .unwrap(),
        votes[0].attestation().clone(),
    );
    let changed_tally = Tally::from_votes(
        digested,
        votes.iter().enumerate().map(|(i, vote)| {
            (
                vote.signer(),
                if i == 0 {
                    altered.body().clone()
                } else {
                    vote.body().clone()
                },
            )
        }),
        codec,
    )
    .unwrap();
    let changed_lqc = Lqc::new(
        leader.block().clone(),
        changed_tally.clone(),
        lqc.signature().unwrap().clone(),
        codec,
    )
    .unwrap();
    let changed_vqc = Vqc::new(
        leader.block().clone(),
        changed_tally,
        vqc.novoters().clone(),
        vqc.conflicting_votes().to_vec(),
        vqc.signature().unwrap().clone(),
        codec,
    )
    .unwrap();
    let validated = validate_vqc::<Sha256, V, Digest>(&vqc, codec)
        .unwrap()
        .into_parts();
    let record = crate::multimmit::types::TipRecord::from_vqc::<Sha256, V>(
        &vqc,
        validated.tips.blocks().to_vec(),
    )
    .unwrap();
    assert_eq!(validated.child_history, Some(record.commitment::<Sha256>()));
    let record =
        crate::multimmit::types::TipRecord::<Digest>::decode_cfg(record.encode(), &codec).unwrap();
    let reports = record.vote_reports().unwrap();
    assert_eq!(reports.round(), leader.block().round());
    assert_eq!(reports.leader(), leader.block().digest::<Sha256>());
    assert_eq!(
        reports.reports(),
        votes
            .iter()
            .map(|v| (v.signer(), v.body().application().clone()))
            .collect::<Vec<_>>()
    );
    let altered_record = crate::multimmit::types::TipRecord::from_vqc::<Sha256, V>(
        &changed_vqc,
        validated.tips.blocks().to_vec(),
    )
    .unwrap();
    assert_ne!(
        record.commitment::<Sha256>(),
        altered_record.commitment::<Sha256>()
    );
    let derived_record = crate::multimmit::types::TipRecord::from_vqc::<Sha256, V>(
        &lqc.derive_vqc(codec).unwrap(),
        validated.tips.blocks().to_vec(),
    )
    .unwrap();
    assert_eq!(record, derived_record);
    let artifacts = [
        Artifact::Vote(votes[0].clone()),
        Artifact::Vote(altered),
        Artifact::Lqc(lqc),
        Artifact::Vqc(vqc),
        Artifact::Lqc(changed_lqc),
        Artifact::Vqc(changed_vqc),
    ];
    assert_eq!(
        committee.verifier.verify_artifacts::<_, Sha256, Digest>(
            &mut test_rng(),
            &artifacts.iter().collect::<Vec<_>>(),
            &[],
            &Sequential,
        ),
        vec![true, false, true, true, false, false]
    );
}

#[test]
fn application_reports_are_authenticated_for_both_variants() {
    application_reports_are_authenticated_in_votes_and_qcs::<MinPk>();
    application_reports_are_authenticated_in_votes_and_qcs::<MinSig>();
}

fn ordinary_lqc_application_transcripts_can_differ<V: Variant>() {
    let committee = Committee::<V>::builder(77, 11)
        .proposal_extension_bound(32)
        .build();
    let codec = committee.codec();
    assert_eq!(codec.view_quorum(), 9);
    let leader = committee.leader_block(View::new(1));
    // Each participant signs exactly one body for the same proposal. The payloads
    // are opaque application intentions, not execution or final-order proofs.
    let votes = (0..10)
        .map(|signer| {
            let original = committee.vote(Participant::from_usize(signer), &leader);
            let application = if signer < 5 { b"AB" } else { b"BA" };
            let body = original
                .body()
                .clone()
                .with_application(bytes::Bytes::from_static(application), codec)
                .unwrap();
            committee.signers[signer].sign_vote(body).unwrap()
        })
        .collect::<Vec<_>>();
    let first = committee
        .verifier
        .assemble_lqc::<Sha256, _>(leader.block().clone(), &votes[..9], &Sequential)
        .unwrap();
    let second = committee
        .verifier
        .assemble_lqc::<Sha256, _>(leader.block().clone(), &votes[1..], &Sequential)
        .unwrap();
    let certificates = [first, second]
        .map(|certificate| Lqc::<V, Digest>::decode_cfg(certificate.encode(), &codec).unwrap());
    assert_ne!(
        certificates[0].id::<Sha256>(),
        certificates[1].id::<Sha256>()
    );
    assert_eq!(certificates[0].leader(), certificates[1].leader());
    let records = certificates.each_ref().map(|certificate| {
        let vqc = certificate.derive_vqc(codec).unwrap();
        let validated = validate_vqc::<Sha256, V, Digest>(&vqc, codec)
            .unwrap()
            .into_parts();
        TipRecord::from_vqc::<Sha256, V>(&vqc, validated.tips.blocks().to_vec()).unwrap()
    });
    for (record, expected) in records.iter().zip([b"AB", b"BA"]) {
        let reports = record.vote_reports().unwrap();
        assert_eq!(reports.reports().len(), 9);
        assert_eq!(
            reports
                .reports()
                .iter()
                .filter(|(_, application)| application.as_ref() == expected)
                .count(),
            5
        );
    }
    // Native signatures authenticate each transcript, but do not choose one
    // application order between these valid quorum subsets. Custom ordering
    // therefore needs its separate authenticated history/finality boundary.
    assert_ne!(
        records[0].commitment::<Sha256>(),
        records[1].commitment::<Sha256>()
    );
    let artifacts = certificates.map(Artifact::Lqc);
    assert_eq!(
        committee.verifier.verify_artifacts::<_, Sha256, Digest>(
            &mut test_rng(),
            &artifacts.iter().collect::<Vec<_>>(),
            &[],
            &Sequential,
        ),
        vec![true, true]
    );
}

#[test]
fn ordinary_lqc_application_transcripts_can_differ_without_equivocation() {
    ordinary_lqc_application_transcripts_can_differ::<MinPk>();
    ordinary_lqc_application_transcripts_can_differ::<MinSig>();
}

fn proposal_extension_is_authenticated_by_proposals_and_qcs<V: Variant>() {
    let committee = Committee::<V>::builder(77, 6)
        .proposal_extension_bound(32)
        .build();
    let codec = committee.codec();
    let view = View::new(1);
    let base = committee.leader_block(view);
    let leader = base
        .block()
        .clone()
        .with_extension(bytes::Bytes::from_static(b"direction"), codec)
        .unwrap();
    let scheduled = committee.config.leader(view);
    let signed = committee.signers[usize::from(scheduled)]
        .sign_leader_block(leader.clone())
        .unwrap();
    let votes = (0..codec.view_quorum())
        .map(|signer| committee.vote(Participant::from_usize(signer), &signed))
        .collect::<Vec<_>>();
    let lqc = committee
        .verifier
        .assemble_lqc::<Sha256, _>(leader.clone(), &votes, &Sequential)
        .unwrap();
    let messages = votes.into_iter().map(ViewMessage::Vote).collect::<Vec<_>>();
    let vqc = committee
        .verifier
        .assemble_vqc::<Sha256, _>(leader.clone(), &messages, &Sequential)
        .unwrap();
    let decoded = Lqc::<V, Digest>::decode_cfg(lqc.encode(), &codec).unwrap();
    assert_eq!(decoded.leader().extension().as_ref(), b"direction");
    let decoded = Vqc::<V, Digest>::decode_cfg(vqc.encode(), &codec).unwrap();
    assert_eq!(decoded.leader().extension().as_ref(), b"direction");
    let validated = validate_vqc::<Sha256, V, Digest>(&vqc, codec)
        .unwrap()
        .into_parts();
    let record =
        crate::multimmit::types::TipRecord::from_leader(&leader, validated.tips.blocks().to_vec())
            .unwrap();
    assert_eq!(
        record.proposal_extension().map(|data| data.as_ref()),
        Some(b"direction".as_slice())
    );
    assert_eq!(validated.child_history, Some(record.commitment::<Sha256>()));

    let changed = leader
        .with_extension(bytes::Bytes::from_static(b"other"), codec)
        .unwrap();
    let changed_proposal = SignedLeaderBlock::new(changed.clone(), signed.attestation().clone());
    let changed_lqc = Lqc::new(
        changed.clone(),
        lqc.tally().clone(),
        lqc.signature().unwrap().clone(),
        codec,
    )
    .unwrap();
    let changed_vqc = Vqc::new(
        changed,
        vqc.tally().clone(),
        vqc.novoters().clone(),
        vqc.conflicting_votes().to_vec(),
        vqc.signature().unwrap().clone(),
        codec,
    )
    .unwrap();
    let artifacts = [
        Artifact::LeaderBlock(signed),
        Artifact::Vqc(vqc),
        Artifact::Lqc(lqc),
        Artifact::LeaderBlock(changed_proposal),
        Artifact::Vqc(changed_vqc),
        Artifact::Lqc(changed_lqc),
    ];
    let refs = artifacts.iter().collect::<Vec<_>>();
    assert_eq!(
        committee.verifier.verify_artifacts::<_, Sha256, Digest>(
            &mut test_rng(),
            &refs,
            &[],
            &Sequential
        ),
        vec![true, true, true, false, false, false]
    );
}

#[test]
fn proposal_extension_is_authenticated_for_both_variants() {
    proposal_extension_is_authenticated_by_proposals_and_qcs::<MinPk>();
    proposal_extension_is_authenticated_by_proposals_and_qcs::<MinSig>();
}

fn ordinary_signatures_are_role_and_domain_bound<V: Variant>() {
    let fixture = Fixture::<V>::new();
    let header = fixture.header(2, 1);
    assert_eq!(
        fixture.signers[0]
            .sign_transaction_block(header.clone())
            .unwrap_err(),
        Error::Signer
    );
    let block = fixture.signers[2]
        .sign_transaction_block(header.clone())
        .unwrap();
    assert!(fixture.verifier.verify_transaction_block(&block));

    let da_vote = fixture.signers[2].sign_da_vote(header.clone()).unwrap();
    let wrong_key_and_domain = SignedTransactionBlock::new(
        header,
        Attestation::new(da_vote.signer(), da_vote.share().lazy_signature().clone()),
    );
    assert!(
        !fixture
            .verifier
            .verify_transaction_block(&wrong_key_and_domain)
    );

    let leader = fixture.leader(1);
    let scheduled = usize::from(
        LeaderSchedule::round_robin(fixture.codec.participants())
            .unwrap()
            .leader(leader.view()),
    );
    assert_eq!(
        fixture.signers[(scheduled + 1) % fixture.signers.len()]
            .sign_leader_block(leader.clone())
            .unwrap_err(),
        Error::Signer
    );
    let signed = fixture.signers[scheduled]
        .sign_leader_block(leader.clone())
        .unwrap();
    assert!(fixture.verifier.verify_leader_block(&signed, &Sequential));

    let vote = fixture.signers[0]
        .sign_vote(fixture.standard_body(&leader))
        .unwrap();
    let novote = fixture.signers[1].sign_novote(fixture.round).unwrap();
    assert!(fixture.verifier.verify_vote(&vote));
    assert!(fixture.verifier.verify_novote(&novote));
}

#[test]
fn ordinary_signatures_are_role_and_domain_bound_for_both_variants() {
    ordinary_signatures_are_role_and_domain_bound::<MinPk>();
    ordinary_signatures_are_role_and_domain_bound::<MinSig>();
}

fn producer_ownership_is_independent_of_participant_index<V: Variant>() {
    let producers = vec![Participant::new(1), Participant::new(4)];
    let fixture = Fixture::<V>::with_producers(producers);

    let first = fixture.header(0, 401);
    assert_eq!(
        fixture.signers[0]
            .sign_transaction_block(first.clone())
            .unwrap_err(),
        Error::Signer
    );
    let first = fixture.signers[1].sign_transaction_block(first).unwrap();
    assert!(fixture.verifier.verify_transaction_block(&first));

    let second = fixture.header(1, 402);
    assert_eq!(
        fixture.signers[1]
            .sign_transaction_block(second.clone())
            .unwrap_err(),
        Error::Signer
    );
    let second = fixture.signers[4].sign_transaction_block(second).unwrap();
    assert!(fixture.verifier.verify_transaction_block(&second));

    let identity = Fixture::<V>::new();
    let wrong_owner = identity.signers[0]
        .sign_transaction_block(fixture.header(0, 403))
        .unwrap();
    assert!(!fixture.verifier.verify_transaction_block(&wrong_owner));
    let artifacts = [
        &Artifact::TransactionBlock(first),
        &Artifact::TransactionBlock(wrong_owner),
    ];
    assert_eq!(
        fixture.verifier.verify_artifacts::<_, Sha256, Digest>(
            &mut test_rng(),
            &artifacts,
            &[],
            &Sequential
        ),
        vec![true, false]
    );

    let validator_vote = fixture.signers[5]
        .sign_da_vote(fixture.header(1, 404))
        .unwrap();
    assert!(fixture.verifier.verify_da_vote(&validator_vote));
    assert_eq!(
        fixture.signers[4]
            .sign_da_vote(fixture.header(2, 405))
            .unwrap_err(),
        Error::Chain
    );
    assert_eq!(
        fixture.signers[4]
            .sign_transaction_block(fixture.header(2, 406))
            .unwrap_err(),
        Error::Chain
    );
}

#[test]
fn producer_ownership_is_independent_for_both_variants() {
    producer_ownership_is_independent_of_participant_index::<MinPk>();
    producer_ownership_is_independent_of_participant_index::<MinSig>();
}

fn structural_failures_keep_their_source<V: Variant>() {
    let fixture = Fixture::<V>::new();
    let genesis = Round::new(fixture.round.epoch(), View::zero());
    assert_eq!(
        fixture.signers[0].sign_novote(genesis).unwrap_err(),
        Error::Types(TypesError::GenesisView)
    );
    assert_eq!(
        fixture.signers[0].sign_nullify(genesis).unwrap_err(),
        Error::Types(TypesError::GenesisView)
    );
}

#[test]
fn structural_failures_keep_their_source_for_both_variants() {
    structural_failures_keep_their_source::<MinPk>();
    structural_failures_keep_their_source::<MinSig>();
}

fn signatures_are_namespace_bound<V: Variant>() {
    let fixture = Fixture::<V>::new();
    let mut wrong_namespace = fixture.verifier.clone();
    wrong_namespace.namespace = Namespace::new(b"wrong namespace");

    let header = fixture.header(0, 301);
    let transaction = fixture.signers[0]
        .sign_transaction_block(header.clone())
        .unwrap();
    let da_vote = fixture.signers[0].sign_da_vote(header).unwrap();

    let leader = fixture.leader(302);
    let scheduled = usize::from(
        LeaderSchedule::round_robin(fixture.codec.participants())
            .unwrap()
            .leader(leader.view()),
    );
    let signed_leader = fixture.signers[scheduled]
        .sign_leader_block(leader.clone())
        .unwrap();
    let vote = fixture.signers[0]
        .sign_vote(fixture.standard_body(&leader))
        .unwrap();
    let novote = fixture.signers[0].sign_novote(fixture.round).unwrap();
    let nullify = fixture.signers[0].sign_nullify(fixture.round).unwrap();

    assert!(!wrong_namespace.verify_transaction_block(&transaction));
    assert!(!wrong_namespace.verify_da_vote(&da_vote));
    assert!(!wrong_namespace.verify_leader_block(&signed_leader, &Sequential));
    assert!(!wrong_namespace.verify_vote(&vote));
    assert!(!wrong_namespace.verify_novote(&novote));
    assert!(!wrong_namespace.verify_nullify(&nullify));
}

#[test]
fn signatures_are_namespace_bound_for_every_subject_kind() {
    signatures_are_namespace_bound::<MinPk>();
    signatures_are_namespace_bound::<MinSig>();
}
