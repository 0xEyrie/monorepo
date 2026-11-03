//! Exact extension subjects survive the production resolver transport.
use super::*;
use crate::{
    simplex::{
        extension::{
            certificate::Finalization as EC,
            vote::{Certificate as RawCertificate, Statement, Vote as EV},
        },
        phase2::Extended,
        scheme::{
            bls12381_multisig,
            bls12381_threshold::{standard, vrf},
            ed25519,
        },
        types::Proposal,
    },
    types::{Round, TermLength},
};
use commonware_cryptography::{
    bls12381::primitives::variant::MinSig, certificate::mocks::Fixture, ed25519::PublicKey,
    sha256::Digest as Sha256Digest,
};
use commonware_macros::select;
use commonware_p2p::{
    simulated::{Config as NetworkConfig, Link, Network},
    utils::mocks::NoopBlocker,
};
use commonware_parallel::Sequential;
use commonware_runtime::{Quota, Runner, Supervisor, deterministic};
use commonware_utils::{NZU32, NZUsize, non_empty, probability};

fn config<S: Scheme<Sha256Digest, PublicKey = PublicKey>>(
    scheme: S,
) -> Config<S, NoopBlocker<PublicKey>, Sequential> {
    Config {
        scheme,
        blocker: NoopBlocker::default(),
        strategy: Sequential,
        epoch: Epoch::new(1),
        mailbox_size: NZUsize!(1),
        fetch_timeout: Duration::from_millis(200),
        term_length: TermLength::ONE,
    }
}
fn exercise<S, F>(fixture: F)
where
    S: Scheme<Sha256Digest, PublicKey = PublicKey>,
    F: FnOnce(&mut deterministic::Context, &[u8], u32) -> Fixture<S>,
{
    deterministic::Runner::timed(Duration::from_secs(10)).start(|mut context|async move {
        let Fixture {participants,schemes,verifier,..}=fixture(&mut context,b"_COMMONWARE_CONSENSUS_EXTENSION_RESOLVER_TEST",6);
        let p=Proposal::new(Round::new(Epoch::new(1),View::new(2)),View::new(1),Sha256Digest::from([1;32]));
        let statement=Statement {ballot:p.round,proposal:p,domain:Sha256Digest::from([2;32]),parent:Sha256Digest::from([3;32]),extension:Sha256Digest::from([4;32])};
        let votes:Vec<_>=schemes.iter().take(5).map(|s|EV::sign(s,statement.clone()).unwrap()).collect();
        let raw=RawCertificate::from_votes(&mut context,&verifier,non_empty![@votes],&Sequential).unwrap();
        let certificate=CertificateWith::<S,Sha256Digest,Extended>::Finalization(EC::new(raw.clone()).unwrap());
        let (mut validator,_)=ActorWith::<_,_,_,_,_,Extended>::new(context.child("validator"),config(schemes[0].clone()));
        assert_eq!(validator.validate(View::new(1),certificate.encode()).unwrap().encode(),certificate.encode());
        assert!(validator.validate(View::new(3),certificate.encode()).is_none());
        for field in 0..4 {
            let mut forged=raw.clone();
            match field {
                0=>forged.statement.extension=Sha256Digest::from([99;32]),
                1=>forged.statement.parent=Sha256Digest::from([99;32]),
                2=>forged.statement.domain=Sha256Digest::from([99;32]),
                _=>forged.statement.proposal.payload=Sha256Digest::from([99;32]),
            }
            assert!(validator.validate(View::new(1),CertificateWith::<S,Sha256Digest,Extended>::Finalization(EC::new(forged).unwrap()).encode()).is_none());
        }
        // The view-keyed native resolver still serves a covering higher QC.
        // This is deliberately NOT an exact old interpretation/preimage lookup.
        validator.state.handle(certificate.clone());
        assert_eq!(validator.produce_certificate(View::new(1)),Some(certificate.encode()));
        let (network,oracle)=Network::new_with_peers(context.child("network"),NetworkConfig {max_size:1024*1024,max_peers_per_set:NZUsize!(6),disconnect_on_block:true,tracked_peer_sets:NZUsize!(1)},participants.clone()).await;
        network.start();
        let requester_connection=oracle.control(participants[0].clone()).register(2,Quota::per_second(NZU32!(1000))).await.unwrap();
        let responder_connection=oracle.control(participants[1].clone()).register(2,Quota::per_second(NZU32!(1000))).await.unwrap();
        let link=Link {latency:Duration::from_millis(10),jitter:Duration::from_millis(1),success_rate:probability!(1.0)};
        oracle.add_link(participants[0].clone(),participants[1].clone(),link.clone()).await.unwrap();
        oracle.add_link(participants[1].clone(),participants[0].clone(),link).await.unwrap();
        let (requester_voter,mut output)=mailbox::new::<voter::Message<S,Sha256Digest,Extended>>(context.child("requester_voter"),NZUsize!(1));
        let (requester,mut request)=ActorWith::<_,_,_,_,_,Extended>::new(context.child("requester"),config(schemes[0].clone()));
        requester.start(voter::Mailbox::new(requester_voter),requester_connection.0,requester_connection.1);
        let (responder_voter,_output)=mailbox::new::<voter::Message<S,Sha256Digest,Extended>>(context.child("responder_voter"),NZUsize!(1));
        let (responder,mut respond)=ActorWith::<_,_,_,_,_,Extended>::new(context.child("responder"),config(schemes[1].clone()));
        responder.start(voter::Mailbox::new(responder_voter),responder_connection.0,responder_connection.1);
        respond.updated(certificate.clone());
        request.resolve(View::new(3),View::new(1),Kind::Notarization,Some(participants[1].clone()));
        let result=select! {
            message=output.recv()=>message.expect("voter mailbox closed"),
            _=context.sleep(Duration::from_secs(3))=>panic!("extended resolver did not deliver the covering certificate"),
        };
        match result {
            voter::Message::Verified {certificate:received,from_resolver:true,..}=>{
                assert_eq!(received.encode(),certificate.encode());
                assert!(received.verify(&mut context,&verifier,&Sequential));
                let CertificateWith::Finalization(qc)=received else {panic!("wrong certificate kind")};
                assert_eq!(qc.certificate().statement,statement);
            }
            _=>panic!("wrong resolver delivery"),
        }
    });
}
#[test]
fn ed25519_resolver_extensions() {
    exercise(ed25519::fixture);
}
#[test]
fn multisig_resolver_extensions() {
    exercise(bls12381_multisig::fixture::<MinSig, _>);
}
#[test]
fn threshold_resolver_extensions() {
    exercise(standard::fixture::<MinSig, _>);
}
#[test]
fn vrf_resolver_extensions() {
    exercise(vrf::fixture::<MinSig, _>);
}
