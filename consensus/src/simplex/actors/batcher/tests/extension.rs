//! Extended votes traverse the production network actor and voter mailbox.
use super::*;
use crate::simplex::{
    extension::{
        certificate::{Finalization as EC, Finalize as EF},
        report::Notarize as EN,
        vote::{Certificate as RawCertificate, Statement, Vote as EV},
    },
    phase2::Extended,
    types::{ActivityWith, CertificateWith, VoteWith},
};
#[derive(Clone)]
struct Report<S: Scheme<Sha256Digest>>(PhantomData<S>);
impl<S: Scheme<Sha256Digest>> crate::Reporter for Report<S> {
    type Activity = ActivityWith<S, Sha256Digest, Extended>;
    fn report(&mut self, _: Self::Activity) -> Feedback {
        Feedback::Ok
    }
}
fn statement(p: Proposal<Sha256Digest>, d: u8) -> Statement<Sha256Digest> {
    Statement {
        ballot: p.round,
        proposal: p,
        domain: Sha256Digest::from([2; 32]),
        parent: Sha256Digest::from([3; 32]),
        extension: Sha256Digest::from([d; 32]),
    }
}
fn exercise<S, F>(fixture: F, split: bool)
where
    S: Scheme<Sha256Digest, PublicKey = PublicKey>,
    F: FnOnce(&mut deterministic::Context, &[u8], u32) -> Fixture<S>,
{
    deterministic::Runner::timed(Duration::from_secs(10)).start(|mut context|async move {
        let Fixture{participants,schemes,verifier,..}=fixture(&mut context,b"_COMMONWARE_CONSENSUS_EXTENSION_ACTOR_TEST",6);
        let epoch=Epoch::new(1);
        let p=Proposal::new(Round::new(epoch,View::new(1)),View::zero(),Sha256Digest::from([1;32]));
        let me=participants[0].clone();
        let oracle=start_test_network_with_peers(context.child("network"),participants.clone()).await;
        let (batcher,mut inbox)=ActorWith::<_,_,_,_,_,_,_,Extended>::new(context.child("actor"),test_config(schemes[0].clone(),oracle.control(me.clone()),Report(PhantomData),MockRelay::new(),epoch,BatcherOptions::default()));
        let (sender,mut output)=mailbox::new::<voter::Message<S,Sha256Digest,Extended>>(context.child("voter"),NZUsize!(1));
        let voter=voter::Mailbox::new(sender);
        let (_,votes)=oracle.control(me.clone()).register(0,TEST_QUOTA).await.unwrap();
        let (_,certs)=oracle.control(me.clone()).register(1,TEST_QUOTA).await.unwrap();
        let mut senders=Vec::new();
        let mut cert_senders=Vec::new();
        for peer in participants.iter().skip(1) {
            senders.push(register_and_link_peer(&oracle,peer.clone(),me.clone(),0,Duration::from_millis(1)).await);
            let (sender,_)=oracle.control(peer.clone()).register(1,TEST_QUOTA).await.unwrap();cert_senders.push(sender);
        }
        batcher.start(voter,votes,certs);
        inbox.update(Span::none(),p.round.view(),Participant::new(1),View::zero(),None);
        for (i,scheme) in schemes.iter().enumerate() {
            let vote=VoteWith::<S,Sha256Digest,Extended>::Notarize(EN::new(Notarize::sign(scheme,p.clone()).unwrap(),Some(bytes::Bytes::from(vec![i as u8]))).unwrap());
            if i==0 {inbox.constructed(vote);} else {senders[i-1].send(Recipients::One(me.clone()),vote.encode(),true);}
        }
        // Mailbox capacity one exercises native overflow while retaining exact subjects.
        context.sleep(Duration::from_millis(20)).await;
        assert!(matches!(output.recv().await.unwrap(),voter::Message::Proposal{proposal,..} if proposal==p));
        match output.recv().await.unwrap() {
            voter::Message::Verified{certificate:CertificateWith::Notarization(qc),..}=>assert!(qc.verify(&mut context,&verifier,&Sequential)),
            _=>panic!("missing first-phase certificate"),
        }
        // One valid minority reaches the actor before the majority. In the split
        // case no exact subject can collect the unchanged native quorum of five.
        let minority=VoteWith::<S,Sha256Digest,Extended>::Finalize(EF::new(EV::sign(&schemes[1],statement(p.clone(),4)).unwrap()).unwrap());
        senders[0].send(Recipients::One(me.clone()),minority.encode(),true);
        context.sleep(Duration::from_millis(10)).await;
        for (i,scheme) in schemes.iter().enumerate() {
            if i==1 {continue;}
            let d=if split && i<3 {4} else {5};
            let vote=VoteWith::<S,Sha256Digest,Extended>::Finalize(EF::new(EV::sign(scheme,statement(p.clone(),d)).unwrap()).unwrap());
            if i==0 {inbox.constructed(vote);} else {senders[i-1].send(Recipients::One(me.clone()),vote.encode(),true);}
        }
        if split {
            select! {
                unexpected=output.recv()=>panic!("split subjects produced a message: {}",unexpected.is_some()),
                _=context.sleep(Duration::from_millis(50))=>{},
            }
        } else {
            match output.recv().await.unwrap() {
                voter::Message::Verified{certificate:CertificateWith::Finalization(qc),..}=>{
                    assert!(qc.certificate().verify(&mut context,&verifier,&Sequential));
                    assert_eq!(qc.certificate().statement,statement(p,5));
                },
                _=>panic!("missing exact final certificate"),
            }
        }
        // Certificate bytes from the network use the same mode, and a signature
        // over different extension bytes cannot reach the voter as verified.
        let next=Proposal::new(Round::new(epoch,View::new(2)),View::new(1),Sha256Digest::from([8;32]));
        inbox.update(Span::none(),View::new(2),Participant::new(2),View::zero(),None);
        let votes:Vec<_>=schemes.iter().take(5).map(|s|EV::sign(s,statement(next.clone(),9)).unwrap()).collect();
        let raw=RawCertificate::from_votes(&mut context,&verifier,non_empty![@votes],&Sequential).unwrap();
        let mut bad=raw.clone();bad.statement.extension=Sha256Digest::from([10;32]);
        cert_senders[4].send(Recipients::One(me.clone()),CertificateWith::<S,Sha256Digest,Extended>::Finalization(EC::new(bad).unwrap()).encode(),true);
        select! {
            unexpected=output.recv()=>panic!("forged certificate reached voter: {}",unexpected.is_some()),
            _=context.sleep(Duration::from_millis(20))=>{},
        }
        cert_senders[1].send(Recipients::One(me),CertificateWith::<S,Sha256Digest,Extended>::Finalization(EC::new(raw).unwrap()).encode(),true);
        match output.recv().await.unwrap() {
            voter::Message::Verified{certificate:CertificateWith::Finalization(qc),..}=>{
                assert!(qc.certificate().verify(&mut context,&verifier,&Sequential));
                assert_eq!(qc.certificate().statement,statement(next,9));
            },
            _=>panic!("missing verified network certificate"),
        }
    });
}
#[test]
fn ed25519_network_extensions() {
    for split in [false, true] {
        exercise(ed25519::fixture, split);
    }
}
#[test]
fn multisig_network_extensions() {
    for split in [false, true] {
        exercise(bls12381_multisig::fixture::<MinSig, _>, split);
    }
}
#[test]
fn threshold_network_extensions() {
    for split in [false, true] {
        exercise(bls12381_threshold_std::fixture::<MinSig, _>, split);
    }
}
#[test]
fn vrf_network_extensions() {
    for split in [false, true] {
        exercise(bls12381_threshold_vrf::fixture::<MinSig, _>, split);
    }
}
