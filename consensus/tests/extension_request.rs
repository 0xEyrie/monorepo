//! Encoding fixtures for authenticated native recovery leader requests.
#[cfg(feature = "arbitrary")]
mod conformance {
    use commonware_codec::conformance::CodecConformance;
    use commonware_consensus::simplex::{
        extension::{
            recovery_wire::Wire,
            request::{Command, Request, Response},
        },
        scheme::ed25519,
    };
    use commonware_cryptography::sha256::Digest;
    type RecoveryRequest = Request<ed25519::Scheme, Digest>;
    type RecoveryResponse = Response<ed25519::Scheme, Digest>;
    type RecoveryWire = Wire<ed25519::Scheme, Digest>;
    commonware_conformance::conformance_tests! {
        CodecConformance<Command<Digest>> => 1024,
        CodecConformance<RecoveryRequest> => 1024,
        CodecConformance<RecoveryResponse> => 1024,
        CodecConformance<RecoveryWire> => 1024,
    }
}

#[cfg(test)]
mod wire_tests {
    use bytes::Bytes;
    use commonware_codec::{Decode as _, Encode as _};
    use commonware_consensus::{
        simplex::{
            extension::{
                certificate::Recovered,
                recovery::{Promise, Status},
                recovery_wire::Wire,
                request::{Command, MAX_BYTES, Request, Response},
                vote::{Certificate, Statement, Vote},
            },
            scheme::ed25519,
            types::Proposal,
        },
        types::{Epoch, Round, View},
    };
    use commonware_cryptography::{certificate::Verifier as _, sha256::Digest};
    use commonware_parallel::Sequential;
    use commonware_utils::{TestRng, iter::NonEmpty};
    type Envelope = Wire<ed25519::Scheme, Digest>;
    #[test]
    fn recovery_wire_rejects_truncation_unknown_tags_versions_trailing_and_oversized_input() {
        let mut rng = TestRng::new(1);
        let f = ed25519::fixture(&mut rng, b"_COMMONWARE_CONSENSUS_RECOVERY_WIRE_TEST", 6);
        let cfg = (6, f.verifier.certificate_codec_config());
        let proposal = Proposal::new(
            Round::new(Epoch::new(1), View::new(1)),
            View::zero(),
            Digest::from([1; 32]),
        );
        let ballot = Round::new(Epoch::new(1), View::new(2));
        let domain = Digest::from([2; 32]);
        let subject = Statement {
            proposal: proposal.clone(),
            domain,
            ballot,
            parent: Digest::from([3; 32]),
            extension: Digest::from([4; 32]),
        };
        let status = Status::sign(
            &f.schemes[0],
            Promise {
                proposal: proposal.clone(),
                domain,
                ballot,
                accepted: None,
            },
        )
        .unwrap();
        let request = Request::sign(
            &f.schemes[0],
            Command::Promise {
                proposal,
                domain,
                ballot,
            },
            None,
        )
        .unwrap();
        let vote = Vote::sign(&f.schemes[0], subject.clone()).unwrap();
        let mut votes = f
            .schemes
            .iter()
            .take(5)
            .map(|s| Vote::sign(s, subject.clone()).unwrap());
        let certificate = Certificate::from_votes(
            &mut rng,
            &f.verifier,
            NonEmpty::new(votes.next().unwrap(), votes),
            &Sequential,
        )
        .unwrap();
        for envelope in [
            Envelope::Request(request),
            Envelope::Response(Response::Status {
                status,
                accepted: None,
            }),
            Envelope::Response(Response::Vote(vote)),
            Envelope::Recovered(Recovered::new(certificate).unwrap()),
        ] {
            let bytes = envelope.encode();
            assert_eq!(
                Envelope::decode_cfg(bytes.clone(), &cfg).unwrap().encode(),
                bytes
            );
            for len in 0..bytes.len() {
                assert!(
                    Envelope::decode_cfg(bytes.slice(..len), &cfg).is_err(),
                    "truncated at {len}"
                );
            }
            for (index, value) in [(0, 0), (0, 2), (1, 3), (1, 255)] {
                let mut bad = bytes.to_vec();
                bad[index] = value;
                assert!(Envelope::decode_cfg(Bytes::from(bad), &cfg).is_err());
            }
            let mut extra = bytes.to_vec();
            extra.push(0);
            assert!(Envelope::decode_cfg(Bytes::from(extra), &cfg).is_err());
        }
        let mut too_large = vec![0; MAX_BYTES + 3];
        too_large[0] = 1;
        assert!(Envelope::decode_cfg(Bytes::from(too_large), &cfg).is_err());
    }
}
