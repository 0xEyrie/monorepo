//! Native phase-two envelopes and existing journal with a statically selected mode.
//! This does not start an extended voter or establish its consensus eligibility.

use commonware_codec::{Decode as _, DecodeExt as _, Encode as _};
use commonware_consensus::{
    Epochable as _, Viewable as _,
    simplex::{
        extension::{
            certificate::{Finalization as ExtendedFinalization, Finalize as ExtendedFinalize},
            report::{MAX_REPORT_BYTES, Notarize as ExtendedNotarize},
            vote::{Certificate as ExtensionCertificate, Statement, Vote as ExtensionVote},
        },
        phase2::Extended,
        scheme::ed25519,
        types::{
            Artifact, ArtifactWith, Certificate, CertificateWith, Finalization, Finalize,
            Notarization, Notarize, Nullification, Nullify, Proposal, Vote, VoteWith,
        },
    },
    types::{Epoch, Round, View},
};
use commonware_cryptography::{
    certificate::{Verifier as _, mocks::Fixture},
    sha256::Digest,
};
use commonware_parallel::Sequential;
use commonware_utils::{TestRng, iter::NonEmpty};
const NS: &[u8] = b"_COMMONWARE_CONSENSUS_EXTENSION_MODE_TEST";
type Scheme = ed25519::Scheme;
type EVote = VoteWith<Scheme, Digest, Extended>;
type ECertificate = CertificateWith<Scheme, Digest, Extended>;
type EArtifact = ArtifactWith<Scheme, Digest, Extended>;
fn statement() -> Statement<Digest> {
    let round = Round::new(Epoch::new(1), View::new(2));
    Statement {
        proposal: Proposal::new(round, View::new(1), Digest::from([1; 32])),
        domain: Digest::from([2; 32]),
        ballot: round,
        parent: Digest::from([3; 32]),
        extension: Digest::from([4; 32]),
    }
}
fn fixture() -> Fixture<Scheme> {
    ed25519::fixture(&mut TestRng::new(0), NS, 6)
}
fn certificate(f: &Fixture<Scheme>, s: &Statement<Digest>) -> ExtensionCertificate<Scheme, Digest> {
    let mut votes = f
        .schemes
        .iter()
        .take(5)
        .map(|scheme| ExtensionVote::sign(scheme, s.clone()).unwrap());
    ExtensionCertificate::from_votes(
        &mut TestRng::new(1),
        &f.verifier,
        NonEmpty::new(votes.next().unwrap(), votes),
        &Sequential,
    )
    .unwrap()
}
fn envelopes(f: &Fixture<Scheme>) -> (EVote, ECertificate) {
    let s = statement();
    let vote =
        ExtendedFinalize::new(ExtensionVote::sign(&f.schemes[0], s.clone()).unwrap()).unwrap();
    let cert = commonware_consensus::simplex::extension::certificate::Certificate::classify(
        certificate(f, &s),
    )
    .unwrap()
    .into_native()
    .unwrap();
    (vote.into(), cert)
}
#[test]
fn native_envelopes_retain_the_exact_extension_and_cannot_verify_as_plain_finality() {
    let f = fixture();
    let (vote, cert) = envelopes(&f);
    let cfg = f.verifier.certificate_codec_config();
    assert_eq!(vote.view(), statement().proposal.round.view());
    assert_eq!(vote.epoch(), statement().proposal.round.epoch());
    let decoded = EVote::decode(vote.encode()).unwrap();
    let EVote::Finalize(decoded) = decoded else {
        panic!("wrong vote phase")
    };
    assert_eq!(decoded.vote().statement, statement());
    assert!(
        decoded
            .vote()
            .verify(&mut TestRng::new(2), &f.verifier, &Sequential)
    );
    let restored = ECertificate::decode_cfg(cert.encode(), &cfg).unwrap();
    assert!(restored.verify(&mut TestRng::new(3), &f.verifier, &Sequential));
    if let Ok(Certificate::Finalization(wrong)) =
        Certificate::<Scheme, Digest>::decode_cfg(cert.encode(), &cfg)
    {
        assert!(!wrong.verify(&mut TestRng::new(4), &f.verifier, &Sequential));
    }
    let base = statement().proposal;
    let mut plain_votes = f
        .schemes
        .iter()
        .take(5)
        .map(|scheme| Finalize::sign(scheme, base.clone()).unwrap());
    let plain = Finalization::from_owned_finalizes(
        &f.verifier,
        NonEmpty::new(plain_votes.next().unwrap(), plain_votes),
        &Sequential,
    )
    .unwrap();
    let plain = Certificate::Finalization(plain);
    if let Ok(wrong) = ECertificate::decode_cfg(plain.encode(), &cfg) {
        assert!(!wrong.verify(&mut TestRng::new(5), &f.verifier, &Sequential));
    }
    let bytes = restored.encode();
    for end in 0..bytes.len() {
        assert!(ECertificate::decode_cfg(bytes.slice(..end), &cfg).is_err());
    }
}
#[test]
fn recovery_votes_and_certificates_cannot_enter_native_finalization_or_its_wal() {
    let f = fixture();
    let mut s = statement();
    s.ballot = Round::new(s.ballot.epoch(), View::new(3));
    let vote = ExtensionVote::sign(&f.schemes[0], s.clone()).unwrap();
    let cert = certificate(&f, &s);
    let cfg = f.verifier.certificate_codec_config();
    assert!(ExtendedFinalize::new(vote.clone()).is_err());
    assert!(ExtendedFinalization::new(cert.clone()).is_err());
    assert!(
        commonware_consensus::simplex::extension::certificate::Certificate::classify(cert.clone())
            .unwrap()
            .into_native()
            .is_err()
    );
    // Forge only envelope tags around real recovery signatures: decoding must reject.
    let mut bytes = vec![2];
    bytes.extend_from_slice(&vote.encode());
    assert!(EVote::decode(bytes).is_err());
    let mut bytes = vec![2];
    bytes.extend_from_slice(&cert.encode());
    assert!(ECertificate::decode_cfg(bytes, &cfg).is_err());
    let mut bytes = vec![5];
    bytes.extend_from_slice(&vote.encode());
    assert!(EArtifact::decode_cfg(bytes, &cfg).is_err());
    let mut bytes = vec![6];
    bytes.extend_from_slice(&cert.encode());
    assert!(EArtifact::decode_cfg(bytes, &cfg).is_err());
}
#[test]
fn original_envelopes_keep_their_fields_and_wire_without_extension_storage() {
    // Reference shapes copied from the original native envelopes, independent of Mode.
    #[allow(dead_code)]
    enum OriginalVote {
        Notarize(Notarize<Scheme, Digest>),
        Nullify(Nullify<Scheme>),
        Finalize(Finalize<Scheme, Digest>),
    }
    #[allow(dead_code)]
    enum OriginalCertificate {
        Notarization(Notarization<Scheme, Digest>),
        Nullification(Nullification<Scheme>),
        Finalization(Finalization<Scheme, Digest>),
    }
    #[allow(dead_code)]
    enum OriginalArtifact {
        Notarize(Notarize<Scheme, Digest>),
        Notarization(Notarization<Scheme, Digest>),
        Certification(Round, bool),
        Nullify(Nullify<Scheme>),
        Nullification(Nullification<Scheme>),
        Finalize(Finalize<Scheme, Digest>),
        Finalization(Finalization<Scheme, Digest>),
    }
    assert_eq!(
        std::mem::size_of::<Vote<Scheme, Digest>>(),
        std::mem::size_of::<OriginalVote>()
    );
    assert_eq!(
        std::mem::size_of::<Certificate<Scheme, Digest>>(),
        std::mem::size_of::<OriginalCertificate>()
    );
    assert_eq!(
        std::mem::size_of::<Artifact<Scheme, Digest>>(),
        std::mem::size_of::<OriginalArtifact>()
    );
    let f = fixture();
    let p = statement().proposal;
    let finalize = Finalize::sign(&f.schemes[0], p.clone()).unwrap();
    let mut expected = vec![2];
    expected.extend_from_slice(&finalize.encode());
    assert_eq!(
        Vote::Finalize(finalize).encode().as_ref(),
        expected.as_slice()
    );
    let notarize = Notarize::sign(&f.schemes[0], p).unwrap();
    let mut expected = vec![0];
    expected.extend_from_slice(&notarize.encode());
    assert_eq!(Vote::Notarize(notarize.clone()).encode().as_ref(), expected);
    expected.push(0); // Extended mode explicitly encodes report absence.
    assert_eq!(EVote::Notarize(notarize.into()).encode().as_ref(), expected);
}
#[test]
fn first_vote_reports_are_bounded_optional_and_independent_of_notarization() {
    use bytes::Bytes;
    let f = fixture();
    let p = statement().proposal;
    let base = Notarize::sign(&f.schemes[0], p.clone()).unwrap();
    for report in [
        None,
        Some(Bytes::new()),
        Some(Bytes::from_static(b"invalid report signature")),
        Some(Bytes::from(vec![7; MAX_REPORT_BYTES])),
    ] {
        let vote = ExtendedNotarize::new(base.clone(), report.clone()).unwrap();
        let encoded = EVote::Notarize(vote).encode();
        let EVote::Notarize(restored) = EVote::decode(encoded.clone()).unwrap() else {
            panic!("wrong phase")
        };
        assert_eq!(restored.report(), report.as_ref());
        assert!(
            restored
                .vote()
                .verify(&mut TestRng::new(9), &f.verifier, &Sequential)
        );
        assert_eq!(restored.into_parts(), (base.clone(), report));
        for end in [0, 1, encoded.len() - 1] {
            assert!(EVote::decode(encoded.slice(..end)).is_err());
        }
        let mut trailing = encoded.to_vec();
        trailing.push(0);
        assert!(EVote::decode(trailing).is_err());
    }
    // An oversized local report returns the usable base vote to the caller.
    let fallback = ExtendedNotarize::new(
        base.clone(),
        Some(Bytes::from(vec![0; MAX_REPORT_BYTES + 1])),
    )
    .unwrap_err();
    assert_eq!(fallback, base);
    let without_report = ExtendedNotarize::from(fallback);
    assert!(without_report.report().is_none());
    // A remote length above the cap is rejected, including a truncated body.
    let mut oversized = vec![0];
    oversized.extend_from_slice(&base.encode());
    oversized.extend_from_slice(&Some(Bytes::from(vec![0; MAX_REPORT_BYTES + 1])).encode());
    assert!(EVote::decode(oversized.clone()).is_err());
    oversized.truncate(base.encode().len() + 10);
    assert!(EVote::decode(oversized).is_err());
    // Different attached reports still aggregate only the original proposal.
    let votes = f.schemes.iter().take(5).enumerate().map(|(i, scheme)| {
        ExtendedNotarize::new(
            Notarize::sign(scheme, p.clone()).unwrap(),
            Some(Bytes::from(vec![i as u8])),
        )
        .unwrap()
        .into_parts()
        .0
    });
    let mut votes = votes;
    let qc = Notarization::from_owned_notarizes(
        &f.verifier,
        NonEmpty::new(votes.next().unwrap(), votes),
        &Sequential,
    )
    .unwrap();
    assert!(qc.verify(&mut TestRng::new(10), &f.verifier, &Sequential));
}
#[cfg(not(target_arch = "wasm32"))]
#[test]
fn existing_native_journal_replays_the_full_extension_subject() {
    use commonware_runtime::{
        ReadOptions, Runner as _, Supervisor as _, buffer::paged::CacheRef, deterministic,
    };
    use commonware_storage::journal::segmented::variable::{Config, Journal};
    use commonware_utils::{NZU16, NZUsize};
    let f = fixture();
    let cfg_codec = f.verifier.certificate_codec_config();
    let (vote, cert) = envelopes(&f);
    let first = ExtendedNotarize::new(
        Notarize::sign(&f.schemes[0], statement().proposal).unwrap(),
        Some(bytes::Bytes::from_static(
            b"original signed report retained verbatim",
        )),
    )
    .unwrap();
    let records = [
        EArtifact::Notarize(first),
        EArtifact::from(vote),
        EArtifact::from(cert),
    ];
    let expected = records.iter().map(|v| v.encode()).collect::<Vec<_>>();
    let (_, checkpoint) =
        deterministic::Runner::default().start_and_recover(move |context| async move {
            let cfg = Config {
                partition: "extension-native-wal".into(),
                compression: None,
                codec_config: cfg_codec,
                page_cache: CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(8)),
                write_buffer: NZUsize!(1024),
            };
            let mut journal = Journal::<_, EArtifact>::init(context.child("wal"), cfg)
                .await
                .unwrap();
            for record in records {
                journal = journal
                    .append(record.view().get(), &record)
                    .await
                    .unwrap()
                    .0;
            }
            let _journal = journal.sync(2).await.unwrap();
        });
    deterministic::Runner::from(checkpoint).start(move |context| async move {
        let cfg = Config {
            partition: "extension-native-wal".into(),
            compression: None,
            codec_config: f.verifier.certificate_codec_config(),
            page_cache: CacheRef::from_pooler(&context, NZU16!(1024), NZUsize!(8)),
            write_buffer: NZUsize!(1024),
        };
        let journal = Journal::<_, EArtifact>::init(context.child("restored"), cfg)
            .await
            .unwrap();
        let mut replay = journal
            .replay(2, 0, NZUsize!(1024), ReadOptions::DONT_CACHE)
            .await
            .unwrap();
        let mut actual = Vec::new();
        let mut round =
            commonware_consensus::simplex::phase2::voting::RoundWith::<_, _, Extended>::new(
                f.schemes[0].clone(),
                statement().proposal.round,
            );
        while let Some(item) = replay.next().await {
            let (_, _, _, record) = item.unwrap();
            actual.push(record.encode());
            if let EArtifact::Finalization(cert) = &record {
                round.add_finalization(cert.clone());
            }
            round.replay(&record);
            match record {
                EArtifact::Notarize(vote) => {
                    assert_eq!(
                        vote.report().unwrap().as_ref(),
                        b"original signed report retained verbatim"
                    );
                    assert!(
                        vote.vote()
                            .verify(&mut TestRng::new(8), &f.verifier, &Sequential)
                    );
                }
                EArtifact::Finalize(vote) => {
                    assert_eq!(vote.vote().statement, statement());
                    assert!(
                        vote.vote()
                            .verify(&mut TestRng::new(6), &f.verifier, &Sequential)
                    );
                }
                EArtifact::Finalization(cert) => {
                    assert_eq!(cert.certificate().statement, statement());
                    assert!(ECertificate::Finalization(cert).verify(
                        &mut TestRng::new(7),
                        &f.verifier,
                        &Sequential
                    ));
                }
                _ => panic!("unexpected record"),
            }
        }
        replay.finish().unwrap();
        assert_eq!(actual, expected);
        assert_eq!(round.final_subject(), Some(&statement()));
        assert_eq!(
            round.finalization().unwrap().certificate().statement,
            statement()
        );
        let mut different = statement();
        different.extension = Digest::from([99; 32]);
        assert!(round.construct_finalize_with(different).is_none());
        assert!(round.broadcast_finalization().is_none());
    });
}
#[cfg(feature = "arbitrary")]
mod conformance {
    use super::*;
    use commonware_codec::conformance::CodecConformance;
    use commonware_consensus::simplex::scheme::bls12381_threshold::vrf;
    use commonware_cryptography::bls12381::primitives::variant::MinSig;
    type OriginalScheme = vrf::Scheme<commonware_cryptography::ed25519::PublicKey, MinSig>;
    commonware_conformance::conformance_tests! {
        CodecConformance<Vote<OriginalScheme,Digest>>,
        CodecConformance<Certificate<OriginalScheme,Digest>>,
        CodecConformance<Artifact<OriginalScheme,Digest>>,
        CodecConformance<EVote> => 1024,
        CodecConformance<ECertificate> => 1024,
        CodecConformance<EArtifact> => 1024,
        CodecConformance<commonware_consensus::simplex::extension::certificate::Recovered<Scheme,Digest>> => 1024,
    }
}
