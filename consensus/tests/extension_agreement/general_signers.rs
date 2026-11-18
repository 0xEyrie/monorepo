//! Actual attributable certificate owner sets, separate from G1 admission.
use commonware_consensus::{
    simplex::{
        extension::{
            agreement::general::{Committee, normal::CertificateSigners},
            vote::{Certificate, Statement, Vote},
        },
        scheme::{self, bls12381_multisig, ed25519, secp256r1},
        types::{Notarization, Notarize, Proposal, Subject},
    },
    types::{Epoch, Participant, Round, View},
};
use commonware_cryptography::{
    bls12381::primitives::variant::{MinPk, MinSig},
    certificate::{Scoped, Signers, Verifier as _, mocks::Fixture},
    sha256::Digest,
};
use commonware_parallel::Sequential;
use commonware_utils::{TestRng, iter::NonEmpty};
use std::{collections::BTreeSet, sync::Arc};

const NS: &[u8] = b"_COMMONWARE_CONSENSUS_G1_CERTIFICATE_SIGNERS_TEST";

fn subject() -> Statement<Digest> {
    let round = Round::new(Epoch::new(17), View::new(4));
    Statement {
        proposal: Proposal::new(round, View::new(3), Digest::from([71; 32])),
        domain: Digest::from([72; 32]),
        ballot: round,
        parent: Digest::from([73; 32]),
        extension: Digest::from([74; 32]),
    }
}

fn nonempty<T>(items: Vec<T>) -> NonEmpty<std::vec::IntoIter<T>> {
    let mut iter = items.into_iter();
    NonEmpty::new(iter.next().unwrap(), iter)
}

fn owners(c: Committee) -> Vec<Participant> {
    let omitted: BTreeSet<_> = (0..c.len())
        .filter(|i| i % 3 == 1)
        .take(c.faults())
        .collect();
    (0..c.len())
        .filter(|i| !omitted.contains(i))
        .map(Participant::from_usize)
        .collect()
}

fn signed_certificate<S: scheme::Scheme<Digest>>(
    f: &Fixture<S>,
    statement: &Statement<Digest>,
    owners: &[Participant],
) -> Certificate<S, Digest> {
    let votes = owners
        .iter()
        .map(|owner| Vote::sign(&f.schemes[usize::from(*owner)], statement.clone()).unwrap())
        .collect();
    Certificate::from_votes(
        &mut TestRng::new(11001),
        &f.verifier,
        nonempty(votes),
        &Sequential,
    )
    .unwrap()
}

fn check<S>(f: Fixture<S>, replace_signers: impl Fn(&mut S::Certificate, Signers))
where
    S: scheme::Scheme<Digest>,
    S::Certificate: CertificateSigners,
{
    let mut rng = TestRng::new(11002);
    let c = Committee::new(f.schemes.len()).unwrap();
    assert_eq!(c.faults(), (c.len() - 1) / 3);
    assert_eq!(c.quorum(), c.len() - c.faults());
    if c.len() % 3 != 1 {
        assert!(c.quorum() > 2 * c.faults() + 1);
    }
    let subject = subject();
    let owners = owners(c);
    assert_eq!(owners.len(), c.quorum());
    assert_eq!(owners.last(), Some(&Participant::from_usize(c.len() - 1)));
    assert!(!owners.contains(&Participant::new(1)));
    let certificate = signed_certificate(&f, &subject, &owners);

    // A verify-only scope may retain a signing-capable scheme internally, but
    // neither reading certificate metadata nor public verification releases it.
    let scoped = Scoped::verifier(Arc::new(f.schemes[0].clone()));
    assert!(scoped.clone().into_scheme().is_none());
    assert!(certificate.verify(&mut rng, &scoped, &Sequential));
    let signers = certificate.certificate.signers();
    assert_eq!(signers.len(), c.len());
    assert_eq!(signers.count(), c.quorum());
    assert_eq!(signers.iter().collect::<Vec<_>>(), owners);

    // Two genuine quorum certificates for one subject can have different owner
    // sets. Independent quorum verification cannot establish set equality.
    let mut alternative = owners.clone();
    alternative[0] = Participant::new(1);
    alternative.sort_unstable();
    let other = signed_certificate(&f, &subject, &alternative);
    assert!(other.verify(&mut rng, &scoped, &Sequential));
    assert_eq!(other.certificate.signers().count(), c.quorum());
    assert_ne!(other.certificate.signers(), signers);

    // Relabelling valid signatures with another valid-width/count bitmap must
    // fail cryptographic verification. The accessor itself makes no such claim.
    let mut relabelled = certificate.clone();
    replace_signers(
        &mut relabelled.certificate,
        Signers::new(c.len() as u32, alternative.iter().copied()).unwrap(),
    );
    assert_eq!(relabelled.certificate.signers().len(), c.len());
    assert_eq!(relabelled.certificate.signers().count(), c.quorum());
    assert!(!relabelled.verify(&mut rng, &scoped, &Sequential));
    let mut wrong_width = certificate.clone();
    replace_signers(
        &mut wrong_width.certificate,
        Signers::new(c.len() as u32 + 1, owners.iter().copied()).unwrap(),
    );
    assert_eq!(wrong_width.certificate.signers().count(), c.quorum());
    assert!(!wrong_width.verify(&mut rng, &scoped, &Sequential));

    // The election witness keeps its genuine original NOTARIZE role and may
    // use a different signer subset from a normal finality certificate.
    let votes = alternative
        .iter()
        .map(|owner| {
            Notarize::sign(&f.schemes[usize::from(*owner)], subject.proposal.clone()).unwrap()
        })
        .collect();
    let nqc =
        Notarization::from_owned_notarizes(&f.verifier, nonempty(votes), &Sequential).unwrap();
    assert_eq!(nqc.proposal, subject.proposal);
    assert!(scoped.verify_certificate::<_, Digest>(
        &mut rng,
        Subject::Notarize {
            proposal: &subject.proposal,
        },
        &nqc.certificate,
        &Sequential,
    ));
    assert_eq!(nqc.certificate.signers().len(), c.len());
    assert_eq!(nqc.certificate.signers().count(), c.quorum());
    assert_eq!(
        nqc.certificate.signers().iter().collect::<Vec<_>>(),
        alternative,
    );
    assert_ne!(nqc.certificate.signers(), signers);
    assert!(!scoped.verify_certificate::<_, Digest>(
        &mut rng,
        Subject::FinalizeExtension {
            statement: &subject,
        },
        &nqc.certificate,
        &Sequential,
    ));
    assert!(!scoped.verify_certificate::<_, Digest>(
        &mut rng,
        Subject::Notarize {
            proposal: &subject.proposal,
        },
        &certificate.certificate,
        &Sequential,
    ));
    assert!(scoped.into_scheme().is_none());
}

#[test]
fn ed25519_general_and_slack_roster_certificate_owners() {
    for n in [4, 7, 8, 9, 10, 11, 12, 13, 16, 31, 64] {
        check(
            ed25519::fixture(&mut TestRng::new(11003), NS, n),
            |certificate, signers| certificate.signers = signers,
        );
    }
}

#[test]
fn secp256r1_general_and_slack_roster_certificate_owners() {
    for n in [4, 8, 9, 10, 16, 64] {
        check(
            secp256r1::fixture(&mut TestRng::new(11004), NS, n),
            |certificate, signers| certificate.signers = signers,
        );
    }
}

#[test]
fn bls_multisig_general_and_slack_roster_certificate_owners() {
    for n in [4, 8, 9, 10, 16, 64] {
        check(
            bls12381_multisig::fixture::<MinSig, _>(&mut TestRng::new(11005), NS, n),
            |certificate, signers| certificate.signers = signers,
        );
        check(
            bls12381_multisig::fixture::<MinPk, _>(&mut TestRng::new(11006), NS, n),
            |certificate, signers| certificate.signers = signers,
        );
    }
}
