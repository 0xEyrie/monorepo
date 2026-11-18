//! Canonical cohort derivation, not native election or admission authority.
use super::*;
use commonware_consensus::simplex::extension::agreement::general as g;

fn slot(f: &Fixture<S>, view: u64) -> g::Slot<Digest> {
    g::Slot {
        profile: Digest::from([170; 32]),
        domain: Digest::from([171; 32]),
        roster: g::Slot::roster::<Sha256, _>(&f.verifier),
        cut: 29,
        proposal: Proposal::new(round(view), View::zero(), Digest::from([172; 32])),
        parent: g::NativeParent::Genesis(Digest::from([173; 32])),
    }
}

// Explicitly enumerates small cohorts; production never enumerates combinations.
fn enumerate(owners: &[Participant], need: usize) -> Vec<Vec<Participant>> {
    if need == 0 {
        return vec![vec![]];
    }
    if owners.len() < need {
        return vec![];
    }
    let mut all = Vec::new();
    for (i, owner) in owners.iter().enumerate() {
        for tail in enumerate(&owners[i + 1..], need - 1) {
            let mut value = vec![*owner];
            value.extend(tail);
            all.push(value);
        }
    }
    all
}

// Independent Pascal recurrence for large-roster period checks.
fn count(n: usize, k: usize) -> u64 {
    if k > n {
        return 0;
    }
    let mut row = vec![0u64; n + 1];
    row[0] = 1;
    for i in 1..=n {
        for j in (1..=i).rev() {
            row[j] = row[j].checked_add(row[j - 1]).unwrap();
        }
    }
    row[k]
}

// Inverse lexicographic rank via the independent Pascal counts.
fn rank(owners: &[Participant], chosen: &[Participant]) -> u64 {
    let reverse: u64 = chosen
        .iter()
        .enumerate()
        .map(|(i, owner)| {
            let position = owners.binary_search(owner).unwrap();
            count(owners.len() - 1 - position, chosen.len() - i)
        })
        .sum();
    count(owners.len(), chosen.len()) - 1 - reverse
}

#[test]
fn derived_core_matches_independent_small_cohort_enumeration() {
    for n in 4usize..=13 {
        let f = fixture(n as u32);
        let c = g::Committee::new(n).unwrap();
        for leader in [0, n / 2, n - 1] {
            let leader = Participant::new(leader as u32);
            let owners: Vec<_> = (0..n as u32)
                .map(Participant::new)
                .filter(|owner| *owner != leader)
                .collect();
            let oracle = enumerate(&owners, c.quorum() - 1);
            assert_eq!(oracle.len() as u64, count(n - 1, c.quorum() - 1));
            for (rank, expected) in oracle.iter().enumerate() {
                let view = oracle.len() as u64 + rank as u64;
                let captured = slot(&f, view);
                let core =
                    g::Core::derive::<Sha256, _>(&f.verifier, captured.clone(), leader).unwrap();
                assert_eq!(core.slot, captured);
                assert_eq!(core.leader, leader);
                assert_eq!(&core.followers, expected);
            }
        }
    }
}

#[test]
fn derivation_covers_general_roster_capacity_and_slack_quorums() {
    for n in 4usize..=64 {
        let f = fixture(n as u32);
        let c = g::Committee::new(n).unwrap();
        let period = count(n - 1, c.quorum() - 1);
        for leader in [0, n / 2, n - 1] {
            let leader = Participant::new(leader as u32);
            let owners: Vec<_> = (0..n as u32)
                .map(Participant::new)
                .filter(|owner| *owner != leader)
                .collect();
            let first =
                g::Core::derive::<Sha256, _>(&f.verifier, slot(&f, period), leader).unwrap();
            assert_eq!(first.followers, owners[..c.quorum() - 1]);
            let last =
                g::Core::derive::<Sha256, _>(&f.verifier, slot(&f, period - 1), leader).unwrap();
            assert_eq!(last.followers, owners[owners.len() - (c.quorum() - 1)..]);
            for view in [1, period / 2, period - 1, period, period + 1, u64::MAX] {
                let a = g::Core::derive::<Sha256, _>(&f.verifier, slot(&f, view), leader).unwrap();
                assert_eq!(rank(&owners, &a.followers), view % period);
                let equivalent = view % period + period;
                let b = g::Core::derive::<Sha256, _>(&f.verifier, slot(&f, equivalent), leader)
                    .unwrap();
                assert_eq!(a.followers, b.followers);
                assert_eq!(a.followers.len() + 1, c.quorum());
                assert!(!a.followers.contains(&leader));
                assert!(a.followers.windows(2).all(|w| w[0] < w[1]));
            }
        }
    }
}

#[test]
fn derivation_rejects_foreign_roster_invalid_parent_or_leader() {
    let f = fixture(10);
    let native = slot(&f, 4);
    assert_eq!(
        g::Core::derive::<Sha256, _>(&f.verifier, native.clone(), Participant::new(10)),
        Err(g::Error::Identity)
    );
    let mut foreign = native.clone();
    foreign.roster = Digest::from([0; 32]);
    assert_eq!(
        g::Core::derive::<Sha256, _>(&f.verifier, foreign, Participant::new(0)),
        Err(g::Error::Context)
    );
    let mut wrong_parent = native;
    wrong_parent.proposal.parent = View::new(3);
    assert_eq!(
        g::Core::derive::<Sha256, _>(&f.verifier, wrong_parent, Participant::new(0)),
        Err(g::Error::Context)
    );
    for n in [3, 65] {
        let f = fixture(n);
        assert_eq!(
            g::Core::derive::<Sha256, _>(&f.verifier, slot(&f, 1), Participant::new(0)),
            Err(g::Error::Roster)
        );
    }
}

#[test]
fn seven_node_period_is_fifteen_without_general_cohort_fairness_claim() {
    let f = fixture(7);
    let leader = Participant::new(3);
    let mut seen = std::collections::BTreeSet::new();
    for view in 1..=15 {
        let core = g::Core::derive::<Sha256, _>(&f.verifier, slot(&f, view), leader).unwrap();
        seen.insert(core.followers);
    }
    assert_eq!(seen.len(), 15);
    assert_eq!(count(9, 6), 84);
    assert_eq!(count(11, 8), 165);
    // Some larger round-robin steps share a factor with the cohort period.
    // Recovery progress must not assume that a leader visits every cohort.
    let period = count(9, 6);
    let ranks: std::collections::BTreeSet<_> = (0..period).map(|i| i * 10 % period).collect();
    assert_eq!(ranks.len(), 42);
    let period = count(11, 8);
    let ranks: std::collections::BTreeSet<_> = (0..period).map(|i| i * 12 % period).collect();
    assert_eq!(ranks.len(), 55);
}
