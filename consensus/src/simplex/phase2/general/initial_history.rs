//! Initial recovery for a live notarized proposal. Native owns the fence and outbox.
use super::*;
use crate::simplex::types::Notarization;

fn proof<H, S, D>(
    core: &g::Core<D>,
    input: D,
    nqc: Notarization<S, D>,
) -> Option<g::entry::Proof<S, D>>
where
    H: Hasher<Digest = D>,
    S: scheme::Scheme<D>,
    D: Digest,
{
    if nqc.proposal != core.slot.proposal {
        return None;
    }
    let round = nqc.proposal.round;
    Some(g::entry::Proof::Initial {
        target: g::entry::Target {
            core: core.id::<H>(),
            input,
            attempt: 0,
            ballot: Round::new(round.epoch(), View::new(round.view().get().checked_add(1)?)),
            leader: Participant::new(0),
        },
        notarization: nqc,
    })
}

fn bounds(n: usize) -> Option<g::entry::Bounds> {
    Some(g::entry::Bounds {
        nodes: 1,
        depth: 0,
        signatures: n.try_into().ok()?,
        encoded_bytes: g::MAX_EVIDENCE_BYTES as u64,
    })
}

pub(super) fn verify_entry<'a, H, S, D, R>(
    rng: &mut R,
    s: &S,
    c: &Context<S, D>,
    ledger: &g::issuance::State<S, D>,
    core: &'a g::Core<D>,
    proof: &'a g::entry::Proof<S, D>,
) -> Option<g::entry::VerifiedEntry<'a, S, D>>
where
    H: Hasher<Digest = D>,
    S: scheme::Scheme<D>,
    D: Digest,
    R: CryptoRng,
    S::Certificate: g::normal::CertificateSigners,
{
    g::entry::verify::<H, _, _, _>(
        rng,
        &ledger.verification_context(),
        core,
        ledger.input(),
        proof,
        c.limits,
        bounds(s.participants().len())?,
        |_| None,
        &Sequential,
    )
    .ok()
}

pub(super) fn stage<H, S, D, R>(
    s: &S,
    c: &Context<S, D>,
    rng: &mut R,
    l: &mut SlotLedger<S, D>,
    nqc: &Notarization<S, D>,
    report: Option<Bytes>,
) -> Option<Wal<S, D>>
where
    H: Hasher<Digest = D>,
    S: scheme::Scheme<D>,
    D: Digest,
    R: CryptoRng,
    S::Certificate: g::normal::CertificateSigners,
{
    if let Some((old, prior)) = &l.history {
        if prior.target().attempt != 0 {
            return None;
        }
        if l.history_from_replay && l.ledger.outbox(old.record()).is_none() {
            return None;
        }
        return matches!(old.record().message().map(|m| &m.kind), Some(g::Kind::Recover(row)) if row.report == report)
            .then(|| old.clone());
    }
    let core = l.ledger.core().clone();
    let input = l.ledger.input();
    let authority = proof::<H, _, _>(&core, input, nqc.clone())?;
    let checked = verify_entry::<H, _, _, _>(rng, s, c, &l.ledger, &core, &authority)?;
    if report
        .as_ref()
        .is_some_and(|r| r.len() > c.limits.report_bytes)
    {
        return None;
    }
    // Slot geometry bounds both records, their release, and the original NQC
    // before any mutation of the sole issuance ledger.
    let max_records = g::MAX_FIRST_BYTES
        .checked_mul(4)?
        .checked_add(2 * core.encode_size())?;
    if nqc.encode_size().checked_add(max_records)? > super::super::voting_wal::MAX_WAL_BYTES {
        return None;
    }
    if l.ledger.records().len().checked_add(3)? > c.resources.records_per_slot {
        return None;
    }
    let entry = l.ledger.enter::<H>(&checked).ok()?;
    let reservation = l
        .ledger
        .reserve_recover::<H>(&checked, report)
        .expect("admitted initial entry must reserve its bounded first history");
    let wal = Wal(Event::History {
        entry,
        reservation,
        nqc: nqc.encode(),
    });
    l.history = Some((wal.clone(), authority));
    Some(wal)
}

// The provider owns retention; its return value grants no vote.
fn originals<S: scheme::Scheme<D>, D: Digest>(
    c: &Context<S, D>,
    root: D,
) -> Option<(g::entry::Bounds, BTreeMap<D, g::entry::Proof<S, D>>)> {
    let (budget, reader) = c.entry_reader.as_ref()?;
    let graph = reader(root)?;
    if graph.len() > budget.nodes as usize || !graph.contains_key(&root) {
        return None;
    }
    Some((*budget, graph))
}

pub(super) fn stage_higher<H, S, D, R>(
    _s: &S,
    c: &Context<S, D>,
    rng: &mut R,
    l: &mut SlotLedger<S, D>,
    id: D,
    report: Option<Bytes>,
) -> Option<Wal<S, D>>
where
    H: Hasher<Digest = D>,
    S: scheme::Scheme<D>,
    D: Digest,
    R: CryptoRng,
    S::Certificate: g::normal::CertificateSigners,
{
    let (prior, previous) = l.history.as_ref()?;
    if previous.artifact_id::<H>() == id {
        if l.history_from_replay && l.ledger.outbox(prior.record()).is_none() {
            return None;
        }
        return matches!(prior.record().message().map(|m| &m.kind),Some(g::Kind::Recover(row)) if row.report==report && previous.target().attempt>0).then(||prior.clone());
    }
    let (budget, graph) = originals(c, id)?;
    let proof = graph.get(&id)?;
    if proof.target().attempt <= previous.target().attempt
        || report
            .as_ref()
            .is_some_and(|raw| raw.len() > c.limits.report_bytes)
        || l.ledger.records().len().checked_add(3)? > c.resources.records_per_slot
    {
        return None;
    }
    let core = l.ledger.core().clone();
    let checked = g::entry::verify::<H, _, _, _>(
        rng,
        &l.ledger.verification_context(),
        &core,
        l.ledger.input(),
        proof,
        c.limits,
        budget,
        |key| graph.get(key),
        &Sequential,
    )
    .ok()?;
    if checked.artifact_id() != id || !matches!(proof, g::entry::Proof::Higher { .. }) {
        return None;
    }
    let entry = l.ledger.enter::<H>(&checked).ok()?;
    let reservation = l
        .ledger
        .reserve_recover::<H>(&checked, report)
        .expect("entered verified successor must reserve its bounded history");
    let wal = Wal(Event::HigherHistory { entry, reservation });
    l.history = Some((wal.clone(), proof.clone()));
    l.history_from_replay = false;
    Some(wal)
}

pub(super) fn replay<H, S, D, R>(
    s: &S,
    c: &Context<S, D>,
    rng: &mut R,
    l: &mut SlotLedger<S, D>,
    wal: &Wal<S, D>,
) -> bool
where
    H: Hasher<Digest = D>,
    S: scheme::Scheme<D>,
    D: Digest,
    R: CryptoRng,
    S::Certificate: g::normal::CertificateSigners,
{
    let (entry, reservation, initial) = match &wal.0 {
        Event::History {
            entry,
            reservation,
            nqc,
        } => (entry, reservation, Some(nqc)),
        Event::HigherHistory { entry, reservation } => (entry, reservation, None),
        _ => return false,
    };
    if let Some((existing, _)) = &l.history {
        if existing == wal {
            return true;
        }
        if initial.is_some() {
            return false;
        }
    } else if initial.is_none() {
        return false;
    }
    if !matches!(entry.action(), g::issuance::Action::Enter { .. })
        || !matches!(
            reservation.message().map(|m| &m.kind),
            Some(g::Kind::Recover(_))
        )
    {
        return false;
    }
    let core = l.ledger.core().clone();
    let input = l.ledger.input();
    let (authority, graph, budget) = if let Some(nqc) = initial {
        let Some(p) = Notarization::decode_cfg(nqc.clone(), &s.certificate_codec_config())
            .ok()
            .and_then(|nqc| proof::<H, _, _>(&core, input, nqc))
        else {
            return false;
        };
        let Some(budget) = bounds(s.participants().len()) else {
            return false;
        };
        (p, BTreeMap::new(), budget)
    } else {
        let g::issuance::Action::Enter { authority: id, .. } = entry.action() else {
            return false;
        };
        let Some((budget, graph)) = originals(c, *id) else {
            return false;
        };
        let Some(p) = graph.get(id) else { return false };
        if !matches!(p, g::entry::Proof::Higher { .. })
            || l.history
                .as_ref()
                .is_none_or(|(_, old)| old.target().attempt >= p.target().attempt)
        {
            return false;
        }
        (p.clone(), graph, budget)
    };
    let Ok(checked) = g::entry::verify::<H, _, _, _>(
        rng,
        &l.ledger.verification_context(),
        &core,
        input,
        &authority,
        c.limits,
        budget,
        |key| graph.get(key),
        &Sequential,
    ) else {
        return false;
    };
    replay_room(c, l, &[entry, reservation]);
    for record in [entry, reservation] {
        if l.ledger
            .restore::<H, _>(
                rng,
                record,
                g::issuance::Material::Entry(&checked),
                |_| false,
                |_, _| false,
                &Sequential,
            )
            .is_err()
        {
            return false;
        }
    }
    l.history = Some((wal.clone(), authority));
    l.history_from_replay = true;
    true
}

pub(super) fn material<S, D>(
    l: &SlotLedger<S, D>,
    q: &HistoryQuery<D>,
) -> Option<HistoryMaterial<S, D>>
where
    S: scheme::Scheme<D>,
    D: Digest,
    S::Certificate: g::normal::CertificateSigners,
{
    let (wal, proof) = l.history.as_ref()?;
    let (entry, reservation) = match &wal.0 {
        Event::History {
            entry, reservation, ..
        }
        | Event::HigherHistory { entry, reservation } => (entry, reservation),
        _ => return None,
    };
    if entry.slot().proposal != q.proposal || entry.input() != q.input || entry.owner() != q.owner {
        return None;
    }
    let g::Kind::Recover(row) = &reservation.message()?.kind else {
        return None;
    };
    let published = l.ledger.outbox(reservation)?;
    match &q.item {
        HistoryItem::Notice => g::Signed::decode_cfg(published.clone(), &super::super::WIRE_LIMITS)
            .ok()
            .map(HistoryMaterial::Notice),
        HistoryItem::Entry(head) if row.snapshot.head() == Some(*head) => {
            Some(HistoryMaterial::Entry(proof.clone()))
        }
        HistoryItem::Page(head, index) if row.snapshot.head() == Some(*head) => {
            if *index >= usize::try_from(row.snapshot.count()).ok()? {
                return None;
            }
            Some(HistoryMaterial::Page(l.ledger.history_page(*index)?))
        }
        HistoryItem::Verification(head) if row.snapshot.head() == Some(*head) => Some(
            HistoryMaterial::Verification(l.ledger.verification_context()),
        ),
        _ => None,
    }
}
