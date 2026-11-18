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
    if let Some((old, _)) = &l.history {
        if l.history_from_replay && l.ledger.outbox(old.record()).is_none() {
            return None;
        }
        return matches!(old.record().message().map(|m| &m.kind), Some(g::Kind::Recover(row)) if row.report == report)
            .then(|| old.clone());
    }
    let core = l.ledger.core().clone();
    let input = l.ledger.input();
    let authority = proof::<H, _, _>(&core, input, nqc.clone())?;
    let checked = g::entry::verify::<H, _, _, _>(
        rng,
        &l.ledger.verification_context(),
        &core,
        input,
        &authority,
        c.limits,
        bounds(s.participants().len())?,
        |_| None,
        &Sequential,
    )
    .ok()?;
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
    let Event::History {
        entry,
        reservation,
        nqc,
    } = &wal.0
    else {
        return false;
    };
    if let Some((existing, _)) = &l.history {
        return existing == wal;
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
    let Some(authority) = Notarization::decode_cfg(nqc.clone(), &s.certificate_codec_config())
        .ok()
        .and_then(|nqc| proof::<H, _, _>(&core, input, nqc))
    else {
        return false;
    };
    let Some(bounds) = bounds(s.participants().len()) else {
        return false;
    };
    let Ok(checked) = g::entry::verify::<H, _, _, _>(
        rng,
        &l.ledger.verification_context(),
        &core,
        input,
        &authority,
        c.limits,
        bounds,
        |_| None,
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
    let Event::History {
        entry, reservation, ..
    } = &wal.0
    else {
        return None;
    };
    if entry.slot().proposal != q.proposal || entry.input() != q.input || entry.owner() != q.owner {
        return None;
    }
    let g::Kind::Recover(row) = &reservation.message()?.kind else {
        return None;
    };
    let published = l.ledger.outbox(reservation)?;
    if q.head.is_none() {
        return g::Signed::decode_cfg(published.clone(), &super::super::WIRE_LIMITS)
            .ok()
            .map(HistoryMaterial::Notice);
    }
    if row.snapshot.head() != q.head {
        return None;
    }
    if let Some(index) = q.page {
        if index >= usize::try_from(row.snapshot.count()).ok()? {
            return None;
        }
        return Some(HistoryMaterial::Page(l.ledger.history_page(index)?));
    }
    Some(HistoryMaterial::Entry(proof.clone()))
}
