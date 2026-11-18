//! Versioned cryptographic evidence for the seven-validator extension profile.
//!
//! Ordinary P notarization remains independent of the fixed report cohort.
//! These types do not authorize a native view, terminal delivery, or signing
//! before the voter's durable reservation. Application selection verification
//! must replay the fixed deterministic rule and check all hard input constraints.

use crate::{
    simplex::{
        scheme,
        types::{Proposal, Subject},
    },
    types::{Participant, Round},
};
use bytes::{BufMut, Bytes};
use commonware_codec::{
    Buf, Encode as _, EncodeSize, Error as CodecError, Read, ReadExt as _, Write,
};
use commonware_cryptography::{
    Digest, Hasher,
    certificate::{self, Attestation, Scoped, Verifier as _},
};
use commonware_parallel::Strategy;
use commonware_utils::{iter::NonEmpty, ordered::Set};
use rand_core::CryptoRng;
use std::collections::BTreeSet;

pub mod general;
pub mod issuance;
pub mod normal;
pub mod recovery;

pub(crate) const SIGNING_TAG: &[u8] = b"_COMMONWARE_CONSENSUS_SIMPLEX_EXTENSION_AGREEMENT_V2";
const ROSTER_TAG: &[u8] = b"_COMMONWARE_CONSENSUS_SIMPLEX_AGREEMENT_ROSTER_V2";
const SLOT_TAG: &[u8] = b"_COMMONWARE_CONSENSUS_SIMPLEX_AGREEMENT_SLOT_V2";
const CORE_TAG: &[u8] = b"_COMMONWARE_CONSENSUS_SIMPLEX_AGREEMENT_CORE_V2";
const ROW_TAG: &[u8] = b"_COMMONWARE_CONSENSUS_SIMPLEX_AGREEMENT_ROW_V2";
const VALUE_TAG: &[u8] = b"_COMMONWARE_CONSENSUS_SIMPLEX_AGREEMENT_VALUE_V2";

// A captured verifier-only scope supplies exactly the same read-only checks as
// the epoch scheme. Neither branch exposes a signer to proof verification.
enum VerificationSource<'a, S: certificate::Scheme> {
    Scheme(&'a S),
    Scoped(&'a Scoped<S>),
}
impl<S: certificate::Scheme> VerificationSource<'_, S> {
    fn participants(&self) -> &Set<S::PublicKey> {
        match self {
            Self::Scheme(scheme) => scheme.participants(),
            Self::Scoped(scoped) => scoped.participants(),
        }
    }
    fn roster<H: Hasher>(&self) -> H::Digest {
        H::hash(&[
            ROSTER_TAG,
            &self
                .participants()
                .iter()
                .cloned()
                .collect::<Vec<_>>()
                .encode(),
        ])
    }
    fn verify_attestation<R: CryptoRng, D: Digest>(
        &self,
        rng: &mut R,
        subject: Subject<'_, D>,
        attestation: &Attestation<S>,
        strategy: &impl Strategy,
    ) -> bool
    where
        S: scheme::Scheme<D>,
    {
        match self {
            Self::Scheme(scheme) => {
                scheme.verify_attestation::<_, D>(rng, subject, attestation, strategy)
            }
            Self::Scoped(scoped) => {
                scoped.verify_attestation::<_, D>(rng, subject, attestation, strategy)
            }
        }
    }
    fn verify_certificate<R: CryptoRng, D: Digest>(
        &self,
        rng: &mut R,
        subject: Subject<'_, D>,
        certificate: &S::Certificate,
        strategy: &impl Strategy,
    ) -> bool
    where
        S: scheme::Scheme<D>,
    {
        match self {
            Self::Scheme(scheme) => {
                scheme.verify_certificate::<_, D>(rng, subject, certificate, strategy)
            }
            Self::Scoped(scoped) => {
                scoped.verify_certificate::<_, D>(rng, subject, certificate, strategy)
            }
        }
    }
}

/// Per-field decoding limits. They must agree with the authenticated deployment.
/// Complete recovery history is referenced in pages, not truncated to these bounds.
#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub report_bytes: usize,
    pub direction_bytes: usize,
}

/// Stable logical cut, separate from a later elected carrier's round.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Slot<D: Digest> {
    /// Protocol, codec, genesis, runtime and hard-order configuration.
    pub domain: D,
    /// Ordered epoch validator roster commitment.
    pub roster: D,
    /// Selector version, parameters and deterministic work budget.
    pub selector: D,
    /// Stable application cut number; a retry must not allocate a new cut.
    pub cut: u64,
    /// Exact original P, retaining its original native coordinates.
    pub proposal: Proposal<D>,
    /// Exact immutable execution interpretation of the original parent.
    pub parent: D,
}
impl<D: Digest> Slot<D> {
    pub fn id<H: Hasher<Digest = D>>(&self) -> D {
        H::hash(&[SLOT_TAG, &self.encode()])
    }
    pub fn roster<H: Hasher<Digest = D>, S: certificate::Scheme>(scheme: &S) -> D {
        VerificationSource::Scheme(scheme).roster::<H>()
    }
    pub fn check_roster<H: Hasher<Digest = D>, S: certificate::Scheme>(
        &self,
        scheme: &S,
    ) -> Result<(), Error> {
        self.check_roster_with::<H, S>(&VerificationSource::Scheme(scheme))
    }
    fn check_roster_with<H: Hasher<Digest = D>, S: certificate::Scheme>(
        &self,
        source: &VerificationSource<'_, S>,
    ) -> Result<(), Error> {
        if source.participants().len() != 7 || !S::is_attributable() {
            return Err(Error::Roster);
        }
        if self.roster != source.roster::<H>() {
            return Err(Error::Context);
        }
        Ok(())
    }
}
impl<D: Digest> Write for Slot<D> {
    fn write(&self, w: &mut impl BufMut) {
        2u8.write(w);
        self.domain.write(w);
        self.roster.write(w);
        self.selector.write(w);
        self.cut.write(w);
        self.proposal.write(w);
        self.parent.write(w);
    }
}
impl<D: Digest> EncodeSize for Slot<D> {
    fn encode_size(&self) -> usize {
        1 + self.domain.encode_size()
            + self.roster.encode_size()
            + self.selector.encode_size()
            + self.cut.encode_size()
            + self.proposal.encode_size()
            + self.parent.encode_size()
    }
}
impl<D: Digest> Read for Slot<D> {
    type Cfg = ();
    fn read_cfg(r: &mut impl Buf, _: &()) -> Result<Self, CodecError> {
        if u8::read(r)? != 2 {
            return Err(CodecError::Invalid("agreement slot", "version"));
        }
        Ok(Self {
            domain: D::read(r)?,
            roster: D::read(r)?,
            selector: D::read(r)?,
            cut: u64::read(r)?,
            proposal: Proposal::read(r)?,
            parent: D::read(r)?,
        })
    }
}

/// The original leader plus four fixed nonleader report origins.
/// This is not the signer family of native P notarization or final certificates.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Core<D: Digest> {
    pub slot: Slot<D>,
    pub leader: Participant,
    /// Strictly ascending, distinct and excluding the leader.
    pub followers: [Participant; 4],
    /// Commitment to the leader's exact ready row or explicit absence.
    pub leader_report: D,
}
impl<D: Digest> Core<D> {
    pub fn id<H: Hasher<Digest = D>>(&self) -> D {
        H::hash(&[CORE_TAG, &self.encode()])
    }
    pub fn row<H: Hasher<Digest = D>>(report: &Option<Bytes>) -> D {
        H::hash(&[ROW_TAG, &report.encode()])
    }
    pub fn check<H: Hasher<Digest = D>, S: certificate::Scheme>(
        &self,
        scheme: &S,
        expected: &Slot<D>,
        leader: Participant,
    ) -> Result<(), Error> {
        self.check_with::<H, S>(&VerificationSource::Scheme(scheme), expected, leader)
    }
    fn check_with<H: Hasher<Digest = D>, S: certificate::Scheme>(
        &self,
        source: &VerificationSource<'_, S>,
        expected: &Slot<D>,
        leader: Participant,
    ) -> Result<(), Error> {
        expected.check_roster_with::<H, S>(source)?;
        if self.slot != *expected
            || self.leader != leader
            || usize::from(leader) >= 7
            || self
                .followers
                .iter()
                .any(|id| usize::from(*id) >= 7 || *id == leader)
            || self.followers.windows(2).any(|pair| pair[0] >= pair[1])
        {
            return Err(Error::Context);
        }
        Ok(())
    }
}
impl<D: Digest> Write for Core<D> {
    fn write(&self, w: &mut impl BufMut) {
        self.slot.write(w);
        self.leader.write(w);
        for id in self.followers {
            id.write(w);
        }
        self.leader_report.write(w);
    }
}
impl<D: Digest> EncodeSize for Core<D> {
    fn encode_size(&self) -> usize {
        self.slot.encode_size()
            + self.leader.encode_size()
            + self
                .followers
                .iter()
                .map(EncodeSize::encode_size)
                .sum::<usize>()
            + self.leader_report.encode_size()
    }
}
impl<D: Digest> Read for Core<D> {
    type Cfg = ();
    fn read_cfg(r: &mut impl Buf, _: &()) -> Result<Self, CodecError> {
        Ok(Self {
            slot: Slot::read(r)?,
            leader: Participant::read(r)?,
            followers: [
                Participant::read(r)?,
                Participant::read(r)?,
                Participant::read(r)?,
                Participant::read(r)?,
            ],
            leader_report: D::read(r)?,
        })
    }
}

/// Semantic report contents. Signatures are deliberately outside value identity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Row {
    pub owner: Participant,
    pub report: Option<Bytes>,
}
impl Write for Row {
    fn write(&self, w: &mut impl BufMut) {
        self.owner.write(w);
        self.report.write(w);
    }
}
impl EncodeSize for Row {
    fn encode_size(&self) -> usize {
        self.owner.encode_size() + self.report.encode_size()
    }
}
impl Read for Row {
    type Cfg = usize;
    fn read_cfg(r: &mut impl Buf, limit: &usize) -> Result<Self, CodecError> {
        Ok(Self {
            owner: Participant::read(r)?,
            report: Option::<Bytes>::read_cfg(r, &(0..=*limit).into())?,
        })
    }
}

/// Original report context, preserved unchanged through later carrier ballots.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Origin<D: Digest> {
    Fast(D),
    Recovery { round: Round, leader: Participant },
}
impl<D: Digest> Write for Origin<D> {
    fn write(&self, w: &mut impl BufMut) {
        match self {
            Self::Fast(core) => {
                0u8.write(w);
                core.write(w);
            }
            Self::Recovery { round, leader } => {
                1u8.write(w);
                round.write(w);
                leader.write(w);
            }
        }
    }
}
impl<D: Digest> EncodeSize for Origin<D> {
    fn encode_size(&self) -> usize {
        1 + match self {
            Self::Fast(d) => d.encode_size(),
            Self::Recovery { round, leader } => round.encode_size() + leader.encode_size(),
        }
    }
}
impl<D: Digest> Read for Origin<D> {
    type Cfg = ();
    fn read_cfg(r: &mut impl Buf, _: &()) -> Result<Self, CodecError> {
        match u8::read(r)? {
            0 => Ok(Self::Fast(D::read(r)?)),
            1 => Ok(Self::Recovery {
                round: Round::read(r)?,
                leader: Participant::read(r)?,
            }),
            _ => Err(CodecError::Invalid("agreement origin", "kind")),
        }
    }
}

/// One exact decision. Equal directions with different original reports differ.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Value<D: Digest> {
    pub slot: Slot<D>,
    pub origin: Origin<D>,
    /// Exactly five distinct original rows, in ascending participant order.
    pub reports: Vec<Row>,
    pub direction: Bytes,
}
impl<D: Digest> Value<D> {
    pub fn id<H: Hasher<Digest = D>>(&self) -> D {
        H::hash(&[VALUE_TAG, &self.encode()])
    }
    pub fn check(&self, limits: Limits) -> Result<(), Error> {
        if self.reports.len() != 5
            || self.direction.len() > limits.direction_bytes
            || self.reports.iter().any(|row| {
                usize::from(row.owner) >= 7
                    || row
                        .report
                        .as_ref()
                        .is_some_and(|b| b.len() > limits.report_bytes)
            })
            || self
                .reports
                .windows(2)
                .any(|pair| pair[0].owner >= pair[1].owner)
        {
            return Err(Error::Value);
        }
        Ok(())
    }
}
impl<D: Digest> Write for Value<D> {
    fn write(&self, w: &mut impl BufMut) {
        self.slot.write(w);
        self.origin.write(w);
        self.reports.write(w);
        self.direction.write(w);
    }
}
impl<D: Digest> EncodeSize for Value<D> {
    fn encode_size(&self) -> usize {
        self.slot.encode_size()
            + self.origin.encode_size()
            + self.reports.encode_size()
            + self.direction.encode_size()
    }
}
impl<D: Digest> Read for Value<D> {
    type Cfg = Limits;
    fn read_cfg(r: &mut impl Buf, limits: &Limits) -> Result<Self, CodecError> {
        Ok(Self {
            slot: Slot::read(r)?,
            origin: Origin::read(r)?,
            reports: Vec::<Row>::read_cfg(r, &((0..=7).into(), limits.report_bytes))?,
            direction: Bytes::read_cfg(r, &(0..=limits.direction_bytes).into())?,
        })
    }
}

/// Phase-separated operation. A PREPARE authorization cannot count as COMMIT.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Kind<D: Digest> {
    First {
        core: D,
        report: Option<Bytes>,
    },
    Select {
        core: D,
        value: D,
    },
    FastFinal(D),
    Prepare(D),
    Commit(D),
    Recover {
        history: Option<D>,
        report: Option<Bytes>,
    },
    /// Leader's exact recovery Value and frozen admission witness commitment.
    Propose {
        proposal: D,
        value: D,
    },
}
impl<D: Digest> Kind<D> {
    pub const fn voted_value(&self) -> Option<D> {
        match self {
            Self::FastFinal(v) | Self::Prepare(v) | Self::Commit(v) => Some(*v),
            _ => None,
        }
    }
}
impl<D: Digest> Write for Kind<D> {
    fn write(&self, w: &mut impl BufMut) {
        match self {
            Self::First { core, report } => {
                0u8.write(w);
                core.write(w);
                report.write(w);
            }
            Self::Select { core, value } => {
                1u8.write(w);
                core.write(w);
                value.write(w);
            }
            Self::FastFinal(v) => {
                2u8.write(w);
                v.write(w);
            }
            Self::Prepare(v) => {
                3u8.write(w);
                v.write(w);
            }
            Self::Commit(v) => {
                4u8.write(w);
                v.write(w);
            }
            Self::Recover { history, report } => {
                5u8.write(w);
                history.write(w);
                report.write(w);
            }
            Self::Propose { proposal, value } => {
                6u8.write(w);
                proposal.write(w);
                value.write(w);
            }
        }
    }
}
impl<D: Digest> EncodeSize for Kind<D> {
    fn encode_size(&self) -> usize {
        1 + match self {
            Self::First { core, report } => core.encode_size() + report.encode_size(),
            Self::Select { core, value } => core.encode_size() + value.encode_size(),
            Self::FastFinal(v) | Self::Prepare(v) | Self::Commit(v) => v.encode_size(),
            Self::Recover { history, report } => history.encode_size() + report.encode_size(),
            Self::Propose { proposal, value } => proposal.encode_size() + value.encode_size(),
        }
    }
}
impl<D: Digest> Read for Kind<D> {
    type Cfg = usize;
    fn read_cfg(r: &mut impl Buf, limit: &usize) -> Result<Self, CodecError> {
        match u8::read(r)? {
            0 => Ok(Self::First {
                core: D::read(r)?,
                report: Option::<Bytes>::read_cfg(r, &(0..=*limit).into())?,
            }),
            1 => Ok(Self::Select {
                core: D::read(r)?,
                value: D::read(r)?,
            }),
            2 => Ok(Self::FastFinal(D::read(r)?)),
            3 => Ok(Self::Prepare(D::read(r)?)),
            4 => Ok(Self::Commit(D::read(r)?)),
            5 => Ok(Self::Recover {
                history: Option::<D>::read(r)?,
                report: Option::<Bytes>::read_cfg(r, &(0..=*limit).into())?,
            }),
            6 => Ok(Self::Propose {
                proposal: D::read(r)?,
                value: D::read(r)?,
            }),
            _ => Err(CodecError::Invalid("agreement message", "kind")),
        }
    }
}

/// Exact authenticated carrier subject; it never rewrites a carried Value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Message<D: Digest> {
    pub slot: D,
    pub round: Round,
    pub leader: Participant,
    pub kind: Kind<D>,
}
impl<D: Digest> Write for Message<D> {
    fn write(&self, w: &mut impl BufMut) {
        2u8.write(w);
        self.slot.write(w);
        self.round.write(w);
        self.leader.write(w);
        self.kind.write(w);
    }
}
impl<D: Digest> EncodeSize for Message<D> {
    fn encode_size(&self) -> usize {
        1 + self.slot.encode_size()
            + self.round.encode_size()
            + self.leader.encode_size()
            + self.kind.encode_size()
    }
}
impl<D: Digest> Read for Message<D> {
    type Cfg = usize;
    fn read_cfg(r: &mut impl Buf, limit: &usize) -> Result<Self, CodecError> {
        if u8::read(r)? != 2 {
            return Err(CodecError::Invalid("agreement message", "version"));
        }
        Ok(Self {
            slot: D::read(r)?,
            round: Round::read(r)?,
            leader: Participant::read(r)?,
            kind: Kind::read_cfg(r, limit)?,
        })
    }
}

/// Individual attributable authorization. Calling sign requires a durable reservation.
#[derive(Clone, Debug)]
pub struct Signed<S: certificate::Scheme, D: Digest> {
    pub message: Message<D>,
    pub attestation: Attestation<S>,
}
impl<S: scheme::Scheme<D>, D: Digest> Signed<S, D> {
    pub fn sign(scheme: &S, message: Message<D>) -> Result<Self, Error> {
        if scheme.participants().len() != 7 || !S::is_attributable() {
            return Err(Error::Roster);
        }
        let bytes = message.encode();
        let attestation = scheme
            .sign::<D>(Subject::ExtensionAgreement {
                round: message.round,
                payload: &bytes,
            })
            .ok_or(Error::Signature)?;
        Ok(Self {
            message,
            attestation,
        })
    }
    pub fn verify<R: CryptoRng>(&self, rng: &mut R, scheme: &S, strategy: &impl Strategy) -> bool {
        self.verify_with(rng, &VerificationSource::Scheme(scheme), strategy)
    }
    fn verify_with<R: CryptoRng>(
        &self,
        rng: &mut R,
        source: &VerificationSource<'_, S>,
        strategy: &impl Strategy,
    ) -> bool {
        let bytes = self.message.encode();
        source.participants().len() == 7
            && S::is_attributable()
            && usize::from(self.message.leader) < 7
            && source.verify_attestation::<_, D>(
                rng,
                Subject::ExtensionAgreement {
                    round: self.message.round,
                    payload: &bytes,
                },
                &self.attestation,
                strategy,
            )
    }
}
impl<S: certificate::Scheme, D: Digest> Write for Signed<S, D> {
    fn write(&self, w: &mut impl BufMut) {
        self.message.write(w);
        self.attestation.write(w);
    }
}
impl<S: certificate::Scheme, D: Digest> EncodeSize for Signed<S, D> {
    fn encode_size(&self) -> usize {
        self.message.encode_size() + self.attestation.encode_size()
    }
}
impl<S: certificate::Scheme, D: Digest> Read for Signed<S, D> {
    type Cfg = usize;
    fn read_cfg(r: &mut impl Buf, limit: &usize) -> Result<Self, CodecError> {
        Ok(Self {
            message: Message::read_cfg(r, limit)?,
            attestation: Attestation::read(r)?,
        })
    }
}

/// Five signatures over one phase and exact value. Not terminal authority alone.
#[derive(Clone, Debug)]
pub struct Quorum<S: certificate::Scheme, D: Digest> {
    pub message: Message<D>,
    pub certificate: S::Certificate,
}
impl<S: scheme::Scheme<D>, D: Digest> Quorum<S, D> {
    pub fn from_votes<R: CryptoRng, I: Iterator<Item = Signed<S, D>> + Send>(
        rng: &mut R,
        scheme: &S,
        votes: NonEmpty<I>,
        strategy: &impl Strategy,
    ) -> Result<Self, Error> {
        let (first, rest) = votes.into_parts();
        if first.message.kind.voted_value().is_none() {
            return Err(Error::Phase);
        }
        let mut ids = BTreeSet::new();
        let mut signatures = Vec::new();
        for vote in std::iter::once(first.clone()).chain(rest) {
            if vote.message != first.message || !ids.insert(vote.attestation.signer) {
                return Err(Error::Identity);
            }
            if !vote.verify(rng, scheme, strategy) {
                return Err(Error::Signature);
            }
            signatures.push(vote.attestation);
        }
        let mut signatures = signatures.into_iter();
        let first_signature = signatures.next().expect("nonempty votes");
        let certificate = scheme
            .assemble(NonEmpty::new(first_signature, signatures), strategy)
            .map_err(|_| Error::Quorum)?;
        Ok(Self {
            message: first.message,
            certificate,
        })
    }
    pub fn verify<R: CryptoRng>(&self, rng: &mut R, scheme: &S, strategy: &impl Strategy) -> bool {
        self.verify_with(rng, &VerificationSource::Scheme(scheme), strategy)
    }
    fn verify_with<R: CryptoRng>(
        &self,
        rng: &mut R,
        source: &VerificationSource<'_, S>,
        strategy: &impl Strategy,
    ) -> bool {
        let bytes = self.message.encode();
        source.participants().len() == 7
            && S::is_attributable()
            && usize::from(self.message.leader) < 7
            && self.message.kind.voted_value().is_some()
            && source.verify_certificate::<_, D>(
                rng,
                Subject::ExtensionAgreement {
                    round: self.message.round,
                    payload: &bytes,
                },
                &self.certificate,
                strategy,
            )
    }
}
impl<S: certificate::Scheme, D: Digest> Write for Quorum<S, D> {
    fn write(&self, w: &mut impl BufMut) {
        self.message.write(w);
        self.certificate.write(w);
    }
}
impl<S: certificate::Scheme, D: Digest> EncodeSize for Quorum<S, D> {
    fn encode_size(&self) -> usize {
        self.message.encode_size() + self.certificate.encode_size()
    }
}
impl<S: certificate::Scheme, D: Digest> Read for Quorum<S, D> {
    type Cfg = <S::Certificate as Read>::Cfg;
    fn read_cfg(r: &mut impl Buf, cfg: &Self::Cfg) -> Result<Self, CodecError> {
        let message = Message::read_cfg(r, &0)?;
        if message.kind.voted_value().is_none() {
            return Err(CodecError::Invalid("agreement quorum", "phase"));
        }
        Ok(Self {
            message,
            certificate: S::Certificate::read_cfg(r, cfg)?,
        })
    }
}

/// Original two-wave origin proof, retaining all five original FIRST signatures.
#[derive(Clone, Debug)]
pub struct FastProof<S: certificate::Scheme, D: Digest> {
    pub core: Core<D>,
    pub firsts: Vec<Signed<S, D>>,
    pub selection: Signed<S, D>,
    pub value: Value<D>,
}
impl<S: scheme::Scheme<D>, D: Digest> FastProof<S, D> {
    /// Checks the full origin and its final certificate with one trusted verifier.
    /// Retain both complete bodies before publishing terminal delivery.
    #[allow(clippy::too_many_arguments)]
    pub fn verify_finalization<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        scheme: &S,
        expected: &Slot<D>,
        leader: Participant,
        limits: Limits,
        policy: impl FnOnce(&Value<D>) -> bool,
        quorum: &Quorum<S, D>,
        strategy: &impl Strategy,
    ) -> Result<VerifiedFinal<D>, Error> {
        let source = VerificationSource::Scheme(scheme);
        self.verify_with::<H, R>(rng, &source, expected, leader, limits, policy, strategy)?
            .finalize_with(rng, &source, quorum, strategy)
    }

    /// Checks the complete original proof and FAST quorum with a captured scope.
    /// The scope supplies no signing authority; expected Slot, native leader,
    /// policy and complete material custody remain caller prerequisites.
    #[allow(clippy::too_many_arguments)]
    pub fn verify_finalization_scoped<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        scoped: &Scoped<S>,
        expected: &Slot<D>,
        leader: Participant,
        limits: Limits,
        policy: impl FnOnce(&Value<D>) -> bool,
        quorum: &Quorum<S, D>,
        strategy: &impl Strategy,
    ) -> Result<VerifiedFinal<D>, Error> {
        let source = VerificationSource::Scoped(scoped);
        self.verify_with::<H, R>(rng, &source, expected, leader, limits, policy, strategy)?
            .finalize_with(rng, &source, quorum, strategy)
    }

    /// Verifies crypto, the fixed report population, exact semantics and policy.
    /// `leader` comes from native election; policy must replay Select and legality.
    #[allow(clippy::too_many_arguments)]
    pub fn verify<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        scheme: &S,
        expected: &Slot<D>,
        leader: Participant,
        limits: Limits,
        policy: impl FnOnce(&Value<D>) -> bool,
        strategy: &impl Strategy,
    ) -> Result<VerifiedOrigin<D>, Error> {
        self.verify_with::<H, R>(
            rng,
            &VerificationSource::Scheme(scheme),
            expected,
            leader,
            limits,
            policy,
            strategy,
        )
    }

    /// Verifies the full origin using a captured public-only scope.
    /// Exact Slot, native elected leader and deterministic policy are checked
    /// by the same path as scheme-based verification.
    #[allow(clippy::too_many_arguments)]
    pub fn verify_scoped<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        scoped: &Scoped<S>,
        expected: &Slot<D>,
        leader: Participant,
        limits: Limits,
        policy: impl FnOnce(&Value<D>) -> bool,
        strategy: &impl Strategy,
    ) -> Result<VerifiedOrigin<D>, Error> {
        self.verify_with::<H, R>(
            rng,
            &VerificationSource::Scoped(scoped),
            expected,
            leader,
            limits,
            policy,
            strategy,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn verify_with<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        source: &VerificationSource<'_, S>,
        expected: &Slot<D>,
        leader: Participant,
        limits: Limits,
        policy: impl FnOnce(&Value<D>) -> bool,
        strategy: &impl Strategy,
    ) -> Result<VerifiedOrigin<D>, Error> {
        self.core.check_with::<H, S>(source, expected, leader)?;
        self.value.check(limits)?;
        let slot = expected.id::<H>();
        let core = self.core.id::<H>();
        let round = expected.proposal.round;
        if self.value.slot != *expected
            || self.value.origin != Origin::Fast(core)
            || self.firsts.len() != 5
        {
            return Err(Error::Context);
        }
        let mut rows = Vec::new();
        let mut previous = None;
        for first in &self.firsts {
            let owner = first.attestation.signer;
            let Kind::First {
                core: first_core,
                report,
            } = &first.message.kind
            else {
                return Err(Error::Phase);
            };
            if previous.is_some_and(|old| old >= owner)
                || owner != leader && !self.core.followers.contains(&owner)
            {
                return Err(Error::Identity);
            }
            previous = Some(owner);
            if first.message.slot != slot
                || first.message.round != round
                || first.message.leader != leader
                || *first_core != core
                || report
                    .as_ref()
                    .is_some_and(|b| b.len() > limits.report_bytes)
            {
                return Err(Error::Context);
            }
            if owner == leader && Core::<D>::row::<H>(report) != self.core.leader_report {
                return Err(Error::Value);
            }
            if !first.verify_with(rng, source, strategy) {
                return Err(Error::Signature);
            }
            rows.push(Row {
                owner,
                report: report.clone(),
            });
        }
        if self.value.reports != rows
            || self.selection.attestation.signer != leader
            || self.selection.message
                != (Message {
                    slot,
                    round,
                    leader,
                    kind: Kind::Select {
                        core,
                        value: self.value.id::<H>(),
                    },
                })
        {
            return Err(Error::Value);
        }
        if !self.selection.verify_with(rng, source, strategy) {
            return Err(Error::Signature);
        }
        if !policy(&self.value) {
            return Err(Error::Policy);
        }
        Ok(VerifiedOrigin {
            slot,
            core,
            value: self.value.id::<H>(),
            round,
            leader,
            reports: rows,
        })
    }
}
impl<S: certificate::Scheme, D: Digest> Write for FastProof<S, D> {
    fn write(&self, w: &mut impl BufMut) {
        self.core.write(w);
        self.firsts.write(w);
        self.selection.write(w);
        self.value.write(w);
    }
}
impl<S: certificate::Scheme, D: Digest> EncodeSize for FastProof<S, D> {
    fn encode_size(&self) -> usize {
        self.core.encode_size()
            + self.firsts.encode_size()
            + self.selection.encode_size()
            + self.value.encode_size()
    }
}
impl<S: certificate::Scheme, D: Digest> Read for FastProof<S, D> {
    type Cfg = Limits;
    fn read_cfg(r: &mut impl Buf, limits: &Limits) -> Result<Self, CodecError> {
        Ok(Self {
            core: Core::read(r)?,
            firsts: Vec::<Signed<S, D>>::read_cfg(r, &((0..=7).into(), limits.report_bytes))?,
            selection: Signed::read_cfg(r, &0)?,
            value: Value::read_cfg(r, limits)?,
        })
    }
}

/// Checked origin identity, not a final certificate or execution-completion proof.
#[derive(Clone, Debug)]
pub struct VerifiedOrigin<D> {
    slot: D,
    core: D,
    value: D,
    round: Round,
    leader: Participant,
    reports: Vec<Row>,
}
impl<D: Copy> VerifiedOrigin<D> {
    pub const fn slot(&self) -> D {
        self.slot
    }
    pub const fn core(&self) -> D {
        self.core
    }
    pub const fn value(&self) -> D {
        self.value
    }
}
impl<D: Digest> VerifiedOrigin<D> {
    /// Identifies the leader and one nonleader that authenticated semantic forks.
    /// Both origins must have been checked with the same trusted selector/context.
    /// More than two exposed faults exceeds this profile's declared fault budget.
    pub fn faults(&self, other: &Self) -> Result<Option<[Participant; 2]>, Error> {
        if self.slot != other.slot || self.core != other.core {
            return Err(Error::Context);
        }
        if self.value == other.value {
            return Ok(None);
        }
        let mut follower = None;
        for (left, right) in self.reports.iter().zip(&other.reports) {
            if left.owner != right.owner {
                return Err(Error::Identity);
            }
            if left.report == right.report {
                continue;
            }
            if left.owner == self.leader {
                return Err(Error::Context);
            }
            if follower.replace(left.owner).is_some() {
                return Err(Error::FaultBudget);
            }
        }
        let follower = follower.ok_or(Error::Policy)?;
        let mut faults = [self.leader, follower];
        faults.sort();
        Ok(Some(faults))
    }

    /// Binds a checked origin to its exact original FAST_FINAL certificate.
    /// The caller retains both complete proof bodies before terminal delivery.
    fn finalize_with<S: scheme::Scheme<D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        source: &VerificationSource<'_, S>,
        quorum: &Quorum<S, D>,
        strategy: &impl Strategy,
    ) -> Result<VerifiedFinal<D>, Error> {
        if quorum.message
            != (Message {
                slot: self.slot,
                round: self.round,
                leader: self.leader,
                kind: Kind::FastFinal(self.value),
            })
        {
            return Err(Error::Context);
        }
        if !quorum.verify_with(rng, source, strategy) {
            return Err(Error::Signature);
        }
        Ok(VerifiedFinal {
            slot: self.slot,
            value: self.value,
        })
    }
}

/// Exact checked fast terminal identity. It neither proves execution nor owns ACK.
/// Complete witness custody, native ancestry and durable delivery are still required.
#[derive(Clone, Debug)]
pub struct VerifiedFinal<D> {
    slot: D,
    value: D,
}
impl<D: Copy> VerifiedFinal<D> {
    pub const fn slot(&self) -> D {
        self.slot
    }
    pub const fn value(&self) -> D {
        self.value
    }
}

/// Verification failure. None permits base/identity finality substitution.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Error {
    #[error("agreement requires seven attributable validators")]
    Roster,
    #[error("wrong agreement context")]
    Context,
    #[error("invalid agreement value")]
    Value,
    #[error("invalid agreement identity population")]
    Identity,
    #[error("invalid agreement signature")]
    Signature,
    #[error("invalid agreement quorum")]
    Quorum,
    #[error("wrong agreement phase")]
    Phase,
    #[error("deterministic selection or hard-order validation failed")]
    Policy,
    #[error("origin forks expose more than two faulty identities")]
    FaultBudget,
}
