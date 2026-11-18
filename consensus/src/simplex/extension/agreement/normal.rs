//! Joint original-round authorization using the existing native signing domains.
//!
//! A reservation is one journal item, not two independently recoverable records.
//! The native voter must first check its own eligibility and once-choice, retain
//! the full origin, then synchronize this item before releasing either signature.
//! These types do not install a Mode or authorize native finality on their own.

use super::{
    FastProof, Kind, Message, Quorum, Signed, Value,
    issuance::{self, Action, Record},
    recovery::Material,
    scheme,
};
use crate::{
    Epochable, Viewable,
    simplex::extension::vote::{self, Statement},
    types::{Epoch, View},
};
use bytes::BufMut;
use commonware_codec::{Buf, EncodeSize, Error as CodecError, Read, ReadExt as _, Write};
use commonware_cryptography::{
    Digest, Hasher,
    certificate,
};
use commonware_parallel::Strategy;
use commonware_utils::iter::NonEmpty;
use rand_core::CryptoRng;

/// One immutable authorization for both original final signatures.
///
/// The embedded M1 choice appears in every later complete recovery history even
/// if a crash interrupted signature production. Replay must restore this record
/// and all later fences before either signing domain is enabled.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reservation<D: Digest> {
    pub(super) subject: Statement<D>,
    pub(super) agreement: Record<D>,
}
impl<D: Digest> Reservation<D> {
    pub const fn subject(&self) -> &Statement<D> {
        &self.subject
    }
    pub const fn agreement(&self) -> &Record<D> {
        &self.agreement
    }
    pub(super) fn check<H: Hasher<Digest = D>>(&self) -> Result<(), issuance::Error> {
        let slot = self.agreement.slot();
        let Action::Reserve {
            message,
            authority: Some(_),
            core: None,
        } = self.agreement.action()
        else {
            return Err(issuance::Error::Authority);
        };
        if self.subject.proposal != slot.proposal
            || self.subject.ballot != slot.proposal.round
            || self.subject.domain != slot.domain
            || self.subject.parent != slot.parent
            || message.slot != slot.id::<H>()
            || message.round != slot.proposal.round
            || message.kind != Kind::FastFinal(self.subject.extension)
        {
            return Err(issuance::Error::Context);
        }
        Ok(())
    }
}
impl<D: Digest> Epochable for Reservation<D> {
    fn epoch(&self) -> Epoch {
        self.agreement.epoch()
    }
}
impl<D: Digest> Viewable for Reservation<D> {
    fn view(&self) -> View {
        self.agreement.view()
    }
}
impl<D: Digest> Write for Reservation<D> {
    fn write(&self, w: &mut impl BufMut) {
        1u8.write(w);
        self.subject.write(w);
        self.agreement.write(w);
    }
}
impl<D: Digest> EncodeSize for Reservation<D> {
    fn encode_size(&self) -> usize {
        1 + self.subject.encode_size() + self.agreement.encode_size()
    }
}
impl<D: Digest> Read for Reservation<D> {
    type Cfg = ();
    fn read_cfg(r: &mut impl Buf, _: &()) -> Result<Self, CodecError> {
        if u8::read(r)? != 1 {
            return Err(CodecError::Invalid("agreement normal reservation", "version"));
        }
        Ok(Self {
            subject: Statement::read(r)?,
            agreement: Record::read(r)?,
        })
    }
}

/// Two genuine original-round attestations from one epoch validator.
///
/// The origin is a content address, not proof validation or material custody.
/// Consumers must verify it against the full origin under trusted configuration.
#[derive(Clone, Debug)]
pub struct Vote<S: certificate::Scheme, D: Digest> {
    pub native: vote::Vote<S, D>,
    pub agreement: Signed<S, D>,
    pub origin: D,
}
impl<S: scheme::Scheme<D>, D: Digest> Vote<S, D> {
    /// Checks attestations against an already authenticated full origin.
    /// The caller must have verified that origin under the exact Slot, native
    /// elected leader, field limits and deterministic selection policy.
    pub fn verify_attestations<H: Hasher<Digest = D>, R: CryptoRng>(
        &self,
        rng: &mut R,
        scheme: &S,
        origin: &FastProof<S, D>,
        strategy: &impl Strategy,
    ) -> bool {
        self.native.statement == subject::<H>(&origin.value)
            && self.origin == Material::Origin(origin.clone()).id::<H>()
            && self.native.attestation.signer == self.agreement.attestation.signer
            && self.agreement.message
                == (Message {
                    slot: origin.value.slot.id::<H>(),
                    round: origin.value.slot.proposal.round,
                    leader: origin.core.leader,
                    kind: Kind::FastFinal(origin.value.id::<H>()),
                })
            && self.native.verify(rng, scheme, strategy)
            && self.agreement.verify(rng, scheme, strategy)
    }
}
impl<S: certificate::Scheme, D: Digest> Write for Vote<S, D> {
    fn write(&self, w: &mut impl BufMut) {
        1u8.write(w);
        self.native.write(w);
        self.agreement.write(w);
        self.origin.write(w);
    }
}
impl<S: certificate::Scheme, D: Digest> EncodeSize for Vote<S, D> {
    fn encode_size(&self) -> usize {
        1 + self.native.encode_size() + self.agreement.encode_size() + self.origin.encode_size()
    }
}
impl<S: certificate::Scheme, D: Digest> Read for Vote<S, D> {
    type Cfg = ();
    fn read_cfg(r: &mut impl Buf, _: &()) -> Result<Self, CodecError> {
        if u8::read(r)? != 1 {
            return Err(CodecError::Invalid("agreement normal vote", "version"));
        }
        Ok(Self {
            native: vote::Vote::read(r)?,
            // FAST_FINAL has no report payload. Reject oversized other roles.
            agreement: Signed::read_cfg(r, &0)?,
            origin: D::read(r)?,
        })
    }
}

/// Joint normal issuance or assembly failure.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("invalid original proof: {0}")]
    Origin(#[from] super::Error),
    #[error("local issuance: {0}")]
    Issuance(#[from] issuance::Error),
    #[error("invalid or mismatched paired final vote")]
    Pair,
    #[error("native final certificate: {0}")]
    Native(#[from] vote::Error),
}

/// Maps the complete M1 value to its exact original native final subject.
pub(super) fn subject<H: Hasher>(value: &Value<H::Digest>) -> Statement<H::Digest> {
    Statement {
        proposal: value.slot.proposal.clone(),
        domain: value.slot.domain,
        ballot: value.slot.proposal.round,
        parent: value.slot.parent,
        extension: value.id::<H>(),
    }
}

/// The genuine native and M1 quorums, requiring complete origin custody.
pub type Quorums<S, D> = (vote::Certificate<S, D>, Quorum<S, D>);

/// Consumes exactly five complete same-owner pairs to assemble both quorums.
///
/// The full origin must have been authenticated by the caller. This constructor
/// guarantees identical signer populations by deriving both certificates from
/// the same checked pairs, without inspecting opaque scheme certificate formats.
/// Neither returned certificate alone is the complete native-plus-M1 authority.
pub fn assemble<H, S, R, I>(
    rng: &mut R,
    scheme: &S,
    origin: &FastProof<S, H::Digest>,
    votes: NonEmpty<I>,
    strategy: &impl Strategy,
) -> Result<Quorums<S, H::Digest>, Error>
where
    H: Hasher,
    S: scheme::Scheme<H::Digest>,
    R: CryptoRng,
    I: Iterator<Item = Vote<S, H::Digest>> + Send,
{
    if scheme.participants().len() != 7 || !S::is_attributable() {
        return Err(Error::Pair);
    }
    let mut native = Vec::with_capacity(5);
    let mut agreement = Vec::with_capacity(5);
    for pair in votes {
        if native.len() == 5 {
            return Err(Error::Pair);
        }
        if !pair.verify_attestations::<H, _>(rng, scheme, origin, strategy) {
            return Err(Error::Pair);
        }
        native.push(pair.native);
        agreement.push(pair.agreement);
    }
    if native.len() != 5 {
        return Err(Error::Pair);
    }
    let (first, rest) = native.split_first().ok_or(Error::Pair)?;
    let native = vote::Certificate::from_votes(
        rng,
        scheme,
        NonEmpty::new(first.clone(), rest.iter().cloned()),
        strategy,
    )?;
    let mut agreement = agreement.into_iter();
    let first = agreement.next().ok_or(Error::Pair)?;
    let agreement = Quorum::from_votes(
        rng,
        scheme,
        NonEmpty::new(first, agreement),
        strategy,
    )?;
    Ok((native, agreement))
}
