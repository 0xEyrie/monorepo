//! Exact original issuance records in the native voter's existing journal.

use super::{FirstVote, WIRE_LIMITS, g};
use crate::{
    Epochable, Viewable,
    simplex::types::Proposal,
    types::{Epoch, View},
};
use bytes::{Buf as _, BufMut};
use commonware_codec::{Buf, EncodeSize, Error, Read, ReadExt as _, Write};
use commonware_cryptography::{Digest, certificate::Scheme};

/// Hard storage-frame ceiling; configured policy limits are checked on replay.
pub const MAX_WAL_BYTES: usize = g::MAX_EVIDENCE_BYTES;

/// Original-only local WAL item. Decoding grants no application or signer authority.
#[derive(Clone, Debug)]
pub struct Wal<S: Scheme, D: Digest>(pub(super) Event<S, D>);

impl<S: Scheme, D: Digest> PartialEq for Wal<S, D> {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (Event::First(a), Event::First(b)) | (Event::Select(a), Event::Select(b)) => a == b,
            (
                Event::FirstReleased {
                    reservation: a,
                    receipt: ar,
                    vote: av,
                },
                Event::FirstReleased {
                    reservation: b,
                    receipt: br,
                    vote: bv,
                },
            ) => a == b && ar == br && av == bv,
            (
                Event::SelectReleased {
                    reservation: a,
                    receipt: ar,
                },
                Event::SelectReleased {
                    reservation: b,
                    receipt: br,
                },
            ) => a == b && ar == br,
            (
                Event::Normal {
                    no_first: a,
                    reservation: ar,
                },
                Event::Normal {
                    no_first: b,
                    reservation: br,
                },
            ) => a == b && ar == br,
            (
                Event::History {
                    entry: a,
                    reservation: b,
                    nqc: c,
                },
                Event::History {
                    entry: x,
                    reservation: y,
                    nqc: z,
                },
            ) => a == x && b == y && c == z,
            (
                Event::HistoryReleased {
                    reservation: a,
                    receipt: b,
                },
                Event::HistoryReleased {
                    reservation: x,
                    receipt: y,
                },
            ) => a == x && b == y,
            (
                Event::Ballot {
                    rpc: a,
                    reservation: b,
                },
                Event::Ballot {
                    rpc: c,
                    reservation: d,
                },
            ) => a == c && b == d,
            (
                Event::BallotReleased {
                    reservation: a,
                    receipt: b,
                },
                Event::BallotReleased {
                    reservation: c,
                    receipt: d,
                },
            ) => a == c && b == d,
            (Event::NormalReleased(a), Event::NormalReleased(b)) => a == b,
            _ => false,
        }
    }
}
impl<S: Scheme, D: Digest> Eq for Wal<S, D> {}

#[derive(Clone, Debug)]
pub(super) enum Event<S: Scheme, D: Digest> {
    First(g::issuance::Record<D>),
    FirstReleased {
        reservation: g::issuance::Record<D>,
        receipt: Option<g::issuance::Record<D>>,
        vote: FirstVote<S, D>,
    },
    Select(g::issuance::Record<D>),
    SelectReleased {
        reservation: g::issuance::Record<D>,
        receipt: g::issuance::Record<D>,
    },
    Normal {
        no_first: Option<g::issuance::Record<D>>,
        reservation: g::normal::Reservation<D>,
    },
    NormalReleased(g::normal::Released<S, D>),
    Ballot {
        rpc: Option<g::issuance::Record<D>>,
        reservation: g::issuance::Record<D>,
    },
    BallotReleased {
        reservation: g::issuance::Record<D>,
        receipt: g::issuance::Record<D>,
    },
    History {
        entry: g::issuance::Record<D>,
        reservation: g::issuance::Record<D>,
        nqc: bytes::Bytes,
    },
    HistoryReleased {
        reservation: g::issuance::Record<D>,
        receipt: g::issuance::Record<D>,
    },
}

impl<S: Scheme, D: Digest> Wal<S, D> {
    pub(super) const fn record(&self) -> &g::issuance::Record<D> {
        match &self.0 {
            Event::First(r) | Event::Select(r) => r,
            Event::History { reservation, .. }
            | Event::Ballot { reservation, .. }
            | Event::BallotReleased { reservation, .. }
            | Event::HistoryReleased { reservation, .. }
            | Event::FirstReleased { reservation, .. }
            | Event::SelectReleased { reservation, .. } => reservation,
            Event::Normal { reservation, .. } => reservation.agreement(),
            Event::NormalReleased(r) => r.reservation().agreement(),
        }
    }
    /// Exact original native proposal, including its original view.
    pub const fn proposal(&self) -> &Proposal<D> {
        &self.record().slot().proposal
    }
    /// Complete accepted logical agreement record at this transition.
    pub const fn agreement(&self) -> &g::issuance::Record<D> {
        self.record()
    }
    fn body_size(&self) -> usize {
        1 + match &self.0 {
            Event::First(r) | Event::Select(r) => r.encode_size(),
            Event::FirstReleased {
                reservation,
                receipt,
                vote,
            } => reservation.encode_size() + receipt.encode_size() + vote.encode_size(),
            Event::SelectReleased {
                reservation,
                receipt,
            } => reservation.encode_size() + receipt.encode_size(),
            Event::Normal {
                no_first,
                reservation,
            } => no_first.encode_size() + reservation.encode_size(),
            Event::NormalReleased(r) => r.encode_size(),
            Event::Ballot { rpc, reservation } => rpc.encode_size() + reservation.encode_size(),
            Event::BallotReleased {
                reservation,
                receipt,
            } => reservation.encode_size() + receipt.encode_size(),
            Event::History {
                entry,
                reservation,
                nqc,
            } => entry.encode_size() + reservation.encode_size() + nqc.len(),
            Event::HistoryReleased {
                reservation,
                receipt,
            } => reservation.encode_size() + receipt.encode_size(),
        }
    }
}
impl<S: Scheme, D: Digest> Epochable for Wal<S, D> {
    fn epoch(&self) -> Epoch {
        self.proposal().epoch()
    }
}
impl<S: Scheme, D: Digest> Viewable for Wal<S, D> {
    fn view(&self) -> View {
        self.proposal().view()
    }
}
impl<S: Scheme, D: Digest> EncodeSize for Wal<S, D> {
    fn encode_size(&self) -> usize {
        8 + self.body_size()
    }
}
impl<S: Scheme, D: Digest> Write for Wal<S, D> {
    fn write(&self, w: &mut impl BufMut) {
        w.put_slice(b"G1W2");
        (self.body_size() as u32).write(w);
        match &self.0 {
            Event::First(r) => {
                0u8.write(w);
                r.write(w);
            }
            Event::FirstReleased {
                reservation,
                receipt,
                vote,
            } => {
                1u8.write(w);
                reservation.write(w);
                receipt.write(w);
                vote.write(w);
            }
            Event::Select(r) => {
                2u8.write(w);
                r.write(w);
            }
            Event::SelectReleased {
                reservation,
                receipt,
            } => {
                3u8.write(w);
                reservation.write(w);
                receipt.write(w);
            }
            Event::Normal {
                no_first,
                reservation,
            } => {
                4u8.write(w);
                no_first.write(w);
                reservation.write(w);
            }
            Event::History {
                entry,
                reservation,
                nqc,
            } => {
                6u8.write(w);
                entry.write(w);
                reservation.write(w);
                w.put_slice(nqc);
            }
            Event::HistoryReleased {
                reservation,
                receipt,
            } => {
                7u8.write(w);
                reservation.write(w);
                receipt.write(w);
            }
            Event::Ballot { rpc, reservation } => {
                8u8.write(w);
                rpc.write(w);
                reservation.write(w);
            }
            Event::BallotReleased {
                reservation,
                receipt,
            } => {
                9u8.write(w);
                reservation.write(w);
                receipt.write(w);
            }
            Event::NormalReleased(r) => {
                5u8.write(w);
                r.write(w);
            }
        }
    }
}
impl<S: Scheme, D: Digest> Read for Wal<S, D> {
    type Cfg = ();
    fn read_cfg(r: &mut impl Buf, _: &()) -> Result<Self, Error> {
        if <[u8; 4]>::read(r)? != *b"G1W2" {
            return Err(Error::Invalid("G1 native WAL", "type/version"));
        }
        let len = u32::read(r)? as usize;
        if len > MAX_WAL_BYTES - 8 || len > r.remaining() {
            return Err(Error::InvalidLength(len));
        }
        let mut b = r.copy_to_bytes(len);
        let record = |b: &mut bytes::Bytes| g::issuance::Record::read_cfg(b, &WIRE_LIMITS);
        let event = match u8::read(&mut b)? {
            0 => Event::First(record(&mut b)?),
            1 => Event::FirstReleased {
                reservation: record(&mut b)?,
                receipt: Option::<g::issuance::Record<D>>::read_cfg(&mut b, &WIRE_LIMITS)?,
                vote: FirstVote::read(&mut b)?,
            },
            2 => Event::Select(record(&mut b)?),
            3 => Event::SelectReleased {
                reservation: record(&mut b)?,
                receipt: record(&mut b)?,
            },
            4 => Event::Normal {
                no_first: Option::<g::issuance::Record<D>>::read_cfg(&mut b, &WIRE_LIMITS)?,
                reservation: g::normal::Reservation::read_cfg(&mut b, &WIRE_LIMITS)?,
            },
            5 => Event::NormalReleased(g::normal::Released::read_cfg(&mut b, &WIRE_LIMITS)?),
            6 => Event::History {
                entry: record(&mut b)?,
                reservation: record(&mut b)?,
                nqc: {
                    if !b.has_remaining() {
                        return Err(Error::InvalidLength(0));
                    }
                    b.copy_to_bytes(b.remaining())
                },
            },
            7 => Event::HistoryReleased {
                reservation: record(&mut b)?,
                receipt: record(&mut b)?,
            },
            8 => Event::Ballot {
                rpc: Option::<g::issuance::Record<D>>::read_cfg(&mut b, &WIRE_LIMITS)?,
                reservation: record(&mut b)?,
            },
            9 => Event::BallotReleased {
                reservation: record(&mut b)?,
                receipt: record(&mut b)?,
            },
            _ => return Err(Error::Invalid("G1 native WAL", "tag")),
        };
        if b.has_remaining() {
            return Err(Error::Invalid("G1 native WAL", "trailing bytes"));
        }
        Ok(Self(event))
    }
}

// Raw bounded codec values only. These constructors grant no native or
// application authority, and the replay state machine still checks their role.
#[cfg(feature = "arbitrary")]
impl<S: Scheme, D: Digest> arbitrary::Arbitrary<'_> for Wal<S, D>
where
    D: for<'a> arbitrary::Arbitrary<'a>,
    S::Signature: for<'a> arbitrary::Arbitrary<'a>,
{
    fn arbitrary(u: &mut arbitrary::Unstructured<'_>) -> arbitrary::Result<Self> {
        use commonware_codec::{Decode as _, Encode as _};

        fn framed(magic: &[u8; 4], body: &[u8]) -> bytes::Bytes {
            let mut bytes = Vec::new();
            bytes.put_slice(magic);
            (body.len() as u32).write(&mut bytes);
            bytes.put_slice(body);
            bytes.into()
        }

        fn record<D: Digest + for<'a> arbitrary::Arbitrary<'a>>(
            u: &mut arbitrary::Unstructured<'_>,
        ) -> arbitrary::Result<g::issuance::Record<D>> {
            let raw: g::issuance::Record<D> = u.arbitrary()?;
            let mut core = raw.core().clone();
            // The historical raw Record generator permits an empty Core. A
            // WAL frame must additionally satisfy its nested codec geometry.
            core.leader = crate::types::Participant::new(0);
            core.followers = vec![
                crate::types::Participant::new(1),
                crate::types::Participant::new(2),
            ];
            let original = raw.encode();
            let mut body = core.encode().to_vec();
            body.extend_from_slice(&original[8 + raw.core().encode_size()..]);
            g::issuance::Record::decode_cfg(framed(b"G1J1", &body), &WIRE_LIMITS)
                .map_err(|_| arbitrary::Error::IncorrectFormat)
        }

        fn optional_record<D: Digest + for<'a> arbitrary::Arbitrary<'a>>(
            u: &mut arbitrary::Unstructured<'_>,
        ) -> arbitrary::Result<Option<g::issuance::Record<D>>> {
            if u.arbitrary()? {
                Ok(Some(record(u)?))
            } else {
                Ok(None)
            }
        }

        // Raw codecs deliberately accept these unrelated subjects. Native
        // replay must separately reject the untrusted combinations.
        let tag: u8 = u.int_in_range(0..=5)?;
        let reservation = record::<D>(u)?;
        let event = match tag {
            0 => Event::First(reservation),
            1 => Event::FirstReleased {
                reservation,
                receipt: optional_record(u)?,
                vote: u.arbitrary()?,
            },
            2 => Event::Select(reservation),
            3 => Event::SelectReleased {
                reservation,
                receipt: record(u)?,
            },
            4 | 5 => {
                let subject: crate::simplex::extension::vote::Statement<D> = u.arbitrary()?;
                let subject_bytes = subject.encode();
                let mut body = Vec::new();
                (subject_bytes.len() as u32).write(&mut body);
                body.put_slice(&subject_bytes);
                reservation.write(&mut body);
                let reservation =
                    g::normal::Reservation::decode_cfg(framed(b"G1G1", &body), &WIRE_LIMITS)
                        .map_err(|_| arbitrary::Error::IncorrectFormat)?;
                if tag == 4 {
                    Event::Normal {
                        no_first: optional_record(u)?,
                        reservation,
                    }
                } else {
                    let receipt = record::<D>(u)?;
                    let vote: super::FinalVote<S, D> = u.arbitrary()?;
                    let mut body = Vec::new();
                    reservation.write(&mut body);
                    receipt.write(&mut body);
                    vote.inner().write(&mut body);
                    Event::NormalReleased(
                        g::normal::Released::decode_cfg(framed(b"G1X1", &body), &WIRE_LIMITS)
                            .map_err(|_| arbitrary::Error::IncorrectFormat)?,
                    )
                }
            }
            _ => unreachable!(),
        };
        let result = Self(event);
        if result.encode_size() > MAX_WAL_BYTES {
            return Err(arbitrary::Error::IncorrectFormat);
        }
        Self::decode_cfg(result.encode(), &()).map_err(|_| arbitrary::Error::IncorrectFormat)
    }
}

#[cfg(test)]
#[path = "voting_wal_tests.rs"]
mod tests;
