//! Bounded envelopes for the native recovery channel, separate from normal voting.
use super::{
    certificate::Recovered,
    request::{MAX_BYTES, Request, Response},
};
use bytes::BufMut;
use commonware_codec::{Buf, EncodeSize, Error, Read, ReadExt as _, Write};
use commonware_cryptography::{Digest, certificate::Scheme};

/// Contents are untrusted until native scheme, authority and ancestry checks pass.
#[derive(Clone, Debug)]
pub enum Wire<S: Scheme, D: Digest> {
    Request(Request<S, D>),
    Response(Response<S, D>),
    Recovered(Recovered<S, D>),
}
impl<S: Scheme, D: Digest> Write for Wire<S, D> {
    fn write(&self, w: &mut impl BufMut) {
        1u8.write(w);
        match self {
            Self::Request(v) => {
                0u8.write(w);
                v.write(w);
            }
            Self::Response(v) => {
                1u8.write(w);
                v.write(w);
            }
            Self::Recovered(v) => {
                2u8.write(w);
                v.write(w);
            }
        }
    }
}
impl<S: Scheme, D: Digest> EncodeSize for Wire<S, D> {
    fn encode_size(&self) -> usize {
        2 + match self {
            Self::Request(v) => v.encode_size(),
            Self::Response(v) => v.encode_size(),
            Self::Recovered(v) => v.encode_size(),
        }
    }
}
impl<S: Scheme, D: Digest> Read for Wire<S, D> {
    type Cfg = (usize, <S::Certificate as Read>::Cfg);
    fn read_cfg(r: &mut impl Buf, cfg: &Self::Cfg) -> Result<Self, Error> {
        if r.remaining() > MAX_BYTES + 2 || u8::read(r)? != 1 {
            return Err(Error::Invalid(
                "recovery wire",
                "oversized input or version",
            ));
        }
        match u8::read(r)? {
            0 => Ok(Self::Request(Request::read_cfg(r, &cfg.0)?)),
            1 => Ok(Self::Response(Response::read(r)?)),
            2 => Ok(Self::Recovered(Recovered::read_cfg(r, &cfg.1)?)),
            _ => Err(Error::Invalid("recovery wire", "unknown tag")),
        }
    }
}
#[cfg(feature = "arbitrary")]
impl<'a, S: Scheme, D: Digest + for<'b> arbitrary::Arbitrary<'b>> arbitrary::Arbitrary<'a>
    for Wire<S, D>
where
    S::Signature: for<'b> arbitrary::Arbitrary<'b>,
    S::Certificate: for<'b> arbitrary::Arbitrary<'b>,
{
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        Ok(match u.int_in_range(0..=2)? {
            0 => Self::Request(u.arbitrary()?),
            1 => Self::Response(u.arbitrary()?),
            _ => Self::Recovered(u.arbitrary()?),
        })
    }
}
