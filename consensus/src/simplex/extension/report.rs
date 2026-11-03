//! First-vote transport for an independently authenticated application report.
//!
//! The ordinary notarize signature endorses only the original proposal. Opaque
//! report bytes are untrusted until application policy verifies their signature,
//! signer and exact proposal context. A notarization QC does not certify reports.

use crate::{
    Epochable, Viewable,
    simplex::types::Notarize as BaseNotarize,
    types::{Attributable, Epoch, Participant, View},
};
use bytes::{BufMut, Bytes};
use commonware_codec::{Buf, EncodeSize, Error, Read, ReadExt as _, Write};
use commonware_cryptography::{Digest, certificate::Scheme};
use std::hash::Hash;

/// Maximum encoded application report carried with one first vote.
pub const MAX_REPORT_BYTES: usize = 64 * 1024;

/// An unchanged first vote with an optional independently signed report.
#[derive(Clone, Debug)]
pub struct Notarize<S: Scheme, D: Digest> {
    vote: BaseNotarize<S, D>,
    report: Option<Bytes>,
}

impl<S: Scheme, D: Digest> Notarize<S, D> {
    /// Bounds an optional report without modifying the ordinary vote. On failure
    /// returns that vote so the caller can transmit it without an extension.
    pub fn new(
        vote: BaseNotarize<S, D>,
        report: Option<Bytes>,
    ) -> Result<Self, BaseNotarize<S, D>> {
        if report
            .as_ref()
            .is_some_and(|bytes| bytes.len() > MAX_REPORT_BYTES)
        {
            return Err(vote);
        }
        Ok(Self { vote, report })
    }

    /// Ordinary proposal vote; verification of it says nothing about the report.
    pub const fn vote(&self) -> &BaseNotarize<S, D> {
        &self.vote
    }

    /// Untrusted original report bytes, requiring independent policy validation.
    pub const fn report(&self) -> Option<&Bytes> {
        self.report.as_ref()
    }

    /// Separates the base vote from its independently validated report path.
    pub fn into_parts(self) -> (BaseNotarize<S, D>, Option<Bytes>) {
        (self.vote, self.report)
    }
}
impl<S: Scheme, D: Digest> From<BaseNotarize<S, D>> for Notarize<S, D> {
    fn from(vote: BaseNotarize<S, D>) -> Self {
        Self { vote, report: None }
    }
}
impl<S: Scheme, D: Digest> PartialEq for Notarize<S, D> {
    fn eq(&self, other: &Self) -> bool {
        self.vote == other.vote && self.report == other.report
    }
}
impl<S: Scheme, D: Digest> Eq for Notarize<S, D> {}
impl<S: Scheme, D: Digest> Hash for Notarize<S, D> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.vote.hash(state);
        self.report.hash(state);
    }
}
impl<S: Scheme, D: Digest> Write for Notarize<S, D> {
    fn write(&self, writer: &mut impl BufMut) {
        self.vote.write(writer);
        self.report.write(writer);
    }
}
impl<S: Scheme, D: Digest> EncodeSize for Notarize<S, D> {
    fn encode_size(&self) -> usize {
        self.vote.encode_size() + self.report.encode_size()
    }
}
impl<S: Scheme, D: Digest> Read for Notarize<S, D> {
    type Cfg = ();
    fn read_cfg(reader: &mut impl Buf, _: &()) -> Result<Self, Error> {
        let vote = BaseNotarize::read(reader)?;
        let report = Option::<Bytes>::read_cfg(reader, &(0..=MAX_REPORT_BYTES).into())?;
        Ok(Self { vote, report })
    }
}
impl<S: Scheme, D: Digest> Epochable for Notarize<S, D> {
    fn epoch(&self) -> Epoch {
        self.vote.epoch()
    }
}
impl<S: Scheme, D: Digest> Viewable for Notarize<S, D> {
    fn view(&self) -> View {
        self.vote.view()
    }
}
#[cfg(feature = "arbitrary")]
impl<'a, S: Scheme, D: Digest + for<'b> arbitrary::Arbitrary<'b>> arbitrary::Arbitrary<'a>
    for Notarize<S, D>
where
    S::Signature: for<'b> arbitrary::Arbitrary<'b>,
{
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let vote = BaseNotarize::arbitrary(u)?;
        let report = Option::<Vec<u8>>::arbitrary(u)?.map(|mut bytes| {
            bytes.truncate(MAX_REPORT_BYTES);
            Bytes::from(bytes)
        });
        Ok(Self { vote, report })
    }
}

impl<S: Scheme, D: Digest> Attributable for Notarize<S, D> {
    fn signer(&self) -> Participant {
        self.vote.signer()
    }
}
