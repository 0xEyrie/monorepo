//! Authenticated safe-tip history.

use super::{BlockRef, CodecConfig, EpochGenesis, Error, LeaderBlock, ensure_canonical_chains};
use crate::types::Height;
use bytes::{BufMut, Bytes};
use commonware_codec::{
    Buf, Encode, EncodeSize, Error as CodecError, RangeCfg, Read, ReadExt, Write,
};
use commonware_cryptography::{Digest, Hasher, bls12381::primitives::variant::Variant};

const TIP_HISTORY_NAMESPACE: &[u8] = b"_COMMONWARE_CONSENSUS_MULTIMMIT_TIP_HISTORY";
const GENESIS_HISTORY_NAMESPACE: &[u8] = b"_COMMONWARE_CONSENSUS_MULTIMMIT_GENESIS_HISTORY";

/// One compact commitment link for safe-to-extend producer tips.
///
/// A leader block commits to the record derived from its parent V-QC. Validators reconstruct that
/// record while validating and extending the parent; certificates carry only the commitment.
///
/// Besides the safe tips, a record carries the tip height each chain's proposal reached in the
/// view that produced it. The ordering sweep places the blocks at or below that height, which the
/// proposal pins, before any block above it, which only vote extensions endorse. Both vectors are
/// committed because peers serve history records during catch-up.
/// The record also commits to the producing proposal's extension, so ordering policies receive
/// the same application data after history catch-up or restart.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TipRecord<D: Digest> {
    parent: D,
    tips: Vec<BlockRef<D>>,
    proposed: Vec<Height>,
    proposal_extension: Option<Bytes>,
}

impl<D: Digest> TipRecord<D> {
    /// Creates a history record extending `parent` with one safe tip and one proposed tip height
    /// per producer chain.
    pub fn new(parent: D, tips: Vec<BlockRef<D>>, proposed: Vec<Height>) -> Result<Self, Error> {
        if tips.is_empty()
            || tips.len() != proposed.len()
            || ensure_canonical_chains(tips.iter().map(BlockRef::chain)).is_err()
        {
            return Err(Error::Chain);
        }
        Ok(Self {
            parent,
            tips,
            proposed,
            proposal_extension: None,
        })
    }

    /// Creates a record whose proposed tips are the safe tips themselves.
    ///
    /// This is the genesis record, and the record of any view whose proposal added nothing above
    /// the tips its V-QC carried.
    pub fn at_tips(parent: D, tips: Vec<BlockRef<D>>) -> Result<Self, Error> {
        let proposed = tips.iter().map(|tip| tip.height()).collect();
        Self::new(parent, tips, proposed)
    }

    /// Attaches the certified proposal's application data to this history commitment.
    ///
    /// Returns an error if present data is empty or exceeds the epoch's byte bound.
    pub fn with_proposal_extension(
        mut self,
        extension: Option<Bytes>,
        config: CodecConfig,
    ) -> Result<Self, Error> {
        if extension.as_ref().is_some_and(|bytes| {
            bytes.is_empty() || bytes.len() > config.proposal_extension_bound()
        }) {
            return Err(Error::ProposalExtensionLength);
        }
        self.proposal_extension = extension;
        Ok(self)
    }

    pub(crate) fn from_leader<V: Variant>(
        leader: &LeaderBlock<V, D>,
        tips: Vec<BlockRef<D>>,
    ) -> Result<Self, Error> {
        let mut record = Self::new(leader.history(), tips, leader.proposed_heights())?;
        record.proposal_extension =
            (!leader.extension().is_empty()).then(|| leader.extension().clone());
        Ok(record)
    }

    /// Returns the application data from the proposal that produced these certified tips.
    pub const fn proposal_extension(&self) -> Option<&Bytes> {
        self.proposal_extension.as_ref()
    }

    /// Returns the preceding history commitment.
    pub const fn parent(&self) -> D {
        self.parent
    }

    /// Returns the safe tips contributed by this history link.
    pub fn tips(&self) -> &[BlockRef<D>] {
        &self.tips
    }

    /// Returns the proposed tip height per chain in the view that produced this link.
    pub fn proposed(&self) -> &[Height] {
        &self.proposed
    }

    /// Returns the child leader's history commitment, including the proposal extension.
    pub fn commitment<H: Hasher<Digest = D>>(&self) -> D {
        let tips = self.tips.encode();
        let proposed = self.proposed.encode();
        let extension = self.proposal_extension.encode();
        H::hash(&[
            TIP_HISTORY_NAMESPACE,
            self.parent.as_ref(),
            tips.as_ref(),
            proposed.as_ref(),
            extension.as_ref(),
        ])
    }
}

impl<D: Digest> Write for TipRecord<D> {
    fn write(&self, buf: &mut impl BufMut) {
        self.parent.write(buf);
        self.tips.write(buf);
        self.proposed.write(buf);
        self.proposal_extension.write(buf);
    }
}

impl<D: Digest> EncodeSize for TipRecord<D> {
    fn encode_size(&self) -> usize {
        self.parent.encode_size()
            + self.tips.encode_size()
            + self.proposed.encode_size()
            + self.proposal_extension.encode_size()
    }
}

impl<D: Digest> Read for TipRecord<D> {
    type Cfg = CodecConfig;

    fn read_cfg(buf: &mut impl Buf, config: &Self::Cfg) -> Result<Self, CodecError> {
        let chains = RangeCfg::exact(config.chains());
        let parent = D::read(buf)?;
        let tips = Vec::<BlockRef<D>>::read_cfg(buf, &(chains, ()))?;
        let proposed = Vec::<Height>::read_cfg(buf, &(chains, ()))?;
        let extension =
            Option::<Bytes>::read_cfg(buf, &(0..=config.proposal_extension_bound()).into())?;
        Self::new(parent, tips, proposed)
            .and_then(|record| record.with_proposal_extension(extension, *config))
            .map_err(|error| CodecError::Wrapped("TipRecord", error.into()))
    }
}

/// Returns `H(namespace, genesis)`, the deterministic commitment preceding the epoch's first tip
/// record.
pub fn genesis_history<H: Hasher>(genesis: &EpochGenesis<H::Digest>) -> H::Digest {
    H::hash(&[GENESIS_HISTORY_NAMESPACE, genesis.encode().as_ref()])
}

/// Returns the commitment after incorporating the synthetic genesis tips.
#[cfg(any(test, feature = "mocks"))]
pub(crate) fn genesis_tip_commitment<H: Hasher>(genesis: &EpochGenesis<H::Digest>) -> H::Digest {
    TipRecord::at_tips(genesis_history::<H>(genesis), genesis.tips().to_vec())
        .expect("genesis tips are canonical")
        .commitment::<H>()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        multimmit::types::{CertificateId, ChainId},
        types::Epoch,
    };
    use commonware_cryptography::Sha256;

    #[rstest::rstest]
    #[case::absent(None)]
    #[case::direction(Some(bytes::Bytes::from_static(b"direction")))]
    fn history_codec_authenticates_the_proposal_extension(#[case] extension: Option<bytes::Bytes>) {
        use commonware_codec::Decode as _;
        let codec = CodecConfig::new(1, 1, super::super::PathLimits::new(1, 0).unwrap())
            .unwrap()
            .with_proposal_extension_bound(16);
        let parent = Sha256::hash(&[b"history parent"]);
        let tips = vec![BlockRef::new(
            ChainId::new(0),
            Height::new(1),
            Sha256::hash(&[b"tip"]),
        )];
        let record = TipRecord::at_tips(parent, tips).unwrap();
        let mut encoded = bytes::BytesMut::new();
        record.parent().write(&mut encoded);
        record.tips().to_vec().write(&mut encoded);
        record.proposed().to_vec().write(&mut encoded);
        extension.write(&mut encoded);
        let decoded = TipRecord::<_>::decode_cfg(encoded.freeze(), &codec)
            .expect("history must decode its authenticated proposal extension");
        let metadata = extension.encode();
        let expected = Sha256::hash(&[
            TIP_HISTORY_NAMESPACE,
            parent.as_ref(),
            record.tips().to_vec().encode().as_ref(),
            record.proposed().to_vec().encode().as_ref(),
            metadata.as_ref(),
        ]);
        assert_eq!(decoded.commitment::<Sha256>(), expected);
    }

    #[test]
    fn commitment_is_domain_separated() {
        let parent = Sha256::hash(&[b"parent"]);
        let tips = vec![
            BlockRef::new(
                ChainId::new(0),
                Height::new(11),
                Sha256::hash(&[b"chain 0 tip"]),
            ),
            BlockRef::new(
                ChainId::new(1),
                Height::new(17),
                Sha256::hash(&[b"chain 1 tip"]),
            ),
        ];
        let proposed = vec![Height::new(12), Height::new(17)];
        let encoded_tips = tips.encode();
        let encoded_proposed = proposed.encode();
        let expected = Sha256::hash(&[
            TIP_HISTORY_NAMESPACE,
            parent.as_ref(),
            encoded_tips.as_ref(),
            encoded_proposed.as_ref(),
            None::<Bytes>.encode().as_ref(),
        ]);
        let record = TipRecord::new(parent, tips.clone(), proposed).unwrap();
        assert_ne!(
            record.commitment::<Sha256>(),
            TipRecord::at_tips(parent, tips)
                .unwrap()
                .commitment::<Sha256>()
        );

        assert_eq!(record.commitment::<Sha256>(), expected);
    }

    #[test]
    fn genesis_history_is_domain_separated() {
        let genesis = EpochGenesis::new(
            Epoch::new(4),
            Sha256::hash(&[b"leader genesis"]),
            CertificateId::new(Sha256::hash(&[b"vqc genesis"])),
            CertificateId::new(Sha256::hash(&[b"lqc genesis"])),
            vec![BlockRef::new(
                ChainId::new(0),
                Height::zero(),
                Sha256::hash(&[b"chain 0 genesis"]),
            )],
        )
        .unwrap();
        let encoded = genesis.encode();
        let history = genesis_history::<Sha256>(&genesis);
        assert_eq!(
            history,
            Sha256::hash(&[GENESIS_HISTORY_NAMESPACE, encoded.as_ref()])
        );
        assert_ne!(history, Sha256::hash(&[encoded.as_ref()]));
        assert_ne!(
            history,
            Sha256::hash(&[TIP_HISTORY_NAMESPACE, encoded.as_ref()])
        );
    }
}
