//! Raw G1W2 storage compatibility. Successful decoding is not replay admission.
#[cfg(feature = "arbitrary")]
mod conformance {
    use super::super::*;
    use arbitrary::{Arbitrary as _, Unstructured};
    use commonware_codec::{DecodeExt as _, Encode as _, conformance::CodecConformance};
    use commonware_cryptography::sha256::Digest as D;
    use commonware_utils::TestRng;
    use rand_core::Rng as _;

    type S = crate::simplex::scheme::ed25519::Scheme;

    #[test]
    fn original_wal_tags_have_bounded_roundtrips_and_reject_bad_frames() {
        let mut seen = [0usize; 6];
        for seed in 0..512 {
            let mut data = vec![0u8; 32 * 1024];
            TestRng::new(seed).fill_bytes(&mut data);
            let Ok(value) = Wal::<S, D>::arbitrary(&mut Unstructured::new(&data)) else {
                continue;
            };
            let bytes = value.encode();
            seen[usize::from(bytes[8])] += 1;
            assert!(bytes.len() <= MAX_WAL_BYTES);
            assert_eq!(Wal::<S, D>::decode(bytes.clone()).unwrap(), value);
            assert!(Wal::<S, D>::decode(bytes.slice(..bytes.len() - 1)).is_err());
            let mut extra = bytes.to_vec();
            extra.push(0);
            assert!(Wal::<S, D>::decode(bytes::Bytes::from(extra)).is_err());
            let mut bad = bytes.to_vec();
            bad[8] = u8::MAX;
            assert!(Wal::<S, D>::decode(bytes::Bytes::copy_from_slice(&bad)).is_err());
            bad[8] = bytes[8];
            bad[0] ^= 1;
            assert!(Wal::<S, D>::decode(bytes::Bytes::from(bad)).is_err());
            let mut huge = bytes.to_vec();
            huge[4..8].copy_from_slice(&u32::MAX.to_be_bytes());
            assert!(Wal::<S, D>::decode(bytes::Bytes::from(huge)).is_err());
        }
        assert!(seen.into_iter().all(|count| count > 0), "all six WAL tags");
    }

    commonware_conformance::conformance_tests! {
        CodecConformance<Wal<S,D>> => 128,
    }
}
