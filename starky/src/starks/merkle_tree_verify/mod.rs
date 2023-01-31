//! Merkle Tree Verify STARK

use crate::lookup::Oracle;

///
pub trait SwappingHash {
    ///
    type Digest;
}

///
pub struct SwappingHashGate<T, H>
where
    H: SwappingHash,
{
    ///
    pub swap: T,

    ///
    pub lhs: H::Digest,

    ///
    pub rhs: H::Digest,

    ///
    pub output: H::Digest,
}

///
pub struct VerifyGate<T, H>
where
    H: SwappingHash,
{
    ///
    pub swapping_hash_oracle: Oracle<SwappingHashGate<T, H>>,
}
