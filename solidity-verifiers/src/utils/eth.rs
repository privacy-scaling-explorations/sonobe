//! This module provides a trait and implementations for converting Rust types
//! to EVM calldata.
use ark_ec::{
    pairing::Pairing,
    short_weierstrass::{Affine, Projective, SWCurveConfig},
    AffineRepr, CurveGroup,
};
use ark_ff::{BigInteger, Fp, Fp2, Fp2Config, FpConfig, PrimeField};
use ark_groth16::Proof;

pub trait ToEth {
    fn to_eth(&self) -> Vec<u8>;
}

impl<T: ToEth> ToEth for [T] {
    fn to_eth(&self) -> Vec<u8> {
        self.iter().flat_map(ToEth::to_eth).collect()
    }
}

impl ToEth for u8 {
    fn to_eth(&self) -> Vec<u8> {
        vec![*self]
    }
}

impl<P: FpConfig<N>, const N: usize> ToEth for Fp<P, N> {
    fn to_eth(&self) -> Vec<u8> {
        self.into_bigint().to_bytes_be()
    }
}

impl<P: Fp2Config<Fp: ToEth>> ToEth for Fp2<P> {
    fn to_eth(&self) -> Vec<u8> {
        [self.c1.to_eth(), self.c0.to_eth()].concat()
    }
}

impl<P: SWCurveConfig<BaseField: ToEth>> ToEth for Affine<P> {
    fn to_eth(&self) -> Vec<u8> {
        // the encoding of the additive identity is [0, 0] on the EVM
        let (x, y) = self.xy().unwrap_or_default();

        [x.to_eth(), y.to_eth()].concat()
    }
}

impl<P: SWCurveConfig<BaseField: ToEth>> ToEth for Projective<P> {
    fn to_eth(&self) -> Vec<u8> {
        self.into_affine().to_eth()
    }
}

impl<E: Pairing<G1Affine: ToEth, G2Affine: ToEth>> ToEth for Proof<E> {
    fn to_eth(&self) -> Vec<u8> {
        [self.a.to_eth(), self.b.to_eth(), self.c.to_eth()].concat()
    }
}
