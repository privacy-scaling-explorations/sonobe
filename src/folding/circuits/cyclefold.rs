/// Implements the C_{EC} circuit described in [CycleFold paper](https://eprint.iacr.org/2023/1192.pdf)
use ark_ec::CurveGroup;
use ark_r1cs_std::{boolean::Boolean, prelude::CurveVar};
use ark_relations::r1cs::SynthesisError;
use core::marker::PhantomData;

use super::CF;

/// ECRLC implements gadget that checks the Elliptic Curve points RandomLinearCombination described
/// in [CycleFold](https://eprint.iacr.org/2023/1192.pdf).
#[derive(Debug)]
pub struct ECRLC<C: CurveGroup, GC: CurveVar<C, CF<C>>> {
    _c: PhantomData<C>,
    _gc: PhantomData<GC>,
}
impl<C: CurveGroup, GC: CurveVar<C, CF<C>>> ECRLC<C, GC> {
    pub fn check(
        // get r in bits format, so it can be reused across many instances of ECRLC gadget,
        // reducing the number of constraints needed
        r_bits: Vec<Boolean<CF<C>>>,
        p1: GC,
        p2: GC,
        p3: GC,
    ) -> Result<Boolean<CF<C>>, SynthesisError> {
        p3.is_eq(&(p1 + p2.scalar_mul_le(r_bits.iter())?))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::{BigInteger, PrimeField};
    use ark_pallas::{constraints::GVar, Fq, Fr, Projective};
    use ark_r1cs_std::{alloc::AllocVar, eq::EqGadget};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::UniformRand;
    use std::ops::Mul;

    /// Let Curve1=pallas and Curve2=vesta. Here our constraints system will work over Curve2::Fr =
    /// vesta::Fr (=pallas::Fq), thus our points are P_i \in Curve1 (=pasta).
    #[test]
    fn test_ecrlc_check() {
        let mut rng = ark_std::test_rng();

        let r = Fr::rand(&mut rng);
        let p1 = Projective::rand(&mut rng);
        let p2 = Projective::rand(&mut rng);
        let p3 = p1 + p2.mul(r);

        let cs = ConstraintSystem::<Fq>::new_ref(); // CS over Curve2::Fr = Curve1::Fq

        // prepare circuit inputs
        let rbitsVar: Vec<Boolean<Fq>> =
            Vec::new_witness(cs.clone(), || Ok(r.into_bigint().to_bits_le())).unwrap();

        let p1Var = GVar::new_witness(cs.clone(), || Ok(p1)).unwrap();
        let p2Var = GVar::new_witness(cs.clone(), || Ok(p2)).unwrap();
        let p3Var = GVar::new_witness(cs.clone(), || Ok(p3)).unwrap();

        // check ECRLC circuit
        let check_pass = ECRLC::<Projective, GVar>::check(rbitsVar, p1Var, p2Var, p3Var).unwrap();
        check_pass.enforce_equal(&Boolean::<Fq>::TRUE).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }
}
