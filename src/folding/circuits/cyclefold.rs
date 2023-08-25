/// Implements the C_{EC} circuit described in CycleFold paper https://eprint.iacr.org/2023/1192.pdf
use ark_ec::CurveGroup;
use ark_r1cs_std::{fields::nonnative::NonNativeFieldVar, prelude::CurveVar, ToBitsGadget};
use ark_relations::r1cs::SynthesisError;
use core::marker::PhantomData;

use super::ConstraintF;

/// ECRLC implements gadget that checks the Elliptic Curve points RandomLinearCombination described
/// in CycleFold (https://eprint.iacr.org/2023/1192.pdf).
#[derive(Debug)]
pub struct ECRLC<C: CurveGroup, GC: CurveVar<C, ConstraintF<C>>> {
    _c: PhantomData<C>,
    _gc: PhantomData<GC>,
}
impl<C: CurveGroup, GC: CurveVar<C, ConstraintF<C>>> ECRLC<C, GC> {
    pub fn check(
        r: NonNativeFieldVar<C::ScalarField, ConstraintF<C>>,
        p1: GC,
        p2: GC,
        p3: GC,
    ) -> Result<(), SynthesisError> {
        p3.enforce_equal(&(p1 + p2.scalar_mul_le(r.to_bits_le()?.iter())?))?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use ark_bls12_377::{constraints::G1Var, Fq, Fr, G1Projective};
    use ark_r1cs_std::alloc::AllocVar;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::UniformRand;
    use std::ops::Mul;

    /// Let Curve1=bls12-377::G1 and Curve2=bw6-761::G1. Here we have our constraint system will
    /// work over Curve2::Fr = bw6-761::Fr (=bls12-377::Fq), thus our points are P_i \in Curve1
    /// (=bls12-377).
    #[test]
    fn test_ecrlc_check() {
        let mut rng = ark_std::test_rng();

        let r = Fr::rand(&mut rng);
        let p1 = G1Projective::rand(&mut rng);
        let p2 = G1Projective::rand(&mut rng);
        let p3 = p1 + p2.mul(r);

        let cs = ConstraintSystem::<Fq>::new_ref(); // CS over Curve2::Fr = Curve1::Fq

        // prepare circuit inputs
        let rVar = NonNativeFieldVar::<Fr, Fq>::new_witness(cs.clone(), || Ok(r)).unwrap();
        let p1Var = G1Var::new_witness(cs.clone(), || Ok(p1)).unwrap();
        let p2Var = G1Var::new_witness(cs.clone(), || Ok(p2)).unwrap();
        let p3Var = G1Var::new_witness(cs.clone(), || Ok(p3)).unwrap();

        // check ECRLC circuit
        ECRLC::<G1Projective, G1Var>::check(rVar, p1Var, p2Var, p3Var).unwrap();
        assert!(cs.is_satisfied().unwrap());
        // dbg!(cs.num_constraints());
    }
}
