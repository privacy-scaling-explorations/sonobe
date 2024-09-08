use ark_crypto_primitives::sponge::{constraints::AbsorbGadget, Absorb};
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_r1cs_std::{fields::fp::FpVar, uint8::UInt8, ToConstraintFieldGadget};
use ark_relations::r1cs::SynthesisError;
use ark_std::{cfg_into_iter, log2, One};
use rayon::prelude::*;

use super::{utils::pow_i, CommittedInstance, CommittedInstanceVar, Witness};
use crate::{
    arith::{r1cs::R1CS, Arith},
    folding::circuits::CF1,
    transcript::AbsorbNonNative,
    utils::vec::is_zero_vec,
    Error,
};

// Implements the trait for absorbing ProtoGalaxy's CommittedInstance.
impl<C: CurveGroup> Absorb for CommittedInstance<C>
where
    C::ScalarField: Absorb,
{
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        C::ScalarField::batch_to_sponge_bytes(&self.to_sponge_field_elements_as_vec(), dest);
    }

    fn to_sponge_field_elements<F: PrimeField>(&self, dest: &mut Vec<F>) {
        self.phi
            .to_native_sponge_field_elements_as_vec()
            .to_sponge_field_elements(dest);
        self.betas.to_sponge_field_elements(dest);
        self.e.to_sponge_field_elements(dest);
        self.x.to_sponge_field_elements(dest);
    }
}

// Implements the trait for absorbing ProtoGalaxy's CommittedInstanceVar in-circuit.
impl<C: CurveGroup> AbsorbGadget<C::ScalarField> for CommittedInstanceVar<C> {
    fn to_sponge_bytes(&self) -> Result<Vec<UInt8<C::ScalarField>>, SynthesisError> {
        FpVar::batch_to_sponge_bytes(&self.to_sponge_field_elements()?)
    }

    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<C::ScalarField>>, SynthesisError> {
        Ok([
            self.phi.to_constraint_field()?,
            self.betas.to_sponge_field_elements()?,
            self.e.to_sponge_field_elements()?,
            self.x.to_sponge_field_elements()?,
        ]
        .concat())
    }
}

impl<C: CurveGroup> Arith<Witness<CF1<C>>, CommittedInstance<C>> for R1CS<CF1<C>> {
    type Evaluation = Vec<CF1<C>>;

    fn eval_relation(
        &self,
        w: &Witness<CF1<C>>,
        u: &CommittedInstance<C>,
    ) -> Result<Self::Evaluation, Error> {
        self.eval_core(&[&[C::ScalarField::one()][..], &u.x, &w.w].concat())
    }

    fn check_evaluation(
        _w: &Witness<C::ScalarField>,
        u: &CommittedInstance<C>,
        e: Vec<C::ScalarField>,
    ) -> Result<(), Error> {
        let ok = if u.betas.is_empty() {
            // incoming instance
            is_zero_vec(&e)
        } else {
            // running instance
            if u.betas.len() != log2(e.len()) as usize {
                return Err(Error::NotSameLength(
                    "instance.betas.len()".to_string(),
                    u.betas.len(),
                    "log2(e.len())".to_string(),
                    log2(e.len()) as usize,
                ));
            }

            u.e == cfg_into_iter!(e)
                .enumerate()
                .map(|(i, e_i)| pow_i(i, &u.betas) * e_i)
                .sum::<CF1<C>>()
        };
        ok.then_some(()).ok_or(Error::NotSatisfied)
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_bn254::{Fr, G1Projective as Projective};
    use ark_r1cs_std::{alloc::AllocVar, R1CSVar};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::UniformRand;
    use rand::Rng;

    /// test that checks the native CommittedInstance.to_sponge_{bytes,field_elements}
    /// vs the R1CS constraints version
    #[test]
    pub fn test_committed_instance_to_sponge_preimage() {
        let mut rng = ark_std::test_rng();

        let t = rng.gen::<u8>() as usize;
        let io_len = rng.gen::<u8>() as usize;

        let ci = CommittedInstance::<Projective> {
            phi: Projective::rand(&mut rng),
            betas: (0..t).map(|_| Fr::rand(&mut rng)).collect(),
            e: Fr::rand(&mut rng),
            x: (0..io_len).map(|_| Fr::rand(&mut rng)).collect(),
        };

        let bytes = ci.to_sponge_bytes_as_vec();
        let field_elements = ci.to_sponge_field_elements_as_vec();

        let cs = ConstraintSystem::<Fr>::new_ref();

        let ciVar =
            CommittedInstanceVar::<Projective>::new_witness(cs.clone(), || Ok(ci.clone())).unwrap();
        let bytes_var = ciVar.to_sponge_bytes().unwrap();
        let field_elements_var = ciVar.to_sponge_field_elements().unwrap();

        assert!(cs.is_satisfied().unwrap());

        // check that the natively computed and in-circuit computed hashes match
        assert_eq!(bytes_var.value().unwrap(), bytes);
        assert_eq!(field_elements_var.value().unwrap(), field_elements);
    }
}
