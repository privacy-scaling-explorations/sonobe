use crate::utils::espresso::sum_check::SumCheck;
use crate::{
    transcript::{
        poseidon::{PoseidonTranscript, PoseidonTranscriptVar},
        TranscriptVar,
    },
    utils::sum_check::{structs::IOPProof, IOPSumCheck},
};
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
/// Heavily inspired from testudo: https://github.com/cryptonetlab/testudo/tree/master
/// Some changes:
/// - Typings to better stick to ark_poly's API
/// - Uses `folding-schemes`' own `TranscriptVar` trait and `PoseidonTranscriptVar` struct
/// - API made closer to gadgets found in `folding-schemes`
use ark_ff::PrimeField;
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    eq::EqGadget,
    fields::fp::FpVar,
};
use ark_relations::r1cs::{Namespace, SynthesisError};
use std::{borrow::Borrow, marker::PhantomData};

#[derive(Clone, Debug)]
pub struct DensePolynomialVar<F: PrimeField> {
    pub coeffs: Vec<FpVar<F>>,
}

impl<F: PrimeField> AllocVar<DensePolynomial<F>, F> for DensePolynomialVar<F> {
    fn new_variable<T: Borrow<DensePolynomial<F>>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|c| {
            let cs = cs.into();
            let cp: &DensePolynomial<F> = c.borrow();
            let mut coeffs_var = Vec::<FpVar<F>>::with_capacity(cp.coeffs.len());
            for coeff in cp.coeffs.iter() {
                let coeff_var = FpVar::<F>::new_variable(cs.clone(), || Ok(coeff), mode)?;
                coeffs_var.push(coeff_var);
            }
            Ok(Self { coeffs: coeffs_var })
        })
    }
}

impl<F: PrimeField> DensePolynomialVar<F> {
    pub fn eval_at_zero(&self) -> FpVar<F> {
        self.coeffs[0].clone()
    }

    pub fn eval_at_one(&self) -> FpVar<F> {
        let mut res = self.coeffs[0].clone();
        for i in 1..self.coeffs.len() {
            res = &res + &self.coeffs[i];
        }
        res
    }

    pub fn evaluate(&self, r: &FpVar<F>) -> FpVar<F> {
        let mut eval = self.coeffs[0].clone();
        let mut power = r.clone();

        for i in 1..self.coeffs.len() {
            eval += &power * &self.coeffs[i];
            power *= r;
        }
        eval
    }
}

#[derive(Clone, Debug)]
pub struct IOPProofVar<C: CurveGroup> {
    // We have to be generic over a CurveGroup because instantiating a IOPProofVar will call IOPSumCheck which requires a CurveGroup
    pub proofs: Vec<DensePolynomialVar<C::ScalarField>>,
    pub claim: FpVar<C::ScalarField>,
}

impl<C: CurveGroup> AllocVar<IOPProof<C::ScalarField>, C::ScalarField> for IOPProofVar<C>
where
    <C as Group>::ScalarField: Absorb,
{
    fn new_variable<T: Borrow<IOPProof<C::ScalarField>>>(
        _cs: impl Into<Namespace<C::ScalarField>>,
        _f: impl FnOnce() -> Result<T, SynthesisError>,
        _mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        _f().and_then(|c| {
            let cs = _cs.into();
            let cp: &IOPProof<C::ScalarField> = c.borrow();
            let claim = IOPSumCheck::<C, PoseidonTranscript<C>>::extract_sum(cp);
            let claim = FpVar::<C::ScalarField>::new_variable(cs.clone(), || Ok(claim), _mode)?;
            let mut proofs =
                Vec::<DensePolynomialVar<C::ScalarField>>::with_capacity(cp.proofs.len());
            for proof in cp.proofs.iter() {
                let poly = DensePolynomial::from_coefficients_slice(&proof.coeffs);
                let proof = DensePolynomialVar::<C::ScalarField>::new_variable(
                    cs.clone(),
                    || Ok(poly),
                    _mode,
                )?;
                proofs.push(proof);
            }
            Ok(Self { proofs, claim })
        })
    }
}

/// Auxillary information for a polynomial, (num_variables, max_degree)
type PolyAuxInfo = (usize, usize);

#[derive(Clone, Debug)]
pub struct PolyAuxInfoVar<F: PrimeField> {
    pub num_variables: FpVar<F>,
    pub max_degree: FpVar<F>,
}

impl<F: PrimeField> AllocVar<PolyAuxInfo, F> for PolyAuxInfoVar<F> {
    fn new_variable<T: Borrow<PolyAuxInfo>>(
        _cs: impl Into<Namespace<F>>,
        _f: impl FnOnce() -> Result<T, SynthesisError>,
        _mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        _f().and_then(|c| {
            let cs = _cs.into();
            let cp: &PolyAuxInfo = c.borrow();
            let num_variables =
                FpVar::<F>::new_variable(cs.clone(), || Ok(F::from(cp.0 as u64)), _mode)?;
            let max_degree =
                FpVar::<F>::new_variable(cs.clone(), || Ok(F::from(cp.1 as u64)), _mode)?;
            Ok(Self {
                num_variables,
                max_degree,
            })
        })
    }
}

#[derive(Debug, Clone)]
pub struct SumCheckVerifierGadget<C: CurveGroup> {
    _f: PhantomData<C>,
}

impl<C: CurveGroup> SumCheckVerifierGadget<C> {
    pub fn verify(
        iop_proof_var: &IOPProofVar<C>,
        poly_aux_info_var: &PolyAuxInfoVar<C::ScalarField>,
        transcript_var: &mut PoseidonTranscriptVar<C::ScalarField>,
    ) -> Result<(FpVar<C::ScalarField>, Vec<FpVar<C::ScalarField>>), SynthesisError> {
        let mut e_var = iop_proof_var.claim.clone();
        let mut r_vars: Vec<FpVar<C::ScalarField>> = Vec::new();
        transcript_var.absorb(poly_aux_info_var.num_variables.clone())?;
        transcript_var.absorb(poly_aux_info_var.max_degree.clone())?;

        for poly_var in iop_proof_var.proofs.iter() {
            let res = poly_var.eval_at_one() + poly_var.eval_at_zero();
            res.enforce_equal(&e_var)?;
            transcript_var.absorb_vec(&poly_var.coeffs)?;
            let r_i_var = transcript_var.get_challenge()?;
            e_var = poly_var.evaluate(&r_i_var);
            r_vars.push(r_i_var);
        }

        Ok((e_var, r_vars))
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        folding::circuits::sum_check::{IOPProofVar, PolyAuxInfoVar},
        transcript::{
            poseidon::{tests::poseidon_test_config, PoseidonTranscript, PoseidonTranscriptVar},
            Transcript, TranscriptVar,
        },
        utils::{
            sum_check::{structs::IOPProof, IOPSumCheck, SumCheck},
            virtual_polynomial::VirtualPolynomial,
        },
    };
    use ark_crypto_primitives::sponge::{poseidon::PoseidonConfig, Absorb};
    use ark_ec::CurveGroup;
    use ark_ff::Field;
    use ark_pallas::{Fr, Projective};
    use ark_poly::{DenseMultilinearExtension, MultilinearExtension};
    use ark_r1cs_std::alloc::{AllocVar, AllocationMode};
    use ark_relations::r1cs::ConstraintSystem;
    use std::sync::Arc;

    use super::SumCheckVerifierGadget;

    pub type TestSumCheckProof<F> = (VirtualPolynomial<F>, PoseidonConfig<F>, IOPProof<F>);

    /// Primarily used for testing the sumcheck gadget
    /// Returns a random virtual polynomial, the poseidon config used and the associated sumcheck proof
    pub fn get_test_sumcheck_proof<C: CurveGroup>(
        num_vars: usize,
    ) -> TestSumCheckProof<C::ScalarField>
    where
        <C as ark_ec::Group>::ScalarField: Absorb,
    {
        let mut rng = ark_std::test_rng();
        let poseidon_config: PoseidonConfig<C::ScalarField> =
            poseidon_test_config::<C::ScalarField>();
        let mut poseidon_transcript_prove = PoseidonTranscript::<C>::new(&poseidon_config);
        let poly_mle = DenseMultilinearExtension::rand(num_vars, &mut rng);
        let virtual_poly =
            VirtualPolynomial::new_from_mle(&Arc::new(poly_mle), C::ScalarField::ONE);
        let sum_check: IOPProof<C::ScalarField> = IOPSumCheck::<C, PoseidonTranscript<C>>::prove(
            &virtual_poly,
            &mut poseidon_transcript_prove,
        )
        .unwrap();
        (virtual_poly, poseidon_config, sum_check)
    }

    #[test]
    fn test_sum_check_circuit() {
        for num_vars in 1..15 {
            let cs = ConstraintSystem::<Fr>::new_ref();
            let (virtual_poly, poseidon_config, sum_check) =
                get_test_sumcheck_proof::<Projective>(num_vars);
            let mut poseidon_var: PoseidonTranscriptVar<Fr> =
                PoseidonTranscriptVar::new(cs.clone(), &poseidon_config);
            let iop_proof_var = IOPProofVar::<Projective>::new_variable(
                cs.clone(),
                || Ok(&sum_check),
                AllocationMode::Witness,
            )
            .unwrap();
            let poly_aux_info_var = PolyAuxInfoVar::<Fr>::new_variable(
                cs.clone(),
                || {
                    Ok((
                        virtual_poly.aux_info.num_variables,
                        virtual_poly.aux_info.max_degree,
                    ))
                },
                AllocationMode::Witness,
            )
            .unwrap();
            let res = SumCheckVerifierGadget::<Projective>::verify(
                &iop_proof_var,
                &poly_aux_info_var,
                &mut poseidon_var,
            );
            assert!(res.is_ok());
            assert!(cs.is_satisfied().unwrap());
        }
    }
}
