/// This file implements the onchain (Ethereum's EVM) decider circuit. For non-ethereum use cases,
/// other more efficient approaches can be used.
use ark_crypto_primitives::sponge::poseidon::{constraints::PoseidonSpongeVar, PoseidonSponge};
use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    eq::EqGadget,
    fields::fp::FpVar,
    R1CSVar,
};
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_std::{borrow::Borrow, log2, marker::PhantomData};

use super::{
    circuits::{CCCSVar, LCCCSVar, NIMFSGadget, ProofVar as NIMFSProofVar},
    nimfs::{NIMFSProof, NIMFS},
    HyperNova, Witness, CCCS, LCCCS,
};
use crate::arith::{
    ccs::{circuits::CCSMatricesVar, CCS},
    ArithRelationGadget,
};
use crate::commitment::{pedersen::Params as PedersenParams, CommitmentScheme};
use crate::folding::circuits::{
    decider::{
        on_chain::GenericOnchainDeciderCircuit, DeciderEnabledNIFS, EvalGadget, KZGChallengesGadget,
    },
    CF1,
};
use crate::folding::traits::{WitnessOps, WitnessVarOps};
use crate::frontend::FCircuit;
use crate::transcript::Transcript;
use crate::utils::gadgets::{eval_mle, MatrixGadget};
use crate::{Curve, Error};

impl<C: Curve> ArithRelationGadget<WitnessVar<CF1<C>>, LCCCSVar<C>> for CCSMatricesVar<CF1<C>> {
    type Evaluation = Vec<FpVar<CF1<C>>>;

    fn eval_relation(
        &self,
        w: &WitnessVar<CF1<C>>,
        u: &LCCCSVar<C>,
    ) -> Result<Self::Evaluation, SynthesisError> {
        let z = [&[u.u.clone()][..], &u.x, &w.w].concat();

        self.M
            .iter()
            .map(|M_j| {
                let s = log2(M_j.n_rows) as usize;
                let Mz = M_j.mul_vector(&z)?;
                Ok(eval_mle(s, Mz, u.r_x.clone()))
            })
            .collect()
    }

    fn enforce_evaluation(
        _w: &WitnessVar<CF1<C>>,
        u: &LCCCSVar<C>,
        v: Self::Evaluation,
    ) -> Result<(), SynthesisError> {
        v.enforce_equal(&u.v)
    }
}

/// In-circuit representation of the Witness associated to the CommittedInstance.
#[derive(Debug, Clone)]
pub struct WitnessVar<F: PrimeField> {
    pub w: Vec<FpVar<F>>,
    pub r_w: FpVar<F>,
}

impl<F: PrimeField> AllocVar<Witness<F>, F> for WitnessVar<F> {
    fn new_variable<T: Borrow<Witness<F>>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let w: Vec<FpVar<F>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().w.clone()), mode)?;
            let r_w = FpVar::<F>::new_variable(cs.clone(), || Ok(val.borrow().r_w), mode)?;

            Ok(Self { w, r_w })
        })
    }
}

impl<F: PrimeField> WitnessVarOps<F> for WitnessVar<F> {
    fn get_openings(&self) -> Vec<(&[FpVar<F>], FpVar<F>)> {
        vec![(&self.w, self.r_w.clone())]
    }
}

pub type DeciderEthCircuit<C1, C2> = GenericOnchainDeciderCircuit<
    C1,
    C2,
    LCCCS<C1>,
    CCCS<C1>,
    Witness<CF1<C1>>,
    CCS<CF1<C1>>,
    CCSMatricesVar<CF1<C1>>,
    DeciderHyperNovaGadget,
>;

impl<
        C1: Curve,
        C2: Curve,
        FC: FCircuit<C1::ScalarField>,
        CS1: CommitmentScheme<C1, H>,
        // enforce that the CS2 is Pedersen commitment scheme, since we're at Ethereum's EVM decider
        CS2: CommitmentScheme<C2, H, ProverParams = PedersenParams<C2>>,
        const MU: usize,
        const NU: usize,
        const H: bool,
    > TryFrom<HyperNova<C1, C2, FC, CS1, CS2, MU, NU, H>> for DeciderEthCircuit<C1, C2>
{
    type Error = Error;

    fn try_from(hn: HyperNova<C1, C2, FC, CS1, CS2, MU, NU, H>) -> Result<Self, Error> {
        // compute the U_{i+1}, W_{i+1}, by folding the last running & incoming instances
        let mut transcript = PoseidonSponge::new_with_pp_hash(&hn.poseidon_config, hn.pp_hash);
        let (nimfs_proof, U_i1, W_i1, rho) = NIMFS::<C1, PoseidonSponge<C1::ScalarField>>::prove(
            &mut transcript,
            &hn.ccs,
            &[hn.U_i.clone()],
            &[hn.u_i.clone()],
            &[hn.W_i.clone()],
            &[hn.w_i.clone()],
        )?;

        // compute the KZG challenges used as inputs in the circuit
        let kzg_challenges = KZGChallengesGadget::get_challenges_native(&mut transcript, &U_i1);

        // get KZG evals
        let kzg_evaluations = W_i1
            .get_openings()
            .iter()
            .zip(&kzg_challenges)
            .map(|((v, _), &c)| EvalGadget::evaluate_native(v, c))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(Self {
            _avar: PhantomData,
            arith: hn.ccs,
            cf_arith: hn.cf_r1cs,
            cf_pedersen_params: hn.cf_cs_pp,
            poseidon_config: hn.poseidon_config,
            pp_hash: hn.pp_hash,
            i: hn.i,
            z_0: hn.z_0,
            z_i: hn.z_i,
            U_i: hn.U_i,
            W_i: hn.W_i,
            u_i: hn.u_i,
            w_i: hn.w_i,
            U_i1,
            W_i1,
            proof: nimfs_proof,
            randomness: rho,
            cf_U_i: hn.cf_U_i,
            cf_W_i: hn.cf_W_i,
            kzg_challenges,
            kzg_evaluations,
        })
    }
}

pub struct DeciderHyperNovaGadget;

impl<C: Curve> DeciderEnabledNIFS<C, LCCCS<C>, CCCS<C>, Witness<C::ScalarField>, CCS<CF1<C>>>
    for DeciderHyperNovaGadget
{
    type ProofDummyCfg = (usize, usize, usize, usize);
    type Proof = NIMFSProof<C>;
    type Randomness = CF1<C>;
    type RandomnessDummyCfg = ();

    fn fold_field_elements_gadget(
        arith: &CCS<CF1<C>>,
        transcript: &mut PoseidonSpongeVar<CF1<C>>,
        U: LCCCSVar<C>,
        _U_vec: Vec<FpVar<CF1<C>>>,
        u: CCCSVar<C>,
        proof: Self::Proof,
        randomness: Self::Randomness,
    ) -> Result<LCCCSVar<C>, SynthesisError> {
        let cs = U.u.cs();
        let nimfs_proof = NIMFSProofVar::<C>::new_witness(cs.clone(), || Ok(proof))?;
        let rho = FpVar::<CF1<C>>::new_input(cs.clone(), || Ok(randomness))?;
        let (computed_U_i1, rho_bits) = NIMFSGadget::<C>::verify(
            cs.clone(),
            arith,
            transcript,
            &[U],
            &[u],
            nimfs_proof,
            Boolean::TRUE, // enabled
        )?;
        Boolean::le_bits_to_fp(&rho_bits)?.enforce_equal(&rho)?;
        Ok(computed_U_i1)
    }

    fn fold_group_elements_native(
        U_commitments: &[C],
        u_commitments: &[C],
        _: Option<Self::Proof>,
        r: Self::Randomness,
    ) -> Result<Vec<C>, Error> {
        let U_C = U_commitments[0];
        let u_C = u_commitments[0];
        let C = U_C + u_C.mul(r);
        Ok(vec![C])
    }
}

#[cfg(test)]
pub mod tests {
    use ark_bn254::{Fr, G1Projective as Projective};
    use ark_grumpkin::Projective as Projective2;
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    use ark_std::{test_rng, UniformRand};

    use super::*;
    use crate::arith::{r1cs::R1CS, Arith};
    use crate::commitment::pedersen::Pedersen;
    use crate::folding::nova::PreprocessorParam;
    use crate::frontend::utils::CubicFCircuit;
    use crate::transcript::poseidon::poseidon_canonical_config;
    use crate::FoldingScheme;

    #[test]
    fn test_lcccs_checker_gadget() -> Result<(), Error> {
        let mut rng = test_rng();
        let n_rows = 2_u32.pow(5) as usize;
        let n_cols = 2_u32.pow(5) as usize;
        let r1cs = R1CS::<Fr>::rand(&mut rng, n_rows, n_cols);
        let ccs = CCS::from(r1cs);
        let z: Vec<Fr> = (0..n_cols).map(|_| Fr::rand(&mut rng)).collect();

        let (pedersen_params, _) = Pedersen::<Projective>::setup(&mut rng, ccs.n_witnesses())?;

        let (lcccs, w) = ccs.to_lcccs::<_, Projective, Pedersen<Projective>, false>(
            &mut rng,
            &pedersen_params,
            &z,
        )?;

        let cs = ConstraintSystem::<Fr>::new_ref();

        // CCS's (sparse) matrices are constants in the circuit
        let ccs_mat = CCSMatricesVar::<Fr>::new_constant(cs.clone(), ccs.clone())?;
        let w_var = WitnessVar::new_witness(cs.clone(), || Ok(w))?;
        let lcccs_var = LCCCSVar::new_input(cs.clone(), || Ok(lcccs))?;

        ccs_mat.enforce_relation(&w_var, &lcccs_var)?;

        assert!(cs.is_satisfied()?);
        Ok(())
    }

    #[test]
    fn test_decider_circuit() -> Result<(), Error> {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();

        let F_circuit = CubicFCircuit::<Fr>::new(())?;
        let z_0 = vec![Fr::from(3_u32)];

        const MU: usize = 1;
        const NU: usize = 1;

        type HN = HyperNova<
            Projective,
            Projective2,
            CubicFCircuit<Fr>,
            Pedersen<Projective>,
            Pedersen<Projective2>,
            MU,
            NU,
            false,
        >;
        let prep_param = PreprocessorParam::<
            Projective,
            Projective2,
            CubicFCircuit<Fr>,
            Pedersen<Projective>,
            Pedersen<Projective2>,
            false,
        >::new(poseidon_config, F_circuit);
        let hn_params = HN::preprocess(&mut rng, &prep_param)?;

        // generate a Nova instance and do a step of it
        let mut hypernova = HN::init(&hn_params, F_circuit, z_0.clone())?;
        hypernova.prove_step(&mut rng, (), None)?;

        let ivc_proof = hypernova.ivc_proof();
        HN::verify(hn_params.1, ivc_proof)?;

        // load the DeciderEthCircuit from the generated Nova instance
        let decider_circuit = DeciderEthCircuit::<Projective, Projective2>::try_from(hypernova)?;

        let cs = ConstraintSystem::<Fr>::new_ref();

        // generate the constraints and check that are satisfied by the inputs
        decider_circuit.generate_constraints(cs.clone())?;
        assert!(cs.is_satisfied()?);
        dbg!(cs.num_constraints());
        Ok(())
    }
}
