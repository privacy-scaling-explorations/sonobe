/// This file implements the HyperNova's onchain (Ethereum's EVM) decider.
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_ff::PrimeField;
use ark_r1cs_std::{groups::GroupOpsBounds, prelude::CurveVar, ToConstraintFieldGadget};
use ark_snark::SNARK;
use ark_std::rand::{CryptoRng, RngCore};
use ark_std::{One, Zero};
use core::marker::PhantomData;

pub use super::decider_eth_circuit::DeciderEthCircuit;
use super::{lcccs::LCCCS, HyperNova};
use crate::commitment::{
    kzg::Proof as KZGProof, pedersen::Params as PedersenParams, CommitmentScheme,
};
use crate::folding::circuits::{nonnative::affine::NonNativeAffineVar, CF2};
use crate::frontend::FCircuit;
use crate::Error;
use crate::{Decider as DeciderTrait, FoldingScheme};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Proof<C1, CS1, S>
where
    C1: CurveGroup,
    CS1: CommitmentScheme<C1, ProverChallenge = C1::ScalarField, Challenge = C1::ScalarField>,
    S: SNARK<C1::ScalarField>,
{
    snark_proof: S::Proof,
    kzg_proof: CS1::Proof,
    // rho used at the last fold, U_{i+1}=NIMFS.V(rho, U_i, u_i), it is checked in-circuit
    rho: C1::ScalarField,
    U_i1: LCCCS<C1>, // U_{i+1}, which is checked in-circuit
    // the KZG challenge is provided by the prover, but in-circuit it is checked to match
    // the in-circuit computed computed one.
    kzg_challenge: C1::ScalarField,
}

/// Onchain Decider, for ethereum use cases
#[derive(Clone, Debug)]
pub struct Decider<C1, GC1, C2, GC2, FC, CS1, CS2, S, FS, const MU: usize, const NU: usize> {
    _c1: PhantomData<C1>,
    _gc1: PhantomData<GC1>,
    _c2: PhantomData<C2>,
    _gc2: PhantomData<GC2>,
    _fc: PhantomData<FC>,
    _cs1: PhantomData<CS1>,
    _cs2: PhantomData<CS2>,
    _s: PhantomData<S>,
    _fs: PhantomData<FS>,
}

impl<C1, GC1, C2, GC2, FC, CS1, CS2, S, FS, const MU: usize, const NU: usize>
    DeciderTrait<C1, C2, FC, FS> for Decider<C1, GC1, C2, GC2, FC, CS1, CS2, S, FS, MU, NU>
where
    C1: CurveGroup,
    C2: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField>,
    // CS1 is a KZG commitment, where challenge is C1::Fr elem
    CS1: CommitmentScheme<
        C1,
        ProverChallenge = C1::ScalarField,
        Challenge = C1::ScalarField,
        Proof = KZGProof<C1>,
    >,
    // enforce that the CS2 is Pedersen commitment scheme, since we're at Ethereum's EVM decider
    CS2: CommitmentScheme<C2, ProverParams = PedersenParams<C2>>,
    S: SNARK<C1::ScalarField>,
    FS: FoldingScheme<C1, C2, FC>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'b> &'b GC1: GroupOpsBounds<'b, C1, GC1>,
    for<'b> &'b GC2: GroupOpsBounds<'b, C2, GC2>,
    // constrain FS into HyperNova, since this is a Decider specifically for HyperNova
    HyperNova<C1, GC1, C2, GC2, FC, CS1, CS2, MU, NU, false>: From<FS>,
    crate::folding::hypernova::ProverParams<C1, C2, CS1, CS2, false>:
        From<<FS as FoldingScheme<C1, C2, FC>>::ProverParam>,
    crate::folding::hypernova::VerifierParams<C1, C2, CS1, CS2, false>:
        From<<FS as FoldingScheme<C1, C2, FC>>::VerifierParam>,
{
    type PreprocessorParam = (FS::ProverParam, FS::VerifierParam);
    type ProverParam = (S::ProvingKey, CS1::ProverParams);
    type Proof = Proof<C1, CS1, S>;
    /// VerifierParam = (pp_hash, snark::vk, commitment_scheme::vk)
    type VerifierParam = (C1::ScalarField, S::VerifyingKey, CS1::VerifierParams);
    type PublicInput = Vec<C1::ScalarField>;
    type CommittedInstance = ();

    fn preprocess(
        mut rng: impl RngCore + CryptoRng,
        prep_param: Self::PreprocessorParam,
        fs: FS,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), Error> {
        let circuit =
            DeciderEthCircuit::<C1, GC1, C2, GC2, CS1, CS2>::from_hypernova::<FC, MU, NU>(
                fs.into(),
            )
            .unwrap();

        // get the Groth16 specific setup for the circuit
        let (g16_pk, g16_vk) = S::circuit_specific_setup(circuit, &mut rng).unwrap();

        // get the FoldingScheme prover & verifier params from HyperNova
        #[allow(clippy::type_complexity)]
        let hypernova_pp: <HyperNova<C1, GC1, C2, GC2, FC, CS1, CS2, MU, NU, false> as FoldingScheme<
            C1,
            C2,
            FC,
        >>::ProverParam = prep_param.0.into();
        #[allow(clippy::type_complexity)]
        let hypernova_vp: <HyperNova<C1, GC1, C2, GC2, FC, CS1, CS2, MU, NU, false> as FoldingScheme<
            C1,
            C2,
            FC,
        >>::VerifierParam = prep_param.1.into();
        let pp_hash = hypernova_vp.pp_hash()?;

        let pp = (g16_pk, hypernova_pp.cs_pp);
        let vp = (pp_hash, g16_vk, hypernova_vp.cs_vp);
        Ok((pp, vp))
    }

    fn prove(
        mut rng: impl RngCore + CryptoRng,
        pp: Self::ProverParam,
        folding_scheme: FS,
    ) -> Result<Self::Proof, Error> {
        let (snark_pk, cs_pk): (S::ProvingKey, CS1::ProverParams) = pp;

        let circuit = DeciderEthCircuit::<C1, GC1, C2, GC2, CS1, CS2>::from_hypernova::<FC, MU, NU>(
            folding_scheme.into(),
        )?;

        let snark_proof = S::prove(&snark_pk, circuit.clone(), &mut rng)
            .map_err(|e| Error::Other(e.to_string()))?;

        // Notice that since the `circuit` has been constructed at the `from_hypernova` call, which
        // in case of failure it would have returned an error there, the next two unwraps should
        // never reach an error.
        let rho_Fr = circuit.rho.ok_or(Error::Empty)?;
        let W_i1 = circuit.W_i1.ok_or(Error::Empty)?;

        // get the challenges that have been already computed when preparing the circuit inputs in
        // the above `from_hypernova` call
        let challenge_W = circuit
            .kzg_challenge
            .ok_or(Error::MissingValue("kzg_challenge".to_string()))?;

        // generate KZG proofs
        let U_cmW_proof = CS1::prove_with_challenge(
            &cs_pk,
            challenge_W,
            &W_i1.w,
            &C1::ScalarField::zero(),
            None,
        )?;

        Ok(Self::Proof {
            snark_proof,
            kzg_proof: U_cmW_proof,
            rho: rho_Fr,
            U_i1: circuit.U_i1.ok_or(Error::Empty)?,
            kzg_challenge: challenge_W,
        })
    }

    fn verify(
        vp: Self::VerifierParam,
        i: C1::ScalarField,
        z_0: Vec<C1::ScalarField>,
        z_i: Vec<C1::ScalarField>,
        // we don't use the instances at the verifier level, since we check them in-circuit
        _running_instance: &Self::CommittedInstance,
        _incoming_instance: &Self::CommittedInstance,
        proof: &Self::Proof,
    ) -> Result<bool, Error> {
        if i <= C1::ScalarField::one() {
            return Err(Error::NotEnoughSteps);
        }

        let (pp_hash, snark_vk, cs_vk): (C1::ScalarField, S::VerifyingKey, CS1::VerifierParams) =
            vp;

        // Note: the NIMFS proof is checked inside the DeciderEthCircuit, which ensures that the
        // 'proof.U_i1' is correctly computed

        let (cmC_x, cmC_y) = NonNativeAffineVar::inputize(proof.U_i1.C)?;

        let public_input: Vec<C1::ScalarField> = [
            vec![pp_hash, i],
            z_0,
            z_i,
            // U_i+1:
            cmC_x,
            cmC_y,
            vec![proof.U_i1.u],
            proof.U_i1.x.clone(),
            proof.U_i1.r_x.clone(),
            proof.U_i1.v.clone(),
            vec![proof.kzg_challenge, proof.kzg_proof.eval, proof.rho],
        ]
        .concat();

        let snark_v = S::verify(&snark_vk, &public_input, &proof.snark_proof)
            .map_err(|e| Error::Other(e.to_string()))?;
        if !snark_v {
            return Err(Error::SNARKVerificationFail);
        }

        // we're at the Ethereum EVM case, so the CS1 is KZG commitments
        CS1::verify_with_challenge(&cs_vk, proof.kzg_challenge, &proof.U_i1.C, &proof.kzg_proof)?;

        Ok(true)
    }
}

#[cfg(test)]
pub mod tests {
    use ark_bn254::{constraints::GVar, Bn254, Fr, G1Projective as Projective};
    use ark_groth16::Groth16;
    use ark_grumpkin::{constraints::GVar as GVar2, Projective as Projective2};
    use std::time::Instant;

    use super::*;
    use crate::commitment::{kzg::KZG, pedersen::Pedersen};
    use crate::folding::hypernova::PreprocessorParam;
    use crate::frontend::tests::CubicFCircuit;
    use crate::transcript::poseidon::poseidon_canonical_config;

    #[test]
    fn test_decider() {
        const MU: usize = 1;
        const NU: usize = 1;
        // use HyperNova as FoldingScheme
        type HN = HyperNova<
            Projective,
            GVar,
            Projective2,
            GVar2,
            CubicFCircuit<Fr>,
            KZG<'static, Bn254>,
            Pedersen<Projective2>,
            MU,
            NU,
            false,
        >;
        type D = Decider<
            Projective,
            GVar,
            Projective2,
            GVar2,
            CubicFCircuit<Fr>,
            KZG<'static, Bn254>,
            Pedersen<Projective2>,
            Groth16<Bn254>, // here we define the Snark to use in the decider
            HN,             // here we define the FoldingScheme to use
            MU,
            NU,
        >;

        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();

        let F_circuit = CubicFCircuit::<Fr>::new(()).unwrap();
        let z_0 = vec![Fr::from(3_u32)];

        let prep_param = PreprocessorParam::new(poseidon_config, F_circuit);
        let hypernova_params = HN::preprocess(&mut rng, &prep_param).unwrap();

        let start = Instant::now();
        let mut hypernova = HN::init(&hypernova_params, F_circuit, z_0.clone()).unwrap();
        println!("Nova initialized, {:?}", start.elapsed());
        let start = Instant::now();
        hypernova
            .prove_step(&mut rng, vec![], Some((vec![], vec![])))
            .unwrap();
        println!("prove_step, {:?}", start.elapsed());
        hypernova
            .prove_step(&mut rng, vec![], Some((vec![], vec![])))
            .unwrap(); // do a 2nd step

        let mut rng = rand::rngs::OsRng;

        // prepare the Decider prover & verifier params
        let (decider_pp, decider_vp) =
            D::preprocess(&mut rng, hypernova_params, hypernova.clone()).unwrap();

        // decider proof generation
        let start = Instant::now();
        let proof = D::prove(rng, decider_pp, hypernova.clone()).unwrap();
        println!("Decider prove, {:?}", start.elapsed());

        // decider proof verification
        let start = Instant::now();
        let verified = D::verify(
            decider_vp,
            hypernova.i,
            hypernova.z_0,
            hypernova.z_i,
            &(),
            &(),
            &proof,
        )
        .unwrap();
        assert!(verified);
        println!("Decider verify, {:?}", start.elapsed());
    }
}
