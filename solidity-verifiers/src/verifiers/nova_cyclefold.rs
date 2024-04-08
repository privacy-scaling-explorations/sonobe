#![allow(non_snake_case)]
#![allow(non_camel_case_types)]

use crate::utils::HeaderInclusion;
use crate::{Groth16Data, KzgData, ProtocolData, PRAGMA_GROTH16_VERIFIER};
use ark_bn254::{Bn254, G1Affine};
use ark_groth16::VerifyingKey;
use ark_poly_commit::kzg10::VerifierKey;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use askama::Template;

use super::g16::Groth16Verifier;
use super::kzg::KZG10Verifier;

pub fn get_decider_template_for_cyclefold_decider(
    nova_cyclefold_data: NovaCycleFoldData,
) -> String {
    HeaderInclusion::<NovaCycleFoldDecider>::builder()
        .template(nova_cyclefold_data)
        .build()
        .render()
        .unwrap()
}

#[derive(Template, Default)]
#[template(path = "nova_cyclefold_decider.askama.sol", ext = "sol")]
pub(crate) struct NovaCycleFoldDecider {
    groth16_verifier: Groth16Verifier,
    kzg10_verifier: KZG10Verifier,
    z_len: usize,
    public_inputs_len: usize,
}

impl From<NovaCycleFoldData> for NovaCycleFoldDecider {
    fn from(value: NovaCycleFoldData) -> Self {
        let groth16_verifier = Groth16Verifier::from(value.g16_data);
        let public_inputs_len = groth16_verifier.gamma_abc_len;
        Self {
            groth16_verifier,
            kzg10_verifier: KZG10Verifier::from(value.kzg_data),
            z_len: value.z_len,
            public_inputs_len,
        }
    }
}

#[derive(CanonicalDeserialize, CanonicalSerialize, PartialEq, Debug, Clone)]
pub struct NovaCycleFoldData {
    g16_data: Groth16Data,
    kzg_data: KzgData,
    z_len: usize,
}

impl ProtocolData for NovaCycleFoldData {
    const PROTOCOL_NAME: &'static str = "NovaCycleFold";

    fn render_as_template(self, pragma: Option<String>) -> Vec<u8> {
        HeaderInclusion::<NovaCycleFoldDecider>::builder()
            .pragma_version(pragma.unwrap_or(PRAGMA_GROTH16_VERIFIER.to_string()))
            .template(self)
            .build()
            .render()
            .unwrap()
            .into_bytes()
    }
}

impl From<(Groth16Data, KzgData, usize)> for NovaCycleFoldData {
    fn from(value: (Groth16Data, KzgData, usize)) -> Self {
        Self {
            g16_data: value.0,
            kzg_data: value.1,
            z_len: value.2,
        }
    }
}

impl NovaCycleFoldData {
    pub fn new(
        vkey_g16: VerifyingKey<Bn254>,
        vkey_kzg: VerifierKey<Bn254>,
        crs_points: Vec<G1Affine>,
        z_len: usize,
    ) -> Self {
        Self {
            g16_data: Groth16Data::from(vkey_g16),
            kzg_data: KzgData::from((vkey_kzg, crs_points)),
            z_len,
        }
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::{constraints::GVar, Bn254, Fr, G1Projective as G1};
    use ark_crypto_primitives::snark::SNARK;
    use ark_ff::PrimeField;
    use ark_groth16::VerifyingKey as G16VerifierKey;
    use ark_groth16::{Groth16, ProvingKey};
    use ark_grumpkin::{constraints::GVar as GVar2, Projective as G2};
    use ark_poly_commit::kzg10::VerifierKey as KZGVerifierKey;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::fields::fp::FpVar;
    use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
    use ark_std::Zero;
    use askama::Template;
    use std::marker::PhantomData;
    use std::time::Instant;

    use folding_schemes::{
        commitment::{
            kzg::{ProverKey as KZGProverKey, KZG},
            pedersen::Pedersen,
            CommitmentScheme,
        },
        folding::nova::{
            decider_eth::{prepare_calldata, Decider as DeciderEth},
            decider_eth_circuit::DeciderEthCircuit,
            get_cs_params_len, Nova, ProverParams,
        },
        frontend::FCircuit,
        transcript::poseidon::poseidon_test_config,
        Decider, Error, FoldingScheme,
    };

    use super::NovaCycleFoldDecider;
    use crate::verifiers::tests::{setup, DEFAULT_SETUP_LEN};
    use crate::{
        evm::{compile_solidity, save_solidity, Evm},
        utils::{get_function_selector_for_nova_cyclefold_verifier, HeaderInclusion},
        verifiers::nova_cyclefold::get_decider_template_for_cyclefold_decider,
        Groth16Data, KzgData, NovaCycleFoldData, ProtocolData,
    };

    /// Test circuit to be folded
    #[derive(Clone, Copy, Debug)]
    pub struct CubicFCircuit<F: PrimeField> {
        _f: PhantomData<F>,
    }
    impl<F: PrimeField> FCircuit<F> for CubicFCircuit<F> {
        type Params = ();
        fn new(_params: Self::Params) -> Self {
            Self { _f: PhantomData }
        }
        fn state_len(&self) -> usize {
            1
        }
        fn step_native(&self, _i: usize, z_i: Vec<F>) -> Result<Vec<F>, Error> {
            Ok(vec![z_i[0] * z_i[0] * z_i[0] + z_i[0] + F::from(5_u32)])
        }
        fn generate_step_constraints(
            &self,
            cs: ConstraintSystemRef<F>,
            _i: usize,
            z_i: Vec<FpVar<F>>,
        ) -> Result<Vec<FpVar<F>>, SynthesisError> {
            let five = FpVar::<F>::new_constant(cs.clone(), F::from(5u32))?;
            let z_i = z_i[0].clone();

            Ok(vec![&z_i * &z_i * &z_i + &z_i + &five])
        }
    }

    /// This is the circuit that we want to fold, it implements the FCircuit trait. The parameter z_i
    /// denotes the current state which contains 5 elements, and z_{i+1} denotes the next state which
    /// we get by applying the step.
    /// In this example we set z_i and z_{i+1} to have five elements, and at each step we do different
    /// operations on each of them.
    #[derive(Clone, Copy, Debug)]
    pub struct MultiInputsFCircuit<F: PrimeField> {
        _f: PhantomData<F>,
    }
    impl<F: PrimeField> FCircuit<F> for MultiInputsFCircuit<F> {
        type Params = ();

        fn new(_params: Self::Params) -> Self {
            Self { _f: PhantomData }
        }
        fn state_len(&self) -> usize {
            5
        }

        /// computes the next state values in place, assigning z_{i+1} into z_i, and computing the new
        /// z_{i+1}
        fn step_native(&self, _i: usize, z_i: Vec<F>) -> Result<Vec<F>, Error> {
            let a = z_i[0] + F::from(4_u32);
            let b = z_i[1] + F::from(40_u32);
            let c = z_i[2] * F::from(4_u32);
            let d = z_i[3] * F::from(40_u32);
            let e = z_i[4] + F::from(100_u32);

            Ok(vec![a, b, c, d, e])
        }

        /// generates the constraints for the step of F for the given z_i
        fn generate_step_constraints(
            &self,
            cs: ConstraintSystemRef<F>,
            _i: usize,
            z_i: Vec<FpVar<F>>,
        ) -> Result<Vec<FpVar<F>>, SynthesisError> {
            let four = FpVar::<F>::new_constant(cs.clone(), F::from(4u32))?;
            let forty = FpVar::<F>::new_constant(cs.clone(), F::from(40u32))?;
            let onehundred = FpVar::<F>::new_constant(cs.clone(), F::from(100u32))?;
            let a = z_i[0].clone() + four.clone();
            let b = z_i[1].clone() + forty.clone();
            let c = z_i[2].clone() * four;
            let d = z_i[3].clone() * forty;
            let e = z_i[4].clone() + onehundred;

            Ok(vec![a, b, c, d, e])
        }
    }

    #[test]
    fn nova_cyclefold_data_serde_roundtrip() {
        let (kzg_pk, kzg_vk, _, g16_vk, _) = setup(DEFAULT_SETUP_LEN);
        let g16_data = Groth16Data::from(g16_vk);
        let kzg_data = KzgData::from((kzg_vk, kzg_pk.powers_of_g[0..3].to_vec()));

        let mut bytes = vec![];
        let nova_cyclefold_data = NovaCycleFoldData::from((g16_data, kzg_data, 1));

        nova_cyclefold_data
            .serialize_protocol_data(&mut bytes)
            .unwrap();
        let obtained_nova_cyclefold_data =
            NovaCycleFoldData::deserialize_protocol_data(bytes.as_slice()).unwrap();

        assert_eq!(nova_cyclefold_data, obtained_nova_cyclefold_data)
    }

    #[test]
    fn nova_cyclefold_decider_template_renders() {
        let (kzg_pk, kzg_vk, _, g16_vk, _) = setup(DEFAULT_SETUP_LEN);
        let g16_data = Groth16Data::from(g16_vk);
        let kzg_data = KzgData::from((kzg_vk, kzg_pk.powers_of_g[0..3].to_vec()));
        let nova_cyclefold_data = NovaCycleFoldData::from((g16_data, kzg_data, 1));

        let decider_template = HeaderInclusion::<NovaCycleFoldDecider>::builder()
            .template(nova_cyclefold_data)
            .build();

        save_solidity("NovaDecider.sol", &decider_template.render().unwrap());
    }

    /// This function allows to define which FCircuit to use for the test, and how many prove_step
    /// rounds to perform.
    /// Actions performed by this test:
    /// - runs the NovaCycleFold folding scheme for the given FCircuit and n_steps times
    /// - generates a DeciderEth proof, and executes it through the EVM
    /// - modifies the calldata and checks that it does not pass the EVM check
    /// - modifies the z_0 and checks that it does not pass the EVM check
    #[allow(clippy::type_complexity)]
    fn nova_cyclefold_solidity_verifier_opt<FC: FCircuit<Fr, Params = ()>>(
        params: (
            ProverParams<G1, G2, KZG<'static, Bn254>, Pedersen<G2>>,
            KZGVerifierKey<Bn254>,
            ProvingKey<Bn254>,
            G16VerifierKey<Bn254>,
        ),
        z_0: Vec<Fr>,
        n_steps: usize,
    ) {
        let (fs_prover_params, kzg_vk, g16_pk, g16_vk) = params.clone();

        pub type NOVA_FCircuit<FC> =
            Nova<G1, GVar, G2, GVar2, FC, KZG<'static, Bn254>, Pedersen<G2>>;
        pub type DECIDERETH_FCircuit<FC> = DeciderEth<
            G1,
            GVar,
            G2,
            GVar2,
            FC,
            KZG<'static, Bn254>,
            Pedersen<G2>,
            Groth16<Bn254>,
            NOVA_FCircuit<FC>,
        >;
        let f_circuit = FC::new(());

        let mut nova = NOVA_FCircuit::init(&fs_prover_params, f_circuit, z_0).unwrap();
        for _ in 0..n_steps {
            nova.prove_step().unwrap();
        }

        let rng = rand::rngs::OsRng;
        let proof = DECIDERETH_FCircuit::prove(
            (g16_pk, fs_prover_params.cs_params.clone()),
            rng,
            nova.clone(),
        )
        .unwrap();

        let verified = DECIDERETH_FCircuit::<FC>::verify(
            (g16_vk.clone(), kzg_vk.clone()),
            nova.i,
            nova.z_0.clone(),
            nova.z_i.clone(),
            &nova.U_i,
            &nova.u_i,
            &proof,
        )
        .unwrap();
        assert!(verified);

        let g16_data = Groth16Data::from(g16_vk);
        let kzg_data = KzgData::from((
            kzg_vk,
            fs_prover_params.cs_params.powers_of_g[0..3].to_vec(),
        ));
        let nova_cyclefold_data = NovaCycleFoldData::from((g16_data, kzg_data, nova.z_0.len()));

        let function_selector =
            get_function_selector_for_nova_cyclefold_verifier(nova.z_0.len() * 2 + 1);

        let mut calldata: Vec<u8> = prepare_calldata(
            function_selector,
            nova.i,
            nova.z_0,
            nova.z_i,
            &nova.U_i,
            &nova.u_i,
            proof,
        )
        .unwrap();

        let decider_template = get_decider_template_for_cyclefold_decider(nova_cyclefold_data);

        let nova_cyclefold_verifier_bytecode = compile_solidity(decider_template, "NovaDecider");

        let mut evm = Evm::default();
        let verifier_address = evm.create(nova_cyclefold_verifier_bytecode);

        let (_, output) = evm.call(verifier_address, calldata.clone());
        assert_eq!(*output.last().unwrap(), 1);

        // change i to make calldata invalid
        // first 4 bytes are the function signature + 32 bytes for i --> change byte at index 35
        let prev_call_data_i = calldata[35];
        calldata[35] = 0;
        let (_, output) = evm.call(verifier_address, calldata.clone());
        assert_eq!(*output.last().unwrap(), 0);
        calldata[35] = prev_call_data_i;

        // TODO: change z_0 to make the EVM check fail
    }

    #[test]
    fn nova_cyclefold_solidity_verifier() {
        let params = init_params::<CubicFCircuit<Fr>>();
        let z_0 = vec![Fr::from(3_u32)];
        nova_cyclefold_solidity_verifier_opt::<CubicFCircuit<Fr>>(params.clone(), z_0.clone(), 2);
        nova_cyclefold_solidity_verifier_opt::<CubicFCircuit<Fr>>(params.clone(), z_0.clone(), 3);

        let params = init_params::<MultiInputsFCircuit<Fr>>();
        let z_0 = vec![
            Fr::from(1_u32),
            Fr::from(1_u32),
            Fr::from(1_u32),
            Fr::from(1_u32),
            Fr::from(1_u32),
        ];
        nova_cyclefold_solidity_verifier_opt::<MultiInputsFCircuit<Fr>>(
            params.clone(),
            z_0.clone(),
            2,
        );
        nova_cyclefold_solidity_verifier_opt::<MultiInputsFCircuit<Fr>>(
            params.clone(),
            z_0.clone(),
            3,
        );
    }

    #[allow(clippy::type_complexity)]
    fn init_test_prover_params<FC: FCircuit<Fr, Params = ()>>() -> (
        ProverParams<G1, G2, KZG<'static, Bn254>, Pedersen<G2>>,
        KZGVerifierKey<Bn254>,
    ) {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_test_config::<Fr>();
        let f_circuit = FC::new(());
        let (cs_len, cf_cs_len) =
            get_cs_params_len::<G1, GVar, G2, GVar2, FC>(&poseidon_config, f_circuit).unwrap();
        let (kzg_pk, kzg_vk): (KZGProverKey<G1>, KZGVerifierKey<Bn254>) =
            KZG::<Bn254>::setup(&mut rng, cs_len).unwrap();
        let (cf_pedersen_params, _) = Pedersen::<G2>::setup(&mut rng, cf_cs_len).unwrap();
        let fs_prover_params = ProverParams::<G1, G2, KZG<Bn254>, Pedersen<G2>> {
            poseidon_config: poseidon_config.clone(),
            cs_params: kzg_pk.clone(),
            cf_cs_params: cf_pedersen_params,
        };
        (fs_prover_params, kzg_vk)
    }

    /// Initializes Nova parameters and DeciderEth parameters. Only for test purposes.
    #[allow(clippy::type_complexity)]
    fn init_params<FC: FCircuit<Fr, Params = ()>>() -> (
        ProverParams<G1, G2, KZG<'static, Bn254>, Pedersen<G2>>,
        KZGVerifierKey<Bn254>,
        ProvingKey<Bn254>,
        G16VerifierKey<Bn254>,
    ) {
        let mut rng = rand::rngs::OsRng;
        let start = Instant::now();
        let (fs_prover_params, kzg_vk) = init_test_prover_params::<FC>();
        println!("generated Nova params: {:?}", start.elapsed());
        let f_circuit = FC::new(());

        pub type NOVA_FCircuit<FC> =
            Nova<G1, GVar, G2, GVar2, FC, KZG<'static, Bn254>, Pedersen<G2>>;
        let z_0 = vec![Fr::zero(); f_circuit.state_len()];
        let nova = NOVA_FCircuit::init(&fs_prover_params, f_circuit, z_0.clone()).unwrap();

        let decider_circuit =
            DeciderEthCircuit::<G1, GVar, G2, GVar2, KZG<Bn254>, Pedersen<G2>>::from_nova::<FC>(
                nova.clone(),
            )
            .unwrap();
        let start = Instant::now();
        let (g16_pk, g16_vk) =
            Groth16::<Bn254>::circuit_specific_setup(decider_circuit.clone(), &mut rng).unwrap();
        println!("generated G16 (Decider) params: {:?}", start.elapsed());
        (fs_prover_params, kzg_vk, g16_pk, g16_vk)
    }
}
