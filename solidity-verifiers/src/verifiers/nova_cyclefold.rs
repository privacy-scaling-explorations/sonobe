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
    nova_cyclefold_data: NovaCyclefoldData,
) -> String {
    let decider_template = HeaderInclusion::<NovaCyclefoldDecider>::builder()
        .template(nova_cyclefold_data)
        .build()
        .render()
        .unwrap();
    decider_template
}

#[derive(Template, Default)]
#[template(path = "nova_cyclefold_decider.askama.sol", ext = "sol")]
pub(crate) struct NovaCyclefoldDecider {
    groth16_verifier: Groth16Verifier,
    kzg10_verifier: KZG10Verifier,
    z_len: usize,
    public_inputs_len: usize,
}

impl From<NovaCyclefoldData> for NovaCyclefoldDecider {
    fn from(value: NovaCyclefoldData) -> Self {
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
pub struct NovaCyclefoldData {
    g16_data: Groth16Data,
    kzg_data: KzgData,
    z_len: usize,
}

impl ProtocolData for NovaCyclefoldData {
    const PROTOCOL_NAME: &'static str = "NovaCyclefold";

    fn render_as_template(self, pragma: Option<String>) -> Vec<u8> {
        HeaderInclusion::<NovaCyclefoldDecider>::builder()
            .pragma_version(pragma.unwrap_or(PRAGMA_GROTH16_VERIFIER.to_string()))
            .template(self)
            .build()
            .render()
            .unwrap()
            .into_bytes()
    }
}

impl From<(Groth16Data, KzgData, usize)> for NovaCyclefoldData {
    fn from(value: (Groth16Data, KzgData, usize)) -> Self {
        Self {
            g16_data: value.0,
            kzg_data: value.1,
            z_len: value.2,
        }
    }
}

impl NovaCyclefoldData {
    pub fn new(
        vkey_g16: VerifyingKey<Bn254>,
        vkey_kzg: VerifierKey<Bn254>,
        crs_points: Vec<G1Affine>,
        z_len: usize,
    ) -> Self {
        Self {
            g16_data: Groth16Data::from(vkey_g16),
            // TODO: Remove option from crs points
            kzg_data: KzgData::from((vkey_kzg, Some(crs_points))),
            z_len,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        evm::{compile_solidity, save_solidity, Evm},
        utils::{get_function_selector_for_nova_cyclefold_verifier, HeaderInclusion},
        verifiers::nova_cyclefold::get_decider_template_for_cyclefold_decider,
        Groth16Data, KzgData, NovaCyclefoldData, ProtocolData,
    };
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
    use askama::Template;
    use rand::rngs::OsRng;
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

    use super::NovaCyclefoldDecider;
    use crate::verifiers::tests::{setup, DEFAULT_SETUP_LEN};

    pub type NOVACubicFCircuit =
        Nova<G1, GVar, G2, GVar2, CubicFCircuit<Fr>, KZG<'static, Bn254>, Pedersen<G2>>;
    pub type DECIDEREthCubicFCircuit = DeciderEth<
        G1,
        GVar,
        G2,
        GVar2,
        CubicFCircuit<Fr>,
        KZG<'static, Bn254>,
        Pedersen<G2>,
        Groth16<Bn254>,
        NOVACubicFCircuit,
    >;

    pub type NOVAMultiInputsFCircuit =
        Nova<G1, GVar, G2, GVar2, MultiInputsFCircuit<Fr>, KZG<'static, Bn254>, Pedersen<G2>>;
    pub type DECIDEREthMultiInputsFCircuit = DeciderEth<
        G1,
        GVar,
        G2,
        GVar2,
        MultiInputsFCircuit<Fr>,
        KZG<'static, Bn254>,
        Pedersen<G2>,
        Groth16<Bn254>,
        NOVAMultiInputsFCircuit,
    >;

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
        let kzg_data = KzgData::from((kzg_vk, Some(kzg_pk.powers_of_g[0..3].to_vec())));

        let mut bytes = vec![];
        let nova_cyclefold_data = NovaCyclefoldData::from((g16_data, kzg_data, 1));

        nova_cyclefold_data
            .serialize_protocol_data(&mut bytes)
            .unwrap();
        let obtained_nova_cyclefold_data =
            NovaCyclefoldData::deserialize_protocol_data(bytes.as_slice()).unwrap();

        assert_eq!(nova_cyclefold_data, obtained_nova_cyclefold_data)
    }

    #[test]
    fn nova_cyclefold_decider_template_renders() {
        let (kzg_pk, kzg_vk, _, g16_vk, _) = setup(DEFAULT_SETUP_LEN);
        let g16_data = Groth16Data::from(g16_vk);
        let kzg_data = KzgData::from((kzg_vk, Some(kzg_pk.powers_of_g[0..3].to_vec())));
        let nova_cyclefold_data = NovaCyclefoldData::from((g16_data, kzg_data, 1));

        let decider_template = HeaderInclusion::<NovaCyclefoldDecider>::builder()
            .template(nova_cyclefold_data)
            .build();

        save_solidity("NovaDecider.sol", &decider_template.render().unwrap());
    }

    #[test]
    fn nova_cyclefold_verifier_accepts_and_rejects_proofs_for_cubic_fcircuit_and_2_steps_folding() {
        let mut rng = rand::rngs::OsRng;
        let z_0 = vec![Fr::from(3_u32)];
        let (prover_params, kzg_vk) = init_test_prover_params::<CubicFCircuit<Fr>>();
        let f_circuit = CubicFCircuit::<Fr>::new(());

        let mut nova = NOVACubicFCircuit::init(&prover_params, f_circuit, z_0.clone()).unwrap();
        nova.prove_step().unwrap();
        nova.prove_step().unwrap();

        let decider_circuit =
            DeciderEthCircuit::<G1, GVar, G2, GVar2, KZG<Bn254>, Pedersen<G2>>::from_nova::<
                CubicFCircuit<Fr>,
            >(nova.clone())
            .unwrap();
        let (g16_pk, g16_vk) =
            init_test_groth16_setup_for_decider_eth_circuit(decider_circuit.clone(), &mut rng);
        let proof = DECIDEREthCubicFCircuit::prove(
            (
                prover_params.poseidon_config.clone(),
                g16_pk,
                prover_params.cs_params.clone(),
            ),
            rng,
            nova.clone(),
        )
        .unwrap();

        let verified = DECIDEREthCubicFCircuit::verify(
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
            Some(prover_params.cs_params.powers_of_g[0..3].to_vec()),
        ));
        let nova_cyclefold_data = NovaCyclefoldData::from((g16_data, kzg_data, nova.z_0.len()));

        let function_selector =
            get_function_selector_for_nova_cyclefold_verifier(nova.z_0.len() * 2 + 1);

        let calldata: Vec<u8> = prepare_calldata(
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
    }

    #[test]
    fn nova_cyclefold_verifier_accepts_and_rejects_proofs_for_cubic_fcircuit() {
        let mut rng = rand::rngs::OsRng;
        let z_0 = vec![Fr::from(3_u32)];
        let (prover_params, kzg_vk) = init_test_prover_params::<CubicFCircuit<Fr>>();
        let f_circuit = CubicFCircuit::<Fr>::new(());

        let mut nova = NOVACubicFCircuit::init(&prover_params, f_circuit, z_0.clone()).unwrap();
        nova.prove_step().unwrap();
        nova.prove_step().unwrap();
        nova.prove_step().unwrap();

        let decider_circuit =
            DeciderEthCircuit::<G1, GVar, G2, GVar2, KZG<Bn254>, Pedersen<G2>>::from_nova::<
                CubicFCircuit<Fr>,
            >(nova.clone())
            .unwrap();
        let (g16_pk, g16_vk) =
            init_test_groth16_setup_for_decider_eth_circuit(decider_circuit.clone(), &mut rng);
        let proof = DECIDEREthCubicFCircuit::prove(
            (
                prover_params.poseidon_config.clone(),
                g16_pk,
                prover_params.cs_params.clone(),
            ),
            rng,
            nova.clone(),
        )
        .unwrap();

        let verified = DECIDEREthCubicFCircuit::verify(
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
            Some(prover_params.cs_params.powers_of_g[0..3].to_vec()),
        ));
        let nova_cyclefold_data = NovaCyclefoldData::from((g16_data, kzg_data, nova.z_0.len()));

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

        save_solidity("NovaDeciderCubicCircuit.sol", &decider_template);

        let nova_cyclefold_verifier_bytecode = compile_solidity(decider_template, "NovaDecider");

        let mut evm = Evm::default();
        let verifier_address = evm.create(nova_cyclefold_verifier_bytecode);

        let (_, output) = evm.call(verifier_address, calldata.clone());
        assert_eq!(*output.last().unwrap(), 1);

        // change i to make calldata invalid
        // first 4 bytes are the function signature + 32 bytes for i --> change byte at index 35
        let prev_call_data_i = calldata[35].clone();
        calldata[35] = 0;
        let (_, output) = evm.call(verifier_address, calldata.clone());
        assert_eq!(*output.last().unwrap(), 0);
        calldata[35] = prev_call_data_i;

        // change z_0 to make calldata invalid
    }

    #[test]
    fn nova_cyclefold_verifier_accepts_and_rejects_proofs_for_multi_inputs_fcircuit_and_2_steps_folding(
    ) {
        let mut rng = rand::rngs::OsRng;
        let z_0 = vec![
            Fr::from(1_u32),
            Fr::from(1_u32),
            Fr::from(1_u32),
            Fr::from(1_u32),
            Fr::from(1_u32),
        ];

        let (prover_params, kzg_vk) = init_test_prover_params::<MultiInputsFCircuit<Fr>>();
        let f_circuit = MultiInputsFCircuit::<Fr>::new(());

        let mut nova =
            NOVAMultiInputsFCircuit::init(&prover_params, f_circuit, z_0.clone()).unwrap();
        nova.prove_step().unwrap();
        nova.prove_step().unwrap();

        let decider_circuit =
            DeciderEthCircuit::<G1, GVar, G2, GVar2, KZG<Bn254>, Pedersen<G2>>::from_nova::<
                MultiInputsFCircuit<Fr>,
            >(nova.clone())
            .unwrap();
        let (g16_pk, g16_vk) =
            init_test_groth16_setup_for_decider_eth_circuit(decider_circuit.clone(), &mut rng);
        let proof = DECIDEREthMultiInputsFCircuit::prove(
            (
                prover_params.poseidon_config.clone(),
                g16_pk,
                prover_params.cs_params.clone(),
            ),
            rng,
            nova.clone(),
        )
        .unwrap();

        let verified = DECIDEREthMultiInputsFCircuit::verify(
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
            Some(prover_params.cs_params.powers_of_g[0..3].to_vec()),
        ));
        let nova_cyclefold_data = NovaCyclefoldData::from((g16_data, kzg_data, nova.z_0.len()));

        let function_selector =
            get_function_selector_for_nova_cyclefold_verifier(nova.z_0.len() * 2 + 1);

        let calldata: Vec<u8> = prepare_calldata(
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
    }

    #[test]
    fn nova_cyclefold_verifier_accepts_and_rejects_proofs_for_multi_inputs_fcircuit() {
        let mut rng = rand::rngs::OsRng;
        let z_0 = vec![
            Fr::from(1_u32),
            Fr::from(1_u32),
            Fr::from(1_u32),
            Fr::from(1_u32),
            Fr::from(1_u32),
        ];

        let (prover_params, kzg_vk) = init_test_prover_params::<MultiInputsFCircuit<Fr>>();
        let f_circuit = MultiInputsFCircuit::<Fr>::new(());

        let mut nova =
            NOVAMultiInputsFCircuit::init(&prover_params, f_circuit, z_0.clone()).unwrap();
        nova.prove_step().unwrap();
        nova.prove_step().unwrap();
        nova.prove_step().unwrap();

        let decider_circuit =
            DeciderEthCircuit::<G1, GVar, G2, GVar2, KZG<Bn254>, Pedersen<G2>>::from_nova::<
                MultiInputsFCircuit<Fr>,
            >(nova.clone())
            .unwrap();
        let (g16_pk, g16_vk) =
            init_test_groth16_setup_for_decider_eth_circuit(decider_circuit.clone(), &mut rng);
        let proof = DECIDEREthMultiInputsFCircuit::prove(
            (
                prover_params.poseidon_config.clone(),
                g16_pk,
                prover_params.cs_params.clone(),
            ),
            rng,
            nova.clone(),
        )
        .unwrap();

        let verified = DECIDEREthMultiInputsFCircuit::verify(
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
            Some(prover_params.cs_params.powers_of_g[0..3].to_vec()),
        ));
        let nova_cyclefold_data = NovaCyclefoldData::from((g16_data, kzg_data, nova.z_0.len()));

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

        save_solidity("NovaDeciderMultiInputs.sol", &decider_template);

        let nova_cyclefold_verifier_bytecode = compile_solidity(decider_template, "NovaDecider");

        let mut evm = Evm::default();
        let verifier_address = evm.create(nova_cyclefold_verifier_bytecode);

        let (_, output) = evm.call(verifier_address, calldata.clone());
        assert_eq!(*output.last().unwrap(), 1);

        // change i to make calldata invalid
        // first 4 bytes are the function signature + 32 bytes for i --> change byte at index 35
        let prev_call_data_i = calldata[35].clone();
        calldata[35] = 0;
        let (_, output) = evm.call(verifier_address, calldata.clone());
        assert_eq!(*output.last().unwrap(), 0);
        calldata[35] = prev_call_data_i;

        // change z_0 to make calldata invalid
    }

    /// Initializes prover parameters. For testing purposes only!
    fn init_test_prover_params<FC: FCircuit<Fr, Params = ()>>() -> (
        ProverParams<G1, G2, KZG<'static, Bn254>, Pedersen<G2>>,
        KZGVerifierKey<Bn254>,
    ) {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_test_config::<Fr>();
        let f_circuit = FC::new(());
        let (cs_len, cf_cs_len) =
            get_cs_params_len::<G1, GVar, G2, GVar2, FC>(&poseidon_config, f_circuit).unwrap();
        let start = Instant::now();
        let (kzg_pk, kzg_vk): (KZGProverKey<G1>, KZGVerifierKey<Bn254>) =
            KZG::<Bn254>::setup(&mut rng, cs_len).unwrap();
        let (cf_pedersen_params, _) = Pedersen::<G2>::setup(&mut rng, cf_cs_len).unwrap();
        println!("generated KZG params, {:?}", start.elapsed());
        let prover_params = ProverParams::<G1, G2, KZG<Bn254>, Pedersen<G2>> {
            poseidon_config: poseidon_config.clone(),
            cs_params: kzg_pk.clone(),
            cf_cs_params: cf_pedersen_params,
        };
        (prover_params, kzg_vk)
    }

    /// Initializes Groth16 setup for the DeciderEthCircuit. For testing purposes only!
    fn init_test_groth16_setup_for_decider_eth_circuit(
        circuit: DeciderEthCircuit<G1, GVar, G2, GVar2, KZG<Bn254>, Pedersen<G2>>,
        rng: &mut OsRng,
    ) -> (ProvingKey<Bn254>, G16VerifierKey<Bn254>) {
        Groth16::<Bn254>::circuit_specific_setup(circuit.clone(), rng).unwrap()
    }
}
