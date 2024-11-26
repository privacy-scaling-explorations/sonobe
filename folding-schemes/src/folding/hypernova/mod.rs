/// Implements the scheme described in [HyperNova](https://eprint.iacr.org/2023/573.pdf)
use ark_crypto_primitives::sponge::{
    poseidon::{PoseidonConfig, PoseidonSponge},
    Absorb, CryptographicSponge,
};
use ark_ec::{CurveGroup, Group};
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{prelude::CurveVar, ToConstraintFieldGadget};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError};
use ark_std::{fmt::Debug, marker::PhantomData, rand::RngCore, One, Zero};

pub mod cccs;
pub mod circuits;
pub mod decider_eth;
pub mod decider_eth_circuit;
pub mod lcccs;
pub mod nimfs;
pub mod utils;

use cccs::CCCS;
use circuits::AugmentedFCircuit;
use decider_eth_circuit::WitnessVar;
use lcccs::LCCCS;
use nimfs::NIMFS;

use crate::commitment::CommitmentScheme;
use crate::constants::NOVA_N_BITS_RO;
use crate::folding::{
    circuits::{
        cyclefold::{
            fold_cyclefold_circuit, CycleFoldCircuit, CycleFoldCommittedInstance, CycleFoldConfig,
            CycleFoldWitness,
        },
        CF2,
    },
    nova::{get_r1cs_from_cs, PreprocessorParam},
    traits::{CommittedInstanceOps, Dummy, WitnessOps},
};
use crate::frontend::FCircuit;
use crate::transcript::poseidon::poseidon_canonical_config;
use crate::utils::{get_cm_coordinates, pp_hash};
use crate::Error;
use crate::{
    arith::{
        ccs::CCS,
        r1cs::{extract_w_x, R1CS},
        Arith,
    },
    FoldingScheme, MultiFolding,
};

/// Configuration for HyperNova's CycleFold circuit
pub struct HyperNovaCycleFoldConfig<C: CurveGroup, const MU: usize, const NU: usize> {
    _c: PhantomData<C>,
}

impl<C: CurveGroup, const MU: usize, const NU: usize> CycleFoldConfig
    for HyperNovaCycleFoldConfig<C, MU, NU>
{
    const RANDOMNESS_BIT_LENGTH: usize = NOVA_N_BITS_RO;
    const N_INPUT_POINTS: usize = MU + NU;
    type C = C;
    type F = C::BaseField;
}

/// CycleFold circuit for computing random linear combinations of group elements
/// in HyperNova instances.
pub type HyperNovaCycleFoldCircuit<C, GC, const MU: usize, const NU: usize> =
    CycleFoldCircuit<HyperNovaCycleFoldConfig<C, MU, NU>, GC>;

/// Witness for the LCCCS & CCCS, containing the w vector, and the r_w used as randomness in the Pedersen commitment.
#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Witness<F: PrimeField> {
    pub w: Vec<F>,
    pub r_w: F,
}

impl<F: PrimeField> Witness<F> {
    pub fn new(w: Vec<F>) -> Self {
        // note: at the current version, we don't use the blinding factors and we set them to 0
        // always.
        Self { w, r_w: F::zero() }
    }
}

impl<F: PrimeField> Dummy<&CCS<F>> for Witness<F> {
    fn dummy(ccs: &CCS<F>) -> Self {
        Self::new(vec![F::zero(); ccs.n - ccs.l - 1])
    }
}

impl<F: PrimeField> WitnessOps<F> for Witness<F> {
    type Var = WitnessVar<F>;

    fn get_openings(&self) -> Vec<(&[F], F)> {
        vec![(&self.w, self.r_w)]
    }
}

/// Proving parameters for HyperNova-based IVC
#[derive(Debug, Clone)]
pub struct ProverParams<C1, C2, CS1, CS2, const H: bool>
where
    C1: CurveGroup,
    C2: CurveGroup,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
{
    /// Poseidon sponge configuration
    pub poseidon_config: PoseidonConfig<C1::ScalarField>,
    /// Proving parameters of the underlying commitment scheme over C1
    pub cs_pp: CS1::ProverParams,
    /// Proving parameters of the underlying commitment scheme over C2
    pub cf_cs_pp: CS2::ProverParams,
    /// CCS of the Augmented Function circuit
    /// If ccs is set, it will be used, if not, it will be computed at runtime
    pub ccs: Option<CCS<C1::ScalarField>>,
}

impl<
        C1: CurveGroup,
        C2: CurveGroup,
        CS1: CommitmentScheme<C1, H>,
        CS2: CommitmentScheme<C2, H>,
        const H: bool,
    > CanonicalSerialize for ProverParams<C1, C2, CS1, CS2, H>
{
    fn serialize_with_mode<W: std::io::prelude::Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        self.cs_pp.serialize_with_mode(&mut writer, compress)?;
        self.cf_cs_pp.serialize_with_mode(&mut writer, compress)
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        self.cs_pp.serialized_size(compress) + self.cf_cs_pp.serialized_size(compress)
    }
}

/// Verification parameters for HyperNova-based IVC
#[derive(Debug, Clone)]
pub struct VerifierParams<
    C1: CurveGroup,
    C2: CurveGroup,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
    const H: bool,
> {
    /// Poseidon sponge configuration
    pub poseidon_config: PoseidonConfig<C1::ScalarField>,
    /// CCS of the Augmented step circuit
    pub ccs: CCS<C1::ScalarField>,
    /// R1CS of the CycleFold circuit
    pub cf_r1cs: R1CS<C2::ScalarField>,
    /// Verification parameters of the underlying commitment scheme over C1
    pub cs_vp: CS1::VerifierParams,
    /// Verification parameters of the underlying commitment scheme over C2
    pub cf_cs_vp: CS2::VerifierParams,
}

impl<C1, C2, CS1, CS2, const H: bool> CanonicalSerialize for VerifierParams<C1, C2, CS1, CS2, H>
where
    C1: CurveGroup,
    C2: CurveGroup,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
{
    fn serialize_with_mode<W: std::io::prelude::Write>(
        &self,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        self.cs_vp.serialize_with_mode(&mut writer, compress)?;
        self.cf_cs_vp.serialize_with_mode(&mut writer, compress)
    }

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        self.cs_vp.serialized_size(compress) + self.cf_cs_vp.serialized_size(compress)
    }
}

impl<C1, C2, CS1, CS2, const H: bool> VerifierParams<C1, C2, CS1, CS2, H>
where
    C1: CurveGroup,
    C2: CurveGroup,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
{
    /// returns the hash of the public parameters of HyperNova
    pub fn pp_hash(&self) -> Result<C1::ScalarField, Error> {
        pp_hash::<C1, C2, CS1, CS2, H>(
            &self.ccs,
            &self.cf_r1cs,
            &self.cs_vp,
            &self.cf_cs_vp,
            &self.poseidon_config,
        )
    }
}

#[derive(PartialEq, Eq, Debug, Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct IVCProof<C1, C2>
where
    C1: CurveGroup,
    C2: CurveGroup,
{
    pub i: C1::ScalarField,
    pub z_0: Vec<C1::ScalarField>,
    pub z_i: Vec<C1::ScalarField>,
    pub W_i: Witness<C1::ScalarField>,
    pub U_i: LCCCS<C1>,
    pub w_i: Witness<C1::ScalarField>,
    pub u_i: CCCS<C1>,
    pub cf_W_i: CycleFoldWitness<C2>,
    pub cf_U_i: CycleFoldCommittedInstance<C2>,
}

/// Implements HyperNova+CycleFold's IVC, described in
/// [HyperNova](https://eprint.iacr.org/2023/573.pdf) and
/// [CycleFold](https://eprint.iacr.org/2023/1192.pdf), following the FoldingScheme trait
///
/// For multi-instance folding, one needs to specify the const generics below:
/// * `MU` - the number of LCCCS instances to be folded
/// * `NU` - the number of CCCS instances to be folded
#[derive(Clone, Debug)]
pub struct HyperNova<
    C1,
    GC1,
    C2,
    GC2,
    FC,
    CS1,
    CS2,
    const MU: usize,
    const NU: usize,
    const H: bool,
> where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>>,
    FC: FCircuit<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
{
    _gc1: PhantomData<GC1>,
    _c2: PhantomData<C2>,
    _gc2: PhantomData<GC2>,

    /// CCS of the Augmented Function circuit
    pub ccs: CCS<C1::ScalarField>,
    /// R1CS of the CycleFold circuit
    pub cf_r1cs: R1CS<C2::ScalarField>,
    pub poseidon_config: PoseidonConfig<C1::ScalarField>,
    /// CommitmentScheme::ProverParams over C1
    pub cs_pp: CS1::ProverParams,
    /// CycleFold CommitmentScheme::ProverParams, over C2
    pub cf_cs_pp: CS2::ProverParams,
    /// F circuit, the circuit that is being folded
    pub F: FC,
    /// public params hash
    pub pp_hash: C1::ScalarField,
    pub i: C1::ScalarField,
    /// initial state
    pub z_0: Vec<C1::ScalarField>,
    /// current i-th state
    pub z_i: Vec<C1::ScalarField>,
    /// HyperNova instances
    pub W_i: Witness<C1::ScalarField>,
    pub U_i: LCCCS<C1>,
    pub w_i: Witness<C1::ScalarField>,
    pub u_i: CCCS<C1>,

    /// CycleFold running instance
    pub cf_W_i: CycleFoldWitness<C2>,
    pub cf_U_i: CycleFoldCommittedInstance<C2>,
}

impl<C1, GC1, C2, GC2, FC, CS1, CS2, const MU: usize, const NU: usize, const H: bool>
    MultiFolding<C1, C2, FC> for HyperNova<C1, GC1, C2, GC2, FC, CS1, CS2, MU, NU, H>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
{
    type RunningInstance = (LCCCS<C1>, Witness<C1::ScalarField>);
    type IncomingInstance = (CCCS<C1>, Witness<C1::ScalarField>);
    type MultiInstance = (Vec<Self::RunningInstance>, Vec<Self::IncomingInstance>);

    /// Creates a new LCCS instance for the given state, which satisfies the HyperNova.CCS. This
    /// method can be used to generate the 'other' LCCS instances to be folded in the multi-folding
    /// step.
    fn new_running_instance(
        &self,
        mut rng: impl RngCore,
        state: Vec<C1::ScalarField>,
        external_inputs: Vec<C1::ScalarField>,
    ) -> Result<Self::RunningInstance, Error> {
        let r1cs_z = self.new_instance_generic(state, external_inputs)?;
        // compute committed instances, w_{i+1}, u_{i+1}, which will be used as w_i, u_i, so we
        // assign them directly to w_i, u_i.
        let (U_i, W_i) = self
            .ccs
            .to_lcccs::<_, _, CS1, H>(&mut rng, &self.cs_pp, &r1cs_z)?;

        #[cfg(test)]
        self.ccs.check_relation(&W_i, &U_i)?;

        Ok((U_i, W_i))
    }

    /// Creates a new CCCS instance for the given state, which satisfies the HyperNova.CCS. This
    /// method can be used to generate the 'other' CCCS instances to be folded in the multi-folding
    /// step.
    fn new_incoming_instance(
        &self,
        mut rng: impl RngCore,
        state: Vec<C1::ScalarField>,
        external_inputs: Vec<C1::ScalarField>,
    ) -> Result<Self::IncomingInstance, Error> {
        let r1cs_z = self.new_instance_generic(state, external_inputs)?;
        // compute committed instances, w_{i+1}, u_{i+1}, which will be used as w_i, u_i, so we
        // assign them directly to w_i, u_i.
        let (u_i, w_i) = self
            .ccs
            .to_cccs::<_, _, CS1, H>(&mut rng, &self.cs_pp, &r1cs_z)?;

        #[cfg(test)]
        self.ccs.check_relation(&w_i, &u_i)?;

        Ok((u_i, w_i))
    }
}

impl<C1, GC1, C2, GC2, FC, CS1, CS2, const MU: usize, const NU: usize, const H: bool>
    HyperNova<C1, GC1, C2, GC2, FC, CS1, CS2, MU, NU, H>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
{
    /// internal helper for new_running_instance & new_incoming_instance methods, returns the R1CS
    /// z=[u,x,w] vector to be used to create the LCCCS & CCCS fresh instances.
    fn new_instance_generic(
        &self,
        state: Vec<C1::ScalarField>,
        external_inputs: Vec<C1::ScalarField>,
    ) -> Result<Vec<C1::ScalarField>, Error> {
        // prepare the initial dummy instances
        let U_i = LCCCS::<C1>::dummy(&self.ccs);
        let mut u_i = CCCS::<C1>::dummy(&self.ccs);
        let (_, cf_U_i): (CycleFoldWitness<C2>, CycleFoldCommittedInstance<C2>) =
            self.cf_r1cs.dummy_witness_instance();

        let sponge = PoseidonSponge::<C1::ScalarField>::new(&self.poseidon_config);

        u_i.x = vec![
            U_i.hash(
                &sponge,
                self.pp_hash,
                C1::ScalarField::zero(), // i
                &self.z_0,
                &state,
            ),
            cf_U_i.hash_cyclefold(&sponge, &self.pp_hash),
        ];
        let us = vec![u_i.clone(); NU - 1];

        let z_i1 = self.F.step_native(0, &state, &external_inputs)?;

        // compute u_{i+1}.x
        let U_i1 = LCCCS::dummy(&self.ccs);
        let u_i1_x = U_i1.hash(
            &sponge,
            self.pp_hash,
            C1::ScalarField::one(), // i+1, where i=0
            &self.z_0,
            &z_i1,
        );

        let cf_u_i1_x = cf_U_i.hash_cyclefold(&sponge, &self.pp_hash);
        let augmented_f_circuit = AugmentedFCircuit::<C1, C2, GC2, FC, MU, NU> {
            _c2: PhantomData,
            _gc2: PhantomData,
            poseidon_config: self.poseidon_config.clone(),
            ccs: self.ccs.clone(),
            pp_hash: Some(self.pp_hash),
            i: Some(C1::ScalarField::zero()),
            i_usize: Some(0),
            z_0: Some(self.z_0.clone()),
            z_i: Some(state.clone()),
            external_inputs: Some(external_inputs),
            U_i: Some(U_i.clone()),
            Us: None,
            u_i_C: Some(u_i.C),
            us: Some(us),
            U_i1_C: Some(U_i1.C),
            F: self.F.clone(),
            x: Some(u_i1_x),
            nimfs_proof: None,

            // cyclefold values
            cf_u_i_cmW: None,
            cf_U_i: None,
            cf_x: Some(cf_u_i1_x),
            cf_cmT: None,
        };

        let (cs, _) = augmented_f_circuit.compute_cs_ccs()?;

        #[cfg(test)]
        assert!(cs.is_satisfied()?);

        let (r1cs_w_i1, r1cs_x_i1) = extract_w_x::<C1::ScalarField>(&cs); // includes 1 and public inputs

        #[cfg(test)]
        assert_eq!(r1cs_x_i1[0], augmented_f_circuit.x.unwrap());

        let r1cs_z = [
            vec![C1::ScalarField::one()],
            r1cs_x_i1.clone(),
            r1cs_w_i1.clone(),
        ]
        .concat();
        Ok(r1cs_z)
    }
}

impl<C1, GC1, C2, GC2, FC, CS1, CS2, const MU: usize, const NU: usize, const H: bool>
    FoldingScheme<C1, C2, FC> for HyperNova<C1, GC1, C2, GC2, FC, CS1, CS2, MU, NU, H>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
{
    /// Reuse Nova's PreprocessorParam.
    type PreprocessorParam = PreprocessorParam<C1, C2, FC, CS1, CS2, H>;
    type ProverParam = ProverParams<C1, C2, CS1, CS2, H>;
    type VerifierParam = VerifierParams<C1, C2, CS1, CS2, H>;
    type RunningInstance = (LCCCS<C1>, Witness<C1::ScalarField>);
    type IncomingInstance = (CCCS<C1>, Witness<C1::ScalarField>);
    type MultiCommittedInstanceWithWitness =
        (Vec<Self::RunningInstance>, Vec<Self::IncomingInstance>);
    type CFInstance = (CycleFoldCommittedInstance<C2>, CycleFoldWitness<C2>);
    type IVCProof = IVCProof<C1, C2>;

    fn pp_deserialize_with_mode<R: std::io::prelude::Read>(
        mut reader: R,
        compress: ark_serialize::Compress,
        validate: ark_serialize::Validate,
        fc_params: FC::Params,
    ) -> Result<Self::ProverParam, Error> {
        let poseidon_config = poseidon_canonical_config::<C1::ScalarField>();

        // generate the r1cs & cf_r1cs needed for the VerifierParams. In this way we avoid needing
        // to serialize them, saving significant space in the VerifierParams serialized size.

        // main circuit R1CS:
        let f_circuit = FC::new(fc_params)?;
        let augmented_F_circuit = AugmentedFCircuit::<C1, C2, GC2, FC, MU, NU>::empty(
            &poseidon_config,
            f_circuit.clone(),
            None,
        )?;
        let ccs = augmented_F_circuit.ccs;

        let cs_pp = CS1::ProverParams::deserialize_with_mode(&mut reader, compress, validate)?;
        let cf_cs_pp = CS2::ProverParams::deserialize_with_mode(&mut reader, compress, validate)?;

        Ok(ProverParams {
            poseidon_config,
            cs_pp,
            cf_cs_pp,
            ccs: Some(ccs),
        })
    }

    fn vp_deserialize_with_mode<R: std::io::prelude::Read>(
        mut reader: R,
        compress: ark_serialize::Compress,
        validate: ark_serialize::Validate,
        fc_params: FC::Params,
    ) -> Result<Self::VerifierParam, Error> {
        let poseidon_config = poseidon_canonical_config::<C1::ScalarField>();

        // generate the r1cs & cf_r1cs needed for the VerifierParams. In this way we avoid needing
        // to serialize them, saving significant space in the VerifierParams serialized size.

        // main circuit R1CS:
        let f_circuit = FC::new(fc_params)?;
        let augmented_F_circuit = AugmentedFCircuit::<C1, C2, GC2, FC, MU, NU>::empty(
            &poseidon_config,
            f_circuit.clone(),
            None,
        )?;
        let ccs = augmented_F_circuit.ccs;

        // CycleFold circuit R1CS
        let cf_circuit = HyperNovaCycleFoldCircuit::<C1, GC1, MU, NU>::empty();
        let cf_r1cs = get_r1cs_from_cs::<C2::ScalarField>(cf_circuit)?;

        let cs_vp = CS1::VerifierParams::deserialize_with_mode(&mut reader, compress, validate)?;
        let cf_cs_vp = CS2::VerifierParams::deserialize_with_mode(&mut reader, compress, validate)?;

        Ok(VerifierParams {
            poseidon_config,
            ccs,
            cf_r1cs,
            cs_vp,
            cf_cs_vp,
        })
    }

    fn preprocess(
        mut rng: impl RngCore,
        prep_param: &Self::PreprocessorParam,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), Error> {
        if MU < 1 || NU < 1 {
            return Err(Error::CantBeZero("mu,nu".to_string()));
        }

        let augmented_f_circuit = AugmentedFCircuit::<C1, C2, GC2, FC, MU, NU>::empty(
            &prep_param.poseidon_config,
            prep_param.F.clone(),
            None,
        )?;
        let ccs = augmented_f_circuit.ccs.clone();

        let cf_circuit = HyperNovaCycleFoldCircuit::<C1, GC1, MU, NU>::empty();
        let cf_r1cs = get_r1cs_from_cs::<C2::ScalarField>(cf_circuit)?;

        // if cs params exist, use them, if not, generate new ones
        let (cs_pp, cs_vp) = match (&prep_param.cs_pp, &prep_param.cs_vp) {
            (Some(cs_pp), Some(cs_vp)) => (cs_pp.clone(), cs_vp.clone()),
            _ => CS1::setup(&mut rng, ccs.n - ccs.l - 1)?,
        };
        let (cf_cs_pp, cf_cs_vp) = match (&prep_param.cf_cs_pp, &prep_param.cf_cs_vp) {
            (Some(cf_cs_pp), Some(cf_cs_vp)) => (cf_cs_pp.clone(), cf_cs_vp.clone()),
            _ => CS2::setup(&mut rng, cf_r1cs.A.n_cols - cf_r1cs.l - 1)?,
        };

        let pp = ProverParams::<C1, C2, CS1, CS2, H> {
            poseidon_config: prep_param.poseidon_config.clone(),
            cs_pp,
            cf_cs_pp,
            ccs: Some(ccs.clone()),
        };
        let vp = VerifierParams::<C1, C2, CS1, CS2, H> {
            poseidon_config: prep_param.poseidon_config.clone(),
            ccs,
            cf_r1cs,
            cs_vp: cs_vp.clone(),
            cf_cs_vp: cf_cs_vp.clone(),
        };
        Ok((pp, vp))
    }

    /// Initializes the HyperNova+CycleFold's IVC for the given parameters and initial state `z_0`.
    fn init(
        params: &(Self::ProverParam, Self::VerifierParam),
        F: FC,
        z_0: Vec<C1::ScalarField>,
    ) -> Result<Self, Error> {
        let (pp, vp) = params;
        if MU < 1 || NU < 1 {
            return Err(Error::CantBeZero("mu,nu".to_string()));
        }

        // `sponge` is for digest computation.
        let sponge = PoseidonSponge::<C1::ScalarField>::new(&pp.poseidon_config);

        // prepare the HyperNova's AugmentedFCircuit and CycleFold's circuits and obtain its CCS
        // and R1CS respectively
        let augmented_f_circuit = AugmentedFCircuit::<C1, C2, GC2, FC, MU, NU>::empty(
            &pp.poseidon_config,
            F.clone(),
            pp.ccs.clone(),
        )?;
        let ccs = augmented_f_circuit.ccs.clone();

        let cf_circuit = HyperNovaCycleFoldCircuit::<C1, GC1, MU, NU>::empty();
        let cf_r1cs = get_r1cs_from_cs::<C2::ScalarField>(cf_circuit)?;

        // compute the public params hash
        let pp_hash = vp.pp_hash()?;

        // setup the dummy instances
        let W_dummy = Witness::<C1::ScalarField>::dummy(&ccs);
        let U_dummy = LCCCS::<C1>::dummy(&ccs);
        let w_dummy = W_dummy.clone();
        let mut u_dummy = CCCS::<C1>::dummy(&ccs);
        let (cf_W_dummy, cf_U_dummy): (CycleFoldWitness<C2>, CycleFoldCommittedInstance<C2>) =
            cf_r1cs.dummy_witness_instance();
        u_dummy.x = vec![
            U_dummy.hash(&sponge, pp_hash, C1::ScalarField::zero(), &z_0, &z_0),
            cf_U_dummy.hash_cyclefold(&sponge, &pp_hash),
        ];

        // W_dummy=W_0 is a 'dummy witness', all zeroes, but with the size corresponding to the
        // R1CS that we're working with.
        Ok(Self {
            _gc1: PhantomData,
            _c2: PhantomData,
            _gc2: PhantomData,
            ccs,
            cf_r1cs,
            poseidon_config: pp.poseidon_config.clone(),
            cs_pp: pp.cs_pp.clone(),
            cf_cs_pp: pp.cf_cs_pp.clone(),
            F,
            pp_hash,
            i: C1::ScalarField::zero(),
            z_0: z_0.clone(),
            z_i: z_0,
            W_i: W_dummy,
            U_i: U_dummy,
            w_i: w_dummy,
            u_i: u_dummy,
            // cyclefold running instance
            cf_W_i: cf_W_dummy,
            cf_U_i: cf_U_dummy,
        })
    }

    /// Implements IVC.P of HyperNova+CycleFold
    fn prove_step(
        &mut self,
        mut rng: impl RngCore,
        external_inputs: Vec<C1::ScalarField>,
        other_instances: Option<Self::MultiCommittedInstanceWithWitness>,
    ) -> Result<(), Error> {
        // ensure that commitments are blinding if user has specified so.

        if H {
            let blinding_commitments = if self.i == C1::ScalarField::zero() {
                vec![self.w_i.r_w]
            } else {
                vec![self.w_i.r_w, self.W_i.r_w]
            };
            if blinding_commitments.contains(&C1::ScalarField::zero()) {
                return Err(Error::IncorrectBlinding(
                    H,
                    format!("{:?}", blinding_commitments),
                ));
            }
        }

        // `sponge` is for digest computation.
        let sponge = PoseidonSponge::<C1::ScalarField>::new(&self.poseidon_config);

        let (Us, Ws, us, ws) = if MU > 1 || NU > 1 {
            let other_instances = other_instances.ok_or(Error::MissingOtherInstances(MU, NU))?;

            #[allow(clippy::type_complexity)]
            let (lcccs, cccs): (
                Vec<(LCCCS<C1>, Witness<C1::ScalarField>)>,
                Vec<(CCCS<C1>, Witness<C1::ScalarField>)>,
            ) = other_instances;

            // recall, mu & nu is the number of all the LCCCS & CCCS respectively, including the
            // running and incoming instances that are not part of the 'other_instances', hence the +1
            // in the couple of following checks.
            if lcccs.len() + 1 != MU {
                return Err(Error::NotSameLength(
                    "other_instances.lcccs.len()".to_string(),
                    lcccs.len(),
                    "hypernova.mu".to_string(),
                    MU,
                ));
            }
            if cccs.len() + 1 != NU {
                return Err(Error::NotSameLength(
                    "other_instances.cccs.len()".to_string(),
                    cccs.len(),
                    "hypernova.nu".to_string(),
                    NU,
                ));
            }

            let (Us, Ws): (Vec<LCCCS<C1>>, Vec<Witness<C1::ScalarField>>) =
                lcccs.into_iter().unzip();
            let (us, ws): (Vec<CCCS<C1>>, Vec<Witness<C1::ScalarField>>) = cccs.into_iter().unzip();
            (Us, Ws, us, ws)
        } else {
            (vec![], vec![], vec![], vec![])
        };

        let augmented_f_circuit: AugmentedFCircuit<C1, C2, GC2, FC, MU, NU>;

        if self.z_i.len() != self.F.state_len() {
            return Err(Error::NotSameLength(
                "z_i.len()".to_string(),
                self.z_i.len(),
                "F.state_len()".to_string(),
                self.F.state_len(),
            ));
        }
        if external_inputs.len() != self.F.external_inputs_len() {
            return Err(Error::NotSameLength(
                "F.external_inputs_len()".to_string(),
                self.F.external_inputs_len(),
                "external_inputs.len()".to_string(),
                external_inputs.len(),
            ));
        }

        if self.i > C1::ScalarField::from_le_bytes_mod_order(&usize::MAX.to_le_bytes()) {
            return Err(Error::MaxStep);
        }

        let i_usize;

        #[cfg(target_pointer_width = "64")]
        {
            let mut i_bytes: [u8; 8] = [0; 8];
            i_bytes.copy_from_slice(&self.i.into_bigint().to_bytes_le()[..8]);
            i_usize = usize::from_le_bytes(i_bytes);
        }

        #[cfg(target_pointer_width = "32")]
        {
            let mut i_bytes: [u8; 4] = [0; 4];
            i_bytes.copy_from_slice(&self.i.into_bigint().to_bytes_le()[..4]);
            i_usize = usize::from_le_bytes(i_bytes);
        }

        let z_i1 = self.F.step_native(i_usize, &self.z_i, &external_inputs)?;

        // u_{i+1}.x[1] = H(cf_U_{i+1})
        let cf_u_i1_x: C1::ScalarField;
        let (U_i1, mut W_i1);

        if self.i == C1::ScalarField::zero() {
            W_i1 = Witness::<C1::ScalarField>::dummy(&self.ccs);
            W_i1.r_w = self.W_i.r_w;
            U_i1 = LCCCS::dummy(&self.ccs);

            let u_i1_x = U_i1.hash(
                &sponge,
                self.pp_hash,
                C1::ScalarField::one(),
                &self.z_0,
                &z_i1,
            );

            // hash the initial (dummy) CycleFold instance, which is used as the 2nd public
            // input in the AugmentedFCircuit
            cf_u_i1_x = self.cf_U_i.hash_cyclefold(&sponge, &self.pp_hash);

            augmented_f_circuit = AugmentedFCircuit::<C1, C2, GC2, FC, MU, NU> {
                _c2: PhantomData,
                _gc2: PhantomData,
                poseidon_config: self.poseidon_config.clone(),
                ccs: self.ccs.clone(),
                pp_hash: Some(self.pp_hash),
                i: Some(C1::ScalarField::zero()),
                i_usize: Some(0),
                z_0: Some(self.z_0.clone()),
                z_i: Some(self.z_i.clone()),
                external_inputs: Some(external_inputs.clone()),
                U_i: Some(self.U_i.clone()),
                Us: Some(Us),
                u_i_C: Some(self.u_i.C),
                us: Some(us),
                U_i1_C: Some(U_i1.C),
                F: self.F.clone(),
                x: Some(u_i1_x),
                nimfs_proof: None,

                // cyclefold values
                cf_u_i_cmW: None,
                cf_U_i: None,
                cf_x: Some(cf_u_i1_x),
                cf_cmT: None,
            };
        } else {
            let mut transcript_p: PoseidonSponge<C1::ScalarField> =
                PoseidonSponge::<C1::ScalarField>::new(&self.poseidon_config);
            transcript_p.absorb(&self.pp_hash);

            let (all_Us, all_us, all_Ws, all_ws) = (
                [&[self.U_i.clone()][..], &Us].concat(),
                [&[self.u_i.clone()][..], &us].concat(),
                [vec![self.W_i.clone()], Ws].concat(),
                [vec![self.w_i.clone()], ws].concat(),
            );

            let (rho, nimfs_proof);
            (nimfs_proof, U_i1, W_i1, rho) = NIMFS::<C1, PoseidonSponge<C1::ScalarField>>::prove(
                &mut transcript_p,
                &self.ccs,
                &all_Us,
                &all_us,
                &all_Ws,
                &all_ws,
            )?;

            // sanity check: check the folded instance relation
            #[cfg(test)]
            self.ccs.check_relation(&W_i1, &U_i1)?;

            let u_i1_x = U_i1.hash(
                &sponge,
                self.pp_hash,
                self.i + C1::ScalarField::one(),
                &self.z_0,
                &z_i1,
            );

            let rho_bits = rho.into_bigint().to_bits_le()[..NOVA_N_BITS_RO].to_vec();
            let rho_Fq = C1::BaseField::from(<C1::BaseField as PrimeField>::BigInt::from_bits_le(
                &rho_bits,
            ));

            // CycleFold part:
            // get the vector used as public inputs 'x' in the CycleFold circuit.
            // Place the random values and the points coordinates as the public input x:
            // In Nova, this is: x == [r, p1, p2, p3].
            // In multifolding schemes such as HyperNova, this is:
            // computed_x = [r, p_0, p_1, p_2, ..., p_n],
            // where each p_i is in fact p_i.to_constraint_field()
            let cf_u_i_x = [
                vec![rho_Fq],
                all_Us
                    .iter()
                    .flat_map(|Us_i| get_cm_coordinates(&Us_i.C))
                    .collect(),
                all_us
                    .iter()
                    .flat_map(|us_i| get_cm_coordinates(&us_i.C))
                    .collect(),
                get_cm_coordinates(&U_i1.C),
            ]
            .concat();

            let cf_circuit = HyperNovaCycleFoldCircuit::<C1, GC1, MU, NU> {
                _gc: PhantomData,
                r_bits: Some(rho_bits.clone()),
                points: Some(
                    [
                        all_Us.iter().map(|Us_i| Us_i.C).collect::<Vec<_>>(),
                        all_us.iter().map(|us_i| us_i.C).collect::<Vec<_>>(),
                    ]
                    .concat(),
                ),
                x: Some(cf_u_i_x.clone()),
            };

            let (_cf_w_i, cf_u_i, cf_W_i1, cf_U_i1, cf_cmT, _) = fold_cyclefold_circuit::<
                HyperNovaCycleFoldConfig<C1, MU, NU>,
                C1,
                GC1,
                C2,
                GC2,
                CS2,
                H,
            >(
                &mut transcript_p,
                &self.cf_r1cs,
                &self.cf_cs_pp,
                &self.pp_hash,
                &self.cf_W_i, // CycleFold running instance witness
                &self.cf_U_i, // CycleFold running instance
                &cf_u_i_x,
                cf_circuit,
                &mut rng,
            )?;

            cf_u_i1_x = cf_U_i1.hash_cyclefold(&sponge, &self.pp_hash);

            augmented_f_circuit = AugmentedFCircuit::<C1, C2, GC2, FC, MU, NU> {
                _c2: PhantomData,
                _gc2: PhantomData,
                poseidon_config: self.poseidon_config.clone(),
                ccs: self.ccs.clone(),
                pp_hash: Some(self.pp_hash),
                i: Some(self.i),
                i_usize: Some(i_usize),
                z_0: Some(self.z_0.clone()),
                z_i: Some(self.z_i.clone()),
                external_inputs: Some(external_inputs),
                U_i: Some(self.U_i.clone()),
                Us: Some(Us),
                u_i_C: Some(self.u_i.C),
                us: Some(us),
                U_i1_C: Some(U_i1.C),
                F: self.F.clone(),
                x: Some(u_i1_x),
                nimfs_proof: Some(nimfs_proof),

                // cyclefold values
                cf_u_i_cmW: Some(cf_u_i.cmW),
                cf_U_i: Some(self.cf_U_i.clone()),
                cf_x: Some(cf_u_i1_x),
                cf_cmT: Some(cf_cmT),
            };

            // assign the next round instances
            self.cf_W_i = cf_W_i1;
            self.cf_U_i = cf_U_i1;
        }

        let (cs, _) = augmented_f_circuit.compute_cs_ccs()?;

        #[cfg(test)]
        assert!(cs.is_satisfied()?);

        let (r1cs_w_i1, r1cs_x_i1) = extract_w_x::<C1::ScalarField>(&cs); // includes 1 and public inputs

        let r1cs_z = [
            vec![C1::ScalarField::one()],
            r1cs_x_i1.clone(),
            r1cs_w_i1.clone(),
        ]
        .concat();
        // compute committed instances, w_{i+1}, u_{i+1}, which will be used as w_i, u_i, so we
        // assign them directly to w_i, u_i.
        let (u_i, w_i) = self
            .ccs
            .to_cccs::<_, C1, CS1, H>(&mut rng, &self.cs_pp, &r1cs_z)?;
        self.u_i = u_i.clone();
        self.w_i = w_i.clone();

        // set values for next iteration
        self.i += C1::ScalarField::one();
        // assign z_{i+1} into z_i
        self.z_i = z_i1.clone();
        self.U_i = U_i1.clone();
        self.W_i = W_i1.clone();

        #[cfg(test)]
        {
            // check the new LCCCS instance relation
            self.ccs.check_relation(&self.W_i, &self.U_i)?;
            // check the new CCCS instance relation
            self.ccs.check_relation(&self.w_i, &self.u_i)?;
        }

        Ok(())
    }

    fn state(&self) -> Vec<C1::ScalarField> {
        self.z_i.clone()
    }

    fn ivc_proof(&self) -> Self::IVCProof {
        Self::IVCProof {
            i: self.i,
            z_0: self.z_0.clone(),
            z_i: self.z_i.clone(),
            W_i: self.W_i.clone(),
            U_i: self.U_i.clone(),
            w_i: self.w_i.clone(),
            u_i: self.u_i.clone(),
            cf_W_i: self.cf_W_i.clone(),
            cf_U_i: self.cf_U_i.clone(),
        }
    }

    fn from_ivc_proof(
        ivc_proof: Self::IVCProof,
        fcircuit_params: FC::Params,
        params: (Self::ProverParam, Self::VerifierParam),
    ) -> Result<Self, Error> {
        let IVCProof {
            i,
            z_0,
            z_i,
            W_i,
            U_i,
            w_i,
            u_i,
            cf_W_i,
            cf_U_i,
        } = ivc_proof;
        let (pp, vp) = params;

        let f_circuit = FC::new(fcircuit_params)?;
        let augmented_f_circuit = AugmentedFCircuit::<C1, C2, GC2, FC, MU, NU>::empty(
            &pp.poseidon_config,
            f_circuit.clone(),
            None,
        )?;
        let cf_circuit = HyperNovaCycleFoldCircuit::<C1, GC1, MU, NU>::empty();

        let ccs = augmented_f_circuit.ccs.clone();
        let cf_r1cs = get_r1cs_from_cs::<C2::ScalarField>(cf_circuit)?;

        Ok(Self {
            _gc1: PhantomData,
            _c2: PhantomData,
            _gc2: PhantomData,
            ccs,
            cf_r1cs,
            poseidon_config: pp.poseidon_config,
            cs_pp: pp.cs_pp,
            cf_cs_pp: pp.cf_cs_pp,
            F: f_circuit,
            pp_hash: vp.pp_hash()?,
            i,
            z_0,
            z_i,
            w_i,
            u_i,
            W_i,
            U_i,
            cf_W_i,
            cf_U_i,
        })
    }

    /// Implements IVC.V of Hyp.clone()erNova+CycleFold. Notice that this method does not include the
    /// commitments verification, which is done in the Decider.
    fn verify(vp: Self::VerifierParam, ivc_proof: Self::IVCProof) -> Result<(), Error> {
        let Self::IVCProof {
            i: num_steps,
            z_0,
            z_i,
            W_i,
            U_i,
            w_i,
            u_i,
            cf_W_i,
            cf_U_i,
        } = ivc_proof;

        if num_steps == C1::ScalarField::zero() {
            if z_0 != z_i {
                return Err(Error::IVCVerificationFail);
            }
            return Ok(());
        }
        // `sponge` is for digest computation.
        let sponge = PoseidonSponge::<C1::ScalarField>::new(&vp.poseidon_config);

        if u_i.x.len() != 2 || U_i.x.len() != 2 {
            return Err(Error::IVCVerificationFail);
        }

        let pp_hash = vp.pp_hash()?;

        // check that u_i's output points to the running instance
        // u_i.X[0] == H(i, z_0, z_i, U_i)
        let expected_u_i_x = U_i.hash(&sponge, pp_hash, num_steps, &z_0, &z_i);
        if expected_u_i_x != u_i.x[0] {
            return Err(Error::IVCVerificationFail);
        }
        // u_i.X[1] == H(cf_U_i)
        let expected_cf_u_i_x = cf_U_i.hash_cyclefold(&sponge, &pp_hash);
        if expected_cf_u_i_x != u_i.x[1] {
            return Err(Error::IVCVerificationFail);
        }

        // check LCCCS satisfiability
        vp.ccs.check_relation(&W_i, &U_i)?;
        // check CCCS satisfiability
        vp.ccs.check_relation(&w_i, &u_i)?;

        // check CycleFold's RelaxedR1CS satisfiability
        vp.cf_r1cs.check_relation(&cf_W_i, &cf_U_i)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::commitment::kzg::KZG;
    use ark_bn254::{constraints::GVar, Bn254, Fr, G1Projective as Projective};
    use ark_grumpkin::{constraints::GVar as GVar2, Projective as Projective2};
    use ark_std::UniformRand;

    use super::*;
    use crate::commitment::pedersen::Pedersen;
    use crate::frontend::utils::CubicFCircuit;
    use crate::transcript::poseidon::poseidon_canonical_config;

    #[test]
    pub fn test_ivc() {
        let poseidon_config = poseidon_canonical_config::<Fr>();

        let F_circuit = CubicFCircuit::<Fr>::new(()).unwrap();

        // run the test using Pedersen commitments on both sides of the curve cycle
        test_ivc_opt::<Pedersen<Projective>, Pedersen<Projective2>, false>(
            poseidon_config.clone(),
            F_circuit,
        );

        test_ivc_opt::<Pedersen<Projective, true>, Pedersen<Projective2, true>, true>(
            poseidon_config.clone(),
            F_circuit,
        );

        // run the test using KZG for the commitments on the main curve, and Pedersen for the
        // commitments on the secondary curve
        test_ivc_opt::<KZG<Bn254>, Pedersen<Projective2>, false>(poseidon_config, F_circuit);
    }

    #[allow(clippy::type_complexity)]
    // test_ivc allowing to choose the CommitmentSchemes
    pub fn test_ivc_opt<
        CS1: CommitmentScheme<Projective, H>,
        CS2: CommitmentScheme<Projective2, H>,
        const H: bool,
    >(
        poseidon_config: PoseidonConfig<Fr>,
        F_circuit: CubicFCircuit<Fr>,
    ) {
        let mut rng = ark_std::test_rng();

        const MU: usize = 2;
        const NU: usize = 3;

        type HN<CS1, CS2, const H: bool> =
            HyperNova<Projective, GVar, Projective2, GVar2, CubicFCircuit<Fr>, CS1, CS2, MU, NU, H>;

        let prep_param =
            PreprocessorParam::<Projective, Projective2, CubicFCircuit<Fr>, CS1, CS2, H>::new(
                poseidon_config.clone(),
                F_circuit,
            );
        let hypernova_params = HN::preprocess(&mut rng, &prep_param).unwrap();

        let z_0 = vec![Fr::from(3_u32)];
        let mut hypernova = HN::init(&hypernova_params, F_circuit, z_0.clone()).unwrap();

        let (w_i_blinding, W_i_blinding) = if H {
            (Fr::rand(&mut rng), Fr::rand(&mut rng))
        } else {
            (Fr::zero(), Fr::zero())
        };
        hypernova.w_i.r_w = w_i_blinding;
        hypernova.W_i.r_w = W_i_blinding;

        let num_steps: usize = 3;
        for _ in 0..num_steps {
            // prepare some new instances to fold in the multifolding step
            let mut lcccs = vec![];
            for j in 0..MU - 1 {
                let instance_state = vec![Fr::from(j as u32 + 85_u32)];
                let (U, W) = hypernova
                    .new_running_instance(&mut rng, instance_state, vec![])
                    .unwrap();
                lcccs.push((U, W));
            }
            let mut cccs = vec![];
            for j in 0..NU - 1 {
                let instance_state = vec![Fr::from(j as u32 + 15_u32)];
                let (u, w) = hypernova
                    .new_incoming_instance(&mut rng, instance_state, vec![])
                    .unwrap();
                cccs.push((u, w));
            }

            hypernova
                .prove_step(&mut rng, vec![], Some((lcccs, cccs)))
                .unwrap();
        }
        assert_eq!(Fr::from(num_steps as u32), hypernova.i);

        let ivc_proof = hypernova.ivc_proof();
        HN::verify(
            hypernova_params.1.clone(), // verifier_params
            ivc_proof,
        )
        .unwrap();
    }
}
