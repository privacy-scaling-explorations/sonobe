/// Contains prebuild objects with common configurations of the library.

/// eth module uses the curve cycle of BN254 and Grumpkin curves.
pub mod eth {
    use ark_bn254::{constraints::GVar, Bn254, G1Projective as G1};
    use ark_groth16::Groth16;
    use ark_grumpkin::{constraints::GVar as GVar2, Projective as G2};

    use crate::{
        commitment::{kzg::KZG, pedersen::Pedersen},
        folding::{
            hypernova::HyperNova,
            nova::{decider_eth::Decider as DeciderEth, Nova},
        },
    };

    /// Nova + CycleFold for Ethereum's onchain verification
    pub type NOVA<FC> = Nova<G1, GVar, G2, GVar2, FC, KZG<'static, Bn254>, Pedersen<G2>>;
    pub type DECIDER<FC> = DeciderEth<
        G1,
        GVar,
        G2,
        GVar2,
        FC,
        KZG<'static, Bn254>,
        Pedersen<G2>,
        Groth16<Bn254>,
        NOVA<FC>,
    >;

    /// HyperNova + CycleFold for Ethereum's onchain verification
    pub type HYPERNOVA<FC> = HyperNova<G1, GVar, G2, GVar2, FC, KZG<'static, Bn254>, Pedersen<G2>>;
}
