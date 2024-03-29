{{ groth16_verifier }}

{{ kzg10_verifier }}

/**
 * @notice  Computes the decomposition of a `uint` into 17 limbs of 15 bits each.
 * @dev     We emulate the limb decomposition `OptimizationType::Constraints` strategy found in arkworks.
 */
library LimbsDecomposition {
    uint8 constant BN254_NUM_LIMBS = 17;
    uint8 constant BN254_BITS_PER_LIMB = 15;

    function decompose(uint256 x) internal pure returns (uint256[BN254_NUM_LIMBS] memory) {
        uint256[BN254_NUM_LIMBS] memory limbs;
        for (uint8 i = 0; i < BN254_NUM_LIMBS; i++) {
            limbs[i] = (x >> (BN254_BITS_PER_LIMB * i)) & ((1 << BN254_BITS_PER_LIMB) - 1);
        }
        return limbs;
    }
}

/**
 * @author  PSE & 0xPARC
 * @title   NovaDecider contract, for verifying Nova IVC SNARK proofs.
 * @dev     This is an askama template which, when templated, features a snarkjs groth16 and a kzg10 verifier from which this contract inherits.
 */
contract NovaDecider is Groth16Verifier, KZG10Verifier {

    /**
     * @notice  Computes the linear combination of a and b with r as the coefficient.
     * @dev     All ops are done mod the BN254 scalar field prime
     */
    function rlCombination(uint256 a, uint256 r, uint256 b) internal pure returns (uint256 result) {
        assembly {
            result := addmod(a, mulmod(r, b, BN254_SCALAR_FIELD), BN254_SCALAR_FIELD)
        }
    }

    /**
     * @notice  Verifies a nova cyclefold proof consisting of two KZG proofs and of a groth16 proof.
     * @dev     The selector of this function is "dynamic", since it depends on `z_len`.
     */
    function verifyNovaProof(
        uint256[{{ 1 + z_len * 2 }}] calldata i_z0_zi, // [i, z0, zi] where |z0| == |zi|
        uint256[4] calldata U_i_cmW_U_i_cmE, // [U_i_cmW[2], U_i_cmE[2]]
        uint256[3] calldata U_i_u_u_i_u_r, // [U_i_u, u_i_u, r]
        uint[3] calldata U_i_x_u_i_cmW, // [U_i_x, u_i_cmW[2]]
        uint[3] calldata u_i_x_cmT, // [u_i_x, cmT[2]]
        uint[2] calldata pA, // groth16 
        uint[2][2] calldata pB, // groth16
        uint[2] calldata pC, // groth16
        uint256[4] calldata challenge_W_challenge_E_kzg_evals, // [challenge_W, challenge_E, eval_W, eval_E]
        uint256[2][2] calldata kzg_proof // [proof_W, proof_E]
    ) public view returns (bool) {

        require(i_z0_zi[0] >= 2, "Folding: the number of folded steps should be at least 2");

        // from gamma_abc_len, we subtract 1. 
        uint256[{{ public_inputs_len - 1 }}] memory public_inputs; 

        public_inputs[0] = i_z0_zi[0];

        for (uint i = 0; i < {{ z_len * 2 }}; i++) {
            public_inputs[1 + i] = i_z0_zi[1 + i];
        }

        {
            uint256 u = rlCombination(U_i_u_u_i_u_r[0], U_i_u_u_i_u_r[2], U_i_u_u_i_u_r[1]);
            uint256 x = rlCombination(U_i_x_u_i_cmW[0], U_i_u_u_i_u_r[2], u_i_x_cmT[0]);

            public_inputs[{{ z_len * 2 + 1 }}] = u;
            public_inputs[{{ z_len * 2 + 2 }}] = x;
        }

        {
            uint256[2] memory mulScalarPoint = super.mulScalar([u_i_x_cmT[1], u_i_x_cmT[2]], U_i_u_u_i_u_r[2]);
            uint256[2] memory cmE = super.add([U_i_cmW_U_i_cmE[2], U_i_cmW_U_i_cmE[3]], mulScalarPoint);

            {
                uint256[17] memory cmE_x_limbs = LimbsDecomposition.decompose(cmE[0]);
                uint256[17] memory cmE_y_limbs = LimbsDecomposition.decompose(cmE[1]);

                // input limbs in little endian format
                for (uint8 k = 0; k < 17; k++) {
                    public_inputs[{{ z_len * 2 + 3 }} + k] = cmE_x_limbs[16 - k];
                    public_inputs[{{ z_len * 2 + 20 }} + k] = cmE_y_limbs[16 - k];
                }
            }

            require(this.check(cmE, kzg_proof[1], challenge_W_challenge_E_kzg_evals[1], challenge_W_challenge_E_kzg_evals[3]), "KZG: verifying proof for challenge E failed");
        }

        {
            uint256[2] memory mulScalarPoint = super.mulScalar([U_i_x_u_i_cmW[1], U_i_x_u_i_cmW[2]], U_i_u_u_i_u_r[2]);
            uint256[2] memory cmW = super.add([U_i_cmW_U_i_cmE[0], U_i_cmW_U_i_cmE[1]], mulScalarPoint);

            {
                uint256[17] memory cmW_x_limbs = LimbsDecomposition.decompose(cmW[0]);
                uint256[17] memory cmW_y_limbs = LimbsDecomposition.decompose(cmW[1]);

                // input limbs in little endian format
                for (uint8 k = 0; k < 17; k++) {
                    public_inputs[{{ z_len * 2 + 37 }} + k] = cmW_x_limbs[16 - k];
                    public_inputs[{{ z_len * 2 + 54 }} + k] = cmW_y_limbs[16 - k];
                }
            }

            require(this.check(cmW, kzg_proof[0], challenge_W_challenge_E_kzg_evals[0], challenge_W_challenge_E_kzg_evals[2]), "KZG: verifying proof for challenge W failed");
        }

        {
            // adding challenges
            // we inserted above 17 limbs starting from index 54, so we now start from 54 + 17 = 71 (+ z_len * 2)
            public_inputs[{{ z_len * 2 + 71 }}] = challenge_W_challenge_E_kzg_evals[0];
            public_inputs[{{ z_len * 2 + 72 }}] = challenge_W_challenge_E_kzg_evals[1];
            public_inputs[{{ z_len * 2 + 73 }}] = challenge_W_challenge_E_kzg_evals[2];
            public_inputs[{{ z_len * 2 + 74 }}] = challenge_W_challenge_E_kzg_evals[3];

            uint256[17] memory cmT_x_limbs;
            uint256[17] memory cmT_y_limbs;

            cmT_x_limbs = LimbsDecomposition.decompose(u_i_x_cmT[1]);
            cmT_y_limbs = LimbsDecomposition.decompose(u_i_x_cmT[2]);

            // input limbs in little endian format
            for (uint8 k = 0; k < 17; k++) {
                public_inputs[{{ z_len * 2 + 75 }} + k] = cmT_x_limbs[16 - k]; 
                public_inputs[{{ z_len * 2 + 92 }} + k] = cmT_y_limbs[16 - k];
            }

            // last element of the groth16 proof's public inputs is `r`
            public_inputs[{{ public_inputs_len - 2 }}] = U_i_u_u_i_u_r[2];
            
            bool success_g16 = this.verifyProof(pA, pB, pC, public_inputs);
            require(success_g16 == true, "Groth16: verifying proof failed");
        }

        return(true);
    }
}
