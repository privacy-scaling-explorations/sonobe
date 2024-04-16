{{ groth16_verifier }}

{{ kzg10_verifier }}

/**
 * @notice  Computes the decomposition of a `uint256` into num_limbs limbs of bits_per_limb bits each.
 * @dev     Compatible with folding-schemes::folding::circuits::nonnative::nonnative_field_to_field_elements.
 */
library LimbsDecomposition {
    function decompose(uint256 x) internal pure returns (uint256[{{num_limbs}}] memory) {
        uint256[{{num_limbs}}] memory limbs;
        for (uint8 i = 0; i < {{num_limbs}}; i++) {
            limbs[i] = (x >> ({{bits_per_limb}} * i)) & ((1 << {{bits_per_limb}}) - 1);
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
        // inputs are grouped to prevent errors due stack too deep
        uint256[{{ 1 + z_len * 2 }}] calldata i_z0_zi, // [i, z0, zi] where |z0| == |zi|
        uint256[4] calldata U_i_cmW_U_i_cmE, // [U_i_cmW[2], U_i_cmE[2]]
        uint256[3] calldata U_i_u_u_i_u_r, // [U_i_u, u_i_u, r]
        uint256[4] calldata U_i_x_u_i_cmW, // [U_i_x[2], u_i_cmW[2]]
        uint256[4] calldata u_i_x_cmT, // [u_i_x[2], cmT[2]]
        uint256[2] calldata pA, // groth16 
        uint256[2][2] calldata pB, // groth16
        uint256[2] calldata pC, // groth16
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
            // U_i.u + r * u_i.u
            uint256 u = rlCombination(U_i_u_u_i_u_r[0], U_i_u_u_i_u_r[2], U_i_u_u_i_u_r[1]);
            // U_i.x + r * u_i.x
            uint256 x0 = rlCombination(U_i_x_u_i_cmW[0], U_i_u_u_i_u_r[2], u_i_x_cmT[0]);
            uint256 x1 = rlCombination(U_i_x_u_i_cmW[1], U_i_u_u_i_u_r[2], u_i_x_cmT[1]);

            public_inputs[{{ z_len * 2 + 1 }}] = u;
            public_inputs[{{ z_len * 2 + 2 }}] = x0;
            public_inputs[{{ z_len * 2 + 3 }}] = x1;
        }

        {
            // U_i.cmE + r * u_i.cmT
            uint256[2] memory mulScalarPoint = super.mulScalar([u_i_x_cmT[2], u_i_x_cmT[3]], U_i_u_u_i_u_r[2]);
            uint256[2] memory cmE = super.add([U_i_cmW_U_i_cmE[2], U_i_cmW_U_i_cmE[3]], mulScalarPoint);

            {
                uint256[{{num_limbs}}] memory cmE_x_limbs = LimbsDecomposition.decompose(cmE[0]);
                uint256[{{num_limbs}}] memory cmE_y_limbs = LimbsDecomposition.decompose(cmE[1]);
            
                for (uint8 k = 0; k < {{num_limbs}}; k++) {
                    public_inputs[{{ z_len * 2 + 4 }} + k] = cmE_x_limbs[k];
                    public_inputs[{{ z_len * 2 + 4 + num_limbs }} + k] = cmE_y_limbs[k];
                }
            }

            require(this.check(cmE, kzg_proof[1], challenge_W_challenge_E_kzg_evals[1], challenge_W_challenge_E_kzg_evals[3]), "KZG: verifying proof for challenge E failed");
        }

        {
            // U_i.cmW + r * u_i.cmW
            uint256[2] memory mulScalarPoint = super.mulScalar([U_i_x_u_i_cmW[2], U_i_x_u_i_cmW[3]], U_i_u_u_i_u_r[2]);
            uint256[2] memory cmW = super.add([U_i_cmW_U_i_cmE[0], U_i_cmW_U_i_cmE[1]], mulScalarPoint);
        
            {
                uint256[{{num_limbs}}] memory cmW_x_limbs = LimbsDecomposition.decompose(cmW[0]);
                uint256[{{num_limbs}}] memory cmW_y_limbs = LimbsDecomposition.decompose(cmW[1]);
        
                for (uint8 k = 0; k < {{num_limbs}}; k++) {
                    public_inputs[{{ z_len * 2 + 4 + num_limbs * 2 }} + k] = cmW_x_limbs[k];
                    public_inputs[{{ z_len * 2 + 4 + num_limbs * 3 }} + k] = cmW_y_limbs[k];
                }
            }
        
            require(this.check(cmW, kzg_proof[0], challenge_W_challenge_E_kzg_evals[0], challenge_W_challenge_E_kzg_evals[2]), "KZG: verifying proof for challenge W failed");
        }

        {
            // add challenges
            public_inputs[{{ z_len * 2 + 4 + num_limbs * 4 }}] = challenge_W_challenge_E_kzg_evals[0];
            public_inputs[{{ z_len * 2 + 4 + num_limbs * 4 + 1 }}] = challenge_W_challenge_E_kzg_evals[1];
            public_inputs[{{ z_len * 2 + 4 + num_limbs * 4 + 2 }}] = challenge_W_challenge_E_kzg_evals[2];
            public_inputs[{{ z_len * 2 + 4 + num_limbs * 4 + 3 }}] = challenge_W_challenge_E_kzg_evals[3];
        
            uint256[{{num_limbs}}] memory cmT_x_limbs;
            uint256[{{num_limbs}}] memory cmT_y_limbs;
        
            cmT_x_limbs = LimbsDecomposition.decompose(u_i_x_cmT[2]);
            cmT_y_limbs = LimbsDecomposition.decompose(u_i_x_cmT[3]);
        
            for (uint8 k = 0; k < {{num_limbs}}; k++) {
                public_inputs[{{ z_len * 2 + 4 + num_limbs * 4 }} + 4 + k] = cmT_x_limbs[k]; 
                public_inputs[{{ z_len * 2 + 4 + num_limbs * 5}} + 4 + k] = cmT_y_limbs[k];
            }
        
            // last element of the groth16 proof's public inputs is `r`
            public_inputs[{{ public_inputs_len - 2 }}] = U_i_u_u_i_u_r[2];
            
            bool success_g16 = this.verifyProof(pA, pB, pC, public_inputs);
            require(success_g16 == true, "Groth16: verifying proof failed");
        }

        return(true);
    }
}
