/*
    Sonobe's Nova + CycleFold decider verifier.
    Joint effort by 0xPARC & PSE.

    More details at https://github.com/privacy-scaling-explorations/sonobe
    Usage and design documentation at https://privacy-scaling-explorations.github.io/sonobe-docs/

    Uses the https://github.com/iden3/snarkjs/blob/master/templates/verifier_groth16.sol.ejs
    Groth16 verifier implementation and a KZG10 Solidity template adapted from
    https://github.com/weijiekoh/libkzg.
    Additionally we implement the NovaDecider contract, which combines the
    Groth16 and KZG10 verifiers to verify the zkSNARK proofs coming from
    Nova+CycleFold folding.
*/


/* =============================== */
/* KZG10 verifier methods */
{{ kzg10_verifier }}

/* =============================== */
/* Groth16 verifier methods */
{{ groth16_verifier }}


/* =============================== */
/* Nova+CycleFold Decider verifier */
/**
 * @notice  Computes the decomposition of a `uint256` into num_limbs limbs of bits_per_limb bits each.
 * @dev     Compatible with sonobe::folding-schemes::folding::circuits::nonnative::nonnative_field_to_field_elements.
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
 * @author PSE & 0xPARC
 * @title  Interface for the NovaDecider contract hiding proof details.
 * @dev    This interface enables calling the verifyNovaProof function without exposing the proof details.
 */
interface OpaqueDecider {
    /**
     * @notice  Verifies a Nova+CycleFold proof given initial and final IVC states, number of steps and the rest proof inputs concatenated.
     * @dev     This function should simply reorganize arguments and pass them to the proper verification function.
     */
    function verifyOpaqueNovaProofWithInputs(
        uint256 steps, // number of folded steps (i)
        uint256[{{ z_len }}] calldata initial_state, // initial IVC state (z0)
        uint256[{{ z_len }}] calldata final_state, // IVC state after i steps (zi)
        uint256[25] calldata proof // the rest of the decider inputs
    ) external view returns (bool);

    /**
     * @notice  Verifies a Nova+CycleFold proof given all the proof inputs collected in a single array.
     * @dev     This function should simpy reorganize arguments and pass them to the proper verification function.
     */
    function verifyOpaqueNovaProof(uint256[{{ 26 + z_len * 2 }}] calldata proof) external view returns (bool);
}

/**
 * @author  PSE & 0xPARC
 * @title   NovaDecider contract, for verifying Nova IVC SNARK proofs.
 * @dev     This is an askama template which, when templated, features a Groth16 and KZG10 verifiers from which this contract inherits.
 */
contract NovaDecider is Groth16Verifier, KZG10Verifier {
    /**
     * @notice  Computes the linear combination of a and b with r as the coefficient.
     * @dev     All ops are done mod the BN254 scalar field prime
     */
    function rlc(uint256 a, uint256 r, uint256 b) internal pure returns (uint256 result) {
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
        uint256[2] calldata u_i_cmW, // [u_i_cmW[2]]
        uint256[3] calldata cmT_r, // [cmT[2], r]
        uint256[2] calldata pA, // groth16 
        uint256[2][2] calldata pB, // groth16
        uint256[2] calldata pC, // groth16
        uint256[4] calldata challenge_W_challenge_E_kzg_evals, // [challenge_W, challenge_E, eval_W, eval_E]
        uint256[2][2] calldata kzg_proof // [proof_W, proof_E]
    ) public view returns (bool) {

        require(i_z0_zi[0] >= 2, "Folding: the number of folded steps should be at least 2");

        // from gamma_abc_len, we subtract 1. 
        uint256[{{ public_inputs_len - 1 }}] memory public_inputs; 

        public_inputs[0] = {{pp_hash}};
        public_inputs[1] = i_z0_zi[0];

        for (uint i = 0; i < {{ z_len * 2 }}; i++) {
            public_inputs[2 + i] = i_z0_zi[1 + i];
        }

        {
            // U_i.cmW + r * u_i.cmW
            uint256[2] memory mulScalarPoint = super.mulScalar([u_i_cmW[0], u_i_cmW[1]], cmT_r[2]);
            uint256[2] memory cmW = super.add([U_i_cmW_U_i_cmE[0], U_i_cmW_U_i_cmE[1]], mulScalarPoint);

            {
                uint256[{{num_limbs}}] memory cmW_x_limbs = LimbsDecomposition.decompose(cmW[0]);
                uint256[{{num_limbs}}] memory cmW_y_limbs = LimbsDecomposition.decompose(cmW[1]);
        
                for (uint8 k = 0; k < {{num_limbs}}; k++) {
                    public_inputs[{{ z_len * 2 + 2 }} + k] = cmW_x_limbs[k];
                    public_inputs[{{ z_len * 2 + 2 + num_limbs }} + k] = cmW_y_limbs[k];
                }
            }
        
            require(this.check(cmW, kzg_proof[0], challenge_W_challenge_E_kzg_evals[0], challenge_W_challenge_E_kzg_evals[2]), "KZG: verifying proof for challenge W failed");
        }

        {
            // U_i.cmE + r * cmT
            uint256[2] memory mulScalarPoint = super.mulScalar([cmT_r[0], cmT_r[1]], cmT_r[2]);
            uint256[2] memory cmE = super.add([U_i_cmW_U_i_cmE[2], U_i_cmW_U_i_cmE[3]], mulScalarPoint);

            {
                uint256[{{num_limbs}}] memory cmE_x_limbs = LimbsDecomposition.decompose(cmE[0]);
                uint256[{{num_limbs}}] memory cmE_y_limbs = LimbsDecomposition.decompose(cmE[1]);
            
                for (uint8 k = 0; k < {{num_limbs}}; k++) {
                    public_inputs[{{ z_len * 2 + 2 + num_limbs * 2 }} + k] = cmE_x_limbs[k];
                    public_inputs[{{ z_len * 2 + 2 + num_limbs * 3 }} + k] = cmE_y_limbs[k];
                }
            }

            require(this.check(cmE, kzg_proof[1], challenge_W_challenge_E_kzg_evals[1], challenge_W_challenge_E_kzg_evals[3]), "KZG: verifying proof for challenge E failed");
        }

        {
            // add challenges
            public_inputs[{{ z_len * 2 + 2 + num_limbs * 4 }}] = challenge_W_challenge_E_kzg_evals[0];
            public_inputs[{{ z_len * 2 + 2 + num_limbs * 4 + 1 }}] = challenge_W_challenge_E_kzg_evals[1];
            public_inputs[{{ z_len * 2 + 2 + num_limbs * 4 + 2 }}] = challenge_W_challenge_E_kzg_evals[2];
            public_inputs[{{ z_len * 2 + 2 + num_limbs * 4 + 3 }}] = challenge_W_challenge_E_kzg_evals[3];

            uint256[{{num_limbs}}] memory cmT_x_limbs;
            uint256[{{num_limbs}}] memory cmT_y_limbs;
        
            cmT_x_limbs = LimbsDecomposition.decompose(cmT_r[0]);
            cmT_y_limbs = LimbsDecomposition.decompose(cmT_r[1]);
        
            for (uint8 k = 0; k < {{num_limbs}}; k++) {
                public_inputs[{{ z_len * 2 + 2 + num_limbs * 4 }} + 4 + k] = cmT_x_limbs[k]; 
                public_inputs[{{ z_len * 2 + 2 + num_limbs * 5 }} + 4 + k] = cmT_y_limbs[k];
            }

            bool success_g16 = this.verifyProof(pA, pB, pC, public_inputs);
            require(success_g16 == true, "Groth16: verifying proof failed");
        }

        return(true);
    }

    /**
     * @notice  Verifies a Nova+CycleFold proof given initial and final IVC states, number of steps and the rest proof inputs concatenated.
     * @dev     Simply reorganization of arguments and call to the `verifyNovaProof` function.
     */
    function verifyOpaqueNovaProofWithInputs(
        uint256 steps,
        uint256[{{ z_len }}] calldata initial_state,
        uint256[{{ z_len }}] calldata final_state,
        uint256[25] calldata proof
    ) public view returns (bool) {
        uint256[1 + 2 * {{ z_len }}] memory i_z0_zi;
        i_z0_zi[0] = steps;
        for (uint256 i = 0; i < {{ z_len }}; i++) {
            i_z0_zi[i + 1] = initial_state[i];
            i_z0_zi[i + 1 + {{ z_len }}] = final_state[i];
        }

        uint256[4] memory U_i_cmW_U_i_cmE = [proof[0], proof[1], proof[2], proof[3]];
        uint256[2] memory u_i_cmW = [proof[4], proof[5]];
        uint256[3] memory cmT_r = [proof[6], proof[7], proof[8]];
        uint256[2] memory pA = [proof[9], proof[10]];
        uint256[2][2] memory pB = [[proof[11], proof[12]], [proof[13], proof[14]]];
        uint256[2] memory pC = [proof[15], proof[16]];
        uint256[4] memory challenge_W_challenge_E_kzg_evals = [proof[17], proof[18], proof[19], proof[20]];
        uint256[2][2] memory kzg_proof = [[proof[21], proof[22]], [proof[23], proof[24]]];

        return this.verifyNovaProof(
            i_z0_zi,
            U_i_cmW_U_i_cmE,
            u_i_cmW,
            cmT_r,
            pA,
            pB,
            pC,
            challenge_W_challenge_E_kzg_evals,
            kzg_proof
        );
    }

    /**
     * @notice  Verifies a Nova+CycleFold proof given all proof inputs concatenated.
     * @dev     Simply reorganization of arguments and call to the `verifyNovaProof` function.
     */
    function verifyOpaqueNovaProof(uint256[{{ 26 + z_len * 2 }}] calldata proof) public view returns (bool) {
        uint256[{{ z_len }}] memory z0;
        uint256[{{ z_len }}] memory zi;
        for (uint256 i = 0; i < {{ z_len }}; i++) {
            z0[i] = proof[i + 1];
            zi[i] = proof[i + 1 + {{ z_len }}];
        }

        uint256[25] memory extracted_proof;
        for (uint256 i = 0; i < 25; i++) {
            extracted_proof[i] = proof[{{ 1 + 2 * z_len }} + i];
        }

        return this.verifyOpaqueNovaProofWithInputs(proof[0], z0, zi, extracted_proof);
    }
}
