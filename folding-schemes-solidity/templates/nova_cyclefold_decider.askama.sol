pragma solidity ^0.8.4;

{{ groth16_verifier }}

{{ kzg10_verifier }}

/**
 * @author  PSE & 0xPARC
 * @title   NovaDecider contract, for verifying zk-snarks Nova IVC proofs.
 * @dev     This is an askama template. It will feature a snarkjs groth16 and a kzg10 verifier, from which this contract inherits.
 *          WARNING: This contract is known to not be sound. It lacks checks to ensure that no soundness issues can happen.
 *          but for now, it's good enough for testing and benchmarking.
 */
contract NovaDecider is Groth16Verifier, KZG10Verifier {
    function verifyProof(uint[2] calldata _pA, uint[2][2] calldata _pB, uint[2] calldata _pC, uint[{{ groth16_verifier.gamma_abc_len - 1 }}] calldata _pubSignals, uint256[2] calldata c, uint256[2] calldata pi, uint256 x, uint256 y) public view returns (bool) {
        require(super.verifyProof(_pA, _pB, _pC, _pubSignals) == true, "Groth16 verification failed");
        // for now, we do not relate the Groth16 and KZG10 proofs
        // this will done in the future, by computing challenge points from the groth16 proof's data
        require(super.check(c, pi, x, y) == true, "KZG10 verification failed");
        return true;
    }   
}