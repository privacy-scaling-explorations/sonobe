pragma solidity ^0.8.4;

{{ groth16_verifier }}

{{ kzg10_verifier }}

/**
 * @author  PSE & 0xPARC
 * @title   NovaDecider contract, for verifying zk-snarks Nova IVC proofs.
 * @dev     This is an askama template. It will feature a snarkjs groth16 and a kzg10 verifier, from which this contract inherits.
 */
contract NovaDecider is Groth16Verifier, KZG10Verifier {
    function verifyProof(uint[2] calldata _pA, uint[2][2] calldata _pB, uint[2] calldata _pC, uint[{{ gamma_abc_len - 1 }}] calldata _pubSignals, uint256[2] calldata c, uint256[2] calldata pi, uint256 x, uint256 y) public view returns (bool) {
        require(super.verifyProof(_pA, _pB, _pC, _pubSignals) == true, "Groth16 verification failed");
        require(super.check(c, pi, x, y) == true, "KZG10 verification failed");
        return true;
    }   
}