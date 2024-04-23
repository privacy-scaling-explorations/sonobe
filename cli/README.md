# Solidity Verifiers CLI

Solidity Verifiers CLI is a Command-Line Interface (CLI) tool to generate the Solidity smart contracts that verify proofs of Zero Knowledge cryptographic protocols. This tool is developed by the collaborative efforts of the PSE (Privacy & Scaling Explorations) and 0xPARC teams.

Solidity Verifiers CLI is released under the MIT license, but notice that the Solidity template for the Groth16 verification has GPL-3.0 license, hence the generated Solidity verifiers that use the Groth16 template will have that license too.

## Supported Protocols

Solidity Verifier currently supports the generation of Solidity smart contracts for the verification of proofs in the following Zero Knowledge protocols:

- **Groth16:**
  - Efficient and succinct zero-knowledge proof system.
  - Template credit: [Jordi Baylina - Groth16 Verifier Template](https://github.com/iden3/snarkjs/blob/master/templates/verifier_groth16.sol.ejs)

- **KZG:**
  - Uses the Kate-Zaverucha-Goldberg polynomial commitment scheme.
  - Template credit: [weijiekoh - KZG10 Verifier Contract](https://github.com/weijiekoh/libkzg/blob/master/sol/KZGVerifier.sol)

- **Nova + CycleFold Decider:**
  - Implements the decider circuit verification for the Nova proof system in conjunction with the CycleFold protocol optimization.
  - Template inspiration and setup credit: [Han - revm/Solidity Contract Testing Functions](https://github.com/privacy-scaling-explorations/halo2-solidity-verifier/tree/main)

## Usage

```bash
solidity-verifiers-cli [OPTIONS] -p <PROTOCOL> -k <PROTOCOL_VK> -o <OUTPUT_PATH>
```

A real use case (which was used to test the tool itself):
`solidity-verifiers-cli -p groth16 -k ./solidity-verifiers/assets/G16_test_vk`
This would generate a Groth16 verifier contract for the given G16 verifier key (which consists on the G16_Vk only) and store this contract in `$pwd`.

### Options:
    -v, --verbose: Increase logging verbosity
    -q, --quiet: Decrease logging verbosity
    -p, --protocol <PROTOCOL>: Selects the protocol for which to generate the Decider circuit Solidity Verifier (possible values: groth16, kzg, nova-cyclefold)
    -o, --out <OUT>: Sets the output path for all generated artifacts
    -k, --protocol-vk <PROTOCOL_VK>: Sets the input path for the file containing the verifier key required by the protocol chosen such that the verification contract can be generated.
    --pragma <PRAGMA>: Selects the Solidity compiler version to be set in the Solidity Verifier contract artifact
    -h, --help: Print help (see a summary with '-h')
    -V, --version: Print version

## License
Solidity Verifier CLI is released under the MIT license, but notice that the Solidity template for the Groth16 verification has GPL-3.0 license, hence the generated Solidity verifiers will have that license too.

## Contributing
Feel free to explore, use, and contribute to Solidity Verifiers CLI as we strive to enhance privacy and scalability in the blockchain space!
We welcome contributions to Solidity Verifiers CLI! If you encounter any issues, have feature requests, or want to contribute to the codebase, please check out the GitHub repository and follow the guidelines outlined in the contributing documentation.
