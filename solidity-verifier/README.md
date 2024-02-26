# Solidity Verifier
                                    _____  ______  ______  ______  ______  ______  ______ 
                                    | |__| || |__| || |__| || |__| || |__| || |__| || |__| |
                                    |  ()  ||  ()  ||  ()  ||  ()  ||  ()  ||  ()  ||  ()  |
                                    |______||______||______||______||______||______||______|
                                    ______                                          ______ 
                                    | |__| |   ____        _ _     _ _ _            | |__| |
                                    |  ()  |  / ___|  ___ | (_) __| (_) |_ _   _    |  ()  |
                                    |______|  \___ \ / _ \| | |/ _` | | __| | | |   |______|
                                    ______    ___) | (_) | | | (_| | | |_| |_| |    ______ 
                                    | |__| |  |____/ \___/|_|_|\__,_|_|\__|\__, |   | |__| |
                                    |  ()  |  __     __        _  __ _     |___/    |  ()  |
                                    |______|  \ \   / /__ _ __(_)/ _(_) ___ _ __    |______|
                                    ______    \ \ / / _ \ '__| | |_| |/ _ \ '__|    ______ 
                                    | |__| |    \ V /  __/ |  | |  _| |  __/ |      | |__| |
                                    |  ()  |     \_/ \___|_|  |_|_| |_|\___|_|      |  ()  |
                                    |______|                                        |______|
                                    ______  ______  ______  ______  ______  ______  ______ 
                                    | |__| || |__| || |__| || |__| || |__| || |__| || |__| |
                                    |  ()  ||  ()  ||  ()  ||  ()  ||  ()  ||  ()  ||  ()  |
                                    |______||______||______||______||______||______||______|

Welcome to Solidity Verifier, a powerful Command-Line Interface (CLI) tool designed to simplify the generation of Solidity smart contracts that verify proofs of Zero Knowledge cryptographic protocols. This tool is developed by the collaborative efforts of the PSE (Privacy & Scaling Explorations) and 0XPARC teams.

As an open-source project, Solidity Verifier is released under the GPL3 license.

## Supported Protocols

Solidity Verifier currently supports the generation of Solidity smart contracts for the verification of proofs in the following Zero Knowledge protocols:

- **Groth16:**
  - Efficient and succinct zero-knowledge proof system.
  - Template credit: [Jordi Baylina - Groth16 Verifier Template](https://github.com/iden3/snarkjs/blob/master/templates/verifier_groth16.sol.ejs)

- **KZG:**
  - Uses the Kate-Zaverucha-Goldberg polynomial commitment scheme.
  - Example credit: [weijiekoh - KZG10 Verifier Contract](https://github.com/weijiekoh/libkzg/blob/master/sol/KZGVerifier.sol)

- **Nova + CycleFold Decider:**
  - Implements the decider circuit verification for the Nova zero-knowledge proof system in conjunction with the CycleFold protocol optimization.
  - Template inspiration and setup credit: [Han - revm/Solidity Contract Testing Functions](https://github.com/privacy-scaling-explorations/halo2-solidity-verifier/tree/main)

## Usage

```bash
solidity-verifier [OPTIONS] -p <PROTOCOL> -pd <PROTOCOL_DATA> -o <OUTPUT_PATH>
```

### Options:
    -v, --verbose: Increase logging verbosity
    -q, --quiet: Decrease logging verbosity
    -p, --protocol <PROTOCOL>: Selects the protocol for which to generate the Decider circuit Solidity Verifier (possible values: groth16, kzg, nova-cyclefold)
    -o, --out <OUT>: Sets the output path for all generated artifacts (default: /home/kr0/Desktop/HDD/ethereum/folding-schemes/verifier.sol)
    -d, --protocol-data <PROTOCOL_DATA>: Sets the input path for the file containing all the data required by the chosen protocol for verification contract generation
    --pragma <PRAGMA>: Selects the Solidity compiler version to be set in the Solidity Verifier contract artifact
    -h, --help: Print help (see a summary with '-h')
    -V, --version: Print version

## License
Solidity Verifier is released under the GPL3 license for any of the protocols that include `Groth16`. See the LICENSE file in the project repository for more details.

## Contributing
Feel free to explore, use, and contribute to Solidity Verifier as we strive to enhance privacy and scalability in the blockchain space!
We welcome contributions to Solidity Verifier! If you encounter any issues, have feature requests, or want to contribute to the codebase, please check out the GitHub repository and follow the guidelines outlined in the contributing documentation.



