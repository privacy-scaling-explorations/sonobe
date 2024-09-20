# sonobe

Experimental folding schemes library implemented jointly by [0xPARC](https://0xparc.org/) and [PSE](https://pse.dev).

<img align="right" style="width:30%;min-width:250px;margin-bottom:20px;" src="https://privacy-scaling-explorations.github.io/sonobe-docs/imgs/sonobe.png">

<b>Sonobe</b> is a modular library to fold arithmetic circuit instances in an Incremental Verifiable computation (IVC) style. It features multiple folding schemes and decider setups, allowing users to pick the scheme which best fits their needs.
<br><br>
Sonobe is conceived as an exploratory effort with the aim to push forward the practical side of folding schemes and advancing towards onchain (EVM) verification.
<br><br>
<i>"The <a href="https://en.wikipedia.org/wiki/Sonobe">Sonobe module</a> is one of the many units used to build modular origami. The popularity of Sonobe modular origami models derives from the simplicity of folding the modules, the sturdy and easy assembly, and the flexibility of the system."</i>

<br>

> **Warning**: experimental code, do not use in production.<br>
> The code has not been audited. Several optimizations are also pending. Our focus so far has been on implementing the Nova and CycleFold schemes and achieving onchain (EVM) verification.

## Schemes implemented

Folding schemes implemented:

- [Nova: Recursive Zero-Knowledge Arguments from Folding Schemes](https://eprint.iacr.org/2021/370.pdf), Abhiram Kothapalli, Srinath Setty, Ioanna Tzialla. 2021
- [CycleFold: Folding-scheme-based recursive arguments over a cycle of elliptic curves](https://eprint.iacr.org/2023/1192.pdf), Abhiram Kothapalli, Srinath Setty. 2023
- [HyperNova: Recursive arguments for customizable constraint systems](https://eprint.iacr.org/2023/573.pdf), Abhiram Kothapalli, Srinath Setty. 2023

Work in progress:

- [ProtoGalaxy: Efficient ProtoStar-style folding of multiple instances](https://eprint.iacr.org/2023/1106.pdf), Liam Eagen, Ariel Gabizon. 2023

## Available frontends

Available frontends to define the folded circuit:

- [arkworks](https://github.com/arkworks-rs), arkworks contributors
- [Circom](https://github.com/iden3/circom), iden3, 0Kims Association
- [Noname](https://github.com/zksecurity/noname), zkSecurity
- [Noir](https://github.com/noir-lang/noir), Aztec

## Usage

### Build & test
You can test the library for both, WASM-targets and regular ones.
#### Regular targets
Tier-S targets allow the user to simply run `cargo test` or `cargo build` without needing to worry about anything.
**We strongly recommend to test using the `light-test` feature.** Which will omit the computationally intensive parts of the tests such as
generating a SNARK of 4~5M constraints to then verify it.

#### WASM targets
In order to build the lib for WASM-targets, use the following command:
`cargo build -p folding-schemes --no-default-features --target wasm32-unknown-unknown --features "wasm, parallel"`.
Where the target can be any WASM one and the `parallel` feature is optional.

**Trying to build for a WASM-target without the `wasm` feature or viceversa will end up in a compilation error.**

### Docs

Detailed usage and design documentation can be found at [Sonobe docs](https://privacy-scaling-explorations.github.io/sonobe-docs/).

### WASM-compatibility & features

The `sonobe/folding-schemes` crate is the only workspace member that supports WASM-target compilation. But, to have it working, `getrandom/js` needs
to be imported in the `Cargo.toml` of the crate that uses it as dependency.
```toml
[dependencies]
folding-schemes = { version = "0.1.0", default-features = false, features = ["parallel", "wasm"] }
getrandom = { version = "0.2", features = ["js"] }
```
See more details about `getrandom` here: https://docs.rs/getrandom/latest/getrandom/#webassembly-support.

Also, notice that:
- `wasm` feature **IS MANDATORY** if compilation to WASM targets is desired.
- `parallel` feature enables some parallelization optimizations available in the crate.
- `light-test` feature runs the computationally-intensive parts of the testing such as the full proof generation for the Eth-decider circuit
of Nova which is approximately 4-5M constraints. **This feature only matters when it comes to running Sonobe's tests.**

### Folding Schemes introduction

Folding schemes efficiently achieve incrementally verifiable computation (IVC), where the prover recursively proves the correct execution of the incremental computations.
Once the IVC iterations are completed, the IVC proof is compressed into the Decider proof, a zkSNARK proof which proves that applying $n$ times the $F$ function (the circuit being folded) to the initial state ($z_0$) results in the final state ($z_n$).


<p align="center">
    <img src="https://privacy-scaling-explorations.github.io/sonobe-docs/imgs/folding-main-idea-diagram.png" style="width:70%;" />
</p>

Where $w_i$ are the external witnesses used at each iterative step.

In other words, it allows to prove efficiently that $z_n = F(...~F(F(F(F(z_0, w_0), w_1), w_2), ...), w_{n-1})$.


### Overview of sonobe

Sonobe is a folding schemes modular library to fold arithmetic circuit instances in an incremental verifiable computation (IVC) style. It also provides the tools required to generate a zkSNARK proof out of an IVC proof and to verify it on Ethereum's EVM.

The development flow using Sonobe looks like:

1. Define a circuit to be folded
2. Set which folding scheme to be used (eg. Nova with CycleFold)
3. Set a final decider to generate the final proof (eg. Spartan over Pasta curves)
4. Generate the decider verifier

<p align="center">
    <img src="https://privacy-scaling-explorations.github.io/sonobe-docs/imgs/sonobe-lib-pipeline.png"/>
</p>

The folding scheme and decider used can be swapped with a few lines of code (eg. switching from a Decider that uses two Spartan proofs over a cycle of curves, to a Decider that uses a single Groth16 proof over the BN254 to be verified in an Ethereum smart contract).

The [Sonobe docs](https://privacy-scaling-explorations.github.io/sonobe-docs/) contain more details about the usage and design of the library.

Complete examples can be found at [folding-schemes/examples](https://github.com/privacy-scaling-explorations/sonobe/tree/main/examples)

## License

Sonobe is [MIT Licensed](https://github.com/privacy-scaling-explorations/sonobe/blob/main/LICENSE).

## Acknowledgments

This project builds on top of multiple [arkworks](https://github.com/arkworks-rs) libraries. It uses Espresso system's [virtual polynomial](https://github.com/EspressoSystems/hyperplonk/blob/main/arithmetic/src/virtual_polynomial.rs) abstraction and its [SumCheck](https://github.com/EspressoSystems/hyperplonk/tree/main/subroutines/src/poly_iop/sum_check) implementation.

The Solidity templates used in `nova_cyclefold_verifier.sol`, use [iden3](https://github.com/iden3/snarkjs/blob/master/templates/verifier_groth16.sol.ejs)'s Groth16 implementation and a KZG10 Solidity template adapted from [weijiekoh/libkzg](https://github.com/weijiekoh/libkzg).

In addition to the direct code contributors who make this repository possible, this project has been made possible by many conversations with [Srinath Setty](https://github.com/srinathsetty), [Lev Soukhanov](https://github.com/levs57), [Matej Penciak](https://github.com/mpenciak), [Adrian Hamelink](https://github.com/adr1anh), [François Garillot](https://github.com/huitseeker), [Daniel Marin](https://github.com/danielmarinq), [Han Jian](https://github.com/han0110), [Wyatt Benno](https://github.com/wyattbenno777), [Nikkolas Gailly](https://github.com/nikkolasg) and [Nalin Bhardwaj](https://github.com/nalinbhardwaj), to whom we are grateful.
