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
> The code has not been audited. Several optimizations are also pending. Our focus so far has been on implementing the Nova, HyperNova and ProtoGalaxy schemes, all with the CycleFold approach; and achieving the onchain (in EVM) verification of the folding proofs.


## Schemes implemented

Folding schemes implemented:

- [Nova: Recursive Zero-Knowledge Arguments from Folding Schemes](https://eprint.iacr.org/2021/370.pdf), Abhiram Kothapalli, Srinath Setty, Ioanna Tzialla. 2021
- [CycleFold: Folding-scheme-based recursive arguments over a cycle of elliptic curves](https://eprint.iacr.org/2023/1192.pdf), Abhiram Kothapalli, Srinath Setty. 2023
- [HyperNova: Recursive arguments for customizable constraint systems](https://eprint.iacr.org/2023/573.pdf), Abhiram Kothapalli, Srinath Setty. 2023
- [ProtoGalaxy: Efficient ProtoStar-style folding of multiple instances](https://eprint.iacr.org/2023/1106.pdf), Liam Eagen, Ariel Gabizon. 2023


## Frontends

Frontends allow to define the circuit to be folded (ie. `FCircuit`).
The recommended frontend is directly implementing the [`FCircuit` trait](https://github.com/privacy-scaling-explorations/sonobe/blob/main/folding-schemes/src/frontend/mod.rs#L16) with the Arkworks constraint system.

Alternatively, experimental frontends for [Circom](https://github.com/iden3/circom), [Noir](https://github.com/noir-lang/noir) and [Noname](https://github.com/zksecurity/noname) can be found at the [sonobe/experimental-frontends](https://github.com/privacy-scaling-explorations/sonobe/tree/main/experimental-frontends) directory, which have some computational (and time) overhead.

More details about the frontend interface and the experimental frontends can be found at the [sonobe-docs/frontend](https://privacy-scaling-explorations.github.io/sonobe-docs/usage/frontend.html) page.


## Usage
Import the library:
```toml
[dependencies]
folding-schemes = { git = "https://github.com/privacy-scaling-explorations/sonobe", package = "folding-schemes"}
```

Available packages:
- `folding-schemes`: main crate, contains the different scheme implementations, together with commitment schemes, frontend trait, arithmetization, transcript, etc.
- `solidity-verifiers`: contains the templating logic to output the verifier contracts for the DeciderEth proofs. Currently only supports Nova+CycleFold DeciderEth proofs.
- `experimental-frontends`: contains the experimental frontends other than the arkworks frontend. More details at the [sonobe/experimental-frontends](https://github.com/privacy-scaling-explorations/sonobe/tree/main/experimental-frontends) directory.

Available features:
- `parallel` enables some parallelization optimizations available in the crate. It is enabled by default.
- `light-test` disables part of the DeciderEthCircuit various circuits (which accounts for ~9M constraints) so that the tests involving those circuits can run faster. Do not use it outside tests. This feature is disabled by default.

Examples of usage can be found at the [examples](https://github.com/privacy-scaling-explorations/sonobe/tree/main/examples) directory.

For WASM (in browser usage), details can be found at [sonobe-docs/usage/wasm](https://privacy-scaling-explorations.github.io/sonobe-docs/usage/wasm.html).


### Docs
Details on usage of the library, together with design documentation, can be found at the [Sonobe docs](https://privacy-scaling-explorations.github.io/sonobe-docs/).

## Folding Schemes introduction

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

This project builds on top of multiple [arkworks](https://github.com/arkworks-rs) libraries. It uses Espresso System's [virtual polynomial](https://github.com/EspressoSystems/hyperplonk/blob/main/arithmetic/src/virtual_polynomial.rs) abstraction and its [SumCheck](https://github.com/EspressoSystems/hyperplonk/tree/main/subroutines/src/poly_iop/sum_check) implementation.

The Solidity templates used in `nova_cyclefold_verifier.sol`, use [iden3](https://github.com/iden3/snarkjs/blob/master/templates/verifier_groth16.sol.ejs)'s Groth16 implementation and a KZG10 Solidity template adapted from [weijiekoh/libkzg](https://github.com/weijiekoh/libkzg).

In addition to the direct code contributors who make this repository possible, this project has been made possible by many conversations with [Srinath Setty](https://github.com/srinathsetty), [Lev Soukhanov](https://github.com/levs57), [Matej Penciak](https://github.com/mpenciak), [Adrian Hamelink](https://github.com/adr1anh), [François Garillot](https://github.com/huitseeker), [Daniel Marin](https://github.com/danielmarinq), [Han Jian](https://github.com/han0110), [Wyatt Benno](https://github.com/wyattbenno777), [Nikkolas Gailly](https://github.com/nikkolasg) and [Nalin Bhardwaj](https://github.com/nalinbhardwaj), to whom we are grateful.
