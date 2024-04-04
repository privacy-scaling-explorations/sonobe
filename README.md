# sonobe

Experimental folding schemes library implemented in a joint effort by [0xPARC](https://0xparc.org/) and [PSE](https://pse.dev).

<img align="left" style="width:30%;min-width:250px;" src="https://privacy-scaling-explorations.github.io/sonobe-docs/imgs/sonobe.png">

<br>
<b>Sonobe</b> is a modular library to fold circuit instances in an Incremental Verifiable computation (IVC) style. It features multiple folding schemes and decider setups, allowing users to pick the scheme which best fit their needs. <b>Sonobe</b> also provides a way for developers to generate an EVM-verifiable zkSNARK proof of correct folding. Sonobe is an [arkworks](https://github.com/arkworks-rs) powered library
<br><br>
<i>"The <a href="https://en.wikipedia.org/wiki/Sonobe">Sonobe module</a> is one of the many units used to build modular origami. The popularity of Sonobe modular origami models derives from the simplicity of folding the modules, the sturdy and easy assembly, and the flexibility of the system."</i>

<br><br>

> **Warning**: experimental code, do not use in production.<br>
> The code has not been audited. Several optimizations are also pending. Our focus so far has been on (1) implementing the Nova + CycleFold proving system and (2) achieving onchain (EVM) verification. See the [Schemes implemented]() section for more details.

## Schemes implemented

The following folding schemes have been implemented in Sonobe:

- [Nova: Recursive Zero-Knowledge Arguments from Folding Schemes](https://eprint.iacr.org/2021/370.pdf), Abhiram Kothapalli, Srinath Setty, Ioanna Tzialla. 2021
- [CycleFold: Folding-scheme-based recursive arguments over a cycle of elliptic curves](https://eprint.iacr.org/2023/1192.pdf), Abhiram Kothapalli, Srinath Setty. 2023

Work in progress:

- [HyperNova: Recursive arguments for customizable constraint systems](https://eprint.iacr.org/2023/573.pdf), Abhiram Kothapalli, Srinath Setty. 2023
- [ProtoGalaxy: Efficient ProtoStar-style folding of multiple instances](https://eprint.iacr.org/2023/1106.pdf), Liam Eagen, Ariel Gabizon. 2023

## Available frontends

Available frontends to define the folded circuit:

- [arkworks](https://github.com/arkworks-rs), arkworks contributors
- [Circom](https://github.com/iden3/circom), iden3, 0Kims Association

Planned frontends:

- [noir](https://noir-lang.org/)

## Usage

### Docs
Usage and design documentation can be found at https://privacy-scaling-explorations.github.io/sonobe-docs/

### Folding Schemes introduction

[one or two lines of introductory text here (TODO)]

<img src="https://privacy-scaling-explorations.github.io/sonobe-docs/imgs/folding-main-idea-diagram.png" style="width:70%;" />

### Overview of sonobe

Sonobe is a modular library to fold R1CS instances in an Incremental Verifiable computation (IVC) style. It also provides the tools required to generate a zkSNARK out of an IVC proof and to verify it on Ethereum's EVM.

All users have to do is to: 
1. Design an input circuit
2. Chooses a folding scheme (e.g. Nova)
3. Pick a final decider (e.g. Spartan over Pasta curve).

In fact, which folding scheme and decider is chosen *does not matter*. Indeed, with a few lines of code, users can always change their folding scheme and final decider (e.g. switching from a Spartan proof to an Ethereum smart contract).

![](https://privacy-scaling-explorations.github.io/sonobe-docs/imgs/sonobe-lib-pipeline.png)

Complete examples can be found at [folding-schemes/examples](https://github.com/privacy-scaling-explorations/sonobe/tree/main/folding-schemes/examples)


Check out [Sonobe docs](https://privacy-scaling-explorations.github.io/sonobe-docs/) for more details on usage and design.


## License
https://github.com/privacy-scaling-explorations/sonobe/blob/main/LICENSE

[TODO: add references to
- arkworks
- Espresso code regarding the multilinear 'virtual polynomial' and SumCheck used in HyperNova
- Solidity KZG & Groth16 original adapted code
    - Groth16: Jordi Baylina
    - KZG10: weijiekoh
    - Templating: Han
- People who helped us: Srinath Setty, Lev57, Matej (Lurk), Adrien (Lurk), Wyatt Benno, Nikkolas TODO
]
