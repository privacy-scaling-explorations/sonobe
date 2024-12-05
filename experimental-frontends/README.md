# experimental-frontends

This crate contains *experimental frontends* for Sonobe.
The recommended frontend is to directly use [arkworks](https://github.com/arkworks-rs) to define the FCircuit, just following the [`FCircuit` trait](https://github.com/privacy-scaling-explorations/sonobe/blob/main/folding-schemes/src/frontend/mod.rs).

> Warning: the following frontends are experimental and some computational and time overhead is expected when using them compared to directly using the [arkworks frontend](https://github.com/privacy-scaling-explorations/sonobe/blob/main/folding-schemes/src/frontend/mod.rs).

Available experimental frontends:
- [Circom](https://github.com/iden3/circom), iden3, 0Kims Association. Supported version`<=v2.1.9`.
- [Noir](https://github.com/noir-lang/noir), Aztec.
- [Noname](https://github.com/zksecurity/noname), zkSecurity. Partially supported.


Documentation about frontend interface and experimental frontends: https://privacy-scaling-explorations.github.io/sonobe-docs/usage/frontend.html

## Implementing new frontends
Support for new frontends can be added (even from outside this repo) by implementing the [`FCircuit` trait](https://github.com/privacy-scaling-explorations/sonobe/blob/main/folding-schemes/src/frontend/mod.rs).
