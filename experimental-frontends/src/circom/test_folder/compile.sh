#!/bin/bash
circom ./experimental-frontends/src/circom/test_folder/cubic_circuit.circom --r1cs --sym --wasm --prime bn128 --output ./experimental-frontends/src/circom/test_folder/
circom ./experimental-frontends/src/circom/test_folder/with_external_inputs.circom --r1cs --sym --wasm --prime bn128 --output ./experimental-frontends/src/circom/test_folder/
circom ./experimental-frontends/src/circom/test_folder/no_external_inputs.circom --r1cs --sym --wasm --prime bn128 --output ./experimental-frontends/src/circom/test_folder/
