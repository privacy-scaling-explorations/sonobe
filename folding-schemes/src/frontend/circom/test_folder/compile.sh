#!/bin/bash
circom ./folding-schemes/src/frontend/circom/test_folder/cubic_circuit.circom --r1cs --sym --wasm --prime bn128 --output ./folding-schemes/src/frontend/circom/test_folder/
circom ./folding-schemes/src/frontend/circom/test_folder/with_external_inputs.circom --r1cs --sym --wasm --prime bn128 --output ./folding-schemes/src/frontend/circom/test_folder/
circom ./folding-schemes/src/frontend/circom/test_folder/no_external_inputs.circom --r1cs --sym --wasm --prime bn128 --output ./folding-schemes/src/frontend/circom/test_folder/
