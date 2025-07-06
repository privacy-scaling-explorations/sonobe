#!/bin/sh

GIT_ROOT=$(pwd)

cd /tmp

# create test project
cargo new foobar
cd foobar

# set rust-toolchain same as "sonobe"
cp "${GIT_ROOT}/rust-toolchain" .

# add wasm32-* targets
rustup target add wasm32-unknown-unknown wasm32-wasip1

# add dependencies
cargo add --path "${GIT_ROOT}/frontends" --features wasm, parallel
cargo add --path "${GIT_ROOT}/folding-schemes" --features parallel
cargo add getrandom --features wasm_js --target wasm32-unknown-unknown

# test build for wasm32-* targets
cargo build --release --target wasm32-unknown-unknown
cargo build --release --target wasm32-wasip1
# Emscripten would require to fetch the `emcc` tooling. Hence we don't build the lib as a dep for it.
# cargo build --release --target wasm32-unknown-emscripten

# delete test project
cd ../
rm -rf foobar
