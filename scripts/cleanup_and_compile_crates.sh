set -e

cd ~/eth/curr-sem/sem-project/v2-qrates/qrates
rm -rf ../workspace/rust-corpus/*
cargo run --release -- compile
