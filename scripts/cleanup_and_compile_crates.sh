set -e

cd ~/eth/curr-sem/sem-project/v2-qrates/qrates
rm -rf ../workspace/rust-corpus/*
cargo build --release --all
cargo run --release -- compile
