#!/bin/bash

case "$1" in
  format)
    cargo +nightly fmt --all -- --check
    ;;
  build)
    cargo build --all
    cargo test --all
    (cd starlark && cargo test --all --features=linked_hash_set)
    ;;
  doc)
    cargo doc --all
    ;;
  clippy)
    cargo clippy --all-targets --all-features -- -D warnings
    ;;
esac
