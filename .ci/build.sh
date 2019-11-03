#!/bin/bash

set -e

case "$1" in
  format)
    cargo +nightly fmt --all -- --check
    ;;
  build)
    cargo build --all
    cargo test --all --all-targets
    # https://github.com/rust-lang/cargo/issues/6669
    cargo test --all --doc
    ;;
  doc)
    cargo doc --all
    ;;
  *)
    echo "unknown mode" >&2
    exit 1
    ;;
esac
