#!/bin/bash

set -e

case "$1" in
  format)
    cargo +nightly fmt --all -- --check
    ;;
  build)
    cargo build --all
    cargo test --all --all-targets
    ;;
  doc)
    cargo doc --all
    ;;
  *)
    echo "unknown mode" >&2
    exit 1
    ;;
esac
