#!/bin/bash

case "$1" in
  format)
    cargo +nightly fmt --all -- --check
    ;;
  build)
    cargo build --all
    cargo test --all
    ;;
  doc)
    cargo doc --all
    ;;
esac
