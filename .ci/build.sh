#!/bin/bash

if ${FORMATTING:-false}; then
  cargo +nightly fmt --all -- --check
else
  cargo build --all
  cargo test --all
fi
