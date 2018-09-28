#!/bin/bash

if [ "$1" == "format" ]; then
  echo "Installing rustfmt..."
  rustup toolchain install nightly
  rustup component add --toolchain nightly rustfmt-preview
  which rustfmt || cargo install --force rustfmt-nightly
  cargo +nightly fmt -- --version
fi
