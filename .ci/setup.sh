#!/bin/bash

set -e

case "$1" in
  format)
    echo "Installing rustfmt..."
    rustup component add --toolchain nightly rustfmt-preview
    which rustfmt || cargo install --force rustfmt-nightly
    cargo +nightly fmt -- --version
    ;;
esac
