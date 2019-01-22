#!/bin/bash

case "$1" in
  format)
    echo "Installing rustfmt..."
    rustup component add --toolchain nightly rustfmt-preview
    which rustfmt || cargo install --force rustfmt-nightly
    cargo +nightly fmt -- --version
    ;;
  clippy)
    echo "Installing clippy..."
    rustup component add clippy || cargo install --git https://github.com/rust-lang/rust-clippy/ --force clippy
    ;;
esac
