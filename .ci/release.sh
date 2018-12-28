#!/bin/bash
set -eu
set -o pipefail
(cd starlark && cargo package && cargo publish)
(cd starlark-repl && cargo package && cargo publish)
