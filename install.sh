#!/bin/bash

set -e

# Format the whole workspace (rapx + rapx/macros).
cargo fmt -q

# Install the rapx and cargo-rapx binaries.
cargo install --path rapx

cargo rapx -help
