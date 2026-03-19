#!/usr/bin/env bash

set -eu

LEAN_TOOLCHAIN_FILE="proof-libs/lean/lean-toolchain"

# Install elan (Lean version manager) if not already installed
if ! command -v elan >/dev/null 2>&1; then
    curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
        | sh -s -- -y --default-toolchain none
fi

export PATH="$HOME/.elan/bin:$PATH"

# Install the Lean toolchain specified in proof-libs/lean/lean-toolchain
TOOLCHAIN="$(cat "$LEAN_TOOLCHAIN_FILE")"
elan toolchain install "$TOOLCHAIN"
