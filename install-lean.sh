#!/usr/bin/env bash

set -eu

LEAN_TOOLCHAIN="leanprover/lean4:v4.29.0-rc1"

# Install elan (Lean version manager) if not already installed
if ! command -v elan >/dev/null 2>&1; then
    curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
        | sh -s -- -y --default-toolchain none
fi

export PATH="$HOME/.elan/bin:$PATH"

elan toolchain install "$LEAN_TOOLCHAIN"
