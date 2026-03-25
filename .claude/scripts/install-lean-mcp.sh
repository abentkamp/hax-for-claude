#!/usr/bin/env bash
# Startup script for Claude Code web: installs Lean (via elan) and lean-lsp-mcp
set -euo pipefail

LEAN_PROJECT_PATH="$(cd "$(dirname "$0")/../.." && pwd)/hax-lib/proof-libs/lean"

# Install elan (Lean version manager) if not already installed
if ! command -v elan &>/dev/null && ! command -v lean &>/dev/null; then
  echo "Installing elan (Lean version manager)..."
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
  export PATH="$HOME/.elan/bin:$PATH"
fi

# Ensure elan/lean is on PATH
export PATH="$HOME/.elan/bin:$PATH"

# Install the toolchain specified by the project
if [ -f "$LEAN_PROJECT_PATH/lean-toolchain" ]; then
  TOOLCHAIN=$(cat "$LEAN_PROJECT_PATH/lean-toolchain" | tr -d '[:space:]')
  echo "Installing Lean toolchain: $TOOLCHAIN"
  elan toolchain install "$TOOLCHAIN"
fi

# Install lean-lsp-mcp if not already installed
if ! command -v lean-lsp-mcp &>/dev/null; then
  echo "Installing lean-lsp-mcp..."
  npm install -g lean-lsp-mcp
fi

# Build the Lean project lake dependencies so the LSP is ready
if [ -f "$LEAN_PROJECT_PATH/lakefile.toml" ]; then
  echo "Building lake dependencies in $LEAN_PROJECT_PATH..."
  cd "$LEAN_PROJECT_PATH"
  lake build --no-build
fi

echo "Lean MCP setup complete."
