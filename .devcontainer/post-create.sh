#!/bin/bash
set -euxo pipefail

# Find the .vsix file in the dist directory
VSIX_PATH=$(find /home/vscode/verus-analyzer/dist -maxdepth 1 -name "verus-analyzer-*.vsix" | head -n 1)

if [[ -f "$VSIX_PATH" ]]; then
  echo "📦 Installing Verus Analyzer from: $VSIX_PATH"
  code --install-extension "$VSIX_PATH"
else
  echo "❌ VSIX file not found at expected path: $VSIX_PATH"
  exit 1
fi

# Install pre-commit Git hook if config is present
PROJECT_DIR="/workspaces/byu-cs-686-verus"
cd "$PROJECT_DIR"

if [[ -f ".pre-commit-config.yaml" ]]; then
  echo "🔧 Installing pre-commit Git hook..."
  pre-commit install
else
  echo "⚠️  Skipping pre-commit install: .pre-commit-config.yaml not found in $PROJECT_DIR"
fi
