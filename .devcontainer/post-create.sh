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
