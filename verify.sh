#!/bin/bash
set -e

CACHE_FILE="target/.builtin-path"

# Reuse cached path if valid
if [[ -f "$CACHE_FILE" && -s "$CACHE_FILE" ]]; then
  builtin_path=$(cat "$CACHE_FILE")
  if [[ -f "$builtin_path" ]]; then
    echo "✅ Reusing builtin: $builtin_path"
    env RUSTFLAGS="--extern builtin=$builtin_path" cargo-verus verify "$@"
    exit $?
  fi
fi

echo "🔍 Probing build to discover builtin .rmeta..."
BUILD_LOG=$(mktemp)
cargo-verus build -vv 2>&1 | tee "$BUILD_LOG"

builtin_path=$(grep -oE -- '--extern builtin=[^ ]+' "$BUILD_LOG" | tail -n 1 | cut -d= -f2)

if [[ -z "$builtin_path" || ! -f "$builtin_path" ]]; then
  echo "❌ Could not locate builtin .rmeta in build output"
  exit 1
fi

# Store in target/.builtin-path for future reuse
mkdir -p target
echo "$builtin_path" > "$CACHE_FILE"

echo "✅ Found and cached builtin: $builtin_path"
env RUSTFLAGS="--extern builtin=$builtin_path" cargo-verus verify "$@"
