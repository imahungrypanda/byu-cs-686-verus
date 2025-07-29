#!/bin/bash
set -euo pipefail

echo "🧹 Running verusfmt on staged Rust files..."

# Get staged .rs files (excluding deleted/renamed)
STAGED_RS_FILES=$(git diff --cached --name-only --diff-filter=ACM | grep '\.rs$' || true)

EXIT_CODE=0

for file in $STAGED_RS_FILES; do
  if [[ -f "$file" ]]; then
    verusfmt "$file"

    # If verusfmt modified the file, exit non-zero
    if ! git diff --quiet "$file"; then
      echo "🔧 Reformatted: $file"
      EXIT_CODE=1
    fi
  fi
done

if [[ $EXIT_CODE -ne 0 ]]; then
  echo "✋ One or more files were reformatted. Please review and git add them."
fi

exit $EXIT_CODE
