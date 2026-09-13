#!/usr/bin/env bash
# Build the Jurix_Implicit_Disagreement session and its AFP-style document.
#
# Usage:            ./build.sh
# Custom Isabelle:  ISABELLE=/path/to/isabelle ./build.sh
#
# The first run also builds the parent session AA_Fixed (a few minutes).
# The generated document is written to output/document.pdf.

set -euo pipefail
cd "$(dirname "$0")"

if [ -z "${ISABELLE:-}" ]; then
  if command -v isabelle >/dev/null 2>&1; then
    ISABELLE=isabelle
  else
    # Fall back to a local Isabelle2025* app bundle (macOS).
    ISABELLE=$(ls -d /Applications/Isabelle2025*.app/bin/isabelle 2>/dev/null | sort | tail -n 1 || true)
    if [ -z "$ISABELLE" ]; then
      echo "error: no 'isabelle' on PATH and no /Applications/Isabelle2025*.app found." >&2
      echo "       Set ISABELLE=/path/to/isabelle and re-run." >&2
      exit 1
    fi
  fi
fi

"$ISABELLE" build -o timeout_scale=3 -d . -d AA_Fixed Jurix_Implicit_Disagreement

echo
echo "OK. Document: $(pwd)/output/document.pdf"
