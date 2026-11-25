#!/bin/sh
# Regenerate every data file and generated document, in order.
# Usage: scripts/run_all.sh <dir-with-the-four-PDFs>
# Set SKIP_LEAN=1 to keep the existing data/lean_declarations.json instead of rerunning Lean
# (the Lean step needs the library built with `lake build` and takes a few minutes).
set -eu
cd "$(dirname "$0")/.."
python3 scripts/extract_statements.py "${1:?usage: scripts/run_all.sh <pdf-dir>}"
if [ "${SKIP_LEAN:-0}" != 1 ]; then
  LEAN_DECLARATIONS_OUT=data/lean_declarations.json lake env lean scripts/LeanDeclarations.lean
fi
python3 scripts/build_graph.py
python3 scripts/dashboard.py
python3 scripts/gen_docs.py
