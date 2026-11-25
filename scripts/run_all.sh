#!/bin/sh
# Regenerate every data file and generated document, in order.
#
# Usage: scripts/run_all.sh                 (every stage that needs no PDF)
#        scripts/run_all.sh --pdfs <dir>    (first the PDF stage, then the others)
#
# The PDF stage (extract_statements.py index) checks the SHA-256 of the four PDFs against
# data/source_manifest.json and writes data/source_manifest.json, data/mechanical_index.json,
# data/dependencies.json and data/references.json. The PDFs are not redistributed (see
# scripts/README.md), so the continuous integration treats those four files as inputs and runs
# the other stages only.
#
# Fails (nonzero exit status) if Graphviz dot is missing, if the library is not built or not up
# to date (lake build --no-build), if a step fails, or if a record is invalid. The Lean
# inventory is always regenerated; there is no switch to reuse an old one. After a failed
# record check the remaining steps still run, so that the generated documents show the
# errors, and the script then exits with status 1.
set -u
cd "$(dirname "$0")/.." || exit 2

if [ $# -eq 2 ] && [ "$1" = --pdfs ]; then
  python3 scripts/extract_statements.py index "$2" || exit 1
elif [ $# -ne 0 ]; then
  echo "usage: scripts/run_all.sh [--pdfs <dir-with-the-four-PDFs>]"
  exit 2
fi
command -v dot > /dev/null || { echo "run_all: Graphviz dot is required"; exit 1; }
lake build --no-build IUT Solution > /dev/null 2>&1 ||
  { echo "run_all: the library is not built or not up to date; run lake build first"; exit 1; }
LEAN_DECLARATIONS_OUT=data/lean_declarations.json lake env lean scripts/LeanDeclarations.lean ||
  { echo "run_all: the Lean inventory failed"; exit 1; }

failed=0
for step in "extract_statements.py merge" build_graph.py dashboard.py gen_docs.py; do
  # shellcheck disable=SC2086
  python3 scripts/$step || { echo "run_all: scripts/$step failed"; failed=1; }
done
if [ "$failed" -ne 0 ]; then
  echo "run_all FAILED"
  exit 1
fi
echo "run_all OK"
