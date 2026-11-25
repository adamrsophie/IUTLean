# Scripts

The data pipeline that indexes the four papers, merges the hand-reviewed records, reads the
built Lean library, and generates the catalog documents. All Python scripts use the
standard library only, take relative paths from the repository root, and write sorted,
deterministic output: a rerun on the same inputs gives identical files.

None of these scripts is trusted. They locate and count; they do not check mathematics.
Their output is an index for readers, and every number in it can be recomputed from the
inputs. What is trusted is the Lean kernel's check of the library, under the axiom policy
that `scripts/LeanDeclarations.lean` reports on.

## Run everything

    scripts/run_all.sh documentation/ref

`documentation/ref` holds the four PDFs (not tracked). Set `SKIP_LEAN=1` to reuse the last
`data/lean_declarations.json`. The same steps by hand:

    python3 scripts/extract_statements.py documentation/ref
    lake build
    LEAN_DECLARATIONS_OUT=data/lean_declarations.json lake env lean scripts/LeanDeclarations.lean
    python3 scripts/build_graph.py
    python3 scripts/dashboard.py
    python3 scripts/gen_docs.py

Requirements: `pdftotext` and `pdfinfo` (Poppler), Graphviz `dot` for the picture, and the
Lean toolchain of `lean-toolchain`.

## What each script does

`extract_statements.py <pdf-dir>` reads the PDFs with `pdftotext -layout` and writes
`data/source_manifest.json` (file, SHA-256, dates, journal and DOI), `data/statements.json`
(one record per numbered statement and lettered Introduction result: id, kind, number, title,
section, PDF and printed page, end page, external keys cited), `data/dependencies.json`
(citation edges, each marked as found in the statement, in the proof, or, for lettered
results, in the surrounding paragraphs) and `data/references.json` (bibliography keys, their
entries, citation counts per paper). It then merges every `data/curated/*.json` over the
mechanical records. A curated id that the index does not have and that has at least three
components (a part or a proof step such as `IUT3.Cor3_12.StepXI`) becomes a record with a
`parent` field; an unknown id with two components is reported and skipped. Statuses outside
the list of the project brief are reported. Records seen only by the index get the statuses
`NOT_EXTRACTED`. Apart from statement titles, no paper text is written. Invalid JSON in a
curated file stops the run.

Header detection rules worth knowing: a header line is "Kind N.M." or "Kind N.M.K." at the
start of a line, whose first number is the current section; the space after the kind may be
missing or replaced by a control character in the text layer; a header-like line whose
previous line ends with a comma, "of" or "in" is the tail of a citation and is rejected.

`LeanDeclarations.lean` (run with `lake env lean`) lists every constant of the modules
`IUT`, `IUT.*` and `Challenge.Defs`: name, kind, module, whether it is an internal auxiliary,
its axioms (`Lean.collectAxioms`) and the project constants its type and value mention
directly. Output goes to the file named by `LEAN_DECLARATIONS_OUT`, otherwise to standard
output. It sees only the modules that `IUT.lean` imports.

`build_graph.py` combines citation edges, curated edges (parts, results used), the link
from a statement to its Lean declaration, and Lean reference edges (contracted through
internal auxiliaries) into `data/dependency_graph.json`. It computes the critical path
(everything reachable from `IUT4.ThmA` and `IUT4.Cor2_3`), circular citations (strongly
connected components), weakly connected components, statements off the critical path, the
most cited unresolved statements, and the external keys cited on the critical path. It writes
`docs/DEPENDENCY_GRAPH.md`, `docs/CRITICAL_PATH.md` and `docs/dependency_graph.svg`. Citation
edges are mechanical and over-approximate logical dependence.

`dashboard.py` writes `docs/DASHBOARD.md` and `data/dashboard.json`: statement counts,
fidelity and proof statuses reported separately, verified and conditional results,
obligations, ambiguities, external gaps, countermodels, axiom and placeholder checks, coverage
per paper and on the critical path. The definitions of the counts are in its docstring.

`gen_docs.py` writes `docs/SOURCE_MANIFEST.md`, `docs/STATEMENT_CATALOG.md` and
`docs/REFERENCE_INVENTORY.md`.

`run_all.sh` runs the steps above in order.
