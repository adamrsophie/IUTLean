# Scripts

The data pipeline that indexes the four papers, merges the hand-reviewed records, reads the
built Lean library, and generates the catalog documents; and, in `Controls/`, the checks of
the trust boundary. All Python scripts use the standard library only, take relative paths
from the repository root, and write sorted, deterministic output: a rerun on the same inputs
gives identical files.

None of these scripts is trusted. They locate, count and compare; they do not check
mathematics. Their output is an index for readers, and every number in it can be recomputed
from the inputs. What is trusted is the Lean kernel's check of the library, under the axiom
policy that `AxiomGate.lean` enforces.

## Run everything

    lake build
    scripts/run_all.sh                          # every stage that needs no PDF
    scripts/run_all.sh --pdfs <pdf-dir>         # the PDF stage first, then the others

`run_all.sh` fails (nonzero exit status) if Graphviz `dot` is missing, if the library is not
built or not up to date (`lake build --no-build IUT Solution`), if a step fails, or if a
record is invalid. It always regenerates the Lean inventory. The same steps by hand:

    python3 scripts/extract_statements.py index <pdf-dir>   # needs the PDFs
    LEAN_DECLARATIONS_OUT=data/lean_declarations.json lake env lean scripts/LeanDeclarations.lean
    python3 scripts/extract_statements.py merge
    python3 scripts/build_graph.py
    python3 scripts/dashboard.py
    python3 scripts/gen_docs.py

`<pdf-dir>` is a folder holding the four manuscripts with the SHA-256 values of
`data/source_manifest.json` (see below).

Requirements: `pdftotext` and `pdfinfo` (Poppler) for the PDF stage only, Graphviz `dot`,
and the Lean toolchain of `lean-toolchain`.

## The PDFs

The PDFs are not redistributed here. They are the author's manuscripts, listed on the
author's page of papers, <https://www.kurims.kyoto-u.ac.jp/~motizuki/papers-english.html>,
under the file names of `data/source_manifest.json` (`Inter-universal Teichmuller Theory
I.pdf` to `IV.pdf`). The journal editions that the DOIs of the manifest resolve to are
paginated differently and are not the files indexed here. The PDF stage starts by comparing
the SHA-256 of each file with `data/source_manifest.json` and stops on a difference; the
author updates the manuscripts from time to time, and a different edition must be recorded
deliberately with `--new-sources`, after which every page reference of the curated records
needs checking.

## Continuous integration

The workflow `.github/workflows/axiom-gate.yml` runs, besides the Lean checks, the stages
that need no PDF (`scripts/run_all.sh`) and then fails if `git diff --exit-code -- data docs`
shows a change or if an untracked file appears there. The outputs of the PDF stage
(`data/source_manifest.json`, `data/mechanical_index.json`, `data/dependencies.json`,
`data/references.json`) are inputs there, so a change to them has to come from a local run
with the PDFs. `data/statements.json` is regenerated from `data/mechanical_index.json` and
`data/curated/*.json`, so it cannot fall behind the curated records. The picture
`docs/dependency_graph.svg` is regenerated but not compared, because its bytes depend on the
Graphviz version.

No second, independent kernel is configured. `lake check` and `lake comparator` replay the
exported declarations through the kernel of the pinned toolchain; no independent checker for
this toolchain is installed as a package of this project, and adding one would add a
dependency.

## What each script does

`extract_statements.py index <pdf-dir> [--new-sources]` checks the hashes (see above), reads
the PDFs with `pdftotext -layout` and writes `data/source_manifest.json` (file, SHA-256,
dates, journal and DOI), `data/mechanical_index.json` (one mechanical record per numbered
statement and lettered Introduction result: id, kind, number, title, section, PDF and printed
page, end page, external keys cited), `data/dependencies.json` (citation edges, each marked as
found in the statement, in the proof, or, for lettered results, in the surrounding
paragraphs) and `data/references.json` (bibliography keys, their entries, citation counts per
paper). A citation that follows a bibliography key of another work, possibly with a locator
in between ("[Silv], Chapter VII, Proposition 5.4"), is a citation of that work and gives no
edge. Apart from statement titles, no paper text is written.

`extract_statements.py merge` needs no PDF. It starts from the mechanical records, merges
every `data/curated/*.json` over them and writes `data/statements.json`. A curated id that
the index does not have is a part or proof step (`IUT3.Cor3_12.StepXI`, parent: the id
without its last component), a fragment (`IUT4.Cor2_2.iii.frag.h_lt`, parent: its `parent`
field) or an unnumbered item of a section (`IUT1.Sec0.PolyMorphism`, no parent, `kind` and
pages from the curated record); any other unknown id is an error. When a curated record
gives its pages (`source.pages`, else `source.pdf_pages`), they become `pdf_page` and
`pdf_page_end`, and the mechanical span (header to next recognized header) is kept in
`extraction_window`. Records seen only by the index get the statuses `NOT_EXTRACTED`. The
merge then validates the records and exits nonzero on an error.

`records.py` holds the rules shared by the other scripts. The fragment rule: a statement
record may have a status of the formalized family (`STATEMENT_FORMALIZED`,
`STATEMENT_REVIEWED`) or of the verified family (`CONDITIONALLY_VERIFIED`, `KERNEL_VERIFIED`,
`INDEPENDENTLY_CHECKED`) only with a `lean_declaration` that states its entire content; a
Lean lemma that checks a piece is a separate record of kind `fragment` (with `parent`,
`covers`, `not_covered`, `lean_declaration`), listed in the parent's `fragments`, and a
parent never counts as formalized or verified through it. Errors: an unknown status, a
`parent` that is not a record, a formalized or verified status on a non-fragment record
without a declaration, a malformed fragment, an `EXTRACTED` record without content,
hypotheses and conclusion, and (where the inventory is read) a `lean_declaration`, or any
qualified name `IUT.*`, `Challenge.*`, `Solution.*` in a hand-written file of `data/`
(curated records, `dispute_map.json`, `countermodels.json`, `external_projects.json`,
`prerequisites.json`), that is not a declaration or module of `data/lean_declarations.json`.

`LeanDeclarations.lean` (run with `lake env lean`) lists every constant of the modules
`IUT`, `IUT.*`, `Challenge.Defs` and `Solution`: name, kind, module, whether it is an
internal auxiliary, its axioms (`Lean.collectAxioms`), the project constants its type and
value mention directly (`refs`), and the theorems of Mathlib and the other dependencies they
mention directly (`external_theorems`). Output goes to the file named by
`LEAN_DECLARATIONS_OUT`, otherwise to standard output. It sees only the modules that
`IUT.lean` imports, and `Challenge.Defs` and `Solution`.

`build_graph.py` builds `data/dependency_graph.json` with typed nodes (statement, fragment,
unresolved citation, external reference, Lean declaration, external Lean theorem) and typed
edges (`cites_in_statement`, `cites_in_proof`, `cites_in_context`, `part_of`, `fragment_of`,
`depends_on` from `results_used`, `depends_on_external` from `external_dependencies`,
`formalized_by`, `lean_uses`). Every edge ends at a node; the script exits nonzero otherwise,
and also when Graphviz fails. It computes the critical path (everything reachable from
`IUT4.ThmA` and `IUT4.Cor2_3`), circular citations, weakly connected components of the
statement records (unresolved targets and fragments left out), the most cited unresolved
statements and the external keys cited on the critical path, and writes
`docs/DEPENDENCY_GRAPH.md`, `docs/CRITICAL_PATH.md` and `docs/dependency_graph.svg`. Citation
edges are mechanical and both over- and under-approximate logical dependence.

`dashboard.py` writes `docs/DASHBOARD.md` and `data/dashboard.json`: statements formalized in
full, proved in full (unconditional, conditional), fragments checked in Lean (unconditional,
conditional) with their parents, model tests (fragments with `"scope": "model_test"`, counted
apart), obligation entries, the countermodel catalog of
`data/countermodels.json` by kind, axiom and placeholder checks, coverage per paper and on the
critical path, and the validation errors. The status tables and the status totals of
`data/dashboard.json` are split by kind of record (full statements, parts and steps,
fragments); no table adds fragments to statements. The definitions of the counts are in its
docstring. It exits nonzero on a validation error.

`records.py` holds the rules shared by these scripts: the page parser (spans per paper,
`[paper, first, last]`, stored as `page_spans` in `data/statements.json`; a page text of
another form is a validation error), the fragment id rule `<parent>.frag.<name>`, the value
`model_test` of `scope`, the axiom rule for records of the proved family, and the rules for
statements of other papers (`EXTERNAL_PAPERS`: the registry of id prefixes `EXPL`, `ZHOU1`,
`ZHOU2`, `DH` and the paper each stands for; records in `data/curated/external.json`, kind
`external_statement` or `fragment`, pages in `source.pages_in_paper`, proof status
`EXTERNAL_CLAIM` for a statement that a Lean `def ... : Prop` states). The dashboard and the
catalog report these records in a section of their own and never count them for IUT I to IV.
`python3 -I scripts/records.py` runs its self-test; the continuous integration runs it after
the regeneration.

`gen_docs.py` writes `docs/SOURCE_MANIFEST.md`, `docs/STATEMENT_CATALOG.md` and
`docs/REFERENCE_INVENTORY.md`, and exits nonzero on an invalid record.

## Controls of the trust boundary (`Controls/`)

`Controls/source_scan.py` is the lexical scan of the proof sources (see its header):
placeholders including `sorryAx` in any spelling (`_root_.sorryAx`, `«sorryAx»`), trust escapes
and native evaluation (`native_decide`, `decide +native`, `Lean.ofReduceBool`,
`Lean.trustCompiler`), code run at elaboration time, new syntax, instances and
`default_instance` (quoted attribute names decoded), `export`, `open ... renaming` and
`open ... hiding`, `open` of namespaces outside `ALLOWED_OPENS`, options, imports; the decoded
`lakefile.toml` against a recorded configuration, each library once; `lake-manifest.json`
against the complete recorded manifest (top-level keys and every field of every package, with
multiplicity); `lean-toolchain`; no `lakefile.lean` and no tracked file under `.lake/`; and
every tracked `.lean` file must belong to a checked root or be one of the tooling files it
lists by exact path. Of these, the gate catches `sorryAx`, `native_decide` and
`Lean.ofReduceBool` independently through their axioms, and instances and default instances
through the registries (check 7).

`Controls/fingerprints.py` checks the trust set recorded in `data/challenge_fingerprints.json`:
the elaborated types and values of `Challenge.Defs`, the elaborated types of the theorems of
`Challenge.lean` (built with `lake build Challenge`, which is not a default target), the
agreement of those theorem names with `comparator.json`, and the SHA-256 of the challenge, the
comparator configuration, the gate and its controls, the files of `Controls/`,
`scripts/gen_root.py` (the continuous integration runs it before the build, so it is part of
the trust set and has a code owner), `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`,
the workflow and `.github/CODEOWNERS`. A change of
`data/challenge_fingerprints.json` must be approved separately by a person, who compares the
changed statements with the previously approved ones; the continuous integration only checks
and never writes the record. A hash stored beside the file it protects stops accidents, not
intent: whoever can change the file can change the hash in the same commit. The rest needs
the code owners of `.github/CODEOWNERS` and branch protection that requires their approval,
which must be enabled in the repository settings.

Limits that no script removes: the axiom gate detects registered forms of the abc conjecture
up to definitional unfolding only; and a vacuous hypothesis (`h : False`, or hypotheses that
cannot hold together) makes any conclusion provable and cannot be caught mechanically.
Hypotheses and statements are a matter for reading.
