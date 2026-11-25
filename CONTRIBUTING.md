# Contributing

Contributions are welcome: a Lean proof of an open step, a faithful statement of a result
that is not yet stated, a correction to the catalog, or a countermodel to a simplified
abstraction. Read [OPEN_PROBLEMS.md](OPEN_PROBLEMS.md) and
[docs/COR312_ANALYSIS.md](docs/COR312_ANALYSIS.md) first. No single step settles the abc
conjecture or Corollary 3.12.

## Trust policy

Everything in `IUT/` outside `IUT/Experimental/`, and everything in `Solution.lean` and
`Challenge/`, follows these rules. CI rejects a change that breaks them.

* **Axioms.** Only `propext`, `Classical.choice` and `Quot.sound`. No declaration may depend
  on any other axiom, and in particular on `sorryAx`.
* **Forbidden constructs.** `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `partial`,
  `native_decide`, `@[implemented_by]`, `@[extern]`, `debug.*` options, `set_option` with an
  option outside the allowed list of the source scan, new syntax, macros, elaborators or
  notation, `run_cmd` and the other commands that run code at elaboration time, `#eval`, and
  local or scoped instances. The full list is in the header of
  `scripts/Controls/source_scan.py`. `Challenge.lean` alone may contain `sorry`, on purpose.
* **No placeholders and no shells.** A Lean `Prop` for a result of the papers exists only when
  every term in it is genuinely defined. A structure whose fields are the conclusions of the
  paper, a hypothesis that restates the conclusion, or a definition chosen so that the
  statement becomes trivial or vacuous is not allowed. When a statement cannot be written
  faithfully, record it as an obligation in the catalog instead.
* **Partial collections are named as such.** A structure that captures only some of the
  conditions of a definition carries `Partial` in its name, and its docstring lists the
  conditions it omits (see `PartialInitialThetaConditions`).
* **The experimental directory.** Drafts with `sorry` go in `IUT/Experimental/`. No module
  outside it may import it, `IUT.lean` never lists it, and nothing in it counts as verified.
  See `IUT/Experimental/README.md`.
* **Trusted definitions.** `Challenge/Defs.lean` imports Mathlib only. A change to it is
  reviewed by hand against its source and then recorded with
  `python3 -I scripts/Controls/fingerprints.py --write`.

## Every Lean module cites its source

Each module starts with a docstring that gives:

* the paper, the numbered statement, and the manuscript pages, written "pages 173 to 186";
* which pages were read, and whether the formulas were checked against rendered pages or only
  against the extracted text (which loses decorations such as `≠`, `∉`, ceilings and floors);
* every interpretation choice, with the reason for it.

A countermodel module also says which simplified abstraction it refutes, and that it does not
refute a statement of the papers unless that is shown.

## How statements enter the catalog

`data/statements.json` is the index of every numbered statement of the four papers. It is
generated: do not edit it by hand. Records written by reading the papers live in
`data/curated/iut1.json` to `iut4.json`, one record per statement id (for example
`IUT3.Cor3_12.StepXI.f`). The fields are `source`, `content`, `explicit_hypotheses`,
`implicit_hypotheses`, `conclusion`, `definitions_required`, `results_used`,
`external_dependencies`, `lean_declaration`, `statement_status`, `proof_status`,
`obligations` and `ambiguities`.

Statement fidelity and proof status are reported separately. The status values are:

| Status | Meaning |
|---|---|
| `NOT_EXTRACTED` | located by the mechanical index; content not read |
| `EXTRACTED` | read and recorded in the curated data |
| `INTERPRETATION_AMBIGUOUS` | read; more than one reading is possible, and the record lists them |
| `LEAN_STATEMENT_DRAFT` | a Lean statement exists but captures only part of the statement, or is not yet reviewed as faithful |
| `STATEMENT_FORMALIZED` | a faithful Lean statement exists in the library |
| `STATEMENT_REVIEWED` | the Lean statement was reviewed against the rendered pages |
| `PROOF_IN_PROGRESS` | a proof is being written |
| `BLOCKED_BY_MATHLIB` | needs a definition or theorem that Mathlib lacks |
| `BLOCKED_BY_EXTERNAL_THEOREM` | needs a result of another paper that is not formalized |
| `BLOCKED_BY_MISSING_JUSTIFICATION` | the papers give no argument that could be formalized |
| `CONDITIONALLY_VERIFIED` | proved in Lean under hypotheses stated in the record |
| `KERNEL_VERIFIED` | proved in Lean, with no hypothesis beyond those of the statement, from the allowed axioms only |
| `INDEPENDENTLY_CHECKED` | kernel verified and also checked independently |
| `COUNTERMODEL_FOUND` | a Lean countermodel to the faithfully stated statement |

A record that claims a verified status must name a `lean_declaration` that exists in the built
library and depends only on the allowed axioms; `scripts/dashboard.py` does not count it as
verified otherwise. The definitions of the dashboard counts are in the docstring of
`scripts/dashboard.py`.
After editing curated data, regenerate the derived files:

```sh
sh scripts/run_all.sh <directory with the four PDFs>
```

`SKIP_LEAN=1` reuses the existing Lean declaration inventory. See `scripts/README.md`.

## Classifying a result

Every gap or failure is put in one of seven categories, and the categories are not mixed:

1. failure of proof search;
2. missing library theorem;
3. gap in the formalization;
4. insufficient hypotheses;
5. counterexample to a simplified abstraction;
6. counterexample to a faithfully formalized statement;
7. demonstrated contradiction.

A hypothesis the paper leaves unstated but that holds is not an error in the paper. A
countermodel to a simplified model is category 5, never 6 or 7.

## Running every check locally

From the repository root, after `lake exe cache get`:

```sh
python3 -I scripts/Controls/source_scan.py
python3 -I scripts/gen_root.py --check
lake build
python3 -I scripts/Controls/fingerprints.py --check
git ls-files -- IUT.lean IUT > tracked-files.txt
AXIOM_GATE_TRACKED_FILES=tracked-files.txt lake env lean AxiomGate.lean
AXIOM_GATE_TRACKED_FILES=tracked-files.txt sh GateControls/run.sh AxiomGate.lean
```

`lake comparator` and `lake check` need the bubblewrap sandbox and therefore Linux; CI runs
them on every push and pull request. A new library file must be imported by `IUT.lean`:
run `python3 -I scripts/gen_root.py` to regenerate it.

## Writing rules for documents

* Self-contained wording: a document describes the project and the papers, not the process
  that produced it.
* Page ranges are written "pages 173 to 186". Cite the manuscript page, not the journal page.
* American English spelling.
* No dash used as a sentence connector or parenthetical; use a semicolon, a colon or a period.
* Do not overstate. Say what is proved, under which hypotheses, and what is not; "the paper
  does not argue X" is not "X is false".
* Do not hand-edit generated files (`docs/DASHBOARD.md`, `docs/CRITICAL_PATH.md`,
  `docs/DEPENDENCY_GRAPH.md`, `docs/STATEMENT_CATALOG.md`, `docs/SOURCE_MANIFEST.md`,
  `docs/REFERENCE_INVENTORY.md`, `docs/dependency_graph.svg`, `data/statements.json`).
* Do not quote counts from the dashboard in hand-written documents; link to it.

## What happens to a pull request

CI runs the checks above. A reviewer reads the Lean statement against the cited pages, checks
the docstring, and checks that the catalog records were updated. A change to
`Challenge/Defs.lean` needs a separate review of the definition against its source.

By contributing you agree that your contribution is licensed under the GNU General Public
License, version 3.
