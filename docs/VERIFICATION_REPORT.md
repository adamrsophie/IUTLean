# Verification report

What each check establishes, what it does not, what the results rest on, and the known limits.
The checks are run by CI on every push and pull request to `main`
(`.github/workflows/axiom-gate.yml`), in the order below.

## The checks

| Command | Establishes | Does not establish |
|---|---|---|
| `python3 -I scripts/Controls/source_scan.py` | No library file contains constructs the gate cannot see in the compiled environment: `debug.*` options, `set_option` outside an allowed list, new syntax, macros, elaborators or notation, commands that run code at elaboration time, local or scoped instances. Placeholders occur only in `Challenge.lean` and `IUT/Experimental/`. No experimental import outside that folder; the challenge files import only Mathlib and `Challenge.*`; no Lean options in `lakefile.toml`; every library file is imported by `IUT.lean`. | It is a syntactic search over sources with comments and strings blanked. It is untrusted. |
| `python3 -I scripts/gen_root.py --check` | `IUT.lean` imports exactly the library files outside `IUT/Experimental/`. | Anything about their content. |
| `lake build` | The default targets `IUT` and `Solution` elaborate and the kernel accepts every declaration. | That the statements mean what the papers say. |
| `python3 -I scripts/Controls/fingerprints.py --check` | `Challenge/Defs.lean` and the elaborated type and value of each of its constants are unchanged since the last recorded review. | That the definitions are right; that is the hand review. |
| `lake env lean AxiomGate.lean` (with `AXIOM_GATE_TRACKED_FILES`) | Every constant of `IUT`, `Challenge.Defs` and `Solution` depends only on `propext`, `Classical.choice`, `Quot.sound` (so no `sorryAx` and no `native_decide` axiom); none is an axiom, `unsafe`, `partial`, `opaque`, `@[implemented_by]` or `@[extern]`; no experimental module is imported; no constant settles a form of the abc conjecture unless named `abcConjecture`; every tracked library file is a module of the build and conversely; no module comes from outside the toolchain, Mathlib and the project. | It cannot see `debug.skipKernelTC` (covered by `lake check`) or custom elaborators (covered by the source scan). It detects conjecture statements only up to definitional equality, not, for example, `True → Challenge.ABC`. |
| `sh GateControls/run.sh AxiomGate.lean` | The gate accepts a clean control and rejects each control with a known defect (`sorry`, a forbidden axiom, `native_decide`, a renamed conjecture statement, an experimental import), with the expected diagnostic; the coverage check fails on a file the root does not import; the source scan reports every construct in its control. | That the gate catches defects not represented by a control. |
| `lake comparator` | Every theorem listed in `comparator.json` has in `Solution` exactly the statement of `Challenge`, uses only the allowed axioms, and is accepted by the kernel in a sandbox. | Anything about theorems not listed there. |
| `lake check` | The default targets, exported and replayed through the kernel, are accepted. This catches declarations added while kernel checking was disabled. | Anything about the meaning of the statements. |

`lake comparator` and `lake check` run inside the bubblewrap sandbox and need Linux with
unprivileged user namespaces. They run in CI on Ubuntu 24.04; on other systems they are not
run locally.

The data pipeline (`scripts/run_all.sh`) and `docs/DASHBOARD.md` are not checks. They count;
they do not verify mathematics.

## What is trusted

* **The Lean kernel** of Lean 4.36.0.
* **Mathlib** at tag v4.36.0, commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`: its
  definitions and the soundness of what it has proved.
* **The three axioms** `propext`, `Classical.choice`, `Quot.sound`.
* **`Challenge/Defs.lean`**, reviewed by hand: `rad`, `ABC`, `ABCFinite`, `ABCLog`. A reader
  must check that these say what the abc conjecture says.
* **The transcription from the papers.** Every Lean statement that formalizes a statement of
  the papers depends on a human reading of the PDF. The table below lists, from the module
  docstrings, which pages were checked against a rendered page; the rest were read in the
  extracted text layer, which loses decorations.

| Module or document | Rendered pages checked |
|---|---|
| `IUT/PaperI/InitialThetaData.lean` | IUT I 61 to 63 |
| `IUT/PaperII/Labels.lean` | IUT I 3; IUT II 3, 72, 79, 80, 122, 136, 145 |
| `IUT/PaperIII/Corollary312/Numerical.lean` | IUT III 173, 174 |
| `IUT/PaperIII/Remark3_9_5/HullOperator.lean` | IUT III 127 (pages 126 to 145 read in the text) |
| `IUT/Foundations/GrothendieckUniverse.lean` | IUT IV 67, 68 |
| `IUT/PaperIV/ArithmeticDivisor.lean` | none stated (pages 21, 22 cited) |
| `IUT/PaperIV/Definition1_9.lean` | IUT IV 21, 22 |
| `IUT/PaperIV/Proposition1_2.lean` | IUT IV 10 to 14 |
| `IUT/PaperIV/Proposition1_3.lean` | IUT IV 11 to 13 |
| `IUT/PaperIV/Proposition1_4.lean` | IUT IV 13, 14 |
| `IUT/PaperIV/Proposition1_5.lean` | IUT IV 15 |
| `IUT/PaperIV/Proposition1_6.lean` | IUT IV 16 |
| `IUT/PaperIV/Proposition1_7.lean` | IUT IV 16, 17 |
| `IUT/PaperIV/Proposition2_1.lean` | IUT IV 40 |
| `IUT/PaperIV/Theorem1_10/Arithmetic.lean` | IUT IV 23, 30, 31 |
| `IUT/PaperIV/Theorem1_10/ElementaryFacts.lean` | IUT IV 23, 24, 26, 29 |
| `IUT/PaperIV/Theorem1_10/StepII.lean` | IUT IV 24 |
| `IUT/PaperIV/Theorem1_10/StepIII.lean` | IUT IV 25, 26 |
| `IUT/PaperIV/Theorem1_10/StepV.lean` | IUT IV 28 to 30 |
| `IUT/PaperIV/Theorem1_10/StepVIII.lean` | IUT IV 30, 31 |
| `IUT/PaperIV/Corollary2_2/Arithmetic.lean` | IUT IV 42 to 48 |
| `IUT/PaperIV/Corollary2_3.lean` | IUT IV 54, 55 |
| `IUT/Prerequisites/PositiveRationalsZhatUnits.lean` | IUT I 127; IUT III 186, 187 |
| `IUT/Prerequisites/ProductFormula.lean` | IUT IV 21, 22; IUT III 186, 187 |
| `IUT/Audit/ScholzeStix/Reduction.lean` | Scholze and Stix 2, 3 |
| `IUT/Audit/ScholzeStix/Blurring.lean` | Scholze and Stix 4, 10 |
| `IUT/Audit/ScholzeStix/Section1_3.lean`, `Diagram.lean` | none (text only) |
| `IUT/Audit/MochizukiResponses/LVExMeasure.lean` | report pages 24, 25 |
| `IUT/Audit/MochizukiResponses/SSIdEx.lean` | report pages 17, 18 |
| `IUT/Audit/MochizukiResponses/ToyModels.lean` | report page 2; IUT III 190, 191 |
| `IUT/Countermodels/HaarNormalization.lean` | IUT III 115 |
| other modules of `IUT/Countermodels/` | none (text only) |
| `docs/COR312_ANALYSIS.md` | IUT III 112 to 117, 120, 124, 127, 129, 153 to 158, 173 to 175, 181 to 186, 190, 191 |
| `docs/PAPER_IV_DERIVATION.md` | IUT IV 3, 10 to 17, 21 to 31, 40 to 48, 54, 55, 67, 68 |

## Known limits

**Errors of the extracted text found against renders.** Each was corrected in the Lean
statement or the record; none is an error in the papers.

* IUT III page 174: the text reads `V^bad (= ∅)`; the render reads `(≠ ∅)`.
* IUT II page 158: the text drops the negation in `V^bad (≠ ∅)` in Definition 4.9 (viii).
* IUT IV page 10: the ceiling in `a_i` and the floor in `b_i` of Proposition 1.2 are dropped.
* IUT IV pages 13 to 14: the floor in Proposition 1.4 (iii) is dropped, which accounts for a
  `+1`.
* IUT IV page 22: `l = 5` in the text; `l ≠ 5` in the render.
* IUT IV page 25: `∉` read as `∈` in Step (iii) of Theorem 1.10.
* IUT IV page 40: `p ∈ A` in the text of Proposition 2.1; `p ∉ A` in the render.
* IUT IV page 46: `V^bad_mod = ∅` in the text; `≠ ∅` in the render.
* IUT I: the arrow decorations of Definition 1.1, the bars of Theorem 2.6 and the `⋊` of
  Definition 6.1 are lost in the text; the last was restored from renders.
* Report of Mochizuki, page 18: a `≠` is dropped.

**Pages not read, or read only at the level of statements.**

* IUT III Remarks 1.5.1 to 1.5.3 (pages 52 to 55) were not read; Remark 1.5.4 cites
  Remark 1.5.2 (ii).
* IUT III Proposition 2.1 and Corollary 2.3 (pages 58 onward) are cited by Remark 3.8.2 but
  were not read.
* IUT I Propositions 2.1, 2.2, 2.4 and Corollaries 2.3, 2.5 were read at the level of
  statements only; their proofs were not checked. IUT I Example 5.1 (pages 123 to 131) was
  read only in part.
* IUT IV Proposition 1.8 (iv), on which IUT I Remark 3.1.5 depends, was not read.
* The corrections to [EtTh] recorded in IUT I Remarks 3.1.6 and 3.2.4 were not checked
  against [EtTh]. No outside reference ([GenEll], [EtTh], [AbsTopIII], ...) was read.
* The Scholze and Stix manuscript quotes an earlier version of Step (xi) than the May 2020
  manuscript; see `docs/SCHOLZE_STIX_ANALYSIS.md`.
* Statements with status `NOT_EXTRACTED` in `docs/DASHBOARD.md` were located by the
  mechanical index only.

**Checks that run only in CI.** `lake comparator` and `lake check` need Linux. A contributor on
another system relies on CI for them.

**The catalog.** Citation edges are mechanical and over-approximate dependence
(`docs/DECISIONS.md`, decision 8). The scripts are untrusted; their output can be recomputed
from the inputs.
