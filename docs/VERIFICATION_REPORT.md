# Verification report

What each check establishes, what it does not, what the results rest on, and the known limits.
The checks are run by CI on every push and pull request to `main`
(`.github/workflows/axiom-gate.yml`), in the order below.

## The checks

| Command | Establishes | Does not establish |
|---|---|---|
| `python3 -I scripts/Controls/source_scan.py` | No library file contains constructs the gate cannot see in the compiled environment: `debug.*` options, `set_option` outside an allowed list, new syntax, macros, elaborators or notation, commands that run code at elaboration time, `export`, `open ... renaming` and `open ... hiding`, an `open` of a namespace outside its list, instance commands and attributes other than the one allowed line (which must occur once), `deriving`, `default_instance` in any spelling, and native evaluation (`native_decide`, `decide +native`, `Lean.ofReduceBool`, `Lean.trustCompiler`). Identifiers are compared after quoted names `«…»` are decoded and `_root_.` is removed, so `_root_.sorryAx` is found. Placeholders occur only in `Challenge.lean` and `IUT/Experimental/`. No experimental import outside that folder; the challenge files import only Mathlib and `Challenge.*`; no Lean options in `lakefile.toml`, and its decoded configuration equals the recorded one, each library declared once; `lake-manifest.json` equals the recorded manifest in every field of every package, with multiplicity, and in its top-level keys; `lean-toolchain` is the recorded toolchain; no tracked file under `.lake/`; every library file is imported by `IUT.lean`; every other tracked `.lean` file is a tooling file listed by exact path. | It is a lexical search over sources with comments and strings blanked; it does not resolve names. It is untrusted. The gate catches `sorryAx`, `native_decide` and `Lean.ofReduceBool` independently through the axioms they add (check 1); it does not see `export`, `open ... renaming` or a `default_instance` attribute on a constant of a dependency except through the registries of check 7. |
| `python3 -I scripts/gen_root.py --check` | `IUT.lean` imports exactly the library files outside `IUT/Experimental/`. | Anything about their content. |
| `lake build` | The default targets `IUT` and `Solution` elaborate and the kernel accepts every declaration. | That the statements mean what the papers say. |
| `lake build Challenge` | `Challenge.lean`, which is not a default target, elaborates; the fingerprint helper imports it. | Anything about its statements, which are proved with `sorry` on purpose. |
| `python3 -I scripts/Controls/fingerprints.py --check` | The elaborated type and value of each constant of `Challenge/Defs.lean`, the elaborated type of each statement of `Challenge.lean`, the list of names in `comparator.json`, and the hashes of the trust files listed in the script (among them `scripts/gen_root.py`, which runs before the build) are unchanged since the record was last written with `--write`. | That the definitions and statements are right; that is the human comparison with the source. That a change of the record was approved: no step ties the record to an approval (see the trust policy in `CONTRIBUTING.md`). |
| `lake env lean AxiomGate.lean` (with `AXIOM_GATE_TRACKED_FILES`) | Every constant of `IUT`, `Challenge.Defs` and `Solution` depends only on `propext`, `Classical.choice`, `Quot.sound` (so no `sorryAx` and no `native_decide` axiom); none is an axiom, `unsafe`, `partial`, `opaque`, `@[implemented_by]` or `@[extern]`; no experimental module is imported; check 3: no constant (axioms included) proves a registered open statement without a hypothesis that mentions a registered statement (see "Registries of open statements" below), unless named `abcConjecture`; every tracked library file is a module of the build and conversely; no module comes from outside the toolchain, Mathlib and the project. Check 6: no project name captures, by name resolution, a constant of a dependency or a trusted constant of `Challenge.*` (a proper suffix of the name, at the root or under an enclosing namespace, names such a constant; or the last component of a name declared directly in a namespace names such a constant in a namespace that the library opens), apart from seven names allowlisted by full name. Check 7: the only instance the library registers is `IUT.PaperI.Capsule.fintype` (by full name and class) besides the `SizeOf` instances Lean generates; no instance is on a dependency class with only dependency arguments after unfolding reducible definitions; the library registers no default instance. | It cannot see `debug.skipKernelTC` (covered by `lake check`) or custom elaborators (covered by the source scan). Check 3 detects registered statements only up to definitional equality, through leading `∀` binders, `∧` and `↔`, and only registered ones: not, for example, `True → Challenge.ABC`, an equivalence of a registered statement with a true statement that mentions a registered constant, or a structure field; a hypothesis that merely mentions a registered constant (`Challenge.ABC → True`) exempts the declaration. Check 6 does not know which file opens which namespace, so its rule over-approximates for names declared directly in a namespace; it does not report a project name that shadows another project name, a member of a project type (`S.c` inside `namespace S`) that shadows an opened name, or a private name shadowing another private name. These remain for reading. |
| `sh GateControls/run.sh AxiomGate.lean` | The gate accepts the clean controls (`Clean`, and `OpenStatementsClean`: conditional statements, refuted instances of a family, an equivalence of two registered statements) and rejects each control with a known defect (`sorry`, a forbidden axiom, `native_decide`, a renamed or restated conjecture statement in `RenamedConjecture`, `EquivalentForm` and `VojtaRestated`, an open statement proved through a local alias, behind binders, in a conjunction or an equivalence, an instance of an open family, an author statement, and the registered `ABCInt` and `ABCWithExponent` of the library from a hypothesis `False` in `OpenStatements`, shadowing names in `Shadowing`, `PrivateShadowing` and `TrustedNames`, instances on aliases and default instances in `ForeignInstances`, an experimental import), with the expected diagnostic; the coverage check fails on a file the root does not import; the source scan reports every construct in its controls, reports unlisted tooling files, and rejects a repeated allowed instance line. | That the gate catches defects not represented by a control. |
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
* **The seven statements of `Challenge.lean`** (`abc_iff_abcFinite`, `abc_iff_abcLog`,
  `rad_eq_radical`, `coprime_iff_pairwise`, `theorem1_10_final_arithmetic`,
  `scholzeStix_with_squares`, `scholzeStix_without_squares`). `lake comparator` checks that
  `Solution` proves exactly these statements; it cannot check that the statements are the
  intended ones. The fingerprint check (`scripts/Controls/fingerprints.py`) records the
  elaborated types of these statements and the list of names in `comparator.json`, so a
  change to them is detected; but a change made together with a new record (`--write`) passes,
  so the record is only as good as the separate approval of its changes. Each of the seven
  statements, and any change to it, needs a human mathematical comparison with its source,
  approved separately from the change itself.
* **The transcription from the papers.** Every Lean statement that formalizes a statement of
  the papers depends on a human reading of the PDF. The table below lists, from the module
  docstrings, which pages were checked against a rendered page; the rest were read in the
  extracted text layer, which loses decorations.

| Module or document | Rendered pages checked |
|---|---|
| `IUT/PaperI/PolyMorphism.lean` | IUT I 33, 34; IUT II 35 |
| `IUT/PaperI/InitialThetaData.lean` | IUT I 61 to 63 |
| `IUT/PaperII/Labels.lean` | IUT I 3; IUT II 3, 72, 79, 80, 122, 136, 145 |
| `IUT/PaperIII/Corollary312/Numerical.lean` | IUT III 173, 174 |
| `IUT/PaperIII/Corollary312/Comparison.lean` | IUT III 115 to 117, 127, 173 to 175, 181 to 185 |
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

## Source review versus kernel acceptance

Two different things are established, by different means, and neither implies the other.

* **Kernel acceptance** (`lake build`, the axiom gate, `lake comparator`, `lake check`): each
  Lean declaration is proved as written from the allowed axioms. This is mechanical.
* **Source review**: a Lean statement says what the cited statement of the papers says, with
  the same objects, hypotheses, quantifiers and conclusion. This is a human comparison of the
  Lean type with the rendered page. It is needed for every correspondence between a statement
  of the papers and a Lean declaration (every `lean_declaration` of `data/curated/`, every
  docstring that names a statement of the papers, the seven statements of `Challenge.lean`),
  not only for `Challenge/Defs.lean`. No script performs it. A record that links a Lean lemma
  checking only one step of a statement is a fragment record (`kind: "fragment"`) and gives the
  parent statement no formalized or verified status.

## Pins and exclusions

* Toolchain `leanprover/lean4:v4.36.0` (`lean-toolchain`); Mathlib tag v4.36.0, commit
  `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (`lakefile.toml`, `lake-manifest.json`).
* Gates configured in CI, in order: the source scan, the root check, `lake build`,
  `lake build Challenge`, the fingerprint check, the axiom gate, the gate controls, `lake comparator` and `lake check`
  (`.github/workflows/axiom-gate.yml`). This report describes what each establishes; it does
  not record the outcome of a particular run. The outcome for a given revision is the CI log of
  that revision.
* Excluded from the gate by design: `IUT/Experimental/` (drafts, never imported) and
  `Challenge.lean` (statements with `sorry`, not a default target, checked only through
  `lake comparator`). The axiom gate detects statements of the abc conjecture only up to
  definitional equality. The source scan is syntactic. `lake comparator` and `lake check` run
  only on Linux.

## Registries of open statements

Check 3 of `AxiomGate.lean` enforces the rule that no declaration of the library proves an
open statement without assuming one. The open statements are three plain lists near the top
of `AxiomGate.lean`; an entry is the full name of a definition and the module that declares
it, and adding one needs no change of the logic.

* `closedForms`: statements of type `Prop` that are open and that the library proves
  equivalent to the abc conjecture: `Challenge.ABC`, `Challenge.ABCFinite`,
  `Challenge.ABCLog`, the three forms of `IUT.ABC.FormalConjectures`,
  `IUT.ABC.Variants.ABCInt`, `IUT.ABC.Variants.ABCIntSum`, and
  `IUT.ABCSpecialization.VojtaLineMinusThreePointsRational` and `...UnitInterval`, and the
  open statement `IUT.VojtaNumberField.VojtaLineMinusThreePointsBoundedDegree`, which implies
  it. Neither a form nor its negation may be proved outright.
* `openFamilies`: constants of type `… → Prop` some of whose instances are open:
  `IUT.ABC.Variants.ABCWithExponent` (open for `κ > 1`) and
  `IUT.ABCSpecialization.RationalPointBoundFor` and
  `IUT.VojtaNumberField.VojtaLineMinusThreePointsDegreeAtMost` (open for `d ≥ 1`, trivially
  true for `d = 0`). No instance may be proved outright, for any
  argument; negated instances may (`not_abcWithExponent_of_le_one` refutes `κ ≤ 1`), and so
  may implications whose hypothesis is an instance (`abcWithExponent_mono`).
* `authorStatements`: statements of results or claims of other papers that the library may
  assume but never proves: `Thm5_4Claim`, `Thm5_3iiRationalClaim`, `Lemma5_7Claim` and
  `Cor5_8Statement` of `IUT.ExplicitEstimates`, and `ZhouTheorem32i`, `ZhouCorollary33`,
  `ZhouNLevelBound` and `ZhouComputedRange` of `IUT.Applications.ZhouExplicit`, and
  `SouleTheoremBClaim`, `LaniewskiMullerMassBound`, `PastenDivisorBound` and
  `DivisorCountPowerBound` of `IUT.ABC.Elementary`. The module
  `IUT/Applications/DupuyHilado.lean` declares no such statement: its conditional lemmas take
  inequalities between real numbers as hypotheses.

A further list, `provedInstances`, accepts a declaration that concludes a registered statement
without assuming one, by full name and the hash of its statement (the gate prints the hash in
its report); it is empty. A proved instance that is not open, such as a future theorem
`VojtaLineMinusThreePointsDegreeAtMost 0`, goes there.

To register a statement, add one line `(`Full.Name, `Module.Name),` to `closedForms`,
`openFamilies` or `authorStatements` in the section "Registries of check 3" of
`AxiomGate.lean`; nothing else changes.

How a statement is compared: the whole statement, and then each conclusion after stripping
the leading `∀` binders one at a time (after reducible unfolding), each with its conjuncts and
with each side of an `↔` whose other side mentions no registered constant, is compared with
`c ?x₁ … ?xₙ` for each entry `c` and fresh metavariables, and with its negation for closed
forms and author statements. Both sides are first expanded: every definition of the project
(`IUT.*`, `Challenge.*`, `Solution`, the file being checked; instances excepted) and `Not` are
unfolded, whatever their reducibility. Then `isDefEq` runs at the transparency of instances,
so definitions of Mathlib stay folded and a near miss (an exponent `3 : ℕ` against `κ : ℝ`,
an extra `+ 0` on `ℝ`) fails at once instead of unfolding the reals; the control
`ExponentThree` checks this. A local `def Y : Prop := Challenge.ABC` followed by `theorem t : Y`
is caught, since `Y` is expanded, and so is an alias marked `@[irreducible]`. Not caught: a
statement equal to a registered one only after unfolding a Mathlib definition, and an alias
that hides the `∀`, `∧` or `↔` around a registered statement (`def Z : Prop := 1 = 1 ∧ ABC`;
the binders and connectives are seen up to reducible unfolding only). Each statement has a
heartbeat budget; running out of it is an error that names the statement, never a pass. A match is accepted when a stripped
hypothesis mentions a registered constant by name. The limits: propositional reformulations
that are not definitionally equal to a registered statement, and a hypothesis that mentions a registered constant without assuming it are
not detected; an alias of a registered statement used as a hypothesis is not recognized as an
assumption, so such a declaration is reported (this fails closed). An entry whose module the
import closure does not contain is skipped with a note, and is an error under continuous
integration.

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

**Name resolution.** The gate compares names, not the elaborated meaning of identifiers in
source files. A reader must still check by eye: that an identifier in a statement means the
constant its spelling suggests when a project constant of the same name exists in an enclosing
project namespace (project names shadowing project names are not reported); members of a
project type used inside `namespace S` of that type; the effect of `open` of a library
namespace; and the three allowlisted names of check 6 (`shadowAllowed` in `AxiomGate.lean`).

**Checks that run only in CI.** `lake comparator` and `lake check` need Linux. A contributor on
another system relies on CI for them.

**The catalog.** Citation edges are mechanical and over-approximate dependence
(`docs/DECISIONS.md`, decision 8). The scripts are untrusted; their output can be recomputed
from the inputs.
