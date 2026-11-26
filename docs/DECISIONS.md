# Design decisions

Each decision gives what was chosen and why. A decision changes only by a new entry that
says which earlier one it replaces.

## 1. Toolchain and Mathlib pin

Lean 4.36.0 (`lean-toolchain`: `leanprover/lean4:v4.36.0`) with Mathlib at tag v4.36.0,
commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (`lakefile.toml`).

Rationale: a tagged Mathlib release matched to the toolchain gives a reproducible build and a
prebuilt cache (`lake exe cache get`). Every Mathlib name cited in `docs/MATHLIB_GAP_ANALYSIS.md`
was checked against this version, so a bump requires rechecking those claims.

## 2. Material kept out of the repository

The PDFs of the four papers, the secondary literature (the manuscript of Scholze and Stix,
Mochizuki's reports and comments), clones of other Lean projects, and working notes are kept
in a local, untracked directory. The PDFs are not redistributed. `data/source_manifest.json`
records the file name, SHA-256, title page date and page count of each PDF in hand, so that a
reader with a copy can confirm it is the same version.

Rationale: the papers are copyrighted, and the project's claims must be checkable from the
tracked files plus a copy of the papers. The pipeline `scripts/run_all.sh` takes the PDF
directory as an argument.

## 3. Trusted definitions, challenge and solution

* `Challenge/Defs.lean` holds the only trusted vocabulary: `rad`, `ABC`, `ABCFinite`,
  `ABCLog`. It imports Mathlib only, is reviewed by hand, and is fingerprinted in
  `data/challenge_fingerprints.json`.
* `Challenge.lean` states the headline theorems with `sorry`; `Solution.lean` states them
  under the same names and proves them from the library. `lake comparator` checks that the two
  statements agree and that the proofs use only the allowed axioms (`comparator.json`).
* `Challenge` is one library, not two, because Lake assigns modules to libraries by root
  prefix; it is not a default target, so `lake build` and `lake check` never compile the file
  with `sorry`.

Rationale: a reader who trusts Mathlib and reads one short file can judge what the headline
theorems mean, without reading the library.

## 4. No Lean `Prop` for Theorem 3.11 or Corollary 3.12

Neither result is stated in Lean. Their statements mention Hodge theaters, the
log-theta-lattice, tensor packets of log-shells, the indeterminacies (Ind1) to (Ind3) and the
holomorphic hull of possible images, none of which is defined in the library.

Rationale: a statement with undefined terms replaced by arbitrary types or by structure fields
would be a shell: it could be proved, or assumed, without saying anything about the papers.
The project records the missing vocabulary as obligations instead (`OPEN_PROBLEMS.md`).

## 5. "Partial" in the names of partial condition collections

A structure that captures only some of the conditions of a definition carries `Partial` in
its name, and its docstring lists what it omits. Example: `PartialInitialThetaConditions` in
`IUT/PaperI/InitialThetaData.lean` states conditions (a), parts of (b) and (c) of IUT I
Definition 3.1, relative to an arbitrary base field, and omits (d), (e), (f) and the `SL_2`
condition.

Rationale: a reader who sees `InitialThetaData` would assume the full definition. The name
must not claim more than the structure states.

## 6. The numerical layer of Corollary 3.12

`IUT/PaperIII/Corollary312/Numerical.lean` takes the two numbers `−|log(Θ)| ∈ ℝ ∪ {+∞}` and
`−|log(q)| ∈ ℝ` as given (`PilotLogVolumes`) and proves what follows from their shape alone:

* the constant form of the conclusion and its equivalence with the inequality when
  `−|log(Θ)|` is finite (`conclusion_iff_constantForm`, `constantForm_of_top`);
* the reduction at the start of the proof (`inequality_of_nonneg`);
* that the inclusion `−|log(q)| ∈ R_{≤−|log(Θ)|}` of Step (xi-f) is the conclusion itself
  (`stepXIf_inclusion_iff_inequality`, by `Iff.rfl`);
* how Theorem 1.10 of IUT IV uses the conclusion (`thm1_10_final_of_cor312`).

What it shows: the last step of the proof of Corollary 3.12 is formal, so all the content of
the corollary lies in establishing the inclusion, which needs the constructions listed in
decision 4. The structure has no field that assumes a conclusion of the paper. The file is not
a formalization of Corollary 3.12, and its docstring says so.

## 7. Archimedean weights

`IUT/PaperIV/ArithmeticDivisor.lean` gives every archimedean place weight `1` in the degree
map, real or complex, exactly as in the display of IUT IV Definition 1.9 (i).
`IUT/Prerequisites/ProductFormula.lean` uses Mathlib's convention, with multiplicity `2` at a
complex place (`NumberField.InfinitePlace.mult`), for which the product formula holds.

Rationale: each module follows its source exactly. IUT IV pages 21 to 23 do not fix the
coefficient of a principal divisor at a complex place; [GenEll] page 4 does, with the factor
`[F_v : ℝ]` in the coefficient, and with that convention the degree of Definition 1.9 (i)
vanishes on principal divisors (`degPb_degF_principal` in `IUT/PaperIV/DegreePullback.lean`).

## 8. Mechanical citation edges over-approximate dependence

`data/dependencies.json` contains an edge whenever a statement's text or proof cites another
statement. `docs/CRITICAL_PATH.md` is everything reachable from IUT IV Theorem A and
Corollary 2.3 along these edges and the curated ones.

Rationale: a citation is not a logical dependence, but missing a real dependence is worse
than including a spurious one. The critical path is a reading list, not a bound in either
direction: it includes statements cited only for context, and it misses dependences that the
text uses without a citation or that the citation parser could not resolve. The documents
say so.

## 9. Status vocabulary

Statement fidelity and proof status are two separate fields with fixed values (listed in
`CONTRIBUTING.md`). `scripts/extract_statements.py` reports any other value, and
`scripts/dashboard.py` counts a record as verified only if its Lean declaration exists in the
built library and depends only on the allowed axioms.

Rationale: progress is measured by statements, not by lines of Lean. A formalized statement
that is not proved, and a proof under extra hypotheses, must not be counted as a verified
result.

## 10. Seven categories of result

Every gap is placed in one of seven categories, from failure of proof search to demonstrated
contradiction (`OPEN_PROBLEMS.md`). Countermodels in `IUT/Countermodels/` are always in the
category "counterexample to a simplified abstraction" unless a docstring proves otherwise.

Rationale: the dispute about the theory makes overstatement costly. A model in which a
simplified step fails says that a hypothesis is needed, not that the paper is wrong.

## 11. License

GNU General Public License, version 3 (`LICENSE`), for the Lean sources, the scripts and the
documents.

Rationale: the same license as the sibling projects of the same author, and one that keeps
derived formalizations open.

## 12. Fragment records (amends decision 9)

A Lean lemma that checks one arithmetic or elementary step of a statement of the papers does
not give the whole statement a formalized or verified status. A record for a statement (or a
part or proof step of one) may carry a `lean_declaration` and a status among
`STATEMENT_FORMALIZED`, `STATEMENT_REVIEWED`, `CONDITIONALLY_VERIFIED`, `KERNEL_VERIFIED`,
`INDEPENDENTLY_CHECKED` only if that declaration states the entire content of the record, with
the same objects, hypotheses and conclusion. Otherwise its `lean_declaration` is null and its
status says what is open. Each lemma that checks a piece gets its own record
`<parent id>.frag.<short name>` with `"kind": "fragment"`, its `parent`, exactly the
hypotheses and conclusion of the Lean lemma, what of the parent it `covers` and what it does
`not_covered`; the parent lists its `fragments`. A fragment is `KERNEL_VERIFIED` when the lemma
has no hypothesis standing for an unproved claim of the papers, and otherwise
`CONDITIONALLY_VERIFIED` with the assumed claims in `obligations`. The dashboard counts full
statements and fragments separately.

Rationale: decision 9 checked that a linked declaration exists and uses only the allowed
axioms, but not that it states the cataloged result. A kernel-checked fragment then made a
whole statement of the papers look formalized or verified. Separate records keep the evidence
and its scope together.

## 13. Working instructions for automated assistants stay out of the repository

Working instructions for automated assistants are not tracked. What
a contributor needs is in tracked documents: the trust policy and writing rules in
`CONTRIBUTING.md`, the decisions in this file, the trust boundary in
`docs/VERIFICATION_REPORT.md`, the open obligations in `OPEN_PROBLEMS.md`, and the plan in
`docs/ROADMAP.md`.

Rationale: the repository must be checkable and continuable from a clean checkout by a person
who has only the tracked files and a copy of the papers. Every rule that matters for the
mathematics or for trust is therefore stated in a tracked document, and nothing in the
repository depends on untracked instructions.
