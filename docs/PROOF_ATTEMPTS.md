# Proof attempts

A log of what was attempted in Lean and how it ended, limited to what the repository shows.
Each entry names the module and the main declarations, the statement attempted, the
assumptions, and the outcome. Outcomes are "proved" (no hypothesis beyond the statement,
allowed axioms only), "proved under stated hypotheses", or "not finished". A Lean lemma that
checks only one step of a statement of the papers proves that step, not the statement: such a
lemma is a fragment (`docs/DECISIONS.md`, decision 12), and "proved" below then refers to the
fragment. Approaches that were abandoned are in `docs/FAILED_APPROACHES.md`. Current counts
are in `docs/DASHBOARD.md`.

## abc statements

* **Equivalence of the three forms.** `IUT/Applications/ABC.lean`: `abc_iff_abcFinite`,
  `abc_iff_abcLog`, `rad_eq_radical`, `coprime_iff_pairwise`, restated in `Solution.lean`
  and checked by `lake comparator`. Proved.
* **Agreement with the Formal Conjectures statement.** `IUT/Applications/ABCFormalConjectures.lean`:
  `abc_iff_ABC`, `ltConstantMul_iff_ABC`, `qualityVariant_iff_ABC`. Proved. The
  Formal Conjectures statement is restated locally, not imported; see
  `docs/EXTERNAL_PROJECTS.md`.

## IUT IV

* **Local estimates, Propositions 1.2 to 1.7.** `IUT/PaperIV/Proposition1_2.lean` to
  `Proposition1_7.lean`. Where a statement needs objects that are not formalized (local
  field theory, tensor products of local fields, metrized real vector spaces), the module
  proves the numerical content and the missing properties enter as real-number hypotheses;
  each docstring says which. The docstring of `Proposition1_5.lean` states that it is not a
  formalization of Proposition 1.5. Proposition 1.6 is proved from Mathlib's prime number
  theorem with `η_prm ≥ 2`.
* **Proposition 2.1.** `IUT/PaperIV/Proposition2_1.lean`, read with `p ∉ A` from the render.
  Proved.
* **Definition 1.9 and arithmetic divisors.** `IUT/PaperIV/ArithmeticDivisor.lean`,
  `Definition1_9.lean`: `ADiv`, `degWeight`, `degE` with its basic properties (`degE_add`,
  `degE_nonneg`, `degE_eq_normalizedDeg`).
  Proved. The pull-back to an extension and the invariance of (i) are in `IUT/PaperIV/DegreePullback.lean`, in one reading of "the evident fashion".
* **Theorem 1.10.** `IUT/PaperIV/Theorem1_10/`: Steps (ii), (iii), (v), (viii), the elementary
  facts, and `final_inequality`. Each step is proved under the hypotheses the paper uses,
  including the inequality of IUT III Corollary 3.12 where the paper invokes it. Two
  hypotheses the page does not write (`D ≥ 0` in Step (iii), nonnegativity in Step (v)) are
  explicit in Lean.
* **Corollaries 2.2 and 2.3.** `IUT/PaperIV/Corollary2_2/Arithmetic.lean`,
  `IUT/PaperIV/Corollary2_3.lean`: the arithmetic of conditions (P1) to (P7), `P1_l_ge_seven`,
  and the extension to `ε > 1` (`BDle_mono_eps`). Proved under stated hypotheses; graded
  conditional in `docs/PAPER_IV_DERIVATION.md` because they depend on Theorem 1.10.
* **Theorem A to `Challenge.ABCLog`.** Not attempted in Lean: heights, log-differents and
  log-conductors on curves are not in Mathlib (`OPEN_PROBLEMS.md`, P-HT).
* **Grothendieck universes (§3).** `IUT/Foundations/GrothendieckUniverse.lean`:
  `exists_universe_forall_mem`, `exists_ascending_chain` (both from the hypothesis
  `ExistenceAxiom`), `not_exists_descending_mem_chain`. Proved. `ExistenceAxiom` is
  independent of what Lean proves about `ZFSet.{u}`, so the two conditional results are vacuous
  in models where it fails (module docstring).

## IUT III

* **Corollary 3.12, numerical layer.** `IUT/PaperIII/Corollary312/Numerical.lean`:
  `inequality_of_nonneg`, `constantForm_of_top`, `conclusion_iff_constantForm`,
  `stepXIf_inclusion_iff_inequality`, `thm1_10_final_of_cor312`. Proved. This is not a
  formalization of Corollary 3.12 (`docs/DECISIONS.md`, decision 6).
* **Remark 3.9.5, the hull operator.** `IUT/PaperIII/Remark3_9_5/HullOperator.lean`:
  `IsHullMap`, `IsHullMap.unique`, `IsHullMap.eq_sInter`. Proved: the intersection formula
  follows from (P1) to (P3) alone.
* **An interface for the last step of Corollary 3.12.** `IUT/PaperIII/Corollary312/Comparison.lean`.
  Attempted: the comparison of the q-pilot region with the hull of the union of possible images,
  as a containment (`Containment`) and as a log-volume inequality (`LogVolumeComparison`), and
  the passage to the numerical layer (`conclusion_of_containment`,
  `conclusion_of_procContainment`). Assumptions: the comparison itself, `μ(q-pilot) ≠ 0` and
  `< 1`, and finiteness; all regions are inputs. Outcome: proved conditionally; examples on `ℝ`
  (`example_bridge_hypotheses`, `example_comparison_fails`, `example_union_matters`). This is an
  interface, not the papers' objects.
* **Theorem 3.11 and Corollary 3.12 themselves.** Not attempted; the statements cannot be
  written without the missing definitions (`docs/DECISIONS.md`, decision 4).

## IUT I and IUT II

* **Poly-morphisms and capsules (IUT I §0).** `IUT/PaperI/PolyMorphism.lean`: `fullPolyIso`,
  `PolyMorphism.comp`, `isPolyIso_fullPolyIso`, `IsPolyIso.comp`, `PolyMorphism.comp_assoc`,
  `Capsule`, `Capsule.Hom`. Definitions of pages 33 and 34 with elementary lemmas, proved. The
  category laws for capsules are not proved.

* **Initial Θ-data, partial.** `IUT/PaperI/InitialThetaData.lean`:
  `PartialInitialThetaConditions`, `not_sqrtNegOneMem_rat`, `auxiliaryPrimeFirstClause_five`,
  `AuxiliaryPrimeFirstClause.coprime_six`, `TorsionRational.of_dvd`, `TorsionRational.two_of_six`.
  Proved. Conditions (d) to (f) are not stated.
* **Labels of IUT II.** `IUT/PaperII/Labels.lean`: `labelRep_bijective`,
  `gammaNormValue_strictMono`, and the identity `24·Σ j² = l(l² − 1)`. Proved. The strict
  monotonicity is what the literal reading of Remark 2.6.3 (d) gives; see `OPEN_PROBLEMS.md`,
  A29.

## Prerequisites

`IUT/Prerequisites/PositiveRationalsZhatUnits.lean` (`posRat_inter_zhatUnits`,
`eq_one_of_forall_valuation_eq_one`) and `IUT/Prerequisites/ProductFormula.lean`
(`prod_normAbs_eq_one`, `sum_log_normAbs_eq_zero`). Proved.

## The published discussion

* **Scholze and Stix.** `IUT/Audit/ScholzeStix/`.
  Attempted: the reduction of their Section 1.2 from Claim 6 to Vojta's inequality
  (`vojta_of_claim6`); the averaging identity (`avgSq_eq`); the two displays of their §1.3
  (`consequence_with_squares`, `consequence_without_squares`, restated in `Solution.lean`);
  the consistency of a cycle of scalars (`Diagram.lean`, `not_consistent_square`) and the
  tolerance condition for a cycle with the averaged scalar (`blur_bound`,
  `consistentUpTo_avgSq_iff`).
  Assumptions: Claim 6, (1.2), (1.3) and `N ≥ 0` as hypotheses of the reduction; the
  hypothesis (Lin) (every identification is a positive scalar) and the chosen tolerance model
  `ConsistentUpTo` for the diagram files.
  Outcome: proved under these assumptions. The lower bound on the tolerance `B` in
  `consistentUpTo_avgSq_iff` is the tolerance hypothesis evaluated, not a derived bound.
* **Mochizuki's responses.** `IUT/Audit/MochizukiResponses/`.
  Attempted: the examples (LVEx) (`not_linear`, `LVExMeasure.volume_R`, `LVExMeasure.gluing`),
  (SSIdEx) (`SSIdEx.not_iso_of_ne_one`) and the toy models (`ToyModels.stepXIf_formal`).
  Assumptions: the regions and admissibility conditions on `λ` of the report; in `gluing` the
  comparison `λ < μ^log(S)` follows from those conditions alone.
  Outcome: proved; each models a passage of the reports, not a statement of the papers.

## Countermodels

`IUT/Countermodels/`: nine modules of models in which a simplified abstraction of a step of
Corollary 3.12 fails when a compatibility condition is dropped, together with positive
statements under the condition. Attempted statement: each abstraction listed in
`docs/COUNTERMODELS.md`. Assumptions: those of each Lean theorem as listed there (for the
log-volume shifts, sets of finite positive measure and a nonzero dilation; for the comparison
model, positive pilot lengths). Outcome: each abstraction is refuted in a model; scope: the
abstraction only. The list, with the question each answers, is
in `docs/COUNTERMODELS.md`. None refutes a statement of the papers.
