# Proof attempts

A log of what was attempted in Lean and how it ended, limited to what the repository shows.
Each entry names the module and the main declarations. Outcomes are "proved" (no hypothesis
beyond the statement, allowed axioms only), "proved under stated hypotheses", or "not
finished". Approaches that were abandoned are in `docs/FAILED_APPROACHES.md`. Current counts
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
  `Definition1_9.lean`: `ADiv`, `degWeight`, `degE`, and the invariance `degE_ratio_invariant`.
  Proved; the pull-back to an extension is not defined (`OPEN_PROBLEMS.md`, P-PULL).
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
  `ExistenceAxiom`), `not_exists_descending_mem_chain`. Proved.

## IUT III

* **Corollary 3.12, numerical layer.** `IUT/PaperIII/Corollary312/Numerical.lean`:
  `inequality_of_nonneg`, `constantForm_of_top`, `conclusion_iff_constantForm`,
  `stepXIf_inclusion_iff_inequality`, `thm1_10_final_of_cor312`. Proved. This is not a
  formalization of Corollary 3.12 (`docs/DECISIONS.md`, decision 6).
* **Remark 3.9.5, the hull operator.** `IUT/PaperIII/Remark3_9_5/HullOperator.lean`:
  `IsHullMap`, `IsHullMap.unique`, `IsHullMap.eq_sInter`. Proved: the intersection formula
  follows from (P1) to (P3) alone.
* **Theorem 3.11 and Corollary 3.12 themselves.** Not attempted; the statements cannot be
  written without the missing definitions (`docs/DECISIONS.md`, decision 4).

## IUT I and IUT II

* **Initial Θ-data, partial.** `IUT/PaperI/InitialThetaData.lean`:
  `PartialInitialThetaConditions`, `not_sqrtNegOneMem_rat`, `isAuxiliaryPrime_five`,
  `IsAuxiliaryPrime.coprime_six`, `TorsionRational.of_dvd`, `TorsionRational.two_of_six`.
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

* **Scholze and Stix.** `IUT/Audit/ScholzeStix/`: the reduction to Vojta's inequality
  (`vojta_of_claim6`, proved under `N ≥ 0`), the averaging identity `avgSq_eq`, the two
  displays of their §1.3 (`consequence_with_squares`, `consequence_without_squares`, also in
  `Solution.lean`), the blurring bound `blur_bound`, and the consistency of a cycle of
  scalars in `Diagram.lean` (`not_consistent_square`). Proved.
* **Mochizuki's responses.** `IUT/Audit/MochizukiResponses/`: the models `LVEx`,
  `LVExMeasure`, `SSIdEx` and `ToyModels` (with `stepXIf_formal`). Proved; each models a
  passage of the reports, not a statement of the papers.

## Countermodels

`IUT/Countermodels/`: eight modules of models in which a simplified abstraction of a step of
Corollary 3.12 fails when a compatibility condition is dropped, together with positive
statements under the condition. The list, with the question each answers, is
in `docs/COUNTERMODELS.md`. None refutes a statement of the papers.
