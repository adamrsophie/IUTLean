# Failed and abandoned approaches

Approaches that were tried and dropped, or rejected before any code was written, with the
reason. Only what the repository evidences is listed. Each entry says where the evidence is.

## Rejected because the result would be a shell

* **Prime strips, Hodge theaters, Θ-links (IUT I, IUT II).** Interfaces with the paper's
  conclusions as fields could be written, but nothing would constrain them to be the paper's
  objects. Not formalized, and the first step (poly-morphisms as sets of morphisms) was not
  started for that reason. Evidence: `docs/PAPER_I_STRUCTURES.md`,
  `docs/PAPER_II_STRUCTURES.md`.
* **The log-shell as `ℤ_p`.** For odd `p`, replacing the log-shell of IUT III Definition 1.1
  (page 24) by `ℤ_p` would typecheck but would not be the definition. Rejected. The faithful
  version is blocked by the missing properties of `NormedSpace.log` (`OPEN_PROBLEMS.md`,
  P-LOG). Evidence: `docs/MATHLIB_GAP_ANALYSIS.md`.
* **A Lean `Prop` for Theorem 3.11 or Corollary 3.12.** Rejected; see `docs/DECISIONS.md`,
  decision 4.
* **Adopting the inclusion of Step (xi-f) as a hypothesis.** It is the conclusion restated
  (`stepXIf_inclusion_iff_inequality`). Rejected as a vacuity trick. Evidence:
  `docs/COR312_ANALYSIS.md`, condition C6.

## Dropped because a statement was found to be vacuous

* **`blur_ge_square` in `IUT/Audit/ScholzeStix/Diagram.lean`.** An earlier version had the
  hypothesis `(j : ℝ)^2 * 1 ≤ B` and the conclusion `(j : ℝ)^2 ≤ B`: the hypothesis restated
  the conclusion. The theorem was removed. The intended content is `blur_bound` and
  `blur_ge_avgSq` in `IUT/Audit/ScholzeStix/Blurring.lean`.

## Blocked on definitions or literature

* **IUT I Definition 3.1, conditions (d), (e), (f) and the `SL_2` condition.** They need the
  field `K`, the `q`-parameter and the field of moduli of the curve, which are not available
  in the needed form. Only a partial collection is stated
  (`PartialInitialThetaConditions`). Evidence: `docs/INITIAL_THETA_DATA.md`.
* **Pull-back invariance of the degree of arithmetic divisors** (IUT IV Definition 1.9 (i)).
  The paper defines the pull-back "in the evident fashion"; choosing a pull-back so that the
  identity holds would make it nearly definitional. Deferred until the convention of [GenEll]
  §1 is fixed. Evidence: `docs/MATHLIB_GAP_ANALYSIS.md`.
* **Degree zero of principal arithmetic divisors.** With weight `1` at every archimedean
  place, a coefficient convention at complex places would have to be invented. Not defined;
  only the product formula was formalized. Evidence: `docs/DECISIONS.md`, decision 7.
* **A Grothendieck universe in `ZFSet`.** Mathlib provides the embedding at the `PSet` level
  only. The universe results take the existence axiom as the hypothesis `ExistenceAxiom`.
* **Morphisms of IUT I Definition 6.13.** Not found on the pages read. Evidence:
  `docs/PAPER_I_STRUCTURES.md`.

## A reading that conflicts with the text

* **IUT II Remark 2.6.3 (d), page 80.** Read literally, `‖Γ′‖` is strictly increasing in
  `|Γ′|` on `{1, …, l*}`, and Lean proves this (`gammaNormValue_strictMono`). The remark says
  "not strictly increasing" and "constant for `|Γ′| ≥ l*`", which the literal reading makes
  false and vacuous respectively. The intended reading is not settled. Evidence:
  `docs/PAPER_II_STRUCTURES.md`.

## Not attempted

The following were planned but have no code: the nonvacuity of
`PartialInitialThetaConditions` (an explicit curve), power maps on `ℤ_p^×`, free and surface
groups for IUT I §§1 to 2, and the passage from IUT IV Theorem A to `Challenge.ABCLog`.
