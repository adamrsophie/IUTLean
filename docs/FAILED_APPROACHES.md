# Failed and abandoned approaches

Approaches that were tried and dropped, or rejected before any code was written, with the
reason. Only what the repository evidences is listed. Each entry says what statement was
attempted or considered, under which assumptions, what the outcome was, and where the evidence
is. A countermodel in `docs/COUNTERMODELS.md` refutes a simplified abstraction only; none
refutes a statement of the papers.

## Rejected because the result would be a shell

* **Prime strips, Hodge theaters, Θ-links (IUT I, IUT II).** Interfaces with the paper's
  conclusions as fields could be written, but nothing would constrain them to be the paper's
  objects. Not formalized. Only the elementary first step is now stated, without conclusions as
  fields: poly-morphisms as sets of morphisms and capsules (`IUT/PaperI/PolyMorphism.lean`). Evidence: `docs/PAPER_I_STRUCTURES.md`,
  `docs/PAPER_II_STRUCTURES.md`.
* **The log-shell as `ℤ_p`.** For odd `p`, replacing the log-shell of IUT III Definition 1.1
  (page 24) by `ℤ_p` would typecheck but would not be the definition. Rejected. The faithful
  definition for the base field `ℚ_p` is now in `IUT/Prerequisites/PadicLog.lean`: the
  log-shell is `(p*)⁻¹ · log(ℤ_p^×)`, with the `p`-adic logarithm proved convergent, a
  homomorphism and of image `{z | ‖z‖ ≤ 1/p*}`, and its equality with `ℤ_p` is a theorem
  (`padicLogShell_eq_range_coe`), not a definition. The identification of the Galois-invariant
  units with `ℤ_p^×` is an interpretation, not formalized. For finite extensions of `ℚ_p` the
  log-shell is defined in the same way in a normed-field model
  (`IUT/PaperIV/LocalFields/Logarithm.lean`) and bounded on the ring of integers
  (`IUT/PaperIV/LocalFields/Bridge.lean`); its compactness and the setting of IUT III remain
  open (`OPEN_PROBLEMS.md`, P-LOG).
* **A Lean `Prop` for Theorem 3.11 or Corollary 3.12.** Rejected; see `docs/DECISIONS.md`,
  decision 4.
* **Adopting the inclusion of Step (xi-f) as a hypothesis.** It restates the inequality
  conjunct of the conclusion (`stepXIf_inclusion_iff_inequality`); the finiteness conjunct of
  page 174 is separate. Rejected as a vacuity trick. Evidence:
  `docs/COR312_ANALYSIS.md`, condition C6.

## Dropped because a statement was found to be vacuous

* **A lower bound on the blurring factor stated as a conclusion.** Attempted statement: under
  (Lin), a cycle with the scalar `j²` (or its average `l(l+1)/12`) on one edge that closes up
  to a factor `B` forces `B ≥ j²` (or `B ≥ l(l+1)/12`). Assumption: the tolerance model, which
  already says that the product of the scalars is at most `B`. Outcome: the conclusion was the
  hypothesis restated after evaluating the product. Both forms were withdrawn; what remains is
  the evaluation itself, stated as an equivalence (`blur_bound`,
  `consistentUpTo_avgSq_iff` in `IUT/Audit/ScholzeStix/Blurring.lean`), with the averaging
  identity `avgSq_eq` as the only content beyond the hypothesis.

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
  only. The universe results take the existence axiom as the hypothesis `ExistenceAxiom`, which
  is independent of what Lean proves about `ZFSet.{u}`; the conditional results are vacuous in
  models where it fails.
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
`PartialInitialThetaConditions` (an explicit curve), power maps on `ℤ_p^×`, and free and surface
groups for IUT I §§1 to 2. The passage from IUT IV Theorem A to the abc statement now exists at
the level of statements: `IUT/Applications/ABCSpecialization.lean` proves that a statement about
rational points of `ℙ¹ \ {0, 1, ∞}` is equivalent to `Challenge.ABC` (`vojta_iff_ABC`). The
remaining gap is named there: IUT IV proves the compactly bounded form (ii) of [GenEll]
Theorem 2.1, and reaching that statement needs the direction (ii) ⟹ (i), whose proof uses points
of bounded degree over number fields and a noncritical Belyi map; neither is formalized
(`OPEN_PROBLEMS.md`, T-GENELL).
