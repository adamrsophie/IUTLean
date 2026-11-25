import Mathlib

/-!
# Scholze–Stix, Section 1.3: the arithmetic of displays (1.4), (1.5), (1.6)

Source: P. Scholze and J. Stix, *Why abc is still a conjecture*, manuscript dated
July 16, 2018, Section 1.3, pages 3 and 4. Read in full.

Scholze and Stix summarize the passage from IUT III, Corollary 3.12, to IUT IV, Theorem 1.10,
by an "essential approximation" of `− |log(Θ)|`. This file checks the real arithmetic of that
summary. It takes no position on whether the approximation (1.5) or its variant (1.6)
describes what IUT III proves; that is the disputed point, and it is not arithmetic.

Notation: `l` is the prime, `lh = (l − 1)/2` is their `ℓ^>`, `d` is the log root discriminant
`d(P)`, `qE` is `deg(q_E)`. Display (1.4) is `− |log(q)| ≤ − |log(Θ)|` with
`− |log(q)| = − qE / (2 l)`.
-/

namespace IUT.Audit.ScholzeStix

/-- The average over `j = 1, …, ℓ^>` in display (1.5), with the factor `j²` on the `q` term:
`(1/ℓ^>) ∑_j (j·d − j²·qE/(2ℓ))`. -/
noncomputable def thetaWithSquares (lh : ℕ) (l d qE : ℝ) : ℝ :=
  (1 / (lh : ℝ)) * ∑ j ∈ Finset.Icc 1 lh, ((j : ℝ) * d - (j : ℝ) ^ 2 * (qE / (2 * l)))

/-- The average in display (1.6), "with the factor `j²` missing":
`(1/ℓ^>) ∑_j (j·d − qE/(2ℓ))`. -/
noncomputable def thetaWithoutSquares (lh : ℕ) (l d qE : ℝ) : ℝ :=
  (1 / (lh : ℝ)) * ∑ j ∈ Finset.Icc 1 lh, ((j : ℝ) * d - qE / (2 * l))

private theorem sum_id (k : ℕ) : ∑ m ∈ Finset.Icc 1 k, (m : ℝ) = k * (k + 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; push_cast; ring

private theorem sum_sq (k : ℕ) :
    ∑ m ∈ Finset.Icc 1 k, (m : ℝ) ^ 2 = k * (k + 1) * (2 * k + 1) / 6 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; push_cast; ring

/-- Display (1.5): with `l = 2·ℓ^> + 1`, the average with squares equals
`(ℓ^> + 1)/2 · (d − qE/6)`. -/
theorem display_1_5 {lh : ℕ} (hlh : 1 ≤ lh) {l : ℝ} (hl : l = 2 * lh + 1) (d qE : ℝ) :
    thetaWithSquares lh l d qE = ((lh : ℝ) + 1) / 2 * (d - qE / 6) := by
  have h0 : (lh : ℝ) ≠ 0 := by positivity
  have hl0 : l ≠ 0 := by rw [hl]; positivity
  unfold thetaWithSquares
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, sum_id, sum_sq]
  field_simp
  rw [hl]; ring

/-- Display (1.6): the average without squares equals `(ℓ^> + 1)/2 · d − qE/(2ℓ)`. -/
theorem display_1_6 {lh : ℕ} (hlh : 1 ≤ lh) (l d qE : ℝ) :
    thetaWithoutSquares lh l d qE = ((lh : ℝ) + 1) / 2 * d - qE / (2 * l) := by
  have h0 : (lh : ℝ) ≠ 0 := by positivity
  unfold thetaWithoutSquares
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_id]
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  field_simp

/-- Substituting (1.5) into (1.4): `(1/6)·qE·(1 − 12/(ℓ(ℓ+1))) ≤ d`. Scholze and Stix write
this as `(1/6) deg(q_E) ≲ (1 − 12/(ℓ(ℓ+1)))⁻¹ · d(P)`. -/
theorem consequence_with_squares {lh : ℕ} (hlh : 1 ≤ lh) {l : ℝ} (hl : l = 2 * lh + 1)
    {d qE : ℝ} (h14 : -(qE / (2 * l)) ≤ thetaWithSquares lh l d qE) :
    1 / 6 * qE * (1 - 12 / (l * (l + 1))) ≤ d := by
  rw [display_1_5 hlh hl] at h14
  have hlh' : (1 : ℝ) ≤ lh := by exact_mod_cast hlh
  have hl0 : 0 < l := by rw [hl]; positivity
  have hlh2 : (lh : ℝ) + 1 = (l + 1) / 2 := by rw [hl]; ring
  rw [hlh2] at h14
  have hpos : 0 < (l + 1) / 2 / 2 := by positivity
  have key : 1 / 6 * qE * (1 - 12 / (l * (l + 1))) - d
      = -((l + 1) / 2 / 2 * (d - qE / 6) + qE / (2 * l)) / ((l + 1) / 2 / 2) := by
    field_simp; ring
  have hnum : 0 ≤ (l + 1) / 2 / 2 * (d - qE / 6) + qE / (2 * l) := by linarith
  have : 1 / 6 * qE * (1 - 12 / (l * (l + 1))) - d ≤ 0 := by
    rw [key]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le
  linarith

/-- Substituting (1.6) into (1.4): the inequality is equivalent to `0 ≤ d`, which Scholze and
Stix call "essentially free of content". The `q` terms cancel exactly. -/
theorem consequence_without_squares {lh : ℕ} (hlh : 1 ≤ lh) (l d qE : ℝ) :
    -(qE / (2 * l)) ≤ thetaWithoutSquares lh l d qE ↔ 0 ≤ d := by
  rw [display_1_6 hlh]
  have hpos : (0 : ℝ) < ((lh : ℝ) + 1) / 2 := by positivity
  constructor
  · intro h
    have : 0 ≤ ((lh : ℝ) + 1) / 2 * d := by linarith
    exact nonneg_of_mul_nonneg_right this hpos
  · intro h
    have : 0 ≤ ((lh : ℝ) + 1) / 2 * d := mul_nonneg hpos.le h
    linarith

end IUT.Audit.ScholzeStix
