import Mathlib

/-!
# IUT IV, Theorem 1.10, Step (i): the elementary facts (E3), (E4), (E6) and numerical bounds

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, proof of Theorem 1.10, Step (i),
pages 23 and 24 of the April 2020 manuscript, and the numerical estimates the later steps quote
"as consequences of the fact that `l ≥ 5`" (pages 24, 26, 29). Pages 23, 24, 26 and 29 were read
from the extracted text and from the rendered pages; every display formalized here was checked
against the render.

This file is not a formalization of Theorem 1.10. It checks the elementary facts that the proof
recalls in Step (i), and the purely numerical inequalities that the later steps take from them:

* (E3) `|GL₂(𝔽_p)| = p(p+1)(p-1)²` for a prime `p` (`card_GL2`).
* (E4) the three values `2·3`, `3·2⁴`, `5·2⁵·3` (`E4`), and the product
  `|GL₂(𝔽₂)|·|GL₂(𝔽₃)|·|GL₂(𝔽₅)|·2 = 2¹¹·3³·5` that bounds `[F : F_mod]` (`E4_product`); the
  proof of Corollary 2.2 uses it to get `[F : ℚ] ≤ δ`.
* (E6) `0 ≤ log 2 ≤ 1`, `1 ≤ log 3 ≤ log π ≤ log 5 ≤ 2` (`E6`).
* `log(l)/l ≤ 1/2` and `1 + 4/l ≤ 2` for `l ≥ 5`, quoted in Step (ii); the first holds for all
  `l > 0` (`log_div_le_half`).
* `log(2¹¹·3³·5²) ≤ 21` (Step (ii)) and `log(2·3·5) ≤ 5` (Step (iii)).

(E5), the bound `[F_mod(√-1) : F_mod] ≤ 2`, is field theory and is not formalized here.
-/

namespace IUT.PaperIV.Theorem1_10

/-- (E3): `|GL₂(𝔽_p)| = p(p+1)(p-1)²` for a prime `p`. -/
theorem card_GL2 (p : ℕ) [hp : Fact p.Prime] :
    Nat.card (GL (Fin 2) (ZMod p)) = p * (p + 1) * (p - 1) ^ 2 := by
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_two]
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := hp.out.one_lt; omega⟩
  have h1 : (k + 1) ^ 2 - (k + 1) ^ ((0 : Fin 2) : ℕ) = k * (k + 2) := by
    simp only [Fin.val_zero, pow_zero]
    rw [show (k + 1) ^ 2 = k * (k + 2) + 1 by ring]; simp
  have h2 : (k + 1) ^ 2 - (k + 1) ^ ((1 : Fin 2) : ℕ) = (k + 1) * k := by
    simp only [Fin.val_one, pow_one]
    rw [show (k + 1) ^ 2 = (k + 1) * k + (k + 1) by ring]; simp
  rw [h1, h2]; simp only [Nat.add_sub_cancel]; ring

/-- (E4): the values of `p(p+1)(p-1)²` at `p = 2, 3, 5`. -/
theorem E4 :
    2 * (2 + 1) * (2 - 1) ^ 2 = 2 * 3 ∧ 3 * (3 + 1) * (3 - 1) ^ 2 = 3 * 2 ^ 4 ∧
      5 * (5 + 1) * (5 - 1) ^ 2 = 5 * 2 ^ 5 * 3 := by
  norm_num

/-- The product `|GL₂(𝔽₂)|·|GL₂(𝔽₃)|·|GL₂(𝔽₅)|·2 = 2¹¹·3³·5`, which bounds
`[F : F_mod]` via the outer inclusion `Gal(F/F_mod) ↪ GL₂(𝔽₂) × GL₂(𝔽₃) × GL₂(𝔽₅) × ℤ/2ℤ`
used in Step (ii) and in the proof of Corollary 2.2 ("`[F : ℚ] ≤ δ`, cf. (E3), (E4), (E5)"). -/
theorem E4_product : (2 * 3) * (3 * 2 ^ 4) * (5 * 2 ^ 5 * 3) * 2 = 2 ^ 11 * 3 ^ 3 * 5 := by
  norm_num

theorem log_two_le_one : Real.log 2 ≤ 1 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have := Real.add_one_le_exp (1 : ℝ); linarith

theorem one_le_log_three : 1 ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9; linarith

theorem log_five_le_two : Real.log 5 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have := Real.exp_one_gt_d9
  rw [h]; nlinarith

/-- (E6): `0 ≤ log(2) ≤ 1`, `1 ≤ log(3) ≤ log(π) ≤ log(5) ≤ 2`. -/
theorem E6 :
    0 ≤ Real.log 2 ∧ Real.log 2 ≤ 1 ∧ 1 ≤ Real.log 3 ∧ Real.log 3 ≤ Real.log Real.pi ∧
      Real.log Real.pi ≤ Real.log 5 ∧ Real.log 5 ≤ 2 := by
  refine ⟨Real.log_nonneg (by norm_num), log_two_le_one, one_le_log_three,
    Real.log_le_log (by norm_num) Real.pi_gt_three.le,
    Real.log_le_log Real.pi_pos (by linarith [Real.pi_lt_d2]), log_five_le_two⟩

/-- `log(l)/l ≤ 1/2`, quoted in Step (ii) as a consequence of `l ≥ 5`; it holds for every
`l > 0`. Stated without division: `2·log(l) ≤ l`. -/
theorem two_log_le_self {l : ℝ} (hl : 0 < l) : 2 * Real.log l ≤ l := by
  have hs : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
  have h1 : Real.log (Real.sqrt l) ≤ Real.sqrt l - 1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log (Real.sqrt l) = Real.log l / 2 := Real.log_sqrt hl.le
  have h3 : Real.sqrt l ^ 2 = l := Real.sq_sqrt hl.le
  nlinarith [sq_nonneg (Real.sqrt l - 2)]

theorem log_div_le_half {l : ℝ} (hl : 0 < l) : Real.log l / l ≤ 1 / 2 := by
  rw [div_le_iff₀ hl]; linarith [two_log_le_self hl]

/-- `1 + 4/l ≤ 2` for `l ≥ 4`, quoted in Step (ii) as a consequence of `l ≥ 5`. -/
theorem one_add_four_div_le_two {l : ℝ} (hl : 4 ≤ l) : 1 + 4 / l ≤ 2 := by
  have : 4 / l ≤ 1 := by rw [div_le_one (by linarith)]; exact hl
  linarith

/-- Step (ii): `log(2¹¹·3³·5²) ≤ 21`, from (E6): `11·1 + 3·2 + 2·2 = 21`. -/
theorem log_E_ii : Real.log (2 ^ 11 * 3 ^ 3 * 5 ^ 2) ≤ 21 := by
  have h3 : Real.log 3 ≤ 2 := by
    have := E6; linarith [this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2]
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  linarith [log_two_le_one, log_five_le_two]

/-- Step (iii): `log(2·3·5·l) ≤ 5 + log(l)` for `l > 0`, from (E6). -/
theorem log_30_mul_le {l : ℝ} (hl : 0 < l) : Real.log (2 * 3 * 5 * l) ≤ 5 + Real.log l := by
  have h3 : Real.log 3 ≤ 2 := by
    have := E6; linarith [this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2]
  rw [Real.log_mul (by norm_num) hl.ne', Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]
  linarith [log_two_le_one, log_five_le_two]

end IUT.PaperIV.Theorem1_10
