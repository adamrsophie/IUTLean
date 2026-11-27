import Mathlib

/-!
# IUT IV, Theorem 1.10: the elementary real arithmetic of the proof

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Theorem 1.10 and its proof,
pages 22 to 31 of the April 2020 manuscript. The displays formalized here were read from the
rendered pages 23, 30 and 31.

This file checks the parts of that proof that are plain manipulations of real numbers. It
does not construct any of the arithmetic objects. Every quantity of the paper is a real
variable here:

* `l` the prime `l`, as a real number;
* `d` the degree `d_mod`;
* `D` the sum `log(𝔡^{F_tpd}) + log(𝔣^{F_tpd})`;
* `E` the sum `e*_mod · l + η_prm`;
* `Q` the quantity `log(𝔮)`;
* `q` the quantity `|log(q)|`, which the paper states equals `Q / (2 l)`;
* `L` the quantity `l*_mod · log(𝔰^≤)` of Step (viii).

What is proved: given the hypotheses on these numbers that the paper derives elsewhere, the
conclusions the paper draws from them by "applying the estimate ..." do follow. What is not
proved here: that the arithmetic objects of the paper satisfy those hypotheses.

## Limits

`final_inequality` and `final_inequality_F` combine supplied inequalities between free real
numbers. Their conclusions have the shape of the final inequality of Theorem 1.10, but no
height, divisor, conductor or log-volume occurs in them: they show only that the passage from
the supplied inequalities to that shape is correct arithmetic. Neither gives any information
about `log(𝔮)` of an actual elliptic curve.
-/

namespace IUT.PaperIV.Theorem1_10

/-- The value of `C_Θ` displayed in the statement of Theorem 1.10 (page 23):
`(l+1)/(4·|log(q)|) · {(1 + 12·d_mod/l)·(log 𝔡 + log 𝔣) + 10·(e*_mod·l + η_prm)
  − (1/6)·(1 − 12/l²)·log(𝔮)} − 1`.
The two `q`-quantities are distinct arguments: `Q` stands for `log(𝔮)`, the normalized degree of
the `q`-parameter divisor, and `q` stands for `|log(q)|`, the absolute value of the `q`-pilot
log-volume of IUT III, Corollary 3.12, which page 23 states equals `log(𝔮)/(2l)`. The relation
`q = Q/(2l)` is not built into the definition; the theorems that need it take it as a
hypothesis (`constant_bound_of_raw`, `step_viii_constant`). -/
noncomputable def constant (l d D E Q q : ℝ) : ℝ :=
  (l + 1) / (4 * q) * ((1 + 12 * d / l) * D + 10 * E - 1 / 6 * (1 - 12 / l ^ 2) * Q) - 1

/-! ## The identities (E1) and (E2) of Step (i) -/

/-- (E1): `(1/n) · ∑_{m=1}^{n} m = (n + 1)/2`. -/
theorem E1 (n : ℕ) (hn : 1 ≤ n) :
    (1 / (n : ℝ)) * ∑ m ∈ Finset.Icc 1 n, (m : ℝ) = (n + 1) / 2 := by
  have h : ∀ k : ℕ, ∑ m ∈ Finset.Icc 1 k, (m : ℝ) = k * (k + 1) / 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; push_cast; ring
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [h]; field_simp

/-- (E2): `(1/n) · ∑_{m=1}^{n} m² = (2n + 1)(n + 1)/6`. -/
theorem E2 (n : ℕ) (hn : 1 ≤ n) :
    (1 / (n : ℝ)) * ∑ m ∈ Finset.Icc 1 n, (m : ℝ) ^ 2 = (2 * n + 1) * (n + 1) / 6 := by
  have h : ∀ k : ℕ, ∑ m ∈ Finset.Icc 1 k, (m : ℝ) ^ 2 = k * (k + 1) * (2 * k + 1) / 6 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; push_cast; ring
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [h]; field_simp

/-! ## Step (vii): the archimedean bound -/

/-- Step (vii), final display: `(l+5)/4 · log π ≤ (l+1)/4 · 4`, "cf. the fact that `l ≥ 5`". -/
theorem step_vii_archimedean {l : ℝ} (hl : 5 ≤ l) :
    (l + 5) / 4 * Real.log Real.pi ≤ (l + 1) / 4 * 4 := by
  have h1 : Real.log Real.pi ≤ Real.pi - 1 := Real.log_le_sub_one_of_pos Real.pi_pos
  have h2 : Real.pi < 3.15 := Real.pi_lt_d2
  have h3 : Real.log Real.pi ≤ 2.15 := by linarith
  nlinarith

/-! ## Step (viii): from the summed local bounds to the constant of the statement -/

/-- Step (viii): "we apply the estimate `(l+1)/4 · 1/6 · 12/l² ≥ 1/(2l)` [cf. the fact that
`l ≥ 1`]". The estimate in fact holds for every `l > 0`. -/
theorem step_viii_estimate {l : ℝ} (hl : 0 < l) :
    1 / (2 * l) ≤ (l + 1) / 4 * (1 / 6) * (12 / l ^ 2) := by
  rw [div_le_iff₀ (by positivity)]
  have : (l + 1) / 4 * (1 / 6) * (12 / l ^ 2) * (2 * l) = (l + 1) / l := by field_simp; ring
  rw [this, le_div_iff₀ hl]; linarith

/-- Step (viii): `(1/3)·(4/3)·(e*_mod·l + η_prm) ≥ (1/3)·(4/3)·e*_mod·l ≥ 2·2·2¹²·3·5·l
≥ 2·log(l) + 56`, with `e*_mod = 2¹²·3³·5·e_mod`. The paper cites `e_mod ≥ 1`,
`2¹²·3·5 ≥ 56`, `l ≥ 5 ≥ 1`, `l ≥ log(l)`. Here `e` is `e_mod` and `η` is `η_prm`. -/
theorem step_viii_absorb {l e η : ℝ} (hl : 5 ≤ l) (he : 1 ≤ e) (hη : 0 ≤ η) :
    2 * Real.log l + 56 ≤ 1 / 3 * (4 / 3) * (2 ^ 12 * 3 ^ 3 * 5 * e * l + η) := by
  have hlog : Real.log l ≤ l - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hel : l ≤ e * l := by nlinarith
  nlinarith

/-- Step (viii), substitution: with `L ≤ (4/3)·E` (the consequence of Proposition 1.6 drawn in
the proof) and the bound of `step_viii_absorb`, the terms `2·log(l) + 56 + (20/3)·L` are at
most `10·E`. The paper's "estimate `(20+1)/3 · 4/3 = 7·4/3 ≤ 10`". -/
theorem step_viii_substitute {l L E : ℝ} (hL : L ≤ 4 / 3 * E)
    (habs : 2 * Real.log l + 56 ≤ 1 / 3 * (4 / 3) * E) (hE : 0 ≤ E) :
    2 * Real.log l + 56 + 20 / 3 * L ≤ 10 * E := by
  linarith

/-- Step (viii), conclusion. Let `X` be the quantity that the proof bounds, which the paper
calls `C_Θ · |log(q)|`. If `X` is at most the raw sum of the first display of Step (viii),
and `L ≤ (4/3)·E`, and the absorption bound holds, then `X / |log(q)|` is at most the constant
displayed in the statement of the theorem. Here `q = Q / (2l)` is `|log(q)|`. -/
theorem constant_bound_of_raw {l d D E Q q L X : ℝ} (hl : 0 < l) (hq : 0 < q)
    (hqQ : q = Q / (2 * l)) (hE : 0 ≤ E) (hL : L ≤ 4 / 3 * E)
    (habs : 2 * Real.log l + 56 ≤ 1 / 3 * (4 / 3) * E)
    (hraw : X ≤ (l + 1) / 4 * ((1 + 12 * d / l) * D + 2 * Real.log l + 56
      - 1 / 6 * (1 - 12 / l ^ 2) * Q + 20 / 3 * L) - 1 / (2 * l) * Q) :
    X / q ≤ constant l d D E Q q := by
  have hsub := step_viii_substitute hL habs hE
  have hpos : 0 < (l + 1) / 4 := by positivity
  have hX : X ≤ (l + 1) / 4 * ((1 + 12 * d / l) * D + 10 * E
      - 1 / 6 * (1 - 12 / l ^ 2) * Q) - q := by
    have hq' : 1 / (2 * l) * Q = q := by rw [hqQ]; ring
    rw [hq'] at hraw
    nlinarith
  unfold constant
  rw [div_le_iff₀ hq]
  have : ((l + 1) / (4 * q) * ((1 + 12 * d / l) * D + 10 * E
      - 1 / 6 * (1 - 12 / l ^ 2) * Q) - 1) * q
      = (l + 1) / 4 * ((1 + 12 * d / l) * D + 10 * E - 1 / 6 * (1 - 12 / l ^ 2) * Q) - q := by
    field_simp
  rw [this]; exact hX

/-! ## The final portion of the theorem -/

/-- First estimate cited at the end of the proof: `(1 − 12/l²)⁻¹ ≤ 2`, "cf. the fact that
`l ≥ 7`". -/
theorem final_estimate_one {l : ℝ} (hl : 7 ≤ l) : (1 - 12 / l ^ 2)⁻¹ ≤ 2 := by
  have hl2 : (49 : ℝ) ≤ l ^ 2 := by nlinarith
  have h12 : 12 / l ^ 2 ≤ 12 / 49 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hl2
  have hpos : (0 : ℝ) < 1 - 12 / l ^ 2 := by linarith
  rw [inv_le_comm₀ hpos (by norm_num)]
  linarith

/-- Second estimate cited at the end of the proof:
`(1 − 12/l²)⁻¹ · (1 + 12·d_mod/l) ≤ 1 + 20·d_mod/l`, "cf. the fact that `l ≥ 7`,
`d_mod ≥ 1`". -/
theorem final_estimate_two {l d : ℝ} (hl : 7 ≤ l) (hd : 1 ≤ d) :
    (1 - 12 / l ^ 2)⁻¹ * (1 + 12 * d / l) ≤ 1 + 20 * d / l := by
  have hl0 : (0 : ℝ) < l := by linarith
  have hl2 : (49 : ℝ) ≤ l ^ 2 := by nlinarith
  have h12 : 12 / l ^ 2 ≤ 12 / 49 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hl2
  have hpos : (0 : ℝ) < 1 - 12 / l ^ 2 := by linarith
  rw [inv_mul_le_iff₀ hpos]
  have key : (1 - 12 / l ^ 2) * (1 + 20 * d / l) - (1 + 12 * d / l)
      = (8 * d * l ^ 2 - 12 * l - 240 * d) / l ^ 3 := by field_simp; ring
  have hnum : 0 ≤ 8 * d * l ^ 2 - 12 * l - 240 * d := by nlinarith
  have : 0 ≤ (8 * d * l ^ 2 - 12 * l - 240 * d) / l ^ 3 := div_nonneg hnum (by positivity)
  linarith

/-- **The final portion of Theorem 1.10, as real arithmetic.** If the constant displayed in
the statement is at least `−1` (this is where the paper invokes the inequality `C_Θ ≥ −1` of
IUT III, Corollary 3.12), then
`(1/6)·log(𝔮) ≤ (1 + 20·d_mod/l)·(log 𝔡 + log 𝔣) + 20·(e*_mod·l + η_prm)`.

The hypotheses `7 ≤ l`, `1 ≤ d` are the facts the paper cites. `0 ≤ D` and `0 ≤ E` hold in
the paper because both are sums of nonnegative quantities. No sign condition on `Q` is
needed.

Limits: every argument is a free real number and `hC` is supplied, not derived; the theorem
is the arithmetic of the last step only. -/
theorem final_inequality {l d D E Q q : ℝ} (hl : 7 ≤ l) (hd : 1 ≤ d) (hD : 0 ≤ D)
    (hE : 0 ≤ E) (hq : 0 < q) (hC : -1 ≤ constant l d D E Q q) :
    1 / 6 * Q ≤ (1 + 20 * d / l) * D + 20 * E := by
  have hl0 : (0 : ℝ) < l := by linarith
  have hl2 : (49 : ℝ) ≤ l ^ 2 := by nlinarith
  have h12 : 12 / l ^ 2 ≤ 12 / 49 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hl2
  have ht : (0 : ℝ) < 1 - 12 / l ^ 2 := by linarith
  have hfac : 0 < (l + 1) / (4 * q) := by positivity
  unfold constant at hC
  have hS : 0 ≤ (1 + 12 * d / l) * D + 10 * E - 1 / 6 * (1 - 12 / l ^ 2) * Q := by
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_pos_of_neg hfac hneg
    linarith
  have h1 := final_estimate_one hl
  have h2 := final_estimate_two hl hd
  rw [inv_le_comm₀ ht (by norm_num)] at h1
  rw [inv_mul_le_iff₀ ht] at h2
  have hmul : (1 - 12 / l ^ 2) * (1 / 6 * Q)
      ≤ (1 - 12 / l ^ 2) * ((1 + 20 * d / l) * D + 20 * E) := by
    have e1 : (1 + 12 * d / l) * D ≤ (1 - 12 / l ^ 2) * (1 + 20 * d / l) * D :=
      mul_le_mul_of_nonneg_right h2 hD
    have e2 : 10 * E ≤ (1 - 12 / l ^ 2) * 20 * E := by nlinarith
    nlinarith
  exact le_of_mul_le_mul_left hmul ht

/-- The second line of the final display: replacing the `F_tpd` quantities by the `F`
quantities, given the inequality `D_tpd ≤ D_F` that the paper takes from "the first display
of Step (ii)".

Limits: `hstep_ii` and `h` are supplied inequalities between free real numbers; the theorem is
monotonicity in `D` and nothing else. -/
theorem final_inequality_F {l d Dtpd DF E Q : ℝ} (hl : 0 < l) (hd : 0 ≤ d)
    (hstep_ii : Dtpd ≤ DF) (h : 1 / 6 * Q ≤ (1 + 20 * d / l) * Dtpd + 20 * E) :
    1 / 6 * Q ≤ (1 + 20 * d / l) * DF + 20 * E := by
  have : 0 ≤ 1 + 20 * d / l := by positivity
  nlinarith

end IUT.PaperIV.Theorem1_10
