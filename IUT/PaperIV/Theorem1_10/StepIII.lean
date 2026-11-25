import IUT.PaperIV.Theorem1_10.StepII

/-!
# IUT IV, Theorem 1.10, Step (iii): ramification indices and the arithmetic divisor `𝔰`

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, proof of Theorem 1.10, Step (iii),
pages 24 to 26 of the April 2020 manuscript, read from the extracted text and from the rendered
pages; every display formalized here was checked against the renders of pages 25 and 26.

This file is not a formalization of Step (iii). Step (iii) introduces the distinguished
valuations, the divisors `𝔰^{F_*}_{ADiv}`, `𝔰^≤_{ADiv}`, the conditions (D0) to (D7) and the
bounds (R1) to (R4) on ramification indices. The facts about the arithmetic objects (that the
conditions are equivalent, that (R1) to (R3) hold, that `log(𝔰^ℚ) ≤ 2·d_mod·D + log(2·3·5·l)`)
are taken as hypotheses. What is checked is the real arithmetic that the paper performs on them:

* (R1) to (R3) imply (R4) (`R4`);
* the bound `(1/p)·log(p) ≤ 1/2` for `p = l ≥ 5` (`step_iii_p_eq_l`);
* the chain `log(𝔰^ℚ) ≤ 2·d_mod·D + 5 + log(l)`, then `(4/l)·log(𝔰^ℚ) ≤ (8·d_mod/l)·D + 6`;
* the final display `(1 + 4/l)·log(𝔡^K) + (4/l)·log(𝔰^ℚ) ≤ (1 + 12·d_mod/l)·D + 2·log(l) + 52`,
  which needs `D ≥ 0` and `d_mod ≥ 1`.

Variables: `D = log(𝔡^{F_tpd}) + log(𝔣^{F_tpd})`, `d = d_mod`, `sQ = log(𝔰^ℚ)`,
`dK = log(𝔡^K)`, `e = e_mod`.
-/

namespace IUT.PaperIV.Theorem1_10

/-- **(R1) to (R3) imply (R4).** Let `v` be a valuation with ramification index `e_v ≥ 1` and residue
characteristic `p_v`. Suppose that either `p_v = l` and (R1) `e_v ≤ 2¹¹·3³·5·e_mod·l⁴`, or
(R2)/(R3) `e_v ≤ 2¹¹·3³·5·e_mod·l` (R3 is the stronger bound `e_v ≤ 2¹¹·3³·5·e_mod`, which implies
this one since `l ≥ 1`). If `e_v ≥ p_v - 1`, then `p_v ≤ 2¹²·3³·5·e_mod·l = e*_mod·l` and
`log(e_v) ≤ -3 + 4·log(e*_mod·l)`. -/
theorem R4 {ev pv e l : ℝ} (he : 1 ≤ e) (hl : 5 ≤ l) (hev : 1 ≤ ev)
    (hR : (pv = l ∧ ev ≤ 2 ^ 11 * 3 ^ 3 * 5 * e * l ^ 4) ∨ ev ≤ 2 ^ 11 * 3 ^ 3 * 5 * e * l)
    (hram : pv - 1 ≤ ev) :
    pv ≤ 2 ^ 12 * 3 ^ 3 * 5 * e * l ∧
      Real.log ev ≤ -3 + 4 * Real.log (2 ^ 12 * 3 ^ 3 * 5 * e * l) := by
  set c : ℝ := 2 ^ 11 * 3 ^ 3 * 5 with hc
  have hc1 : 3 ≤ c := by norm_num [hc]
  have hlogc : 1 ≤ Real.log c := le_trans one_le_log_three (Real.log_le_log (by norm_num) hc1)
  have hl0 : 0 < l := by linarith
  have he0 : 0 < e := by linarith
  have e2 : (2 : ℝ) ^ 12 * 3 ^ 3 * 5 * e * l = 2 * c * e * l := by rw [hc]; ring
  rw [e2]
  have hL : Real.log (2 * c * e * l) = Real.log 2 + Real.log c + Real.log e + Real.log l := by
    rw [Real.log_mul (by positivity) hl0.ne', Real.log_mul (by positivity) he0.ne',
      Real.log_mul (by norm_num) (by positivity)]
  have hloge : 0 ≤ Real.log e := Real.log_nonneg he
  have hlogl : 0 ≤ Real.log l := Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rcases hR with ⟨hp, hR1⟩ | hR2
  · refine ⟨by rw [hp]; nlinarith, ?_⟩
    have h1 : Real.log ev ≤ Real.log (c * e * l ^ 4) := Real.log_le_log (by linarith) hR1
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) he0.ne',
      Real.log_pow] at h1
    rw [hL]; push_cast at h1; nlinarith
  · have hcel : 1 ≤ c * e * l := by nlinarith
    refine ⟨by nlinarith, ?_⟩
    have h1 : Real.log ev ≤ Real.log (c * e * l) := Real.log_le_log (by linarith) hR2
    rw [Real.log_mul (by positivity) hl0.ne', Real.log_mul (by positivity) he0.ne'] at h1
    rw [hL]; nlinarith

/-- Second display of Step (iii): for `p_{v_ℚ} = l ≥ 5`, `(1/p)·log(p) ≤ 1/2`. -/
theorem step_iii_p_eq_l {l : ℝ} (hl : 5 ≤ l) : 1 / l * Real.log l ≤ 1 / 2 := by
  have := log_div_le_half (by linarith : (0 : ℝ) < l)
  rwa [one_div_mul_eq_div]

/-- Step (iii), the chain on `log(𝔰^ℚ)`. Input: `log(𝔰^ℚ) ≤ 2·d_mod·D + log(2·3·5·l)`, which the
paper takes from Proposition 1.3 (i). Conclusions: `log(𝔰^ℚ) ≤ 2·d_mod·D + 5 + log(l)` and
`(4/l)·log(𝔰^ℚ) ≤ (8·d_mod/l)·D + 6` ("cf. (E6); the fact that `l ≥ 5`"). -/
theorem step_iii_sQ {sQ d D l : ℝ} (hl : 5 ≤ l)
    (h : sQ ≤ 2 * d * D + Real.log (2 * 3 * 5 * l)) :
    sQ ≤ 2 * d * D + 5 + Real.log l ∧ 4 / l * sQ ≤ 8 * d / l * D + 6 := by
  have hl0 : 0 < l := by linarith
  have h1 : sQ ≤ 2 * d * D + 5 + Real.log l := by linarith [log_30_mul_le hl0]
  refine ⟨h1, ?_⟩
  have h4 : 0 ≤ 4 / l := by positivity
  have := mul_le_mul_of_nonneg_left h1 h4
  have e1 : 4 / l * (2 * d * D + 5 + Real.log l) = 8 * d / l * D + 20 / l + 4 / l * Real.log l := by
    field_simp; ring
  have h20 : 20 / l ≤ 4 := by rw [div_le_iff₀ hl0]; linarith
  have hlog : 4 / l * Real.log l ≤ 2 := by
    have := two_log_le_self hl0
    rw [div_mul_eq_mul_div, div_le_iff₀ hl0]; linarith
  linarith

/-- **Final display of Step (iii).** From the final display of Step (ii) and the bound on
`(4/l)·log(𝔰^ℚ)`:
`(1 + 4/l)·log(𝔡^K) + (4/l)·log(𝔰^ℚ) ≤ (1 + 12·d_mod/l)·D + 2·log(l) + 52`.
The paper applies `d_mod ≥ 1`; the step `4/l·D ≤ 4·d_mod/l·D` also needs `D ≥ 0`, which holds
because `D` is a sum of degrees of effective arithmetic divisors. -/
theorem step_iii_final {dK sQ d D l : ℝ} (hl : 5 ≤ l) (hd : 1 ≤ d) (hD : 0 ≤ D)
    (hii : (1 + 4 / l) * dK ≤ (1 + 4 / l) * D + 2 * Real.log l + 46)
    (hs : 4 / l * sQ ≤ 8 * d / l * D + 6) :
    (1 + 4 / l) * dK + 4 / l * sQ ≤ (1 + 12 * d / l) * D + 2 * Real.log l + 52 := by
  have hl0 : 0 < l := by linarith
  have h : (1 + 4 / l) * D + 8 * d / l * D ≤ (1 + 12 * d / l) * D := by
    have : 4 / l ≤ 4 * d / l := div_le_div_of_nonneg_right (by linarith) hl0.le
    have e : (1 + 12 * d / l) * D = (1 + 4 * d / l) * D + 8 * d / l * D := by ring
    rw [e]; nlinarith
  linarith

end IUT.PaperIV.Theorem1_10
