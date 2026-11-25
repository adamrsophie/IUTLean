import IUT.PaperIV.Theorem1_10.ElementaryFacts

/-!
# IUT IV, Theorem 1.10, Step (ii): the bounds on differents and conductors

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, proof of Theorem 1.10, Step (ii),
page 24 of the April 2020 manuscript, read from the extracted text and from the rendered page;
every display formalized here was checked against the render.

This file is not a formalization of Step (ii). Step (ii) derives three inequalities between the
quantities `log(𝔡^{F_tpd}) + log(𝔣^{F_tpd})`, `log(𝔡^F) + log(𝔣^F)` and `log(𝔡^K)` from
Proposition 1.3 and from facts about the Galois groups `Gal(F/F_tpd)`, `Gal(K/F)`. Those local
field inputs are not formalized. Here every quantity is a real variable and the inputs are
hypotheses; what is checked is that the constants `21` and `46` of the paper follow from them.

Variables: `Dtpd = log(𝔡^{F_tpd}) + log(𝔣^{F_tpd})`, `DF = log(𝔡^F) + log(𝔣^F)`,
`dK = log(𝔡^K)`, `fK = log(𝔣^K)`.
-/

namespace IUT.PaperIV.Theorem1_10

/-- Second display of Step (ii). Input (the paper's application of Proposition 1.3 at the
primes dividing `2·3·5` and not dividing it): `DF ≤ Dtpd + log(2¹¹·3³·5²)`. Conclusion:
`DF ≤ Dtpd + 21`. -/
theorem step_ii_F {Dtpd DF : ℝ} (h : DF ≤ Dtpd + Real.log (2 ^ 11 * 3 ^ 3 * 5 ^ 2)) :
    DF ≤ Dtpd + 21 := by
  linarith [log_E_ii]

/-- Third display of Step (ii). Inputs: `log(𝔣^K) ≥ 0`, the bound
`log(𝔡^K) + log(𝔣^K) ≤ DF + 2·log(l)` that the paper takes from Proposition 1.3 and
`Gal(K/F) ↪ GL₂(𝔽_l)`, and the second display. Conclusion:
`log(𝔡^K) ≤ Dtpd + 2·log(l) + 21`. -/
theorem step_ii_K {Dtpd DF dK fK l : ℝ} (hf : 0 ≤ fK)
    (hK : dK + fK ≤ DF + 2 * Real.log l)
    (hF : DF ≤ Dtpd + Real.log (2 ^ 11 * 3 ^ 3 * 5 ^ 2)) :
    dK ≤ Dtpd + 2 * Real.log l + 21 := by
  linarith [step_ii_F hF]

/-- Final display of Step (ii):
`(1 + 4/l)·log(𝔡^K) ≤ (1 + 4/l)·Dtpd + 2·log(l) + 46`, using `log(l)/l ≤ 1/2` and
`1 + 4/l ≤ 2`, "consequences of the fact that `l ≥ 5`". -/
theorem step_ii_final {Dtpd dK l : ℝ} (hl : 5 ≤ l) (h : dK ≤ Dtpd + 2 * Real.log l + 21) :
    (1 + 4 / l) * dK ≤ (1 + 4 / l) * Dtpd + 2 * Real.log l + 46 := by
  have hl0 : 0 < l := by linarith
  have hc : 0 ≤ 1 + 4 / l := by positivity
  have h2 := one_add_four_div_le_two (by linarith : (4 : ℝ) ≤ l)
  have hlog : 4 / l * (2 * Real.log l) ≤ 4 := by
    have := two_log_le_self hl0
    rw [div_mul_eq_mul_div, div_le_iff₀ hl0]; linarith
  have := mul_le_mul_of_nonneg_left h hc
  nlinarith

end IUT.PaperIV.Theorem1_10
