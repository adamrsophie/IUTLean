import Mathlib

/-!
# IUT IV, Proposition 1.3: estimates of differents (elementary part)

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Proposition 1.3 and its proof,
pages 11 to 13 of the April 2020 manuscript, read from the extracted text and from the rendered
pages 11, 12 and 13; the displays formalized here were checked against the renders.

Statement of the paper (with `d_i`, `d_0` the orders of generators of the differents of `k_i`,
`k_0` over `ℚ_p`, `e_0` the ramification index of `k_0`, `e_{i/0} = e_i/e_0`, `n_i` the `p`-adic
valuation of `[k_i : k_0]`):

* (i) `d_i ≥ d_0 + (e_{i/0} - 1)/(e_{i/0}·e_0) = d_0 + (e_{i/0} - 1)/e_i`, with equality when
  `k_i/k_0` is tamely ramified;
* (ii) if `k_i` is Galois over some `k_1 ⊇ k_0` with `k_1/k_0` tame, then
  `d_i ≤ d_0 + n_i + 1/e_0`.

This file is not a formalization of Proposition 1.3. The proof computes differents through
Eisenstein and Kummer polynomials over local rings, which needs local field theory not
formalized here. On the papers' objects over a general base, the inequality of (i), its tame
equality and (ii) in the tame and `n_i = 0` cases are proved in
`IUT/PaperIV/LocalFields/Tower.lean`. This file checks the arithmetic of the proof:

* the minimum in the display of (i) (`i_min`);
* the base case `n_i = 0` of the induction in (ii), i.e. that (i) with equality gives
  `d_i ≤ d_0 + 1/e_0` (`ii_base`);
* the chain of the inductive step of (ii) (`ii_step`), and the passage "it suffices to verify
  `d_i ≤ d_0 + n_i + 1/e_0 + ε` for every `ε > 0`" (`ii_of_forall_eps`).
-/

namespace IUT.PaperIV.Proposition1_3

/-- The minimum in the proof of (i): for integers `e' = e_{i/0} ≥ 1`, `e_0 ≥ 1`,
`(e' - 1)/(e'·e_0) ≤ 1/e_0`, so `min(1/e_0, (e' - 1)/(e'·e_0)) = (e' - 1)/(e'·e_0)`, and this
equals `(e' - 1)/e_i` with `e_i = e'·e_0`. -/
theorem i_min {e' e0 : ℝ} (he' : 1 ≤ e') (he0 : 1 ≤ e0) :
    min (1 / e0) ((e' - 1) / (e' * e0)) = (e' - 1) / (e' * e0) := by
  apply min_eq_right
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The base case of the induction in (ii): if `d_i = d_0 + (e' - 1)/(e'·e_0)` (tame case of
(i)), then `d_i ≤ d_0 + 1/e_0`. -/
theorem ii_base {di d0 e' e0 : ℝ} (he' : 1 ≤ e') (he0 : 1 ≤ e0)
    (h : di = d0 + (e' - 1) / (e' * e0)) : di ≤ d0 + 1 / e0 := by
  have := i_min he' he0
  have h2 : (e' - 1) / (e' * e0) ≤ 1 / e0 := by rw [← this]; exact min_le_left _ _
  linarith

/-- **The inductive step of (ii)** (page 12). Inputs:

* `d_i ≤ ord(p·ϖ_i^{p-1}) + d_*` (different of the Kummer extension);
* `ord(p·ϖ_i^{p-1}) = 1 + (p-1)·ord(ϖ_i)`;
* the induction hypothesis `d_* ≤ d_0 + n_i - 1 + 1/e_0`;
* `ord(ϖ_i) ≤ (p-1)/(p·e_*)` (the paper also states `0 ≤ ord(ϖ_i)`, which is not needed),
  and `e_* ≥ p/ε`.

Conclusion: `d_i ≤ d_0 + n_i + 1/e_0 + ε`, via
`(p-1)·ord(ϖ_i) ≤ (p-1)²/(p·e_*) ≤ p/e_* ≤ ε`. -/
theorem ii_step {di dstar d0 n e0 p o estar ordpw ε : ℝ} (hp : 1 ≤ p) (hε : 0 < ε)
    (hestar : p / ε ≤ estar)
    (h1 : di ≤ ordpw + dstar) (hord : ordpw = 1 + (p - 1) * o)
    (hind : dstar ≤ d0 + n - 1 + 1 / e0)
    (ho : o ≤ (p - 1) / (p * estar)) :
    di ≤ d0 + n + 1 / e0 + ε := by
  have hp0 : 0 < p := by linarith
  have hes : 0 < estar := lt_of_lt_of_le (div_pos hp0 hε) hestar
  have h2 : (p - 1) * o ≤ (p - 1) ^ 2 / (p * estar) := by
    have := mul_le_mul_of_nonneg_left ho (by linarith : (0 : ℝ) ≤ p - 1)
    calc (p - 1) * o ≤ (p - 1) * ((p - 1) / (p * estar)) := this
      _ = (p - 1) ^ 2 / (p * estar) := by ring
  have h3 : (p - 1) ^ 2 / (p * estar) ≤ p / estar := by
    rw [div_le_div_iff₀ (by positivity) hes]; nlinarith
  have h4 : p / estar ≤ ε := by
    rw [div_le_iff₀ hes]; rw [div_le_iff₀ hε] at hestar; linarith
  linarith

/-- "It suffices to verify `d_i ≤ d_0 + n_i + 1/e_0 + ε` for every positive `ε`." -/
theorem ii_of_forall_eps {di X : ℝ} (h : ∀ ε : ℝ, 0 < ε → di ≤ X + ε) : di ≤ X :=
  le_of_forall_pos_le_add h

end IUT.PaperIV.Proposition1_3
