import Mathlib

/-!
# Scholze–Stix, Section 1.2: from Claim 6 to Vojta's inequality, as real analysis

Source: P. Scholze and J. Stix, *Why abc is still a conjecture*, manuscript dated July 16,
2018, Section 1.2, pages 2 and 3 (displays (1.2), (1.3), Claim 6, and the two displays after
it). Read in full; the formulas were checked against the rendered pages 2 and 3.

**Whose argument.** This is the reduction that Scholze and Stix write down to explain why
Claim 6 (their summary of IUT IV, Theorem 1.10) would imply the uniform Vojta inequality for
elliptic curves, and hence abc. Neither side disputes this step. Mochizuki's comments on the
2018-08 version, item (C1), pages 1 and 2, concern the justification of Remark 5 (page 3),
which Scholze and Stix invoke for the final `O(1)`.

**What this file is not.** It is not a formalization of Claim 6, of IUT IV, Theorem 1.10, of
the Belyi reduction, of heights, or of Faltings' theorem. Every arithmetic quantity
(`h(P)`, `deg(q_E)`, `d(P) + n¹_∞(P)`, `ℓ(P)`) is an arbitrary real number or natural number
attached to an index `P`, and (1.2), (1.3), Claim 6 are hypotheses. The file checks only the
real analysis that turns those hypotheses into the conclusion. It does not settle the dispute,
which concerns whether Claim 6 is proved.

**Hypotheses, stated exactly.** For an index type `ι` (the curves `E/k` "as above"), with
`hgt P = h(P)`, `Q P = (1/6) deg(q_E)`, `N P = d(P) + n¹_∞(P)`, `ℓ P = ℓ(P)`:

* (1.2), upper half, as Scholze and Stix use it: `h ≤ Q + c (h^{1/2} + 1)` with `c > 0`;
* (1.3): `h^{1/2} ≤ ℓ ≤ h^{1/2} (c₁ + c₂ log h)` with `c₁, c₂ > 0`;
* Claim 6: `Q ≤ (1 + α(ℓ)) N + β(ℓ) ℓ`, with `α(ℓ) → 0` and `β` bounded for large `ℓ`;
* `h > 0` and `N ≥ 0`. These two are not displayed in the manuscript. `N ≥ 0` holds for the
  intended quantities (a log root discriminant and a log conductor are nonnegative) and is
  needed in the step "we conclude Vojta's inequality"; without it the step fails.

**Two observations recorded by this file (assessment of this project, not of either party).**

1. The display after Claim 6 uses `β_d(ℓ) ℓ ≤ β_d(ℓ) h^{1/2} (c₁ + c₂ log h)`, which needs
   `β_d(ℓ) ≥ 0`. The manuscript only says `β_d(ℓ) = O_d(1)`. This is harmless: Claim 6 with
   `β` implies Claim 6 with `|β|`, and `display_after_claim6_abs` proves the display with `|β|`.
2. The final `O(1)` does not need the finiteness statement of Remark 5. Once Vojta's
   inequality holds for `h(P) ≥ H`, the points with `h(P) < H` satisfy
   `h(P) < H ≤ (1 + ε) N + H` because `N ≥ 0`. See `vojta_of_claim6`, which uses no
   finiteness hypothesis: the only property of `N = d(P) + n¹_∞(P)` (the different plus
   conductor term) that it uses is the lower bound `N ≥ 0`. So the dispute in Mochizuki's
   comment (C1) on Remark 5 does not affect the validity of this reduction.
3. Remark 5 asserts finiteness of the curves `E/k` "as above" (over the varying fields `k`
   with `[k : ℚ] ≤ d`) with `h(P) ≤ b`, via Faltings' theorem and finite fibers of the Weil
   restriction. Comment (C1) argues through the `j`-invariant and finiteness of algebraic
   numbers of bounded degree and bounded height (Northcott's theorem). That argument controls
   the moduli values `j(E)`; it does not by itself give finiteness of curves, since infinitely
   many quadratic twists over `ℚ` share one `j`-invariant. Any claim about curves, or about the
   fibers of `E/k ↦ R_{k/ℚ}(E)`, needs its own argument using the restrictions "as above". This
   file needs neither.
-/

namespace IUT.Audit.ScholzeStix

open Filter Topology Real

/-- The display after Claim 6 (page 3), for one point, assuming `β ≥ 0`:
`h · (1 − (c (1 + h^{−1/2}) + β (c₁ + c₂ log h)) / h^{1/2}) ≤ (1 + α) N`.
Hypotheses: `h12` is (1.2) in the form Scholze and Stix use, `hC6` is Claim 6, `h13` is the
upper half of (1.3). -/
theorem display_after_claim6 {h Q N ℓ α β c c₁ c₂ : ℝ} (hh : 0 < h) (hβ : 0 ≤ β)
    (h12 : h ≤ Q + c * (√h + 1)) (hC6 : Q ≤ (1 + α) * N + β * ℓ)
    (h13 : ℓ ≤ √h * (c₁ + c₂ * Real.log h)) :
    h * (1 - (c * (1 + (√h)⁻¹) + β * (c₁ + c₂ * Real.log h)) / √h) ≤ (1 + α) * N := by
  have hs : 0 < √h := Real.sqrt_pos.mpr hh
  have hss : √h * √h = h := Real.mul_self_sqrt hh.le
  have hβℓ : β * ℓ ≤ β * (√h * (c₁ + c₂ * Real.log h)) := mul_le_mul_of_nonneg_left h13 hβ
  have e : ∀ X : ℝ, h * (X / √h) = X * √h := fun X => by
    rw [mul_div_assoc', mul_comm, mul_div_assoc, Real.div_sqrt]
  have hinv : (√h)⁻¹ * √h = 1 := inv_mul_cancel₀ hs.ne'
  have key : h * (1 - (c * (1 + (√h)⁻¹) + β * (c₁ + c₂ * Real.log h)) / √h)
      = h - c * √h - c - β * (√h * (c₁ + c₂ * Real.log h)) := by
    rw [mul_sub, mul_one, e]; linear_combination (-c) * hinv
  rw [key]; linarith

/-- The same display with `|β|` in place of `β`, for arbitrary real `β`. Claim 6 with `β`
implies Claim 6 with `|β|` because `ℓ ≥ 0`. -/
theorem display_after_claim6_abs {h Q N ℓ α β c c₁ c₂ : ℝ} (hh : 0 < h) (hℓ : 0 ≤ ℓ)
    (h12 : h ≤ Q + c * (√h + 1)) (hC6 : Q ≤ (1 + α) * N + β * ℓ)
    (h13 : ℓ ≤ √h * (c₁ + c₂ * Real.log h)) :
    h * (1 - (c * (1 + (√h)⁻¹) + |β| * (c₁ + c₂ * Real.log h)) / √h) ≤ (1 + α) * N := by
  have : β * ℓ ≤ |β| * ℓ := mul_le_mul_of_nonneg_right (le_abs_self β) hℓ
  exact display_after_claim6 hh (abs_nonneg β) h12 (by linarith) h13

/-- The step "we conclude Vojta's inequality" (page 3), for one point: if `h · M ≤ (1 + α) N`
and `0 < 1 + α < M (1 + ε)` with `ε > 0`, and `N ≥ 0`, then `h ≤ (1 + ε) N`. Here `M` stands
for the factor `1 − (…)/h^{1/2}` of the previous display. -/
theorem vojta_pointwise {h N α ε M : ℝ} (hε : 0 < ε) (hN : 0 ≤ N)
    (hdisp : h * M ≤ (1 + α) * N) (hα : 0 < 1 + α) (hlt : 1 + α < M * (1 + ε)) :
    h ≤ (1 + ε) * N := by
  have hM : 0 < M := by
    by_contra hM; have hM' := not_lt.mp hM; nlinarith
  have h1 : (1 + α) * N ≤ M * (1 + ε) * N := mul_le_mul_of_nonneg_right hlt.le hN
  have h2 : h * M ≤ (1 + ε) * N * M := by nlinarith
  exact le_of_mul_le_mul_right h2 hM

/-- `h^{-1/2} → 0` and `log h · h^{-1/2} → 0` as `h → ∞`. -/
private theorem tendsto_inv_sqrt : Tendsto (fun h : ℝ => (√h)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_sqrt_atTop

private theorem tendsto_log_mul_inv_sqrt :
    Tendsto (fun h : ℝ => Real.log h * (√h)⁻¹) atTop (𝓝 0) := by
  have h1 := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).tendsto_div_nhds_zero
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with h hh
  rw [Real.sqrt_eq_rpow, div_eq_mul_inv]

/-- The error term `(c (1 + h^{−1/2}) + B (c₁ + c₂ log h)) / h^{1/2}` tends to `0`. -/
private theorem tendsto_error (c B c₁ c₂ : ℝ) :
    Tendsto (fun h : ℝ => (c * (1 + (√h)⁻¹) + B * (c₁ + c₂ * Real.log h)) / √h) atTop
      (𝓝 0) := by
  have hu := tendsto_inv_sqrt
  have hl := tendsto_log_mul_inv_sqrt
  have : Tendsto (fun h : ℝ => c * (√h)⁻¹ + c * ((√h)⁻¹ * (√h)⁻¹) + B * c₁ * (√h)⁻¹
      + B * c₂ * (Real.log h * (√h)⁻¹)) atTop (𝓝 0) := by
    have := ((((hu.const_mul c).add ((hu.mul hu).const_mul c)).add (hu.const_mul (B * c₁))).add
      (hl.const_mul (B * c₂)))
    simpa using this
  refine this.congr' (Eventually.of_forall fun h => ?_)
  simp only [div_eq_mul_inv]; ring

/-- **The reduction of Section 1.2.** Scholze and Stix: "the inequalities of Claim 6 and
(1.3) yield [the display]. … As soon as for large `h(P)` … we conclude Vojta's inequality
`h(P) ≤ (1 + ε)(d(P) + n¹_∞(P)) + O_{ε,d}(1)`."

Hypotheses, uniform over the index type `ι`: `hgt P > 0`, `N P ≥ 0`, (1.2) as used,
(1.3), and Claim 6 with `α ℓ → 0` and `|β ℓ| ≤ B` for `ℓ ≥ L₀`. Conclusion: for every
`ε > 0` there is a constant `C` with `hgt P ≤ (1 + ε) N P + C` for all `P`. No finiteness
hypothesis (Remark 5) is used. -/
theorem vojta_of_claim6 {ι : Type*} (hgt Q N : ι → ℝ) (ℓ : ι → ℕ) (α β : ℕ → ℝ)
    {c c₁ c₂ : ℝ} (hpos : ∀ P, 0 < hgt P) (hN : ∀ P, 0 ≤ N P)
    (h12 : ∀ P, hgt P ≤ Q P + c * (√(hgt P) + 1))
    (h13lo : ∀ P, √(hgt P) ≤ ℓ P)
    (h13hi : ∀ P, (ℓ P : ℝ) ≤ √(hgt P) * (c₁ + c₂ * Real.log (hgt P)))
    (hC6 : ∀ P, Q P ≤ (1 + α (ℓ P)) * N P + β (ℓ P) * ℓ P)
    (hα : Tendsto α atTop (𝓝 0)) (hβ : ∃ B L₀, ∀ n ≥ L₀, |β n| ≤ B) :
    ∀ ε > 0, ∃ C : ℝ, ∀ P, hgt P ≤ (1 + ε) * N P + C := by
  intro ε hε
  obtain ⟨B, L₀, hB⟩ := hβ
  -- `δ` with `1 + δ < (1 − δ)(1 + ε)`.
  set δ : ℝ := ε / (2 * (2 + ε)) with hδdef
  have hδ : 0 < δ := by positivity
  have hδ1 : δ < 1 := by rw [hδdef, div_lt_one (by positivity)]; linarith
  have hδε : 1 + δ < (1 - δ) * (1 + ε) := by
    have : δ * (2 + ε) < ε := by
      rw [hδdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
    nlinarith
  -- threshold for `α`
  obtain ⟨L₁, hL₁⟩ := Metric.tendsto_atTop.mp hα δ hδ
  -- threshold for the error term, with `B' = max B 0`
  set B' := max B 0
  have hB' : ∀ n ≥ L₀, |β n| ≤ B' := fun n hn => (hB n hn).trans (le_max_left _ _)
  obtain ⟨H₁, hH₁⟩ := eventually_atTop.mp
    ((tendsto_error c B' c₁ c₂).eventually (gt_mem_nhds hδ))
  set H : ℝ := max (max H₁ 1) (max ((L₀ : ℝ) ^ 2) ((L₁ : ℝ) ^ 2))
  refine ⟨H, fun P => ?_⟩
  have hNP := hN P
  have hH1 : 1 ≤ H := (le_max_right _ _).trans (le_max_left _ _)
  rcases lt_or_ge (hgt P) H with hsmall | hlarge
  · nlinarith
  -- the large case
  set h := hgt P
  have hh := hpos P
  have hs : 0 < √h := Real.sqrt_pos.mpr hh
  have hsq : ∀ L : ℕ, (L : ℝ) ^ 2 ≤ H → L ≤ ℓ P := by
    intro L hL
    have : (L : ℝ) ≤ √h := by
      rw [← Real.sqrt_sq (Nat.cast_nonneg L)]
      exact Real.sqrt_le_sqrt (hL.trans hlarge)
    exact_mod_cast this.trans (h13lo P)
  have hℓL₀ : L₀ ≤ ℓ P := hsq L₀ ((le_max_left _ _).trans (le_max_right _ _))
  have hℓL₁ : L₁ ≤ ℓ P := hsq L₁ ((le_max_right _ _).trans (le_max_right _ _))
  have hαδ : |α (ℓ P)| < δ := by simpa [Real.dist_eq] using hL₁ (ℓ P) hℓL₁
  have hβB : |β (ℓ P)| ≤ B' := hB' _ hℓL₀
  have herr : (c * (1 + (√h)⁻¹) + B' * (c₁ + c₂ * Real.log h)) / √h < δ :=
    hH₁ h ((le_max_left _ _).trans ((le_max_left _ _).trans hlarge))
  -- the display, with `|β|`
  have hdisp := display_after_claim6_abs hh (Nat.cast_nonneg _) (h12 P) (hC6 P) (h13hi P)
  -- compare `|β|` with `B'`; needs `c₁ + c₂ log h ≥ 0`, which follows from (1.3)
  have hlogfac : 0 ≤ c₁ + c₂ * Real.log h := by
    have := (h13lo P).trans (h13hi P)
    by_contra hneg; have hneg := not_le.mp hneg
    have : √h * (c₁ + c₂ * Real.log h) < 0 := mul_neg_of_pos_of_neg hs hneg
    linarith
  have hcmp : (c * (1 + (√h)⁻¹) + |β (ℓ P)| * (c₁ + c₂ * Real.log h)) / √h
      ≤ (c * (1 + (√h)⁻¹) + B' * (c₁ + c₂ * Real.log h)) / √h := by
    apply div_le_div_of_nonneg_right _ hs.le
    nlinarith [mul_le_mul_of_nonneg_right hβB hlogfac]
  set M := 1 - (c * (1 + (√h)⁻¹) + |β (ℓ P)| * (c₁ + c₂ * Real.log h)) / √h
  have hM : 1 - δ ≤ M := by simp only [M]; linarith
  have hαlt := abs_lt.mp hαδ
  refine le_trans (vojta_pointwise hε hNP hdisp (by linarith) ?_) (by linarith)
  calc 1 + α (ℓ P) < 1 + δ := by linarith
    _ < (1 - δ) * (1 + ε) := hδε
    _ ≤ M * (1 + ε) := by nlinarith

end IUT.Audit.ScholzeStix
