import IUT.Applications.VojtaNumberField
import IUT.PaperIV.LegendreFrey

/-!
# Height comparison on the `λ`-line

Sources: Mochizuki, *Inter-universal Teichmüller Theory IV*, Corollary 2.2 and the first part of
its proof (pages 41 to 43); Mochizuki, *Arithmetic Elliptic Curves in General Position*
([GenEll]), §1 (the normalized degree and heights, page 4; Definition 1.2, page 5;
Proposition 1.4, page 6; Definition 1.5, page 8; Proposition 1.6, page 9).
Pages read for this file: IUT IV pages 41 to 43; [GenEll] pages 4 to 6, 8 and 9. Pages checked
against rendered images: all of these. [GenEll] page 4 states that the normalized degree
`(1/[F : ℚ]) deg_F` is invariant under finite extension of `F`, so that `ht` is defined on
`X(ℚ̄)`; Definition 1.2 (ii) on page 5 prints `α ≲ β` as `β - α ≤ C`, a direction reversed by
the published correction (2) recorded in `IUT.Applications.VojtaNumberField`; the statements
below are explicit inequalities and do not use `≲`.

**What the pages print.** Corollary 2.2 (i) (page 41) asserts the equality of bounded discrepancy
classes `(1/6) log(𝔮^{†2}) ≈ (1/6) log(𝔮^∀) ≈ (1/6) ht_∞ ≈ ht_{ω_X(D)}` on a compactly bounded
subset `K_V` of `U_X(ℚ̄)`, `X = ℙ¹_ℚ` the `λ`-line of the Legendre form and `D = {0, 1, ∞}`, where
`ht_∞` is the normalized height of the pullback of the divisor at infinity of the compactified
moduli stack of elliptic curves. The proof (page 43) obtains the last equality from the fact
that this pullback has degree 6 while `ω_X(D)` has degree 1, citing [GenEll] Proposition 1.4
(i), (iii). The pages print no explicit inequality between heights and no constant; the
comparison with `1 - λ` or `1/λ` is not used on these pages. The comparison between `log(𝔮)`
and `ht_∞` (page 43) rests on the `q`-parameters of the elliptic curves at the nonarchimedean
primes and on condition `(*_{j-inv})` at the prime `2`.

**What this file proves.** Heights are `IUT.VojtaNumberField.heightNF` (Mathlib's
`Height.logHeight₁` divided by `[K : ℚ]`), and `j = IUT.LegendreFrey.legendreJ`, the
`j`-invariant `2⁸(λ² - λ + 1)³ / (λ²(λ - 1)²)` of the Legendre curve.

1. Height of the `j`-invariant (`htCmp_abs_heightNF_legendreJ_sub_le`): for every number field
   `K` and every `y ∈ K`, `|ht(j(y)) - 6 ht(y)| ≤ log 41 + 8 log 2 = log 10496`; one-sided forms
   `ht(j(y)) ≤ 6 ht(y) + log 27 + 8 log 2` and `6 ht(y) ≤ ht(j(y)) + log 41 + 8 log 2`. The
   constant is the same for all number fields (`htCmp_exists_uniform_constant`). At `y = 0, 1`
   both sides vanish (Lean's convention `x / 0 = 0`), so no hypothesis on `y` is needed. This is
   an explicit form, for the Weil heights of `j` and of `λ`, of the degree 6 comparison behind
   `(1/6) ht_∞ ≈ ht_{ω_X(D)}`. The proof works place by place over any field with Mathlib's
   `Height.AdmissibleAbsValues`: with `N = (y² - y + 1)³`, `D = y²(y - 1)²`, the upper bound uses
   `max(|N|_v, |D|_v) ≤ 27 max(1, |y|_v)⁶` at archimedean places and `≤ max(1, |y|_v)⁶` at the
   others; the lower bound uses the resultant certificate
   `y¹¹ = (y⁵ + 3y⁴ - 3y³) N + (6y⁵ - 8y⁴ + 11y³ - 6y² + 3y) D` and
   `1 = (1 + 3y - 3y²) N + (6 - 8y + 11y² - 6y³ + 3y⁴) D` (checked by `ring`), which gives
   `max(1, |y|_v)⁶ ≤ 41 max(|N|_v, |D|_v)` at archimedean places and the same with `1` at the
   others; the product formula removes `Σ_v log |D|_v`; the factor `2⁸` costs `8 log 2`.
2. Triples (`htCmp_heightNF_legendreJ_triple`): for coprime positive `a + b = c` and
   `λ = a / c`, `6 log c - log(64/27) ≤ ht(j(λ)) ≤ 6 log c + 8 log 2` in `ℚ`, from
   `IUT.ABCSpecialization.logHeight₁_of_triple` (`ht(λ) = log c`) and the bounds of
   `IUT.LegendreFrey`.
3. Conductor and height (`htCmp_logCondNF_le`): for every number field `K` and
   `x ∈ K \ {0, 1}`, `log-cond(x) ≤ 3 ht(x) + log 2` with `log-cond = logCondNF`. At a prime
   where `x` meets `D`, `x`, `1/x` or `1/(1 - x)` has absolute value at least the norm of the
   prime; summing gives the finite parts of `ht(x) + ht(1/x) + ht((x - 1)⁻¹) ≤ 3 ht(x) + log 2`.
   This is the instance `D = {0, 1, ∞}` of [GenEll] Proposition 1.6 (page 9,
   `log-cond_D ≲ ht_D`, with `ht_D` of degree 3), with the explicit constant `log 2`. It is the
   easy direction; it says nothing about the open inequality
   `ht ≤ (1 + ε)(log-diff + log-cond) + C` of `VojtaLineMinusThreePointsBoundedDegree`.

**Not proved.**

* Invariance of `heightNF` under field extension (`heightNF L (algebraMap K L y) = heightNF K y`
  for number fields `K ⊆ L`; [GenEll] page 4 asserts the corresponding invariance of the
  normalized degree). Not attempted here; no missing Mathlib lemma was identified. Mathlib has
  the ingredients: at finite places the local relation `|x|_w = |x|_v^{e f}`
  (`NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply_algebraMap`) and the fundamental
  identity `Σ e f = rank` over `p.primesOver S` (`Ideal.sum_ramification_inertia_eq_finrank`);
  at infinite places `NumberField.InfinitePlace.mult_mul_finrank` and
  `NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank`, which give
  `Σ_{w | v} mult(w) = [L : K] mult(v)`. What is missing is the glue: regrouping the `finsum`
  over the finite places of `L` by the prime of `𝓞_K` below, matching these fibers with
  `p.primesOver (𝓞 L)` and the rank of `𝓞_L` over `𝓞_K` with `[L : K]`, and the completion
  algebra structures required by `mult_mul_finrank`. Only the case `K = ℚ` is proved
  (`IUT.VojtaNumberField.heightNF_algebraMap_rat`).
* The comparison of `(1/6) log(𝔮^∀)` and `(1/6) log(𝔮^{†2})` with `(1/6) ht_∞` (page 43). It needs
  the `q`-parameter of an elliptic curve with multiplicative reduction at a nonarchimedean prime
  (Tate's uniformization); Mathlib has no Tate curve and no `q`-parameter, so `log(𝔮^∀)` is not
  defined here. The function `ht_∞` itself (height attached to the divisor at infinity of the
  compactified moduli stack) and `ht_{ω_X(D)}` are not defined either; the theorems above are
  stated for Weil heights, whose identification with these functions up to bounded functions is
  not formalized.
* The inequalities `log(𝔣^{F_tpd}) ≤ log-cond_D(x_E) ≤ log(𝔣^{F_tpd}) + log(2l)` (page 43) need
  the conductor of the elliptic curve, which Mathlib does not define.
-/

namespace IUT.HeightComparison

open Real
open IUT.VojtaNumberField IUT.LegendreFrey

/-! ## Sums over all places of a field with admissible absolute values -/

section Places

variable {K : Type*} [Field K] [Height.AdmissibleAbsValues K]

/-- The sum of a real function over all places of `K`: the archimedean absolute values, with
multiplicity, and then the nonarchimedean ones (a `finsum`). This is the shape of
`Height.logHeight₁_eq`. -/
noncomputable def htCmpPlaceSum (f : AbsoluteValue K ℝ → ℝ) : ℝ :=
  (Height.AdmissibleAbsValues.archAbsVal.map f).sum +
    ∑ᶠ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K), f v.val

/-- The logarithmic height is the place sum of `log⁺ |x|_v`. -/
theorem htCmp_logHeight₁_eq_placeSum (x : K) :
    Height.logHeight₁ x = htCmpPlaceSum (fun v ↦ log⁺ (v x)) :=
  Height.logHeight₁_eq x

/-- A function of `|x|_v` that vanishes at `0` and at `1` has finite support on the
nonarchimedean places. -/
theorem htCmp_hasFiniteSupport (φ : ℝ → ℝ) (h0 : φ 0 = 0) (h1 : φ 1 = 0) (x : K) :
    Function.HasFiniteSupport
      (fun v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K) ↦ φ (v.val x)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Function.HasFiniteSupport, h0]
  · refine Set.Finite.subset (Height.AdmissibleAbsValues.hasFiniteMulSupport hx) ?_
    intro v hv
    simp only [Function.mem_support, Function.mem_mulSupport] at hv ⊢
    intro h
    exact hv (by rw [h, h1])

/-- **The product formula in logarithmic form.** For `x ≠ 0`, the place sum of `log |x|_v`
is `0`. -/
theorem htCmp_placeSum_log_eq_zero {x : K} (hx : x ≠ 0) :
    htCmpPlaceSum (fun v ↦ Real.log (v x)) = 0 := by
  have h := Height.AdmissibleAbsValues.product_formula hx
  have hpos : ∀ v : AbsoluteValue K ℝ, 0 < v x := fun v ↦ v.pos hx
  have hA : ∀ a ∈ Height.AdmissibleAbsValues.archAbsVal.map (· x), a ≠ 0 := by
    intro a ha
    obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp ha
    exact (hpos v).ne'
  have hA' : (Height.AdmissibleAbsValues.archAbsVal.map (· x)).prod ≠ 0 :=
    Multiset.prod_ne_zero (fun h0 ↦ hA 0 h0 rfl)
  have hB : (∏ᶠ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K), v.val x) ≠ 0 :=
    right_ne_zero_of_mul (h ▸ one_ne_zero)
  have := congrArg Real.log h
  rw [Real.log_mul hA' hB, Real.log_multiset_prod hA, Multiset.map_map,
    Real.log_finprod (f := fun v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K) ↦ v.val x)
      (fun v ↦ hpos v.val), Real.log_one] at this
  exact this

/-- The place sum is additive for functions of finite support on the nonarchimedean places. -/
theorem htCmpPlaceSum_add {f g : AbsoluteValue K ℝ → ℝ}
    (hf : Function.HasFiniteSupport
      (fun v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K) ↦ f v.val))
    (hg : Function.HasFiniteSupport
      (fun v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K) ↦ g v.val)) :
    htCmpPlaceSum (fun v ↦ f v + g v) = htCmpPlaceSum f + htCmpPlaceSum g := by
  unfold htCmpPlaceSum
  rw [Multiset.sum_map_add, finsum_add_distrib hf hg]
  ring

/-- The place sum commutes with multiplication by a constant. -/
theorem htCmpPlaceSum_mul (r : ℝ) (f : AbsoluteValue K ℝ → ℝ) :
    htCmpPlaceSum (fun v ↦ r * f v) = r * htCmpPlaceSum f := by
  unfold htCmpPlaceSum
  rw [Multiset.sum_map_mul_left, ← mul_finsum]
  ring

/-- **Comparison of place sums.** If `f ≤ g + c` at the archimedean places and `f ≤ g` at the
nonarchimedean places, then the place sum of `f` is at most that of `g` plus
`totalWeight K · c`. -/
theorem htCmpPlaceSum_le {f g : AbsoluteValue K ℝ → ℝ} (c : ℝ)
    (hf : Function.HasFiniteSupport
      (fun v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K) ↦ f v.val))
    (hg : Function.HasFiniteSupport
      (fun v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K) ↦ g v.val))
    (harch : ∀ v, f v ≤ g v + c)
    (hnon : ∀ v ∈ Height.AdmissibleAbsValues.nonarchAbsVal (K := K), f v ≤ g v) :
    htCmpPlaceSum f ≤ htCmpPlaceSum g + Height.totalWeight K * c := by
  unfold htCmpPlaceSum
  have h1 : (Height.AdmissibleAbsValues.archAbsVal.map f).sum ≤
      (Height.AdmissibleAbsValues.archAbsVal.map g).sum + Height.totalWeight K * c := by
    calc (Height.AdmissibleAbsValues.archAbsVal.map f).sum
        ≤ (Height.AdmissibleAbsValues.archAbsVal.map fun v ↦ g v + c).sum :=
          Multiset.sum_map_le_sum_map _ _ fun v _ ↦ harch v
      _ = _ := by
          rw [Multiset.sum_map_add, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul,
            Height.totalWeight]
  have h2 := finsum_le_finsum hf hg (fun v ↦ hnon v.val v.prop)
  linarith

end Places

/-! ## Local estimates for integer polynomials -/

section Local

variable {K : Type*} [Field K]

/-- An absolute value of an integer is at most its absolute value. -/
theorem htCmp_abv_intCast_le (v : AbsoluteValue K ℝ) (z : ℤ) : v (z : K) ≤ |(z : ℝ)| := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · simpa using v.apply_nat_le_self m
  · simpa using v.apply_nat_le_self m

/-- **Archimedean bound for an integer polynomial.** `|Σ cᵢ yⁱ|_v ≤ (Σ |cᵢ|) max(1, |y|_v)ⁿ`
for a polynomial of degree at most `n`. -/
theorem htCmp_abv_poly_le (v : AbsoluteValue K ℝ) {n : ℕ} (c : Fin (n + 1) → ℤ) (y : K) :
    v (∑ i, (c i : K) * y ^ (i : ℕ)) ≤ (∑ i, |(c i : ℝ)|) * max 1 (v y) ^ n := by
  have hM : 1 ≤ max 1 (v y) := le_max_left _ _
  calc v (∑ i, (c i : K) * y ^ (i : ℕ)) ≤ ∑ i, v ((c i : K) * y ^ (i : ℕ)) := v.sum_le _ _
    _ ≤ ∑ i, |(c i : ℝ)| * max 1 (v y) ^ n := by
        gcongr with i
        rw [map_mul, map_pow]
        refine mul_le_mul (htCmp_abv_intCast_le v (c i)) ?_ (by positivity) (abs_nonneg _)
        calc v y ^ (i : ℕ) ≤ max 1 (v y) ^ (i : ℕ) :=
              pow_le_pow_left₀ (v.nonneg y) (le_max_right _ _) _
          _ ≤ max 1 (v y) ^ n := pow_le_pow_right₀ hM (Nat.lt_succ_iff.mp i.isLt)
    _ = _ := by rw [Finset.sum_mul]

/-- **Nonarchimedean bound for an integer polynomial.** `|Σ cᵢ yⁱ|_v ≤ max(1, |y|_v)ⁿ`. -/
theorem htCmp_nonarch_poly_le {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v) {n : ℕ}
    (c : Fin (n + 1) → ℤ) (y : K) :
    v (∑ i, (c i : K) * y ^ (i : ℕ)) ≤ max 1 (v y) ^ n := by
  refine hv.apply_sum_univ_le.trans (ciSup_le fun i ↦ ?_)
  rw [map_mul, map_pow]
  have hc : v (c i : K) ≤ 1 :=
    hv.apply_intCast_le_one (map_zero_le v 1) (map_one v) (map_neg_eq_map v)
  have hM : 1 ≤ max 1 (v y) := le_max_left _ _
  calc v (c i : K) * v y ^ (i : ℕ) ≤ 1 * max 1 (v y) ^ n := by
        refine mul_le_mul hc ?_ (by positivity) zero_le_one
        calc v y ^ (i : ℕ) ≤ max 1 (v y) ^ (i : ℕ) :=
              pow_le_pow_left₀ (v.nonneg y) (le_max_right _ _) _
          _ ≤ max 1 (v y) ^ n := pow_le_pow_right₀ hM (Nat.lt_succ_iff.mp i.isLt)
    _ = _ := one_mul _

end Local

/-! ## The numerator and denominator of the `j`-function -/

section Forms

variable {K : Type*} [Field K]

/-- The numerator `(y² - y + 1)³` of `legendreJ y / 2⁸`. -/
def htCmpNum (y : K) : K := (y ^ 2 - y + 1) ^ 3

/-- The denominator `y²(y - 1)²` of `legendreJ y`. -/
def htCmpDen (y : K) : K := y ^ 2 * (y - 1) ^ 2

/-- `legendreJ y = 2⁸ (N(y) / D(y))`. -/
theorem htCmp_legendreJ_eq (y : K) : legendreJ y = 2 ^ 8 * (htCmpNum y / htCmpDen y) := by
  rw [legendreJ, htCmpNum, htCmpDen, mul_div_assoc]

/-- The denominator vanishes exactly at `0` and `1`. -/
theorem htCmpDen_eq_zero_iff (y : K) : htCmpDen y = 0 ↔ y = 0 ∨ y = 1 := by
  simp [htCmpDen, sub_eq_zero]

/-- `N(y) = y⁶ - 3y⁵ + 6y⁴ - 7y³ + 6y² - 3y + 1` as a sum over its coefficients. -/
theorem htCmpNum_eq_sum (y : K) :
    htCmpNum y = ∑ i, (((![1, -3, 6, -7, 6, -3, 1] : Fin 7 → ℤ) i : ℤ) : K) * y ^ (i : ℕ) := by
  simp [htCmpNum, Fin.sum_univ_succ]
  ring

/-- `D(y) = y⁴ - 2y³ + y²` as a sum over its coefficients (degree at most 6). -/
theorem htCmpDen_eq_sum (y : K) :
    htCmpDen y = ∑ i, (((![0, 0, 1, -2, 1, 0, 0] : Fin 7 → ℤ) i : ℤ) : K) * y ^ (i : ℕ) := by
  simp [htCmpDen, Fin.sum_univ_succ]
  ring

/-- **Resultant certificate, first identity.** `y¹¹ = A₁(y) N(y) + B₁(y) D(y)` with
`A₁ = y⁵ + 3y⁴ - 3y³`, `B₁ = 6y⁵ - 8y⁴ + 11y³ - 6y² + 3y`, `N = (y² - y + 1)³`,
`D = y²(y - 1)²`. -/
theorem htCmp_certificate_one (y : K) :
    y ^ 11 =
      (∑ i, (((![0, 0, 0, -3, 3, 1] : Fin 6 → ℤ) i : ℤ) : K) * y ^ (i : ℕ)) * htCmpNum y +
      (∑ i, (((![0, 3, -6, 11, -8, 6] : Fin 6 → ℤ) i : ℤ) : K) * y ^ (i : ℕ)) * htCmpDen y := by
  simp [htCmpNum, htCmpDen, Fin.sum_univ_succ]
  ring

/-- **Resultant certificate, second identity.** `1 = A₂(y) N(y) + B₂(y) D(y)` with
`A₂ = 1 + 3y - 3y²`, `B₂ = 6 - 8y + 11y² - 6y³ + 3y⁴`. -/
theorem htCmp_certificate_two (y : K) :
    1 =
      (∑ i, (((![1, 3, -3, 0, 0, 0] : Fin 6 → ℤ) i : ℤ) : K) * y ^ (i : ℕ)) * htCmpNum y +
      (∑ i, (((![6, -8, 11, -6, 3, 0] : Fin 6 → ℤ) i : ℤ) : K) * y ^ (i : ℕ)) * htCmpDen y := by
  simp [htCmpNum, htCmpDen, Fin.sum_univ_succ]
  ring

end Forms

/-! ## Local estimates for the numerator and denominator -/

section LocalForms

variable {K : Type*} [Field K]

/-- The sum of the absolute values of the coefficients of `N` is `27`. -/
theorem htCmp_coeffSum_num :
    (∑ i, |((((![1, -3, 6, -7, 6, -3, 1] : Fin 7 → ℤ) i : ℤ)) : ℝ)|) = 27 := by
  simp [Fin.sum_univ_succ]
  norm_num

/-- The sum of the absolute values of the coefficients of `D` is `4`. -/
theorem htCmp_coeffSum_den :
    (∑ i, |((((![0, 0, 1, -2, 1, 0, 0] : Fin 7 → ℤ) i : ℤ)) : ℝ)|) = 4 := by
  simp [Fin.sum_univ_succ]
  norm_num

/-- **Archimedean upper bound.** `max(|N(y)|_v, |D(y)|_v) ≤ 27 max(1, |y|_v)⁶` for every
absolute value `v`. -/
theorem htCmp_abv_upper (v : AbsoluteValue K ℝ) (y : K) :
    max (v (htCmpNum y)) (v (htCmpDen y)) ≤ 27 * max 1 (v y) ^ 6 := by
  have h1 := htCmp_abv_poly_le v (![1, -3, 6, -7, 6, -3, 1] : Fin 7 → ℤ) y
  have h2 := htCmp_abv_poly_le v (![0, 0, 1, -2, 1, 0, 0] : Fin 7 → ℤ) y
  rw [htCmp_coeffSum_num] at h1
  rw [htCmp_coeffSum_den] at h2
  rw [htCmpNum_eq_sum, htCmpDen_eq_sum]
  have : 0 ≤ max 1 (v y) ^ 6 := by positivity
  exact max_le h1 (h2.trans (by linarith))

/-- **Nonarchimedean upper bound.** `max(|N(y)|_v, |D(y)|_v) ≤ max(1, |y|_v)⁶`. -/
theorem htCmp_nonarch_upper {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v) (y : K) :
    max (v (htCmpNum y)) (v (htCmpDen y)) ≤ 1 * max 1 (v y) ^ 6 := by
  rw [one_mul, htCmpNum_eq_sum, htCmpDen_eq_sum]
  exact max_le (htCmp_nonarch_poly_le hv _ y) (htCmp_nonarch_poly_le hv _ y)

/-- From `M¹¹ ≤ C M⁵ X` and `M ≥ 1`, `M⁶ ≤ C X`. -/
theorem htCmp_cancel_five {M X C : ℝ} (hM : 1 ≤ M) (h : M ^ 11 ≤ C * M ^ 5 * X) :
    M ^ 6 ≤ C * X := by
  have h5 : 0 < M ^ 5 := by positivity
  refine le_of_mul_le_mul_left ?_ h5
  calc M ^ 5 * M ^ 6 = M ^ 11 := by ring
    _ ≤ C * M ^ 5 * X := h
    _ = M ^ 5 * (C * X) := by ring

/-- From `|y|_v¹¹ ≤ B` and `1 ≤ B`, `max(1, |y|_v)¹¹ ≤ B`. -/
theorem htCmp_max_pow_le {t B : ℝ} (ht : t ^ 11 ≤ B) (h1 : 1 ≤ B) : max 1 t ^ 11 ≤ B := by
  rcases le_total t 1 with h | h
  · rw [max_eq_left h, one_pow]
    exact h1
  · rw [max_eq_right h]
    exact ht

/-- **Archimedean lower bound** (from the resultant certificate):
`max(1, |y|_v)⁶ ≤ 41 max(|N(y)|_v, |D(y)|_v)` for every absolute value `v`. -/
theorem htCmp_abv_lower (v : AbsoluteValue K ℝ) (y : K) :
    max 1 (v y) ^ 6 ≤ 41 * max (v (htCmpNum y)) (v (htCmpDen y)) := by
  set M := max 1 (v y) with hMdef
  set X := max (v (htCmpNum y)) (v (htCmpDen y)) with hXdef
  have hM : 1 ≤ M := le_max_left _ _
  have key : ∀ (A B : K) (a b : ℝ), v A ≤ a * M ^ 5 → v B ≤ b * M ^ 5 →
      v (A * htCmpNum y + B * htCmpDen y) ≤ (a + b) * M ^ 5 * X := by
    intro A B a b hA hB
    have hN : v (htCmpNum y) ≤ X := le_max_left _ _
    have hD : v (htCmpDen y) ≤ X := le_max_right _ _
    calc v (A * htCmpNum y + B * htCmpDen y)
        ≤ v (A * htCmpNum y) + v (B * htCmpDen y) := v.add_le _ _
      _ = v A * v (htCmpNum y) + v B * v (htCmpDen y) := by rw [map_mul, map_mul]
      _ ≤ a * M ^ 5 * X + b * M ^ 5 * X :=
          add_le_add (mul_le_mul hA hN (v.nonneg _) ((v.nonneg _).trans hA))
            (mul_le_mul hB hD (v.nonneg _) ((v.nonneg _).trans hB))
      _ = (a + b) * M ^ 5 * X := by ring
  have hA1 := htCmp_abv_poly_le v (![0, 0, 0, -3, 3, 1] : Fin 6 → ℤ) y
  have hB1 := htCmp_abv_poly_le v (![0, 3, -6, 11, -8, 6] : Fin 6 → ℤ) y
  have hA2 := htCmp_abv_poly_le v (![1, 3, -3, 0, 0, 0] : Fin 6 → ℤ) y
  have hB2 := htCmp_abv_poly_le v (![6, -8, 11, -6, 3, 0] : Fin 6 → ℤ) y
  have s1 : (∑ i, |((((![0, 0, 0, -3, 3, 1] : Fin 6 → ℤ) i : ℤ)) : ℝ)|) = 7 := by
    simp [Fin.sum_univ_succ]; norm_num
  have s2 : (∑ i, |((((![0, 3, -6, 11, -8, 6] : Fin 6 → ℤ) i : ℤ)) : ℝ)|) = 34 := by
    simp [Fin.sum_univ_succ]; norm_num
  have s3 : (∑ i, |((((![1, 3, -3, 0, 0, 0] : Fin 6 → ℤ) i : ℤ)) : ℝ)|) = 7 := by
    simp [Fin.sum_univ_succ]; norm_num
  have s4 : (∑ i, |((((![6, -8, 11, -6, 3, 0] : Fin 6 → ℤ) i : ℤ)) : ℝ)|) = 34 := by
    simp [Fin.sum_univ_succ]; norm_num
  rw [s1] at hA1
  rw [s2] at hB1
  rw [s3] at hA2
  rw [s4] at hB2
  have e1 := key _ _ _ _ hA1 hB1
  have e2 := key _ _ _ _ hA2 hB2
  rw [← htCmp_certificate_one, map_pow] at e1
  rw [← htCmp_certificate_two, map_one] at e2
  norm_num at e1 e2
  exact htCmp_cancel_five hM (htCmp_max_pow_le e1 e2)

/-- **Nonarchimedean lower bound**: `max(1, |y|_v)⁶ ≤ max(|N(y)|_v, |D(y)|_v)`. -/
theorem htCmp_nonarch_lower {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v) (y : K) :
    max 1 (v y) ^ 6 ≤ 1 * max (v (htCmpNum y)) (v (htCmpDen y)) := by
  set M := max 1 (v y) with hMdef
  set X := max (v (htCmpNum y)) (v (htCmpDen y)) with hXdef
  have hM : 1 ≤ M := le_max_left _ _
  have key : ∀ (A B : K), v A ≤ M ^ 5 → v B ≤ M ^ 5 →
      v (A * htCmpNum y + B * htCmpDen y) ≤ 1 * M ^ 5 * X := by
    intro A B hA hB
    have hN : v (htCmpNum y) ≤ X := le_max_left _ _
    have hD : v (htCmpDen y) ≤ X := le_max_right _ _
    have hM5 : 0 ≤ M ^ 5 := by positivity
    calc v (A * htCmpNum y + B * htCmpDen y)
        ≤ max (v (A * htCmpNum y)) (v (B * htCmpDen y)) := hv _ _
      _ = max (v A * v (htCmpNum y)) (v B * v (htCmpDen y)) := by rw [map_mul, map_mul]
      _ ≤ 1 * M ^ 5 * X := by
          rw [one_mul]
          exact max_le (mul_le_mul hA hN (v.nonneg _) hM5) (mul_le_mul hB hD (v.nonneg _) hM5)
  have e1 := key _ _ (htCmp_nonarch_poly_le hv (![0, 0, 0, -3, 3, 1] : Fin 6 → ℤ) y)
    (htCmp_nonarch_poly_le hv (![0, 3, -6, 11, -8, 6] : Fin 6 → ℤ) y)
  have e2 := key _ _ (htCmp_nonarch_poly_le hv (![1, 3, -3, 0, 0, 0] : Fin 6 → ℤ) y)
    (htCmp_nonarch_poly_le hv (![6, -8, 11, -6, 3, 0] : Fin 6 → ℤ) y)
  rw [← htCmp_certificate_one, map_pow] at e1
  rw [← htCmp_certificate_two, map_one] at e2
  exact htCmp_cancel_five hM (htCmp_max_pow_le e1 e2)

/-- The local term of the height of `N(y)/D(y)` plus `log |D(y)|_v` is
`log max(|N(y)|_v, |D(y)|_v)`. -/
theorem htCmp_log_identity (v : AbsoluteValue K ℝ) {y : K} (hD : htCmpDen y ≠ 0) :
    log⁺ (v (htCmpNum y / htCmpDen y)) + Real.log (v (htCmpDen y)) =
      Real.log (max (v (htCmpNum y)) (v (htCmpDen y))) := by
  have hb : 0 < v (htCmpDen y) := v.pos hD
  rw [map_div₀, Real.posLog_eq_log_max_one (div_nonneg (v.nonneg _) hb.le)]
  have : max 1 (v (htCmpNum y) / v (htCmpDen y)) =
      max (v (htCmpDen y)) (v (htCmpNum y)) / v (htCmpDen y) := by
    rw [← max_div_div_right hb.le, div_self hb.ne']
  rw [this, Real.log_div (lt_max_of_lt_left hb).ne' hb.ne', max_comm]
  ring

/-- Logarithmic form of an upper local bound: `X ≤ C M⁶` gives
`log X ≤ 6 log M + log C`. -/
theorem htCmp_log_upper {M X C : ℝ} (hX : 0 < X) (hC : 0 < C) (hM : 1 ≤ M)
    (h : X ≤ C * M ^ 6) : Real.log X ≤ 6 * Real.log M + Real.log C := by
  have := Real.log_le_log hX h
  rw [Real.log_mul hC.ne' (by positivity), Real.log_pow] at this
  push_cast at this
  linarith

/-- Logarithmic form of a lower local bound: `M⁶ ≤ C X` gives
`6 log M ≤ log X + log C`. -/
theorem htCmp_log_lower {M X C : ℝ} (hX : 0 < X) (hC : 0 < C) (hM : 1 ≤ M)
    (h : M ^ 6 ≤ C * X) : 6 * Real.log M ≤ Real.log X + Real.log C := by
  have := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_mul hC.ne' hX.ne'] at this
  push_cast at this
  linarith

end LocalForms

/-! ## The global comparison for `N/D` over a field with admissible absolute values -/

section Global

variable {K : Type*} [Field K] [Height.AdmissibleAbsValues K]

/-- `r · log⁺ |x|_v` has finite support on the nonarchimedean places. -/
theorem htCmp_hasFiniteSupport_mul (r : ℝ) (x : K) :
    Function.HasFiniteSupport
      (fun v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K) ↦ r * log⁺ (v.val x)) := by
  refine Set.Finite.subset (htCmp_hasFiniteSupport Real.posLog Real.posLog_zero
    Real.posLog_one x) ?_
  intro v hv
  simp only [Function.mem_support] at hv ⊢
  intro h
  exact hv (by rw [h, mul_zero])

/-- **Upper comparison.** For every `y ∈ K`,
`h(N(y)/D(y)) ≤ 6 h(y) + totalWeight K · log 27`, with `h = Height.logHeight₁`. -/
theorem htCmp_logHeight₁_ratio_le (y : K) :
    Height.logHeight₁ (htCmpNum y / htCmpDen y) ≤
      6 * Height.logHeight₁ y + Height.totalWeight K * Real.log 27 := by
  have h27 : 0 ≤ Real.log 27 := Real.log_nonneg (by norm_num)
  by_cases hD : htCmpDen y = 0
  · rw [hD, div_zero, Height.logHeight₁_zero]
    have := Height.zero_le_logHeight₁ y
    have : (0 : ℝ) ≤ Height.totalWeight K := Nat.cast_nonneg _
    nlinarith
  have hfa := htCmp_hasFiniteSupport Real.posLog Real.posLog_zero Real.posLog_one
    (htCmpNum y / htCmpDen y)
  have hfb := htCmp_hasFiniteSupport Real.log Real.log_zero Real.log_one (htCmpDen y)
  have hX : ∀ v : AbsoluteValue K ℝ, 0 < max (v (htCmpNum y)) (v (htCmpDen y)) :=
    fun v ↦ lt_max_of_lt_right (v.pos hD)
  have key := htCmpPlaceSum_le (f := fun v ↦ log⁺ (v (htCmpNum y / htCmpDen y)) +
      Real.log (v (htCmpDen y))) (g := fun v ↦ 6 * log⁺ (v y)) (Real.log 27)
    (hfa.add hfb) (htCmp_hasFiniteSupport_mul 6 y)
    (fun v ↦ by
      rw [htCmp_log_identity v hD, Real.posLog_eq_log_max_one (v.nonneg y)]
      exact htCmp_log_upper (hX v) (by norm_num) (le_max_left _ _) (htCmp_abv_upper v y))
    (fun v hv ↦ by
      rw [htCmp_log_identity v hD, Real.posLog_eq_log_max_one (v.nonneg y)]
      have := htCmp_log_upper (hX v) one_pos (le_max_left _ _)
        (htCmp_nonarch_upper (Height.AdmissibleAbsValues.isNonarchimedean v hv) y)
      rwa [Real.log_one, add_zero] at this)
  rw [htCmpPlaceSum_add (f := fun v ↦ log⁺ (v (htCmpNum y / htCmpDen y)))
    (g := fun v ↦ Real.log (v (htCmpDen y))) hfa hfb, htCmp_placeSum_log_eq_zero hD,
    add_zero, ← htCmp_logHeight₁_eq_placeSum, htCmpPlaceSum_mul,
    ← htCmp_logHeight₁_eq_placeSum] at key
  exact key

/-- **Lower comparison.** For every `y ∈ K`,
`6 h(y) ≤ h(N(y)/D(y)) + totalWeight K · log 41`. -/
theorem htCmp_le_logHeight₁_ratio (y : K) :
    6 * Height.logHeight₁ y ≤
      Height.logHeight₁ (htCmpNum y / htCmpDen y) + Height.totalWeight K * Real.log 41 := by
  have h41 : 0 ≤ Real.log 41 := Real.log_nonneg (by norm_num)
  by_cases hD : htCmpDen y = 0
  · rcases (htCmpDen_eq_zero_iff y).mp hD with rfl | rfl
    · rw [Height.logHeight₁_zero]
      have := Height.zero_le_logHeight₁ (htCmpNum (0 : K) / htCmpDen 0)
      have : (0 : ℝ) ≤ Height.totalWeight K := Nat.cast_nonneg _
      nlinarith
    · rw [Height.logHeight₁_one]
      have := Height.zero_le_logHeight₁ (htCmpNum (1 : K) / htCmpDen 1)
      have : (0 : ℝ) ≤ Height.totalWeight K := Nat.cast_nonneg _
      nlinarith
  have hfa := htCmp_hasFiniteSupport Real.posLog Real.posLog_zero Real.posLog_one
    (htCmpNum y / htCmpDen y)
  have hfb := htCmp_hasFiniteSupport Real.log Real.log_zero Real.log_one (htCmpDen y)
  have hX : ∀ v : AbsoluteValue K ℝ, 0 < max (v (htCmpNum y)) (v (htCmpDen y)) :=
    fun v ↦ lt_max_of_lt_right (v.pos hD)
  have key := htCmpPlaceSum_le (f := fun v ↦ 6 * log⁺ (v y))
    (g := fun v ↦ log⁺ (v (htCmpNum y / htCmpDen y)) + Real.log (v (htCmpDen y)))
    (Real.log 41) (htCmp_hasFiniteSupport_mul 6 y) (hfa.add hfb)
    (fun v ↦ by
      rw [htCmp_log_identity v hD, Real.posLog_eq_log_max_one (v.nonneg y)]
      exact htCmp_log_lower (hX v) (by norm_num) (le_max_left _ _) (htCmp_abv_lower v y))
    (fun v hv ↦ by
      rw [htCmp_log_identity v hD, Real.posLog_eq_log_max_one (v.nonneg y)]
      have := htCmp_log_lower (hX v) one_pos (le_max_left _ _)
        (htCmp_nonarch_lower (Height.AdmissibleAbsValues.isNonarchimedean v hv) y)
      rwa [Real.log_one, add_zero] at this)
  rw [htCmpPlaceSum_add (f := fun v ↦ log⁺ (v (htCmpNum y / htCmpDen y)))
    (g := fun v ↦ Real.log (v (htCmpDen y))) hfa hfb, htCmp_placeSum_log_eq_zero hD,
    add_zero, ← htCmp_logHeight₁_eq_placeSum, htCmpPlaceSum_mul,
    ← htCmp_logHeight₁_eq_placeSum] at key
  exact key

end Global

/-! ## Number fields: the `j`-invariant of the Legendre curve -/

section NumberFieldJ

open NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The height of `2⁸` in a number field `K` is `[K : ℚ] · 8 log 2`. -/
theorem htCmp_logHeight₁_two_pow_eight :
    Height.logHeight₁ ((2 : K) ^ 8) = Module.finrank ℚ K * (8 * Real.log 2) := by
  have h2 : Height.logHeight₁ (2 : ℚ) = Real.log 2 := by
    rw [Rat.logHeight₁_eq_log_max]
    norm_num
  have := logHeight₁_algebraMap_rat (K := K) (2 : ℚ)
  rw [map_ofNat, h2] at this
  rw [Height.logHeight₁_pow, this]
  push_cast
  ring

/-- **Upper bound for the height of the `j`-invariant.** For every number field `K` and every
`y ∈ K`, `ht(j(y)) ≤ 6 ht(y) + log 27 + 8 log 2`, with `ht = heightNF` and `j = legendreJ`.
The constant does not depend on `K`. -/
theorem htCmp_heightNF_legendreJ_le (y : K) :
    heightNF K (legendreJ y) ≤ 6 * heightNF K y + (Real.log 27 + 8 * Real.log 2) := by
  have hn := finrank_pos_real K
  have h1 := Height.logHeight₁_mul_le ((2 : K) ^ 8) (htCmpNum y / htCmpDen y)
  have h2 := htCmp_logHeight₁_ratio_le y
  rw [NumberField.totalWeight_eq_finrank] at h2
  rw [htCmp_logHeight₁_two_pow_eight] at h1
  have key : Height.logHeight₁ (legendreJ y) ≤
      6 * Height.logHeight₁ y + Module.finrank ℚ K * (Real.log 27 + 8 * Real.log 2) := by
    rw [htCmp_legendreJ_eq]
    linarith
  unfold heightNF
  calc Height.logHeight₁ (legendreJ y) / Module.finrank ℚ K
      ≤ (6 * Height.logHeight₁ y + Module.finrank ℚ K * (Real.log 27 + 8 * Real.log 2)) /
          Module.finrank ℚ K := div_le_div_of_nonneg_right key hn.le
    _ = _ := by rw [add_div, mul_div_assoc, mul_div_cancel_left₀ _ hn.ne']

/-- **Lower bound for the height of the `j`-invariant.** For every number field `K` and every
`y ∈ K`, `6 ht(y) ≤ ht(j(y)) + log 41 + 8 log 2`. The constant does not depend on `K`. -/
theorem htCmp_le_heightNF_legendreJ (y : K) :
    6 * heightNF K y ≤ heightNF K (legendreJ y) + (Real.log 41 + 8 * Real.log 2) := by
  have hn := finrank_pos_real K
  have hr : htCmpNum y / htCmpDen y = ((2 : K) ^ 8)⁻¹ * legendreJ y := by
    rw [htCmp_legendreJ_eq, ← mul_assoc, inv_mul_cancel₀ (by norm_num), one_mul]
  have h1 := Height.logHeight₁_mul_le ((2 : K) ^ 8)⁻¹ (legendreJ y)
  rw [← hr, Height.logHeight₁_inv, htCmp_logHeight₁_two_pow_eight] at h1
  have h2 := htCmp_le_logHeight₁_ratio y
  rw [NumberField.totalWeight_eq_finrank] at h2
  have key : 6 * Height.logHeight₁ y ≤
      Height.logHeight₁ (legendreJ y) + Module.finrank ℚ K * (Real.log 41 + 8 * Real.log 2) := by
    linarith
  unfold heightNF
  calc 6 * (Height.logHeight₁ y / Module.finrank ℚ K)
      = 6 * Height.logHeight₁ y / Module.finrank ℚ K := by rw [mul_div_assoc]
    _ ≤ (Height.logHeight₁ (legendreJ y) +
          Module.finrank ℚ K * (Real.log 41 + 8 * Real.log 2)) / Module.finrank ℚ K :=
        div_le_div_of_nonneg_right key hn.le
    _ = _ := by rw [add_div, mul_div_cancel_left₀ _ hn.ne']

/-- **The height of the `j`-invariant is six times the height of `λ`, up to a constant
independent of the number field.** For every number field `K` and every `y ∈ K`,
`|ht(j(y)) - 6 ht(y)| ≤ log 41 + 8 log 2 = log 10496`. At `y = 0` and `y = 1` the statement
holds through Lean's convention `x / 0 = 0`: there `legendreJ y = 0` and both heights vanish;
these values have no meaning as `j`-invariants. -/
theorem htCmp_abs_heightNF_legendreJ_sub_le (y : K) :
    |heightNF K (legendreJ y) - 6 * heightNF K y| ≤ Real.log 41 + 8 * Real.log 2 := by
  have h1 := htCmp_heightNF_legendreJ_le y
  have h2 := htCmp_le_heightNF_legendreJ y
  have h3 : Real.log 27 ≤ Real.log 41 := Real.log_le_log (by norm_num) (by norm_num)
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The constant of `htCmp_abs_heightNF_legendreJ_sub_le` is `log 10496`. -/
theorem htCmp_constant_eq : Real.log 41 + 8 * Real.log 2 = Real.log 10496 := by
  rw [show (10496 : ℝ) = 41 * 2 ^ 8 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow]
  push_cast
  ring

/-- **Uniform statement.** There is one constant `C` such that for every number field `K` and
every `y ∈ K`, `|ht(j(y)) - 6 ht(y)| ≤ C`. -/
theorem htCmp_exists_uniform_constant :
    ∃ C : ℝ, ∀ (F : Type) [Field F] [NumberField F] (y : F),
      |heightNF F (legendreJ y) - 6 * heightNF F y| ≤ C :=
  ⟨_, fun _ _ _ y ↦ htCmp_abs_heightNF_legendreJ_sub_le y⟩

end NumberFieldJ

/-! ## Rational points of coprime triples -/

section Triples

variable {a b c : ℕ}

/-- **The `j`-height at the point of a coprime triple.** For positive coprime `a + b = c` and
`λ = a / c`: `6 log c - log(64/27) ≤ ht(j(λ)) ≤ 6 log c + 8 log 2`, with `ht = heightNF ℚ`. It
combines `IUT.ABCSpecialization.logHeight₁_of_triple` (`ht(λ) = log c`) with the explicit
bounds of `IUT.LegendreFrey`. -/
theorem htCmp_heightNF_legendreJ_triple (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : a + b = c) :
    6 * Real.log c - Real.log (64 / 27) ≤ heightNF ℚ (legendreJ ((a : ℚ) / c)) ∧
      heightNF ℚ (legendreJ ((a : ℚ) / c)) ≤ 6 * Real.log c + 8 * Real.log 2 := by
  have e := IUT.ABCSpecialization.logHeight₁_of_triple ha hb hab h
  have h1 := le_logHeight₁_legendreJ_triple ha hb hab h
  have h2 := logHeight₁_legendreJ_triple_le ha hb hab h
  rw [e] at h1 h2
  rw [heightNF_rat]
  exact ⟨h1, h2⟩

end Triples

/-! ## The log-conductor is bounded by three times the height -/

section Conductor

open NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- If `m ∈ ℤᵐ⁰` is neither `0` nor `1` and `e ≥ 1`, then `e ≤ e^{log m}` or `e ≤ e^{log m⁻¹}`
(through `WithZeroMulInt.toNNReal`). -/
theorem htCmp_toNNReal_ge {e : NNReal} (he0 : e ≠ 0) (he : 1 ≤ e) {m : WithZero (Multiplicative ℤ)}
    (hm0 : m ≠ 0) (hm1 : m ≠ 1) :
    e ≤ WithZeroMulInt.toNNReal he0 m ∨ e ≤ WithZeroMulInt.toNNReal he0 m⁻¹ := by
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, m = WithZero.exp k := ⟨_, (WithZero.exp_log hm0).symm⟩
  have hk : k ≠ 0 := by
    rintro rfl
    exact hm1 WithZero.exp_zero
  rw [← WithZero.exp_neg, WithZeroMulInt.toNNReal_neg_apply he0 WithZero.exp_ne_zero,
    WithZeroMulInt.toNNReal_neg_apply he0 WithZero.exp_ne_zero, WithZero.log_exp,
    WithZero.log_exp]
  rcases lt_or_gt_of_ne hk with hk | hk
  · right
    calc e = e ^ (1 : ℤ) := (zpow_one e).symm
      _ ≤ e ^ (-k) := zpow_le_zpow_right₀ he (by omega)
  · left
    calc e = e ^ (1 : ℤ) := (zpow_one e).symm
      _ ≤ e ^ k := zpow_le_zpow_right₀ he (by omega)

/-- At a finite place `w` where the valuation of `z ≠ 0` is not `1`, `|z|_w` or `|z⁻¹|_w` is at
least the norm of the prime of `w`. -/
theorem htCmp_finitePlace_ge {w : FinitePlace K} {z : K} (hz : z ≠ 0)
    (hv : (FinitePlace.maximalIdeal w).valuation K z ≠ 1) :
    (Ideal.absNorm (FinitePlace.maximalIdeal w).asIdeal : ℝ) ≤ w z ∨
      (Ideal.absNorm (FinitePlace.maximalIdeal w).asIdeal : ℝ) ≤ w z⁻¹ := by
  rw [← FinitePlace.norm_embedding_eq w z, ← FinitePlace.norm_embedding_eq w z⁻¹,
    FinitePlace.norm_embedding', FinitePlace.norm_embedding', map_inv₀]
  have hm0 : (FinitePlace.maximalIdeal w).valuation K z ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hz
  rcases htCmp_toNNReal_ge
    (NumberField.HeightOneSpectrum.absNorm_ne_zero (FinitePlace.maximalIdeal w))
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal (FinitePlace.maximalIdeal w)).le
    hm0 hv with h | h
  · left
    exact_mod_cast h
  · right
    exact_mod_cast h

/-- **Pointwise bound.** At a finite place `w` with prime `𝔭`, the contribution of `𝔭` to the
log-conductor of `x ∉ {0, 1}` is at most `log⁺|x|_w + log⁺|x⁻¹|_w + log⁺|(x - 1)⁻¹|_w`. -/
theorem htCmp_cond_term_le (w : FinitePlace K) {x : K} (h0 : x ≠ 0) (h1 : x ≠ 1) :
    (open Classical in
      if MeetsBoundaryAt K (FinitePlace.maximalIdeal w) x then
        Real.log (Nat.card (𝓞 K ⧸ (FinitePlace.maximalIdeal w).asIdeal)) else 0) ≤
      log⁺ (w x) + log⁺ (w x⁻¹) + log⁺ (w (x - 1)⁻¹) := by
  have p1 : 0 ≤ log⁺ (w x) := Real.posLog_nonneg
  have p2 : 0 ≤ log⁺ (w x⁻¹) := Real.posLog_nonneg
  have p3 : 0 ≤ log⁺ (w (x - 1)⁻¹) := Real.posLog_nonneg
  split_ifs with hm
  · rw [meetsBoundaryAt_iff_valuation] at hm
    have hcard : (Nat.card (𝓞 K ⧸ (FinitePlace.maximalIdeal w).asIdeal) : ℝ) =
        (Ideal.absNorm (FinitePlace.maximalIdeal w).asIdeal : ℝ) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [hcard]
    set N : ℝ := (Ideal.absNorm (FinitePlace.maximalIdeal w).asIdeal : ℝ) with hNdef
    have hN : 1 < N := by
      rw [hNdef]
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm (FinitePlace.maximalIdeal w)
    have hlog : ∀ t, N ≤ t → Real.log N ≤ log⁺ t := fun t ht ↦ by
      rw [Real.posLog_apply]
      exact (Real.log_le_log (by linarith) ht).trans (le_max_right _ _)
    rcases hm with hx | hx1
    · rcases htCmp_finitePlace_ge h0 hx with h | h
      · linarith [hlog _ h]
      · linarith [hlog _ h]
    · rcases htCmp_finitePlace_ge (sub_ne_zero.mpr h1) hx1 with h | h
      · have hle : w (x - 1) ≤ max (w x) 1 := by
          have := FinitePlace.add_le w x (-1)
          rwa [map_neg_eq_map, map_one, ← sub_eq_add_neg] at this
        have hNx : N ≤ w x := by
          rcases le_max_iff.mp (h.trans hle) with h' | h'
          · exact h'
          · linarith
        linarith [hlog _ hNx]
      · linarith [hlog _ h]
  · linarith

/-- The finite part of the height is at most the height. -/
theorem htCmp_finsum_posLog_le (z : K) :
    ∑ᶠ w : FinitePlace K, log⁺ (w z) ≤ Height.logHeight₁ z := by
  rw [NumberField.logHeight₁_eq]
  have : 0 ≤ ∑ v : InfinitePlace K, (v.mult : ℝ) * log⁺ (v z) :=
    Finset.sum_nonneg fun v _ ↦ mul_nonneg (Nat.cast_nonneg _) Real.posLog_nonneg
  linarith

/-- `log⁺ |z|_w` has finite support on the finite places of a number field. -/
theorem htCmp_hasFiniteSupport_finitePlace (z : K) :
    Function.HasFiniteSupport (fun w : FinitePlace K ↦ log⁺ (w z)) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [Function.HasFiniteSupport]
  · refine Set.Finite.subset (FinitePlace.hasFiniteMulSupport hz) ?_
    intro w hw
    simp only [Function.mem_support, Function.mem_mulSupport] at hw ⊢
    intro h
    exact hw (by rw [h, Real.posLog_one])

/-- **The log-conductor is bounded by three times the height.** For every number field `K`
and `x ∈ K` with `x ≠ 0, 1`: `log-cond(x) ≤ 3 ht(x) + log 2`, with `log-cond = logCondNF` and
`ht = heightNF`. This is the instance `D = {0, 1, ∞}` of [GenEll] Proposition 1.6
(`log-cond_D ≲ ht_D`, page 9), with the explicit constant `log 2`. It is the easy direction and
says nothing about the open inequality `ht ≤ (1 + ε)(log-diff + log-cond) + C`
(`IUT.VojtaNumberField.VojtaLineMinusThreePointsBoundedDegree`). -/
theorem htCmp_logCondNF_le (x : K) (h0 : x ≠ 0) (h1 : x ≠ 1) :
    logCondNF K x ≤ 3 * heightNF K x + Real.log 2 := by
  classical
  have hn := finrank_pos_real K
  set T : FinitePlace K → ℝ := fun w ↦
    if MeetsBoundaryAt K (FinitePlace.maximalIdeal w) x then
      Real.log (Nat.card (𝓞 K ⧸ (FinitePlace.maximalIdeal w).asIdeal)) else 0 with hTdef
  have hsum : (∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      if MeetsBoundaryAt K v x then Real.log (Nat.card (𝓞 K ⧸ v.asIdeal)) else 0) =
      ∑ᶠ w, T w :=
    (finsum_comp_equiv FinitePlace.equivHeightOneSpectrum).symm
  have hP := htCmp_hasFiniteSupport_finitePlace (K := K)
  have hR : Function.HasFiniteSupport
      (fun w : FinitePlace K ↦ log⁺ (w x) + log⁺ (w x⁻¹) + log⁺ (w (x - 1)⁻¹)) :=
    ((hP x).add (hP _)).add (hP _)
  have hTle : ∀ w, T w ≤ log⁺ (w x) + log⁺ (w x⁻¹) + log⁺ (w (x - 1)⁻¹) :=
    fun w ↦ htCmp_cond_term_le w h0 h1
  have hT0 : ∀ w, 0 ≤ T w := fun w ↦ by
    simp only [hTdef]
    split_ifs
    · exact Real.log_natCast_nonneg _
    · exact le_rfl
  have hT : Function.HasFiniteSupport T := by
    refine Set.Finite.subset hR ?_
    intro w hw
    simp only [Function.mem_support] at hw ⊢
    have := lt_of_le_of_ne (hT0 w) (Ne.symm hw)
    linarith [hTle w]
  have hle := finsum_le_finsum hT hR hTle
  rw [finsum_add_distrib (f := fun w : FinitePlace K ↦ log⁺ (w x) + log⁺ (w x⁻¹))
    (g := fun w : FinitePlace K ↦ log⁺ (w (x - 1)⁻¹)) ((hP x).add (hP _)) (hP _),
    finsum_add_distrib (f := fun w : FinitePlace K ↦ log⁺ (w x))
    (g := fun w : FinitePlace K ↦ log⁺ (w x⁻¹)) (hP x) (hP _)] at hle
  have e1 := htCmp_finsum_posLog_le x
  have e2 := htCmp_finsum_posLog_le x⁻¹
  have e3 := htCmp_finsum_posLog_le (x - 1)⁻¹
  rw [Height.logHeight₁_inv] at e2 e3
  have e4 := Height.logHeight₁_sub_le x 1
  rw [Height.logHeight₁_one, NumberField.totalWeight_eq_finrank] at e4
  have key : ∑ᶠ w, T w ≤ 3 * Height.logHeight₁ x + Module.finrank ℚ K * Real.log 2 := by
    linarith
  unfold logCondNF heightNF
  rw [hsum]
  calc (∑ᶠ w, T w) / Module.finrank ℚ K
      ≤ (3 * Height.logHeight₁ x + Module.finrank ℚ K * Real.log 2) / Module.finrank ℚ K :=
        div_le_div_of_nonneg_right key hn.le
    _ = _ := by rw [add_div, mul_div_assoc, mul_div_cancel_left₀ _ hn.ne']

end Conductor

end IUT.HeightComparison
