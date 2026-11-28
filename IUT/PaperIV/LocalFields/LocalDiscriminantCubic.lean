import Mathlib
import IUT.PaperIV.LocalFields.LocalDiscriminantExample

/-!
# The exact two-factor index for `K = ℚ_3(3^{1/3})`

Sources: IUT IV, Proposition 1.4 (i) (page 13; the log-volume normalized at the normalization of
a tensor product), checked against the page render; the paper of C. Zeng (hexagon 2610.00646),
Theorem 5.1 and its section 14, read in the TeX source of version 1 (no page render). The field
`ℚ_3(3^{1/3})` is chosen here: section 14 of version 1 treats the non-Galois case with the
example `ℚ_2(2^{1/3})`, and version 2 of the paper lists `ℚ(3^{1/3})` at `p = 3` in its table
of non-Galois samples, with 3-adic valuation 7 of the index. Everything here is a model test:
an explicit computation for one field, not a printed statement.

## What is proved

Let `K` be a field of degree `3` over `ℚ_3` with an element `π`, `π ^ 3 = 3` (for example
`ℚ_3[X] / (X ^ 3 − 3)`, `locDiscEx_exists`). Write `R_E` for the `ℤ_3`-span of the `π^i ⊗ π^j`
in `K ⊗ K` and `(R_E)^∼` for its normalization, the elements of `K ⊗ K` integral over `ℤ_3`.

* `locDiscCu_index`: `[(R_E)^∼ : R_E] = 3 ^ 7`.
* `locDiscCu_normDiscr_valuation`: `v_3(disc n) = 16` for every basis `n` whose `ℤ_3`-span is
  `(R_E)^∼` (from the index by `locDisc_index_valuation`: `2 · 7 = 3 · 5 + 3 · 5 − 16`).
* `locDiscCu_normRing_eq`: `(R_E)^∼` is the set of `z = Σ c_{3i+j} π^i ⊗ π^j` at which nine
  explicit linear forms (the rows of `locDiscCuMat`, an upper triangular integer matrix of
  determinant `−3^7`) take values in `ℤ_3`.

## Method

Two `ℚ_3`-algebra maps out of `K ⊗ K` detect integrality. The multiplication map to `K` sends
`z` to `A₀ + A₁ π + A₂ π²`, and `1, π, π²` is an integral basis (`locDiscExBasis_integral`).
The second map goes to a field `L` with an element `ϖ`, `ϖ ^ 6 = −3` (`locDiscCu_exists_sixth`:
the quotient by an irreducible factor of `X ^ 6 + 3`). It sends `π ⊗ 1` to `−ϖ²` and `1 ⊗ π` to
`ϖ² (ϖ³ + 1) / 2`, two cube roots of `3` in `L` (`locDiscCuLift`, from the minimal polynomial
`X ^ 3 − 3` of `π`). In `L` the terms of `Σ b_k ϖ^k` (`k ≤ 5`) have norms in six distinct classes
`3 ^ (ℤ − k/6)`, so an integral element has all `b_k ∈ ℤ_3` (`locDiscCu_coeff_le_one`). This
bounds the nine linear forms on `(R_E)^∼`. Conversely the dual elements are built from the
integral elements `x = (π ⊗ π²) / 3` (`x³ = 1`), `e = (1 + x + x²) / 3` (`e² = e`) and
`w = (π ⊗ π − 1 ⊗ π²) / 3` (`w⁷ + 3 w = 0`), so every element where the forms are integral lies
in `(R_E)^∼` (`locDiscCu_ring_identity`). The index is then `‖det‖⁻¹ = 3 ^ 7`
(`tOrdIdx_relIndex_eq`).

No assumption that `K ⊗ K` splits as `K × L` is used: only the two maps.
-/

open IUT.Audit.TensorOrderIndex IUT.Prerequisites.PadicVolume

namespace IUT.PaperIV.LocalFields

/-! ## 1. Ultrametric sums whose nonzero terms have distinct norms -/

/-- In an ultrametric normed field, if no two of the first `n` terms `y i` share a norm unless the
earlier one is `0`, then each term has norm at most the norm of the sum (and the norm of the sum
is `0` or the norm of one of the terms). -/
theorem locDiscCu_norm_le_sum {F : Type*} [NormedField F] [IsUltrametricDist F] (y : ℕ → F)
    (n : ℕ) (hy : ∀ i j, i < j → j < n → ‖y i‖ = ‖y j‖ → y i = 0) :
    (∀ i < n, ‖y i‖ ≤ ‖∑ i ∈ Finset.range n, y i‖) ∧
      (‖∑ i ∈ Finset.range n, y i‖ = 0 ∨ ∃ k < n, ‖∑ i ∈ Finset.range n, y i‖ = ‖y k‖) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih fun i j hij hj => hy i j hij (by omega)
    rw [Finset.sum_range_succ]
    by_cases hne : ‖∑ i ∈ Finset.range n, y i‖ = ‖y n‖
    · have hyn : y n = 0 := by
        rcases h2 with h0 | ⟨k, hk, hSk⟩
        · exact norm_eq_zero.1 (hne.symm.trans h0)
        · have hk0 := hy k n hk (by omega) (hSk.symm.trans hne)
          rw [hk0, norm_zero] at hSk
          exact norm_eq_zero.1 (hne.symm.trans hSk)
      rw [hyn, add_zero]
      refine ⟨fun i hi => ?_, ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact h1 i hi
        · rw [hyn, norm_zero]
          exact norm_nonneg _
      · rcases h2 with h0 | ⟨k, hk, hSk⟩
        · exact Or.inl h0
        · exact Or.inr ⟨k, by omega, hSk⟩
    · rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne]
      refine ⟨fun i hi => ?_, ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact (h1 i hi).trans (le_max_left _ _)
        · exact le_max_right _ _
      · rcases le_total ‖∑ i ∈ Finset.range n, y i‖ ‖y n‖ with h | h
        · exact Or.inr ⟨n, by omega, max_eq_right h⟩
        · rw [max_eq_left h]
          rcases h2 with h0 | ⟨k, hk, hSk⟩
          · exact Or.inl h0
          · exact Or.inr ⟨k, by omega, hSk⟩

/-! ## 2. A sixth root of `−p`: integral coordinates -/

section Sixth

variable (p : ℕ) [hp : Fact p.Prime]

/-- The sixth power of `‖q‖ s^j` when `s ^ 6 = p⁻¹`: `p ^ (−6 v_p(q) − j)`. -/
theorem locDiscCu_six_eq {s : ℝ} (hs : s ^ 6 = (p : ℝ)⁻¹) {q : ℚ_[p]} (hq : q ≠ 0) (j : ℕ) :
    (‖q‖ * s ^ j) ^ 6 = (p : ℝ) ^ (-q.valuation * 6 - j) := by
  have hP : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have e1 : ((p : ℝ) ^ (-q.valuation)) ^ 6 = (p : ℝ) ^ (-q.valuation * 6) := by
    rw [← zpow_natCast, ← zpow_mul]
    norm_num
  have e2 : ((p : ℝ)⁻¹) ^ j = (p : ℝ) ^ (-(j : ℤ)) := by rw [zpow_neg, zpow_natCast, inv_pow]
  rw [mul_pow, ← pow_mul, mul_comm j 6, pow_mul, hs, Padic.norm_eq_zpow_neg_valuation hq, e1, e2,
    ← zpow_add₀ hP.ne']
  congr 1

/-- **Distinct norm classes**: with `s ^ 6 = p⁻¹` and `j < j' ≤ 5`, `‖q‖ s^j = ‖q'‖ s^{j'}` forces
`q = 0`. -/
theorem locDiscCu_norm_ne {s : ℝ} (hs : s ^ 6 = (p : ℝ)⁻¹) (q q' : ℚ_[p]) {j j' : ℕ}
    (hjj : j < j') (hj' : j' ≤ 5) (h : ‖q‖ * s ^ j = ‖q'‖ * s ^ j') : q = 0 := by
  have hP : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hP1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hsn : s ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hs
    exact (inv_pos.2 hP).ne' hs.symm
  by_contra hq
  by_cases hq' : q' = 0
  · rw [hq', norm_zero, zero_mul] at h
    exact hq (norm_eq_zero.1 ((mul_eq_zero.1 h).resolve_right (pow_ne_zero _ hsn)))
  have h6 := congrArg (fun t => t ^ 6) h
  rw [locDiscCu_six_eq p hs hq, locDiscCu_six_eq p hs hq'] at h6
  have := zpow_right_injective₀ hP hP1.ne' h6
  omega

/-- **Integrality from the norm**: with `s ^ 6 = p⁻¹`, `s ≥ 0` and `j ≤ 5`, `‖q‖ s^j ≤ 1` forces
`‖q‖ ≤ 1`. -/
theorem locDiscCu_le_one_of {s : ℝ} (hs : s ^ 6 = (p : ℝ)⁻¹) (hs0 : 0 ≤ s) (q : ℚ_[p]) {j : ℕ}
    (hj : j ≤ 5) (h : ‖q‖ * s ^ j ≤ 1) : ‖q‖ ≤ 1 := by
  have hP1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  by_cases hq : q = 0
  · rw [hq, norm_zero]
    exact zero_le_one
  have h6 : (‖q‖ * s ^ j) ^ 6 ≤ 1 :=
    pow_le_one₀ (mul_nonneg (norm_nonneg _) (pow_nonneg hs0 _)) h
  rw [locDiscCu_six_eq p hs hq j, zpow_le_one_iff_right₀ hP1] at h6
  rw [Padic.norm_eq_zpow_neg_valuation hq]
  exact zpow_le_one_of_nonpos₀ hP1.le (by omega)

variable {L : Type*} [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]

/-- **Coordinates of an integral element in the powers of `ϖ`**: if the spectral norm of `ϖ ∈ L`
satisfies `|ϖ| ^ 6 = p⁻¹` and `b₀ + b₁ ϖ + ⋯ + b₅ ϖ⁵` is integral over `ℤ_p`, then every
`b_k ∈ ℤ_p`. -/
theorem locDiscCu_coeff_le_one {ϖ : L} (hs : spectralNorm ℚ_[p] L ϖ ^ 6 = (p : ℝ)⁻¹)
    (b₀ b₁ b₂ b₃ b₄ b₅ : ℚ_[p])
    (h : padicVolIntegral p (algebraMap ℚ_[p] L b₀ + algebraMap ℚ_[p] L b₁ * ϖ +
      algebraMap ℚ_[p] L b₂ * ϖ ^ 2 + algebraMap ℚ_[p] L b₃ * ϖ ^ 3 +
      algebraMap ℚ_[p] L b₄ * ϖ ^ 4 + algebraMap ℚ_[p] L b₅ * ϖ ^ 5)) :
    ‖b₀‖ ≤ 1 ∧ ‖b₁‖ ≤ 1 ∧ ‖b₂‖ ≤ 1 ∧ ‖b₃‖ ≤ 1 ∧ ‖b₄‖ ≤ 1 ∧ ‖b₅‖ ≤ 1 := by
  rw [volBridge_padicVolIntegral_iff] at h
  let _ := spectralNorm.normedField ℚ_[p] L
  let _ := spectralNorm.normedAlgebra ℚ_[p] L
  have : IsUltrametricDist L := extLog_isUltrametricDist p
  change ‖(_ : L)‖ ≤ 1 at h
  change ‖ϖ‖ ^ 6 = _ at hs
  have hs0 : 0 ≤ ‖ϖ‖ := norm_nonneg _
  let b : ℕ → ℚ_[p] := fun i => [b₀, b₁, b₂, b₃, b₄, b₅].getD i 0
  have hn : ∀ i, ‖algebraMap ℚ_[p] L (b i) * ϖ ^ i‖ = ‖b i‖ * ‖ϖ‖ ^ i := fun i => by
    rw [norm_mul, norm_algebraMap', norm_pow]
  obtain ⟨h1, -⟩ := locDiscCu_norm_le_sum (fun i => algebraMap ℚ_[p] L (b i) * ϖ ^ i) 6
    fun i j hij hj hij' => by
      have hij'' : ‖b i‖ * ‖ϖ‖ ^ i = ‖b j‖ * ‖ϖ‖ ^ j := by rw [← hn, ← hn]; exact hij'
      change algebraMap ℚ_[p] L (b i) * ϖ ^ i = 0
      rw [locDiscCu_norm_ne p hs (b i) (b j) hij (by omega) hij'', map_zero, zero_mul]
  have hsum : ∑ i ∈ Finset.range 6, algebraMap ℚ_[p] L (b i) * ϖ ^ i =
      algebraMap ℚ_[p] L b₀ + algebraMap ℚ_[p] L b₁ * ϖ + algebraMap ℚ_[p] L b₂ * ϖ ^ 2 +
        algebraMap ℚ_[p] L b₃ * ϖ ^ 3 + algebraMap ℚ_[p] L b₄ * ϖ ^ 4 +
          algebraMap ℚ_[p] L b₅ * ϖ ^ 5 := by
    simp [Finset.sum_range_succ, b]
  have key : ∀ k, k ≤ 5 → ‖b k‖ ≤ 1 := fun k hk => by
    have h2 : ‖algebraMap ℚ_[p] L (b k) * ϖ ^ k‖ ≤
        ‖∑ i ∈ Finset.range 6, algebraMap ℚ_[p] L (b i) * ϖ ^ i‖ := h1 k (by omega)
    rw [hsum, hn] at h2
    exact locDiscCu_le_one_of p hs hs0 (b k) hk (h2.trans h)
  exact ⟨key 0 (by norm_num), key 1 (by norm_num), key 2 (by norm_num), key 3 (by norm_num),
    key 4 (by norm_num), key 5 le_rfl⟩

end Sixth

/-- `|ϖ| ^ 6 = 3⁻¹` for the spectral norm when `ϖ ^ 6 = −3`. -/
theorem locDiscCu_spectralNorm_six {L : Type*} [Field L] [Algebra ℚ_[3] L]
    [FiniteDimensional ℚ_[3] L] {ϖ : L} (hϖ : ϖ ^ 6 = -3) :
    spectralNorm ℚ_[3] L ϖ ^ 6 = ((3 : ℕ) : ℝ)⁻¹ := by
  let _ := spectralNorm.normedField ℚ_[3] L
  let _ := spectralNorm.normedAlgebra ℚ_[3] L
  change ‖ϖ‖ ^ 6 = _
  rw [← norm_pow, hϖ, show (-3 : L) = algebraMap ℚ_[3] L (-((3 : ℕ) : ℚ_[3])) by
    rw [map_neg, map_natCast]; norm_num, norm_algebraMap', norm_neg, Padic.norm_p]

/-- **A sixth root of `−3`**: some field of finite degree over `ℚ_3` contains `ϖ` with
`ϖ ^ 6 = −3` (the quotient of `ℚ_3[X]` by an irreducible factor of `X ^ 6 + 3`). -/
theorem locDiscCu_exists_sixth : ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ_[3] L)
    (_ : FiniteDimensional ℚ_[3] L), ∃ ϖ : L, ϖ ^ 6 = -3 := by
  have hdeg : 0 < (Polynomial.X ^ 6 + Polynomial.C (3 : ℚ_[3])).degree := by
    rw [Polynomial.degree_X_pow_add_C (by norm_num)]
    exact WithBot.coe_lt_coe.2 (by norm_num)
  obtain ⟨g, hg, hdvd⟩ := Polynomial.exists_irreducible_of_degree_pos hdeg
  have : Fact (Irreducible g) := ⟨hg⟩
  refine ⟨AdjoinRoot g, inferInstance, inferInstance,
    (AdjoinRoot.powerBasis hg.ne_zero).finite, AdjoinRoot.root g, ?_⟩
  have h0 : Polynomial.aeval (AdjoinRoot.root g) g = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have h := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdvd h0
  rw [map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_ofNat] at h
  linear_combination h

/-! ## 3. Algebraic identities -/

/-- **The dual elements**: in a commutative ring with `u³ = v³ = 3`, `3 k = 1` and `2 t = 1`, the
element `Σ a_{3i+j} u^i v^j` is the combination, with the nine linear forms of `locDiscCuMat` as
coefficients, of `1, v, v², u, w, 1 − x, t (w⁴ + w), e − 1, w²`, where `x = k u v²`,
`e = k (1 + x + x²)` and `w = k v (u − v)`. -/
theorem locDiscCu_ring_identity {R : Type*} [CommRing R]
    (u v k t a0 a1 a2 a3 a4 a5 a6 a7 a8 : R)
    (hu : u ^ 3 = 3) (hv : v ^ 3 = 3) (hk : k * 3 = 1) (ht : t * 2 = 1) :
    a0 + a1 * v + a2 * v ^ 2 + a3 * u + a4 * (u * v) + a5 * (u * v ^ 2) + a6 * u ^ 2 +
        a7 * (u ^ 2 * v) + a8 * (u ^ 2 * v ^ 2) =
      (a0 + 3 * a5 + 3 * a7) + (a1 - 3 * a8) * v + (a2 + a4 + a6) * v ^ 2 +
        (a3 + 6 * a8) * u + 3 * a4 * (k * v * (u - v)) +
        (-3 * a5 + 3 * a7) * (1 - k * u * v ^ 2) +
        3 * a6 * (t * ((k * v * (u - v)) ^ 4 + k * v * (u - v))) +
        9 * a7 * (k * (1 + k * u * v ^ 2 + (k * u * v ^ 2) ^ 2) - 1) +
        9 * a8 * (k * v * (u - v)) ^ 2 := by
  linear_combination (-3 * a6 * k ^ 4 * t * u * v ^ 4 + 12 * a6 * k ^ 4 * t * v ^ 5) * hu +
    (-18 * a6 * k ^ 4 * t * u ^ 2 * v ^ 3 - 54 * a6 * k ^ 4 * t * u ^ 2 +
      12 * a6 * k ^ 4 * t * u * v ^ 4 + 27 * a6 * k ^ 4 * t * u * v - 3 * a6 * k ^ 4 * t * v ^ 5 +
      27 * a6 * k ^ 4 * t * v ^ 2 - 9 * a7 * k ^ 3 * u ^ 2 * v + 18 * a8 * k ^ 2 * u -
      9 * a8 * k ^ 2 * v) * hv +
    (-a4 * u * v + a4 * v ^ 2 - a5 * u * v ^ 2 - 54 * a6 * k ^ 3 * t * u ^ 2 +
      27 * a6 * k ^ 3 * t * u * v + 27 * a6 * k ^ 3 * t * v ^ 2 - 18 * a6 * k ^ 2 * t * u ^ 2 +
      9 * a6 * k ^ 2 * t * u * v + 9 * a6 * k ^ 2 * t * v ^ 2 - 6 * a6 * k * t * u ^ 2 +
      3 * a6 * k * t * u * v + 3 * a6 * k * t * v ^ 2 - 2 * a6 * t * u ^ 2 +
      2 * a6 * t * v ^ 2 - 9 * a7 * k ^ 2 * u ^ 2 * v - 3 * a7 * k * u ^ 2 * v -
      3 * a7 * k * u * v ^ 2 - a7 * u ^ 2 * v - 3 * a7 - 3 * a8 * k * u ^ 2 * v ^ 2 +
      18 * a8 * k * u - 9 * a8 * k * v - a8 * u ^ 2 * v ^ 2 + 6 * a8 * u - 3 * a8 * v) * hk +
    (-a6 * u ^ 2 + a6 * v ^ 2) * ht

/-- `x = k u v²` satisfies `x³ = 1` (`u³ = v³ = 3`, `3 k = 1`). -/
theorem locDiscCu_x_cube {R : Type*} [CommRing R] (u v k : R) (hu : u ^ 3 = 3)
    (hv : v ^ 3 = 3) (hk : k * 3 = 1) : (k * u * v ^ 2) ^ 3 = 1 := by
  linear_combination (k ^ 3 * v ^ 6) * hu + (3 * k ^ 3 * (v ^ 3 + 3)) * hv +
    (9 * k ^ 2 + 3 * k + 1) * hk

/-- `e = k (1 + x + x²)` with `x = k u v²` is idempotent. -/
theorem locDiscCu_e_idem {R : Type*} [CommRing R] (u v k : R) (hu : u ^ 3 = 3)
    (hv : v ^ 3 = 3) (hk : k * 3 = 1) :
    k * (1 + k * u * v ^ 2 + (k * u * v ^ 2) ^ 2) * (k * (1 + k * u * v ^ 2 + (k * u * v ^ 2) ^ 2))
      = k * (1 + k * u * v ^ 2 + (k * u * v ^ 2) ^ 2) := by
  linear_combination (k ^ 5 * v ^ 6 * (k * u * v ^ 2 + 2)) * hu +
    (k ^ 3 * (3 * k ^ 3 * u * v ^ 5 + 9 * k ^ 3 * u * v ^ 2 + 6 * k ^ 2 * v ^ 3 + 18 * k ^ 2 +
      3 * k * u ^ 2 * v - u ^ 2 * v)) * hv +
    (k * (9 * k ^ 4 * u * v ^ 2 + 3 * k ^ 3 * u * v ^ 2 + 18 * k ^ 3 + 3 * k ^ 2 * u ^ 2 * v +
      k ^ 2 * u * v ^ 2 + 6 * k ^ 2 + k * u * v ^ 2 + 2 * k + 1)) * hk

/-- `w = k v (u − v)` satisfies `w⁷ + 3 w = 0`. -/
theorem locDiscCu_w_rel {R : Type*} [CommRing R] (u v k : R) (hu : u ^ 3 = 3)
    (hv : v ^ 3 = 3) (hk : k * 3 = 1) : (k * v * (u - v)) ^ 7 + 3 * (k * v * (u - v)) = 0 := by
  linear_combination (k ^ 7 * v ^ 7 * (u ^ 4 - 7 * u ^ 3 * v + 21 * u ^ 2 * v ^ 2 -
      35 * u * v ^ 3 + 3 * u + 35 * v ^ 4 - 21 * v)) * hu +
    (-k ^ 7 * v * (21 * u ^ 2 * v ^ 8 - 7 * u * v ^ 9 + 84 * u * v ^ 6 + 243 * u * v ^ 3 +
      729 * u + v ^ 10 - 102 * v ^ 7 - 243 * v ^ 4 - 729 * v)) * hv +
    (-3 * k * v * (3 * k + 1) * (u - v) * (9 * k ^ 2 - 3 * k + 1) * (9 * k ^ 2 + 3 * k + 1)) * hk

/-! ## 4. The nine linear forms -/

/-- The integer matrix of the nine linear forms in the coordinates `c_{3i+j}` of `π^i ⊗ π^j`:
`c₀ + 3c₅ + 3c₇`, `c₁ − 3c₈`, `c₂ + c₄ + c₆`, `c₃ + 6c₈`, `3c₄`, `−3c₅ + 3c₇`, `3c₆`, `9c₇`,
`9c₈`. It is upper triangular. -/
def locDiscCuMatZ : Matrix (Fin 9) (Fin 9) ℤ :=
  !![1, 0, 0, 0, 0, 3, 0, 3, 0;
     0, 1, 0, 0, 0, 0, 0, 0, -3;
     0, 0, 1, 0, 1, 0, 1, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0, 6;
     0, 0, 0, 0, 3, 0, 0, 0, 0;
     0, 0, 0, 0, 0, -3, 0, 3, 0;
     0, 0, 0, 0, 0, 0, 3, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 9, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 9]

/-- `det = −3^7`. -/
theorem locDiscCuMatZ_det : locDiscCuMatZ.det = -2187 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [Fin.prod_univ_succ, locDiscCuMatZ]
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | (simp at h)

/-- The matrix of the nine linear forms over `ℚ_3`. -/
noncomputable def locDiscCuMat : Matrix (Fin 9) (Fin 9) ℚ_[3] :=
  locDiscCuMatZ.map (Int.castRingHom ℚ_[3])

theorem locDiscCuMat_det : locDiscCuMat.det = -2187 := by
  have h := (Int.castRingHom ℚ_[3]).map_det locDiscCuMatZ
  rw [RingHom.mapMatrix_apply, locDiscCuMatZ_det] at h
  rw [locDiscCuMat, ← h]
  simp

/-- The matrix `locDiscCuMat` is invertible. -/
theorem locDiscCuMat_isUnit : IsUnit locDiscCuMat.det := by
  rw [locDiscCuMat_det]
  exact isUnit_iff_ne_zero.2 (by norm_num)

/-! ## 5. The example `K = ℚ_3(π)`, `π ^ 3 = 3` -/

section Three

variable {K : Type*} [Field K] [Algebra ℚ_[3] K] [FiniteDimensional ℚ_[3] K] {π : K}

/-- `1, π, π²` as a power basis. -/
noncomputable def locDiscCuPowerBasis (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3) :
    PowerBasis ℚ_[3] K where
  gen := π
  dim := 3
  basis := locDiscExBasis 3 hK (locDiscEx_three_cast hπ)
  basis_eq_pow := locDiscExBasis_apply 3 hK (locDiscEx_three_cast hπ)

/-- The minimal polynomial of `π` is `X ^ 3 − 3`. -/
theorem locDiscCu_minpoly (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3) :
    minpoly ℚ_[3] π = Polynomial.X ^ 3 - Polynomial.C 3 := by
  have hdvd : minpoly ℚ_[3] π ∣ Polynomial.X ^ 3 - Polynomial.C 3 :=
    minpoly.dvd _ _ (by
      rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hπ]
      exact sub_eq_zero.2 (map_ofNat _ 3).symm)
  have hdeg : (minpoly ℚ_[3] π).natDegree = 3 := (locDiscCuPowerBasis hK hπ).natDegree_minpoly
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (locDiscCuPowerBasis hK hπ).isIntegral_gen)
    (Polynomial.monic_X_pow_sub_C _ (by norm_num)) hdvd
    (by rw [Polynomial.natDegree_X_pow_sub_C]; exact hdeg.ge)).symm

/-- The `ℚ_3`-algebra map `K → L` sending `π` to a cube root `y` of `3` in `L`. -/
noncomputable def locDiscCuLift (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3)
    {L : Type*} [Field L] [Algebra ℚ_[3] L] (y : L) (hy : y ^ 3 = 3) : K →ₐ[ℚ_[3]] L :=
  (locDiscCuPowerBasis hK hπ).lift y (by
    rw [show (locDiscCuPowerBasis hK hπ).gen = π from rfl, locDiscCu_minpoly hK hπ, map_sub,
      map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hy]
    exact sub_eq_zero.2 (map_ofNat _ 3).symm)

theorem locDiscCuLift_apply (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3)
    {L : Type*} [Field L] [Algebra ℚ_[3] L] (y : L) (hy : y ^ 3 = 3) :
    locDiscCuLift hK hπ y hy π = y :=
  (locDiscCuPowerBasis hK hπ).lift_gen y _

/-- The basis `π^i ⊗ π^j` of `K ⊗ K`, indexed by `3 i + j`. -/
noncomputable def locDiscCuE1 (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3) :
    Module.Basis (Fin 9) ℚ_[3] (TensorProduct ℚ_[3] K K) :=
  ((locDiscExBasis 3 hK (locDiscEx_three_cast hπ)).tensorProduct
    (locDiscExBasis 3 hK (locDiscEx_three_cast hπ))).reindex finProdFinEquiv

/-- The basis whose coordinates are the nine linear forms of `locDiscCuMat`. -/
noncomputable def locDiscCuE2 (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3) :
    Module.Basis (Fin 9) ℚ_[3] (TensorProduct ℚ_[3] K K) :=
  Module.Basis.ofEquivFun ((locDiscCuE1 hK hπ).equivFun.trans
    (locDiscCuMat.toLinearEquiv' (Matrix.invertibleOfIsUnitDet _ locDiscCuMat_isUnit)))

/-- The element `Σ c_{3i+j} π^i ⊗ π^j`, written with `u = π ⊗ 1` and `v = 1 ⊗ π`. -/
noncomputable def locDiscCuVec (π : K) (c : Fin 9 → ℚ_[3]) : TensorProduct ℚ_[3] K K :=
  c 0 • (1 : TensorProduct ℚ_[3] K K) + c 1 • ((1 : K) ⊗ₜ π) + c 2 • ((1 : K) ⊗ₜ π) ^ 2 +
    c 3 • (π ⊗ₜ (1 : K)) + c 4 • ((π ⊗ₜ (1 : K)) * ((1 : K) ⊗ₜ π)) +
    c 5 • ((π ⊗ₜ (1 : K)) * ((1 : K) ⊗ₜ π) ^ 2) + c 6 • (π ⊗ₜ (1 : K)) ^ 2 +
    c 7 • ((π ⊗ₜ (1 : K)) ^ 2 * ((1 : K) ⊗ₜ π)) +
    c 8 • ((π ⊗ₜ (1 : K)) ^ 2 * ((1 : K) ⊗ₜ π) ^ 2)

theorem locDiscCuE1_apply (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3) (i j : Fin 3) :
    locDiscCuE1 hK hπ (finProdFinEquiv (i, j)) =
      (π ⊗ₜ[ℚ_[3]] (1 : K)) ^ (i : ℕ) * ((1 : K) ⊗ₜ[ℚ_[3]] π) ^ (j : ℕ) := by
  rw [locDiscCuE1, Module.Basis.reindex_apply, Equiv.symm_apply_apply,
    Module.Basis.tensorProduct_apply, locDiscExBasis_apply, locDiscExBasis_apply,
    Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow,
    Algebra.TensorProduct.tmul_mul_tmul, one_pow, one_pow, mul_one, one_mul]

/-- Every `z ∈ K ⊗ K` is `Σ c_{3i+j} π^i ⊗ π^j` with `c` its coordinates in `locDiscCuE1`. -/
theorem locDiscCu_expand (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3)
    (z : TensorProduct ℚ_[3] K K) :
    z = locDiscCuVec π (fun m => (locDiscCuE1 hK hπ).repr z m) := by
  conv_lhs => rw [← (locDiscCuE1 hK hπ).sum_repr z]
  refine (Equiv.sum_comp (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9)
    (fun m => (locDiscCuE1 hK hπ).repr z m • locDiscCuE1 hK hπ m)).symm.trans ?_
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, locDiscCuE1_apply]
  have h0 : finProdFinEquiv ((0 : Fin 3), (0 : Fin 3)) = (0 : Fin 9) := rfl
  have h1 : finProdFinEquiv ((0 : Fin 3), (1 : Fin 3)) = (1 : Fin 9) := rfl
  have h2 : finProdFinEquiv ((0 : Fin 3), (2 : Fin 3)) = (2 : Fin 9) := rfl
  have h3 : finProdFinEquiv ((1 : Fin 3), (0 : Fin 3)) = (3 : Fin 9) := rfl
  have h4 : finProdFinEquiv ((1 : Fin 3), (1 : Fin 3)) = (4 : Fin 9) := rfl
  have h5 : finProdFinEquiv ((1 : Fin 3), (2 : Fin 3)) = (5 : Fin 9) := rfl
  have h6 : finProdFinEquiv ((2 : Fin 3), (0 : Fin 3)) = (6 : Fin 9) := rfl
  have h7 : finProdFinEquiv ((2 : Fin 3), (1 : Fin 3)) = (7 : Fin 9) := rfl
  have h8 : finProdFinEquiv ((2 : Fin 3), (2 : Fin 3)) = (8 : Fin 9) := rfl
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, Fin.val_zero, Fin.val_one, Fin.val_two,
    pow_zero, pow_one, mul_one, one_mul, locDiscCuVec]
  abel

/-- The coordinates in `locDiscCuE2` are the nine linear forms. -/
theorem locDiscCuE2_repr (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3)
    (z : TensorProduct ℚ_[3] K K) (k : Fin 9) :
    (locDiscCuE2 hK hπ).repr z k = ∑ m, locDiscCuMat k m * (locDiscCuE1 hK hπ).repr z m := by
  rw [locDiscCuE2, Module.Basis.ofEquivFun_repr_apply, LinearEquiv.trans_apply]
  change (Matrix.toLin' locDiscCuMat ((locDiscCuE1 hK hπ).equivFun z)) k = _
  rw [Matrix.toLin'_apply]
  simp [Matrix.mulVec, dotProduct]

theorem locDiscCu_lattice_E1 (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3) :
    tOrdIdxLattice (locDiscCuE1 hK hπ) = tOrdIdxLattice
      ((locDiscExBasis 3 hK (locDiscEx_three_cast hπ)).tensorProduct
        (locDiscExBasis 3 hK (locDiscEx_three_cast hπ))) := by
  ext z
  simp only [tOrdIdx_mem_lattice, locDiscCuE1, Module.Basis.repr_reindex_apply]
  exact ⟨fun h i => by simpa using h (finProdFinEquiv i), fun h m => h _⟩

theorem locDiscCu_det (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3) :
    (locDiscCuE2 hK hπ).det (locDiscCuE1 hK hπ) = -2187 := by
  rw [Module.Basis.det_apply, ← locDiscCuMat_det]
  congr 1
  ext i j
  rw [Module.Basis.toMatrix_apply, locDiscCuE2_repr]
  simp [Finsupp.single_apply]

theorem locDiscCu_E1_le_E2 (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3) :
    tOrdIdxLattice (locDiscCuE1 hK hπ) ≤ tOrdIdxLattice (locDiscCuE2 hK hπ) := by
  intro z hz k
  rw [locDiscCuE2_repr, ← PadicInt.mem_subring_iff]
  refine Subring.sum_mem _ fun m _ => Subring.mul_mem _ ?_ ((PadicInt.mem_subring_iff 3).2 (hz m))
  rw [locDiscCuMat, Matrix.map_apply, Int.coe_castRingHom]
  exact intCast_mem _ _

/-- The nine linear forms, row by row. -/
theorem locDiscCu_rows (c : Fin 9 → ℚ_[3]) (k : Fin 9) :
    ∑ m, locDiscCuMat k m * c m = ![c 0 + 3 * c 5 + 3 * c 7, c 1 - 3 * c 8, c 2 + c 4 + c 6,
      c 3 + 6 * c 8, 3 * c 4, -3 * c 5 + 3 * c 7, 3 * c 6, 9 * c 7, 9 * c 8] k := by
  fin_cases k <;> simp [Fin.sum_univ_succ, locDiscCuMat, locDiscCuMatZ] <;> ring

/-- **Upper bound on the normalization**: if `Σ c_{3i+j} π^i ⊗ π^j` is integral over `ℤ_3`, the
nine linear forms take values in `ℤ_3`. Proof: the images under the multiplication map to `K`
and under the map to `L ∋ ϖ`, `ϖ ^ 6 = −3`, are integral, and their coordinates are integral
combinations of the nine forms (and conversely). -/
theorem locDiscCu_bound_aux (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3)
    (c : Fin 9 → ℚ_[3]) (hz : padicVolIntegral 3 (locDiscCuVec π c)) :
    ‖c 0 + 3 * c 5 + 3 * c 7‖ ≤ 1 ∧ ‖c 1 - 3 * c 8‖ ≤ 1 ∧ ‖c 2 + c 4 + c 6‖ ≤ 1 ∧
      ‖c 3 + 6 * c 8‖ ≤ 1 ∧ ‖3 * c 4‖ ≤ 1 ∧ ‖-3 * c 5 + 3 * c 7‖ ≤ 1 ∧ ‖3 * c 6‖ ≤ 1 ∧
        ‖9 * c 7‖ ≤ 1 ∧ ‖9 * c 8‖ ≤ 1 := by
  have hπ' := locDiscEx_three_cast hπ
  -- the multiplication map to `K`
  have hK1 := padicVolIntegral_map (p := 3) (Algebra.TensorProduct.lmul' ℚ_[3] (S := K)) hz
  have hKz : Algebra.TensorProduct.lmul' ℚ_[3] (S := K) (locDiscCuVec π c) =
      algebraMap ℚ_[3] K (c 0 + 3 * c 5 + 3 * c 7) +
        algebraMap ℚ_[3] K (c 1 + c 3 + 3 * c 8) * π +
          algebraMap ℚ_[3] K (c 2 + c 4 + c 6) * π ^ 2 := by
    simp only [locDiscCuVec, Algebra.smul_def, map_add, map_mul, map_pow,
      AlgHom.commutes, Algebra.TensorProduct.lmul'_apply_tmul, mul_one, one_mul, map_ofNat]
    linear_combination (algebraMap ℚ_[3] K (c 5) + algebraMap ℚ_[3] K (c 7) +
      algebraMap ℚ_[3] K (c 8) * π) * hπ
  rw [hKz] at hK1
  obtain ⟨hA0, hA1, hA2⟩ := locDiscEx_coeff_le_one 3 hπ' hK1
  -- the map to `L`
  obtain ⟨L, _, _, _, ϖ, hϖ⟩ := locDiscCu_exists_sixth
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[3] L).injective
  have hya : (-ϖ ^ 2) ^ 3 = (3 : L) := by linear_combination (-1 : L) * hϖ
  have hyb : (ϖ ^ 2 * (ϖ ^ 3 + 1) / 2) ^ 3 = (3 : L) := by
    linear_combination ((ϖ ^ 9 + 3 * ϖ ^ 6 - 8) / 8) * hϖ
  let Φ := Algebra.TensorProduct.productMap (locDiscCuLift hK hπ _ hya)
    (locDiscCuLift hK hπ _ hyb)
  have hL1 := padicVolIntegral_map (p := 3) Φ hz
  have hΦu : Φ (π ⊗ₜ (1 : K)) = -ϖ ^ 2 := by
    rw [Algebra.TensorProduct.productMap_apply_tmul, locDiscCuLift_apply, map_one, mul_one]
  have hΦv : Φ ((1 : K) ⊗ₜ π) = ϖ ^ 2 * (ϖ ^ 3 + 1) / 2 := by
    rw [Algebra.TensorProduct.productMap_apply_tmul, locDiscCuLift_apply, map_one, one_mul]
  have hLz : Φ (locDiscCuVec π c) =
      algebraMap ℚ_[3] L ((2 * c 0 - 3 * c 5 - 3 * c 7) / 2) +
        algebraMap ℚ_[3] L (-3 * (c 2 - c 4) / 2) * ϖ +
        algebraMap ℚ_[3] L ((c 1 - 2 * c 3 + 3 * c 8) / 2) * ϖ ^ 2 +
        algebraMap ℚ_[3] L (3 * (c 5 - c 7) / 2) * ϖ ^ 3 +
        algebraMap ℚ_[3] L (-(c 2 + c 4 - 2 * c 6) / 2) * ϖ ^ 4 +
        algebraMap ℚ_[3] L ((c 1 - 3 * c 8) / 2) * ϖ ^ 5 := by
    simp only [locDiscCuVec, Algebra.smul_def, map_add, map_mul, map_pow, map_one,
      AlgHom.commutes, hΦu, hΦv]
    simp only [map_add, map_sub, map_mul, map_neg, map_div₀, map_ofNat]
    linear_combination (ϖ ^ 8 * algebraMap ℚ_[3] L (c 8) / 4 -
      ϖ ^ 6 * algebraMap ℚ_[3] L (c 5) / 4 + ϖ ^ 5 * algebraMap ℚ_[3] L (c 8) / 2 +
      ϖ ^ 4 * algebraMap ℚ_[3] L (c 2) / 4 +
      ϖ ^ 3 * (-algebraMap ℚ_[3] L (c 5) / 2 + algebraMap ℚ_[3] L (c 7) / 2) -
      ϖ ^ 2 * algebraMap ℚ_[3] L (c 8) / 2 +
      ϖ * (algebraMap ℚ_[3] L (c 2) / 2 - algebraMap ℚ_[3] L (c 4) / 2) +
      algebraMap ℚ_[3] L (c 5) / 2 + algebraMap ℚ_[3] L (c 7) / 2) * hϖ
  rw [hLz] at hL1
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5⟩ :=
    locDiscCu_coeff_le_one 3 (locDiscCu_spectralNorm_six hϖ) _ _ _ _ _ _ hL1
  -- the nine forms are integral combinations of the coordinates
  have hS : ∀ x : ℚ_[3], ‖x‖ ≤ 1 ↔ x ∈ PadicInt.subring 3 :=
    fun x => (PadicInt.mem_subring_iff 3).symm
  rw [hS] at hA0 hA1 hA2 hb0 hb1 hb2 hb3 hb4 hb5
  have h2 : (2 : ℚ_[3]) ∈ PadicInt.subring 3 := ofNat_mem _ 2
  have h3 : (3 : ℚ_[3]) ∈ PadicInt.subring 3 := ofNat_mem _ 3
  refine ⟨hS _ |>.2 hA0, ?_, hS _ |>.2 hA2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hS, show c 1 - 3 * c 8 = 2 * ((c 1 - 3 * c 8) / 2) by ring]
    exact mul_mem h2 hb5
  · rw [hS, show c 3 + 6 * c 8 = (c 1 + c 3 + 3 * c 8) - 2 * ((c 1 - 3 * c 8) / 2) by ring]
    exact sub_mem hA1 (mul_mem h2 hb5)
  · rw [hS, show 3 * c 4 = (c 2 + c 4 + c 6) + -3 * (c 2 - c 4) / 2 -
      -(c 2 + c 4 - 2 * c 6) / 2 by ring]
    exact sub_mem (add_mem hA2 hb1) hb4
  · rw [hS, show -3 * c 5 + 3 * c 7 = -(2 * (3 * (c 5 - c 7) / 2)) by ring]
    exact neg_mem (mul_mem h2 hb3)
  · rw [hS, show 3 * c 6 = (c 2 + c 4 + c 6) + 2 * (-(c 2 + c 4 - 2 * c 6) / 2) by ring]
    exact add_mem hA2 (mul_mem h2 hb4)
  · rw [hS, show 9 * c 7 = (c 0 + 3 * c 5 + 3 * c 7) - (2 * c 0 - 3 * c 5 - 3 * c 7) / 2 -
      3 * (3 * (c 5 - c 7) / 2) by ring]
    exact sub_mem (sub_mem hA0 hb0) (mul_mem h3 hb3)
  · rw [hS, show 9 * c 8 = (c 1 + c 3 + 3 * c 8) + (c 1 - 2 * c 3 + 3 * c 8) / 2 -
      3 * ((c 1 - 3 * c 8) / 2) by ring]
    exact sub_mem (add_mem hA1 hb2) (mul_mem h3 hb5)

omit [FiniteDimensional ℚ_[3] K] in
/-- **Lower bound on the normalization**: if the nine linear forms take values in `ℤ_3` at `c`,
then `Σ c_{3i+j} π^i ⊗ π^j` is integral over `ℤ_3`. It is the combination, with these values
as coefficients, of the integral elements `1, v, v², u, w, 1 − x, (w⁴ + w) / 2, e − 1, w²`
(`locDiscCu_ring_identity`). -/
theorem locDiscCu_mem_aux (hπ : π ^ 3 = 3) (c : Fin 9 → ℚ_[3])
    (h0 : ‖c 0 + 3 * c 5 + 3 * c 7‖ ≤ 1) (h1 : ‖c 1 - 3 * c 8‖ ≤ 1)
    (h2 : ‖c 2 + c 4 + c 6‖ ≤ 1) (h3 : ‖c 3 + 6 * c 8‖ ≤ 1) (h4 : ‖3 * c 4‖ ≤ 1)
    (h5 : ‖-3 * c 5 + 3 * c 7‖ ≤ 1) (h6 : ‖3 * c 6‖ ≤ 1) (h7 : ‖9 * c 7‖ ≤ 1)
    (h8 : ‖9 * c 8‖ ≤ 1) :
    locDiscCuVec π c ∈ tensorIdxNormRing 3 K K := by
  set u : TensorProduct ℚ_[3] K K := π ⊗ₜ (1 : K) with hudef
  set v : TensorProduct ℚ_[3] K K := (1 : K) ⊗ₜ π with hvdef
  set k : TensorProduct ℚ_[3] K K := algebraMap ℚ_[3] _ 3⁻¹ with hkdef
  set t : TensorProduct ℚ_[3] K K := algebraMap ℚ_[3] _ 2⁻¹ with htdef
  have hu : u ^ 3 = 3 := by
    rw [hudef, Algebra.TensorProduct.tmul_pow, hπ, one_pow,
      ← Algebra.TensorProduct.includeLeft_apply (S := ℚ_[3]), map_ofNat]
  have hv : v ^ 3 = 3 := by
    rw [hvdef, Algebra.TensorProduct.tmul_pow, hπ, one_pow,
      ← Algebra.TensorProduct.includeRight_apply, map_ofNat]
  have hk : k * 3 = 1 := by
    rw [hkdef, show (3 : TensorProduct ℚ_[3] K K) = algebraMap ℚ_[3] _ 3 from
      (map_ofNat _ 3).symm, ← map_mul, inv_mul_cancel₀ (by norm_num), map_one]
  have ht : t * 2 = 1 := by
    rw [htdef, show (2 : TensorProduct ℚ_[3] K K) = algebraMap ℚ_[3] _ 2 from
      (map_ofNat _ 2).symm, ← map_mul, inv_mul_cancel₀ (by norm_num), map_one]
  -- integral elements
  have hsc : ∀ q : ℚ_[3], ‖q‖ ≤ 1 → algebraMap ℚ_[3] (TensorProduct ℚ_[3] K K) q ∈
      tensorIdxNormRing 3 K K := fun q hq => by
    obtain ⟨a, rfl⟩ : ∃ a : ℤ_[3], (a : ℚ_[3]) = q := ⟨⟨q, hq⟩, rfl⟩
    refine ⟨Polynomial.X - Polynomial.C a, Polynomial.monic_X_sub_C _, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]
    exact sub_self _
  have hcube : ∀ y : TensorProduct ℚ_[3] K K, y ^ 3 = 3 → y ∈ tensorIdxNormRing 3 K K :=
    fun y hy => by
      refine ⟨Polynomial.X ^ 3 - Polynomial.C 3, Polynomial.monic_X_pow_sub_C _ (by norm_num), ?_⟩
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, map_ofNat, hy,
        sub_self]
  have hum := hcube u hu
  have hvm := hcube v hv
  have hxm : k * u * v ^ 2 ∈ tensorIdxNormRing 3 K K := by
    refine ⟨Polynomial.X ^ 3 - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ (by norm_num), ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, map_one,
      locDiscCu_x_cube u v k hu hv hk, sub_self]
  have hem : k * (1 + k * u * v ^ 2 + (k * u * v ^ 2) ^ 2) ∈ tensorIdxNormRing 3 K K := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub ?_, ?_⟩
    · rw [Polynomial.degree_X]
      norm_num
    · rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, sq,
        locDiscCu_e_idem u v k hu hv hk, sub_self]
  have hwm : k * v * (u - v) ∈ tensorIdxNormRing 3 K K := by
    refine ⟨Polynomial.X ^ 7 + Polynomial.C 3 * Polynomial.X, by monicity!, ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X, map_ofNat]
    exact locDiscCu_w_rel u v k hu hv hk
  have htm : t ∈ tensorIdxNormRing 3 K K := hsc _ (by
    rw [norm_inv, show (2 : ℚ_[3]) = ((2 : ℕ) : ℚ_[3]) by norm_num,
      Padic.norm_natCast_eq_one_iff.2 (by norm_num), inv_one])
  -- the decomposition
  have hid : locDiscCuVec π c =
      algebraMap ℚ_[3] _ (c 0 + 3 * c 5 + 3 * c 7) + algebraMap ℚ_[3] _ (c 1 - 3 * c 8) * v +
        algebraMap ℚ_[3] _ (c 2 + c 4 + c 6) * v ^ 2 +
        algebraMap ℚ_[3] _ (c 3 + 6 * c 8) * u +
        algebraMap ℚ_[3] _ (3 * c 4) * (k * v * (u - v)) +
        algebraMap ℚ_[3] _ (-3 * c 5 + 3 * c 7) * (1 - k * u * v ^ 2) +
        algebraMap ℚ_[3] _ (3 * c 6) * (t * ((k * v * (u - v)) ^ 4 + k * v * (u - v))) +
        algebraMap ℚ_[3] _ (9 * c 7) * (k * (1 + k * u * v ^ 2 + (k * u * v ^ 2) ^ 2) - 1) +
        algebraMap ℚ_[3] _ (9 * c 8) * (k * v * (u - v)) ^ 2 := by
    simp only [locDiscCuVec, Algebra.smul_def, map_add, map_sub, map_mul, map_neg, map_ofNat]
    linear_combination locDiscCu_ring_identity u v k t (algebraMap ℚ_[3] _ (c 0))
      (algebraMap ℚ_[3] _ (c 1)) (algebraMap ℚ_[3] _ (c 2)) (algebraMap ℚ_[3] _ (c 3))
      (algebraMap ℚ_[3] _ (c 4)) (algebraMap ℚ_[3] _ (c 5)) (algebraMap ℚ_[3] _ (c 6))
      (algebraMap ℚ_[3] _ (c 7)) (algebraMap ℚ_[3] _ (c 8)) hu hv hk ht
  rw [hid]
  refine add_mem (add_mem (add_mem (add_mem (add_mem (add_mem (add_mem (add_mem
    (hsc _ h0) (mul_mem (hsc _ h1) hvm)) (mul_mem (hsc _ h2) (pow_mem hvm 2)))
    (mul_mem (hsc _ h3) hum)) (mul_mem (hsc _ h4) hwm))
    (mul_mem (hsc _ h5) (sub_mem (one_mem _) hxm)))
    (mul_mem (hsc _ h6) (mul_mem htm (add_mem (pow_mem hwm 4) hwm))))
    (mul_mem (hsc _ h7) (sub_mem hem (one_mem _)))) (mul_mem (hsc _ h8) (pow_mem hwm 2))

/-- **The normalization `(R_E)^∼` of `K ⊗ K`** is the `ℤ_3`-span of the basis `locDiscCuE2`:
the elements at which the nine linear forms of `locDiscCuMat` take values in `ℤ_3`. -/
theorem locDiscCu_normRing_eq (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3) :
    (tensorIdxNormRing 3 K K).toAddSubgroup = tOrdIdxLattice (locDiscCuE2 hK hπ) := by
  ext z
  rw [Subring.mem_toAddSubgroup, tOrdIdx_mem_lattice]
  constructor
  · intro hz
    have hz' : padicVolIntegral 3 z := hz
    rw [locDiscCu_expand hK hπ z] at hz'
    obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩ := locDiscCu_bound_aux hK hπ _ hz'
    intro k
    rw [locDiscCuE2_repr, locDiscCu_rows]
    fin_cases k
    exacts [g0, g1, g2, g3, g4, g5, g6, g7, g8]
  · intro hz
    have hr : ∀ k, ‖![(locDiscCuE1 hK hπ).repr z 0 + 3 * (locDiscCuE1 hK hπ).repr z 5 +
        3 * (locDiscCuE1 hK hπ).repr z 7, (locDiscCuE1 hK hπ).repr z 1 -
        3 * (locDiscCuE1 hK hπ).repr z 8, (locDiscCuE1 hK hπ).repr z 2 +
        (locDiscCuE1 hK hπ).repr z 4 + (locDiscCuE1 hK hπ).repr z 6,
        (locDiscCuE1 hK hπ).repr z 3 + 6 * (locDiscCuE1 hK hπ).repr z 8,
        3 * (locDiscCuE1 hK hπ).repr z 4, -3 * (locDiscCuE1 hK hπ).repr z 5 +
        3 * (locDiscCuE1 hK hπ).repr z 7, 3 * (locDiscCuE1 hK hπ).repr z 6,
        9 * (locDiscCuE1 hK hπ).repr z 7, 9 * (locDiscCuE1 hK hπ).repr z 8] k‖ ≤ 1 :=
      fun k => by
        rw [← locDiscCu_rows, ← locDiscCuE2_repr]
        exact hz k
    rw [locDiscCu_expand hK hπ z]
    exact locDiscCu_mem_aux hπ _ (hr 0) (hr 1) (hr 2) (hr 3) (hr 4) (hr 5) (hr 6) (hr 7) (hr 8)

/-- **The exact index**: for `K = ℚ_3(π)`, `π ^ 3 = 3`, `[(R_E)^∼ : R_E] = 3 ^ 7` for
`R_E = O_K ⊗ O_K ⊂ K ⊗ K`. -/
theorem locDiscCu_index (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3) :
    (tensorIdxRing 3 K K).toAddSubgroup.relIndex (tensorIdxNormRing 3 K K).toAddSubgroup =
      3 ^ 7 := by
  have hB := locDiscExBasis_integral 3 hK (locDiscEx_three_cast hπ)
  rw [tOrdIdx_ring_eq_lattice _ _ hB hB, ← locDiscCu_lattice_E1 hK hπ,
    locDiscCu_normRing_eq hK hπ]
  have h := tOrdIdx_relIndex_eq _ _ (locDiscCu_E1_le_E2 hK hπ)
  rw [locDiscCu_det, norm_neg, show (2187 : ℚ_[3]) = ((3 : ℕ) : ℚ_[3]) ^ 7 by norm_num,
    norm_pow, Padic.norm_p] at h
  have h' : (((tOrdIdxLattice (locDiscCuE1 hK hπ)).relIndex
      (tOrdIdxLattice (locDiscCuE2 hK hπ)) : ℕ) : ℝ) = ((3 ^ 7 : ℕ) : ℝ) := by
    rw [h]
    norm_num
  exact_mod_cast h'

/-- **`v_3(disc n) = 16`** for every basis `n` of `K ⊗ K` whose `ℤ_3`-span is `(R_E)^∼`
(`K = ℚ_3(π)`, `π ^ 3 = 3`): `locDisc_index_valuation` gives
`2 · 7 = 3 · 5 + 3 · 5 − v_3(disc n)`. -/
theorem locDiscCu_normDiscr_valuation (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3)
    (n : Module.Basis (Fin 3 × Fin 3) ℚ_[3] (TensorProduct ℚ_[3] K K))
    (hn : (tensorIdxNormRing 3 K K).toAddSubgroup = tOrdIdxLattice n) :
    (Algebra.discr ℚ_[3] n).valuation = 16 := by
  have hB := locDiscExBasis_integral 3 hK (locDiscEx_three_cast hπ)
  have h := locDisc_index_valuation _ _ hB hB n hn
  rw [locDiscCu_index hK hπ, locDiscEx_three_valuation hK hπ, Fintype.card_fin,
    multiplicity_pow_self_of_prime (Nat.prime_iff.1 Nat.prime_three) 7] at h
  omega

/-- Such a basis exists (`locDisc_exists_normBasis`), so `v_3(disc((R_E)^∼)) = 16`. -/
theorem locDiscCu_exists_normDiscr (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3) :
    ∃ n : Module.Basis (Fin 3 × Fin 3) ℚ_[3] (TensorProduct ℚ_[3] K K),
      (tensorIdxNormRing 3 K K).toAddSubgroup = tOrdIdxLattice n ∧
        (Algebra.discr ℚ_[3] n).valuation = 16 := by
  have hB := locDiscExBasis_integral 3 hK (locDiscEx_three_cast hπ)
  obtain ⟨n, hn⟩ := locDisc_exists_normBasis _ _ hB hB
  exact ⟨n, hn, locDiscCu_normDiscr_valuation hK hπ n hn⟩

end Three

end IUT.PaperIV.LocalFields
