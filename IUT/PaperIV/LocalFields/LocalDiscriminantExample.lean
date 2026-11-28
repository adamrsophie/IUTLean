import Mathlib
import IUT.PaperIV.LocalFields.LocalDiscriminant

/-!
# A non-Galois example: `K = ℚ_3(3^{1/3})` and the two-factor index for `K` with itself

Sources: IUT IV, Proposition 1.1 (page 9; the different `𝔡` of a local field) and
Proposition 1.4 (i) (page 13; the log-volume normalized at the normalization of a tensor
product), both checked against page renders; the paper of C. Zeng (hexagon 2610.00646),
Theorem 5.1 and its section 14, read in the TeX source of version 1 (no page render). The field
`ℚ_3(3^{1/3})` is chosen here: section 14 of version 1 treats the non-Galois case with the
example `ℚ_2(2^{1/3})`, and version 2 of the paper lists `ℚ(3^{1/3})` at `p = 3` in its table
of non-Galois samples, with 3-adic valuation 7 of the index. Everything here is a model test:
an explicit computation for one field, not a printed statement.

## What is proved

For a field `K` of degree `3` over `ℚ_p` containing an element `π` with `π ^ 3 = p` (for
example `ℚ_p[X] / (X ^ 3 − p)`, `locDiscEx_exists` for `p = 3`):

* `locDiscEx_spectralNorm`: for `a, b, c ∈ ℚ_p`,
  `|a + b π + c π²| = max (|a|, |b| |π|, |c| |π|²)` for the spectral norm (the three terms have
  norms in the distinct classes `p ^ ℤ`, `p ^ (ℤ − 1/3)`, `p ^ (ℤ − 2/3)`).
* `locDiscExBasis`, `locDiscExBasis_integral`: `1, π, π²` is a `ℚ_p`-basis of `K` and an
  integral basis (so the ring of integers is `ℤ_p[π]`).
* `locDiscEx_trace_*`, `locDiscEx_discr`: the traces of `1, π, …, π⁴` are `3, 0, 0, 3p, 0` and
  `disc(1, π, π²) = −27 p²`.

For `p = 3` (`π ^ 3 = 3`):

* `locDiscEx_three_valuation`: `v_3(disc(1, π, π²)) = 5`; `locDiscEx_three_differentOrder`:
  `𝔡 = 5/3`.
* `locDiscEx_valuation_odd`: `v_3(disc b)` is odd for every `ℚ_3`-basis `b` of `K`.
* `locDiscEx_index_sq_ne`: the Galois formula `[(R_E)^∼ : R_E]² = (‖disc b‖⁻¹)^d`
  (`tOrdIdx_index_sq_galois`, proved there under `IsGalois`) fails for `K ⊗ K`, for every basis
  `b`: the left side is the square of a natural number and the right side is `3` to an odd
  power. `locDiscEx_not_isGalois`: hence `K` is not Galois over `ℚ_3`.
* `locDiscEx_normDiscr_even`: for an integral basis `b` and any basis `n` whose `ℤ_3`-span is
  `(R_E)^∼`, `v_3(disc n)` is even, so it differs from `d · v_3(disc b) = 15`, the value that
  the Galois decomposition `K ⊗ K ≅ K^d` would give.
* `locDiscEx_index_bounds`: `9 ∣ [(R_E)^∼ : R_E]` (the idempotent `(1 + x + x²) / 3` with
  `x = (π ⊗ π²) / 3`, `x³ = 1`, lies in `(R_E)^∼`) and `v_3([(R_E)^∼ : R_E]) ≤ 15` (from
  `v_3(disc n) ≥ 0`, `locDiscEx_norm_discr_le_one`, which holds for any two factors).

## Not proved here

The exact index `3^7`, equivalently `v_3(disc n) = 16`, here; it is proved by another route in
`IUT.PaperIV.LocalFields.LocalDiscriminantCubic` (`locDiscCu_index`). The route sketched here
needs `(R_E)^∼` itself: the
splitting `K ⊗ K ≅ K × K(√−3)`, transport of `(R_E)^∼` to `O_K × O_{K(√−3)}` (the
normalization of a product is `volBridge_padicVolIntegral_pi`), the discriminant of a block
basis, and `v_3(disc O_{K(√−3)}) = 11` for the totally ramified
extension `K(√−3)` of degree `6` of `ℚ_3`. Then `v_3(disc n) = 5 + 11` and
`2 · 7 = 15 + 15 − 16`.
-/

open IUT.Audit.TensorOrderIndex IUT.Prerequisites.PadicVolume

namespace IUT.PaperIV.LocalFields

/-! ## 1. A cube root of `p`: the norm of `a + b π + c π²` -/

section Cubic

variable (p : ℕ) [hp : Fact p.Prime]

/-- `p` has no cube root in `ℚ_p`. -/
theorem locDiscEx_not_cube (x : ℚ_[p]) : x ^ 3 ≠ (p : ℚ_[p]) := by
  intro hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow three_ne_zero] at hx
    exact hp.out.ne_zero (by exact_mod_cast hx.symm)
  have h := congrArg norm hx
  rw [norm_pow, Padic.norm_eq_zpow_neg_valuation hx0, Padic.norm_p, ← zpow_natCast,
    ← zpow_mul, ← zpow_neg_one] at h
  have := zpow_right_injective₀ (by exact_mod_cast hp.out.pos : (0 : ℝ) < p)
    (by exact_mod_cast hp.out.one_lt.ne' : (p : ℝ) ≠ 1) h
  omega

/-- The cube of `‖q‖ s^j` when `s ^ 3 = p⁻¹`: `p ^ (−3 v_p(q) − j)`. -/
theorem locDiscEx_cube_eq {s : ℝ} (hs : s ^ 3 = (p : ℝ)⁻¹) {q : ℚ_[p]} (hq : q ≠ 0) (j : ℕ) :
    (‖q‖ * s ^ j) ^ 3 = (p : ℝ) ^ (-q.valuation * 3 - j) := by
  have hP : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have e1 : ((p : ℝ) ^ (-q.valuation)) ^ 3 = (p : ℝ) ^ (-q.valuation * 3) := by
    rw [← zpow_natCast, ← zpow_mul]
    norm_num
  have e2 : ((p : ℝ)⁻¹) ^ j = (p : ℝ) ^ (-(j : ℤ)) := by rw [zpow_neg, zpow_natCast, inv_pow]
  rw [mul_pow, ← pow_mul, mul_comm j 3, pow_mul, hs, Padic.norm_eq_zpow_neg_valuation hq, e1, e2,
    ← zpow_add₀ hP.ne']
  congr 1

/-- **Distinct norm classes**: with `s ^ 3 = p⁻¹` and `j < j' ≤ 2`, `‖q‖ s^j = ‖q'‖ s^{j'}` forces
`q = q' = 0`. -/
theorem locDiscEx_norm_ne {s : ℝ} (hs : s ^ 3 = (p : ℝ)⁻¹) (q q' : ℚ_[p]) {j j' : ℕ}
    (hjj : j < j') (hj' : j' ≤ 2) (h : ‖q‖ * s ^ j = ‖q'‖ * s ^ j') : q = 0 ∧ q' = 0 := by
  have hP : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hP1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hsn : s ≠ 0 := by
    rintro rfl
    rw [zero_pow three_ne_zero] at hs
    exact (inv_pos.2 hP).ne' hs.symm
  by_cases hq : q = 0
  · subst hq
    rw [norm_zero, zero_mul] at h
    exact ⟨rfl, norm_eq_zero.1 ((mul_eq_zero.1 h.symm).resolve_right (pow_ne_zero _ hsn))⟩
  by_cases hq' : q' = 0
  · subst hq'
    rw [norm_zero, zero_mul] at h
    exact absurd (norm_eq_zero.1 ((mul_eq_zero.1 h).resolve_right (pow_ne_zero _ hsn))) hq
  exfalso
  have h3 := congrArg (fun t => t ^ 3) h
  rw [locDiscEx_cube_eq p hs hq, locDiscEx_cube_eq p hs hq'] at h3
  have := zpow_right_injective₀ hP hP1.ne' h3
  omega

/-- **Integrality from the norm**: with `s ^ 3 = p⁻¹`, `s ≥ 0` and `j ≤ 2`, `‖q‖ s^j ≤ 1` forces
`‖q‖ ≤ 1`. -/
theorem locDiscEx_le_one_of {s : ℝ} (hs : s ^ 3 = (p : ℝ)⁻¹) (hs0 : 0 ≤ s) (q : ℚ_[p]) {j : ℕ}
    (hj : j ≤ 2) (h : ‖q‖ * s ^ j ≤ 1) : ‖q‖ ≤ 1 := by
  have hP1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  by_cases hq : q = 0
  · rw [hq, norm_zero]
    exact zero_le_one
  have h3 : (‖q‖ * s ^ j) ^ 3 ≤ 1 := pow_le_one₀ (mul_nonneg (norm_nonneg _) (pow_nonneg hs0 _)) h
  rw [locDiscEx_cube_eq p hs hq j, zpow_le_one_iff_right₀ hP1] at h3
  rw [Padic.norm_eq_zpow_neg_valuation hq]
  exact zpow_le_one_of_nonpos₀ hP1.le (by omega)

variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] {π : K}

/-- `|π|³ = p⁻¹` for the spectral norm when `π ^ 3 = p`. -/
theorem locDiscEx_spectralNorm_pi (hπ : π ^ 3 = algebraMap ℚ_[p] K p) :
    spectralNorm ℚ_[p] K π ^ 3 = (p : ℝ)⁻¹ := by
  let _ := spectralNorm.normedField ℚ_[p] K
  let _ := spectralNorm.normedAlgebra ℚ_[p] K
  change ‖π‖ ^ 3 = _
  rw [← norm_pow, hπ, norm_algebraMap', Padic.norm_p]

/-- **The spectral norm of `a + b π + c π²`** (`π ^ 3 = p`): the maximum of the norms of the three
terms. -/
theorem locDiscEx_spectralNorm (hπ : π ^ 3 = algebraMap ℚ_[p] K p) (a b c : ℚ_[p]) :
    spectralNorm ℚ_[p] K (algebraMap ℚ_[p] K a + algebraMap ℚ_[p] K b * π +
        algebraMap ℚ_[p] K c * π ^ 2) =
      max ‖a‖ (max (‖b‖ * spectralNorm ℚ_[p] K π) (‖c‖ * spectralNorm ℚ_[p] K π ^ 2)) := by
  have hs := locDiscEx_spectralNorm_pi p hπ
  let _ := spectralNorm.normedField ℚ_[p] K
  let _ := spectralNorm.normedAlgebra ℚ_[p] K
  have : IsUltrametricDist K := extLog_isUltrametricDist p
  change ‖(_ : K)‖ = max ‖a‖ (max (‖b‖ * ‖π‖) (‖c‖ * ‖π‖ ^ 2))
  change ‖π‖ ^ 3 = _ at hs
  have hmax : ∀ y z : K, (‖y‖ = ‖z‖ → y = 0 ∧ z = 0) → ‖y + z‖ = max ‖y‖ ‖z‖ := by
    intro y z h
    by_cases hyz : ‖y‖ = ‖z‖
    · obtain ⟨rfl, rfl⟩ := h hyz
      simp
    · exact IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hyz
  have na : ‖algebraMap ℚ_[p] K a‖ = ‖a‖ * ‖π‖ ^ 0 := by
    rw [norm_algebraMap', pow_zero, mul_one]
  have nb : ‖algebraMap ℚ_[p] K b * π‖ = ‖b‖ * ‖π‖ ^ 1 := by
    rw [norm_mul, norm_algebraMap', pow_one]
  have nc : ‖algebraMap ℚ_[p] K c * π ^ 2‖ = ‖c‖ * ‖π‖ ^ 2 := by
    rw [norm_mul, norm_algebraMap', norm_pow]
  have hab : ‖algebraMap ℚ_[p] K a + algebraMap ℚ_[p] K b * π‖ =
      max (‖a‖ * ‖π‖ ^ 0) (‖b‖ * ‖π‖ ^ 1) := by
    rw [← na, ← nb]
    refine hmax _ _ fun h => ?_
    rw [na, nb] at h
    obtain ⟨rfl, rfl⟩ := locDiscEx_norm_ne p hs a b (by norm_num) (by norm_num) h
    simp
  rw [hmax _ _ ?_, hab, nc, pow_zero, mul_one, pow_one, max_assoc]
  intro h
  rw [hab, nc] at h
  have hc : c = 0 := by
    rcases max_choice (‖a‖ * ‖π‖ ^ 0) (‖b‖ * ‖π‖ ^ 1) with hm | hm
    · rw [hm] at h
      exact (locDiscEx_norm_ne p hs a c (by norm_num) le_rfl h).2
    · rw [hm] at h
      exact (locDiscEx_norm_ne p hs b c (by norm_num) le_rfl h).2
  subst hc
  rw [norm_zero, zero_mul, ← hab] at h
  exact ⟨norm_eq_zero.1 h, by simp⟩

/-- **The coordinates of an integral element are integral**: if `a + b π + c π²` is integral
over `ℤ_p` (`π ^ 3 = p`), then `a`, `b`, `c ∈ ℤ_p`. -/
theorem locDiscEx_coeff_le_one (hπ : π ^ 3 = algebraMap ℚ_[p] K p) {a b c : ℚ_[p]}
    (h : padicVolIntegral p (algebraMap ℚ_[p] K a + algebraMap ℚ_[p] K b * π +
      algebraMap ℚ_[p] K c * π ^ 2)) : ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 ∧ ‖c‖ ≤ 1 := by
  rw [volBridge_padicVolIntegral_iff, locDiscEx_spectralNorm p hπ] at h
  have hs := locDiscEx_spectralNorm_pi p hπ
  have hs0 : 0 ≤ spectralNorm ℚ_[p] K π := spectralNorm_nonneg _
  refine ⟨(le_max_left _ _).trans h, locDiscEx_le_one_of p hs hs0 b (j := 1) (by norm_num) ?_,
    locDiscEx_le_one_of p hs hs0 c (j := 2) le_rfl ?_⟩
  · rw [pow_one]
    exact ((le_max_left _ _).trans (le_max_right _ _)).trans h
  · exact ((le_max_right _ _).trans (le_max_right _ _)).trans h

/-- **`1, π, π²` are linearly independent** (`π ^ 3 = p`). -/
theorem locDiscEx_coeff_eq_zero (hπ : π ^ 3 = algebraMap ℚ_[p] K p) {a b c : ℚ_[p]}
    (h : algebraMap ℚ_[p] K a + algebraMap ℚ_[p] K b * π + algebraMap ℚ_[p] K c * π ^ 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hP : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have h1 := locDiscEx_spectralNorm p hπ a b c
  rw [h, spectralNorm_zero] at h1
  have hs := locDiscEx_spectralNorm_pi p hπ
  have hs0 : 0 ≤ spectralNorm ℚ_[p] K π := spectralNorm_nonneg _
  have hsn : spectralNorm ℚ_[p] K π ≠ 0 := by
    intro h0
    rw [h0, zero_pow three_ne_zero] at hs
    exact (inv_pos.2 hP).ne' hs.symm
  have hA : ‖a‖ = 0 := le_antisymm ((le_max_left _ _).trans h1.symm.le) (norm_nonneg _)
  have hB : ‖b‖ * spectralNorm ℚ_[p] K π = 0 :=
    le_antisymm (((le_max_left _ _).trans (le_max_right _ _)).trans h1.symm.le)
      (mul_nonneg (norm_nonneg _) hs0)
  have hC : ‖c‖ * spectralNorm ℚ_[p] K π ^ 2 = 0 :=
    le_antisymm (((le_max_right _ _).trans (le_max_right _ _)).trans h1.symm.le)
      (mul_nonneg (norm_nonneg _) (pow_nonneg hs0 2))
  exact ⟨norm_eq_zero.1 hA, norm_eq_zero.1 ((mul_eq_zero.1 hB).resolve_right hsn),
    norm_eq_zero.1 ((mul_eq_zero.1 hC).resolve_right (pow_ne_zero 2 hsn))⟩

/-! ## 2. The integral basis `1, π, π²` and its discriminant -/

/-- `1, π, π²` is a `ℚ_p`-basis of `K` (`[K : ℚ_p] = 3`, `π ^ 3 = p`). -/
noncomputable def locDiscExBasis (hK : Module.finrank ℚ_[p] K = 3)
    (hπ : π ^ 3 = algebraMap ℚ_[p] K p) : Module.Basis (Fin 3) ℚ_[p] K :=
  basisOfLinearIndependentOfCardEqFinrank (b := fun i : Fin 3 => π ^ (i : ℕ))
    (Fintype.linearIndependent_iff.2 fun g hg i => by
      rw [Fin.sum_univ_three] at hg
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, Algebra.smul_def,
        mul_one] at hg
      obtain ⟨h0, h1, h2⟩ := locDiscEx_coeff_eq_zero p hπ hg
      fin_cases i
      exacts [h0, h1, h2])
    (by rw [Fintype.card_fin, hK])

theorem locDiscExBasis_apply (hK : Module.finrank ℚ_[p] K = 3)
    (hπ : π ^ 3 = algebraMap ℚ_[p] K p) (i : Fin 3) :
    locDiscExBasis p hK hπ i = π ^ (i : ℕ) := by
  simp [locDiscExBasis]

/-- Every `x ∈ K` is `a + b π + c π²` with `(a, b, c)` its coordinates. -/
theorem locDiscExBasis_expand (hK : Module.finrank ℚ_[p] K = 3)
    (hπ : π ^ 3 = algebraMap ℚ_[p] K p) (x : K) :
    x = algebraMap ℚ_[p] K ((locDiscExBasis p hK hπ).repr x 0) +
      algebraMap ℚ_[p] K ((locDiscExBasis p hK hπ).repr x 1) * π +
        algebraMap ℚ_[p] K ((locDiscExBasis p hK hπ).repr x 2) * π ^ 2 := by
  conv_lhs => rw [← (locDiscExBasis p hK hπ).sum_repr x]
  rw [Fin.sum_univ_three, locDiscExBasis_apply, locDiscExBasis_apply, locDiscExBasis_apply,
    Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]
  simp

/-- **`1, π, π²` is an integral basis**: `x ∈ K` is integral over `ℤ_p` if and only if its
coordinates lie in `ℤ_p`. So the ring of integers of `K` is `ℤ_p[π]`. -/
theorem locDiscExBasis_integral (hK : Module.finrank ℚ_[p] K = 3)
    (hπ : π ^ 3 = algebraMap ℚ_[p] K p) : tOrdIdxIntegralBasis p (locDiscExBasis p hK hπ) := by
  intro x
  constructor
  · intro hx
    rw [locDiscExBasis_expand p hK hπ x] at hx
    obtain ⟨h0, h1, h2⟩ := locDiscEx_coeff_le_one p hπ hx
    intro i
    fin_cases i
    exacts [h0, h1, h2]
  · intro hx
    have hs := locDiscEx_spectralNorm_pi p hπ
    have hs0 : 0 ≤ spectralNorm ℚ_[p] K π := spectralNorm_nonneg _
    have hP1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
    have hs1 : spectralNorm ℚ_[p] K π ≤ 1 := by
      rw [← pow_le_one_iff_of_nonneg hs0 three_ne_zero, hs]
      exact inv_le_one_of_one_le₀ hP1
    rw [locDiscExBasis_expand p hK hπ x, volBridge_padicVolIntegral_iff,
      locDiscEx_spectralNorm p hπ]
    refine max_le (hx 0) (max_le ?_ ?_)
    · exact (mul_le_mul (hx 1) hs1 hs0 zero_le_one).trans_eq (one_mul 1)
    · exact (mul_le_mul (hx 2) (pow_le_one₀ hs0 hs1) (pow_nonneg hs0 2) zero_le_one).trans_eq
        (one_mul 1)

/-- The trace of `1` is `3`. -/
theorem locDiscEx_trace_one (hK : Module.finrank ℚ_[p] K = 3) :
    Algebra.trace ℚ_[p] K 1 = 3 := by
  rw [← map_one (algebraMap ℚ_[p] K), Algebra.trace_algebraMap, hK, nsmul_eq_mul]
  norm_num

/-- The trace of `π ^ 3 = p` is `3 p`. -/
theorem locDiscEx_trace_pi_cube (hK : Module.finrank ℚ_[p] K = 3)
    (hπ : π ^ 3 = algebraMap ℚ_[p] K p) : Algebra.trace ℚ_[p] K (π ^ 3) = 3 * p := by
  rw [hπ, Algebra.trace_algebraMap, hK, nsmul_eq_mul]
  norm_num

/-- The trace as the sum of the diagonal coordinates of the multiplication. -/
theorem locDiscEx_trace_eq (hK : Module.finrank ℚ_[p] K = 3)
    (hπ : π ^ 3 = algebraMap ℚ_[p] K p) (x : K) :
    Algebra.trace ℚ_[p] K x = (locDiscExBasis p hK hπ).repr x 0 +
      (locDiscExBasis p hK hπ).repr (x * π) 1 + (locDiscExBasis p hK hπ).repr (x * π ^ 2) 2 := by
  rw [Algebra.trace_eq_matrix_trace (locDiscExBasis p hK hπ), Matrix.trace_fin_three]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, locDiscExBasis_apply]
  simp

/-- The coordinates of `π`, `π²`, `π³`, `π⁴`. -/
theorem locDiscEx_repr_pows (hK : Module.finrank ℚ_[p] K = 3)
    (hπ : π ^ 3 = algebraMap ℚ_[p] K p) :
    (locDiscExBasis p hK hπ).repr π = Finsupp.single 1 1 ∧
      (locDiscExBasis p hK hπ).repr (π ^ 2) = Finsupp.single 2 1 ∧
      (locDiscExBasis p hK hπ).repr (π ^ 3) = (p : ℚ_[p]) • Finsupp.single 0 1 ∧
      (locDiscExBasis p hK hπ).repr (π ^ 4) = (p : ℚ_[p]) • Finsupp.single 1 1 := by
  set B := locDiscExBasis p hK hπ
  have b0 : B 0 = 1 := by rw [locDiscExBasis_apply]; simp
  have b1 : B 1 = π := by rw [locDiscExBasis_apply]; simp
  have b2 : B 2 = π ^ 2 := by rw [locDiscExBasis_apply]; simp
  refine ⟨by rw [← b1, B.repr_self], by rw [← b2, B.repr_self], ?_, ?_⟩
  · rw [hπ, Algebra.algebraMap_eq_smul_one, ← b0, map_smul, B.repr_self]
  · rw [show π ^ 4 = π ^ 3 * π by ring, hπ, ← Algebra.smul_def, ← b1, map_smul, B.repr_self]

/-- The trace of `π` is `0`. -/
theorem locDiscEx_trace_pi (hK : Module.finrank ℚ_[p] K = 3)
    (hπ : π ^ 3 = algebraMap ℚ_[p] K p) : Algebra.trace ℚ_[p] K π = 0 := by
  obtain ⟨r1, r2, r3, -⟩ := locDiscEx_repr_pows p hK hπ
  rw [locDiscEx_trace_eq p hK hπ, ← sq, show π * π ^ 2 = π ^ 3 by ring, r1, r2, r3]
  simp

/-- The trace of `π²` is `0`. -/
theorem locDiscEx_trace_pi_sq (hK : Module.finrank ℚ_[p] K = 3)
    (hπ : π ^ 3 = algebraMap ℚ_[p] K p) : Algebra.trace ℚ_[p] K (π ^ 2) = 0 := by
  obtain ⟨-, r2, r3, r4⟩ := locDiscEx_repr_pows p hK hπ
  rw [locDiscEx_trace_eq p hK hπ, show π ^ 2 * π = π ^ 3 by ring,
    show π ^ 2 * π ^ 2 = π ^ 4 by ring, r2, r3, r4]
  simp

/-- The trace of `π⁴ = p π` is `0`. -/
theorem locDiscEx_trace_pi_four (hK : Module.finrank ℚ_[p] K = 3)
    (hπ : π ^ 3 = algebraMap ℚ_[p] K p) : Algebra.trace ℚ_[p] K (π ^ 4) = 0 := by
  rw [show π ^ 4 = π ^ 3 * π by ring, hπ, ← Algebra.smul_def, map_smul,
    locDiscEx_trace_pi p hK hπ, smul_zero]

/-- **The discriminant of `1, π, π²`** (`π ^ 3 = p`): `−27 p²`. The trace matrix is
`[[3, 0, 0], [0, 0, 3p], [0, 3p, 0]]`. -/
theorem locDiscEx_discr (hK : Module.finrank ℚ_[p] K = 3) (hπ : π ^ 3 = algebraMap ℚ_[p] K p) :
    Algebra.discr ℚ_[p] (locDiscExBasis p hK hπ) = -27 * (p : ℚ_[p]) ^ 2 := by
  have hT : ∀ i j : Fin 3, Algebra.traceMatrix ℚ_[p] (locDiscExBasis p hK hπ) i j =
      Algebra.trace ℚ_[p] K (π ^ ((i : ℕ) + (j : ℕ))) := by
    intro i j
    rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, locDiscExBasis_apply,
      locDiscExBasis_apply, ← pow_add]
  rw [Algebra.discr_def, Matrix.det_fin_three]
  simp only [hT]
  simp [locDiscEx_trace_one p hK, locDiscEx_trace_pi p hK hπ, locDiscEx_trace_pi_sq p hK hπ,
    locDiscEx_trace_pi_cube p hK hπ, locDiscEx_trace_pi_four p hK hπ]
  ring

end Cubic

/-! ## 3. The discriminant of `(R_E)^∼` is integral (any two factors) -/

section Integral

variable {p : ℕ} [hp : Fact p.Prime] {K₁ K₂ : Type*} [Field K₁] [Field K₂] [Algebra ℚ_[p] K₁]
  [Algebra ℚ_[p] K₂] [FiniteDimensional ℚ_[p] K₁] [FiniteDimensional ℚ_[p] K₂]

/-- The trace of an element of `(R_E)^∼` lies in `ℤ_p` (`tensorDiff_isIntegralElem_trace`). -/
theorem locDiscEx_norm_trace_le_one {z : TensorProduct ℚ_[p] K₁ K₂}
    (hz : z ∈ tensorIdxNormRing p K₁ K₂) :
    ‖Algebra.trace ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂) z‖ ≤ 1 := by
  have h := tensorDiff_isIntegralElem_trace (algebraMap ℤ_[p] ℚ_[p]) hz
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ_[p]) (K := ℚ_[p])).1 h
  rw [← hy, PadicInt.algebraMap_apply, ← PadicInt.norm_def]
  exact PadicInt.norm_le_one y

/-- **`v_p(disc n) ≥ 0`** for a basis `n` whose `ℤ_p`-span is `(R_E)^∼`: the trace form is
`ℤ_p`-valued on `(R_E)^∼`. -/
theorem locDiscEx_norm_discr_le_one {κ : Type*} [Fintype κ] [DecidableEq κ]
    (n : Module.Basis κ ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂))
    (hn : (tensorIdxNormRing p K₁ K₂).toAddSubgroup = tOrdIdxLattice n) :
    ‖Algebra.discr ℚ_[p] n‖ ≤ 1 := by
  have hmem : ∀ i, n i ∈ tensorIdxNormRing p K₁ K₂ := fun i => by
    rw [← Subring.mem_toAddSubgroup, hn]
    exact tOrdIdx_basis_mem n i
  have hle : ∀ i j, ‖Algebra.traceMatrix ℚ_[p] n i j‖ ≤ 1 := fun i j => by
    rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    exact locDiscEx_norm_trace_le_one (mul_mem (hmem i) (hmem j))
  let M : Matrix κ κ ℤ_[p] := fun i j =>
    ⟨Algebra.traceMatrix ℚ_[p] n i j, (PadicInt.mem_subring_iff p).2 (hle i j)⟩
  have hM : (algebraMap ℤ_[p] ℚ_[p]).mapMatrix M = Algebra.traceMatrix ℚ_[p] n := by
    ext i j
    rfl
  rw [Algebra.discr_def, ← hM, ← RingHom.map_det, PadicInt.algebraMap_apply,
    ← PadicInt.norm_def]
  exact PadicInt.norm_le_one _

end Integral

/-! ## 4. `p = 3`: the valuation `5`, the parity obstruction and bounds for the index -/

section Three

variable {K : Type*} [Field K] [Algebra ℚ_[3] K] [FiniteDimensional ℚ_[3] K] {π : K}

omit [FiniteDimensional ℚ_[3] K] in
/-- `π ^ 3 = 3` in the form used in section 2. -/
theorem locDiscEx_three_cast (hπ : π ^ 3 = 3) : π ^ 3 = algebraMap ℚ_[3] K (3 : ℕ) := by
  rw [hπ, map_natCast]
  norm_num

/-- `‖disc(1, π, π²)‖ = 3⁻⁵` for `π ^ 3 = 3`. -/
theorem locDiscEx_three_discr_norm (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3) :
    ‖Algebra.discr ℚ_[3] (locDiscExBasis 3 hK (locDiscEx_three_cast hπ))‖ = (3 : ℝ) ^ (-5 : ℤ) := by
  rw [locDiscEx_discr]
  have h3 : ‖((3 : ℕ) : ℚ_[3])‖ = (3 : ℝ)⁻¹ := by
    rw [Padic.norm_p]
    norm_num
  have e : -27 * ((3 : ℕ) : ℚ_[3]) ^ 2 = -(((3 : ℕ) : ℚ_[3]) ^ 5) := by
    push_cast
    ring
  rw [e, norm_neg, norm_pow, h3]
  norm_num

/-- **`v_3(disc(1, π, π²)) = 5`** for `K = ℚ_3(π)`, `π ^ 3 = 3`. -/
theorem locDiscEx_three_valuation (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3) :
    (Algebra.discr ℚ_[3] (locDiscExBasis 3 hK (locDiscEx_three_cast hπ))).valuation = 5 := by
  have hne := Algebra.discr_not_zero_of_basis ℚ_[3]
    (locDiscExBasis 3 hK (locDiscEx_three_cast hπ))
  have h := locDiscEx_three_discr_norm hK hπ
  rw [Padic.norm_eq_zpow_neg_valuation hne] at h
  have h' : (3 : ℝ) ^ (-(Algebra.discr ℚ_[3]
      (locDiscExBasis 3 hK (locDiscEx_three_cast hπ))).valuation) = (3 : ℝ) ^ (-5 : ℤ) := by
    exact_mod_cast h
  have := zpow_right_injective₀ (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≠ 1) h'
  omega

/-- **`v_3(disc b)` is odd for every `ℚ_3`-basis `b` of `K`**: `disc b = det² · disc(1, π, π²)`
and `v_3(disc(1, π, π²)) = 5`. -/
theorem locDiscEx_valuation_odd (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ_[3] K) :
    Odd (Algebra.discr ℚ_[3] b).valuation := by
  set B := locDiscExBasis 3 hK (locDiscEx_three_cast hπ) with hBdef
  have hc : Fintype.card (Fin 3) = Fintype.card ι := by
    rw [Fintype.card_fin, ← Module.finrank_eq_card_basis b, hK]
  let B' := B.reindex (Fintype.equivOfCardEq hc)
  have hB' : Algebra.discr ℚ_[3] B' = Algebra.discr ℚ_[3] B := by
    simp only [B', Module.Basis.coe_reindex, Algebra.discr_reindex]
  have h := tOrdIdx_discr_change b B'
  have hd : B'.det b ≠ 0 := (B'.isUnit_det b).ne_zero
  have hD : Algebra.discr ℚ_[3] B' ≠ 0 := Algebra.discr_not_zero_of_basis ℚ_[3] B'
  rw [h, Padic.valuation_mul (pow_ne_zero 2 hd) hD, Padic.valuation_pow, hB', hBdef,
    locDiscEx_three_valuation hK hπ]
  exact ⟨(B'.det b).valuation + 2, by push_cast; ring⟩

/-- **The Galois formula fails for `K ⊗ K`** (`K = ℚ_3(π)`, `π ^ 3 = 3`): for every `ℚ_3`-basis
`b` of `K`, `[(R_E)^∼ : R_E]² ≠ (‖disc b‖⁻¹)^d` with `d = [K : ℚ_3] = 3`; this is the identity
`tOrdIdx_index_sq_galois` proves under `IsGalois`. The left side is the square of a natural
number; the right side is `3 ^ (3 v_3(disc b))` with `v_3(disc b)` odd. -/
theorem locDiscEx_index_sq_ne (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ_[3] K) :
    ((tensorIdxRing 3 K K).toAddSubgroup.relIndex (tensorIdxNormRing 3 K K).toAddSubgroup :
        ℝ) ^ 2 ≠ (‖Algebra.discr ℚ_[3] b‖⁻¹) ^ Module.finrank ℚ_[3] K := by
  intro h
  obtain ⟨k, hk⟩ := locDiscEx_valuation_odd hK hπ b
  set I := (tensorIdxRing 3 K K).toAddSubgroup.relIndex (tensorIdxNormRing 3 K K).toAddSubgroup
  have hI0 : I ≠ 0 := tensorIdx_relIndex_ne_zero 3 K K
  rw [Padic.norm_eq_zpow_neg_valuation (Algebra.discr_not_zero_of_basis ℚ_[3] b), hK, hk] at h
  have e : ((((3 : ℕ) : ℝ) ^ (-(2 * k + 1)))⁻¹) ^ 3 = (3 : ℝ) ^ ((2 * k + 1) * 3) := by
    rw [← zpow_neg, neg_neg, ← zpow_natCast, ← zpow_mul]
    norm_num
  rw [e] at h
  have hI1 : (1 : ℝ) ≤ (I : ℝ) ^ 2 :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hI0)
  by_cases hk0 : 0 ≤ k
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ (2 * k + 1) * 3)
    rw [hm, zpow_natCast] at h
    have hnat : I ^ 2 = 3 ^ m := by exact_mod_cast h
    have hv := congrArg (multiplicity 3) hnat
    rw [Nat.multiplicity_pow, Nat.multiplicity_prime_pow] at hv
    omega
  · have hlt : (3 : ℝ) ^ ((2 * k + 1) * 3) < 1 := zpow_lt_one_of_neg₀ (by norm_num) (by omega)
    linarith

/-- **`K = ℚ_3(π)` (`π ^ 3 = 3`) is not Galois over `ℚ_3`**: otherwise
`tOrdIdx_index_sq_galois` would hold for an integral basis, against `locDiscEx_index_sq_ne`. -/
theorem locDiscEx_not_isGalois (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3) :
    ¬ IsGalois ℚ_[3] K := by
  intro hG
  obtain ⟨n, b, hb⟩ := tOrdIdx_exists_integralBasis (p := 3) K
  exact locDiscEx_index_sq_ne hK hπ b (tOrdIdx_index_sq_galois b hb)

/-- **`v_3(disc (R_E)^∼)` is even**, hence differs from `d · v_3(disc b)`: for an integral basis
`b` of `K = ℚ_3(π)` and any basis `n` of `K ⊗ K` whose `ℤ_3`-span is `(R_E)^∼`. In the Galois case
`(R_E)^∼ ≅ O_K^d` gives `disc n = (disc b)^d` (`tOrdIdx_index_sq_galois`); here
`d · v_3(disc b) = 3 · 5` is odd. -/
theorem locDiscEx_normDiscr_even (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ_[3] K)
    (hb : tOrdIdxIntegralBasis 3 b) (n : Module.Basis (ι × ι) ℚ_[3] (TensorProduct ℚ_[3] K K))
    (hn : (tensorIdxNormRing 3 K K).toAddSubgroup = tOrdIdxLattice n) :
    Even (Algebra.discr ℚ_[3] n).valuation ∧
      (Algebra.discr ℚ_[3] n).valuation ≠
        (Module.finrank ℚ_[3] K : ℤ) * (Algebra.discr ℚ_[3] b).valuation := by
  have h := locDisc_index_valuation b b hb hb n hn
  obtain ⟨k, hk⟩ := locDiscEx_valuation_odd hK hπ b
  have hcard : (Fintype.card ι : ℤ) = 3 := by
    rw [← Module.finrank_eq_card_basis b, hK]
    rfl
  rw [hcard, hk] at h
  rw [hK, hk]
  refine ⟨⟨3 * (2 * k + 1) - (multiplicity 3 ((tensorIdxRing 3 K K).toAddSubgroup.relIndex
    (tensorIdxNormRing 3 K K).toAddSubgroup) : ℤ), by omega⟩, ?_⟩
  push_cast
  omega

/-- **Upper bound: `v_3([(R_E)^∼ : R_E]) ≤ 15`** for `K = ℚ_3(π)`, `π ^ 3 = 3`: by
`locDisc_index_valuation` with the integral basis `1, π, π²`,
`2 v_3(index) = 3 · 5 + 3 · 5 − v_3(disc n)`, and `v_3(disc n) ≥ 0`
(`locDiscEx_norm_discr_le_one`). -/
theorem locDiscEx_index_multiplicity_le (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3) :
    multiplicity 3 ((tensorIdxRing 3 K K).toAddSubgroup.relIndex
      (tensorIdxNormRing 3 K K).toAddSubgroup) ≤ 15 := by
  have hB := locDiscExBasis_integral 3 hK (locDiscEx_three_cast hπ)
  obtain ⟨n, hn⟩ := locDisc_exists_normBasis _ _ hB hB
  have h := locDisc_index_valuation _ _ hB hB n hn
  rw [locDiscEx_three_valuation hK hπ, Fintype.card_fin] at h
  have hv : 0 ≤ (Algebra.discr ℚ_[3] n).valuation := by
    by_cases h0 : Algebra.discr ℚ_[3] n = 0
    · rw [h0, Padic.valuation_zero]
    · have h1 := locDiscEx_norm_discr_le_one n hn
      rw [Padic.norm_eq_zpow_neg_valuation h0, zpow_le_one_iff_right₀ (by norm_num)] at h1
      omega
  omega

/-- **Lower bound: `9` divides `[(R_E)^∼ : R_E]`** for `K = ℚ_3(π)`, `π ^ 3 = 3`. With
`x = (π ⊗ π²) / 3` one has `x³ = 1`, so `e = (1 + x + x²) / 3` is an idempotent, hence lies in
`(R_E)^∼`; its coordinate at `π ⊗ π²` in the basis `π^i ⊗ π^j` of `R_E` is `1/9`. Since
`[(R_E)^∼ : R_E] · e ∈ R_E`, the index is divisible by `9`. -/
theorem locDiscEx_nine_dvd_index (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3) :
    9 ∣ (tensorIdxRing 3 K K).toAddSubgroup.relIndex (tensorIdxNormRing 3 K K).toAddSubgroup := by
  have hπ' := locDiscEx_three_cast hπ
  have hB := locDiscExBasis_integral 3 hK hπ'
  obtain ⟨r1, r2, -, r4⟩ := locDiscEx_repr_pows 3 hK hπ'
  have r0 : (locDiscExBasis 3 hK hπ').repr 1 = Finsupp.single 0 1 := by
    rw [show (1 : K) = locDiscExBasis 3 hK hπ' 0 by rw [locDiscExBasis_apply]; simp,
      Module.Basis.repr_self]
  set t : TensorProduct ℚ_[3] K K := π ⊗ₜ[ℚ_[3]] (π ^ 2) with ht
  set c : TensorProduct ℚ_[3] K K := algebraMap ℚ_[3] (TensorProduct ℚ_[3] K K) 3⁻¹ with hc
  set x : TensorProduct ℚ_[3] K K := (3 : ℚ_[3])⁻¹ • t with hx
  set e : TensorProduct ℚ_[3] K K := (3 : ℚ_[3])⁻¹ • (1 + x + x ^ 2) with he
  have hc3 : c * 3 = 1 := by
    rw [hc, show (3 : TensorProduct ℚ_[3] K K) = algebraMap ℚ_[3] _ 3 from (map_ofNat _ 3).symm,
      ← map_mul,
      inv_mul_cancel₀ (by norm_num), map_one]
  have ht3 : t ^ 3 = algebraMap ℚ_[3] (TensorProduct ℚ_[3] K K) 27 := by
    rw [ht, Algebra.TensorProduct.tmul_pow, show (π ^ 2) ^ 3 = (π ^ 3) ^ 2 by ring, hπ', ← map_pow,
      Algebra.algebraMap_eq_smul_one (((3 : ℕ) : ℚ_[3]) ^ 2), TensorProduct.tmul_smul,
      ← Algebra.TensorProduct.algebraMap_apply, Algebra.smul_def, ← map_mul]
    norm_num
  have hx3 : x ^ 3 = 1 := by
    rw [hx, Algebra.smul_def, mul_pow, ht3, ← map_pow, ← map_mul]
    norm_num
    exact Algebra.TensorProduct.one_def.symm
  have hemul : e * e = e := by
    rw [he, Algebra.smul_def]
    rw [← hc]
    linear_combination (c ^ 2 * (x + 2)) * hx3 + (c * (1 + x + x ^ 2)) * hc3
  have hemem : e ∈ tensorIdxNormRing 3 K K := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub ?_, ?_⟩
    · rw [Polynomial.degree_X]
      norm_num
    · rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, sq, hemul, sub_self]
  have hI := AddSubgroup.nsmul_relIndex_mem (tensorIdxRing 3 K K).toAddSubgroup
    (K := (tensorIdxNormRing 3 K K).toAddSubgroup) hemem
  set I := (tensorIdxRing 3 K K).toAddSubgroup.relIndex (tensorIdxNormRing 3 K K).toAddSubgroup
  rw [tOrdIdx_ring_eq_lattice _ _ hB hB, tOrdIdx_mem_lattice] at hI
  have hx2 : x ^ 2 = (3 : ℚ_[3])⁻¹ ^ 2 • ((π ^ 2) ⊗ₜ[ℚ_[3]] (π ^ 4)) := by
    rw [hx, smul_pow, ht, Algebra.TensorProduct.tmul_pow, show (π ^ 2) ^ 2 = π ^ 4 by ring]
  have hrep : ((locDiscExBasis 3 hK hπ').tensorProduct (locDiscExBasis 3 hK hπ')).repr (I • e)
      (1, 2) = (I : ℚ_[3]) * 9⁻¹ := by
    rw [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul, he, hx2, hx, ht]
    simp only [map_smul, map_add, Finsupp.smul_apply, Finsupp.add_apply,
      Algebra.TensorProduct.one_def, Module.Basis.tensorProduct_repr_tmul_apply, r0, r1, r2, r4,
      Finsupp.single_apply, smul_eq_mul]
    norm_num
  have hle := hI (1, 2)
  rw [hrep, norm_mul, norm_inv] at hle
  have h9 : ‖(9 : ℚ_[3])‖ = (3 : ℝ) ^ (-2 : ℤ) := by
    rw [show (9 : ℚ_[3]) = ((3 : ℕ) : ℚ_[3]) ^ 2 by norm_num, norm_pow, Padic.norm_p]
    norm_num
  rw [h9] at hle
  have hI3 : ‖(I : ℚ_[3])‖ ≤ (3 : ℝ) ^ (-2 : ℤ) := by
    have h0 : (0 : ℝ) < (3 : ℝ) ^ (-2 : ℤ) := zpow_pos (by norm_num) _
    have := mul_le_mul_of_nonneg_right hle h0.le
    rwa [mul_assoc, inv_mul_cancel₀ h0.ne', mul_one, one_mul] at this
  have hd := (Padic.norm_int_le_pow_iff_dvd (p := 3) (I : ℤ) 2).1
    (by rw [Int.cast_natCast]; exact_mod_cast hI3)
  norm_num at hd
  omega

/-- **Bounds for the index** (`K = ℚ_3(π)`, `π ^ 3 = 3`): `9 ∣ [(R_E)^∼ : R_E]` and
`v_3([(R_E)^∼ : R_E]) ≤ 15`. (The hand value of the exponent is `7`; it is not proved here.) -/
theorem locDiscEx_index_bounds (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3) :
    9 ∣ (tensorIdxRing 3 K K).toAddSubgroup.relIndex (tensorIdxNormRing 3 K K).toAddSubgroup ∧
      multiplicity 3 ((tensorIdxRing 3 K K).toAddSubgroup.relIndex
        (tensorIdxNormRing 3 K K).toAddSubgroup) ≤ 15 :=
  ⟨locDiscEx_nine_dvd_index hK hπ, locDiscEx_index_multiplicity_le hK hπ⟩

/-- **`𝔡 = 5/3` for `ℚ_3(π)`, `π ^ 3 = 3`**: `v_3(disc) = d · 𝔡` (`locDisc_valuation_discr`) with
`v_3(disc) = 5` and `d = 3`. -/
theorem locDiscEx_three_differentOrder [Algebra ℤ_[3] K] [IsScalarTower ℤ_[3] ℚ_[3] K]
    (hK : Module.finrank ℚ_[3] K = 3) (hπ : π ^ 3 = 3) (P : Ideal (integralClosure ℤ_[3] K))
    [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[3])] :
    letI := isDedekindDomain_ringOfIntegers_padic 3 K
    letI := isTorsionFree_ringOfIntegers_padic 3 K
    differentOrder ℤ_[3] (integralClosure ℤ_[3] K) P = 5 / 3 := by
  let := isDedekindDomain_ringOfIntegers_padic 3 K
  let := isTorsionFree_ringOfIntegers_padic 3 K
  have h := locDisc_valuation_discr P _ (locDiscExBasis_integral 3 hK (locDiscEx_three_cast hπ))
  rw [locDiscEx_three_valuation hK hπ, hK] at h
  push_cast at h
  linarith

/-- **The example exists**: `ℚ_3[X] / (X ^ 3 − 3)` is a field of degree `3` over `ℚ_3` with an
element `π` such that `π ^ 3 = 3` (`X ^ 3 − 3` has no root in `ℚ_3`, so it is irreducible). -/
theorem locDiscEx_exists :
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ_[3] K) (_ : FiniteDimensional ℚ_[3] K),
      Module.finrank ℚ_[3] K = 3 ∧ ∃ π : K, π ^ 3 = 3 := by
  have hdeg : (Polynomial.X ^ 3 - Polynomial.C (3 : ℚ_[3])).natDegree = 3 :=
    Polynomial.natDegree_X_pow_sub_C _
  have hirr : Irreducible (Polynomial.X ^ 3 - Polynomial.C (3 : ℚ_[3])) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [hdeg]
      decide
    · intro x hx
      rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C, sub_eq_zero] at hx
      exact locDiscEx_not_cube 3 x (by exact_mod_cast hx)
  have : Fact (Irreducible (Polynomial.X ^ 3 - Polynomial.C (3 : ℚ_[3]))) := ⟨hirr⟩
  have hne : Polynomial.X ^ 3 - Polynomial.C (3 : ℚ_[3]) ≠ 0 := hirr.ne_zero
  refine ⟨AdjoinRoot (Polynomial.X ^ 3 - Polynomial.C (3 : ℚ_[3])), inferInstance, inferInstance,
    (AdjoinRoot.powerBasis hne).finite, ?_, AdjoinRoot.root _, ?_⟩
  · rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  · have h := AdjoinRoot.eval₂_root (Polynomial.X ^ 3 - Polynomial.C (3 : ℚ_[3]))
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero] at h
    rw [h]
    exact map_ofNat _ 3

end Three

end IUT.PaperIV.LocalFields
