import IUT.PaperIV.LocalFields.TensorDifferent
import IUT.PaperIV.LocalFields.Packets
import IUT.PaperIV.LocalFields.Tame

/-!
# IUT IV, Propositions 1.2 (ii) to (iv) and 1.4 (iii), (iv) for two tensor factors

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Proposition 1.2 (page 10) with its
proof (page 11), Proposition 1.4 (page 13) with its proof (pages 13 and 14). Pages read for this
file: 10, 11, 13, 14 and 15. Pages checked against rendered images: 10, 11, 13 and 14 (page 15,
Proposition 1.5, is not used). Displays formalized, as printed:

* page 10: `log_p(R_E^×) = ⊗_{i ∈ E} log_p(R_i^×)`, "where the tensor product is over `ℤ_p`";
  "For `λ ∈ (1/e_i) · ℤ`, we shall write `p^λ · R_i` for the fractional ideal of `R_i` generated
  by any element `p^λ` of `k_i` such that `ord(p^λ) = λ`"; `φ` is "an automorphism of the finite
  dimensional `ℚ_p`-vector space `log_p(R_I^×) ⊗ ℚ_p` that induces an automorphism of the
  submodule `log_p(R_I^×)`";
* page 10, (ii): `φ(p^λ · (R_I)^∼) ⊆ p^{⌊λ − 𝔡_I − a_I⌋} · log_p(R_I^×) ⊆
  p^{⌊λ − 𝔡_I − a_I⌋ − b_I} · (R_I)^∼` "for any `λ ∈ (1/e_i) · ℤ`, `i ∈ I`"; "In particular,
  `φ((R_I)^∼) ⊆ p^{−⌈𝔡_I + a_I⌉} · log_p(R_I^×) ⊆ p^{−⌈𝔡_I + a_I⌉ − b_I} · (R_I)^∼`";
* page 11, (iii): "Suppose that `p > 2`, and that `e_i ≤ p − 2` for all `i ∈ I`. Then
  `φ(p^λ · (R_I)^∼) ⊆ p^{λ − 𝔡_I − 1} · (R_I)^∼`"; "In particular
  `φ((R_I)^∼) ⊆ p^{−𝔡_I − 1} · (R_I)^∼`";
* page 11, (iv): "If `p > 2` and `e_i = 1` for all `i ∈ I`, then `φ((R_I)^∼) ⊆ (R_I)^∼`";
* page 11, proof: `p^{𝔡_I + a_I} · (R_I)^∼ ⊆ ⊗_{i ∈ I} p^{a_i} · R_i (⊆ R_I = ⊗ R_i)`, then
  (i) on each factor; (iv) "follows from (ii)" with `𝔡_I = 0`, `a_I = −b_I ∈ ℤ`;
* page 13, (iii): for `I* ⊆ I` with `p − 2 ≥ e_i (≥ 1)` for `i ∈ I \ I*` and
  `λ ∈ (1/e_{i†}) · ℤ`, the inclusions of (ii) and the inequalities
  `μ^log(p^{⌊λ − 𝔡_I − a_I⌋} · log_p(R_I^×)) ≤ (−λ + 𝔡_I + 1 + 4 · |I*|/p) · log(p)` and
  `μ^log(p^{⌊λ − 𝔡_I − a_I⌋ − b_I} · (R_I)^∼) ≤ (−λ + 𝔡_I + 1) · log(p) +
  ∑_{i ∈ I*} {3 + log(e_i)}`; "Moreover, `𝔡_I + a_I ≥ |I|` if `p > 2`;
  `𝔡_I + a_I ≥ 2 · |I|` if `p = 2`";
* page 13, (iv): "If `p > 2` and `e_i = 1` for all `i ∈ I`, then `φ((R_I)^∼) ⊆ (R_I)^∼`, and
  `μ^log((R_I)^∼) = 0`"; page 13, (i): the normalization `μ^log((R_E)^∼) = 0`.

## The objects and interpretation choices

`K₁`, `K₂` are finite extensions of `ℚ_[p]` and `R_i = integralClosure ℤ_[p] K_i`; two factors
only, `I = {1, 2}`. As in `IUT.Prerequisites.PadicVolume`, `R_I` is the additive span of the
`x ⊗ y` (`x`, `y` integral) in `K₁ ⊗[ℚ_p] K₂` and `(R_I)^∼` is the set of elements integral over
`ℤ_p` (`padicPacketNormalization`). `ord` is read through the spectral norm,
`ord(x) = λ ⟺ ‖x‖ = p ^ (−λ)`. `e_i`, `𝔡_i` are the ramification index and `differentOrder` at a
prime `P_i` of `R_i` over `p` (`tensorLogDiffOrder`); `a_i`, `b_i` are `Proposition1_2.a`,
`Proposition1_2.b` at `e_i`; `𝔡_I = 𝔡_1 + 𝔡_2`, `a_I = a_1 + a_2`, `b_I = b_1 + b_2`.

* `log_p(R_I^×)` (`tensorLogLattice`) is the image in `K₁ ⊗[ℚ_p] K₂` of
  `log_p(R_1^×) ⊗_{ℤ_p} log_p(R_2^×)`: the `ℤ_p`-span of the `log_p(u₁) ⊗ log_p(u₂)`. Its
  `ℚ_p`-span is `K₁ ⊗[ℚ_p] K₂` (`tensorLog_span_lattice`), so `φ` is taken as a `ℚ_p`-linear
  automorphism of `K₁ ⊗[ℚ_p] K₂` with `φ(log_p(R_I^×)) = log_p(R_I^×)` (the printed "induces an
  automorphism of the submodule").
* `p^μ · (R_I)^∼`, for `μ` real, is `(x ⊗ y) · (R_I)^∼` (`tensorLogShift`) for any `x`, `y` with
  `‖x‖ ‖y‖ = p ^ (−μ)`; it depends only on `‖x‖ ‖y‖` (`tensorLogShift_subset` both ways). The
  printed `p^λ` is an element of one `k_i`, that is `x = p^λ`, `y = 1` or the reverse. The
  theorems hold for every real `λ` with such a representative; for `λ ∈ (1/e_i) ℤ` one exists
  (`padicBridge_exists_norm_eq_rpow`). Integer powers `p ^ n · S` are the scalar action of
  `(p : ℚ_p) ^ n`.
* `p^{k − b_I} · (R_I)^∼` is written `p ^ k · ((z₁ ⊗ z₂) · (R_I)^∼)` with `ord(z_i) = −b_i`.
* `μ^log` is `padicPacketMuLog` with reference set `(R_I)^∼`, so `μ^log((R_I)^∼) = 0` holds by
  construction (`padicPacketMuLog_self`); `tensorLog_normalization_measure` shows the reference
  set has positive finite Haar measure.

## What is proved

* `tensorLog_tmul_mem_normalization`: `x ⊗ y ∈ (R_I)^∼` when `‖x‖ ‖y‖ ≤ 1`.
* The two inclusions of page 11 around `log_p(R_I^×)`:
  `tensorLog_shift_subset_lattice` (`p^{𝔡_I + a_I} · (R_I)^∼ ⊆ log_p(R_I^×)`, through the first
  display `tensorLog_shift_subset_integers` and `tensorLog_mul_integers_subset_lattice`) and
  `tensorLog_lattice_subset_shift` (`log_p(R_I^×) ⊆ p^{−b_I} · (R_I)^∼`).
* `tensorLog_prop1_2_ii`, `tensorLog_prop1_2_ii_zero`: Proposition 1.2 (ii) and its
  "in particular", for every `φ` as above.
* `tensorLog_prop1_2_iii`, `tensorLog_prop1_2_iii_zero`: Proposition 1.2 (iii).
* `tensorLog_prop1_2_iv`: Proposition 1.2 (iv).
* `tensorLog_muLog_shift`: `μ^log((x ⊗ y) · (R_I)^∼) = log(‖x‖ ‖y‖)`.
* `tensorLog_prop1_4_iii_shift`: the second inequality of Proposition 1.4 (iii), for every
  `I*` as printed.
* `tensorLog_prop1_4_iii_lattice`: the first inequality of Proposition 1.4 (iii) when
  `p > 2` and `e_1, e_2 ≤ p − 2` (every `I*`).
* `tensorLog_dI_add_aI_ge`: the last sentence of Proposition 1.4 (iii).
* `tensorLog_prop1_4_iv`: Proposition 1.4 (iv).
* Nonvacuity for `K₁ = K₂ = ℚ_p`, `p > 2`: `e = 1` (`tensorLog_padic_ramificationIdx`),
  `log_p(ℤ_p^×) = p ℤ_p` (`tensorLog_padic_units`), `log_p(R_I^×) = p ^ 2 ℤ_p · (1 ⊗ 1)`
  (`tensorLog_padic_lattice`), `(R_I)^∼ = ℤ_p · (1 ⊗ 1)` (`tensorLog_padic_normalization`), and
  `tensorLog_padic_prop1_2_iv`: `φ = −id` satisfies the hypothesis of (iv) and (iv) applies.

## Not proved

* The first inequality of Proposition 1.4 (iii) when some `e_i > p − 2`. The page 14 proof uses
  `μ^log(log_p(R_I^×)) = ∑_i μ^log(log_p(R_i^×)) + μ^log(R_I)` (additivity over the tensor
  factors) and `μ^log(R_I) ≤ 0`; the additivity is not formalized.
* That `log_p(R_1^×) ⊗_{ℤ_p} log_p(R_2^×) → K₁ ⊗[ℚ_p] K₂` is injective, so that the image used
  here is the printed tensor product. The normalization property of `(R_I)^∼` is proved for two
  factors in `IUT.PaperIV.LocalFields.TensorIndex` (`tensorIdx_isFractionRing`).
* More than two factors.
-/

open MeasureTheory IUT.Prerequisites.PadicVolume
open scoped Pointwise

namespace IUT.PaperIV.LocalFields

/-! ## The value group of one factor -/

section OneFactor

variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [Algebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]

/-- `𝔡_i` of IUT IV Proposition 1.1 (as in `IUT.PaperIV.LocalFields.Padic`): the order of the
different of `R_i = integralClosure ℤ_[p] K` over `ℤ_p` at the prime `P` over `p`, normalized by
`ord(p) = 1` (`differentOrder`). -/
noncomputable def tensorLogDiffOrder (P : Ideal (integralClosure ℤ_[p] K)) : ℝ :=
  letI := isDedekindDomain_ringOfIntegers_padic p K
  letI := isTorsionFree_ringOfIntegers_padic p K
  differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P

/-- The elements `log_p(u)`, `u ∈ R^×`, of a finite extension `K` of `ℚ_p`: the image of the
unit group of `integralClosure ℤ_[p] K` under the `p`-adic logarithm `extLogUnit` of the spectral
norm. -/
noncomputable def tensorLogUnits : Set K :=
  @extLogUnit K (spectralNorm.normedField ℚ_[p] K) '' Set.range
    (fun u : (integralClosure ℤ_[p] K)ˣ => ((u : integralClosure ℤ_[p] K) : K))

/-- **The value group**: every nonzero `x` has `‖x‖ ^ e = p ^ k` for some `e ≥ 1` and `k ∈ ℤ`
(take `e` the ramification index). -/
theorem tensorLog_norm_pow_eq_zpow {x : K} (hx : x ≠ 0) :
    letI := spectralNorm.normedField ℚ_[p] K
    ∃ e : ℕ, 0 < e ∧ ∃ k : ℤ, ‖x‖ ^ e = (p : ℝ) ^ k := by
  let _ := spectralNorm.normedField ℚ_[p] K
  have := padicBridge_isLocalRing p K
  have := padicBridge_maximalIdeal_liesOver p K
  have := isDedekindDomain_ringOfIntegers_padic p K
  have := isTorsionFree_ringOfIntegers_padic p K
  obtain ⟨ϖ, -, -, -, -, -, hpe, hval, -⟩ :=
    padicBridge_uniformizer p K (IsLocalRing.maximalIdeal (integralClosure ℤ_[p] K))
  obtain ⟨j, hj⟩ := hval x hx
  refine ⟨(IsLocalRing.maximalIdeal (integralClosure ℤ_[p] K)).ramificationIdx ℤ_[p],
    ramificationIdx_pos_of_liesOver (IsDiscreteValuationRing.not_a_field ℤ_[p]) _, -j, ?_⟩
  rw [hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hpe, inv_zpow']

omit [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] in
/-- The norm of `p ^ k · x` for the spectral norm: `p ^ (−k) ‖x‖`. -/
theorem tensorLog_norm_p_zpow_smul (k : ℤ) (x : K) :
    letI := spectralNorm.normedField ℚ_[p] K
    ‖((p : ℚ_[p]) ^ k) • x‖ = (p : ℝ) ^ (-(k : ℝ)) * ‖x‖ := by
  let _ := spectralNorm.normedField ℚ_[p] K
  let _ := spectralNorm.normedAlgebra ℚ_[p] K
  rw [norm_smul, Padic.norm_p_zpow, ← Real.rpow_intCast]
  push_cast
  rfl

/-- An element of spectral norm at most one is integral over `ℤ_p`. -/
theorem tensorLog_integral_of_norm_le_one {x : K}
    (hx : letI := spectralNorm.normedField ℚ_[p] K; ‖x‖ ≤ 1) : padicVolIntegral p x :=
  (tensorDiff_padicVolIntegral_iff p K x).2 ((padicBridge_mem_integralClosure_iff p K x).2 hx)

/-- The ramification index of a prime over `p` is at least one. -/
theorem tensorLog_one_le_ramificationIdx (P : Ideal (integralClosure ℤ_[p] K)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] : 1 ≤ P.ramificationIdx ℤ_[p] := by
  have := isDedekindDomain_ringOfIntegers_padic p K
  have := isTorsionFree_ringOfIntegers_padic p K
  exact ramificationIdx_pos_of_liesOver (IsDiscreteValuationRing.not_a_field ℤ_[p]) P

/-- `𝔡_i ≥ 0`. -/
theorem tensorLogDiffOrder_nonneg (P : Ideal (integralClosure ℤ_[p] K)) :
    0 ≤ tensorLogDiffOrder p K P := by
  unfold tensorLogDiffOrder differentOrder
  positivity

end OneFactor

/-! ## Pure tensors in `(R_I)^∼` -/

section Tensor

variable (p : ℕ) [hp : Fact p.Prime] (K₁ K₂ : Type*) [Field K₁] [Field K₂] [Algebra ℚ_[p] K₁]
  [Algebra ℚ_[p] K₂] [FiniteDimensional ℚ_[p] K₁] [FiniteDimensional ℚ_[p] K₂]
  [Algebra ℤ_[p] K₁] [Algebra ℤ_[p] K₂] [IsScalarTower ℤ_[p] ℚ_[p] K₁]
  [IsScalarTower ℤ_[p] ℚ_[p] K₂]

omit [FiniteDimensional ℚ_[p] K₁] [FiniteDimensional ℚ_[p] K₂] [Algebra ℤ_[p] K₁]
  [Algebra ℤ_[p] K₂] [IsScalarTower ℤ_[p] ℚ_[p] K₁] [IsScalarTower ℤ_[p] ℚ_[p] K₂] in
/-- `(R_I)^∼` is closed under multiplication. -/
theorem tensorLog_mul_mem {z w : TensorProduct ℚ_[p] K₁ K₂}
    (hz : z ∈ padicPacketNormalization p K₁ K₂) (hw : w ∈ padicPacketNormalization p K₁ K₂) :
    z * w ∈ padicPacketNormalization p K₁ K₂ :=
  RingHom.IsIntegralElem.mul _ hz hw

omit [FiniteDimensional ℚ_[p] K₁] [FiniteDimensional ℚ_[p] K₂] [Algebra ℤ_[p] K₁]
  [Algebra ℤ_[p] K₂] [IsScalarTower ℤ_[p] ℚ_[p] K₁] [IsScalarTower ℤ_[p] ℚ_[p] K₂] in
/-- `(R_I)^∼` is closed under addition. -/
theorem tensorLog_add_mem {z w : TensorProduct ℚ_[p] K₁ K₂}
    (hz : z ∈ padicPacketNormalization p K₁ K₂) (hw : w ∈ padicPacketNormalization p K₁ K₂) :
    z + w ∈ padicPacketNormalization p K₁ K₂ :=
  RingHom.IsIntegralElem.add _ hz hw

omit [FiniteDimensional ℚ_[p] K₁] [FiniteDimensional ℚ_[p] K₂] [Algebra ℤ_[p] K₁]
  [Algebra ℤ_[p] K₂] [IsScalarTower ℤ_[p] ℚ_[p] K₁] [IsScalarTower ℤ_[p] ℚ_[p] K₂] in
/-- `(R_I)^∼` is a `ℤ_p`-module: `a · z ∈ (R_I)^∼` for `‖a‖ ≤ 1`. -/
theorem tensorLog_smul_mem {a : ℚ_[p]} (ha : ‖a‖ ≤ 1) {z : TensorProduct ℚ_[p] K₁ K₂}
    (hz : z ∈ padicPacketNormalization p K₁ K₂) :
    a • z ∈ padicPacketNormalization p K₁ K₂ := by
  set φ := (algebraMap ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).comp (algebraMap ℤ_[p] ℚ_[p])
  have h1 : a • z = φ ⟨a, ha⟩ * z := by
    rw [Algebra.smul_def]
    rfl
  show φ.IsIntegralElem _
  rw [h1]
  exact RingHom.IsIntegralElem.mul φ φ.isIntegralElem_map hz

omit [FiniteDimensional ℚ_[p] K₁] [FiniteDimensional ℚ_[p] K₂] [Algebra ℤ_[p] K₁]
  [Algebra ℤ_[p] K₂] [IsScalarTower ℤ_[p] ℚ_[p] K₁] [IsScalarTower ℤ_[p] ℚ_[p] K₂] in
/-- `x ⊗ y ∈ (R_I)^∼` for `x`, `y` integral over `ℤ_p`. -/
theorem tensorLog_tmul_mem_of_integral {x : K₁} {y : K₂} (hx : padicVolIntegral p x)
    (hy : padicVolIntegral p y) :
    TensorProduct.tmul ℚ_[p] x y ∈ padicPacketNormalization p K₁ K₂ :=
  padicPacketIntegers_subset p K₁ K₂ (AddSubmonoid.subset_closure ⟨x, y, hx, hy, rfl⟩)

/-- **A power of a pure tensor**: for nonzero `x ∈ K₁`, `y ∈ K₂` there are `n ≥ 1`, `m ∈ ℤ` and
`x'`, `y'` of spectral norm one with `x ^ n ⊗ y ^ n = p ^ m · (x' ⊗ y')` and
`(‖x‖ ‖y‖) ^ n = p ^ (−m)`. -/
theorem tensorLog_tmul_pow_eq {x : K₁} {y : K₂} (hx : x ≠ 0) (hy : y ≠ 0) :
    letI := spectralNorm.normedField ℚ_[p] K₁
    letI := spectralNorm.normedField ℚ_[p] K₂
    ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ, ∃ (x' : K₁) (y' : K₂), ‖x'‖ = 1 ∧ ‖y'‖ = 1 ∧
      TensorProduct.tmul ℚ_[p] (x ^ n) (y ^ n) =
        ((p : ℚ_[p]) ^ m) • TensorProduct.tmul ℚ_[p] x' y' ∧
      (‖x‖ * ‖y‖) ^ n = (p : ℝ) ^ (-m) := by
  let _ := spectralNorm.normedField ℚ_[p] K₁
  let _ := spectralNorm.normedField ℚ_[p] K₂
  let _ := spectralNorm.normedAlgebra ℚ_[p] K₁
  let _ := spectralNorm.normedAlgebra ℚ_[p] K₂
  obtain ⟨e₁, he₁, k₁, hk₁⟩ := tensorLog_norm_pow_eq_zpow p K₁ hx
  obtain ⟨e₂, he₂, k₂, hk₂⟩ := tensorLog_norm_pow_eq_zpow p K₂ hy
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpq : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set A : ℤ := k₁ * (e₂ : ℤ)
  set B : ℤ := k₂ * (e₁ : ℤ)
  have hxn : ‖x ^ (e₁ * e₂)‖ = (p : ℝ) ^ A := by
    rw [norm_pow, pow_mul, hk₁, ← zpow_natCast, ← zpow_mul]
  have hyn : ‖y ^ (e₁ * e₂)‖ = (p : ℝ) ^ B := by
    rw [norm_pow, mul_comm e₁, pow_mul, hk₂, ← zpow_natCast, ← zpow_mul]
  refine ⟨e₁ * e₂, Nat.mul_pos he₁ he₂, -(A + B), ((p : ℚ_[p]) ^ A) • x ^ (e₁ * e₂),
    ((p : ℚ_[p]) ^ B) • y ^ (e₁ * e₂), ?_, ?_, ?_, ?_⟩
  · rw [norm_smul, Padic.norm_p_zpow, hxn, ← zpow_add₀ hp0, neg_add_cancel, zpow_zero]
  · rw [norm_smul, Padic.norm_p_zpow, hyn, ← zpow_add₀ hp0, neg_add_cancel, zpow_zero]
  · rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, smul_smul,
      ← zpow_add₀ hpq, ← zpow_add₀ hpq, show -(A + B) + A + B = 0 by ring, zpow_zero, one_smul]
  · rw [mul_pow, ← norm_pow, ← norm_pow, hxn, hyn, neg_neg, zpow_add₀ hp0]

/-- **A pure tensor `x ⊗ y` with `‖x‖ ‖y‖ ≤ 1` lies in `(R_I)^∼`**, although one factor may have
norm larger than one: a power of `x ⊗ y` is `p ^ m (x' ⊗ y')` with `m ≥ 0` and `x'`, `y'` units,
and an element with an integral power is integral. -/
theorem tensorLog_tmul_mem_normalization {x : K₁} {y : K₂}
    (h : letI := spectralNorm.normedField ℚ_[p] K₁
      letI := spectralNorm.normedField ℚ_[p] K₂
      ‖x‖ * ‖y‖ ≤ 1) :
    TensorProduct.tmul ℚ_[p] x y ∈ padicPacketNormalization p K₁ K₂ := by
  let _ := spectralNorm.normedField ℚ_[p] K₁
  let _ := spectralNorm.normedField ℚ_[p] K₂
  by_cases hx : x = 0
  · rw [hx, TensorProduct.zero_tmul]
    exact packet_zero_mem_normalization p _
  by_cases hy : y = 0
  · rw [hy, TensorProduct.tmul_zero]
    exact packet_zero_mem_normalization p _
  obtain ⟨n, hn, m, x', y', hx', hy', heq, hnorm⟩ := tensorLog_tmul_pow_eq p K₁ K₂ hx hy
  have hm : 0 ≤ m := by
    have h1 : (p : ℝ) ^ (-m) ≤ 1 := hnorm ▸ pow_le_one₀ (by positivity) h
    by_contra hneg
    rw [not_le] at hneg
    have : (1 : ℝ) < (p : ℝ) ^ (-m) :=
      one_lt_zpow₀ (by exact_mod_cast hp.out.one_lt) (by omega)
    linarith
  have hint : padicVolIntegral p ((TensorProduct.tmul ℚ_[p] x y) ^ n) := by
    rw [Algebra.TensorProduct.tmul_pow, heq]
    lift m to ℕ using hm
    rw [zpow_natCast]
    exact packet_pow_smul_mem_normalization p _ (tensorLog_tmul_mem_of_integral p K₁ K₂
      (tensorLog_integral_of_norm_le_one p K₁ hx'.le)
      (tensorLog_integral_of_norm_le_one p K₂ hy'.le)) m
  let _ : Algebra ℤ_[p] (TensorProduct ℚ_[p] K₁ K₂) :=
    Algebra.compHom _ (algebraMap ℤ_[p] ℚ_[p])
  exact IsIntegral.of_pow (R := ℤ_[p]) hn hint

/-! ### `p ^ μ · (R_I)^∼` -/

/-- **`p ^ μ · (R_I)^∼`** of IUT IV pages 10 and 11, represented by a pure tensor `x ⊗ y` with
`‖x‖ ‖y‖ = p ^ (−μ)`: the set `(x ⊗ y) · (R_I)^∼`. By `tensorLogShift_subset` it depends only on
`‖x‖ ‖y‖`; for `λ ∈ (1 / e_1) ℤ` the page's `p ^ λ · (R_I)^∼` is `tensorLogShift t 1` with
`ord(t) = λ` (similarly in the second factor). -/
noncomputable def tensorLogShift (x : K₁) (y : K₂) : Set (TensorProduct ℚ_[p] K₁ K₂) :=
  (fun z => TensorProduct.tmul ℚ_[p] x y * z) '' padicPacketNormalization p K₁ K₂

/-- **Monotonicity and independence of the choices**: if `‖x‖ ‖y‖ ≤ ‖x'‖ ‖y'‖` with `x'`, `y'`
nonzero, then `(x ⊗ y) · (R_I)^∼ ⊆ (x' ⊗ y') · (R_I)^∼`. -/
theorem tensorLogShift_subset {x x' : K₁} {y y' : K₂} (hx' : x' ≠ 0) (hy' : y' ≠ 0)
    (h : letI := spectralNorm.normedField ℚ_[p] K₁
      letI := spectralNorm.normedField ℚ_[p] K₂
      ‖x‖ * ‖y‖ ≤ ‖x'‖ * ‖y'‖) :
    tensorLogShift p K₁ K₂ x y ⊆ tensorLogShift p K₁ K₂ x' y' := by
  let _ := spectralNorm.normedField ℚ_[p] K₁
  let _ := spectralNorm.normedField ℚ_[p] K₂
  rintro _ ⟨z, hz, rfl⟩
  have hpos : 0 < ‖x'‖ * ‖y'‖ := mul_pos (norm_pos_iff.2 hx') (norm_pos_iff.2 hy')
  refine ⟨TensorProduct.tmul ℚ_[p] (x / x') (y / y') * z,
    tensorLog_mul_mem p K₁ K₂ (tensorLog_tmul_mem_normalization p K₁ K₂ ?_) hz, ?_⟩
  · show ‖x / x'‖ * ‖y / y'‖ ≤ 1
    rw [norm_div, norm_div, div_mul_div_comm, div_le_one hpos]
    exact h
  · show TensorProduct.tmul ℚ_[p] x' y' * (TensorProduct.tmul ℚ_[p] (x / x') (y / y') * z) =
      TensorProduct.tmul ℚ_[p] x y * z
    rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_div_cancel₀ _ hx',
      mul_div_cancel₀ _ hy']

omit [FiniteDimensional ℚ_[p] K₁] [FiniteDimensional ℚ_[p] K₂] [Algebra ℤ_[p] K₁]
  [Algebra ℤ_[p] K₂] [IsScalarTower ℤ_[p] ℚ_[p] K₁] [IsScalarTower ℤ_[p] ℚ_[p] K₂] in
/-- `p ^ 0 · (R_I)^∼ = (R_I)^∼`. -/
theorem tensorLogShift_one :
    tensorLogShift p K₁ K₂ 1 1 = padicPacketNormalization p K₁ K₂ := by
  unfold tensorLogShift
  rw [← Algebra.TensorProduct.one_def]
  simp

omit [FiniteDimensional ℚ_[p] K₁] [FiniteDimensional ℚ_[p] K₂] [Algebra ℤ_[p] K₁]
  [Algebra ℤ_[p] K₂] [IsScalarTower ℤ_[p] ℚ_[p] K₁] [IsScalarTower ℤ_[p] ℚ_[p] K₂] in
/-- Scalars of `ℚ_p` move into the first factor: `c · ((x ⊗ y) · (R_I)^∼) =
(c x ⊗ y) · (R_I)^∼`. -/
theorem tensorLogShift_smul (c : ℚ_[p]) (x : K₁) (y : K₂) :
    c • tensorLogShift p K₁ K₂ x y = tensorLogShift p K₁ K₂ (c • x) y := by
  unfold tensorLogShift
  rw [← Set.image_smul, Set.image_image]
  congr 1
  funext z
  rw [← TensorProduct.smul_tmul', smul_mul_assoc]

end Tensor


/-! ## The lattice `log_p(R_I^×)` and Proposition 1.2 (ii) to (iv) -/

section Lattice

variable (p : ℕ) [hp : Fact p.Prime] (K₁ K₂ : Type*) [Field K₁] [Field K₂] [Algebra ℚ_[p] K₁]
  [Algebra ℚ_[p] K₂] [FiniteDimensional ℚ_[p] K₁] [FiniteDimensional ℚ_[p] K₂]
  [Algebra ℤ_[p] K₁] [Algebra ℤ_[p] K₂] [IsScalarTower ℤ_[p] ℚ_[p] K₁]
  [IsScalarTower ℤ_[p] ℚ_[p] K₂]

/-- **`log_p(R_I^×) = log_p(R_1^×) ⊗_{ℤ_p} log_p(R_2^×)`** (IUT IV page 10), as its image in
`K₁ ⊗[ℚ_p] K₂`: the `ℤ_p`-span of the pure tensors `log_p(u₁) ⊗ log_p(u₂)`, written as the
additive span of the `a · (x ⊗ y)` with `a ∈ ℤ_p`, `x ∈ log_p(R_1^×)`, `y ∈ log_p(R_2^×)`. -/
noncomputable def tensorLogLattice : Set (TensorProduct ℚ_[p] K₁ K₂) :=
  ((AddSubmonoid.closure {w | ∃ (a : ℤ_[p]) (x : K₁) (y : K₂), x ∈ tensorLogUnits p K₁ ∧
      y ∈ tensorLogUnits p K₂ ∧ w = (a : ℚ_[p]) • TensorProduct.tmul ℚ_[p] x y} :
    AddSubmonoid (TensorProduct ℚ_[p] K₁ K₂)) : Set (TensorProduct ℚ_[p] K₁ K₂))

omit [IsScalarTower ℤ_[p] ℚ_[p] K₁] [IsScalarTower ℤ_[p] ℚ_[p] K₂] in
/-- The additive span of the pure tensors `log_p(u₁) ⊗ log_p(u₂)` (the set of
`tensorDiff_mul_mem_logUnit_span`) lies in `tensorLogLattice`. -/
theorem tensorLog_closure_subset_lattice :
    ((AddSubmonoid.closure {w | ∃ x y, x ∈ tensorLogUnits p K₁ ∧ y ∈ tensorLogUnits p K₂ ∧
        w = TensorProduct.tmul ℚ_[p] x y} : AddSubmonoid (TensorProduct ℚ_[p] K₁ K₂)) :
      Set (TensorProduct ℚ_[p] K₁ K₂)) ⊆ tensorLogLattice p K₁ K₂ := by
  unfold tensorLogLattice
  refine SetLike.coe_subset_coe.2 (AddSubmonoid.closure_le.2 ?_)
  rintro _ ⟨x, y, hx, hy, rfl⟩
  exact AddSubmonoid.subset_closure ⟨1, x, y, hx, hy, by simp⟩

variable (P₁ : Ideal (integralClosure ℤ_[p] K₁)) [P₁.IsPrime]
  [P₁.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
  (P₂ : Ideal (integralClosure ℤ_[p] K₂)) [P₂.IsPrime]
  [P₂.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]

/-- **`⊗_i p ^ (a_i) · R_i ⊆ log_p(R_I^×)`**: for `u_i` with `ord(u_i) = a_i`, the image
`(u₁ ⊗ u₂) · R_I` of `p ^ (a_1) R_1 ⊗ p ^ (a_2) R_2` lies in `log_p(R_I^×)`, by Proposition
1.2 (i) on each factor. -/
theorem tensorLog_mul_integers_subset_lattice {u₁ : K₁} {u₂ : K₂}
    (hu₁ : letI := spectralNorm.normedField ℚ_[p] K₁
      ‖u₁‖ = (p : ℝ) ^ (-Proposition1_2.a p (P₁.ramificationIdx ℤ_[p])))
    (hu₂ : letI := spectralNorm.normedField ℚ_[p] K₂
      ‖u₂‖ = (p : ℝ) ^ (-Proposition1_2.a p (P₂.ramificationIdx ℤ_[p]))) :
    (fun w => TensorProduct.tmul ℚ_[p] u₁ u₂ * w) '' padicPacketIntegers p K₁ K₂ ⊆
      tensorLogLattice p K₁ K₂ := by
  obtain ⟨-, ⟨w₁, hw₁⟩, H₁⟩ := padicBridge_extLogUnit_image_fractionalIdeal p K₁ P₁
  obtain ⟨-, ⟨w₂, hw₂⟩, H₂⟩ := padicBridge_extLogUnit_image_fractionalIdeal p K₂ P₂
  have hS₁ := (H₁ u₁ w₁ hu₁ hw₁).1
  have hS₂ := (H₂ u₂ w₂ hu₂ hw₂).1
  rintro _ ⟨w, hw, rfl⟩
  unfold padicPacketIntegers at hw
  rw [SetLike.mem_coe] at hw
  unfold tensorLogLattice
  rw [SetLike.mem_coe]
  induction hw using AddSubmonoid.closure_induction with
  | mem w hw =>
    obtain ⟨x, y, hx, hy, rfl⟩ := hw
    refine AddSubmonoid.subset_closure
      ⟨1, u₁ * x, u₂ * y, hS₁ ⟨⟨x, ?_⟩, rfl⟩, hS₂ ⟨⟨y, ?_⟩, rfl⟩, ?_⟩
    · exact (tensorDiff_padicVolIntegral_iff p K₁ x).1 hx
    · exact (tensorDiff_padicVolIntegral_iff p K₂ y).1 hy
    · beta_reduce
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      simp
  | zero =>
    beta_reduce
    rw [mul_zero]
    exact zero_mem _
  | add a b _ _ ha hb =>
    beta_reduce at ha hb ⊢
    rw [mul_add]
    exact add_mem ha hb

/-- **`log_p(R_I^×) ⊆ p ^ (−b_I) · (R_I)^∼`**, the last inclusion of the first display of
Proposition 1.2 (ii) (page 10): for `z_i` with `ord(z_i) = −b_i`, every element of
`log_p(R_I^×)` is `(z₁ ⊗ z₂) · w` with `w ∈ (R_I)^∼`, by Proposition 1.2 (i) on each factor. -/
theorem tensorLog_lattice_subset_shift {z₁ : K₁} {z₂ : K₂}
    (hz₁ : letI := spectralNorm.normedField ℚ_[p] K₁
      ‖z₁‖ = (p : ℝ) ^ (Proposition1_2.b p (P₁.ramificationIdx ℤ_[p])))
    (hz₂ : letI := spectralNorm.normedField ℚ_[p] K₂
      ‖z₂‖ = (p : ℝ) ^ (Proposition1_2.b p (P₂.ramificationIdx ℤ_[p]))) :
    tensorLogLattice p K₁ K₂ ⊆ tensorLogShift p K₁ K₂ z₁ z₂ := by
  obtain ⟨⟨y₁, hy₁⟩, -, H₁⟩ := padicBridge_extLogUnit_image_fractionalIdeal p K₁ P₁
  obtain ⟨⟨y₂, hy₂⟩, -, H₂⟩ := padicBridge_extLogUnit_image_fractionalIdeal p K₂ P₂
  have hT₁ := (H₁ y₁ z₁ hy₁ hz₁).2
  have hT₂ := (H₂ y₂ z₂ hy₂ hz₂).2
  intro w hw
  unfold tensorLogLattice at hw
  rw [SetLike.mem_coe] at hw
  induction hw using AddSubmonoid.closure_induction with
  | mem w hw =>
    obtain ⟨a, x, y, hx, hy, rfl⟩ := hw
    obtain ⟨r₁, rfl⟩ := hT₁ hx
    obtain ⟨r₂, rfl⟩ := hT₂ hy
    refine ⟨(a : ℚ_[p]) • TensorProduct.tmul ℚ_[p] (r₁ : K₁) (r₂ : K₂),
      tensorLog_smul_mem p K₁ K₂ a.2 (tensorLog_tmul_mem_of_integral p K₁ K₂
        ((tensorDiff_padicVolIntegral_iff p K₁ _).2 r₁.2)
        ((tensorDiff_padicVolIntegral_iff p K₂ _).2 r₂.2)), ?_⟩
    show TensorProduct.tmul ℚ_[p] z₁ z₂ *
        ((a : ℚ_[p]) • TensorProduct.tmul ℚ_[p] (r₁ : K₁) (r₂ : K₂)) =
      (a : ℚ_[p]) • TensorProduct.tmul ℚ_[p] (z₁ * r₁) (z₂ * r₂)
    rw [mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul]
  | zero => exact ⟨0, packet_zero_mem_normalization p _, mul_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨n, hn, rfl⟩ := ha
    obtain ⟨n', hn', rfl⟩ := hb
    exact ⟨n + n', tensorLog_add_mem p K₁ K₂ hn hn', mul_add _ _ _⟩

omit [P₁.IsPrime] [P₁.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] in
/-- **The first display of the proof of Proposition 1.2 (ii)** (page 11), for two factors, in
the printed form with `𝔡_I = 𝔡_1 + 𝔡_2`: for `u_i` with `ord(u_i) = a_i` and any `x ⊗ y` with
`‖x‖ ‖y‖ ≤ p ^ (−(𝔡_I + a_I))`, `(x ⊗ y) · (R_I)^∼ ⊆ (u₁ ⊗ u₂) · R_I`, the image of
`⊗_i p ^ (a_i) · R_i`. The proof uses Proposition 1.1 for `I* = {2}`
(`tensorDiff_order_mul_mem_packetIntegers`) and `𝔡_1 ≥ 0`. -/
theorem tensorLog_shift_subset_integers {u₁ : K₁} {u₂ : K₂}
    (hu₁ : letI := spectralNorm.normedField ℚ_[p] K₁
      ‖u₁‖ = (p : ℝ) ^ (-Proposition1_2.a p (P₁.ramificationIdx ℤ_[p])))
    (hu₂ : letI := spectralNorm.normedField ℚ_[p] K₂
      ‖u₂‖ = (p : ℝ) ^ (-Proposition1_2.a p (P₂.ramificationIdx ℤ_[p])))
    {x : K₁} {y : K₂}
    (h : letI := spectralNorm.normedField ℚ_[p] K₁
      letI := spectralNorm.normedField ℚ_[p] K₂
      ‖x‖ * ‖y‖ ≤ (p : ℝ) ^ (-(tensorLogDiffOrder p K₁ P₁ + tensorLogDiffOrder p K₂ P₂ +
        (Proposition1_2.a p (P₁.ramificationIdx ℤ_[p]) +
          Proposition1_2.a p (P₂.ramificationIdx ℤ_[p]))))) :
    tensorLogShift p K₁ K₂ x y ⊆
      (fun w => TensorProduct.tmul ℚ_[p] u₁ u₂ * w) '' padicPacketIntegers p K₁ K₂ := by
  let _ := spectralNorm.normedField ℚ_[p] K₁
  let _ := spectralNorm.normedField ℚ_[p] K₂
  let _ := isDedekindDomain_ringOfIntegers_padic p K₂
  let _ := isTorsionFree_ringOfIntegers_padic p K₂
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  obtain ⟨d, hd0, hd⟩ := padicBridge_exists_norm_eq_rpow p K₂ P₂
    (-((differentExponent ℤ_[p] (integralClosure ℤ_[p] K₂) P₂ : ℕ) : ℤ))
  have hd' : ‖d‖ = (p : ℝ) ^ (-tensorLogDiffOrder p K₂ P₂) := by
    rw [hd]
    congr 1
    unfold tensorLogDiffOrder differentOrder
    push_cast
    ring
  have hd1 := tensorLogDiffOrder_nonneg p K₁ P₁
  have hu₁0 : u₁ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu₁
    exact (Real.rpow_pos_of_pos hp0 _).ne' hu₁.symm
  have hu₂0 : u₂ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu₂
    exact (Real.rpow_pos_of_pos hp0 _).ne' hu₂.symm
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨TensorProduct.tmul ℚ_[p] (1 : K₁) d *
      (TensorProduct.tmul ℚ_[p] (x / u₁) (y / (u₂ * d)) * z),
    tensorDiff_order_mul_mem_packetIntegers p K₁ K₂ P₂ hd'
      (tensorLog_mul_mem p K₁ K₂ (tensorLog_tmul_mem_normalization p K₁ K₂ ?_) hz), ?_⟩
  · show ‖x / u₁‖ * ‖y / (u₂ * d)‖ ≤ 1
    have hpos : 0 < ‖u₁‖ * ‖u₂ * d‖ :=
      mul_pos (norm_pos_iff.2 hu₁0) (norm_pos_iff.2 (mul_ne_zero hu₂0 hd0))
    rw [norm_div, norm_div, div_mul_div_comm, div_le_one hpos, norm_mul, hu₁, hu₂, hd',
      ← mul_assoc, ← Real.rpow_add hp0, ← Real.rpow_add hp0]
    refine h.trans (Real.rpow_le_rpow_of_exponent_le hp1 ?_)
    linarith
  · show TensorProduct.tmul ℚ_[p] u₁ u₂ * (TensorProduct.tmul ℚ_[p] (1 : K₁) d *
        (TensorProduct.tmul ℚ_[p] (x / u₁) (y / (u₂ * d)) * z)) = TensorProduct.tmul ℚ_[p] x y * z
    rw [← mul_assoc, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_div_cancel₀ _ hu₁0,
      mul_div_cancel₀ _ (mul_ne_zero hu₂0 hd0)]

/-- **`⊗_i p ^ (a_i) · R_i ⊆ R_I`**, the parenthetical inclusion of the first display of page 11:
`(u₁ ⊗ u₂) · R_I ⊆ R_I` for `ord(u_i) = a_i > 0`. -/
theorem tensorLog_mul_integers_subset_integers {u₁ : K₁} {u₂ : K₂}
    (hu₁ : letI := spectralNorm.normedField ℚ_[p] K₁
      ‖u₁‖ = (p : ℝ) ^ (-Proposition1_2.a p (P₁.ramificationIdx ℤ_[p])))
    (hu₂ : letI := spectralNorm.normedField ℚ_[p] K₂
      ‖u₂‖ = (p : ℝ) ^ (-Proposition1_2.a p (P₂.ramificationIdx ℤ_[p]))) :
    (fun w => TensorProduct.tmul ℚ_[p] u₁ u₂ * w) '' padicPacketIntegers p K₁ K₂ ⊆
      padicPacketIntegers p K₁ K₂ := by
  let _ := spectralNorm.normedField ℚ_[p] K₁
  let _ := spectralNorm.normedField ℚ_[p] K₂
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
  have hle : ∀ e : ℕ, 1 ≤ e → (p : ℝ) ^ (-Proposition1_2.a p e) ≤ 1 := by
    intro e he
    have ha := Proposition1_2.a_gt hp.out.two_le he
    have : 0 < 1 / ((p : ℝ) - 1) := by
      apply div_pos one_pos
      linarith
    exact Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
  have h₁ : ‖u₁‖ ≤ 1 := hu₁ ▸ hle _ (tensorLog_one_le_ramificationIdx p K₁ P₁)
  have h₂ : ‖u₂‖ ≤ 1 := hu₂ ▸ hle _ (tensorLog_one_le_ramificationIdx p K₂ P₂)
  rintro _ ⟨w, hw, rfl⟩
  unfold padicPacketIntegers at hw ⊢
  rw [SetLike.mem_coe] at hw ⊢
  induction hw using AddSubmonoid.closure_induction with
  | mem w hw =>
    obtain ⟨x, y, hx, hy, rfl⟩ := hw
    have hx' := (padicBridge_mem_integralClosure_iff p K₁ x).1
      ((tensorDiff_padicVolIntegral_iff p K₁ x).1 hx)
    have hy' := (padicBridge_mem_integralClosure_iff p K₂ y).1
      ((tensorDiff_padicVolIntegral_iff p K₂ y).1 hy)
    refine AddSubmonoid.subset_closure ⟨u₁ * x, u₂ * y,
      tensorLog_integral_of_norm_le_one p K₁ ?_, tensorLog_integral_of_norm_le_one p K₂ ?_,
      Algebra.TensorProduct.tmul_mul_tmul _ _ _ _⟩
    · show ‖u₁ * x‖ ≤ 1
      rw [norm_mul]
      nlinarith [norm_nonneg u₁, norm_nonneg x]
    · show ‖u₂ * y‖ ≤ 1
      rw [norm_mul]
      nlinarith [norm_nonneg u₂, norm_nonneg y]
  | zero =>
    beta_reduce
    rw [mul_zero]
    exact zero_mem _
  | add a b _ _ ha hb =>
    beta_reduce at ha hb ⊢
    rw [mul_add]
    exact add_mem ha hb

/-- **`p ^ (𝔡_I + a_I) · (R_I)^∼ ⊆ log_p(R_I^×)`** (page 11, from the first display and
Proposition 1.2 (i)): every `(x ⊗ y) · (R_I)^∼` with `‖x‖ ‖y‖ ≤ p ^ (−(𝔡_I + a_I))` lies in
`log_p(R_I^×)`. -/
theorem tensorLog_shift_subset_lattice {x : K₁} {y : K₂}
    (h : letI := spectralNorm.normedField ℚ_[p] K₁
      letI := spectralNorm.normedField ℚ_[p] K₂
      ‖x‖ * ‖y‖ ≤ (p : ℝ) ^ (-(tensorLogDiffOrder p K₁ P₁ + tensorLogDiffOrder p K₂ P₂ +
        (Proposition1_2.a p (P₁.ramificationIdx ℤ_[p]) +
          Proposition1_2.a p (P₂.ramificationIdx ℤ_[p]))))) :
    tensorLogShift p K₁ K₂ x y ⊆ tensorLogLattice p K₁ K₂ := by
  obtain ⟨⟨u₁, hu₁⟩, -, -⟩ := padicBridge_extLogUnit_image_fractionalIdeal p K₁ P₁
  obtain ⟨⟨u₂, hu₂⟩, -, -⟩ := padicBridge_extLogUnit_image_fractionalIdeal p K₂ P₂
  exact (tensorLog_shift_subset_integers p K₁ K₂ P₁ P₂ hu₁ hu₂ h).trans
    (tensorLog_mul_integers_subset_lattice p K₁ K₂ P₁ P₂ hu₁ hu₂)

/-- **IUT IV Proposition 1.2 (ii) for two factors** (page 10, proof on page 11). Let `φ` be a
`ℚ_p`-linear automorphism of `K₁ ⊗[ℚ_p] K₂` (the `ℚ_p`-span of `log_p(R_I^×)`,
`tensorLog_span_lattice`) that maps `log_p(R_I^×)` onto itself. For every real `λ`, every
`t₁ ⊗ t₂` with `‖t₁‖ ‖t₂‖ = p ^ (−λ)` (for `λ ∈ (1 / e_i) ℤ` this is `p ^ λ` taken in either
factor) and every `z_i` with `ord(z_i) = −b_i`:
`φ(p ^ λ · (R_I)^∼) ⊆ p ^ ⌊λ − 𝔡_I − a_I⌋ · log_p(R_I^×) ⊆ p ^ ⌊λ − 𝔡_I − a_I⌋ ·
(p ^ (−b_I) · (R_I)^∼)`. -/
theorem tensorLog_prop1_2_ii
    (φ : TensorProduct ℚ_[p] K₁ K₂ ≃ₗ[ℚ_[p]] TensorProduct ℚ_[p] K₁ K₂)
    (hφ : φ '' tensorLogLattice p K₁ K₂ = tensorLogLattice p K₁ K₂) (lam : ℝ)
    {t₁ : K₁} {t₂ : K₂}
    (ht : letI := spectralNorm.normedField ℚ_[p] K₁
      letI := spectralNorm.normedField ℚ_[p] K₂
      ‖t₁‖ * ‖t₂‖ = (p : ℝ) ^ (-lam))
    {z₁ : K₁} {z₂ : K₂}
    (hz₁ : letI := spectralNorm.normedField ℚ_[p] K₁
      ‖z₁‖ = (p : ℝ) ^ (Proposition1_2.b p (P₁.ramificationIdx ℤ_[p])))
    (hz₂ : letI := spectralNorm.normedField ℚ_[p] K₂
      ‖z₂‖ = (p : ℝ) ^ (Proposition1_2.b p (P₂.ramificationIdx ℤ_[p]))) :
    φ '' tensorLogShift p K₁ K₂ t₁ t₂ ⊆
        ((p : ℚ_[p]) ^ ⌊lam - (tensorLogDiffOrder p K₁ P₁ + tensorLogDiffOrder p K₂ P₂) -
          (Proposition1_2.a p (P₁.ramificationIdx ℤ_[p]) +
            Proposition1_2.a p (P₂.ramificationIdx ℤ_[p]))⌋) • tensorLogLattice p K₁ K₂ ∧
      ((p : ℚ_[p]) ^ ⌊lam - (tensorLogDiffOrder p K₁ P₁ + tensorLogDiffOrder p K₂ P₂) -
          (Proposition1_2.a p (P₁.ramificationIdx ℤ_[p]) +
            Proposition1_2.a p (P₂.ramificationIdx ℤ_[p]))⌋) • tensorLogLattice p K₁ K₂ ⊆
        ((p : ℚ_[p]) ^ ⌊lam - (tensorLogDiffOrder p K₁ P₁ + tensorLogDiffOrder p K₂ P₂) -
          (Proposition1_2.a p (P₁.ramificationIdx ℤ_[p]) +
            Proposition1_2.a p (P₂.ramificationIdx ℤ_[p]))⌋) • tensorLogShift p K₁ K₂ z₁ z₂ := by
  let _ := spectralNorm.normedField ℚ_[p] K₁
  let _ := spectralNorm.normedField ℚ_[p] K₂
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hpq : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set k := ⌊lam - (tensorLogDiffOrder p K₁ P₁ + tensorLogDiffOrder p K₂ P₂) -
    (Proposition1_2.a p (P₁.ramificationIdx ℤ_[p]) +
      Proposition1_2.a p (P₂.ramificationIdx ℤ_[p]))⌋ with hk
  have hkle := Int.floor_le (lam - (tensorLogDiffOrder p K₁ P₁ + tensorLogDiffOrder p K₂ P₂) -
    (Proposition1_2.a p (P₁.ramificationIdx ℤ_[p]) +
      Proposition1_2.a p (P₂.ramificationIdx ℤ_[p])))
  rw [← hk] at hkle
  have hS : tensorLogShift p K₁ K₂ (((p : ℚ_[p]) ^ (-k)) • t₁) t₂ ⊆ tensorLogLattice p K₁ K₂ := by
    refine tensorLog_shift_subset_lattice p K₁ K₂ P₁ P₂ ?_
    show ‖((p : ℚ_[p]) ^ (-k)) • t₁‖ * ‖t₂‖ ≤ _
    rw [tensorLog_norm_p_zpow_smul, mul_assoc, ht, ← Real.rpow_add hp0]
    apply Real.rpow_le_rpow_of_exponent_le hp1
    push_cast
    linarith
  have heq : tensorLogShift p K₁ K₂ t₁ t₂ =
      ((p : ℚ_[p]) ^ k) • tensorLogShift p K₁ K₂ (((p : ℚ_[p]) ^ (-k)) • t₁) t₂ := by
    rw [tensorLogShift_smul, smul_smul, ← zpow_add₀ hpq, add_neg_cancel, zpow_zero, one_smul]
  refine ⟨?_, Set.smul_set_mono (tensorLog_lattice_subset_shift p K₁ K₂ P₁ P₂ hz₁ hz₂)⟩
  rw [heq, padicVol_image_smul p φ]
  have h := Set.smul_set_mono (a := (p : ℚ_[p]) ^ k) (Set.image_mono (f := φ) hS)
  rwa [hφ] at h

/-- **IUT IV Proposition 1.2 (ii), "in particular"** (page 10), `λ = 0`:
`φ((R_I)^∼) ⊆ p ^ (−⌈𝔡_I + a_I⌉) · log_p(R_I^×) ⊆ p ^ (−⌈𝔡_I + a_I⌉) · (p ^ (−b_I) · (R_I)^∼)`. -/
theorem tensorLog_prop1_2_ii_zero
    (φ : TensorProduct ℚ_[p] K₁ K₂ ≃ₗ[ℚ_[p]] TensorProduct ℚ_[p] K₁ K₂)
    (hφ : φ '' tensorLogLattice p K₁ K₂ = tensorLogLattice p K₁ K₂)
    {z₁ : K₁} {z₂ : K₂}
    (hz₁ : letI := spectralNorm.normedField ℚ_[p] K₁
      ‖z₁‖ = (p : ℝ) ^ (Proposition1_2.b p (P₁.ramificationIdx ℤ_[p])))
    (hz₂ : letI := spectralNorm.normedField ℚ_[p] K₂
      ‖z₂‖ = (p : ℝ) ^ (Proposition1_2.b p (P₂.ramificationIdx ℤ_[p]))) :
    φ '' padicPacketNormalization p K₁ K₂ ⊆
        ((p : ℚ_[p]) ^ (-⌈tensorLogDiffOrder p K₁ P₁ + tensorLogDiffOrder p K₂ P₂ +
          (Proposition1_2.a p (P₁.ramificationIdx ℤ_[p]) +
            Proposition1_2.a p (P₂.ramificationIdx ℤ_[p]))⌉)) • tensorLogLattice p K₁ K₂ ∧
      ((p : ℚ_[p]) ^ (-⌈tensorLogDiffOrder p K₁ P₁ + tensorLogDiffOrder p K₂ P₂ +
          (Proposition1_2.a p (P₁.ramificationIdx ℤ_[p]) +
            Proposition1_2.a p (P₂.ramificationIdx ℤ_[p]))⌉)) • tensorLogLattice p K₁ K₂ ⊆
        ((p : ℚ_[p]) ^ (-⌈tensorLogDiffOrder p K₁ P₁ + tensorLogDiffOrder p K₂ P₂ +
          (Proposition1_2.a p (P₁.ramificationIdx ℤ_[p]) +
            Proposition1_2.a p (P₂.ramificationIdx ℤ_[p]))⌉)) • tensorLogShift p K₁ K₂ z₁ z₂ := by
  let _ := spectralNorm.normedField ℚ_[p] K₁
  let _ := spectralNorm.normedField ℚ_[p] K₂
  have h := tensorLog_prop1_2_ii p K₁ K₂ P₁ P₂ φ hφ 0 (t₁ := 1) (t₂ := 1)
    (by rw [norm_one, norm_one, neg_zero, Real.rpow_zero, mul_one]) hz₁ hz₂
  rwa [tensorLogShift_one, zero_sub, ← neg_add', Int.floor_neg] at h

/-- **IUT IV Proposition 1.2 (iii) for two factors** (page 11): if `p > 2` and `e_i ≤ p − 2` for
`i = 1, 2`, then `φ(p ^ λ · (R_I)^∼) ⊆ p ^ (λ − 𝔡_I − 1) · (R_I)^∼` for every `λ`, `t₁ ⊗ t₂` with
`‖t₁‖ ‖t₂‖ = p ^ (−λ)`, and every representative `w₁ ⊗ w₂` of `p ^ (λ − 𝔡_I − 1)`. -/
theorem tensorLog_prop1_2_iii (hp2 : 2 < p) (he₁ : P₁.ramificationIdx ℤ_[p] ≤ p - 2)
    (he₂ : P₂.ramificationIdx ℤ_[p] ≤ p - 2)
    (φ : TensorProduct ℚ_[p] K₁ K₂ ≃ₗ[ℚ_[p]] TensorProduct ℚ_[p] K₁ K₂)
    (hφ : φ '' tensorLogLattice p K₁ K₂ = tensorLogLattice p K₁ K₂) (lam : ℝ)
    {t₁ : K₁} {t₂ : K₂}
    (ht : letI := spectralNorm.normedField ℚ_[p] K₁
      letI := spectralNorm.normedField ℚ_[p] K₂
      ‖t₁‖ * ‖t₂‖ = (p : ℝ) ^ (-lam))
    {w₁ : K₁} {w₂ : K₂}
    (hw : letI := spectralNorm.normedField ℚ_[p] K₁
      letI := spectralNorm.normedField ℚ_[p] K₂
      ‖w₁‖ * ‖w₂‖ = (p : ℝ) ^
        (-(lam - (tensorLogDiffOrder p K₁ P₁ + tensorLogDiffOrder p K₂ P₂) - 1))) :
    φ '' tensorLogShift p K₁ K₂ t₁ t₂ ⊆ tensorLogShift p K₁ K₂ w₁ w₂ := by
  let _ := spectralNorm.normedField ℚ_[p] K₁
  let _ := spectralNorm.normedField ℚ_[p] K₂
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  obtain ⟨-, ⟨z₁, hz₁⟩, -⟩ := padicBridge_extLogUnit_image_fractionalIdeal p K₁ P₁
  obtain ⟨-, ⟨z₂, hz₂⟩, -⟩ := padicBridge_extLogUnit_image_fractionalIdeal p K₂ P₂
  have hii := tensorLog_prop1_2_ii p K₁ K₂ P₁ P₂ φ hφ lam ht hz₁ hz₂
  have h := hii.1.trans hii.2
  rw [tensorLogShift_smul] at h
  have hwpos : 0 < ‖w₁‖ * ‖w₂‖ := hw ▸ Real.rpow_pos_of_pos hp0 _
  have hw₁ : w₁ ≠ 0 := by
    intro h0
    rw [h0, norm_zero, zero_mul] at hwpos
    exact lt_irrefl _ hwpos
  have hw₂ : w₂ ≠ 0 := by
    intro h0
    rw [h0, norm_zero, mul_zero] at hwpos
    exact lt_irrefl _ hwpos
  refine h.trans (tensorLogShift_subset p K₁ K₂ hw₁ hw₂ ?_)
  show ‖_ • z₁‖ * ‖z₂‖ ≤ ‖w₁‖ * ‖w₂‖
  rw [tensorLog_norm_p_zpow_smul, mul_assoc, hz₁, hz₂, hw, ← Real.rpow_add hp0,
    ← Real.rpow_add hp0]
  apply Real.rpow_le_rpow_of_exponent_le hp1
  have hab₁ := Proposition1_2.a_b_of_le hp2 (tensorLog_one_le_ramificationIdx p K₁ P₁) he₁
  have hab₂ := Proposition1_2.a_b_of_le hp2 (tensorLog_one_le_ramificationIdx p K₂ P₂) he₂
  have hf := Proposition1_2.iii_floor (lam - (tensorLogDiffOrder p K₁ P₁ +
      tensorLogDiffOrder p K₂ P₂))
    (Proposition1_2.a p (P₁.ramificationIdx ℤ_[p]) + Proposition1_2.a p (P₂.ramificationIdx ℤ_[p]))
    (Proposition1_2.b p (P₁.ramificationIdx ℤ_[p]) + Proposition1_2.b p (P₂.ramificationIdx ℤ_[p]))
    (by linarith [hab₁.1, hab₁.2, hab₂.1, hab₂.2])
  linarith

/-- **IUT IV Proposition 1.2 (iii), "in particular"** (page 11): under the same hypotheses,
`φ((R_I)^∼) ⊆ p ^ (−𝔡_I − 1) · (R_I)^∼`. -/
theorem tensorLog_prop1_2_iii_zero (hp2 : 2 < p) (he₁ : P₁.ramificationIdx ℤ_[p] ≤ p - 2)
    (he₂ : P₂.ramificationIdx ℤ_[p] ≤ p - 2)
    (φ : TensorProduct ℚ_[p] K₁ K₂ ≃ₗ[ℚ_[p]] TensorProduct ℚ_[p] K₁ K₂)
    (hφ : φ '' tensorLogLattice p K₁ K₂ = tensorLogLattice p K₁ K₂)
    {w₁ : K₁} {w₂ : K₂}
    (hw : letI := spectralNorm.normedField ℚ_[p] K₁
      letI := spectralNorm.normedField ℚ_[p] K₂
      ‖w₁‖ * ‖w₂‖ = (p : ℝ) ^ (tensorLogDiffOrder p K₁ P₁ + tensorLogDiffOrder p K₂ P₂ + 1)) :
    φ '' padicPacketNormalization p K₁ K₂ ⊆ tensorLogShift p K₁ K₂ w₁ w₂ := by
  let _ := spectralNorm.normedField ℚ_[p] K₁
  let _ := spectralNorm.normedField ℚ_[p] K₂
  rw [← tensorLogShift_one]
  refine tensorLog_prop1_2_iii p K₁ K₂ P₁ P₂ hp2 he₁ he₂ φ hφ 0
    (by rw [norm_one, norm_one, neg_zero, Real.rpow_zero, mul_one]) ?_
  rw [hw]
  congr 1
  ring

/-- **IUT IV Proposition 1.2 (iv) for two factors** (page 11): if `p > 2` and `e_1 = e_2 = 1`,
then `φ((R_I)^∼) ⊆ (R_I)^∼`. Here `𝔡_i = 0` (Proposition 1.3 (i), equality case,
`differentOrder_eq_of_not_dvd_ramificationIdx_padic`) and `a_i = 1 = −b_i`. -/
theorem tensorLog_prop1_2_iv (hp2 : 2 < p) (he₁ : P₁.ramificationIdx ℤ_[p] = 1)
    (he₂ : P₂.ramificationIdx ℤ_[p] = 1)
    (φ : TensorProduct ℚ_[p] K₁ K₂ ≃ₗ[ℚ_[p]] TensorProduct ℚ_[p] K₁ K₂)
    (hφ : φ '' tensorLogLattice p K₁ K₂ = tensorLogLattice p K₁ K₂) :
    φ '' padicPacketNormalization p K₁ K₂ ⊆ padicPacketNormalization p K₁ K₂ := by
  let _ := spectralNorm.normedField ℚ_[p] K₁
  let _ := spectralNorm.normedField ℚ_[p] K₂
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hnd : ¬ p ∣ 1 := fun h => (Nat.le_of_dvd one_pos h).not_gt hp.out.one_lt
  have hD₁ : tensorLogDiffOrder p K₁ P₁ = 0 := by
    have h := differentOrder_eq_of_not_dvd_ramificationIdx_padic p K₁ P₁ (by rw [he₁]; exact hnd)
    unfold tensorLogDiffOrder
    rw [h, he₁]
    norm_num
  have hD₂ : tensorLogDiffOrder p K₂ P₂ = 0 := by
    have h := differentOrder_eq_of_not_dvd_ramificationIdx_padic p K₂ P₂ (by rw [he₂]; exact hnd)
    unfold tensorLogDiffOrder
    rw [h, he₂]
    norm_num
  obtain ⟨-, ⟨z₁, hz₁⟩, -⟩ := padicBridge_extLogUnit_image_fractionalIdeal p K₁ P₁
  obtain ⟨-, ⟨z₂, hz₂⟩, -⟩ := padicBridge_extLogUnit_image_fractionalIdeal p K₂ P₂
  have hii := tensorLog_prop1_2_ii_zero p K₁ K₂ P₁ P₂ φ hφ hz₁ hz₂
  have h := hii.1.trans hii.2
  rw [tensorLogShift_smul] at h
  refine h.trans ((tensorLogShift_subset p K₁ K₂ one_ne_zero one_ne_zero ?_).trans
    (tensorLogShift_one p K₁ K₂).subset)
  have hab := Proposition1_2.a_b_of_e_one hp2
  show ‖_ • z₁‖ * ‖z₂‖ ≤ ‖(1 : K₁)‖ * ‖(1 : K₂)‖
  rw [tensorLog_norm_p_zpow_smul, mul_assoc, hz₁, hz₂, ← Real.rpow_add hp0,
    ← Real.rpow_add hp0, norm_one, norm_one, mul_one, hD₁, hD₂, he₁, he₂, hab.1, hab.2]
  have hc : ⌈(0 : ℝ) + 0 + (1 + 1)⌉ = 2 := by norm_num
  rw [hc]
  norm_num

end Lattice

/-! ## Log-volumes: Proposition 1.4 (iii) and (iv) -/

section Volume

variable (p : ℕ) [hp : Fact p.Prime] (K₁ K₂ : Type*) [Field K₁] [Field K₂] [Algebra ℚ_[p] K₁]
  [Algebra ℚ_[p] K₂] [FiniteDimensional ℚ_[p] K₁] [FiniteDimensional ℚ_[p] K₂]

/-- `K₁ ⊗[ℚ_p] K₂ ≠ 0`. -/
theorem tensorLog_finrank_pos : 0 < Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂) := by
  rw [Module.finrank_tensorProduct]
  exact Nat.mul_pos Module.finrank_pos Module.finrank_pos

variable [Algebra ℤ_[p] K₁] [Algebra ℤ_[p] K₂] [IsScalarTower ℤ_[p] ℚ_[p] K₁]
  [IsScalarTower ℤ_[p] ℚ_[p] K₂]

/-- **`log_p(R_I^×) ⊗ ℚ_p = K₁ ⊗ K₂`**: the `ℚ_p`-span of `log_p(R_I^×)` is the whole tensor
product, so the automorphisms `φ` of Proposition 1.2 are `ℚ_p`-linear automorphisms of
`K₁ ⊗[ℚ_p] K₂`. -/
theorem tensorLog_span_lattice (P₁ : Ideal (integralClosure ℤ_[p] K₁)) [P₁.IsPrime]
    [P₁.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (P₂ : Ideal (integralClosure ℤ_[p] K₂)) [P₂.IsPrime]
    [P₂.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    Submodule.span ℚ_[p] (tensorLogLattice p K₁ K₂) = ⊤ := by
  let _ := spectralNorm.normedField ℚ_[p] K₁
  let _ := spectralNorm.normedField ℚ_[p] K₂
  have := volBridge_tensor_formallyUnramified p K₁ K₂
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hpq : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  obtain ⟨M, hM⟩ := exists_nat_ge (tensorLogDiffOrder p K₁ P₁ + tensorLogDiffOrder p K₂ P₂ +
    (Proposition1_2.a p (P₁.ramificationIdx ℤ_[p]) +
      Proposition1_2.a p (P₂.ramificationIdx ℤ_[p])))
  have hsub : ((p : ℚ_[p]) ^ (M : ℤ)) • padicPacketNormalization p K₁ K₂ ⊆
      tensorLogLattice p K₁ K₂ := by
    rw [← tensorLogShift_one, tensorLogShift_smul]
    refine tensorLog_shift_subset_lattice p K₁ K₂ P₁ P₂ ?_
    show ‖((p : ℚ_[p]) ^ (M : ℤ)) • (1 : K₁)‖ * ‖(1 : K₂)‖ ≤ _
    rw [tensorLog_norm_p_zpow_smul, norm_one, norm_one, mul_one, mul_one]
    apply Real.rpow_le_rpow_of_exponent_le hp1
    push_cast
    linarith
  have hspan := (packet_normalization_lattice p (TensorProduct ℚ_[p] K₁ K₂)).2.2
  rw [eq_top_iff, ← hspan, Submodule.span_le]
  intro n hn
  have hmem : ((p : ℚ_[p]) ^ (M : ℤ)) • n ∈ tensorLogLattice p K₁ K₂ :=
    hsub (Set.smul_mem_smul_set hn)
  have hn' : n = ((p : ℚ_[p]) ^ (M : ℤ))⁻¹ • (((p : ℚ_[p]) ^ (M : ℤ)) • n) := by
    rw [smul_smul, inv_mul_cancel₀ (zpow_ne_zero _ hpq), one_smul]
  rw [SetLike.mem_coe, hn']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

variable [MeasurableSpace (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) → ℚ_[p])]
  [BorelSpace (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) → ℚ_[p])]
  (μ : Measure (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) → ℚ_[p]))
  [μ.IsAddHaarMeasure]

omit [Algebra ℤ_[p] K₁] [Algebra ℤ_[p] K₂] [IsScalarTower ℤ_[p] ℚ_[p] K₁]
  [IsScalarTower ℤ_[p] ℚ_[p] K₂] in
/-- **Proposition 1.4 (i) for two factors** on the tensor product over `ℚ_p`: `(R_I)^∼` has
positive finite Haar measure in coordinates, `μ^log((R_I)^∼) = 0` and
`μ^log(p ^ n · (R_I)^∼) = −n log p`. -/
theorem tensorLog_normalization_measure :
    μ ((Module.finBasis ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).equivFun ''
        padicPacketNormalization p K₁ K₂) ≠ 0 ∧
      μ ((Module.finBasis ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).equivFun ''
        padicPacketNormalization p K₁ K₂) ≠ ⊤ ∧
      padicPacketMuLog p (TensorProduct ℚ_[p] K₁ K₂) μ (padicPacketNormalization p K₁ K₂)
        (padicPacketNormalization p K₁ K₂) = 0 ∧
      ∀ n : ℤ, padicPacketMuLog p (TensorProduct ℚ_[p] K₁ K₂) μ
        (padicPacketNormalization p K₁ K₂)
        (((p : ℚ_[p]) ^ n) • padicPacketNormalization p K₁ K₂) = -(n * Real.log p) := by
  have := volBridge_tensor_formallyUnramified p K₁ K₂
  have : Nontrivial (TensorProduct ℚ_[p] K₁ K₂) :=
    Module.nontrivial_of_finrank_pos (R := ℚ_[p]) (tensorLog_finrank_pos p K₁ K₂)
  exact packet_muLog_normalization p (TensorProduct ℚ_[p] K₁ K₂) μ

omit [Algebra ℤ_[p] K₁] [Algebra ℤ_[p] K₂] [IsScalarTower ℤ_[p] ℚ_[p] K₁]
  [IsScalarTower ℤ_[p] ℚ_[p] K₂] in
/-- Scaling by `p ^ n` keeps the measure positive and finite. -/
theorem tensorLog_measure_zpow_smul {S : Set (TensorProduct ℚ_[p] K₁ K₂)}
    (h0 : μ ((Module.finBasis ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).equivFun '' S) ≠ 0)
    (h1 : μ ((Module.finBasis ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).equivFun '' S) ≠ ⊤) (n : ℤ) :
    μ ((Module.finBasis ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).equivFun ''
        (((p : ℚ_[p]) ^ n) • S)) ≠ 0 ∧
      μ ((Module.finBasis ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).equivFun ''
        (((p : ℚ_[p]) ^ n) • S)) ≠ ⊤ := by
  have hpq : (p : ℚ_[p]) ^ n ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  rw [padicVol_image_smul p, padicVol_measure_smul p μ hpq]
  refine ⟨mul_ne_zero ?_ h0, ENNReal.mul_ne_top ENNReal.coe_ne_top h1⟩
  exact ENNReal.coe_ne_zero.2 (pow_ne_zero _ (nnNorm_ne_zero_iff.2 hpq))

/-- **Sets between two shifts have positive finite measure**: if `(x ⊗ y) · (R_I)^∼ ⊆ S ⊆
(x' ⊗ y') · (R_I)^∼` with `x`, `y`, `x'`, `y'` nonzero. -/
theorem tensorLog_measure_of_subset {x x' : K₁} {y y' : K₂} (hx : x ≠ 0) (hy : y ≠ 0)
    (hx' : x' ≠ 0) (hy' : y' ≠ 0) {S : Set (TensorProduct ℚ_[p] K₁ K₂)}
    (hlo : tensorLogShift p K₁ K₂ x y ⊆ S) (hhi : S ⊆ tensorLogShift p K₁ K₂ x' y') :
    μ ((Module.finBasis ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).equivFun '' S) ≠ 0 ∧
      μ ((Module.finBasis ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).equivFun '' S) ≠ ⊤ := by
  let _ := spectralNorm.normedField ℚ_[p] K₁
  let _ := spectralNorm.normedField ℚ_[p] K₂
  have hN := tensorLog_normalization_measure p K₁ K₂ μ
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpq : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hr : 0 < ‖x‖ * ‖y‖ := mul_pos (norm_pos_iff.2 hx) (norm_pos_iff.2 hy)
  have hr' : 0 < ‖x'‖ * ‖y'‖ := mul_pos (norm_pos_iff.2 hx') (norm_pos_iff.2 hy')
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (max (‖x‖ * ‖y‖)⁻¹ (‖x'‖ * ‖y'‖)) hp1
  have hpn : (0 : ℝ) < (p : ℝ) ^ n := by positivity
  have hnorm : ∀ m : ℤ, ‖((p : ℚ_[p]) ^ m) • (1 : K₁)‖ * ‖(1 : K₂)‖ = (p : ℝ) ^ (-m) := by
    intro m
    rw [tensorLog_norm_p_zpow_smul, norm_one, norm_one, mul_one, mul_one, ← Real.rpow_intCast]
    push_cast
    rfl
  have hset : ∀ m : ℤ, tensorLogShift p K₁ K₂ (((p : ℚ_[p]) ^ m) • (1 : K₁)) 1 =
      ((p : ℚ_[p]) ^ m) • padicPacketNormalization p K₁ K₂ := by
    intro m
    rw [← tensorLogShift_smul, tensorLogShift_one]
  have hlo' : tensorLogShift p K₁ K₂ (((p : ℚ_[p]) ^ (n : ℤ)) • (1 : K₁)) 1 ⊆ S := by
    refine (tensorLogShift_subset p K₁ K₂ hx hy ?_).trans hlo
    show ‖((p : ℚ_[p]) ^ (n : ℤ)) • (1 : K₁)‖ * ‖(1 : K₂)‖ ≤ ‖x‖ * ‖y‖
    rw [hnorm, zpow_neg, zpow_natCast, inv_le_comm₀ hpn hr]
    exact (le_max_left _ _).trans hn.le
  have hhi' : S ⊆ tensorLogShift p K₁ K₂ (((p : ℚ_[p]) ^ (-(n : ℤ))) • (1 : K₁)) 1 := by
    refine hhi.trans (tensorLogShift_subset p K₁ K₂
      (smul_ne_zero (zpow_ne_zero _ hpq) one_ne_zero) one_ne_zero ?_)
    show ‖x'‖ * ‖y'‖ ≤ ‖((p : ℚ_[p]) ^ (-(n : ℤ))) • (1 : K₁)‖ * ‖(1 : K₂)‖
    rw [hnorm, neg_neg, zpow_natCast]
    exact (le_max_right _ _).trans hn.le
  rw [hset] at hlo' hhi'
  have h₁ := tensorLog_measure_zpow_smul p K₁ K₂ μ hN.1 hN.2.1 n
  have h₂ := tensorLog_measure_zpow_smul p K₁ K₂ μ hN.1 hN.2.1 (-(n : ℤ))
  exact ⟨fun h => h₁.1 (measure_mono_null (Set.image_mono hlo') h),
    ne_top_of_le_ne_top h₂.2 (measure_mono (Set.image_mono hhi'))⟩

omit [Algebra ℤ_[p] K₁] [Algebra ℤ_[p] K₂] [IsScalarTower ℤ_[p] ℚ_[p] K₁]
  [IsScalarTower ℤ_[p] ℚ_[p] K₂] in
/-- **Multiplication by a unit preserves `μ^log`**: for `t` with inverse `s`,
`μ^log(t Λ, t A) = μ^log(Λ, A)` (the packet log-volume does not depend on the linear
coordinates). -/
theorem tensorLog_muLog_mul_image {t s : TensorProduct ℚ_[p] K₁ K₂} (hst : s * t = 1)
    (hts : t * s = 1) (Λ A : Set (TensorProduct ℚ_[p] K₁ K₂)) :
    padicPacketMuLog p (TensorProduct ℚ_[p] K₁ K₂) μ ((fun z => t * z) '' Λ)
        ((fun z => t * z) '' A) =
      padicPacketMuLog p (TensorProduct ℚ_[p] K₁ K₂) μ Λ A := by
  let T : TensorProduct ℚ_[p] K₁ K₂ ≃ₗ[ℚ_[p]] TensorProduct ℚ_[p] K₁ K₂ :=
    { toFun := fun z => t * z
      invFun := fun z => s * z
      map_add' := fun a b => mul_add t a b
      map_smul' := fun c z => mul_smul_comm c t z
      left_inv := fun z => by
        show s * (t * z) = z
        rw [← mul_assoc, hst, one_mul]
      right_inv := fun z => by
        show t * (s * z) = z
        rw [← mul_assoc, hts, one_mul] }
  rw [← padicPacketMuLog_coord_indep p μ (T.trans (Module.finBasis ℚ_[p] _).equivFun) Λ A]
  unfold padicPacketMuLog
  rw [Set.image_image, Set.image_image]
  rfl

omit [Algebra ℤ_[p] K₁] [Algebra ℤ_[p] K₂] [IsScalarTower ℤ_[p] ℚ_[p] K₁]
  [IsScalarTower ℤ_[p] ℚ_[p] K₂] [BorelSpace (Fin (Module.finrank ℚ_[p]
    (TensorProduct ℚ_[p] K₁ K₂)) → ℚ_[p])] [μ.IsAddHaarMeasure] in
/-- **The cocycle relation** `μ^log(Λ, A) = μ^log(Λ, B) + μ^log(B, A)` for sets of positive
finite measure. -/
theorem tensorLog_muLog_cocycle {Λ B A : Set (TensorProduct ℚ_[p] K₁ K₂)}
    (hΛ0 : μ ((Module.finBasis ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).equivFun '' Λ) ≠ 0)
    (hΛ : μ ((Module.finBasis ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).equivFun '' Λ) ≠ ⊤)
    (hB0 : μ ((Module.finBasis ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).equivFun '' B) ≠ 0)
    (hB : μ ((Module.finBasis ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).equivFun '' B) ≠ ⊤)
    (hA0 : μ ((Module.finBasis ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).equivFun '' A) ≠ 0)
    (hA : μ ((Module.finBasis ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).equivFun '' A) ≠ ⊤) :
    padicPacketMuLog p (TensorProduct ℚ_[p] K₁ K₂) μ Λ A =
      padicPacketMuLog p (TensorProduct ℚ_[p] K₁ K₂) μ Λ B +
        padicPacketMuLog p (TensorProduct ℚ_[p] K₁ K₂) μ B A := by
  unfold padicPacketMuLog padicMuLog
  have hl := ENNReal.toReal_pos hΛ0 hΛ
  have hb := ENNReal.toReal_pos hB0 hB
  have ha := ENNReal.toReal_pos hA0 hA
  rw [Real.log_div ha.ne' hl.ne', Real.log_div hb.ne' hl.ne', Real.log_div ha.ne' hb.ne']
  ring

/-- **The log-volume of `p ^ μ · (R_I)^∼`**: for nonzero `x`, `y`,
`μ^log((x ⊗ y) · (R_I)^∼) = log(‖x‖ ‖y‖)`, that is `−μ log p` when `‖x‖ ‖y‖ = p ^ (−μ)`. Proof:
`n μ^log((x ⊗ y)(R_I)^∼) = μ^log((x ⊗ y) ^ n (R_I)^∼)` by the cocycle relation and the
invariance under multiplication by a unit, and `(x ⊗ y) ^ n = p ^ m (x' ⊗ y')` with
`(x' ⊗ y') (R_I)^∼ = (R_I)^∼`. -/
theorem tensorLog_muLog_shift {x : K₁} {y : K₂} (hx : x ≠ 0) (hy : y ≠ 0) :
    letI := spectralNorm.normedField ℚ_[p] K₁
    letI := spectralNorm.normedField ℚ_[p] K₂
    padicPacketMuLog p (TensorProduct ℚ_[p] K₁ K₂) μ (padicPacketNormalization p K₁ K₂)
        (tensorLogShift p K₁ K₂ x y) = Real.log (‖x‖ * ‖y‖) := by
  let _ := spectralNorm.normedField ℚ_[p] K₁
  let _ := spectralNorm.normedField ℚ_[p] K₂
  have hN := tensorLog_normalization_measure p K₁ K₂ μ
  have hmeas : ∀ j : ℕ, μ ((Module.finBasis ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).equivFun ''
      tensorLogShift p K₁ K₂ (x ^ j) (y ^ j)) ≠ 0 ∧
      μ ((Module.finBasis ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).equivFun ''
        tensorLogShift p K₁ K₂ (x ^ j) (y ^ j)) ≠ ⊤ := fun j =>
    tensorLog_measure_of_subset p K₁ K₂ μ (pow_ne_zero j hx) (pow_ne_zero j hy)
      (pow_ne_zero j hx) (pow_ne_zero j hy) subset_rfl subset_rfl
  have hstep : ∀ j : ℕ, tensorLogShift p K₁ K₂ (x ^ (j + 1)) (y ^ (j + 1)) =
      (fun z => TensorProduct.tmul ℚ_[p] x y * z) '' tensorLogShift p K₁ K₂ (x ^ j) (y ^ j) := by
    intro j
    unfold tensorLogShift
    rw [Set.image_image]
    congr 1
    funext z
    rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, pow_succ', pow_succ']
  have hinv : TensorProduct.tmul ℚ_[p] x⁻¹ y⁻¹ * TensorProduct.tmul ℚ_[p] x y = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ hx, inv_mul_cancel₀ hy,
      Algebra.TensorProduct.one_def]
  have hinv' : TensorProduct.tmul ℚ_[p] x y * TensorProduct.tmul ℚ_[p] x⁻¹ y⁻¹ = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hx, mul_inv_cancel₀ hy,
      Algebra.TensorProduct.one_def]
  have hone : tensorLogShift p K₁ K₂ (x ^ 1) (y ^ 1) =
      (fun z => TensorProduct.tmul ℚ_[p] x y * z) '' padicPacketNormalization p K₁ K₂ := by
    rw [pow_one, pow_one]
    rfl
  set g : ℕ → ℝ := fun j => padicPacketMuLog p (TensorProduct ℚ_[p] K₁ K₂) μ
    (padicPacketNormalization p K₁ K₂) (tensorLogShift p K₁ K₂ (x ^ j) (y ^ j)) with hg
  have hgj : ∀ j : ℕ, g j = j * g 1 := by
    intro j
    induction j with
    | zero =>
      simp only [hg, pow_zero, tensorLogShift_one]
      rw [padicPacketMuLog_self]
      simp
    | succ j ih =>
      have key : padicPacketMuLog p (TensorProduct ℚ_[p] K₁ K₂) μ
          (tensorLogShift p K₁ K₂ (x ^ 1) (y ^ 1))
          (tensorLogShift p K₁ K₂ (x ^ (j + 1)) (y ^ (j + 1))) = g j := by
        rw [hstep j, hone, tensorLog_muLog_mul_image p K₁ K₂ μ hinv hinv']
      have hc := tensorLog_muLog_cocycle p K₁ K₂ μ hN.1 hN.2.1 (hmeas 1).1 (hmeas 1).2
        (hmeas (j + 1)).1 (hmeas (j + 1)).2
      show padicPacketMuLog p (TensorProduct ℚ_[p] K₁ K₂) μ (padicPacketNormalization p K₁ K₂)
        (tensorLogShift p K₁ K₂ (x ^ (j + 1)) (y ^ (j + 1))) = _
      rw [hc, key, ih]
      push_cast
      ring
  obtain ⟨n, hn, m, x', y', hx', hy', heq, hnorm⟩ := tensorLog_tmul_pow_eq p K₁ K₂ hx hy
  have hx'0 : x' ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hx'
    exact zero_ne_one hx'
  have hy'0 : y' ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hy'
    exact zero_ne_one hy'
  have hunit : tensorLogShift p K₁ K₂ x' y' = padicPacketNormalization p K₁ K₂ := by
    rw [← tensorLogShift_one]
    refine Set.Subset.antisymm (tensorLogShift_subset p K₁ K₂ one_ne_zero one_ne_zero ?_)
      (tensorLogShift_subset p K₁ K₂ hx'0 hy'0 ?_)
    · show ‖x'‖ * ‖y'‖ ≤ ‖(1 : K₁)‖ * ‖(1 : K₂)‖
      rw [hx', hy', norm_one, norm_one]
    · show ‖(1 : K₁)‖ * ‖(1 : K₂)‖ ≤ ‖x'‖ * ‖y'‖
      rw [hx', hy', norm_one, norm_one]
  have hpow : tensorLogShift p K₁ K₂ (x ^ n) (y ^ n) =
      ((p : ℚ_[p]) ^ m) • padicPacketNormalization p K₁ K₂ := by
    show (fun z => TensorProduct.tmul ℚ_[p] (x ^ n) (y ^ n) * z) ''
      padicPacketNormalization p K₁ K₂ = _
    rw [heq, TensorProduct.smul_tmul']
    show tensorLogShift p K₁ K₂ (((p : ℚ_[p]) ^ m) • x') y' = _
    rw [← tensorLogShift_smul, hunit]
  have hgn : g n = -(m * Real.log p) := by
    show padicPacketMuLog p (TensorProduct ℚ_[p] K₁ K₂) μ (padicPacketNormalization p K₁ K₂)
      (tensorLogShift p K₁ K₂ (x ^ n) (y ^ n)) = _
    rw [hpow]
    exact hN.2.2.2 m
  have hlog : (n : ℝ) * Real.log (‖x‖ * ‖y‖) = -(m * Real.log p) := by
    rw [← Real.log_pow, hnorm, Real.log_zpow]
    push_cast
    ring
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : (n : ℝ) * g 1 = (n : ℝ) * Real.log (‖x‖ * ‖y‖) := by
    rw [← hgj n, hgn, hlog]
  have h2 := mul_left_cancel₀ hn0 h1
  simpa only [hg, pow_one] using h2

variable (P₁ : Ideal (integralClosure ℤ_[p] K₁)) [P₁.IsPrime]
  [P₁.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
  (P₂ : Ideal (integralClosure ℤ_[p] K₂)) [P₂.IsPrime]
  [P₂.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]

/-- **IUT IV Proposition 1.4 (iii), second inequality, for two factors** (page 13, proof on
page 14). Let `I* ⊆ I = {1, 2}` be such that `e_i ≤ p − 2` for `i ∉ I*`. For every real `λ` and
`z_i` with `ord(z_i) = −b_i`:
`μ^log(p ^ ⌊λ − 𝔡_I − a_I⌋ · (p ^ (−b_I) · (R_I)^∼)) ≤ (−λ + 𝔡_I + 1) log p +
∑_{i ∈ I*} (3 + log e_i)`. The log-volume is the packet log-volume normalized by
`μ^log((R_I)^∼) = 0`; the exact value `μ^log(p ^ (−b_I) · (R_I)^∼) = b_I log p` is
`tensorLog_muLog_shift`, and the summation is `Proposition1_4.iii_second`. -/
theorem tensorLog_prop1_4_iii_shift (Istar : Finset (Fin 2))
    (hIstar : ∀ i, i ∉ Istar →
      (![P₁.ramificationIdx ℤ_[p], P₂.ramificationIdx ℤ_[p]] : Fin 2 → ℕ) i ≤ p - 2)
    (lam : ℝ) {z₁ : K₁} {z₂ : K₂}
    (hz₁ : letI := spectralNorm.normedField ℚ_[p] K₁
      ‖z₁‖ = (p : ℝ) ^ (Proposition1_2.b p (P₁.ramificationIdx ℤ_[p])))
    (hz₂ : letI := spectralNorm.normedField ℚ_[p] K₂
      ‖z₂‖ = (p : ℝ) ^ (Proposition1_2.b p (P₂.ramificationIdx ℤ_[p]))) :
    padicPacketMuLog p (TensorProduct ℚ_[p] K₁ K₂) μ (padicPacketNormalization p K₁ K₂)
        (((p : ℚ_[p]) ^ ⌊lam - (tensorLogDiffOrder p K₁ P₁ + tensorLogDiffOrder p K₂ P₂) -
          (Proposition1_2.a p (P₁.ramificationIdx ℤ_[p]) +
            Proposition1_2.a p (P₂.ramificationIdx ℤ_[p]))⌋) • tensorLogShift p K₁ K₂ z₁ z₂) ≤
      (-lam + (tensorLogDiffOrder p K₁ P₁ + tensorLogDiffOrder p K₂ P₂) + 1) * Real.log p +
        ∑ i ∈ Istar, (3 + Real.log
          (((![P₁.ramificationIdx ℤ_[p], P₂.ramificationIdx ℤ_[p]] : Fin 2 → ℕ) i : ℕ) : ℝ)) := by
  let _ := spectralNorm.normedField ℚ_[p] K₁
  let _ := spectralNorm.normedField ℚ_[p] K₂
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hL : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.out.one_lt)
  have hz₁0 : z₁ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hz₁
    exact (Real.rpow_pos_of_pos hp0 _).ne' hz₁.symm
  have hz₂0 : z₂ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hz₂
    exact (Real.rpow_pos_of_pos hp0 _).ne' hz₂.symm
  have hN := tensorLog_normalization_measure p K₁ K₂ μ
  have hS := tensorLog_measure_of_subset p K₁ K₂ μ hz₁0 hz₂0 hz₁0 hz₂0 subset_rfl subset_rfl
  have hk1 := Int.sub_one_lt_floor (lam - (tensorLogDiffOrder p K₁ P₁ +
    tensorLogDiffOrder p K₂ P₂) - (Proposition1_2.a p (P₁.ramificationIdx ℤ_[p]) +
      Proposition1_2.a p (P₂.ramificationIdx ℤ_[p])))
  rw [padicPacketMuLog_p_zpow_smul p μ (tensorLog_finrank_pos p K₁ K₂) hN.1 hN.2.1 hS.1 hS.2,
    tensorLog_muLog_shift p K₁ K₂ μ hz₁0 hz₂0, hz₁, hz₂, ← Real.rpow_add hp0,
    Real.log_rpow hp0]
  refine Proposition1_4.iii_second hp.out.two_le Finset.univ Istar (Finset.subset_univ _) _ ?_
    (fun i _ hi => hIstar i hi) ?_
  · intro i
    fin_cases i
    · exact tensorLog_one_le_ramificationIdx p K₁ P₁
    · exact tensorLog_one_le_ramificationIdx p K₂ P₂
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    have h := mul_le_mul_of_nonneg_right (show -((⌊lam - (tensorLogDiffOrder p K₁ P₁ +
      tensorLogDiffOrder p K₂ P₂) - (Proposition1_2.a p (P₁.ramificationIdx ℤ_[p]) +
        Proposition1_2.a p (P₂.ramificationIdx ℤ_[p]))⌋ : ℤ) : ℝ) ≤
        -(lam - (tensorLogDiffOrder p K₁ P₁ + tensorLogDiffOrder p K₂ P₂) -
          (Proposition1_2.a p (P₁.ramificationIdx ℤ_[p]) +
            Proposition1_2.a p (P₂.ramificationIdx ℤ_[p]))) + 1 by linarith) hL.le
    linarith

/-- **IUT IV Proposition 1.4 (iii), first inequality, for two factors, in the case
`e_1, e_2 ≤ p − 2`** (page 13): if `p > 2` and `e_i ≤ p − 2` for `i = 1, 2`, then for every
`I* ⊆ I` and real `λ`, `μ^log(p ^ ⌊λ − 𝔡_I − a_I⌋ · log_p(R_I^×)) ≤
(−λ + 𝔡_I + 1 + 4 |I*| / p) log p`. The proof bounds `μ^log(log_p(R_I^×))` by
`μ^log(p ^ (−b_I) · (R_I)^∼) = b_I log p = −a_I log p` instead of the additivity over the tensor
factors used on page 14; for `e_i > p − 2` that bound is too weak and the case is not covered. -/
theorem tensorLog_prop1_4_iii_lattice (hp2 : 2 < p) (he₁ : P₁.ramificationIdx ℤ_[p] ≤ p - 2)
    (he₂ : P₂.ramificationIdx ℤ_[p] ≤ p - 2) (Istar : Finset (Fin 2)) (lam : ℝ) :
    padicPacketMuLog p (TensorProduct ℚ_[p] K₁ K₂) μ (padicPacketNormalization p K₁ K₂)
        (((p : ℚ_[p]) ^ ⌊lam - (tensorLogDiffOrder p K₁ P₁ + tensorLogDiffOrder p K₂ P₂) -
          (Proposition1_2.a p (P₁.ramificationIdx ℤ_[p]) +
            Proposition1_2.a p (P₂.ramificationIdx ℤ_[p]))⌋) • tensorLogLattice p K₁ K₂) ≤
      (-lam + (tensorLogDiffOrder p K₁ P₁ + tensorLogDiffOrder p K₂ P₂) + 1 +
        4 * Istar.card / p) * Real.log p := by
  let _ := spectralNorm.normedField ℚ_[p] K₁
  let _ := spectralNorm.normedField ℚ_[p] K₂
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hpq : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hL : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.out.one_lt)
  obtain ⟨-, ⟨z₁, hz₁⟩, -⟩ := padicBridge_extLogUnit_image_fractionalIdeal p K₁ P₁
  obtain ⟨-, ⟨z₂, hz₂⟩, -⟩ := padicBridge_extLogUnit_image_fractionalIdeal p K₂ P₂
  have hz₁0 : z₁ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hz₁
    exact (Real.rpow_pos_of_pos hp0 _).ne' hz₁.symm
  have hz₂0 : z₂ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hz₂
    exact (Real.rpow_pos_of_pos hp0 _).ne' hz₂.symm
  have hN := tensorLog_normalization_measure p K₁ K₂ μ
  obtain ⟨M, hM⟩ := exists_nat_ge (tensorLogDiffOrder p K₁ P₁ + tensorLogDiffOrder p K₂ P₂ +
    (Proposition1_2.a p (P₁.ramificationIdx ℤ_[p]) +
      Proposition1_2.a p (P₂.ramificationIdx ℤ_[p])))
  have hlo : tensorLogShift p K₁ K₂ (((p : ℚ_[p]) ^ (M : ℤ)) • (1 : K₁)) 1 ⊆
      tensorLogLattice p K₁ K₂ := by
    refine tensorLog_shift_subset_lattice p K₁ K₂ P₁ P₂ ?_
    show ‖((p : ℚ_[p]) ^ (M : ℤ)) • (1 : K₁)‖ * ‖(1 : K₂)‖ ≤ _
    rw [tensorLog_norm_p_zpow_smul, norm_one, norm_one, mul_one, mul_one]
    apply Real.rpow_le_rpow_of_exponent_le hp1
    push_cast
    linarith
  have hhi := tensorLog_lattice_subset_shift p K₁ K₂ P₁ P₂ hz₁ hz₂
  have hLat := tensorLog_measure_of_subset p K₁ K₂ μ
    (smul_ne_zero (zpow_ne_zero _ hpq) one_ne_zero) one_ne_zero hz₁0 hz₂0 hlo hhi
  have hS := tensorLog_measure_of_subset p K₁ K₂ μ hz₁0 hz₂0 hz₁0 hz₂0 subset_rfl subset_rfl
  have h1 := packet_muLog_floor_smul_le p (TensorProduct ℚ_[p] K₁ K₂) μ
    (tensorLog_finrank_pos p K₁ K₂) (Λ := padicPacketNormalization p K₁ K₂) hN.1 hN.2.1
    hLat.1 hLat.2 (lam - (tensorLogDiffOrder p K₁ P₁ + tensorLogDiffOrder p K₂ P₂) -
      (Proposition1_2.a p (P₁.ramificationIdx ℤ_[p]) +
        Proposition1_2.a p (P₂.ramificationIdx ℤ_[p])))
  have h2 : padicPacketMuLog p (TensorProduct ℚ_[p] K₁ K₂) μ (padicPacketNormalization p K₁ K₂)
      (tensorLogLattice p K₁ K₂) ≤ padicPacketMuLog p (TensorProduct ℚ_[p] K₁ K₂) μ
        (padicPacketNormalization p K₁ K₂) (tensorLogShift p K₁ K₂ z₁ z₂) := by
    unfold padicPacketMuLog
    exact padicMuLog_mono p μ (Set.image_mono hhi) hN.1 hN.2.1 hLat.1 hS.2
  have h3 := tensorLog_muLog_shift p K₁ K₂ μ hz₁0 hz₂0
  rw [hz₁, hz₂, ← Real.rpow_add hp0, Real.log_rpow hp0] at h3
  have hab₁ := Proposition1_2.a_b_of_le hp2 (tensorLog_one_le_ramificationIdx p K₁ P₁) he₁
  have hab₂ := Proposition1_2.a_b_of_le hp2 (tensorLog_one_le_ramificationIdx p K₂ P₂) he₂
  rw [hab₁.2, hab₂.2] at h3
  rw [hab₁.1, hab₂.1] at h1 ⊢
  have h4 : 0 ≤ 4 * (Istar.card : ℝ) / p * Real.log p := by positivity
  linarith

omit [MeasurableSpace (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) → ℚ_[p])]
  [BorelSpace (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) → ℚ_[p])] in
/-- **IUT IV Proposition 1.4 (iii), last sentence, for two factors** (page 13):
`𝔡_I + a_I ≥ |I| = 2` if `p > 2`, and `𝔡_I + a_I ≥ 2 |I| = 4` if `p = 2`. -/
theorem tensorLog_dI_add_aI_ge :
    (2 < p → 2 ≤ tensorLogDiffOrder p K₁ P₁ + tensorLogDiffOrder p K₂ P₂ +
      (Proposition1_2.a p (P₁.ramificationIdx ℤ_[p]) +
        Proposition1_2.a p (P₂.ramificationIdx ℤ_[p]))) ∧
    (p = 2 → 4 ≤ tensorLogDiffOrder p K₁ P₁ + tensorLogDiffOrder p K₂ P₂ +
      (Proposition1_2.a p (P₁.ramificationIdx ℤ_[p]) +
        Proposition1_2.a p (P₂.ramificationIdx ℤ_[p]))) := by
  have h₁ := padic_differentOrder_add_a_ge p K₁ P₁
  have h₂ := padic_differentOrder_add_a_ge p K₂ P₂
  unfold tensorLogDiffOrder
  exact ⟨fun h => by linarith [h₁.1 h, h₂.1 h], fun h => by linarith [h₁.2 h, h₂.2 h]⟩

/-- **IUT IV Proposition 1.4 (iv) for two factors** (page 13): if `p > 2` and `e_1 = e_2 = 1`,
then `φ((R_I)^∼) ⊆ (R_I)^∼` and `μ^log((R_I)^∼) = 0`. -/
theorem tensorLog_prop1_4_iv (hp2 : 2 < p) (he₁ : P₁.ramificationIdx ℤ_[p] = 1)
    (he₂ : P₂.ramificationIdx ℤ_[p] = 1)
    (φ : TensorProduct ℚ_[p] K₁ K₂ ≃ₗ[ℚ_[p]] TensorProduct ℚ_[p] K₁ K₂)
    (hφ : φ '' tensorLogLattice p K₁ K₂ = tensorLogLattice p K₁ K₂) :
    φ '' padicPacketNormalization p K₁ K₂ ⊆ padicPacketNormalization p K₁ K₂ ∧
      padicPacketMuLog p (TensorProduct ℚ_[p] K₁ K₂) μ (padicPacketNormalization p K₁ K₂)
        (padicPacketNormalization p K₁ K₂) = 0 :=
  ⟨tensorLog_prop1_2_iv p K₁ K₂ P₁ P₂ hp2 he₁ he₂ φ hφ,
    (tensorLog_normalization_measure p K₁ K₂ μ).2.2.1⟩

end Volume

/-! ## Nonvacuity: `K₁ = K₂ = ℚ_p`, `p > 2` -/

section Nonvacuity

variable (p : ℕ) [hp : Fact p.Prime]

/-- On `ℚ_p` itself the spectral norm is the `p`-adic norm. -/
theorem tensorLog_padic_spectralNorm (x : ℚ_[p]) : spectralNorm ℚ_[p] ℚ_[p] x = ‖x‖ :=
  spectralNorm_extends (L := ℚ_[p]) x

/-- **`e = 1` for `ℚ_p`**: the ramification index of a prime of `ℤ_p = integralClosure ℤ_p ℚ_p`
over `p` is `1`. -/
theorem tensorLog_padic_ramificationIdx (P : Ideal (integralClosure ℤ_[p] ℚ_[p])) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] : P.ramificationIdx ℤ_[p] = 1 := by
  refine le_antisymm (padicBridge_ramificationIdx_le_of_hval p ℚ_[p] P (e' := 1) ?_)
    (tensorLog_one_le_ramificationIdx p ℚ_[p] P)
  intro x hx
  change spectralNorm ℚ_[p] ℚ_[p] x < 1 at hx
  show spectralNorm ℚ_[p] ℚ_[p] x ^ 1 ≤ _
  rw [tensorLog_padic_spectralNorm] at hx ⊢
  rw [pow_one]
  obtain ⟨w, hw⟩ := (PadicInt.norm_lt_one_iff_dvd (⟨x, hx.le⟩ : ℤ_[p])).1 hx
  have hx' : x = (p : ℚ_[p]) * (w : ℚ_[p]) := by
    have := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hw
    simpa using this
  rw [hx', norm_mul, Padic.norm_p]
  exact mul_le_of_le_one_right (inv_nonneg.2 (Nat.cast_nonneg _)) (PadicInt.norm_le_one w)

/-- **`log_p(ℤ_p^×) = p ℤ_p`** for `p > 2` (Proposition 1.2 (i) with `e = 1`). -/
theorem tensorLog_padic_units (hp2 : 2 < p) :
    tensorLogUnits p ℚ_[p] = {z : ℚ_[p] | ‖z‖ ≤ (p : ℝ)⁻¹} := by
  have := padicBridge_isLocalRing p ℚ_[p]
  have := padicBridge_maximalIdeal_liesOver p ℚ_[p]
  have he := tensorLog_padic_ramificationIdx p (IsLocalRing.maximalIdeal _)
  have h := padicBridge_extLogUnit_image_eq_of_le p ℚ_[p] (IsLocalRing.maximalIdeal _) hp2
    (by rw [he]; omega)
  unfold tensorLogUnits
  rw [h, he]
  ext z
  change spectralNorm ℚ_[p] ℚ_[p] z ≤ _ ↔ _
  rw [tensorLog_padic_spectralNorm]
  norm_num [Real.rpow_neg_one]

/-- `x ⊗ y = (x y) · (1 ⊗ 1)` in `ℚ_p ⊗[ℚ_p] ℚ_p`. -/
theorem tensorLog_padic_tmul (x y : ℚ_[p]) :
    TensorProduct.tmul ℚ_[p] x y = (x * y) • TensorProduct.tmul ℚ_[p] (1 : ℚ_[p]) (1 : ℚ_[p]) := by
  rw [mul_smul, ← TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul,
    mul_one, mul_one]

/-- **The lattice `log_p(R_I^×)` for `K₁ = K₂ = ℚ_p`, `p > 2`**, explicitly:
`log_p(ℤ_p^×) ⊗ log_p(ℤ_p^×) = p ^ 2 ℤ_p · (1 ⊗ 1)`. -/
theorem tensorLog_padic_lattice (hp2 : 2 < p) :
    tensorLogLattice p ℚ_[p] ℚ_[p] = {w | ∃ c : ℚ_[p], ‖c‖ ≤ ((p : ℝ) ^ 2)⁻¹ ∧
      w = c • TensorProduct.tmul ℚ_[p] (1 : ℚ_[p]) (1 : ℚ_[p])} := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hpq : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  unfold tensorLogLattice
  rw [tensorLog_padic_units p hp2]
  let M : AddSubmonoid (TensorProduct ℚ_[p] ℚ_[p] ℚ_[p]) :=
    { carrier := {w | ∃ c : ℚ_[p], ‖c‖ ≤ ((p : ℝ) ^ 2)⁻¹ ∧
        w = c • TensorProduct.tmul ℚ_[p] (1 : ℚ_[p]) (1 : ℚ_[p])}
      zero_mem' := ⟨0, by simp, by simp⟩
      add_mem' := by
        rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
        exact ⟨c + d, (IsUltrametricDist.norm_add_le_max c d).trans (max_le hc hd),
          (add_smul c d _).symm⟩ }
  refine Set.Subset.antisymm ?_ ?_
  · show _ ⊆ SetLike.coe M
    refine SetLike.coe_subset_coe.2 (AddSubmonoid.closure_le.2 ?_)
    rintro _ ⟨a, x, y, hx, hy, rfl⟩
    refine ⟨a * (x * y), ?_, ?_⟩
    · rw [norm_mul, norm_mul, pow_two, mul_inv]
      have ha := PadicInt.norm_le_one a
      rw [PadicInt.norm_def] at ha
      have hx' : ‖x‖ ≤ (p : ℝ)⁻¹ := hx
      have hy' : ‖y‖ ≤ (p : ℝ)⁻¹ := hy
      calc ‖(a : ℚ_[p])‖ * (‖x‖ * ‖y‖) ≤ 1 * ((p : ℝ)⁻¹ * (p : ℝ)⁻¹) :=
            mul_le_mul ha (mul_le_mul hx' hy' (norm_nonneg _) (by positivity))
              (by positivity) zero_le_one
        _ = _ := one_mul _
    · rw [tensorLog_padic_tmul, smul_smul]
  · rintro _ ⟨c, hc, rfl⟩
    have hpn : ‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹ := Padic.norm_p
    have ha : ‖c / (p : ℚ_[p]) ^ 2‖ ≤ 1 := by
      rw [norm_div, norm_pow, hpn, div_le_one (by positivity), inv_pow]
      exact hc
    refine AddSubmonoid.subset_closure ⟨⟨c / (p : ℚ_[p]) ^ 2, ha⟩, p, p, ?_, ?_, ?_⟩
    · show ‖(p : ℚ_[p])‖ ≤ _
      rw [hpn]
    · show ‖(p : ℚ_[p])‖ ≤ _
      rw [hpn]
    · rw [tensorLog_padic_tmul p (p : ℚ_[p]) p, smul_smul]
      congr 1
      show c = c / (p : ℚ_[p]) ^ 2 * ((p : ℚ_[p]) * p)
      field_simp

/-- **`(R_I)^∼` for `K₁ = K₂ = ℚ_p`**, explicitly: `ℤ_p · (1 ⊗ 1)`. -/
theorem tensorLog_padic_normalization :
    padicPacketNormalization p ℚ_[p] ℚ_[p] = {w | ∃ c : ℚ_[p], ‖c‖ ≤ 1 ∧
      w = c • TensorProduct.tmul ℚ_[p] (1 : ℚ_[p]) (1 : ℚ_[p])} := by
  refine Set.Subset.antisymm ?_ ?_
  · intro z hz
    let e := Algebra.TensorProduct.lid ℚ_[p] ℚ_[p]
    have hc : ‖e z‖ ≤ 1 := by
      have h1 := padicVolIntegral_map p e.toAlgHom hz
      have h2 := (padicBridge_mem_integralClosure_iff p ℚ_[p] _).1
        ((tensorDiff_padicVolIntegral_iff p ℚ_[p] _).1 h1)
      change spectralNorm ℚ_[p] ℚ_[p] _ ≤ 1 at h2
      rwa [tensorLog_padic_spectralNorm] at h2
    refine ⟨e z, hc, ?_⟩
    conv_lhs => rw [← e.symm_apply_apply z]
    rw [Algebra.TensorProduct.lid_symm_apply, ← TensorProduct.tmul_smul, smul_eq_mul, mul_one]
  · rintro _ ⟨c, hc, rfl⟩
    have h : c • TensorProduct.tmul ℚ_[p] (1 : ℚ_[p]) (1 : ℚ_[p]) =
        TensorProduct.tmul ℚ_[p] c (1 : ℚ_[p]) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h]
    refine tensorLog_tmul_mem_normalization p ℚ_[p] ℚ_[p] ?_
    show spectralNorm ℚ_[p] ℚ_[p] c * spectralNorm ℚ_[p] ℚ_[p] 1 ≤ 1
    rw [tensorLog_padic_spectralNorm, tensorLog_padic_spectralNorm, norm_one, mul_one]
    exact hc

/-- **Nonvacuity of Proposition 1.2 (iv) and 1.4 (iv)** for `K₁ = K₂ = ℚ_p`, `p > 2`: with `P`
the maximal ideal of `ℤ_p`, `e_1 = e_2 = 1`; `φ = −id` maps `log_p(R_I^×) = p ^ 2 ℤ_p (1 ⊗ 1)`
onto itself (and is not the identity); and `tensorLog_prop1_2_iv` gives
`φ(ℤ_p (1 ⊗ 1)) ⊆ ℤ_p (1 ⊗ 1)`. -/
theorem tensorLog_padic_prop1_2_iv (hp2 : 2 < p) :
    haveI := padicBridge_isLocalRing p ℚ_[p]
    (IsLocalRing.maximalIdeal (integralClosure ℤ_[p] ℚ_[p])).ramificationIdx ℤ_[p] = 1 ∧
      LinearEquiv.neg ℚ_[p] '' tensorLogLattice p ℚ_[p] ℚ_[p] = tensorLogLattice p ℚ_[p] ℚ_[p] ∧
      LinearEquiv.neg ℚ_[p] ≠ LinearEquiv.refl ℚ_[p] (TensorProduct ℚ_[p] ℚ_[p] ℚ_[p]) ∧
      LinearEquiv.neg ℚ_[p] '' {w | ∃ c : ℚ_[p], ‖c‖ ≤ 1 ∧
          w = c • TensorProduct.tmul ℚ_[p] (1 : ℚ_[p]) (1 : ℚ_[p])} ⊆
        {w | ∃ c : ℚ_[p], ‖c‖ ≤ 1 ∧
          w = c • TensorProduct.tmul ℚ_[p] (1 : ℚ_[p]) (1 : ℚ_[p])} := by
  have := padicBridge_isLocalRing p ℚ_[p]
  have := padicBridge_maximalIdeal_liesOver p ℚ_[p]
  have he := tensorLog_padic_ramificationIdx p (IsLocalRing.maximalIdeal _)
  have hφ : LinearEquiv.neg ℚ_[p] '' tensorLogLattice p ℚ_[p] ℚ_[p] =
      tensorLogLattice p ℚ_[p] ℚ_[p] := by
    rw [tensorLog_padic_lattice p hp2]
    ext w
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨-c, by rwa [norm_neg], by rw [LinearEquiv.neg_apply, neg_smul]⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨(-c) • TensorProduct.tmul ℚ_[p] (1 : ℚ_[p]) (1 : ℚ_[p]),
        ⟨-c, by rwa [norm_neg], rfl⟩, by rw [LinearEquiv.neg_apply, neg_smul, neg_neg]⟩
  refine ⟨he, hφ, ?_, ?_⟩
  · intro h
    have h1 := LinearEquiv.congr_fun h (1 : TensorProduct ℚ_[p] ℚ_[p] ℚ_[p])
    rw [LinearEquiv.neg_apply, LinearEquiv.refl_apply] at h1
    have h2 : (2 : ℚ_[p]) • (1 : TensorProduct ℚ_[p] ℚ_[p] ℚ_[p]) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h1]
      exact neg_add_cancel 1
    have h3 : (1 : TensorProduct ℚ_[p] ℚ_[p] ℚ_[p]) = 0 :=
      (smul_eq_zero.1 h2).resolve_left two_ne_zero
    have : Nontrivial (TensorProduct ℚ_[p] ℚ_[p] ℚ_[p]) :=
      Module.nontrivial_of_finrank_pos (R := ℚ_[p]) (tensorLog_finrank_pos p ℚ_[p] ℚ_[p])
    exact one_ne_zero h3
  · rw [← tensorLog_padic_normalization p]
    exact tensorLog_prop1_2_iv p ℚ_[p] ℚ_[p] (IsLocalRing.maximalIdeal _)
      (IsLocalRing.maximalIdeal _) hp2 he he (LinearEquiv.neg ℚ_[p]) hφ

end Nonvacuity

end IUT.PaperIV.LocalFields
