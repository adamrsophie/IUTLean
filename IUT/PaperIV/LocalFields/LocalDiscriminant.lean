import Mathlib
import IUT.Audit.TensorOrderIndex

/-!
# The discriminant and the different of a finite extension of `ℚ_p`; the index of `R_E`

Sources: Mochizuki, *Inter-universal Teichmüller Theory IV*, Proposition 1.1 (page 9) and
Proposition 1.4 (i) (page 13). Pages read for this file: 9 and 13; both were checked against
rendered images. Displays relied on:
* page 9: `ord` is the `p`-adic valuation with `ord(p) = 1`; `R_i` is the ring of integers of a
  finite extension `k_i` of `ℚ_p` and `𝔡_i ∈ ℚ_{≥0}` the order `ord` of any generator of the
  different ideal of `R_i` over `ℤ_p`; `R_E` is the tensor product over `ℤ_p`, and
  `p ^ (𝔡_{I*}) · (R_I)^∼ ⊆ R_I ⊆ (R_I)^∼` (for `I = {1, 2}`, `* = 1`: the allowance `p ^ 𝔡_2`);
* page 13, Proposition 1.4 (i): log-volumes normalized "by dividing by the degree of the finite
  extension", with `μ^log((R_E)^∼) = 0` and `μ^log(p · (R_E)^∼) = −log(p)`.
Also: C. Zeng, "An Integral-Structure Inflation in the Hull Operation of IUT Corollary 3.12",
hexagon 2610.00646, version 1, Theorem 5.1 and section 14 (the non-Galois case), read from its
TeX source; there is no page render of it.

This file is not a formalization of Proposition 1.1 or 1.4. It proves the relation between the
discriminant and the different of a finite extension of `ℚ_p`, uses it to express the index of
`R_E` in `(R_E)^∼` (computed in `IUT.Audit.TensorOrderIndex`) through `𝔡`, and removes the basis
hypothesis of the general two-factor index formula.

## The objects

`K` is a finite extension of `ℚ_[p]` (a field with a finite-dimensional `ℚ_[p]`-algebra
structure and a compatible `ℤ_[p]`-algebra structure), `d = [K : ℚ_p]`,
`R = integralClosure ℤ_[p] K`, `P` a prime of `R` over `p` with ramification index `e`
(`R` is local, `IUT.PaperIV.LocalFields.Bridge`, so `P` is its maximal ideal),
`n = differentExponent ℤ_[p] R P` the exponent of `P` in Mathlib's `differentIdeal ℤ_[p] R`, and
`𝔡 = differentOrder ℤ_[p] R P = n / e`, the page's `𝔡` in the normalization `ord(p) = 1`. An
integral basis is a `ℚ_p`-basis `b` of `K` that is a `ℤ_p`-basis of `R`
(`tOrdIdxIntegralBasis`); one exists (`tOrdIdx_exists_integralBasis`). `v_p` is
`Padic.valuation`. `R_E`, `(R_E)^∼` and `μ^log` are `tensorIdxRing`, `tensorIdxNormRing` and
`padicPacketMuLog`, as in `IUT.PaperIV.LocalFields.TensorIndex`.

## What is proved

1. *Discriminant and different.* `locDisc_norm_discr_pow`: `‖disc b‖ ^ e = (p⁻¹) ^ (d · n)`;
   `locDisc_valuation_discr_mul`: `v_p(disc b) · e = d · n`; `locDisc_valuation_discr`:
   `v_p(disc b) = d · 𝔡`. Proof: the trace dual basis `b^∨` spans the inverse different
   (`coeIdeal_differentIdeal`, `FractionalIdeal.mem_dual`), which is `ϖ^{-n} R` for a
   uniformizer `ϖ`, so `b^∨` and `ϖ^{-n} b` span the same lattice and the determinant between them
   is a unit (`tOrdIdx_relIndex_eq`); the determinant of `b` in `b^∨` is `disc b`, and that of
   `ϖ^{-n} b` in `b` is `N(ϖ)^{-n}`; finally `(p) = (ϖ)^e` gives `‖N(ϖ)‖^e = p^{-d}`
   (`locDisc_norm_algNorm_uniformizer`, with `locDisc_norm_algNorm_unit`). Mathlib's
   `NumberField.absNorm_differentIdeal` is for number fields; it is not used. Neither the
   residue degree nor `e f = d` is needed.
2. *The Galois case.* `locDisc_muLog_galois`: for `K/ℚ_p` Galois,
   `μ^log(R_E) = −(1/2) · 𝔡 · log p` on `K ⊗ K` (from `tOrdIdx_muLog_galois_valuation` and item
   1). `locDisc_muLog_galois_allowance`: `0 ≤ μ^log(R_E) + 𝔡 log p` and the gap between the exact
   value and the allowance `−𝔡 log p` of Proposition 1.1 is `(1/2) · 𝔡 · log p`; that is, the
   exact value is half of the allowance. These are statements about the normalized log-volume of
   this library only; the library's general lower bound `tensorIdx_muLog_bounds` has `⌈𝔡⌉` in
   place of `𝔡`.
3. *Any two factors.* `locDisc_exists_normBasis`: for any finite extensions `K₁`, `K₂` (no
   Galois hypothesis) `(R_E)^∼` is the `ℤ_p`-span of a `ℚ_p`-basis of `K₁ ⊗ K₂` (Mathlib's
   lattices over a principal ideal domain, `Submodule.IsFullLattice`; `(R_E)^∼` lies between
   `R_E` and `N⁻¹ R_E`, `N` the finite index). `locDisc_index_valuation`: for any such basis `n`,
   `2 v_p([(R_E)^∼ : R_E]) = d₂ v_p(disc b) + d₁ v_p(disc c) − v_p(disc n)`, where `v_p` of the
   index is `multiplicity p` (Mathlib's `p`-adic valuation of a natural number);
   `locDisc_index_general`: the same together with the norm form of
   `tOrdIdx_index_sq_general`, with `n` supplied.

## Not proved

* The value of `v_p(disc n)` in the non-Galois case. Section 14 of the paper decomposes
  `K ⊗ K` into composita `K_j` and uses `v_p(disc n) = Σ_j v_p(disc K_j)`; this needs the
  splitting of `K ⊗ K` into fields for a non-Galois `K` and the rings of integers of the
  composita, which are not formalized here. So the paper's comparison `ρ_NG² = ρ_G² / p^Δ`,
  `Δ ≥ 0`, is not proved.
* An explicit non-Galois example, here; the index `3^7` below is proved in
  `IUT.PaperIV.LocalFields.LocalDiscriminantCubic` (`locDiscCu_index`). For `K = ℚ_3(∛3)` with
  itself a hand computation (not in Lean)
  gives `v_3(disc K) = 5`, `K ⊗ K ≅ K × K(ω)` with `v_3(disc K(ω)) = 11`, hence
  `2 v_3(index) = 15 + 15 − 16 = 14`, index `3^7`, while the Galois formula would give
  `index² = 3^15`. Formalizing it needs the field `ℚ_3(∛3)`, its ring of integers, the
  decomposition of `K ⊗ K` and the different of the degree 6 field `K(ω)`.
* More than two factors, here; in the Galois case the index for `n` factors is
  `IUT.Audit.TensorOrderIndexMany.tOrdMany_index_sq`.
-/

open IUT.Audit.TensorOrderIndex IUT.Prerequisites.PadicVolume

namespace IUT.PaperIV.LocalFields

/-! ## 1. `v_p(disc b) = d · 𝔡` -/

section Discriminant

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K] [Algebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]

/-- An element of `ℚ_p` is in the image of `ℤ_p` exactly when its norm is at most one. -/
theorem locDisc_mem_range_iff (q : ℚ_[p]) :
    q ∈ (algebraMap ℤ_[p] ℚ_[p]).range ↔ ‖q‖ ≤ 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [PadicInt.algebraMap_apply, ← PadicInt.norm_def]
    exact PadicInt.norm_le_one y
  · intro h
    exact ⟨⟨q, h⟩, rfl⟩

omit [FiniteDimensional ℚ_[p] K] in
/-- The norm from `K` to `ℚ_p` of an element of the ring of integers has `p`-adic norm at most
one. -/
theorem locDisc_norm_algNorm_le_one (r : integralClosure ℤ_[p] K) :
    ‖Algebra.norm ℚ_[p] (r : K)‖ ≤ 1 := by
  have h : IsIntegral ℤ_[p] (Algebra.norm ℚ_[p] (r : K)) := Algebra.isIntegral_norm ℚ_[p] r.2
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [← hy, PadicInt.algebraMap_apply, ← PadicInt.norm_def]
  exact PadicInt.norm_le_one y

omit [FiniteDimensional ℚ_[p] K] in
/-- The norm from `K` to `ℚ_p` of a unit of the ring of integers has `p`-adic norm one. -/
theorem locDisc_norm_algNorm_unit (v : (integralClosure ℤ_[p] K)ˣ) :
    ‖Algebra.norm ℚ_[p] ((v : integralClosure ℤ_[p] K) : K)‖ = 1 := by
  have h1 := locDisc_norm_algNorm_le_one (p := p) (K := K) (v : integralClosure ℤ_[p] K)
  have h2 := locDisc_norm_algNorm_le_one (p := p) (K := K)
    ((v⁻¹ : (integralClosure ℤ_[p] K)ˣ) : integralClosure ℤ_[p] K)
  have hvv : ((v : integralClosure ℤ_[p] K) : K) *
      (((v⁻¹ : (integralClosure ℤ_[p] K)ˣ) : integralClosure ℤ_[p] K) : K) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
  have hm := congrArg (fun x : K => ‖Algebra.norm ℚ_[p] x‖) hvv
  simp only [map_mul, norm_mul, map_one, norm_one] at hm
  have h3 := mul_le_mul_of_nonneg_left h2 (norm_nonneg (Algebra.norm ℚ_[p]
    ((v : integralClosure ℤ_[p] K) : K)))
  rw [hm, mul_one] at h3
  exact le_antisymm h1 h3

/-- **The norm of a uniformizer**: if `(p) = (ϖ) ^ e` as ideals of the ring of integers, then
`‖N_{K/ℚ_p}(ϖ)‖ ^ e = p ^ (-d)` with `d = [K : ℚ_p]`. -/
theorem locDisc_norm_algNorm_uniformizer {ϖ : integralClosure ℤ_[p] K} {e : ℕ}
    (hpe : Ideal.span {((p : ℕ) : integralClosure ℤ_[p] K)} = Ideal.span {ϖ} ^ e) :
    ‖Algebra.norm ℚ_[p] (ϖ : K)‖ ^ e = ((p : ℝ)⁻¹) ^ Module.finrank ℚ_[p] K := by
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at hpe
  obtain ⟨v, hv⟩ := hpe
  have hK := congrArg (fun x : integralClosure ℤ_[p] K => ‖Algebra.norm ℚ_[p] (x : K)‖) hv
  have hp' : (((p : ℕ) : integralClosure ℤ_[p] K) : K) = algebraMap ℚ_[p] K (p : ℚ_[p]) := by
    simp
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, norm_mul,
    norm_pow] at hK
  rw [hp', Algebra.norm_algebraMap, norm_pow, Padic.norm_p, locDisc_norm_algNorm_unit,
    mul_one] at hK
  exact hK.symm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℚ_[p] K] [Fintype ι] [DecidableEq ι] in
/-- For an integral basis `b`, membership in the ring of integers is integrality of all
`b`-coordinates. -/
theorem locDisc_mem_iff {b : Module.Basis ι ℚ_[p] K} (hb : tOrdIdxIntegralBasis p b) (y : K) :
    y ∈ integralClosure ℤ_[p] K ↔ ∀ i, ‖b.repr y i‖ ≤ 1 :=
  (tensorDiff_padicVolIntegral_iff p K y).symm.trans (hb y)

omit [FiniteDimensional ℚ_[p] K] [DecidableEq ι] in
/-- **The trace dual of the ring of integers, through an integral basis**: `x` pairs integrally
with all of `R` under the trace if and only if it pairs integrally with every `b_i`. -/
theorem locDisc_trace_mem_iff {b : Module.Basis ι ℚ_[p] K} (hb : tOrdIdxIntegralBasis p b)
    (x : K) :
    (∀ r : integralClosure ℤ_[p] K,
        Algebra.trace ℚ_[p] K (x * r) ∈ (algebraMap ℤ_[p] ℚ_[p]).range) ↔
      ∀ i, ‖Algebra.trace ℚ_[p] K (x * b i)‖ ≤ 1 := by
  constructor
  · intro h i
    rw [← locDisc_mem_range_iff]
    exact h ⟨b i, (locDisc_mem_iff hb (b i)).2 ((tOrdIdx_mem_lattice b _).1
      (tOrdIdx_basis_mem b i))⟩
  · intro h r
    have hr := (locDisc_mem_iff hb (r : K)).1 r.2
    rw [locDisc_mem_range_iff, ← (PadicInt.mem_subring_iff p), ← b.sum_repr (r : K),
      Finset.mul_sum, map_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul]
    exact Subring.mul_mem _ ((PadicInt.mem_subring_iff p).2 (hr i))
      ((PadicInt.mem_subring_iff p).2 (h i))

/-- **`v_p(disc b) = d · 𝔡`, in norm form**: for a finite extension `K` of `ℚ_p` of degree `d`,
a prime `P` of its ring of integers `R` over `p` with ramification index `e`, and an integral
basis `b`, `‖disc b‖ ^ e = (p⁻¹) ^ (d · n)`, where `n` is the exponent of `P` in the different
of `R` over `ℤ_p` (`differentExponent`). -/
theorem locDisc_norm_discr_pow (P : Ideal (integralClosure ℤ_[p] K)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] (b : Module.Basis ι ℚ_[p] K)
    (hb : tOrdIdxIntegralBasis p b) :
    letI := isDedekindDomain_ringOfIntegers_padic p K
    letI := isTorsionFree_ringOfIntegers_padic p K
    ‖Algebra.discr ℚ_[p] b‖ ^ P.ramificationIdx ℤ_[p] =
      ((p : ℝ)⁻¹) ^ (Module.finrank ℚ_[p] K *
        differentExponent ℤ_[p] (integralClosure ℤ_[p] K) P) := by
  let := isDedekindDomain_ringOfIntegers_padic p K
  let := isTorsionFree_ringOfIntegers_padic p K
  have := padicBridge_isLocalRing p K
  have := padicBridge_isDiscreteValuationRing p K
  have : IsFractionRing (integralClosure ℤ_[p] K) K :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[p] ℚ_[p] K _
  obtain ⟨ϖ, hirr, hPϖ, hpe, -⟩ := padicBridge_uniformizer p K P
  have hD := differentIdeal_ne_bot_of_isIntegralClosure ℤ_[p] ℚ_[p] K
    (integralClosure ℤ_[p] K)
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hD hirr
  have hP0 : P ≠ ⊥ := by
    rw [hPϖ, Ne, Ideal.span_singleton_eq_bot]
    exact hirr.ne_zero
  have hexp : differentExponent ℤ_[p] (integralClosure ℤ_[p] K) P = n := by
    unfold differentExponent
    rw [hn, ← Ideal.span_singleton_pow, ← hPϖ,
      multiplicity_pow_self_of_prime (Ideal.prime_of_isPrime hP0 inferInstance)]
  rw [hexp]
  -- `u` generates the different in `K`
  set u : K := algebraMap (integralClosure ℤ_[p] K) K (ϖ ^ n) with hu_def
  have hu : u ≠ 0 := by
    rw [hu_def, Ne, map_eq_zero_iff _ (IsFractionRing.injective _ K)]
    exact pow_ne_zero _ hirr.ne_zero
  -- the trace dual of `R` is `u⁻¹ R`
  have hdual : ∀ x : K, (∀ r : integralClosure ℤ_[p] K,
      Algebra.trace ℚ_[p] K (x * r) ∈ (algebraMap ℤ_[p] ℚ_[p]).range) ↔
      ∃ z : integralClosure ℤ_[p] K, (z : K) * u⁻¹ = x := by
    intro x
    have h1 := coeIdeal_differentIdeal ℤ_[p] ℚ_[p] K (integralClosure ℤ_[p] K)
    rw [hn, FractionalIdeal.coeIdeal_span_singleton] at h1
    have h2 : FractionalIdeal.dual ℤ_[p] ℚ_[p]
        (1 : FractionalIdeal (nonZeroDivisors (integralClosure ℤ_[p] K)) K) =
        FractionalIdeal.spanSingleton _ u⁻¹ := by
      rw [← FractionalIdeal.spanSingleton_inv, h1, inv_inv]
    have hm := FractionalIdeal.mem_dual (A := ℤ_[p]) (K := ℚ_[p])
      (I := (1 : FractionalIdeal (nonZeroDivisors (integralClosure ℤ_[p] K)) K))
      one_ne_zero (x := x)
    rw [h2, FractionalIdeal.mem_spanSingleton] at hm
    simp only [Algebra.smul_def] at hm
    refine Iff.trans ?_ hm.symm
    constructor
    · intro h a ha
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      rw [Algebra.traceForm_apply]
      exact h r
    · intro h r
      exact h _ ((FractionalIdeal.mem_one_iff _).2 ⟨r, rfl⟩)
  -- the basis `u⁻¹ b`
  let f : K ≃ₗ[ℚ_[p]] K :=
    { toFun := fun x => u⁻¹ * x
      invFun := fun x => u * x
      map_add' := fun x y => mul_add _ x y
      map_smul' := fun c x => by rw [RingHom.id_apply, mul_smul_comm]
      left_inv := fun x => mul_inv_cancel_left₀ hu x
      right_inv := fun x => inv_mul_cancel_left₀ hu x }
  let c := b.map f
  have hcrepr : ∀ y i, c.repr y i = b.repr (u * y) i := fun y i => rfl
  have hlat : tOrdIdxLattice c = tOrdIdxLattice b.traceDual := by
    ext y
    rw [tOrdIdx_mem_lattice, tOrdIdx_mem_lattice]
    simp only [hcrepr, Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply]
    rw [← locDisc_mem_iff hb, ← locDisc_trace_mem_iff hb, hdual]
    constructor
    · intro h
      exact ⟨⟨u * y, h⟩, by
        change u * y * u⁻¹ = y
        rw [mul_comm u y, mul_assoc, mul_inv_cancel₀ hu, mul_one]⟩
    · rintro ⟨z, rfl⟩
      have : u * ((z : K) * u⁻¹) = z := by
        rw [mul_comm (z : K), ← mul_assoc, mul_inv_cancel₀ hu, one_mul]
      rw [this]
      exact z.2
  -- determinants
  have hdet1 : b.traceDual.det b = Algebra.discr ℚ_[p] b := by
    rw [Module.Basis.det_apply, Algebra.discr_def]
    congr 1
    ext i j
    rw [Module.Basis.toMatrix_apply, Module.Basis.traceDual_repr_apply,
      Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.traceForm_apply, mul_comm]
  have hdet2 : c.det b = Algebra.norm ℚ_[p] u := by
    rw [Module.Basis.det_map]
    have : (⇑f.symm ∘ ⇑b) = ⇑(Algebra.lmul ℚ_[p] K u) ∘ ⇑b := by
      funext i
      rfl
    rw [this, Module.Basis.det_comp, Module.Basis.det_self, mul_one, Algebra.norm_apply]
  have hunit : ‖b.traceDual.det c‖ = 1 := by
    have h := tOrdIdx_relIndex_eq c b.traceDual hlat.le
    rw [hlat, AddSubgroup.relIndex_self, Nat.cast_one] at h
    exact inv_eq_one.1 h.symm
  have hmain : ‖Algebra.discr ℚ_[p] b‖ = ‖Algebra.norm ℚ_[p] (ϖ : K)‖ ^ n := by
    rw [← hdet1, ← Module.Basis.det_mul_det b.traceDual c b, norm_mul, hunit, one_mul, hdet2,
      hu_def, map_pow, map_pow, norm_pow]
    rfl
  rw [hmain, ← pow_mul, mul_comm n, pow_mul, locDisc_norm_algNorm_uniformizer hpe, ← pow_mul]

/-- **`v_p(disc b) · e = d · n`**: the integer form of `locDisc_norm_discr_pow`, with
`v_p = Padic.valuation`. -/
theorem locDisc_valuation_discr_mul (P : Ideal (integralClosure ℤ_[p] K)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] (b : Module.Basis ι ℚ_[p] K)
    (hb : tOrdIdxIntegralBasis p b) :
    letI := isDedekindDomain_ringOfIntegers_padic p K
    letI := isTorsionFree_ringOfIntegers_padic p K
    (Algebra.discr ℚ_[p] b).valuation * (P.ramificationIdx ℤ_[p] : ℤ) =
      (Module.finrank ℚ_[p] K : ℤ) * differentExponent ℤ_[p] (integralClosure ℤ_[p] K) P := by
  let := isDedekindDomain_ringOfIntegers_padic p K
  let := isTorsionFree_ringOfIntegers_padic p K
  have h := locDisc_norm_discr_pow P b hb
  have hne := Algebra.discr_not_zero_of_basis ℚ_[p] b
  rw [Padic.norm_eq_zpow_neg_valuation hne, ← zpow_natCast, ← zpow_mul, inv_pow, ← zpow_natCast,
    ← zpow_neg] at h
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have h' := zpow_right_injective₀ (by linarith : (0 : ℝ) < p) hp1.ne' h
  push_cast at h'
  linarith

/-- **`v_p(disc b) = d · 𝔡`** (IUT IV, page 9: `𝔡` is the order, with `ord(p) = 1`, of a
generator of the different of `R` over `ℤ_p`): for a finite extension `K` of `ℚ_p` of degree
`d`, a prime `P` of `R = integralClosure ℤ_[p] K` over `p` and an integral basis `b`, the
`p`-adic valuation of the discriminant of `b` is `d · differentOrder ℤ_[p] R P`. -/
theorem locDisc_valuation_discr (P : Ideal (integralClosure ℤ_[p] K)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] (b : Module.Basis ι ℚ_[p] K)
    (hb : tOrdIdxIntegralBasis p b) :
    letI := isDedekindDomain_ringOfIntegers_padic p K
    letI := isTorsionFree_ringOfIntegers_padic p K
    ((Algebra.discr ℚ_[p] b).valuation : ℝ) =
      Module.finrank ℚ_[p] K * differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P := by
  let := isDedekindDomain_ringOfIntegers_padic p K
  let := isTorsionFree_ringOfIntegers_padic p K
  have h := locDisc_valuation_discr_mul P b hb
  have he : 0 < P.ramificationIdx ℤ_[p] :=
    ramificationIdx_pos_of_liesOver (IsDiscreteValuationRing.not_a_field ℤ_[p]) P
  have he' : (0 : ℝ) < P.ramificationIdx ℤ_[p] := by exact_mod_cast he
  unfold differentOrder
  have h' : ((Algebra.discr ℚ_[p] b).valuation : ℝ) * (P.ramificationIdx ℤ_[p] : ℝ) =
      (Module.finrank ℚ_[p] K : ℝ) *
        (differentExponent ℤ_[p] (integralClosure ℤ_[p] K) P : ℝ) := by
    exact_mod_cast h
  field_simp
  linarith

end Discriminant

/-! ## 2. The Galois case: the exact value and the allowance `𝔡 · log p` -/

section Galois

open MeasureTheory

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K] [Algebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]

/-- **The normalized log-volume of `R_E` for `K ⊗ K`, `K/ℚ_p` Galois, in terms of `𝔡`**: with
the normalization of IUT IV Proposition 1.4 (i) (page 13; `μ^log((R_E)^∼) = 0`, divided by the
dimension), `μ^log(R_E) = −(1/2) · 𝔡 · log p`, where `𝔡 = differentOrder ℤ_[p] R P` is the
order of the different of `R = integralClosure ℤ_[p] K` normalized by `ord(p) = 1`. -/
theorem locDisc_muLog_galois [IsGalois ℚ_[p] K]
    [MeasurableSpace (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K K)) → ℚ_[p])]
    [BorelSpace (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K K)) → ℚ_[p])]
    (μ : Measure (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K K)) → ℚ_[p]))
    [μ.IsAddHaarMeasure] (P : Ideal (integralClosure ℤ_[p] K)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    letI := isDedekindDomain_ringOfIntegers_padic p K
    letI := isTorsionFree_ringOfIntegers_padic p K
    padicPacketMuLog p (TensorProduct ℚ_[p] K K) μ (padicPacketNormalization p K K)
        (padicPacketIntegers p K K) =
      -(1 / 2) * (differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P * Real.log p) := by
  let := isDedekindDomain_ringOfIntegers_padic p K
  let := isTorsionFree_ringOfIntegers_padic p K
  obtain ⟨m, b, hb⟩ := tOrdIdx_exists_integralBasis (p := p) K
  rw [tOrdIdx_muLog_galois_valuation μ b hb, locDisc_valuation_discr P b hb]
  have hd : (0 : ℝ) < Module.finrank ℚ_[p] K := by exact_mod_cast Module.finrank_pos
  field_simp

/-- **The exact value against the allowance of Proposition 1.1** (`K ⊗ K`, `K/ℚ_p` Galois): the
inclusion `p ^ 𝔡 · (R_E)^∼ ⊆ R_E` of IUT IV Proposition 1.1 (page 9, two factors) corresponds,
under this normalization, to the allowance `μ^log(R_E) ≥ −𝔡 · log p`. The exact value satisfies
it, and its distance to `−𝔡 · log p` is `(1/2) · 𝔡 · log p`: `0 ≤ μ^log(R_E) + 𝔡 log p` and
`μ^log(R_E) + 𝔡 log p = (1/2) 𝔡 log p`. -/
theorem locDisc_muLog_galois_allowance [IsGalois ℚ_[p] K]
    [MeasurableSpace (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K K)) → ℚ_[p])]
    [BorelSpace (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K K)) → ℚ_[p])]
    (μ : Measure (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K K)) → ℚ_[p]))
    [μ.IsAddHaarMeasure] (P : Ideal (integralClosure ℤ_[p] K)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    letI := isDedekindDomain_ringOfIntegers_padic p K
    letI := isTorsionFree_ringOfIntegers_padic p K
    0 ≤ padicPacketMuLog p (TensorProduct ℚ_[p] K K) μ (padicPacketNormalization p K K)
          (padicPacketIntegers p K K) +
          differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P * Real.log p ∧
      padicPacketMuLog p (TensorProduct ℚ_[p] K K) μ (padicPacketNormalization p K K)
          (padicPacketIntegers p K K) +
          differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P * Real.log p =
        (1 / 2) * (differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P * Real.log p) := by
  let := isDedekindDomain_ringOfIntegers_padic p K
  let := isTorsionFree_ringOfIntegers_padic p K
  rw [locDisc_muLog_galois μ P]
  have h0 : 0 ≤ differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hl : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.out.one_lt)
  have := mul_nonneg h0 hl.le
  constructor
  · linarith
  · ring

end Galois

/-! ## 3. Two arbitrary factors: a basis of `(R_E)^∼` and the index formula -/

section General

variable {p : ℕ} [hp : Fact p.Prime] {K₁ K₂ : Type*} [Field K₁] [Field K₂] [Algebra ℚ_[p] K₁]
  [Algebra ℚ_[p] K₂] [FiniteDimensional ℚ_[p] K₁] [FiniteDimensional ℚ_[p] K₂]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
/-- **`(R_E)^∼` is a free `ℤ_p`-module of full rank**: for any finite extensions `K₁`, `K₂` of
`ℚ_p` (no Galois hypothesis) with integral bases `b`, `c`, there is a `ℚ_p`-basis `n` of
`K₁ ⊗[ℚ_p] K₂`, indexed like `b ⊗ c`, whose `ℤ_p`-span is the normalization `(R_E)^∼`
(`tensorIdxNormRing`). So the basis that `tOrdIdx_index_sq_general` takes as data exists. -/
theorem locDisc_exists_normBasis (b : Module.Basis ι ℚ_[p] K₁) (c : Module.Basis κ ℚ_[p] K₂)
    (hb : tOrdIdxIntegralBasis p b) (hc : tOrdIdxIntegralBasis p c) :
    ∃ n : Module.Basis (ι × κ) ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂),
      (tensorIdxNormRing p K₁ K₂).toAddSubgroup = tOrdIdxLattice n := by
  classical
  let : Module ℤ_[p] (TensorProduct ℚ_[p] K₁ K₂) :=
    Module.compHom _ (algebraMap ℤ_[p] ℚ_[p])
  have hsmul : ∀ (a : ℤ_[p]) (v : TensorProduct ℚ_[p] K₁ K₂),
      a • v = (algebraMap ℤ_[p] ℚ_[p] a) • v := fun a v => rfl
  have : IsScalarTower ℤ_[p] ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂) :=
    ⟨fun a q v => by rw [hsmul, ← mul_smul, ← Algebra.smul_def]⟩
  let M : Submodule ℤ_[p] (TensorProduct ℚ_[p] K₁ K₂) :=
    { carrier := tensorIdxNormRing p K₁ K₂
      add_mem' := add_mem
      zero_mem' := zero_mem _
      smul_mem' := fun a z hz => by
        rw [hsmul, Algebra.smul_def]
        exact mul_mem (tensorIdxRing_le p K₁ K₂ (tensorIdx_algebraMap_mem p K₁ K₂ a)) hz }
  let e := b.tensorProduct c
  let L : Submodule ℤ_[p] (TensorProduct ℚ_[p] K₁ K₂) := Submodule.span ℤ_[p] (Set.range e)
  have hRE : ∀ x, x ∈ tensorIdxRing p K₁ K₂ ↔ x ∈ tOrdIdxLattice e := by
    intro x
    rw [← Subring.mem_toAddSubgroup, tOrdIdx_ring_eq_lattice b c hb hc]
  have hlatL : ∀ x, x ∈ tOrdIdxLattice e → x ∈ L := by
    intro x hx
    rw [← e.sum_repr x]
    refine Submodule.sum_mem _ fun k _ => ?_
    have : e.repr x k • e k = (⟨e.repr x k, hx k⟩ : ℤ_[p]) • e k := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hLM : L ≤ M := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact tensorIdxRing_le p K₁ K₂ ((hRE _).2 (tOrdIdx_basis_mem e k))
  have hN : (tensorIdxRing p K₁ K₂).toAddSubgroup.relIndex
      (tensorIdxNormRing p K₁ K₂).toAddSubgroup ≠ 0 := tensorIdx_relIndex_ne_zero p K₁ K₂
  have hNq : (((tensorIdxRing p K₁ K₂).toAddSubgroup.relIndex
      (tensorIdxNormRing p K₁ K₂).toAddSubgroup : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hN
  let g : TensorProduct ℚ_[p] K₁ K₂ →ₗ[ℤ_[p]] TensorProduct ℚ_[p] K₁ K₂ :=
    LinearMap.restrictScalars ℤ_[p]
      (((tensorIdxRing p K₁ K₂).toAddSubgroup.relIndex
        (tensorIdxNormRing p K₁ K₂).toAddSubgroup : ℚ_[p])⁻¹ •
        (LinearMap.id : TensorProduct ℚ_[p] K₁ K₂ →ₗ[ℚ_[p]] TensorProduct ℚ_[p] K₁ K₂))
  have hMT : M ≤ L.map g := by
    intro z hz
    have h1 := AddSubgroup.nsmul_relIndex_mem (tensorIdxRing p K₁ K₂).toAddSubgroup
      (K := (tensorIdxNormRing p K₁ K₂).toAddSubgroup) hz
    have h2 := hlatL _ ((hRE _).1 h1)
    have h3 := Submodule.mem_map_of_mem (f := g) h2
    convert h3 using 1
    change z = (_ : ℚ_[p])⁻¹ • _
    rw [LinearMap.id_apply, ← Nat.cast_smul_eq_nsmul ℚ_[p], smul_smul, inv_mul_cancel₀ hNq,
      one_smul]
  have : Submodule.IsLattice ℚ_[p] (L.map g) :=
    Submodule.IsLattice.of_fg ℚ_[p] ((Submodule.fg_span (Set.finite_range e)).map g)
  have : Submodule.IsFullLattice ℚ_[p] L :=
    { toIsLattice := Submodule.IsLattice.of_fg ℚ_[p] (Submodule.fg_span (Set.finite_range e))
      span_eq_top := by rw [Submodule.span_span_of_tower]; exact e.span_eq }
  have : Submodule.IsLattice ℚ_[p] M := Submodule.IsLattice.mono ℚ_[p] hMT
  have : Submodule.IsFullLattice ℚ_[p] M := Submodule.IsFullLattice.of_le ℚ_[p] hLM
  have := Submodule.IsLattice.free ℚ_[p] M
  have := Submodule.IsLattice.finite ℚ_[p] M
  have hrk : Module.finrank ℤ_[p] M = Fintype.card (ι × κ) := by
    rw [Submodule.IsFullLattice.finrank_eq ℚ_[p] M, Module.finrank_eq_card_basis e]
  let B : Module.Basis (ι × κ) ℤ_[p] M :=
    (Module.finBasisOfFinrankEq ℤ_[p] M hrk).reindex (Fintype.equivFin _).symm
  let n := B.extendOfIsFullLattice ℚ_[p]
  have hn : ∀ k, n k = (B k : TensorProduct ℚ_[p] K₁ K₂) :=
    fun k => Module.Basis.extendOfIsFullLattice_apply ℚ_[p] B k
  refine ⟨n, ?_⟩
  ext z
  rw [Subring.mem_toAddSubgroup, tOrdIdx_mem_lattice]
  constructor
  · intro hz k
    have hsum : z = n.equivFun.symm (fun k => algebraMap ℤ_[p] ℚ_[p] (B.repr ⟨z, hz⟩ k)) := by
      rw [Module.Basis.equivFun_symm_apply]
      have h := congrArg (fun y : M => (y : TensorProduct ℚ_[p] K₁ K₂)) (B.sum_repr ⟨z, hz⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h
      conv_lhs => rw [← h]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hn, hsmul]
    have hk : n.repr z k = algebraMap ℤ_[p] ℚ_[p] (B.repr ⟨z, hz⟩ k) := by
      rw [← Module.Basis.equivFun_apply]
      conv_lhs => rw [hsum]
      rw [LinearEquiv.apply_symm_apply]
    rw [hk, PadicInt.algebraMap_apply, ← PadicInt.norm_def]
    exact PadicInt.norm_le_one _
  · intro h
    change z ∈ M
    rw [← n.sum_repr z]
    refine Submodule.sum_mem _ fun k _ => ?_
    have : n.repr z k • n k =
        (⟨n.repr z k, h k⟩ : ℤ_[p]) • (B k : TensorProduct ℚ_[p] K₁ K₂) := by
      rw [hn]
      rfl
    rw [this]
    exact M.smul_mem _ (B k).2

/-- **The index formula in valuations, any two factors**: for integral bases `b`, `c` of
`K₁`, `K₂` (degrees `d₁ = |ι|`, `d₂ = |κ|`) and any basis `n` whose `ℤ_p`-span is `(R_E)^∼`,
`2 v_p([(R_E)^∼ : R_E]) = d₂ v_p(disc b) + d₁ v_p(disc c) − v_p(disc n)`. -/
theorem locDisc_index_valuation (b : Module.Basis ι ℚ_[p] K₁) (c : Module.Basis κ ℚ_[p] K₂)
    (hb : tOrdIdxIntegralBasis p b) (hc : tOrdIdxIntegralBasis p c)
    (n : Module.Basis (ι × κ) ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂))
    (hn : (tensorIdxNormRing p K₁ K₂).toAddSubgroup = tOrdIdxLattice n) :
    2 * (multiplicity p ((tensorIdxRing p K₁ K₂).toAddSubgroup.relIndex
        (tensorIdxNormRing p K₁ K₂).toAddSubgroup) : ℤ) =
      Fintype.card κ * (Algebra.discr ℚ_[p] b).valuation +
        Fintype.card ι * (Algebra.discr ℚ_[p] c).valuation -
          (Algebra.discr ℚ_[p] n).valuation := by
  have h := tOrdIdx_index_sq_general b c hb hc n hn
  set I := (tensorIdxRing p K₁ K₂).toAddSubgroup.relIndex
    (tensorIdxNormRing p K₁ K₂).toAddSubgroup with hI
  have hI0 : I ≠ 0 := tensorIdx_relIndex_ne_zero p K₁ K₂
  set E : ℤ := Fintype.card κ * (Algebra.discr ℚ_[p] b).valuation +
    Fintype.card ι * (Algebra.discr ℚ_[p] c).valuation - (Algebra.discr ℚ_[p] n).valuation
    with hE
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  rw [Padic.norm_eq_zpow_neg_valuation (Algebra.discr_not_zero_of_basis ℚ_[p] b),
    Padic.norm_eq_zpow_neg_valuation (Algebra.discr_not_zero_of_basis ℚ_[p] c)] at h
  have hn0 : Algebra.discr ℚ_[p] n ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h
    have : (0 : ℝ) < (I : ℝ) ^ 2 * (((p : ℝ) ^ (-(Algebra.discr ℚ_[p] b).valuation)) ^
        Fintype.card κ * ((p : ℝ) ^ (-(Algebra.discr ℚ_[p] c).valuation)) ^ Fintype.card ι) :=
      mul_pos (pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hI0)) 2)
        (mul_pos (pow_pos (zpow_pos hp0 _) _) (pow_pos (zpow_pos hp0 _) _))
    linarith
  have e1 : ((p : ℝ) ^ (-(Algebra.discr ℚ_[p] b).valuation)) ^ Fintype.card κ =
      (p : ℝ) ^ (-(Algebra.discr ℚ_[p] b).valuation * (Fintype.card κ : ℤ)) := by
    rw [zpow_mul, zpow_natCast]
  have e2 : ((p : ℝ) ^ (-(Algebra.discr ℚ_[p] c).valuation)) ^ Fintype.card ι =
      (p : ℝ) ^ (-(Algebra.discr ℚ_[p] c).valuation * (Fintype.card ι : ℤ)) := by
    rw [zpow_mul, zpow_natCast]
  rw [Padic.norm_eq_zpow_neg_valuation hn0, e1, e2, ← zpow_add₀ hp0.ne'] at h
  have hI2 : (I : ℝ) ^ 2 = (p : ℝ) ^ E := by
    have hpos : (0 : ℝ) < (p : ℝ) ^ (-(Algebra.discr ℚ_[p] b).valuation * (Fintype.card κ : ℤ) +
        -(Algebra.discr ℚ_[p] c).valuation * (Fintype.card ι : ℤ)) := zpow_pos hp0 _
    have h' : (I : ℝ) ^ 2 = (p : ℝ) ^ (-(Algebra.discr ℚ_[p] n).valuation) *
        ((p : ℝ) ^ (-(Algebra.discr ℚ_[p] b).valuation * (Fintype.card κ : ℤ) +
          -(Algebra.discr ℚ_[p] c).valuation * (Fintype.card ι : ℤ)))⁻¹ := by
      rw [← h, mul_inv_cancel_right₀ hpos.ne']
    rw [h', ← zpow_neg, ← zpow_add₀ hp0.ne', hE]
    congr 1
    ring
  have hE0 : 0 ≤ E := by
    have h1 : (1 : ℝ) ≤ (I : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ I := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hI0
      nlinarith
    rw [hI2] at h1
    exact (one_le_zpow_iff_right₀ hp1).1 h1
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hE0
  rw [hm, zpow_natCast] at hI2
  have hnat : I ^ 2 = p ^ m := by exact_mod_cast hI2
  have hv := congrArg (multiplicity p) hnat
  rw [Nat.multiplicity_pow, Nat.multiplicity_prime_pow] at hv
  rw [hm, ← hv]
  push_cast
  ring

/-- **The index formula with the basis of `(R_E)^∼` supplied**: for any finite extensions
`K₁`, `K₂` of `ℚ_p` with integral bases `b`, `c` there is a basis `n` of
`(R_E)^∼` (as in `locDisc_exists_normBasis`) with
`[(R_E)^∼ : R_E]² · ‖disc b‖^{d₂} · ‖disc c‖^{d₁} = ‖disc n‖` and
`2 v_p([(R_E)^∼ : R_E]) = d₂ v_p(disc b) + d₁ v_p(disc c) − v_p(disc n)`. -/
theorem locDisc_index_general (b : Module.Basis ι ℚ_[p] K₁) (c : Module.Basis κ ℚ_[p] K₂)
    (hb : tOrdIdxIntegralBasis p b) (hc : tOrdIdxIntegralBasis p c) :
    ∃ n : Module.Basis (ι × κ) ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂),
      (tensorIdxNormRing p K₁ K₂).toAddSubgroup = tOrdIdxLattice n ∧
      ((tensorIdxRing p K₁ K₂).toAddSubgroup.relIndex (tensorIdxNormRing p K₁ K₂).toAddSubgroup :
          ℝ) ^ 2 * (‖Algebra.discr ℚ_[p] b‖ ^ Fintype.card κ *
            ‖Algebra.discr ℚ_[p] c‖ ^ Fintype.card ι) = ‖Algebra.discr ℚ_[p] n‖ ∧
      2 * (multiplicity p ((tensorIdxRing p K₁ K₂).toAddSubgroup.relIndex
          (tensorIdxNormRing p K₁ K₂).toAddSubgroup) : ℤ) =
        Fintype.card κ * (Algebra.discr ℚ_[p] b).valuation +
          Fintype.card ι * (Algebra.discr ℚ_[p] c).valuation -
            (Algebra.discr ℚ_[p] n).valuation := by
  obtain ⟨n, hn⟩ := locDisc_exists_normBasis b c hb hc
  exact ⟨n, hn, tOrdIdx_index_sq_general b c hb hc n hn, locDisc_index_valuation b c hb hc n hn⟩

end General

end IUT.PaperIV.LocalFields
