import IUT.PaperIV.LocalFields.TensorDifferent
import IUT.PaperIV.LocalFields.Packets

/-!
# Proposition 1.1 of IUT IV for any finite number of factors

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Proposition 1.1 (page 9) with its
proof (pages 9 and 10). Pages read for this file: 9 and 10. Pages checked against rendered images:
9 and 10. Displays relied on:
* page 9: `I` finite of cardinality `≥ 2`; `k_i` finite extensions of `ℚ_p`, `R_i = 𝒪_{k_i}`,
  `𝔡_i ∈ ℚ_{≥0}` "the order [i.e., `ord(−)`] of any generator of the different ideal of `R_i`
  over `ℤ_p`", with `ord(p) = 1`; for nonempty `E ⊆ I`, `R_E = ⊗_{i ∈ E} R_i` over `ℤ_p` and
  `𝔡_E = ∑_{i ∈ E} 𝔡_i`; a fixed `* ∈ I`, `I* = I \ {*}`; the display
  `p ^ (𝔡_{I*}) · (R_I)^∼ ⊆ R_I ⊆ (R_I)^∼`, with `(−)^∼` "the normalization of the [reduced]
  ring in parentheses in its ring of fractions", and the remark that the left-hand side "is
  well-defined for suitable `p ^ (𝔡_{I*})` [such as products of elements `p ^ (𝔡_i) ∈ R_i`, for
  `i ∈ I*`] and independent of the choice of such suitable `p ^ (𝔡_{I*})`". The exponent is
  `𝔡_{I*}`: no ceiling, and no contribution of the different of `R_*`;
* page 10: the proof ends by induction on the cardinality of `I`, reducing to two factors, where
  the inclusion "follows immediately from the definition of the different ideal".

## The objects

`K : ι → Type` is a finite family of finite extensions of `ℚ_[p]` with compatible `ℤ_p`-algebra
structures, `R_i = integralClosure ℤ_[p] (K i)`, and the packet is `PiTensorProduct ℚ_[p] K`, as
in `IUT.PaperIV.LocalFields.Packets`. `R_I` is `tdManyIntegers`, the additive span of the pure
tensors `⊗_i x_i` with every `x_i` integral over `ℤ_p` (the image of `⊗_{i ∈ I} R_i` in the
packet over `ℚ_p`; the analogue of the two-factor `padicPacketIntegers`). `(R_I)^∼` is
`packetNormalizationSet`, the elements of the packet integral over `ℤ_p`. The page's `*` is an
index `s : ι`. The page's `p ^ (𝔡_{I*})` is taken in the form the page suggests: a pure tensor
`⊗_i δ_i` with `δ_s = 1` and, for `i ≠ s`, `δ_i ∈ K_i` an element of order `𝔡_i` (spectral norm
`p ^ (−𝔡_i)`, with `𝔡_i = differentOrder` at a prime `P_i` of `R_i` over `p`, normalized by
`ord(p) = 1`), or more generally an element of the different ideal of `R_i`.

## The proof

The route of pages 9 and 10 (base change to the ring of integers of `ℚ̄_p`, faithful flatness,
induction on `|I|`) is not followed. The proof is direct, through trace duals, and keeps the
coordinates in the field `K_s`: the packet is identified with `K_s ⊗ (⊗_{i ≠ s} K_i)`
(`tdMany_splitMap_bijective`); this is free over `K_s` with basis `1 ⊗ (⊗_{i ≠ s} b_i^∨)`, where
`b_i` is a `ℤ_p`-basis of `R_i` and `b_i^∨` its dual basis for the trace form; the coordinate of
`z` on `1 ⊗ (⊗_i b_i^∨(j_i))` is the trace over `K_s` of `z · (1 ⊗ (⊗_i b_i(j_i)))`, integral
when `z` is (`tensorDiff_isIntegralElem_trace`, which needs a field as base); and `δ_i b_i^∨` is
integral by the definition of the different. Using `K_s` as the base is what removes `𝔡_s` from
the exponent: coordinates over `ℚ_p` would only give `p ^ (𝔡_I) · (R_I)^∼ ⊆ R_I`.

## What is proved

* `tdMany_trace_tprod`: `Tr(⊗_i x_i) = ∏_i Tr(x_i)` for finite-dimensional algebras over a field.
* `tdMany_tprod_integral`: a pure tensor of integral elements is integral.
* `tdMany_exists_integralBasis`: a `ℤ_p`-basis `b` of `R_i` (as a `ℚ_p`-basis of `K_i`) with
  `δ · b_j^∨` integral for every `δ` in the different.
* `tdMany_order_mem_different`: an element of order `𝔡_i` lies in the different ideal.
* `tdMany_split_mul_mem`, `tdMany_splitIntegers_integral`: the two inclusions in the split form
  `K_s ⊗ (⊗_{i ≠ s} K_i)`.
* `tdManySplitMap`, `tdMany_splitMap_bijective`: the `ℚ_p`-algebra isomorphism
  `K_s ⊗ (⊗_{i ≠ s} K_i) ≅ ⊗_i K_i` (surjective, and both sides have dimension
  `∏_i [K_i : ℚ_p]`).
* `tdMany_mul_mem_integers` (elements of the differents), `tdMany_order_mul_mem_integers`
  (elements of order `𝔡_i`): `p ^ (𝔡_{I*}) · (R_I)^∼ ⊆ R_I` for any finite `I`.
* `tdMany_integers_subset`: `R_I ⊆ (R_I)^∼`.
* `tdMany_choice_independent`: `(⊗_i δ_i) · (R_I)^∼` does not depend on the choice of the
  elements `δ_i` of order `𝔡_i`.
* `tdMany_proposition1_1`: the three together, with the page's hypothesis `|I| ≥ 2` (not used).

## Not proved

* That `(R_I)^∼` (the integral closure of `ℤ_p` in the packet) is the normalization of `R_I` in
  its ring of fractions, and that `⊗_{i ∈ I} R_i → ⊗_{i ∈ I} K_i` is injective, here; both are
  proved in `IUT.PaperIV.LocalFields.PacketIdentifications` (`packetId_isLocalization`,
  `packetId_isIntegralElem_iff`, `packetId_map_injective`), with the inclusions on the tensor
  product over `ℤ_p` (`packetId_proposition1_1`).
* The fields `k_i` are abstract finite extensions of `ℚ_p`, not subfields of a fixed `ℚ̄_p`;
  "suitable `p ^ (𝔡_{I*})`" beyond products `⊗_i δ_i` is not formalized here; every element of
  order `𝔡_{I*}` in each field component is treated in
  `IUT.PaperIV.LocalFields.PacketSuitable` (`psuit_proposition1_1`).
* That the statements here, for a two-element index type, specialize to the two-factor theorems
  of `IUT.PaperIV.LocalFields.TensorDifferent` (stated on the binary `TensorProduct`): the
  identification of `PiTensorProduct` over two indices with `TensorProduct` is not made.
* That an element of order `𝔡_i` exists in `K_i` (needed for the order form to apply), here; it
  is `IUT.PaperIV.LocalFields.packetId_exists_generator_order`. The
  ideal form `tdMany_mul_mem_integers` applies to any element of the different, for instance a
  generator.
-/

namespace IUT.PaperIV.LocalFields

open IUT.Prerequisites.PadicVolume

/-! ## The trace of a pure tensor -/

section TraceTprod

/-- **The trace of a pure tensor in a finite tensor product of algebras**: over a field `F`, for
finite-dimensional commutative `F`-algebras `A_i`, the trace of `⊗_i x_i` in `⊗_i A_i` is
`∏_i Tr_{A_i/F}(x_i)`. -/
theorem tdMany_trace_tprod {F : Type*} [Field F] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : κ → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)]
    [∀ i, FiniteDimensional F (A i)] (x : ∀ i, A i) :
    Algebra.trace F (PiTensorProduct F A) (PiTensorProduct.tprod F x) =
      ∏ i, Algebra.trace F (A i) (x i) := by
  classical
  set b := fun i => Module.finBasis F (A i)
  rw [Algebra.trace_apply, LinearMap.trace_eq_matrix_trace F (Basis.piTensorProduct b)]
  have hi : ∀ i, Algebra.trace F (A i) (x i) =
      ∑ k, (b i).repr (x i * b i k) k := by
    intro i
    rw [Algebra.trace_apply, LinearMap.trace_eq_matrix_trace F (b i)]
    simp [Matrix.trace, LinearMap.toMatrix_apply]
  simp only [hi]
  rw [Fintype.prod_sum]
  simp [Matrix.trace, LinearMap.toMatrix_apply, Basis.piTensorProduct_apply]

end TraceTprod

/-! ## Integrality of pure tensors -/

section Integral

variable (p : ℕ) [hp : Fact p.Prime]

/-- A pure tensor `⊗_i x_i` of elements integral over `ℤ_p` is integral over `ℤ_p`. -/
theorem tdMany_tprod_integral {κ : Type*} [Fintype κ] (A : κ → Type*) [∀ i, CommRing (A i)]
    [∀ i, Algebra ℚ_[p] (A i)] {x : ∀ i, A i} (hx : ∀ i, padicVolIntegral p (x i)) :
    padicVolIntegral p (PiTensorProduct.tprod ℚ_[p] x) := by
  classical
  have h : PiTensorProduct.tprod ℚ_[p] x =
      ∏ i, PiTensorProduct.singleAlgHom (R := ℚ_[p]) (A := A) i (x i) := by
    have h0 := map_prod (PiTensorProduct.tprodMonoidHom ℚ_[p] (A := A))
      (fun i => Pi.mulSingle i (x i)) Finset.univ
    rw [Finset.univ_prod_mulSingle] at h0
    exact h0
  rw [h]
  refine Finset.prod_induction _ (fun w => padicVolIntegral p w) (fun a b ha hb => ?_) ?_ ?_
  · exact RingHom.IsIntegralElem.mul _ ha hb
  · show RingHom.IsIntegralElem _ 1
    exact RingHom.isIntegralElem_one _
  · intro i _
    exact padicVolIntegral_map p _ (hx i)

end Integral

/-! ## An integral basis with its trace dual, one factor -/

section OneFactor

variable (p : ℕ) [hp : Fact p.Prime]

/-- **An integral basis and the different**: a finite extension `K` of `ℚ_p` has a `ℚ_p`-basis
`b` of elements integral over `ℤ_p` (a `ℤ_p`-basis of `R = integralClosure ℤ_[p] K`) such that
for every `δ` in the different ideal of `R` over `ℤ_p`, every `δ · b_j^∨` is integral, where
`b^∨` is the dual basis for the trace form. This is the step "from the definition of the different
ideal" of page 10. -/
theorem tdMany_exists_integralBasis (K : Type) [Field K] [Algebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℚ_[p] K), (∀ j, padicVolIntegral p (b j)) ∧
      ∀ δ : integralClosure ℤ_[p] K,
        (letI := isDedekindDomain_ringOfIntegers_padic p K;
          letI := isTorsionFree_ringOfIntegers_padic p K;
          δ ∈ differentIdeal ℤ_[p] (integralClosure ℤ_[p] K)) →
        ∀ j, padicVolIntegral p ((δ : K) * b.traceDual j) := by
  classical
  let := isDedekindDomain_ringOfIntegers_padic p K
  let := isTorsionFree_ringOfIntegers_padic p K
  have : IsFractionRing (integralClosure ℤ_[p] K) K :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[p] ℚ_[p] K _
  have : Module.Finite ℤ_[p] (integralClosure ℤ_[p] K) :=
    IsIntegralClosure.finite ℤ_[p] ℚ_[p] K _
  have : Module.Free ℤ_[p] (integralClosure ℤ_[p] K) := Module.free_of_finite_type_torsion_free'
  have : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure ℤ_[p] K)
      (nonZeroDivisors ℤ_[p])) K :=
    IsIntegralClosure.isLocalization ℤ_[p] ℚ_[p] K _
  set b₀ := Module.Free.chooseBasis ℤ_[p] (integralClosure ℤ_[p] K)
  set b := (b₀.localizationLocalization ℚ_[p] (nonZeroDivisors ℤ_[p]) K).reindex
    (Fintype.equivFin _)
  have hbint : ∀ j, padicVolIntegral p (b j) := by
    intro j
    rw [tensorDiff_padicVolIntegral_iff, Module.Basis.reindex_apply,
      Module.Basis.localizationLocalization_apply]
    exact (b₀ _).2
  have hspan : (1 : Submodule (integralClosure ℤ_[p] K) K).restrictScalars ℤ_[p] =
      Submodule.span ℤ_[p] (Set.range b) := by
    rw [Module.Basis.range_reindex, Module.Basis.localizationLocalization_span]
    ext x
    simp
  refine ⟨_, b, hbint, fun δ hδ j => ?_⟩
  have hmem : b.traceDual j ∈
      Submodule.traceDual ℤ_[p] ℚ_[p] (1 : Submodule (integralClosure ℤ_[p] K) K) := by
    have h := Submodule.traceDual_span_of_basis ℤ_[p]
      (1 : Submodule (integralClosure ℤ_[p] K) K) b hspan
    have h' : b.traceDual j ∈ Submodule.span ℤ_[p] (Set.range b.traceDual) :=
      Submodule.subset_span ⟨j, rfl⟩
    rw [← h] at h'
    exact h'
  have hδ' : (δ : K) ∈ IsLocalization.coeSubmodule K
      (differentIdeal ℤ_[p] (integralClosure ℤ_[p] K)) :=
    (IsLocalization.mem_coeSubmodule K _).2 ⟨δ, hδ, rfl⟩
  rw [coeSubmodule_differentIdeal ℤ_[p] ℚ_[p] (integralClosure ℤ_[p] K),
    Submodule.mem_div_iff_forall_mul_mem] at hδ'
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hδ' _ hmem)
  rw [tensorDiff_padicVolIntegral_iff, ← hr]
  exact r.2

/-- **An element of order `𝔡` lies in the different** (page 9: `p ^ (𝔡_i)` is an element of
`K_i` of order `𝔡_i`, the order of a generator of the different): for a prime `P` of
`R = integralClosure ℤ_[p] K` over `p` and `y ∈ K` with spectral norm `p ^ (−𝔡)`,
`𝔡 = differentOrder` at `P`, `y` lies in `R` and in its different ideal. -/
theorem tdMany_order_mem_different (K : Type) [Field K] [Algebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]
    (P : Ideal (integralClosure ℤ_[p] K)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] {y : K}
    (hy : letI := isDedekindDomain_ringOfIntegers_padic p K;
      letI := isTorsionFree_ringOfIntegers_padic p K;
      letI := spectralNorm.normedField ℚ_[p] K;
      ‖y‖ = (p : ℝ) ^ (-differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P)) :
    ∃ d : integralClosure ℤ_[p] K,
      (letI := isDedekindDomain_ringOfIntegers_padic p K;
        letI := isTorsionFree_ringOfIntegers_padic p K;
        d ∈ differentIdeal ℤ_[p] (integralClosure ℤ_[p] K)) ∧ (d : K) = y := by
  let := isDedekindDomain_ringOfIntegers_padic p K
  let := isTorsionFree_ringOfIntegers_padic p K
  let := spectralNorm.normedField ℚ_[p] K
  have := padicBridge_isLocalRing p K
  have := padicBridge_isDiscreteValuationRing p K
  have hy' : ‖y‖ = (p : ℝ) ^ (-((differentExponent ℤ_[p] (integralClosure ℤ_[p] K) P : ℝ) /
      (P.ramificationIdx ℤ_[p] : ℝ))) := hy
  obtain ⟨ϖ, hirr, hPϖ, -, hpos, -, hpe, -, -⟩ := padicBridge_uniformizer p K P
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
  have he : P.ramificationIdx ℤ_[p] ≠ 0 :=
    (ramificationIdx_pos_of_liesOver (IsDiscreteValuationRing.not_a_field ℤ_[p]) P).ne'
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hr := padicBridge_rpow_of_pow_eq p hpos.le he hpe
  have hyn : ‖y‖ = ‖(ϖ : K)‖ ^ n := by
    rw [hy', hexp, hr, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    congr 1
    ring
  have hint : IsIntegral ℤ_[p] (y / (ϖ : K) ^ n) := by
    refine (padicBridge_norm_le_one_iff_isIntegral p K _).1 ?_
    rw [norm_div, norm_pow, hyn, div_self (pow_ne_zero _ hpos.ne')]
  set u : integralClosure ℤ_[p] K := ⟨y / (ϖ : K) ^ n, hint⟩
  refine ⟨ϖ ^ n * u, ?_, ?_⟩
  · show ϖ ^ n * u ∈ differentIdeal ℤ_[p] (integralClosure ℤ_[p] K)
    rw [hn]
    exact Ideal.mul_mem_right u _ (Ideal.mem_span_singleton_self _)
  · rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
    exact mul_div_cancel₀ y (pow_ne_zero n (norm_pos_iff.mp hpos))

end OneFactor

/-! ## The inclusion with one factor singled out -/

section Split

variable (p : ℕ) [hp : Fact p.Prime] {κ : Type} [Fintype κ] [DecidableEq κ] (L : κ → Type)
  [∀ i, Field (L i)] [∀ i, Algebra ℚ_[p] (L i)] [∀ i, FiniteDimensional ℚ_[p] (L i)]
  [∀ i, Algebra ℤ_[p] (L i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (L i)]
  (K₀ : Type) [Field K₀] [Algebra ℚ_[p] K₀]

/-- `R_I` in the split form `K_* ⊗ (⊗_{i ∈ I*} K_i)`: the additive span of the elements
`x ⊗ (⊗_i y_i)` with `x` and every `y_i` integral over `ℤ_p`. -/
noncomputable def tdManySplitIntegers :
    Set (TensorProduct ℚ_[p] K₀ (PiTensorProduct ℚ_[p] L)) :=
  ((AddSubmonoid.closure {w | ∃ (x : K₀) (y : ∀ i, L i), padicVolIntegral p x ∧
      (∀ i, padicVolIntegral p (y i)) ∧
      w = TensorProduct.tmul ℚ_[p] x (PiTensorProduct.tprod ℚ_[p] y)} :
    AddSubmonoid (TensorProduct ℚ_[p] K₀ (PiTensorProduct ℚ_[p] L))) : Set _)

/-- **IUT IV Proposition 1.1 in the split form** (page 9): with `K₀ = K_*` and the family
`L = (K_i)_{i ∈ I*}`, for `δ_i` in the different ideal of `R_i` over `ℤ_p` (`i ∈ I*`) and `z`
in `K_* ⊗ (⊗_{i ∈ I*} K_i)` integral over `ℤ_p`, `(1 ⊗ (⊗_i δ_i)) · z` lies in `R_I`. The
coordinates of `z` are taken in `K_*`, over which `K_* ⊗ (⊗_{i ∈ I*} K_i)` is free with basis
`1 ⊗ (⊗_i b_i^∨)`; they are traces over the field `K_*`, hence integral, and `δ_i b_i^∨` is
integral by the definition of the different. No factor `δ_*` is used. -/
theorem tdMany_split_mul_mem (δ : ∀ i, L i)
    (hδ : ∀ i, ∃ d : integralClosure ℤ_[p] (L i),
      (letI := isDedekindDomain_ringOfIntegers_padic p (L i);
        letI := isTorsionFree_ringOfIntegers_padic p (L i);
        d ∈ differentIdeal ℤ_[p] (integralClosure ℤ_[p] (L i))) ∧ (d : L i) = δ i)
    {z : TensorProduct ℚ_[p] K₀ (PiTensorProduct ℚ_[p] L)} (hz : padicVolIntegral p z) :
    TensorProduct.tmul ℚ_[p] (1 : K₀) (PiTensorProduct.tprod ℚ_[p] δ) * z ∈
      tdManySplitIntegers p L K₀ := by
  classical
  have hb := fun i => tdMany_exists_integralBasis p (L i)
  choose n b hbint hdual using hb
  have hd : ∀ i j, padicVolIntegral p (δ i * (b i).traceDual j) := by
    intro i j
    obtain ⟨d, hdmem, hdδ⟩ := hδ i
    rw [← hdδ]
    exact hdual i d hdmem j
  set B := Basis.piTensorProduct b
  set B' := Basis.piTensorProduct (fun i => (b i).traceDual)
  set D := Algebra.TensorProduct.basis K₀ B'
  have hD : ∀ q, D q = TensorProduct.tmul ℚ_[p] (1 : K₀) (B' q) := fun q =>
    Algebra.TensorProduct.basis_apply _ q
  have hpair : ∀ q r, Algebra.trace ℚ_[p] (PiTensorProduct ℚ_[p] L) (B' q * B r) =
      if r = q then 1 else 0 := by
    intro q r
    rw [Basis.piTensorProduct_apply, Basis.piTensorProduct_apply,
      PiTensorProduct.tprod_mul_tprod, tdMany_trace_tprod]
    simp only [Pi.mul_apply, Module.Basis.trace_traceDual_mul]
    rw [Fintype.prod_ite_zero]
    simp [← funext_iff]
  have hc : ∀ r, Algebra.trace K₀ (TensorProduct ℚ_[p] K₀ (PiTensorProduct ℚ_[p] L))
      (z * TensorProduct.tmul ℚ_[p] (1 : K₀) (B r)) = D.repr z r := by
    intro r
    conv_lhs => rw [← D.sum_repr z]
    simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, hD,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, tensorDiff_trace_one_tmul, hpair,
      smul_eq_mul]
    simp
  have hφ : (algebraMap K₀ (TensorProduct ℚ_[p] K₀ (PiTensorProduct ℚ_[p] L))).comp
      ((algebraMap ℚ_[p] K₀).comp (algebraMap ℤ_[p] ℚ_[p])) =
      (algebraMap ℚ_[p] (TensorProduct ℚ_[p] K₀ (PiTensorProduct ℚ_[p] L))).comp
        (algebraMap ℤ_[p] ℚ_[p]) := by
    rw [IsScalarTower.algebraMap_eq ℚ_[p] K₀
      (TensorProduct ℚ_[p] K₀ (PiTensorProduct ℚ_[p] L))]
    rfl
  have hcint : ∀ r, padicVolIntegral p (D.repr z r) := by
    intro r
    rw [← hc r]
    have hBr : padicVolIntegral p (B r) := by
      rw [Basis.piTensorProduct_apply]
      exact tdMany_tprod_integral p L fun i => hbint i (r i)
    have hb' := padicVolIntegral_map p
      (Algebra.TensorProduct.includeRight :
        PiTensorProduct ℚ_[p] L →ₐ[ℚ_[p]] TensorProduct ℚ_[p] K₀ (PiTensorProduct ℚ_[p] L)) hBr
    rw [Algebra.TensorProduct.includeRight_apply] at hb'
    refine tensorDiff_isIntegralElem_trace ((algebraMap ℚ_[p] K₀).comp (algebraMap ℤ_[p] ℚ_[p]))
      ?_
    rw [hφ]
    exact RingHom.IsIntegralElem.mul _ hz hb'
  unfold tdManySplitIntegers
  rw [SetLike.mem_coe, ← D.sum_repr z, Finset.mul_sum]
  refine sum_mem fun r _ => AddSubmonoid.subset_closure
    ⟨D.repr z r, fun i => δ i * (b i).traceDual (r i), hcint r, fun i => hd i (r i), ?_⟩
  rw [hD, mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Basis.piTensorProduct_apply,
    PiTensorProduct.tprod_mul_tprod, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

omit [DecidableEq κ] [∀ i, FiniteDimensional ℚ_[p] (L i)] [∀ i, Algebra ℤ_[p] (L i)]
  [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (L i)] in
/-- `R_I ⊆ (R_I)^∼` in the split form: every element of `tdManySplitIntegers` is integral over
`ℤ_p`. -/
theorem tdMany_splitIntegers_integral {w : TensorProduct ℚ_[p] K₀ (PiTensorProduct ℚ_[p] L)}
    (hw : w ∈ tdManySplitIntegers p L K₀) : padicVolIntegral p w := by
  set φ := (algebraMap ℚ_[p] (TensorProduct ℚ_[p] K₀ (PiTensorProduct ℚ_[p] L))).comp
    (algebraMap ℤ_[p] ℚ_[p])
  let M : AddSubmonoid (TensorProduct ℚ_[p] K₀ (PiTensorProduct ℚ_[p] L)) :=
    { carrier := {z | φ.IsIntegralElem z}
      add_mem' := fun ha hb => RingHom.IsIntegralElem.add φ ha hb
      zero_mem' := RingHom.isIntegralElem_zero φ }
  have hgen : {w | ∃ (x : K₀) (y : ∀ i, L i), padicVolIntegral p x ∧
      (∀ i, padicVolIntegral p (y i)) ∧
      w = TensorProduct.tmul ℚ_[p] x (PiTensorProduct.tprod ℚ_[p] y)} ⊆
      (M : Set (TensorProduct ℚ_[p] K₀ (PiTensorProduct ℚ_[p] L))) := by
    rintro _ ⟨x, y, hx, hy, rfl⟩
    have hxy : TensorProduct.tmul ℚ_[p] x (PiTensorProduct.tprod ℚ_[p] y) =
        Algebra.TensorProduct.includeLeft (S := ℚ_[p]) x *
          Algebra.TensorProduct.includeRight (PiTensorProduct.tprod ℚ_[p] y) := by
      simp
    show φ.IsIntegralElem _
    rw [hxy]
    exact RingHom.IsIntegralElem.mul φ (padicVolIntegral_map p _ hx)
      (padicVolIntegral_map p _ (tdMany_tprod_integral p L hy))
  exact (AddSubmonoid.closure_le.mpr hgen) hw

end Split

/-! ## The packet `⊗_{i ∈ I} K_i` and the inclusion as printed -/

section Packet

variable (p : ℕ) [hp : Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] (K : ι → Type)
  [∀ i, Field (K i)] [∀ i, Algebra ℚ_[p] (K i)] [∀ i, FiniteDimensional ℚ_[p] (K i)]
  [∀ i, Algebra ℤ_[p] (K i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (K i)]

/-- `R_I = ⊗_{i ∈ I} R_i` inside the packet `⊗_{i ∈ I} K_i` over `ℚ_p`: the additive span of the
pure tensors `⊗_i x_i` with every `x_i` integral over `ℤ_p`; the analogue, for a
`PiTensorProduct`, of the two-factor `padicPacketIntegers`. -/
noncomputable def tdManyIntegers : Set (PiTensorProduct ℚ_[p] K) :=
  ((AddSubmonoid.closure {w | ∃ x : ∀ i, K i, (∀ i, padicVolIntegral p (x i)) ∧
      w = PiTensorProduct.tprod ℚ_[p] x} : AddSubmonoid (PiTensorProduct ℚ_[p] K)) : Set _)

omit [DecidableEq ι] [∀ i, FiniteDimensional ℚ_[p] (K i)] [∀ i, Algebra ℤ_[p] (K i)]
  [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (K i)] in
/-- **`R_I ⊆ (R_I)^∼`** (page 9, the second inclusion of the display; "immediate from the
definitions", page 9): every element of `tdManyIntegers` is integral over `ℤ_p`. -/
theorem tdMany_integers_subset :
    tdManyIntegers p K ⊆ packetNormalizationSet p (PiTensorProduct ℚ_[p] K) := by
  set φ := (algebraMap ℚ_[p] (PiTensorProduct ℚ_[p] K)).comp (algebraMap ℤ_[p] ℚ_[p])
  let M : AddSubmonoid (PiTensorProduct ℚ_[p] K) :=
    { carrier := {z | φ.IsIntegralElem z}
      add_mem' := fun ha hb => RingHom.IsIntegralElem.add φ ha hb
      zero_mem' := RingHom.isIntegralElem_zero φ }
  have hgen : {w | ∃ x : ∀ i, K i, (∀ i, padicVolIntegral p (x i)) ∧
      w = PiTensorProduct.tprod ℚ_[p] x} ⊆ (M : Set (PiTensorProduct ℚ_[p] K)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact tdMany_tprod_integral p K hx
  intro z hz
  exact (AddSubmonoid.closure_le.mpr hgen) hz

variable (s : ι)

/-- The `ℚ_p`-algebra map `⊗_{i ≠ s} K_i → ⊗_i K_i`, `⊗_i y_i ↦ ⊗_i y'_i` with `y'_s = 1`. -/
noncomputable def tdManyInsertOne :
    PiTensorProduct ℚ_[p] (fun i : {i // i ≠ s} => K i) →ₐ[ℚ_[p]] PiTensorProduct ℚ_[p] K :=
  PiTensorProduct.liftAlgHom
    ((PiTensorProduct.tprod ℚ_[p]).domDomRestrict (fun i => i ≠ s) (fun _ => 1))
    (by
      rw [MultilinearMap.domDomRestrict_apply, PiTensorProduct.one_def]
      congr 1
      funext j
      split_ifs <;> rfl)
    (by
      intro x y
      rw [MultilinearMap.domDomRestrict_apply, MultilinearMap.domDomRestrict_apply,
        MultilinearMap.domDomRestrict_apply, PiTensorProduct.tprod_mul_tprod]
      congr 1
      funext j
      by_cases h : j = s
      · subst h
        simp
      · simp [h])

/-- The `ℚ_p`-algebra map `K_s ⊗ (⊗_{i ≠ s} K_i) → ⊗_i K_i`, `x ⊗ (⊗_i y_i) ↦ ⊗_i y'_i` with
`y'_s = x`. -/
noncomputable def tdManySplitMap :
    TensorProduct ℚ_[p] (K s) (PiTensorProduct ℚ_[p] (fun i : {i // i ≠ s} => K i)) →ₐ[ℚ_[p]]
      PiTensorProduct ℚ_[p] K :=
  Algebra.TensorProduct.lift (PiTensorProduct.singleAlgHom s) (tdManyInsertOne p K s)
    (fun _ _ => Commute.all _ _)

omit [Fintype ι] [∀ i, FiniteDimensional ℚ_[p] (K i)] [∀ i, Algebra ℤ_[p] (K i)]
  [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (K i)] in
/-- `tdManySplitMap` on a generator. -/
theorem tdMany_splitMap_tmul (x : K s) (y : ∀ i : {i // i ≠ s}, K i) :
    tdManySplitMap p K s (TensorProduct.tmul ℚ_[p] x (PiTensorProduct.tprod ℚ_[p] y)) =
      PiTensorProduct.tprod ℚ_[p]
        (Pi.mulSingle s x * fun j => if h : j ≠ s then y ⟨j, h⟩ else 1) := by
  rw [tdManySplitMap, Algebra.TensorProduct.lift_tmul, tdManyInsertOne,
    PiTensorProduct.liftAlgHom_apply, PiTensorProduct.lift.tprod,
    MultilinearMap.domDomRestrict_apply, PiTensorProduct.singleAlgHom_apply,
    PiTensorProduct.tprod_mul_tprod]
  rfl

omit [Fintype ι] [∀ i, FiniteDimensional ℚ_[p] (K i)] [∀ i, Algebra ℤ_[p] (K i)]
  [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (K i)] in
/-- The components of the image of a generator are integral when `x` and the `y_i` are. -/
theorem tdMany_splitMap_component_integral {x : K s} {y : ∀ i : {i // i ≠ s}, K i}
    (hx : padicVolIntegral p x) (hy : ∀ i, padicVolIntegral p (y i)) (j : ι) :
    padicVolIntegral p ((Pi.mulSingle s x * fun j => if h : j ≠ s then y ⟨j, h⟩ else 1) j) := by
  by_cases h : j = s
  · subst h
    simpa using hx
  · simpa [h, Pi.mulSingle_eq_of_ne h] using hy ⟨j, h⟩

omit [∀ i, Algebra ℤ_[p] (K i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (K i)] in
/-- **The split `⊗_i K_i = K_s ⊗ (⊗_{i ≠ s} K_i)`**: `tdManySplitMap` is bijective. It is
surjective because its image contains every pure tensor, and the two sides have the same
dimension `∏_i [K_i : ℚ_p]`. -/
theorem tdMany_splitMap_bijective : Function.Bijective (tdManySplitMap p K s) := by
  classical
  have hsurj : Function.Surjective (tdManySplitMap p K s) := by
    have hle : Submodule.span ℚ_[p] (Set.range (PiTensorProduct.tprod ℚ_[p] (s := K))) ≤
        LinearMap.range (tdManySplitMap p K s).toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      refine ⟨TensorProduct.tmul ℚ_[p] (x s)
        (PiTensorProduct.tprod ℚ_[p] (fun i : {i // i ≠ s} => x i)), ?_⟩
      rw [AlgHom.toLinearMap_apply, tdMany_splitMap_tmul]
      congr 1
      funext j
      by_cases h : j = s
      · subst h
        simp
      · simp [h]
    rw [PiTensorProduct.span_tprod_eq_top, top_le_iff, LinearMap.range_eq_top] at hle
    exact hle
  refine ⟨?_, hsurj⟩
  have hdim : Module.finrank ℚ_[p]
      (TensorProduct ℚ_[p] (K s) (PiTensorProduct ℚ_[p] (fun i : {i // i ≠ s} => K i))) =
      Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] K) := by
    rw [Module.finrank_tensorProduct, packet_finrank, packet_finrank,
      Fintype.prod_eq_mul_prod_subtype_ne _ s]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (tdManySplitMap p K s).toLinearMap)).2 hsurj

/-- **IUT IV Proposition 1.1, ideal form, any finite number of factors** (page 9): fix `s ∈ I`
(the page's `*`) and, for `i ≠ s`, `δ_i` in the different ideal of `R_i` over `ℤ_p`, with
`δ_s = 1`. Then `(⊗_i δ_i) · z ∈ R_I` for every `z` of `⊗_i K_i` integral over `ℤ_p`:
`p ^ (𝔡_{I*}) · (R_I)^∼ ⊆ R_I` for the products `⊗_{i ∈ I*} δ_i` of elements of the differents. -/
theorem tdMany_mul_mem_integers (δ : ∀ i, K i) (hδs : δ s = 1)
    (hδ : ∀ i, i ≠ s → ∃ d : integralClosure ℤ_[p] (K i),
      (letI := isDedekindDomain_ringOfIntegers_padic p (K i);
        letI := isTorsionFree_ringOfIntegers_padic p (K i);
        d ∈ differentIdeal ℤ_[p] (integralClosure ℤ_[p] (K i))) ∧ (d : K i) = δ i)
    {z : PiTensorProduct ℚ_[p] K} (hz : z ∈ packetNormalizationSet p (PiTensorProduct ℚ_[p] K)) :
    PiTensorProduct.tprod ℚ_[p] δ * z ∈ tdManyIntegers p K := by
  classical
  set e := AlgEquiv.ofBijective _ (tdMany_splitMap_bijective p K s)
  have he : ∀ w, e w = tdManySplitMap p K s w := fun w => rfl
  have hz' : padicVolIntegral p (e.symm z) := padicVolIntegral_map p e.symm.toAlgHom hz
  have hmem := tdMany_split_mul_mem p (fun i : {i // i ≠ s} => K i) (K s)
    (fun i => δ i) (fun i => hδ i i.2) hz'
  have hδe : e (TensorProduct.tmul ℚ_[p] (1 : K s)
      (PiTensorProduct.tprod ℚ_[p] (fun i : {i // i ≠ s} => δ i))) =
      PiTensorProduct.tprod ℚ_[p] δ := by
    rw [he, tdMany_splitMap_tmul, Pi.mulSingle_one, one_mul]
    congr 1
    funext j
    by_cases h : j = s
    · subst h
      simp [hδs]
    · simp [h]
  have hmap : ∀ w ∈ tdManySplitIntegers p (fun i : {i // i ≠ s} => K i) (K s),
      e w ∈ tdManyIntegers p K := by
    intro w hw
    let T : AddSubmonoid
        (TensorProduct ℚ_[p] (K s) (PiTensorProduct ℚ_[p] (fun i : {i // i ≠ s} => K i))) :=
      (AddSubmonoid.closure {w | ∃ x : ∀ i, K i, (∀ i, padicVolIntegral p (x i)) ∧
        w = PiTensorProduct.tprod ℚ_[p] x}).comap (e : _ →+ PiTensorProduct ℚ_[p] K)
    have hgen : {w | ∃ (x : K s) (y : ∀ i : {i // i ≠ s}, K i), padicVolIntegral p x ∧
        (∀ i, padicVolIntegral p (y i)) ∧
        w = TensorProduct.tmul ℚ_[p] x (PiTensorProduct.tprod ℚ_[p] y)} ⊆
        (T : Set _) := by
      rintro _ ⟨x, y, hx, hy, rfl⟩
      show e _ ∈ AddSubmonoid.closure _
      rw [he, tdMany_splitMap_tmul]
      exact AddSubmonoid.subset_closure
        ⟨_, tdMany_splitMap_component_integral p K s hx hy, rfl⟩
    exact (AddSubmonoid.closure_le.mpr hgen) hw
  have h := hmap _ hmem
  rwa [map_mul, hδe, AlgEquiv.apply_symm_apply] at h


/-- **IUT IV Proposition 1.1, any finite number of factors, with `p ^ (𝔡_i)` given by its order**
(page 9): fix `s ∈ I` (the page's `*`) and, for each `i`, a prime `P_i` of `R_i` over `p`. Let
`δ_s = 1` and, for `i ≠ s`, let `δ_i ∈ K_i` have order `𝔡_i` (spectral norm `p ^ (−𝔡_i)`,
`𝔡_i = differentOrder` at `P_i`), the page's `p ^ (𝔡_i)`. Then for every `z` of `⊗_i K_i`
integral over `ℤ_p`, `(⊗_i δ_i) · z ∈ R_I`. -/
theorem tdMany_order_mul_mem_integers (P : ∀ i, Ideal (integralClosure ℤ_[p] (K i)))
    [∀ i, (P i).IsPrime] [∀ i, (P i).LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (δ : ∀ i, K i) (hδs : δ s = 1)
    (hδ : ∀ i, i ≠ s → (letI := isDedekindDomain_ringOfIntegers_padic p (K i);
      letI := isTorsionFree_ringOfIntegers_padic p (K i);
      letI := spectralNorm.normedField ℚ_[p] (K i);
      ‖δ i‖ = (p : ℝ) ^ (-differentOrder ℤ_[p] (integralClosure ℤ_[p] (K i)) (P i))))
    {z : PiTensorProduct ℚ_[p] K} (hz : z ∈ packetNormalizationSet p (PiTensorProduct ℚ_[p] K)) :
    PiTensorProduct.tprod ℚ_[p] δ * z ∈ tdManyIntegers p K :=
  tdMany_mul_mem_integers p K s δ hδs
    (fun i hi => tdMany_order_mem_different p (K i) (P i) (hδ i hi)) hz

omit [DecidableEq ι] [∀ i, FiniteDimensional ℚ_[p] (K i)] [∀ i, Algebra ℤ_[p] (K i)]
  [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (K i)] in
/-- Changing the elements `δ_i` by factors integral over `ℤ_p` does not enlarge the set
`(⊗_i δ_i) · (R_I)^∼`. -/
theorem tdMany_image_subset (δ δ' : ∀ i, K i) (h0 : ∀ i, δ i ≠ 0)
    (hq : ∀ i, padicVolIntegral p (δ' i / δ i)) :
    (fun z => PiTensorProduct.tprod ℚ_[p] δ' * z) ''
        packetNormalizationSet p (PiTensorProduct ℚ_[p] K) ⊆
      (fun z => PiTensorProduct.tprod ℚ_[p] δ * z) ''
        packetNormalizationSet p (PiTensorProduct ℚ_[p] K) := by
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨PiTensorProduct.tprod ℚ_[p] (fun i => δ' i / δ i) * z, ?_, ?_⟩
  · exact RingHom.IsIntegralElem.mul _ (tdMany_tprod_integral p K hq) hz
  · show PiTensorProduct.tprod ℚ_[p] δ * (PiTensorProduct.tprod ℚ_[p] _ * z) = _
    rw [← mul_assoc, PiTensorProduct.tprod_mul_tprod]
    congr 2
    funext i
    exact mul_div_cancel₀ (δ' i) (h0 i)

/-- **Independence of the choice of `p ^ (𝔡_{I*})`** (page 9: the left-hand side "is well-defined
for suitable `p ^ (𝔡_{I*})` ... and independent of the choice"): for two families `δ`, `δ'` as
in `tdMany_order_mul_mem_integers`, `(⊗_i δ_i) · (R_I)^∼ = (⊗_i δ'_i) · (R_I)^∼`. -/
theorem tdMany_choice_independent (P : ∀ i, Ideal (integralClosure ℤ_[p] (K i)))
    (δ δ' : ∀ i, K i) (hδs : δ s = 1) (hδ's : δ' s = 1)
    (hδ : ∀ i, i ≠ s → (letI := isDedekindDomain_ringOfIntegers_padic p (K i);
      letI := isTorsionFree_ringOfIntegers_padic p (K i);
      letI := spectralNorm.normedField ℚ_[p] (K i);
      ‖δ i‖ = (p : ℝ) ^ (-differentOrder ℤ_[p] (integralClosure ℤ_[p] (K i)) (P i))))
    (hδ' : ∀ i, i ≠ s → (letI := isDedekindDomain_ringOfIntegers_padic p (K i);
      letI := isTorsionFree_ringOfIntegers_padic p (K i);
      letI := spectralNorm.normedField ℚ_[p] (K i);
      ‖δ' i‖ = (p : ℝ) ^ (-differentOrder ℤ_[p] (integralClosure ℤ_[p] (K i)) (P i)))) :
    (fun z => PiTensorProduct.tprod ℚ_[p] δ * z) ''
        packetNormalizationSet p (PiTensorProduct ℚ_[p] K) =
      (fun z => PiTensorProduct.tprod ℚ_[p] δ' * z) ''
        packetNormalizationSet p (PiTensorProduct ℚ_[p] K) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have key : ∀ (a b : ∀ i, K i), a s = 1 → b s = 1 →
      (∀ i, i ≠ s → (letI := spectralNorm.normedField ℚ_[p] (K i); ‖a i‖ = ‖b i‖)) →
      (∀ i, i ≠ s → (letI := spectralNorm.normedField ℚ_[p] (K i); 0 < ‖a i‖)) →
      (∀ i, a i ≠ 0) ∧ ∀ i, padicVolIntegral p (b i / a i) := by
    intro a b ha hb hab hpos
    refine ⟨fun i => ?_, fun i => ?_⟩
    · by_cases h : i = s
      · subst h
        rw [ha]
        exact one_ne_zero
      · let := spectralNorm.normedField ℚ_[p] (K i)
        exact norm_pos_iff.mp (hpos i h)
    · by_cases h : i = s
      · subst h
        rw [ha, hb, div_one]
        exact RingHom.isIntegralElem_one _
      · let := spectralNorm.normedField ℚ_[p] (K i)
        rw [tensorDiff_padicVolIntegral_iff, mem_integralClosure_iff]
        refine (padicBridge_norm_le_one_iff_isIntegral p (K i) _).1 ?_
        rw [norm_div, ← hab i h, div_self (hpos i h).ne']
  have hpos : ∀ (a : ∀ i, K i),
      (∀ i, i ≠ s → (letI := isDedekindDomain_ringOfIntegers_padic p (K i);
      letI := isTorsionFree_ringOfIntegers_padic p (K i);
      letI := spectralNorm.normedField ℚ_[p] (K i);
      ‖a i‖ = (p : ℝ) ^ (-differentOrder ℤ_[p] (integralClosure ℤ_[p] (K i)) (P i)))) →
      ∀ i, i ≠ s → (letI := spectralNorm.normedField ℚ_[p] (K i); 0 < ‖a i‖) := by
    intro a ha i hi
    rw [ha i hi]
    exact Real.rpow_pos_of_pos hp0 _
  obtain ⟨h0, hq⟩ := key δ δ' hδs hδ's (fun i hi => (hδ i hi).trans (hδ' i hi).symm)
    (hpos δ hδ)
  obtain ⟨h0', hq'⟩ := key δ' δ hδ's hδs (fun i hi => (hδ' i hi).trans (hδ i hi).symm)
    (hpos δ' hδ')
  exact (tdMany_image_subset p K δ' δ h0' hq').antisymm (tdMany_image_subset p K δ δ' h0 hq)

/-- **IUT IV Proposition 1.1** (page 9, proof on pages 9 and 10), as printed, for the packet
`⊗_{i ∈ I} K_i` over `ℚ_p`: let `I` be finite of cardinality at least two, `s ∈ I` the page's
`*`, and for each `i` a prime `P_i` of `R_i` over `p`, with `𝔡_i` the order of the different at
`P_i`. Then
1. `p ^ (𝔡_{I*}) · (R_I)^∼ ⊆ R_I` for every product `p ^ (𝔡_{I*}) = ⊗_i δ_i` with `δ_s = 1`
   and `δ_i` of order `𝔡_i` for `i ≠ s`;
2. `R_I ⊆ (R_I)^∼`;
3. the set `p ^ (𝔡_{I*}) · (R_I)^∼` does not depend on the choice of the `δ_i`.
The cardinality hypothesis is the page's; the proof does not use it. -/
theorem tdMany_proposition1_1 (_hI : 2 ≤ Fintype.card ι)
    (P : ∀ i, Ideal (integralClosure ℤ_[p] (K i)))
    [∀ i, (P i).IsPrime] [∀ i, (P i).LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    (∀ δ : ∀ i, K i, δ s = 1 →
      (∀ i, i ≠ s → (letI := isDedekindDomain_ringOfIntegers_padic p (K i);
        letI := isTorsionFree_ringOfIntegers_padic p (K i);
        letI := spectralNorm.normedField ℚ_[p] (K i);
        ‖δ i‖ = (p : ℝ) ^ (-differentOrder ℤ_[p] (integralClosure ℤ_[p] (K i)) (P i)))) →
      ∀ z ∈ packetNormalizationSet p (PiTensorProduct ℚ_[p] K),
        PiTensorProduct.tprod ℚ_[p] δ * z ∈ tdManyIntegers p K) ∧
    tdManyIntegers p K ⊆ packetNormalizationSet p (PiTensorProduct ℚ_[p] K) ∧
    (∀ δ δ' : ∀ i, K i, δ s = 1 → δ' s = 1 →
      (∀ i, i ≠ s → (letI := isDedekindDomain_ringOfIntegers_padic p (K i);
        letI := isTorsionFree_ringOfIntegers_padic p (K i);
        letI := spectralNorm.normedField ℚ_[p] (K i);
        ‖δ i‖ = (p : ℝ) ^ (-differentOrder ℤ_[p] (integralClosure ℤ_[p] (K i)) (P i)))) →
      (∀ i, i ≠ s → (letI := isDedekindDomain_ringOfIntegers_padic p (K i);
        letI := isTorsionFree_ringOfIntegers_padic p (K i);
        letI := spectralNorm.normedField ℚ_[p] (K i);
        ‖δ' i‖ = (p : ℝ) ^ (-differentOrder ℤ_[p] (integralClosure ℤ_[p] (K i)) (P i)))) →
      (fun z => PiTensorProduct.tprod ℚ_[p] δ * z) ''
          packetNormalizationSet p (PiTensorProduct ℚ_[p] K) =
        (fun z => PiTensorProduct.tprod ℚ_[p] δ' * z) ''
          packetNormalizationSet p (PiTensorProduct ℚ_[p] K)) :=
  ⟨fun δ hδs hδ _ hz => tdMany_order_mul_mem_integers p K s P δ hδs hδ hz,
    tdMany_integers_subset p K,
    fun δ δ' hδs hδ's hδ hδ' => tdMany_choice_independent p K s P δ δ' hδs hδ's hδ hδ'⟩

end Packet

end IUT.PaperIV.LocalFields
