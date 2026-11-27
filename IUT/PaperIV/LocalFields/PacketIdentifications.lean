import IUT.PaperIV.LocalFields.TensorDifferentMany

/-!
# Proposition 1.1 of IUT IV on the page's own rings

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Proposition 1.1 (page 9). Pages read
for this file: 9 and 10. Pages checked against rendered images: 9 and 10. Displays relied on:
* page 9: `R_i = 𝒪_{k_i}` for finite extensions `k_i` of `ℚ_p`, `i ∈ I`, `I` finite of
  cardinality `≥ 2`; `𝔡_i ∈ ℚ_{≥0}` "the order [i.e., `ord(−)`] of any generator of the different
  ideal of `R_i` over `ℤ_p`", with `ord(p) = 1`; `R_E = ⊗_{i ∈ E} R_i` "where the tensor product
  is over `ℤ_p`"; the display `p ^ (𝔡_{I*}) · (R_I)^∼ ⊆ R_I ⊆ (R_I)^∼`, where `(−)^∼` is "the
  normalization of the [reduced] ring in parentheses in its ring of fractions", and the
  left-hand side "is well-defined for suitable `p ^ (𝔡_{I*})` [such as products of elements
  `p ^ (𝔡_i) ∈ R_i`, for `i ∈ I*`] and independent of the choice";
* page 10: the end of the proof (read to confirm that no further hypothesis enters).

## What this file adds to `IUT.PaperIV.LocalFields.TensorDifferentMany`

That module proves Proposition 1.1 with `R_I` read as the additive span `tdManyIntegers` of the
integral pure tensors inside the packet `⊗_{i ∈ I} K_i` over `ℚ_p`, and `(R_I)^∼` read as the
integral closure `packetNormalizationSet` of `ℤ_p` in the packet. This file identifies both with
the page's objects, for any finite index type, directly for `PiTensorProduct` (not two factors
first):

1. `packetIdZpTensor`: the page's `R_I = ⊗_{i ∈ I} R_i` over `ℤ_p`, with
   `R_i = integralClosure ℤ_[p] K_i`, as a commutative ring. `packetIdMap`: the natural
   `ℤ_p`-algebra map `R_I → ⊗_{i ∈ I} K_i` (over `ℚ_p`), `⊗_i r_i ↦ ⊗_i r_i`.
   `packetId_map_injective`: it is injective (a `ℤ_p`-basis of `R_I`, the tensor product of
   bases of the `R_i`, goes to a `ℚ_p`-basis of the packet). `packetId_range_eq`: its image is
   `tdManyIntegers` when `I` is nonempty.
2. `packetId_isReduced`: `R_I` is reduced. `packetId_isLocalization`: the packet, as an
   `R_I`-algebra through `packetIdMap`, is the localization of `R_I` at its nonzero divisors
   (its total ring of fractions). `packetId_isIntegralElem_iff`: an element of the packet is
   integral over `R_I` if and only if it is integral over `ℤ_p` (`R_I` is finite over `ℤ_p`;
   transitivity of integrality). So the normalization of `R_I` in its ring of fractions is
   `packetNormalizationSet`.
3. `packetId_proposition1_1`: Proposition 1.1 stated on `R_I = ⊗_{ℤ_p} R_i` and on its
   normalization in its total ring of fractions, a corollary of `tdMany_proposition1_1`.
   Clause by clause against the page: `R_I` is the tensor product over `ℤ_p` (yes); "[reduced]"
   (yes, as a conjunct); "normalization in its ring of fractions" (yes, the packet is proved to
   be the localization at the nonzero divisors and `(R_I)^∼` is the set of elements integral
   over `R_I`); both inclusions (yes); well-definedness and independence of the choice (yes, for
   the pure-tensor choices); `|I| ≥ 2` and any `* ∈ I` (yes). Not in the statement: the `k_i`
   as subfields of a fixed `ℚ̄_p`, and choices of `p ^ (𝔡_{I*})` other than pure tensors, here;
   every element of order `𝔡_{I*}` in each field component is treated in
   `IUT.PaperIV.LocalFields.PacketSuitable` (`psuit_proposition1_1`).
4. `packetId_exists_generator_order`: the different ideal of `R_i` has a generator `d` with
   `‖d‖ = p ^ (−𝔡_i)` for the spectral norm, so an element of order `𝔡_i` exists in `K_i`;
   `packetId_exists_admissible`: a family `δ` as in item 3 exists for every `s`.

## Readings that remain

* The fields `k_i` are abstract finite extensions of `ℚ_p` with compatible `ℤ_p`-algebra
  structures, not subfields of a fixed algebraic closure; the ring of fractions is realized as
  the packet over `ℚ_p` with the map `packetIdMap`, proved to be a localization of `R_I` at its
  nonzero divisors (any two such are isomorphic over `R_I` by the universal property).
* "Order `𝔡_i`" is read through the spectral norm, `‖δ_i‖ = p ^ (−𝔡_i)`, and `𝔡_i` is
  `differentOrder` at a prime `P_i` of `R_i` over `p` (normalized by `ord(p) = 1`).
  `packetId_exists_generator_order` repeats part of the argument of
  `tdMany_order_mem_different` (the different is a power of the uniformizer); no library lemma
  gives the norm of a generator of the different.
* The primes `P_i` remain inputs (each `R_i` is local, so `P_i` is its maximal ideal; this is
  not used to remove the parameter).
* "Suitable `p ^ (𝔡_{I*})`" is read as a pure tensor `⊗_i δ_i` with `δ_* = 1` and `δ_i` of
  order `𝔡_i` for `i ≠ *`; other suitable elements are not formalized here (see
  `IUT.PaperIV.LocalFields.PacketSuitable`).

## Not proved

* That the many-factor statements, for a two-element index type, specialize to the binary
  theorems of `IUT.PaperIV.LocalFields.TensorDifferent` (the identification of `PiTensorProduct`
  over two indices with `TensorProduct` is not made).
-/

namespace IUT.PaperIV.LocalFields

open IUT.Prerequisites.PadicVolume

section ZpTensor

variable (p : ℕ) [hp : Fact p.Prime] {ι : Type} [Fintype ι] (K : ι → Type)
  [∀ i, Field (K i)] [∀ i, Algebra ℚ_[p] (K i)] [∀ i, FiniteDimensional ℚ_[p] (K i)]
  [∀ i, Algebra ℤ_[p] (K i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (K i)]

/-- The page's `R_I = ⊗_{i ∈ I} R_i`, the tensor product over `ℤ_p` of the rings of integers
`R_i = integralClosure ℤ_[p] K_i` (page 9), as a commutative `ℤ_p`-algebra. -/
abbrev packetIdZpTensor : Type :=
  PiTensorProduct ℤ_[p] (fun i => integralClosure ℤ_[p] (K i))

/-- The `ℤ_p`-multilinear map `(r_i)_i ↦ ⊗_i r_i` into the packet over `ℚ_p`. -/
noncomputable def packetIdMultilinear :
    (∀ i, integralClosure ℤ_[p] (K i)) →ₘₗ[ℤ_[p]] PiTensorProduct ℚ_[p] K :=
  ((PiTensorProduct.tprod ℚ_[p]).restrictScalars ℤ_[p]).compLinearMap
    (fun i => (integralClosure ℤ_[p] (K i)).val.toLinearMap)

/-- The natural `ℤ_p`-algebra map `⊗_{ℤ_p} R_i → ⊗_{ℚ_p} K_i`, `⊗_i r_i ↦ ⊗_i r_i`. -/
noncomputable def packetIdMap : packetIdZpTensor p K →ₐ[ℤ_[p]] PiTensorProduct ℚ_[p] K :=
  PiTensorProduct.liftAlgHom (packetIdMultilinear p K)
    (by
      show PiTensorProduct.tprod ℚ_[p] (fun i => ((1 : integralClosure ℤ_[p] (K i)) : K i)) = 1
      rw [PiTensorProduct.one_def]
      rfl)
    (by
      intro x y
      show PiTensorProduct.tprod ℚ_[p] (fun i => ((x i * y i : integralClosure ℤ_[p] (K i)) : K i))
        = PiTensorProduct.tprod ℚ_[p] (fun i => (x i : K i)) *
          PiTensorProduct.tprod ℚ_[p] (fun i => (y i : K i))
      rw [PiTensorProduct.tprod_mul_tprod]
      rfl)

omit [Fintype ι] [∀ i, FiniteDimensional ℚ_[p] (K i)] in
/-- `packetIdMap` on a pure tensor. -/
theorem packetId_map_tprod (r : ∀ i, integralClosure ℤ_[p] (K i)) :
    packetIdMap p K (PiTensorProduct.tprod ℤ_[p] r) =
      PiTensorProduct.tprod ℚ_[p] (fun i => (r i : K i)) := by
  rw [packetIdMap, PiTensorProduct.liftAlgHom_apply, PiTensorProduct.lift.tprod]
  rfl

/-- Bases: a `ℤ_p`-basis `B` of `⊗_{ℤ_p} R_i` and a `ℚ_p`-basis `B'` of `⊗_{ℚ_p} K_i`, on the
same index set, with `packetIdMap (B j) = B' j` (tensor products of a `ℤ_p`-basis of each `R_i`,
viewed in `R_i` and in `K_i`). -/
theorem packetId_exists_bases :
    ∃ (n : ι → ℕ) (B : Module.Basis (∀ i, Fin (n i)) ℤ_[p] (packetIdZpTensor p K))
      (B' : Module.Basis (∀ i, Fin (n i)) ℚ_[p] (PiTensorProduct ℚ_[p] K)),
      ∀ j, packetIdMap p K (B j) = B' j := by
  classical
  have hfin : ∀ i, Module.Finite ℤ_[p] (integralClosure ℤ_[p] (K i)) := fun i =>
    IsIntegralClosure.finite ℤ_[p] ℚ_[p] (K i) _
  have hfree : ∀ i, Module.Free ℤ_[p] (integralClosure ℤ_[p] (K i)) := fun i => by
    let := isTorsionFree_ringOfIntegers_padic p (K i)
    exact Module.free_of_finite_type_torsion_free'
  have hloc : ∀ i, IsLocalization (Algebra.algebraMapSubmonoid (integralClosure ℤ_[p] (K i))
      (nonZeroDivisors ℤ_[p])) (K i) := fun i =>
    IsIntegralClosure.isLocalization ℤ_[p] ℚ_[p] (K i) _
  let b := fun i => (Module.Free.chooseBasis ℤ_[p] (integralClosure ℤ_[p] (K i))).reindex
    (Fintype.equivFin _)
  let b' := fun i => (b i).localizationLocalization ℚ_[p] (nonZeroDivisors ℤ_[p]) (K i)
  refine ⟨_, Basis.piTensorProduct b, Basis.piTensorProduct b', fun j => ?_⟩
  rw [Basis.piTensorProduct_apply, Basis.piTensorProduct_apply, packetId_map_tprod]
  congr 1
  funext i
  rw [Module.Basis.localizationLocalization_apply]
  rfl

/-- **Injectivity** (item 1 of the module docstring):
the natural map `⊗_{ℤ_p} R_i → ⊗_{ℚ_p} K_i` is injective, for any
finite index type. -/
theorem packetId_map_injective : Function.Injective (packetIdMap p K) := by
  obtain ⟨n, B, B', hBB⟩ := packetId_exists_bases p K
  have hcomp : (packetIdMap p K).toLinearMap ∘ B = B' := funext hBB
  have hli : LinearIndependent ℤ_[p] ((packetIdMap p K).toLinearMap ∘ B) := by
    rw [hcomp]
    refine B'.linearIndependent.restrict_scalars ?_
    intro x y hxy
    have h : algebraMap ℤ_[p] ℚ_[p] x = algebraMap ℤ_[p] ℚ_[p] y := by
      simpa [Algebra.smul_def] using hxy
    exact IsFractionRing.injective ℤ_[p] ℚ_[p] h
  have hdis := Submodule.range_ker_disjoint hli
  rw [B.span_eq, top_disjoint] at hdis
  exact LinearMap.ker_eq_bot.1 hdis

omit [Fintype ι] [∀ i, FiniteDimensional ℚ_[p] (K i)] in
/-- **The image** (item 1 of the module docstring): for nonempty `I`, the image of
`⊗_{ℤ_p} R_i` in the packet is `tdManyIntegers`, the additive span of the pure tensors of
integral elements. Nonemptiness is needed: for empty `I`, `tdManyIntegers` is the additive
submonoid `ℕ · 1`, while the image is `ℤ_p · 1`. -/
theorem packetId_range_eq [Nonempty ι] :
    Set.range (packetIdMap p K) = tdManyIntegers p K := by
  classical
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using PiTensorProduct.induction_on with
    | smul_tprod c r =>
      obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
      have hr : c • PiTensorProduct.tprod ℤ_[p] r =
          PiTensorProduct.tprod ℤ_[p] (Function.update r i₀ (c • r i₀)) := by
        rw [MultilinearMap.map_update_smul, Function.update_eq_self, RingHom.id_apply]
      rw [hr, packetId_map_tprod]
      refine AddSubmonoid.subset_closure ⟨_, fun i => ?_, rfl⟩
      exact (tensorDiff_padicVolIntegral_iff p (K i) _).2
        (Function.update r i₀ (c • r i₀) i).2
    | add x y hx hy =>
      rw [map_add]
      exact AddSubmonoid.add_mem _ hx hy
  · intro z hz
    let M : AddSubmonoid (PiTensorProduct ℚ_[p] K) := AddMonoidHom.mrange
      (packetIdMap p K).toRingHom.toAddMonoidHom
    have hgen : {w | ∃ x : ∀ i, K i, (∀ i, padicVolIntegral p (x i)) ∧
        w = PiTensorProduct.tprod ℚ_[p] x} ⊆ (M : Set (PiTensorProduct ℚ_[p] K)) := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨PiTensorProduct.tprod ℤ_[p]
        (fun i => ⟨x i, (tensorDiff_padicVolIntegral_iff p (K i) _).1 (hx i)⟩), ?_⟩
      exact packetId_map_tprod p K _
    exact (AddSubmonoid.closure_le.mpr hgen) hz

/-- **Reducedness** (item 2 of the module docstring):
`R_I = ⊗_{ℤ_p} R_i` is reduced (it embeds in the reduced packet). -/
theorem packetId_isReduced : IsReduced (packetIdZpTensor p K) := by
  have := packet_isReduced p K
  exact isReduced_of_injective (packetIdMap p K) (packetId_map_injective p K)

/-- Every element of the packet has a multiple by a nonzero element of `ℤ_p` in the image of
`R_I`. -/
theorem packetId_exists_integer_multiple (w : PiTensorProduct ℚ_[p] K) :
    ∃ d ∈ nonZeroDivisors ℤ_[p], ∃ y : packetIdZpTensor p K,
      packetIdMap p K y = algebraMap ℤ_[p] (PiTensorProduct ℚ_[p] K) d * w := by
  classical
  obtain ⟨n, B, B', hBB⟩ := packetId_exists_bases p K
  obtain ⟨⟨d, hd⟩, h⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ_[p])
    (Finset.univ : Finset (∀ i, Fin (n i))) (B'.repr w)
  choose a ha using fun j => h j (Finset.mem_univ j)
  refine ⟨d, hd, ∑ j, a j • B j, ?_⟩
  rw [map_sum, ← Algebra.smul_def]
  conv_rhs => rw [← B'.sum_repr w, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, hBB, ← algebraMap_smul ℚ_[p] (a j), ha j, smul_assoc]

omit [Fintype ι] [∀ i, FiniteDimensional ℚ_[p] (K i)] [∀ i, Algebra ℤ_[p] (K i)]
  [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (K i)] in
/-- The image of a nonzero element of `ℤ_p` is a unit of the packet. -/
theorem packetId_algebraMap_isUnit {d : ℤ_[p]} (hd : d ∈ nonZeroDivisors ℤ_[p]) :
    IsUnit (algebraMap ℤ_[p] (PiTensorProduct ℚ_[p] K) d) := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PiTensorProduct ℚ_[p] K)]
  refine (IsUnit.map _ (Ne.isUnit ?_))
  exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := ℚ_[p]) hd)

/-- **The total ring of fractions** (item 2 of the module docstring):
the packet `⊗_{ℚ_p} K_i`, as an `R_I`-algebra
through `packetIdMap`, is the localization of `R_I = ⊗_{ℤ_p} R_i` at its nonzero divisors. -/
theorem packetId_isLocalization :
    letI : Algebra (packetIdZpTensor p K) (PiTensorProduct ℚ_[p] K) :=
      (packetIdMap p K).toRingHom.toAlgebra
    IsLocalization (nonZeroDivisors (packetIdZpTensor p K)) (PiTensorProduct ℚ_[p] K) := by
  let : Algebra (packetIdZpTensor p K) (PiTensorProduct ℚ_[p] K) :=
    (packetIdMap p K).toRingHom.toAlgebra
  have hinj := packetId_map_injective p K
  have hf : ∀ y, algebraMap (packetIdZpTensor p K) (PiTensorProduct ℚ_[p] K) y =
      packetIdMap p K y := fun _ => rfl
  rw [isLocalization_iff]
  refine ⟨fun ⟨x, hx⟩ => ?_, fun z => ?_, fun {x y} hxy => ⟨1, by rw [hinj hxy]⟩⟩
  · -- a nonzero divisor of `R_I` maps to a nonzero divisor of the packet, hence to a unit
    rw [hf]
    have hinjmul : Function.Injective
        (LinearMap.mulLeft ℚ_[p] (packetIdMap p K x : PiTensorProduct ℚ_[p] K)) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro w hw
      obtain ⟨d, hd, y, hy⟩ := packetId_exists_integer_multiple p K w
      have hxy : packetIdMap p K (y * x) = 0 := by
        rw [LinearMap.mulLeft_apply] at hw
        rw [map_mul, hy, mul_assoc, mul_comm w, hw, mul_zero]
      have hy0 : y = 0 := (mem_nonZeroDivisors_iff.1 hx).2 y
        (hinj (by rw [hxy, map_zero]))
      rw [hy0, map_zero] at hy
      exact ((packetId_algebraMap_isUnit p K hd).mul_right_eq_zero).1 hy.symm
    obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective.1 hinjmul) 1
    exact IsUnit.of_mul_eq_one w hw
  · obtain ⟨d, hd, y, hy⟩ := packetId_exists_integer_multiple p K z
    have hd' : algebraMap ℤ_[p] (packetIdZpTensor p K) d ∈
        nonZeroDivisors (packetIdZpTensor p K) := by
      refine mem_nonZeroDivisors_iff.2 ⟨fun a ha => hinj ?_, fun a ha => hinj ?_⟩
      · have h := congrArg (packetIdMap p K) ha
        rw [map_mul, AlgHom.commutes, map_zero] at h
        rw [map_zero]
        exact ((packetId_algebraMap_isUnit p K hd).mul_right_eq_zero).1 h
      · have h := congrArg (packetIdMap p K) ha
        rw [map_mul, AlgHom.commutes, map_zero] at h
        rw [map_zero]
        exact ((packetId_algebraMap_isUnit p K hd).mul_left_eq_zero).1 h
    refine ⟨⟨y, ⟨_, hd'⟩⟩, ?_⟩
    show z * packetIdMap p K (algebraMap ℤ_[p] _ d) = packetIdMap p K y
    rw [AlgHom.commutes, hy, mul_comm]

/-- **The normalization** (item 2 of the module docstring):
an element of the packet is integral over `R_I = ⊗_{ℤ_p} R_i`
(through `packetIdMap`) if and only if it is integral over `ℤ_p`. With
`packetId_isLocalization`, the normalization `(R_I)^∼` of `R_I` in its total ring of fractions
is `packetNormalizationSet`. -/
theorem packetId_isIntegralElem_iff (w : PiTensorProduct ℚ_[p] K) :
    (packetIdMap p K).toRingHom.IsIntegralElem w ↔
      w ∈ packetNormalizationSet p (PiTensorProduct ℚ_[p] K) := by
  let : Algebra (packetIdZpTensor p K) (PiTensorProduct ℚ_[p] K) :=
    (packetIdMap p K).toRingHom.toAlgebra
  have htower : IsScalarTower ℤ_[p] (packetIdZpTensor p K) (PiTensorProduct ℚ_[p] K) :=
    IsScalarTower.of_algebraMap_eq fun r => ((packetIdMap p K).commutes r).symm
  have hφ : (algebraMap ℚ_[p] (PiTensorProduct ℚ_[p] K)).comp (algebraMap ℤ_[p] ℚ_[p]) =
      algebraMap ℤ_[p] (PiTensorProduct ℚ_[p] K) :=
    (IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (PiTensorProduct ℚ_[p] K)).symm
  obtain ⟨n, B, -, -⟩ := packetId_exists_bases p K
  have : Module.Finite ℤ_[p] (packetIdZpTensor p K) := Module.Finite.of_basis B
  have : Algebra.IsIntegral ℤ_[p] (packetIdZpTensor p K) := Algebra.IsIntegral.of_finite _ _
  show IsIntegral (packetIdZpTensor p K) w ↔ padicVolIntegral p w
  rw [padicVolIntegral, hφ]
  exact ⟨fun h => isIntegral_trans w h, fun h => IsIntegral.tower_top h⟩

end ZpTensor

/-! ## An element of order `𝔡` (item 4 of the module docstring) -/

section Order

variable (p : ℕ) [hp : Fact p.Prime]

/-- **A generator of the different of order `𝔡`** (page 9: `𝔡_i` is the order of any generator
of the different ideal of `R_i` over `ℤ_p`, and `p ^ (𝔡_i)` is an element of that order): for a
prime `P` of `R = integralClosure ℤ_[p] K` over `p`, the different ideal of `R` is generated by
an element `d` with spectral norm `‖d‖ = p ^ (−𝔡)`, `𝔡 = differentOrder` at `P`. -/
theorem packetId_exists_generator_order (K : Type) [Field K] [Algebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]
    (P : Ideal (integralClosure ℤ_[p] K)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    letI := isDedekindDomain_ringOfIntegers_padic p K
    letI := isTorsionFree_ringOfIntegers_padic p K
    letI := spectralNorm.normedField ℚ_[p] K
    ∃ d : integralClosure ℤ_[p] K,
      differentIdeal ℤ_[p] (integralClosure ℤ_[p] K) = Ideal.span {d} ∧
      ‖(d : K)‖ = (p : ℝ) ^ (-differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P) := by
  let := isDedekindDomain_ringOfIntegers_padic p K
  let := isTorsionFree_ringOfIntegers_padic p K
  let := spectralNorm.normedField ℚ_[p] K
  have := padicBridge_isLocalRing p K
  have := padicBridge_isDiscreteValuationRing p K
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
  refine ⟨ϖ ^ n, hn, ?_⟩
  show ‖((ϖ ^ n : integralClosure ℤ_[p] K) : K)‖ = (p : ℝ) ^
    (-((differentExponent ℤ_[p] (integralClosure ℤ_[p] K) P : ℝ) /
      (P.ramificationIdx ℤ_[p] : ℝ)))
  rw [SubmonoidClass.coe_pow, norm_pow, hr, hexp, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
  congr 1
  ring

end Order

/-! ## Proposition 1.1 on the page's objects (item 3 of the module docstring) -/

section Proposition

variable (p : ℕ) [hp : Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] (K : ι → Type)
  [∀ i, Field (K i)] [∀ i, Algebra ℚ_[p] (K i)] [∀ i, FiniteDimensional ℚ_[p] (K i)]
  [∀ i, Algebra ℤ_[p] (K i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (K i)]

omit [Fintype ι] in
/-- **Admissible families exist** (item 4 of the module docstring):
for `s ∈ I` and primes `P_i` of the `R_i` over `p`,
there is `δ` with `δ_s = 1` and `‖δ_i‖ = p ^ (−𝔡_i)` for `i ≠ s`; so the hypotheses on `δ` in
`packetId_proposition1_1` are satisfiable. -/
theorem packetId_exists_admissible (s : ι) (P : ∀ i, Ideal (integralClosure ℤ_[p] (K i)))
    [∀ i, (P i).IsPrime] [∀ i, (P i).LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    ∃ δ : ∀ i, K i, δ s = 1 ∧
      ∀ i, i ≠ s → (letI := isDedekindDomain_ringOfIntegers_padic p (K i);
        letI := isTorsionFree_ringOfIntegers_padic p (K i);
        letI := spectralNorm.normedField ℚ_[p] (K i);
        ‖δ i‖ = (p : ℝ) ^ (-differentOrder ℤ_[p] (integralClosure ℤ_[p] (K i)) (P i))) := by
  choose d hd using fun i => packetId_exists_generator_order p (K i) (P i)
  refine ⟨fun i => if i = s then 1 else (d i : K i), by simp, fun i hi => ?_⟩
  simp only [hi, ite_false]
  exact (hd i).2

/-- **IUT IV Proposition 1.1 on the page's objects** (page 9), for any finite `I` with
`|I| ≥ 2`: `R_I = ⊗_{ℤ_p} R_i` (`packetIdZpTensor`), its total ring of fractions realized as the
packet `⊗_{ℚ_p} K_i` through `packetIdMap`, and `(R_I)^∼` the elements of the packet integral
over `R_I`. With `s` the page's `*` and primes `P_i` of the `R_i` over `p` (so `𝔡_i` is the
order of the different at `P_i`):
0. `R_I` is reduced (the page's "[reduced]");
1. the packet is the localization of `R_I` at its nonzero divisors;
2. `p ^ (𝔡_{I*}) · (R_I)^∼ ⊆ R_I` for every product `p ^ (𝔡_{I*}) = ⊗_i δ_i` with `δ_s = 1`
   and `δ_i` of order `𝔡_i` for `i ≠ s`;
3. `R_I ⊆ (R_I)^∼`;
4. the set `p ^ (𝔡_{I*}) · (R_I)^∼` does not depend on the choice of the `δ_i`.
A corollary of `tdMany_proposition1_1` through `packetId_range_eq` and
`packetId_isIntegralElem_iff`. The hypothesis `|I| ≥ 2` is the page's; the proof uses it only to
know that `I` is nonempty (needed for `packetId_range_eq`). -/
theorem packetId_proposition1_1 (hI : 2 ≤ Fintype.card ι) (s : ι)
    (P : ∀ i, Ideal (integralClosure ℤ_[p] (K i)))
    [∀ i, (P i).IsPrime] [∀ i, (P i).LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    IsReduced (packetIdZpTensor p K) ∧
    (letI : Algebra (packetIdZpTensor p K) (PiTensorProduct ℚ_[p] K) :=
        (packetIdMap p K).toRingHom.toAlgebra;
      IsLocalization (nonZeroDivisors (packetIdZpTensor p K)) (PiTensorProduct ℚ_[p] K)) ∧
    (∀ δ : ∀ i, K i, δ s = 1 →
      (∀ i, i ≠ s → (letI := isDedekindDomain_ringOfIntegers_padic p (K i);
        letI := isTorsionFree_ringOfIntegers_padic p (K i);
        letI := spectralNorm.normedField ℚ_[p] (K i);
        ‖δ i‖ = (p : ℝ) ^ (-differentOrder ℤ_[p] (integralClosure ℤ_[p] (K i)) (P i)))) →
      ∀ w, (packetIdMap p K).toRingHom.IsIntegralElem w →
        PiTensorProduct.tprod ℚ_[p] δ * w ∈ Set.range (packetIdMap p K)) ∧
    (∀ x, (packetIdMap p K).toRingHom.IsIntegralElem (packetIdMap p K x)) ∧
    (∀ δ δ' : ∀ i, K i, δ s = 1 → δ' s = 1 →
      (∀ i, i ≠ s → (letI := isDedekindDomain_ringOfIntegers_padic p (K i);
        letI := isTorsionFree_ringOfIntegers_padic p (K i);
        letI := spectralNorm.normedField ℚ_[p] (K i);
        ‖δ i‖ = (p : ℝ) ^ (-differentOrder ℤ_[p] (integralClosure ℤ_[p] (K i)) (P i)))) →
      (∀ i, i ≠ s → (letI := isDedekindDomain_ringOfIntegers_padic p (K i);
        letI := isTorsionFree_ringOfIntegers_padic p (K i);
        letI := spectralNorm.normedField ℚ_[p] (K i);
        ‖δ' i‖ = (p : ℝ) ^ (-differentOrder ℤ_[p] (integralClosure ℤ_[p] (K i)) (P i)))) →
      (fun w => PiTensorProduct.tprod ℚ_[p] δ * w) ''
          {w | (packetIdMap p K).toRingHom.IsIntegralElem w} =
        (fun w => PiTensorProduct.tprod ℚ_[p] δ' * w) ''
          {w | (packetIdMap p K).toRingHom.IsIntegralElem w}) := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hset : {w | (packetIdMap p K).toRingHom.IsIntegralElem w} =
      packetNormalizationSet p (PiTensorProduct ℚ_[p] K) :=
    Set.ext (packetId_isIntegralElem_iff p K)
  obtain ⟨h1, -, h3⟩ := tdMany_proposition1_1 p K s hI P
  refine ⟨packetId_isReduced p K, packetId_isLocalization p K, fun δ hs hδ w hw => ?_, fun x => ?_,
    fun δ δ' hs hs' hδ hδ' => ?_⟩
  · rw [packetId_range_eq]
    exact h1 δ hs hδ w ((packetId_isIntegralElem_iff p K w).1 hw)
  · exact (packetIdMap p K).toRingHom.isIntegralElem_map
  · rw [hset]
    exact h3 δ δ' hs hs' hδ hδ'

end Proposition

end IUT.PaperIV.LocalFields
