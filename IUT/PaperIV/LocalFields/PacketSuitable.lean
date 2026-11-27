import IUT.PaperIV.LocalFields.PacketIdentifications

/-!
# Proposition 1.1 of IUT IV for every suitable element of order `𝔡_{I*}`

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Proposition 1.1 (page 9). Pages read
for this file: 9. Pages checked against rendered images: 9. Sentences relied on (page 9):
* "write `p^λ` for "some" [unspecified] element of `ℚ̄_p` such that `ord(p^λ) = λ`", with
  `ord : ℚ̄_p^× → ℚ` the `p`-adic valuation normalized so that `ord(p) = 1`;
* `R_E = ⊗_{i ∈ E} R_i` over `ℤ_p` and `𝔡_E = ∑_{i ∈ E} 𝔡_i`; `I* = I \ {*}`;
* the display `p^{𝔡_{I*}} · (R_I)^∼ ⊆ R_I ⊆ (R_I)^∼`, and "the notation on the left-hand side of
  the first inclusion of the above display is well-defined for suitable `p^{𝔡_{I*}}` [such as
  products of elements `p^{𝔡_i} ∈ R_i`, for `i ∈ I*`] and independent of the choice of such
  suitable `p^{𝔡_{I*}}`".

## What this file adds to `IUT.PaperIV.LocalFields.PacketIdentifications`

`packetId_proposition1_1` proves the display and the independence for the pure tensors
`⊗_i δ_i` with `δ_* = 1` and `‖δ_i‖ = p^{−𝔡_i}` (spectral norm) for `i ≠ *`. Here the
restriction to pure tensors is removed.

1. *Order.* `psuitHasOrder p u λ` for `u` in a commutative `ℚ_p`-algebra `W`: every
   `ℚ_p`-algebra map `φ : W → ℚ̄_p` (`ℚ̄_p = AlgebraicClosure ℚ_[p]`) sends `u` to an element of
   spectral norm `p^{−λ}`, that is, of `ord = λ`. `psuit_hasOrder_iff_components`: for every
   decomposition `e : W ≃ Π_j L_j` into finite extensions of `ℚ_p`, this holds if and only if
   every field component `e(u)_j` has spectral norm `p^{−λ}` in `L_j`; so the definition is the
   reading "of order `λ` in every field component" and does not depend on the decomposition.
   (`psuit_algHom_pi_factor`: every `ℚ_p`-algebra map from `Π_j L_j` to a field factors through
   one projection.)
2. *Orders of products.* `psuit_prod_single_hasOrder`: a product `∏_{i ∈ S} δ_i` of elements
   `δ_i ∈ K_i ⊆ ⊗_i K_i` with `δ_i` of spectral norm `p^{−λ_i}` has order `∑_{i ∈ S} λ_i` (each
   component is a product of conjugates of the `δ_i`, and the spectral norm on `ℚ̄_p` is
   multiplicative). `psuit_tprod_hasOrder`: the pure tensor `⊗_i δ_i` has order `∑_i λ_i`.
   `psuit_examples_hasOrder`: the page's examples, products of elements `p^{𝔡_i} ∈ R_i` for
   `i ∈ I*`, have order `𝔡_{I*}`. `psuit_admissible_hasOrder`: so do the pure tensors of
   `packetId_proposition1_1`.
3. *Normalization in components.* `psuit_normalization_eq`: under `e : W ≃ Π_j L_j`, the set
   `packetNormalizationSet` (the elements integral over `ℤ_p`, which is `(R_I)^∼` by
   `packetId_isIntegralElem_iff`) is the preimage of the product of the closed unit balls of the
   spectral norms, the rings of integers of the `L_j`. `psuit_image_eq_of_hasOrder`: two elements
   `u`, `t` of the same order `λ` in a finite formally unramified `ℚ_p`-algebra satisfy
   `u · (R_I)^∼ = t · (R_I)^∼` (their quotient is a unit of `(R_I)^∼`).
4. *Proposition 1.1.* `psuit_proposition1_1`: the statement of `packetId_proposition1_1` with
   the pure tensors replaced by all `u ∈ ⊗_i K_i` of order `𝔡_{I*}`: `u · (R_I)^∼ ⊆ R_I` for
   every such `u`, `R_I ⊆ (R_I)^∼`, and `u · (R_I)^∼` is the same set for all such `u`.
   `psuit_image_eq_tprod`: that set equals `t · (R_I)^∼` for the pure tensors `t` of
   `packetId_proposition1_1`. `psuit_proposition1_1_closure`: the two main clauses when the
   `k_i` are intermediate fields of `ℚ̄_p ⊇ ℚ_p`, the page's setting.

## Readings

* "Suitable `p^{𝔡_{I*}}`" is read as "an element of `⊗_i K_i` of order `𝔡_{I*}` in every field
  component" (equivalently, under every `ℚ_p`-algebra map to `ℚ̄_p`). The page names products of
  elements `p^{𝔡_i} ∈ R_i` as examples; these are in the class (`psuit_examples_hasOrder`). The
  page does not say how an element of `ℚ̄_p` itself acts on `(R_I)^∼`; that reading is not
  formalized.
* As in `IUT.PaperIV.LocalFields.PacketIdentifications`: `𝔡_i` is `differentOrder` at a prime
  `P_i` of `R_i` over `p` (a parameter), the ring of fractions of `R_I` is the packet
  `⊗_{ℚ_p} K_i` through `packetIdMap`, and `(R_I)^∼` is the set of elements integral over `R_I`.
* In `psuit_proposition1_1_closure`, `R_i` is the integral closure of `ℤ_p` in `k_i`, not
  literally `R̄ ∩ k_i` (the two agree, but the identification is not stated here).

## Not proved

* The identification of `integralClosure ℤ_[p] k_i` with `R̄ ∩ k_i` for `R̄` the integral closure
  of `ℤ_p` in `ℚ̄_p` (not needed for the statements here).
-/

namespace IUT.PaperIV.LocalFields

open IUT.Prerequisites.PadicVolume

/-! ## Order of an element of a `ℚ_p`-algebra -/

section Order

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Order `λ`** (page 9: `p^λ` is an element with `ord(p^λ) = λ`, `ord(p) = 1`): an element `u`
of a commutative `ℚ_p`-algebra `W` has order `λ` if every `ℚ_p`-algebra map `W → ℚ̄_p` sends it to
an element of spectral norm `p^{−λ}`. By `psuit_hasOrder_iff_components` this says that every
field component of `u` has spectral norm `p^{−λ}`, for any decomposition of `W` into fields. The
condition has content only when maps `W → ℚ̄_p` exist; for the packet `⊗_i K_i` they do, and
elements of order `𝔡_{I*}` exist (`psuit_exists_hasOrder`). -/
def psuitHasOrder {W : Type*} [CommRing W] [Algebra ℚ_[p] W] (u : W) (lam : ℝ) : Prop :=
  ∀ φ : W →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
    spectralNorm ℚ_[p] (AlgebraicClosure ℚ_[p]) (φ u) = (p : ℝ) ^ (-lam)

/-- The spectral norm over `ℚ_p` is invariant under `ℚ_p`-algebra maps of fields (it depends only
on the minimal polynomial). -/
theorem psuit_spectralNorm_algHom {L M : Type*} [Field L] [Field M] [Algebra ℚ_[p] L]
    [Algebra ℚ_[p] M] (ψ : L →ₐ[ℚ_[p]] M) (x : L) :
    spectralNorm ℚ_[p] M (ψ x) = spectralNorm ℚ_[p] L x := by
  simp only [spectralNorm, minpoly.algHom_eq ψ ψ.toRingHom.injective x]

/-- The spectral norm on an algebraic extension of `ℚ_p` is multiplicative. -/
theorem psuit_spectralNorm_mul {L : Type*} [Field L] [Algebra ℚ_[p] L]
    [Algebra.IsAlgebraic ℚ_[p] L] (x y : L) :
    spectralNorm ℚ_[p] L (x * y) = spectralNorm ℚ_[p] L x * spectralNorm ℚ_[p] L y := by
  simpa only [spectralMulAlgNorm_def] using map_mul (spectralMulAlgNorm ℚ_[p] L) x y

/-- The spectral norm on an algebraic extension of `ℚ_p` takes quotients to quotients. -/
theorem psuit_spectralNorm_div {L : Type*} [Field L] [Algebra ℚ_[p] L]
    [Algebra.IsAlgebraic ℚ_[p] L] (x y : L) :
    spectralNorm ℚ_[p] L (x / y) = spectralNorm ℚ_[p] L x / spectralNorm ℚ_[p] L y := by
  simpa only [spectralMulAlgNorm_def] using map_div₀ (spectralMulAlgNorm ℚ_[p] L) x y

/-- **Maps from a finite product of fields**: every `ℚ_p`-algebra map from `Π_j L_j` to a field
factors through the projection to one `L_j`. -/
theorem psuit_algHom_pi_factor {J : Type*} [Fintype J] (L : J → Type*) [∀ j, Field (L j)]
    [∀ j, Algebra ℚ_[p] (L j)] {M : Type*} [Field M] [Algebra ℚ_[p] M]
    (φ : (Π j, L j) →ₐ[ℚ_[p]] M) :
    ∃ j, ∃ ψ : L j →ₐ[ℚ_[p]] M, ∀ x, φ x = ψ (x j) := by
  classical
  have hsum : ∑ j, φ (Pi.single j 1) = 1 := by
    have h := Finset.univ_sum_single (1 : Π j, L j)
    simp only [Pi.one_apply] at h
    rw [← map_sum, h, map_one]
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
    (f := fun j => φ (Pi.single j 1)) (by rw [hsum]; exact one_ne_zero)
  have hmul : ∀ x : Π j, L j, x * Pi.single j 1 = Pi.single j (x j) := fun x => by
    funext k
    by_cases hk : k = j
    · subst hk
      simp
    · simp [Pi.single_eq_of_ne hk]
  have hone : φ (Pi.single j 1) = 1 := by
    have h := congrArg φ (hmul (Pi.single j 1))
    rw [map_mul, Pi.single_eq_same] at h
    exact mul_left_cancel₀ hj (h.trans (mul_one _).symm)
  have hfac : ∀ x, φ x = φ (Pi.single j (x j)) := fun x => by
    rw [← hmul, map_mul, hone, mul_one]
  refine ⟨j,
    { toFun := fun a => φ (Pi.single j a)
      map_one' := hone
      map_mul' := fun a b => by rw [Pi.single_mul, map_mul]
      map_zero' := by rw [Pi.single_zero, map_zero]
      map_add' := fun a b => by rw [Pi.single_add, map_add]
      commutes' := fun r => by
        have h := hfac (algebraMap ℚ_[p] (Π j, L j) r)
        rw [AlgHom.commutes] at h
        exact h.symm }, hfac⟩

/-- **The order is read in the field components** (item 1 of the module docstring): for any
decomposition `e : W ≃ Π_j L_j` into finite extensions of `ℚ_p`, `u` has order `λ` if and only if
every component `e(u)_j` has spectral norm `p^{−λ}` in `L_j`. -/
theorem psuit_hasOrder_iff_components {W : Type*} [CommRing W] [Algebra ℚ_[p] W] {J : Type*}
    [Fintype J] (L : J → Type*) [∀ j, Field (L j)] [∀ j, Algebra ℚ_[p] (L j)]
    [∀ j, FiniteDimensional ℚ_[p] (L j)] (e : W ≃ₐ[ℚ_[p]] Π j, L j) (u : W) (lam : ℝ) :
    psuitHasOrder p u lam ↔ ∀ j, spectralNorm ℚ_[p] (L j) (e u j) = (p : ℝ) ^ (-lam) := by
  constructor
  · intro h j
    have : Algebra.IsAlgebraic ℚ_[p] (L j) := Algebra.IsAlgebraic.of_finite _ _
    have h' := h ((IsAlgClosed.lift (M := AlgebraicClosure ℚ_[p]) (R := ℚ_[p])
      (S := L j)).comp ((Pi.evalAlgHom ℚ_[p] L j).comp e.toAlgHom))
    rwa [AlgHom.comp_apply, psuit_spectralNorm_algHom] at h'
  · intro h φ
    obtain ⟨j, ψ, hψ⟩ := psuit_algHom_pi_factor p L (φ.comp e.symm.toAlgHom)
    have h1 : φ u = ψ (e u j) := by
      rw [← hψ]
      simp
    rw [h1, psuit_spectralNorm_algHom, h j]

end Order

/-! ## Orders of products of elements of the factors (item 2 of the module docstring) -/

section Tensor

variable (p : ℕ) [hp : Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] (K : ι → Type)
  [∀ i, Field (K i)] [∀ i, Algebra ℚ_[p] (K i)]

/-- A pure tensor is the product of its factors placed in the tensor product:
`⊗_i δ_i = ∏_i (1 ⊗ ⋯ ⊗ δ_i ⊗ ⋯ ⊗ 1)`. -/
theorem psuit_tprod_eq_prod (δ : ∀ i, K i) :
    PiTensorProduct.tprod ℚ_[p] δ =
      ∏ i, PiTensorProduct.singleAlgHom (R := ℚ_[p]) (A := K) i (δ i) := by
  have h := map_prod (PiTensorProduct.tprodMonoidHom (A := K) ℚ_[p])
    (fun i => Pi.mulSingle i (δ i)) Finset.univ
  rw [Finset.univ_prod_mulSingle] at h
  exact h

omit [Fintype ι] in
/-- **Products of elements of the factors** (item 2 of the module docstring): if `δ_i ∈ K_i` has
spectral norm `p^{−λ_i}` for `i ∈ S`, then the product `∏_{i ∈ S} δ_i` in `⊗_i K_i` has order
`∑_{i ∈ S} λ_i`. -/
theorem psuit_prod_single_hasOrder (S : Finset ι) (δ : ∀ i, K i) (lam : ι → ℝ)
    (hδ : ∀ i ∈ S, spectralNorm ℚ_[p] (K i) (δ i) = (p : ℝ) ^ (-lam i)) :
    psuitHasOrder p (∏ i ∈ S, PiTensorProduct.singleAlgHom (R := ℚ_[p]) (A := K) i (δ i))
      (∑ i ∈ S, lam i) := by
  intro φ
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  rw [map_prod, ← spectralMulAlgNorm_def, map_prod, ← Finset.sum_neg_distrib,
    Real.rpow_sum_of_pos hp0]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [spectralMulAlgNorm_def, ← hδ i hi, ← AlgHom.comp_apply, psuit_spectralNorm_algHom]

/-- **Pure tensors** (item 2 of the module docstring): if `δ_i` has spectral norm `p^{−λ_i}` for
every `i`, then `⊗_i δ_i` has order `∑_i λ_i`. -/
theorem psuit_tprod_hasOrder (δ : ∀ i, K i) (lam : ι → ℝ)
    (hδ : ∀ i, spectralNorm ℚ_[p] (K i) (δ i) = (p : ℝ) ^ (-lam i)) :
    psuitHasOrder p (PiTensorProduct.tprod ℚ_[p] δ) (∑ i, lam i) := by
  rw [psuit_tprod_eq_prod]
  exact psuit_prod_single_hasOrder p K Finset.univ δ lam fun i _ => hδ i

end Tensor

/-! ## The normalization in the field components (item 3 of the module docstring) -/

section Components

variable (p : ℕ) [hp : Fact p.Prime]

/-- **`(R_I)^∼` is the product of the rings of integers**: under a decomposition
`e : W ≃ Π_j L_j` into finite extensions of `ℚ_p`, the elements of `W` integral over `ℤ_p` are
those whose components all have spectral norm at most one. -/
theorem psuit_normalization_eq (W : Type*) [CommRing W] [Algebra ℚ_[p] W] {J : Type*}
    [Fintype J] (L : J → Type*) [∀ j, Field (L j)] [∀ j, Algebra ℚ_[p] (L j)]
    [∀ j, FiniteDimensional ℚ_[p] (L j)] (e : W ≃ₐ[ℚ_[p]] Π j, L j) :
    packetNormalizationSet p W =
      e ⁻¹' Set.univ.pi (fun j => {x | spectralNorm ℚ_[p] (L j) x ≤ 1}) := by
  rw [packet_normalization_eq_preimage p W L e]
  ext z
  show (∀ j ∈ Set.univ, e z j ∈ packetNormalizationSet p (L j)) ↔
    ∀ j ∈ Set.univ, spectralNorm ℚ_[p] (L j) (e z j) ≤ 1
  exact forall_congr' fun j => imp_congr_right fun _ =>
    volBridge_padicVolIntegral_iff p (L j) (e z j)

/-- Multiplying `(R_I)^∼` by `u` gives a subset of `t · (R_I)^∼` when the components of `u` and
`t` have the same spectral norms and those of `t` are nonzero. -/
theorem psuit_image_subset (W : Type*) [CommRing W] [Algebra ℚ_[p] W] {J : Type*}
    [Fintype J] (L : J → Type*) [∀ j, Field (L j)] [∀ j, Algebra ℚ_[p] (L j)]
    [∀ j, FiniteDimensional ℚ_[p] (L j)] (e : W ≃ₐ[ℚ_[p]] Π j, L j) (u t : W)
    (h : ∀ j, spectralNorm ℚ_[p] (L j) (e u j) = spectralNorm ℚ_[p] (L j) (e t j))
    (ht : ∀ j, e t j ≠ 0) :
    (fun w => u * w) '' packetNormalizationSet p W ⊆
      (fun w => t * w) '' packetNormalizationSet p W := by
  have halg : ∀ j, Algebra.IsAlgebraic ℚ_[p] (L j) := fun j => Algebra.IsAlgebraic.of_finite _ _
  rintro _ ⟨w, hw, rfl⟩
  refine ⟨e.symm (fun j => e u j / e t j * e w j), ?_, ?_⟩
  · rw [psuit_normalization_eq p W L e] at hw ⊢
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_ofPred_eq,
      AlgEquiv.apply_symm_apply] at hw ⊢
    intro j
    have hne : spectralNorm ℚ_[p] (L j) (e t j) ≠ 0 :=
      (spectralNorm_zero_lt (ht j) (Algebra.IsAlgebraic.isAlgebraic _)).ne'
    rw [psuit_spectralNorm_mul, psuit_spectralNorm_div, h j, div_self hne, one_mul]
    exact hw j
  · show t * e.symm (fun j => e u j / e t j * e w j) = u * w
    apply e.injective
    rw [map_mul, map_mul, AlgEquiv.apply_symm_apply]
    funext j
    simp only [Pi.mul_apply]
    field_simp [ht j]

/-- **Elements of the same order give the same multiple of `(R_I)^∼`** (item 3 of the module
docstring): in a finite formally unramified `ℚ_p`-algebra `W` (a finite product of finite
extensions of `ℚ_p`), if `u` and `t` both have order `λ`, then `u · (R_I)^∼ = t · (R_I)^∼`. -/
theorem psuit_image_eq_of_hasOrder {W : Type} [CommRing W] [Algebra ℚ_[p] W]
    [FiniteDimensional ℚ_[p] W] [Algebra.FormallyUnramified ℚ_[p] W] {u t : W} {lam : ℝ}
    (hu : psuitHasOrder p u lam) (ht : psuitHasOrder p t lam) :
    (fun w => u * w) '' packetNormalizationSet p W =
      (fun w => t * w) '' packetNormalizationSet p W := by
  obtain ⟨J, _, L, _, _, e, hL⟩ := packet_equiv_pi_of_unramified p W
  have : ∀ j, FiniteDimensional ℚ_[p] (L j) := fun j => (hL j).2
  have hu' := (psuit_hasOrder_iff_components p L e u lam).1 hu
  have ht' := (psuit_hasOrder_iff_components p L e t lam).1 ht
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hne : ∀ (x : W), (∀ j, spectralNorm ℚ_[p] (L j) (e x j) = (p : ℝ) ^ (-lam)) →
      ∀ j, e x j ≠ 0 := by
    intro x hx j h0
    have := hx j
    rw [h0, spectralNorm_zero] at this
    exact (Real.rpow_pos_of_pos hp0 _).ne' this.symm
  apply Set.Subset.antisymm
  · exact psuit_image_subset p W L e u t (fun j => (hu' j).trans (ht' j).symm) (hne t ht')
  · exact psuit_image_subset p W L e t u (fun j => (ht' j).trans (hu' j).symm) (hne u hu')

end Components

/-! ## Proposition 1.1 for every element of order `𝔡_{I*}` (item 4 of the module docstring) -/

section Proposition

variable (p : ℕ) [hp : Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] (K : ι → Type)
  [∀ i, Field (K i)] [∀ i, Algebra ℚ_[p] (K i)] [∀ i, FiniteDimensional ℚ_[p] (K i)]
  [∀ i, Algebra ℤ_[p] (K i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (K i)]

/-- The page's `𝔡_{I*} = ∑_{i ∈ I \ {*}} 𝔡_i`, with `𝔡_i = differentOrder` at the prime `P_i`
of `R_i = integralClosure ℤ_[p] K_i` (page 9). -/
noncomputable def psuitDiffSum (s : ι) (P : ∀ i, Ideal (integralClosure ℤ_[p] (K i))) : ℝ :=
  ∑ i ∈ Finset.univ.erase s, (letI := isDedekindDomain_ringOfIntegers_padic p (K i);
    letI := isTorsionFree_ringOfIntegers_padic p (K i);
    differentOrder ℤ_[p] (integralClosure ℤ_[p] (K i)) (P i))

/-- **The page's examples are suitable** (page 9: "such as products of elements
`p^{𝔡_i} ∈ R_i`, for `i ∈ I*`"): if `δ_i ∈ K_i` has spectral norm `p^{−𝔡_i}` for every `i ≠ *`,
then the product `∏_{i ∈ I*} δ_i` in `⊗_i K_i` has order `𝔡_{I*}`. -/
theorem psuit_examples_hasOrder (s : ι) (P : ∀ i, Ideal (integralClosure ℤ_[p] (K i)))
    (δ : ∀ i, K i)
    (hδ : ∀ i, i ≠ s → (letI := isDedekindDomain_ringOfIntegers_padic p (K i);
      letI := isTorsionFree_ringOfIntegers_padic p (K i);
      letI := spectralNorm.normedField ℚ_[p] (K i);
      ‖δ i‖ = (p : ℝ) ^ (-differentOrder ℤ_[p] (integralClosure ℤ_[p] (K i)) (P i)))) :
    psuitHasOrder p
      (∏ i ∈ Finset.univ.erase s, PiTensorProduct.singleAlgHom (R := ℚ_[p]) (A := K) i (δ i))
      (psuitDiffSum p K s P) :=
  psuit_prod_single_hasOrder p K _ δ _ fun i hi => hδ i (Finset.ne_of_mem_erase hi)

/-- **The pure tensors of `packetId_proposition1_1` are suitable**: if `δ_* = 1` and `δ_i` has
spectral norm `p^{−𝔡_i}` for `i ≠ *`, then `⊗_i δ_i` has order `𝔡_{I*}`. -/
theorem psuit_admissible_hasOrder (s : ι) (P : ∀ i, Ideal (integralClosure ℤ_[p] (K i)))
    (δ : ∀ i, K i) (hδs : δ s = 1)
    (hδ : ∀ i, i ≠ s → (letI := isDedekindDomain_ringOfIntegers_padic p (K i);
      letI := isTorsionFree_ringOfIntegers_padic p (K i);
      letI := spectralNorm.normedField ℚ_[p] (K i);
      ‖δ i‖ = (p : ℝ) ^ (-differentOrder ℤ_[p] (integralClosure ℤ_[p] (K i)) (P i)))) :
    psuitHasOrder p (PiTensorProduct.tprod ℚ_[p] δ) (psuitDiffSum p K s P) := by
  rw [psuit_tprod_eq_prod, ← Finset.prod_erase Finset.univ (a := s)
    (by rw [hδs, map_one])]
  exact psuit_examples_hasOrder p K s P δ hδ

/-- **Suitable elements exist**: for `s ∈ I` and primes `P_i` of the `R_i` over `p`, some element
of the packet has order `𝔡_{I*}` (so the hypotheses on `u` in `psuit_proposition1_1` are
satisfiable). -/
theorem psuit_exists_hasOrder (s : ι) (P : ∀ i, Ideal (integralClosure ℤ_[p] (K i)))
    [∀ i, (P i).IsPrime] [∀ i, (P i).LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    ∃ u : PiTensorProduct ℚ_[p] K, psuitHasOrder p u (psuitDiffSum p K s P) := by
  obtain ⟨δ, hδs, hδ⟩ := packetId_exists_admissible p K s P
  exact ⟨_, psuit_admissible_hasOrder p K s P δ hδs hδ⟩

/-- **IUT IV Proposition 1.1 for every suitable element** (page 9), "suitable `p^{𝔡_{I*}}`" read
as an element `u` of the packet `⊗_{ℚ_p} K_i` of order `𝔡_{I*}` in every field component
(`psuitHasOrder`; the page's examples are instances by `psuit_examples_hasOrder`). For any
finite `I` with `|I| ≥ 2`, `R_I = ⊗_{ℤ_p} R_i` (`packetIdZpTensor`), its total ring of fractions
realized as the packet through `packetIdMap`, `(R_I)^∼` the elements of the packet integral over
`R_I`, `s` the page's `*` and primes `P_i` of the `R_i` over `p`:
0. `R_I` is reduced;
1. the packet is the localization of `R_I` at its nonzero divisors;
2. `u · (R_I)^∼ ⊆ R_I` for every `u` of order `𝔡_{I*}`;
3. `R_I ⊆ (R_I)^∼`;
4. the set `u · (R_I)^∼` is the same for all `u` of order `𝔡_{I*}`. -/
theorem psuit_proposition1_1 (hI : 2 ≤ Fintype.card ι) (s : ι)
    (P : ∀ i, Ideal (integralClosure ℤ_[p] (K i)))
    [∀ i, (P i).IsPrime] [∀ i, (P i).LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    IsReduced (packetIdZpTensor p K) ∧
    (letI : Algebra (packetIdZpTensor p K) (PiTensorProduct ℚ_[p] K) :=
        (packetIdMap p K).toRingHom.toAlgebra;
      IsLocalization (nonZeroDivisors (packetIdZpTensor p K)) (PiTensorProduct ℚ_[p] K)) ∧
    (∀ u : PiTensorProduct ℚ_[p] K, psuitHasOrder p u (psuitDiffSum p K s P) →
      ∀ w, (packetIdMap p K).toRingHom.IsIntegralElem w →
        u * w ∈ Set.range (packetIdMap p K)) ∧
    (∀ x, (packetIdMap p K).toRingHom.IsIntegralElem (packetIdMap p K x)) ∧
    (∀ u u' : PiTensorProduct ℚ_[p] K, psuitHasOrder p u (psuitDiffSum p K s P) →
      psuitHasOrder p u' (psuitDiffSum p K s P) →
      (fun w => u * w) '' {w | (packetIdMap p K).toRingHom.IsIntegralElem w} =
        (fun w => u' * w) '' {w | (packetIdMap p K).toRingHom.IsIntegralElem w}) := by
  have hset : {w | (packetIdMap p K).toRingHom.IsIntegralElem w} =
      packetNormalizationSet p (PiTensorProduct ℚ_[p] K) :=
    Set.ext (packetId_isIntegralElem_iff p K)
  obtain ⟨h0, h1, h2, h3, -⟩ := packetId_proposition1_1 p K hI s P
  obtain ⟨δ, hδs, hδ⟩ := packetId_exists_admissible p K s P
  have ht := psuit_admissible_hasOrder p K s P δ hδs hδ
  have := packet_formallyUnramified p K
  refine ⟨h0, h1, fun u hu w hw => ?_, h3, fun u u' hu hu' => ?_⟩
  · have hmem : u * w ∈ (fun w => u * w) '' packetNormalizationSet p
        (PiTensorProduct ℚ_[p] K) :=
      ⟨w, (packetId_isIntegralElem_iff p K w).1 hw, rfl⟩
    rw [psuit_image_eq_of_hasOrder p hu ht] at hmem
    obtain ⟨w', hw', hw'eq⟩ := hmem
    rw [← hw'eq]
    exact h2 δ hδs hδ w' ((packetId_isIntegralElem_iff p K w').2 hw')
  · rw [hset, psuit_image_eq_of_hasOrder p hu ht, psuit_image_eq_of_hasOrder p hu' ht]

/-- **The suitable multiples agree with the pure-tensor ones**: for `u` of order `𝔡_{I*}` and a
pure tensor `⊗_i δ_i` as in `packetId_proposition1_1` (`δ_* = 1`, `δ_i` of spectral norm
`p^{−𝔡_i}` for `i ≠ *`), `u · (R_I)^∼ = (⊗_i δ_i) · (R_I)^∼`. -/
theorem psuit_image_eq_tprod (s : ι) (P : ∀ i, Ideal (integralClosure ℤ_[p] (K i)))
    (u : PiTensorProduct ℚ_[p] K) (hu : psuitHasOrder p u (psuitDiffSum p K s P))
    (δ : ∀ i, K i) (hδs : δ s = 1)
    (hδ : ∀ i, i ≠ s → (letI := isDedekindDomain_ringOfIntegers_padic p (K i);
      letI := isTorsionFree_ringOfIntegers_padic p (K i);
      letI := spectralNorm.normedField ℚ_[p] (K i);
      ‖δ i‖ = (p : ℝ) ^ (-differentOrder ℤ_[p] (integralClosure ℤ_[p] (K i)) (P i)))) :
    (fun w => u * w) '' {w | (packetIdMap p K).toRingHom.IsIntegralElem w} =
      (fun w => PiTensorProduct.tprod ℚ_[p] δ * w) ''
        {w | (packetIdMap p K).toRingHom.IsIntegralElem w} := by
  have hset : {w | (packetIdMap p K).toRingHom.IsIntegralElem w} =
      packetNormalizationSet p (PiTensorProduct ℚ_[p] K) :=
    Set.ext (packetId_isIntegralElem_iff p K)
  have := packet_formallyUnramified p K
  rw [hset]
  exact psuit_image_eq_of_hasOrder p hu (psuit_admissible_hasOrder p K s P δ hδs hδ)

end Proposition

/-! ## The page's setting: subfields of `ℚ̄_p` -/

section Closure

variable (p : ℕ) [hp : Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Proposition 1.1 for subfields of `ℚ̄_p`** (page 9: "`k_i ⊆ ℚ̄_p` a finite extension of
`ℚ_p`"): for finite intermediate fields `k_i` of `ℚ̄_p / ℚ_p`, clauses 2 and 4 of
`psuit_proposition1_1`, with `R_i` the integral closure of `ℤ_p` in `k_i`. -/
theorem psuit_proposition1_1_closure
    (k : ι → IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]))
    [∀ i, FiniteDimensional ℚ_[p] (k i)] (hI : 2 ≤ Fintype.card ι) (s : ι)
    (P : ∀ i, Ideal (integralClosure ℤ_[p] (k i)))
    [∀ i, (P i).IsPrime] [∀ i, (P i).LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    (∀ u : PiTensorProduct ℚ_[p] (fun i => k i),
      psuitHasOrder p u (psuitDiffSum p (fun i => k i) s P) →
      ∀ w, (packetIdMap p (fun i => k i)).toRingHom.IsIntegralElem w →
        u * w ∈ Set.range (packetIdMap p (fun i => k i))) ∧
    (∀ u u' : PiTensorProduct ℚ_[p] (fun i => k i),
      psuitHasOrder p u (psuitDiffSum p (fun i => k i) s P) →
      psuitHasOrder p u' (psuitDiffSum p (fun i => k i) s P) →
      (fun w => u * w) '' {w | (packetIdMap p (fun i => k i)).toRingHom.IsIntegralElem w} =
        (fun w => u' * w) '' {w | (packetIdMap p (fun i => k i)).toRingHom.IsIntegralElem w}) :=
  let h := psuit_proposition1_1 p (fun i => k i) hI s P
  ⟨h.2.2.1, h.2.2.2.2⟩

end Closure

end IUT.PaperIV.LocalFields
