import IUT.Audit.TensorOrderIndex
import IUT.PaperIV.LocalFields.TensorDifferentMany

/-!
# The exact index of `R_I` in its normalization for any number of factors

Source: C. Zeng, "An Integral-Structure Inflation in the Hull Operation of IUT Corollary 3.12",
hexagon 2610.00646, version 1: section 0 (notation, identity (0.1)), section 2 (the map `Φ`,
Lemma 2.1, Lemma 2.2, Definition 2.3), section 3 (Lemma 3.1), section 4 (Lemmas 4.1 and 4.2),
section 5 (Theorem 5.1 and Corollary 5.2). The paper was read from its TeX source and is cited
by section and statement number; it has no page render here, so its displays were checked
against the TeX source. IUT IV, Proposition 1.4 (i) (page 13) for the normalization of `μ^log`
(log-volumes "normalized [i.e., by dividing by the degree of the finite extension]", with
`μ^log((R_E)^∼) = 0`, `μ^log(p · (R_E)^∼) = −log(p)` on tensor products): page 13 was read and
checked against its rendered image; the normalization is the one the library's
`padicPacketMuLog` implements (see `IUT.PaperIV.LocalFields.Packets`).

This file continues `IUT.Audit.TensorOrderIndex` (two factors) to a finite index type `I` with
`n = |I| ≥ 1` factors, all equal to one finite Galois extension `K/ℚ_p` of degree `d` with group
`G`. The objects are the library's: the packet `⊗_{i ∈ I} K` is `PiTensorProduct ℚ_[p]`, `R_I` is
`tdManyIntegers` (the span of the pure tensors of integral elements, the image of
`⊗_{i ∈ I} O_K` over `ℤ_p`), and `(R_I)^∼` is `packetNormalizationSet` (the elements integral
over `ℤ_p`), both from `IUT.PaperIV.LocalFields.TensorDifferentMany` and
`IUT.PaperIV.LocalFields.Packets`. As in the two-factor file, `|𝔡_K|` of the paper is read as
`‖disc b‖⁻¹ = p ^ v` for an integral basis `b` of `K`, `v = v_p(disc b)`; the paper's index
`ρ_n = [P_n : Φ(O_n)]` is the index of `R_I` in `(R_I)^∼`, because `Φ` maps `(R_I)^∼` onto
`P_n = ∏_g O_K` (`tOrdMany_normalization_iff`).

## The map `Φ` and the route

The paper's `Φ(x_1 ⊗ ⋯ ⊗ x_n) = (x_1 · σ_{g_2}(x_2) ⋯ σ_{g_n}(x_n))_g`, `g ∈ G^{n−1}`, is
`tOrdManyPhi`, with a distinguished index `s ∈ I` in the role of the paper's first factor and
`G^{n−1}` realized as the functions `I ∖ {s} → G` (`tOrdManyPhi_tprod`). The paper proves
surjectivity by induction on `n` through the case `n = 2`; here the proof is direct: the packet
is split as `K ⊗ (⊗_{i ≠ s} K)` (`tdMany_splitMap_bijective` of the library), the characters
`⊗_{i ≠ s} y_i ↦ ∏_i g_i(y_i)` of `⊗_{i ≠ s} K` are pairwise distinct (`tOrdManyHom_injective`)
and as many as `dim ⊗_{i ≠ s} K = d^{n−1}`, so `x ⊗ y ↦ (x · χ(y))_χ` is injective by
independence of characters and bijective by dimension (`tOrdManyPhiGen_bijective`). Lemma 4.2 is
proved by induction on `n` through the same split and the two-factor `tOrdIdx_discr_tensor`, not
through triangularization of a Kronecker power as in the paper.

## What is proved

* `tOrdManyPhiGen_bijective`: for a finite-dimensional commutative `F`-algebra `C` and an
  injective family `ψ : J → (C →ₐ[F] K)` with `|J| = dim_F C`, `x ⊗ y ↦ (x · ψ_j(y))_j` is an
  isomorphism `K ⊗_F C ≅ ∏_J K`.
* `tOrdManyPhi`, `tOrdManyPhi_tprod`: Lemma 2.1 of the paper for `n` factors, the
  `ℚ_p`-algebra isomorphism `⊗_{i ∈ I} K ≅ ∏_{G^{I ∖ {s}}} K` with the printed formula.
* `tOrdMany_trace_phi`: Lemma 3.1 (trace preservation), `Tr(Φ(⊗_i x_i)) = ∏_i Tr(x_i)`; the
  trace of a pure tensor is `tdMany_trace_tprod` of the library.
* `tOrdMany_normalization_iff`: `z ∈ (R_I)^∼` if and only if every component of `Φ(z)` is
  integral; `tOrdMany_phi_integers`: Lemma 2.2 (`Φ(O_n) ⊆ P_n`).
* `tOrdMany_discr_pi`: Lemma 4.1 for any finite index set: the product basis of `∏_J K` has
  discriminant `disc b ^ |J|`; `tOrdMany_discr_normBasis`: its pullback by `Φ` has discriminant
  `disc b ^ {d^{n−1}}`.
* `tOrdMany_discr_tensor`: Lemma 4.2, the tensor basis of `⊗_{i ∈ I} K` has discriminant
  `disc b ^ {n d^{n−1}}`.
* `tOrdMany_integers_eq_lattice`, `tOrdMany_norm_eq_lattice`: `R_I` is the `ℤ_p`-span of the
  tensor basis; `(R_I)^∼` is the `ℤ_p`-span of the pullback of the product basis.
* `tOrdMany_index_sq`: **Theorem 5.1 for `n` factors**, without a square root:
  `[(R_I)^∼ : R_I]² = (‖disc b‖⁻¹)^{(n−1) d^{n−1}}`.
* `tOrdMany_muLog`: with the library's normalized log-volume on the packet (normalized at
  `(R_I)^∼`, divided by `dim = d^n`), `μ^log(R_I) = −((n−1)/2) · (v/d) · log p`.
* Auxiliary: `tOrdManyRingGrp`, `tOrdManyNormGrp` (`R_I` and `(R_I)^∼` as additive subgroups,
  with carriers `tdManyIntegers` and `packetNormalizationSet`), `tOrdMany_lattice_coord` (a basis
  lattice is open and compact in coordinates), `tOrdMany_muLog_lattice`
  (`μ^log(ℤ_p e₁) = −log [ℤ_p e₂ : ℤ_p e₁] / dim` for `ℤ_p e₁ ⊆ ℤ_p e₂`).

Nothing here concerns the hull operation of IUT III or whether any document is right about IUT
III Corollary 3.12: the file computes an index and its value under the normalization of IUT IV
Proposition 1.4 (i).

## Not proved

* Factors that are distinct fields, or a non-Galois `K`: `Φ` needs `|Gal(K/ℚ_p)| = d`.
* The identification `v/d = 𝔡` of the valuation of the discriminant over the degree with the
  order of the different (`differentOrder`), here; it is proved in
  `IUT.PaperIV.LocalFields.LocalDiscriminant` (`locDisc_valuation_discr`) and used in
  `IUT.Audit.TensorOrderIndexAllowance`. The value of `tOrdMany_muLog` is stated with `v/d`.
* That `tdManyIntegers` is the tensor product over `ℤ_p` of the rings of integers and that
  `packetNormalizationSet` is the normalization of `R_I` in its ring of fractions, here; both are
  proved in `IUT.PaperIV.LocalFields.PacketIdentifications` (`packetId_map_injective`,
  `packetId_isLocalization`, `packetId_isIntegralElem_iff`).
-/

namespace IUT.Audit.TensorOrderIndexMany

open IUT.PaperIV.LocalFields IUT.Audit.TensorOrderIndex IUT.Prerequisites.PadicVolume

/-! ## A splitting criterion for `K ⊗_F C` -/

section General

variable (F K C : Type*) [Field F] [Field K] [Algebra F K] [CommRing C] [Algebra F C]
  {J : Type*} [Fintype J]

/-- `x ⊗ y ↦ (x · ψ_j(y))_j`, from `K ⊗_F C` to `∏_{j ∈ J} K`, for a family `ψ` of `F`-algebra
maps `C → K`. -/
noncomputable def tOrdManyPhiGen (ψ : J → (C →ₐ[F] K)) : TensorProduct F K C →ₐ[F] (J → K) :=
  AlgHom.pi fun j => Algebra.TensorProduct.productMap (AlgHom.id F K) (ψ j)

omit [Fintype J] in
/-- `tOrdManyPhiGen ψ (x ⊗ y) = (x · ψ_j(y))_j`. -/
theorem tOrdManyPhiGen_tmul (ψ : J → (C →ₐ[F] K)) (x : K) (y : C) (j : J) :
    tOrdManyPhiGen F K C ψ (x ⊗ₜ[F] y) j = x * ψ j y := rfl

/-- **Injectivity by independence of characters**: if `ψ` is injective and `|J| = dim_F C`, then
`x ⊗ y ↦ (x · ψ_j(y))_j` is injective. -/
theorem tOrdManyPhiGen_injective [FiniteDimensional F C] (ψ : J → (C →ₐ[F] K))
    (hψ : Function.Injective ψ) (hcard : Fintype.card J = Module.finrank F C) :
    Function.Injective (tOrdManyPhiGen F K C ψ) := by
  classical
  let b := Module.finBasis F C
  let B := Algebra.TensorProduct.basis K b
  rw [injective_iff_map_eq_zero]
  intro z hz
  set c := B.repr z
  have hz' : z = ∑ j, c j ⊗ₜ[F] b j := by
    conv_lhs => rw [← B.sum_repr z]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hσ : ∀ σ : J, ∑ j, c j * ψ σ (b j) = 0 := by
    intro σ
    have := congrFun hz σ
    rw [hz', map_sum, Finset.sum_apply] at this
    simpa only [tOrdManyPhiGen_tmul, Pi.zero_apply] using this
  have hli : LinearIndependent K (fun σ : J => (ψ σ).toLinearMap) :=
    (linearIndependent_toLinearMap F C K).comp ψ hψ
  let T : (J → K) →ₗ[K] (Fin (Module.finrank F C) → K) :=
    { toFun := fun w j => ∑ σ, w σ * ψ σ (b j)
      map_add' := fun v w => by
        ext j
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun a w => by
        ext j
        simp [Finset.mul_sum, mul_assoc] }
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h0 : ∑ σ, w σ • (ψ σ).toLinearMap = 0 := by
      apply b.ext
      intro j
      have := congrFun hw j
      simpa [T, LinearMap.sum_apply] using this
    funext σ
    exact Fintype.linearIndependent_iff.1 hli w h0 σ
  have hcard' : Module.finrank K (J → K) = Module.finrank K (Fin (Module.finrank F C) → K) := by
    rw [Module.finrank_pi, Module.finrank_pi, Fintype.card_fin, hcard]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hcard').1 hT
  have hc : ∀ j, c j = 0 := by
    intro j
    obtain ⟨w, hw⟩ := hsurj (Pi.single j 1)
    calc c j = ∑ i, (Pi.single j (1 : K) : Fin (Module.finrank F C) → K) i * c i := by
          simp [Pi.single_apply]
      _ = ∑ i, (∑ σ, w σ * ψ σ (b i)) * c i := by rw [← hw]; rfl
      _ = ∑ σ, w σ * ∑ i, c i * ψ σ (b i) := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_comm.trans
            (Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun i _ => by ring)
      _ = 0 := by simp [hσ]
  rw [hz']
  simp [hc]

/-- **The splitting criterion**: if `ψ` is injective and `|J| = dim_F C`, then
`x ⊗ y ↦ (x · ψ_j(y))_j` is bijective from `K ⊗_F C` onto `∏_{j ∈ J} K`. -/
theorem tOrdManyPhiGen_bijective [FiniteDimensional F K] [FiniteDimensional F C]
    (ψ : J → (C →ₐ[F] K)) (hψ : Function.Injective ψ)
    (hcard : Fintype.card J = Module.finrank F C) :
    Function.Bijective (tOrdManyPhiGen F K C ψ) := by
  refine ⟨tOrdManyPhiGen_injective F K C ψ hψ hcard, ?_⟩
  have h : Module.finrank F (TensorProduct F K C) = Module.finrank F (J → K) := by
    rw [Module.finrank_tensorProduct, Module.finrank_pi_fintype, Finset.sum_const,
      Finset.card_univ, hcard, smul_eq_mul, mul_comm]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (tOrdManyPhiGen F K C ψ).toLinearMap) h).1 (tOrdManyPhiGen_injective F K C ψ hψ hcard)

end General

/-! ## The product basis of `∏_{j ∈ J} K` and its discriminant -/

section PiBasis

variable (F K : Type*) [Field F] [Field K] [Algebra F K] (J : Type*) [Fintype J] [DecidableEq J]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The basis `(k, j) ↦ b_k` in the `j`-component of `∏_{j ∈ J} K`. -/
noncomputable def tOrdManyPiBasis (b : Module.Basis κ F K) : Module.Basis (κ × J) F (J → K) :=
  (Pi.basis fun _ : J => b).reindex ((Equiv.sigmaEquivProd _ _).trans (Equiv.prodComm _ _))

variable {F K J}

omit [Fintype κ] [DecidableEq κ] in
/-- The vector `(k, j)` of `tOrdManyPiBasis b` is `b_k` in the `j`-component. -/
theorem tOrdManyPiBasis_apply (b : Module.Basis κ F K) (k : κ) (j : J) :
    tOrdManyPiBasis F K J b (k, j) = Pi.single j (b k) := by
  simp [tOrdManyPiBasis]

omit [DecidableEq J] [Fintype κ] [DecidableEq κ] in
/-- The `(k, j)`-coordinate of `w` is the `k`-th `b`-coordinate of `w j`. -/
theorem tOrdManyPiBasis_repr (b : Module.Basis κ F K) (w : J → K) (k : κ) (j : J) :
    (tOrdManyPiBasis F K J b).repr w (k, j) = b.repr (w j) k := by
  simp [tOrdManyPiBasis]

/-- The trace of `∏_{j ∈ J} K` over `F` is the sum of the traces of the components. -/
theorem tOrdMany_trace_pi (b : Module.Basis κ F K) (w : J → K) :
    Algebra.trace F (J → K) w = ∑ j, Algebra.trace F K (w j) := by
  rw [Algebra.trace_eq_matrix_trace (tOrdManyPiBasis F K J b), Matrix.trace,
    Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, tOrdManyPiBasis_apply,
    tOrdManyPiBasis_repr, Pi.mul_apply, Pi.single_eq_same]

/-- The trace matrix of `tOrdManyPiBasis b` is block diagonal with blocks the trace matrix of
`b`. -/
theorem tOrdMany_traceMatrix_pi (b : Module.Basis κ F K) :
    Algebra.traceMatrix F (tOrdManyPiBasis F K J b) =
      Matrix.blockDiagonal fun _ => Algebra.traceMatrix F b := by
  ext ⟨i, σ⟩ ⟨j, τ⟩
  rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, tOrdMany_trace_pi b,
    tOrdManyPiBasis_apply, tOrdManyPiBasis_apply, Matrix.blockDiagonal_apply]
  by_cases h : σ = τ
  · subst h
    rw [ite_eq_left_of_eq_true _ _ (eq_self σ), Algebra.traceMatrix_apply, Algebra.traceForm_apply,
      Finset.sum_eq_single σ]
    · rw [Pi.mul_apply, Pi.single_eq_same, Pi.single_eq_same]
    · intro ρ _ hρ
      rw [Pi.mul_apply, Pi.single_eq_of_ne hρ, zero_mul, map_zero]
    · intro h
      exact absurd (Finset.mem_univ σ) h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
    refine Finset.sum_eq_zero fun ρ _ => ?_
    rw [Pi.mul_apply]
    by_cases h1 : ρ = σ
    · subst h1
      rw [Pi.single_eq_of_ne h, mul_zero, map_zero]
    · rw [Pi.single_eq_of_ne h1, zero_mul, map_zero]

/-- **Lemma 4.1 of the paper, for any finite index set**: the product basis of `∏_{j ∈ J} K`
has discriminant `disc b ^ |J|`. -/
theorem tOrdMany_discr_pi (b : Module.Basis κ F K) :
    Algebra.discr F (tOrdManyPiBasis F K J b) = Algebra.discr F b ^ Fintype.card J := by
  rw [Algebra.discr_def, tOrdMany_traceMatrix_pi, Matrix.det_blockDiagonal, Finset.prod_const,
    Finset.card_univ, ← Algebra.discr_def]

end PiBasis

/-! ## The characters `⊗_{i ∈ M} K → K` -/

section Characters

variable (F K : Type*) [Field F] [Field K] [Algebra F K] (M : Type*) [Fintype M] [DecidableEq M]

/-- The multilinear map `(y_i)_i ↦ ∏_i g_i(y_i)` on `K^M`, for `g : M → Gal(K/F)`. -/
noncomputable def tOrdManyMulti (g : M → (K ≃ₐ[F] K)) :
    (Π _ : M, K) →ₘₗ[F] K :=
  (MultilinearMap.mkPiAlgebra F M K).compLinearMap fun i => (g i).toLinearMap

omit [DecidableEq M] in
/-- `tOrdManyMulti g y = ∏_i g_i(y_i)`. -/
theorem tOrdManyMulti_apply (g : M → (K ≃ₐ[F] K)) (y : M → K) :
    tOrdManyMulti F K M g y = ∏ i, g i (y i) := rfl

/-- The `F`-algebra map `⊗_{i ∈ M} K → K`, `⊗_i y_i ↦ ∏_i g_i(y_i)`, for `g : M → Gal(K/F)`. -/
noncomputable def tOrdManyHom (g : M → (K ≃ₐ[F] K)) :
    PiTensorProduct F (fun _ : M => K) →ₐ[F] K :=
  PiTensorProduct.liftAlgHom (tOrdManyMulti F K M g)
    (by rw [tOrdManyMulti_apply]; simp)
    (fun x y => by
      rw [tOrdManyMulti_apply, tOrdManyMulti_apply, tOrdManyMulti_apply,
        ← Finset.prod_mul_distrib]
      simp only [Pi.mul_apply, map_mul])

omit [DecidableEq M] in
/-- `tOrdManyHom g (⊗_i y_i) = ∏_i g_i(y_i)`. -/
theorem tOrdManyHom_tprod (g : M → (K ≃ₐ[F] K)) (y : M → K) :
    tOrdManyHom F K M g (PiTensorProduct.tprod F y) = ∏ i, g i (y i) := by
  simp only [tOrdManyHom, PiTensorProduct.liftAlgHom_apply, PiTensorProduct.lift.tprod,
    tOrdManyMulti_apply]

/-- Distinct `g` give distinct characters: `tOrdManyHom g` restricted to the `i`-th factor is
`g_i`. -/
theorem tOrdManyHom_injective : Function.Injective (tOrdManyHom F K M) := by
  intro g g' h
  funext i
  apply AlgEquiv.ext
  intro y
  have key : ∀ g : M → (K ≃ₐ[F] K),
      tOrdManyHom F K M g (PiTensorProduct.tprod F (Pi.mulSingle i y)) = g i y := by
    intro g
    rw [tOrdManyHom_tprod, Finset.prod_eq_single i]
    · rw [Pi.mulSingle_eq_same]
    · intro j _ hj
      rw [Pi.mulSingle_eq_of_ne hj, map_one]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have := DFunLike.congr_fun h (PiTensorProduct.tprod F (Pi.mulSingle i y))
  rwa [key, key] at this

end Characters


/-! ## The isomorphism `Φ : ⊗_{i ∈ I} K ≅ ∏_{G^{I ∖ {s}}} K` -/

section Phi

variable (p : ℕ) [hp : Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι)
  (K : Type) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

/-- `|Gal(K/ℚ_p)| = [K : ℚ_p]`. -/
theorem tOrdMany_card_gal [IsGalois ℚ_[p] K] :
    Fintype.card (K ≃ₐ[ℚ_[p]] K) = Module.finrank ℚ_[p] K := by
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]

/-- The number of components: `|G^{I ∖ {s}}| = dim ⊗_{i ≠ s} K`. -/
theorem tOrdMany_card_index [IsGalois ℚ_[p] K] :
    Fintype.card ({i // i ≠ s} → (K ≃ₐ[ℚ_[p]] K)) =
      Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] (fun _ : {i // i ≠ s} => K)) := by
  rw [Fintype.card_fun, tOrdMany_card_gal, packet_finrank p (fun _ : {i // i ≠ s} => K),
    Finset.prod_const, Finset.card_univ]

/-- **The isomorphism `Φ` of the paper** (section 2), for `n = |I|` factors with a distinguished
index `s` (the paper's first factor): `⊗_{i ∈ I} K ≅ ∏_{g ∈ G^{I ∖ {s}}} K`, the composite of the
split `⊗_i K ≅ K ⊗ (⊗_{i ≠ s} K)` and the splitting criterion for the characters
`⊗_{i ≠ s} y_i ↦ ∏_i g_i(y_i)`. -/
noncomputable def tOrdManyPhi [IsGalois ℚ_[p] K] :
    PiTensorProduct ℚ_[p] (fun _ : ι => K) ≃ₐ[ℚ_[p]]
      (({i // i ≠ s} → (K ≃ₐ[ℚ_[p]] K)) → K) :=
  (AlgEquiv.ofBijective _ (tdMany_splitMap_bijective p (fun _ : ι => K) s)).symm.trans
    (AlgEquiv.ofBijective _ (tOrdManyPhiGen_bijective ℚ_[p] K _
      (tOrdManyHom ℚ_[p] K {i // i ≠ s}) (tOrdManyHom_injective ℚ_[p] K {i // i ≠ s})
      (tOrdMany_card_index p s K)))

omit [Fintype ι] [FiniteDimensional ℚ_[p] K] in
/-- A pure tensor in split form: `⊗_i x_i = x_s ⊗ (⊗_{i ≠ s} x_i)`. -/
theorem tOrdMany_tprod_split (x : ι → K) :
    PiTensorProduct.tprod ℚ_[p] x = tdManySplitMap p (fun _ : ι => K) s
      (x s ⊗ₜ[ℚ_[p]] PiTensorProduct.tprod ℚ_[p] (fun i : {i // i ≠ s} => x i)) := by
  rw [tdMany_splitMap_tmul]
  congr 1
  funext j
  by_cases h : j = s
  · subst h
    simp
  · simp [h]

/-- **`Φ` on pure tensors**: `Φ(⊗_i x_i)_g = x_s · ∏_{i ≠ s} g_i(x_i)`, the formula of section 2
of the paper with `g_s = id`. -/
theorem tOrdManyPhi_tprod [IsGalois ℚ_[p] K] (x : ι → K)
    (g : {i // i ≠ s} → (K ≃ₐ[ℚ_[p]] K)) :
    tOrdManyPhi p s K (PiTensorProduct.tprod ℚ_[p] x) g = x s * ∏ i, g i (x i) := by
  rw [tOrdMany_tprod_split p s K x]
  have e1 : tdManySplitMap p (fun _ : ι => K) s
      (x s ⊗ₜ[ℚ_[p]] PiTensorProduct.tprod ℚ_[p] (fun i : {i // i ≠ s} => x i)) =
      AlgEquiv.ofBijective _ (tdMany_splitMap_bijective p (fun _ : ι => K) s)
        (x s ⊗ₜ[ℚ_[p]] PiTensorProduct.tprod ℚ_[p] (fun i : {i // i ≠ s} => x i)) := rfl
  rw [e1, tOrdManyPhi, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply,
    AlgEquiv.ofBijective_apply, tOrdManyPhiGen_tmul, tOrdManyHom_tprod]

/-- **Lemma 3.1 of the paper (trace preservation)**: `Tr(Φ(⊗_i x_i)) = ∏_i Tr(x_i)`, and this is
the trace of `⊗_i x_i` in `⊗_i K`. -/
theorem tOrdMany_trace_phi [IsGalois ℚ_[p] K] (x : ι → K) :
    Algebra.trace ℚ_[p] _ (tOrdManyPhi p s K (PiTensorProduct.tprod ℚ_[p] x)) =
        ∏ i, Algebra.trace ℚ_[p] K (x i) ∧
      Algebra.trace ℚ_[p] (PiTensorProduct ℚ_[p] (fun _ : ι => K))
        (PiTensorProduct.tprod ℚ_[p] x) = ∏ i, Algebra.trace ℚ_[p] K (x i) := by
  have h := tdMany_trace_tprod (F := ℚ_[p]) (fun _ : ι => K) x
  exact ⟨(Algebra.trace_eq_of_algEquiv _ _).trans h, h⟩

/-- **`(R_I)^∼` through `Φ`**: `z ∈ ⊗_i K` is integral over `ℤ_p` if and only if every component
`Φ(z)_g` is, that is, `Φ((R_I)^∼) = ∏_g O_K` (with Lemma 2.2 of the paper,
`Φ(R_I) ⊆ ∏_g O_K`, as the special case `z ∈ R_I`). -/
theorem tOrdMany_normalization_iff [IsGalois ℚ_[p] K]
    (z : PiTensorProduct ℚ_[p] (fun _ : ι => K)) :
    z ∈ packetNormalizationSet p (PiTensorProduct ℚ_[p] (fun _ : ι => K)) ↔
      ∀ g, padicVolIntegral p (tOrdManyPhi p s K z g) := by
  change padicVolIntegral p z ↔ _
  rw [← volBridge_padicVolIntegral_pi p (fun _ : {i // i ≠ s} → (K ≃ₐ[ℚ_[p]] K) => K)]
  exact ⟨fun h => padicVolIntegral_map p (tOrdManyPhi p s K).toAlgHom h,
    fun h => by simpa using padicVolIntegral_map p (tOrdManyPhi p s K).symm.toAlgHom h⟩

/-- **Lemma 2.2 of the paper** (`Φ(O_n) ⊆ P_n`): for `z ∈ R_I`, every component `Φ(z)_g` is
integral over `ℤ_p`. -/
theorem tOrdMany_phi_integers [IsGalois ℚ_[p] K] {z : PiTensorProduct ℚ_[p] (fun _ : ι => K)}
    (hz : z ∈ tdManyIntegers p (fun _ : ι => K)) (g : {i // i ≠ s} → (K ≃ₐ[ℚ_[p]] K)) :
    padicVolIntegral p (tOrdManyPhi p s K z g) :=
  (tOrdMany_normalization_iff p s K z).1 (tdMany_integers_subset p _ hz) g

end Phi

/-! ## `R_I` and `(R_I)^∼` as additive subgroups -/

section Groups

variable (p : ℕ) [hp : Fact p.Prime]

/-- `(R_I)^∼` as an additive subgroup: the elements of a commutative `ℚ_p`-algebra `W` integral
over `ℤ_p` (the carrier is `packetNormalizationSet p W`). -/
noncomputable def tOrdManyNormGrp (W : Type*) [CommRing W] [Algebra ℚ_[p] W] : AddSubgroup W where
  carrier := packetNormalizationSet p W
  add_mem' ha hb := RingHom.IsIntegralElem.add _ ha hb
  zero_mem' := RingHom.isIntegralElem_zero _
  neg_mem' ha := RingHom.IsIntegralElem.neg _ ha

/-- The carrier of `tOrdManyNormGrp` is `packetNormalizationSet`. -/
theorem tOrdManyNormGrp_coe (W : Type*) [CommRing W] [Algebra ℚ_[p] W] :
    (tOrdManyNormGrp p W : Set W) = packetNormalizationSet p W := rfl

/-- A `ℚ_p`-multiple of an integral element by a scalar of norm at most one is integral. -/
theorem tOrdMany_smul_integral {A : Type*} [CommRing A] [Algebra ℚ_[p] A] {r : ℚ_[p]}
    (hr : ‖r‖ ≤ 1) {y : A} (hy : padicVolIntegral p y) : padicVolIntegral p (r • y) := by
  have h : r = ((⟨r, hr⟩ : ℤ_[p]) : ℚ_[p]) := rfl
  rw [Algebra.smul_def, h]
  exact RingHom.IsIntegralElem.mul _ (tensorIdx_integral_algebraMap p _) hy

variable {ι : Type} [Fintype ι] [DecidableEq ι] (K : ι → Type) [∀ i, Field (K i)]
  [∀ i, Algebra ℚ_[p] (K i)] [∀ i, FiniteDimensional ℚ_[p] (K i)]

omit [Fintype ι] [∀ i, FiniteDimensional ℚ_[p] (K i)] in
/-- `R_I` is closed under negation when `I` is nonempty: `−(⊗_i x_i) = ⊗_i x'_i` with
`x'_s = −x_s`. -/
theorem tOrdMany_integers_neg (s : ι) {z : PiTensorProduct ℚ_[p] K}
    (hz : z ∈ tdManyIntegers p K) : -z ∈ tdManyIntegers p K := by
  unfold tdManyIntegers at hz ⊢
  rw [SetLike.mem_coe] at hz ⊢
  induction hz using AddSubmonoid.closure_induction with
  | mem w hw =>
    obtain ⟨x, hx, rfl⟩ := hw
    refine AddSubmonoid.subset_closure ⟨Function.update x s ((-1 : ℚ_[p]) • x s), fun i => ?_, ?_⟩
    · by_cases h : i = s
      · subst h
        rw [Function.update_self]
        exact tOrdMany_smul_integral p (by simp) (hx i)
      · rw [Function.update_of_ne h]
        exact hx i
    · rw [MultilinearMap.map_update_smul, Function.update_eq_self, RingHom.id_apply,
        neg_one_smul]
  | zero =>
    rw [neg_zero]
    exact zero_mem _
  | add a b _ _ ha hb =>
    rw [neg_add]
    exact add_mem ha hb

/-- `R_I` as an additive subgroup of `⊗_i K_i` (for `I` nonempty, witnessed by `s`); its carrier
is the library's `tdManyIntegers`, the span of the integral pure tensors. -/
noncomputable def tOrdManyRingGrp (s : ι) : AddSubgroup (PiTensorProduct ℚ_[p] K) :=
  { AddSubmonoid.closure {w | ∃ x : ∀ i, K i, (∀ i, padicVolIntegral p (x i)) ∧
      w = PiTensorProduct.tprod ℚ_[p] x} with
    neg_mem' := fun hz => tOrdMany_integers_neg p K s hz }

omit [Fintype ι] [∀ i, FiniteDimensional ℚ_[p] (K i)] in
/-- The carrier of `tOrdManyRingGrp` is `tdManyIntegers`. -/
theorem tOrdManyRingGrp_coe (s : ι) :
    (tOrdManyRingGrp p K s : Set (PiTensorProduct ℚ_[p] K)) = tdManyIntegers p K := rfl

end Groups

/-! ## The lattices -/

section Lattices

open Classical

variable (p : ℕ) [hp : Fact p.Prime]

/-- Reindexing a basis does not change its lattice. -/
theorem tOrdMany_lattice_reindex {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] {ι ι' : Type*}
    (e : Module.Basis ι ℚ_[p] V) (f : ι ≃ ι') :
    tOrdIdxLattice (e.reindex f) = tOrdIdxLattice e := by
  ext z
  simp only [tOrdIdx_mem_lattice, Module.Basis.repr_reindex_apply]
  constructor
  · intro h i
    simpa using h (f i)
  · intro h i
    exact h _

variable {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι)
  (K : Type) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
  {κ : Type} [Fintype κ] [DecidableEq κ]

omit [FiniteDimensional ℚ_[p] K] [DecidableEq κ] in
/-- **`R_I` is the lattice of the tensor basis**: for an integral basis `b` of `K`, `R_I` (the
library's `tdManyIntegers`, `n = |I|` factors) is the `ℤ_p`-span of the `⊗_i b_{j_i}`. -/
theorem tOrdMany_integers_eq_lattice [Nonempty ι] (b : Module.Basis κ ℚ_[p] K)
    (hb : tOrdIdxIntegralBasis p b) :
    tdManyIntegers p (fun _ : ι => K) =
      (tOrdIdxLattice (Basis.piTensorProduct fun _ : ι => b) : Set _) := by
  obtain ⟨s⟩ := ‹Nonempty ι›
  apply Set.Subset.antisymm
  · intro z hz
    have hgen : {w | ∃ x : ι → K, (∀ i, padicVolIntegral p (x i)) ∧
        w = PiTensorProduct.tprod ℚ_[p] x} ⊆
        ((tOrdIdxLattice (Basis.piTensorProduct fun _ : ι => b)).toAddSubmonoid : Set _) := by
      rintro _ ⟨x, hx, rfl⟩
      refine (tOrdIdx_mem_lattice _ _).2 fun j => ?_
      rw [Basis.piTensorProduct_repr_tprod_apply, norm_prod]
      exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) fun i _ => (hb (x i)).1 (hx i) (j i)
    exact (AddSubmonoid.closure_le.mpr hgen) hz
  · intro z hz
    rw [SetLike.mem_coe, tOrdIdx_mem_lattice] at hz
    rw [← (Basis.piTensorProduct fun _ : ι => b).sum_repr z]
    unfold tdManyIntegers
    rw [SetLike.mem_coe]
    refine sum_mem fun j _ => AddSubmonoid.subset_closure ?_
    set r := (Basis.piTensorProduct fun _ : ι => b).repr z j
    refine ⟨Function.update (fun i => b (j i)) s (r • (fun i => b (j i)) s), fun i => ?_, ?_⟩
    · by_cases h : i = s
      · subst h
        rw [Function.update_self]
        exact tOrdMany_smul_integral p (hz j) (tOrdIdxIntegralBasis_mem hb _)
      · rw [Function.update_of_ne h]
        exact tOrdIdxIntegralBasis_mem hb (j i)
    · rw [Basis.piTensorProduct_apply, MultilinearMap.map_update_smul, Function.update_eq_self]
      rfl

/-- The basis of `⊗_i K` that `Φ` sends to the product basis of `∏_g K`. -/
noncomputable def tOrdManyNormBasis [IsGalois ℚ_[p] K] (b : Module.Basis κ ℚ_[p] K) :
    Module.Basis (κ × ({i // i ≠ s} → (K ≃ₐ[ℚ_[p]] K))) ℚ_[p]
      (PiTensorProduct ℚ_[p] (fun _ : ι => K)) :=
  (tOrdManyPiBasis ℚ_[p] K _ b).map (tOrdManyPhi p s K).symm.toLinearEquiv

omit [Fintype κ] [DecidableEq κ] in
/-- Coordinates in `tOrdManyNormBasis b` are the `b`-coordinates of the components of `Φ`. -/
theorem tOrdManyNormBasis_repr [IsGalois ℚ_[p] K] (b : Module.Basis κ ℚ_[p] K)
    (z : PiTensorProduct ℚ_[p] (fun _ : ι => K)) (k : κ) (g : {i // i ≠ s} → (K ≃ₐ[ℚ_[p]] K)) :
    (tOrdManyNormBasis p s K b).repr z (k, g) = b.repr (tOrdManyPhi p s K z g) k := by
  rw [tOrdManyNormBasis, Module.Basis.map_repr]
  exact tOrdManyPiBasis_repr b _ k g

omit [Fintype κ] [DecidableEq κ] in
/-- **`(R_I)^∼` is the lattice of `tOrdManyNormBasis b`** (Galois case). -/
theorem tOrdMany_norm_eq_lattice [IsGalois ℚ_[p] K] (b : Module.Basis κ ℚ_[p] K)
    (hb : tOrdIdxIntegralBasis p b) :
    packetNormalizationSet p (PiTensorProduct ℚ_[p] (fun _ : ι => K)) =
      (tOrdIdxLattice (tOrdManyNormBasis p s K b) : Set _) := by
  ext z
  rw [tOrdMany_normalization_iff p s K, SetLike.mem_coe, tOrdIdx_mem_lattice]
  constructor
  · rintro h ⟨k, g⟩
    rw [tOrdManyNormBasis_repr]
    exact (hb _).1 (h g) k
  · intro h g
    refine (hb _).2 fun k => ?_
    have := h (k, g)
    rwa [tOrdManyNormBasis_repr] at this

/-- The discriminant of `tOrdManyNormBasis b` is `disc b ^ |G|^{n−1}` (Lemma 4.1 of the paper
transported by `Φ`). -/
theorem tOrdMany_discr_normBasis [IsGalois ℚ_[p] K] (b : Module.Basis κ ℚ_[p] K) :
    Algebra.discr ℚ_[p] (tOrdManyNormBasis p s K b) =
      Algebra.discr ℚ_[p] b ^ Fintype.card ({i // i ≠ s} → (K ≃ₐ[ℚ_[p]] K)) := by
  rw [← tOrdMany_discr_pi (J := {i // i ≠ s} → (K ≃ₐ[ℚ_[p]] K)) b,
    Algebra.discr_eq_discr_of_algEquiv (tOrdManyPiBasis ℚ_[p] K _ b) (tOrdManyPhi p s K).symm,
    tOrdManyNormBasis, Module.Basis.coe_map]
  rfl

end Lattices

/-! ## The discriminant of the tensor basis (Lemma 4.2) -/

section TensorDisc

variable (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [Algebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K]
  {κ : Type} [Fintype κ] [DecidableEq κ]

/-- `|I| = |I ∖ {s}| + 1`. -/
theorem tOrdMany_card_eq {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) :
    Fintype.card ι = Fintype.card {i // i ≠ s} + 1 := by
  rw [← Fintype.card_option, Fintype.card_congr (Equiv.optionSubtypeNe s)]

/-- **Lemma 4.2 of the paper** (`disc(O_n) = 𝔡_K ^ {n d^{n−1}}`): for a basis `b` of `K` with
`|b| = d` and a finite index set `I` with `|I| = m`, the tensor basis `⊗_{i ∈ I} b_{j_i}` of
`⊗_{i ∈ I} K` has discriminant `disc b ^ {m · d^{m−1}}`. By induction on `m`, through the split
`⊗_I K ≅ K ⊗ (⊗_{I ∖ {s}} K)` and the two-factor formula `tOrdIdx_discr_tensor`. -/
theorem tOrdMany_discr_tensor (b : Module.Basis κ ℚ_[p] K) :
    ∀ (m : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = m →
      Algebra.discr ℚ_[p] (Basis.piTensorProduct fun _ : ι => b) =
        Algebra.discr ℚ_[p] b ^ (m * Fintype.card κ ^ (m - 1)) := by
  intro m
  induction m with
  | zero =>
    intro ι _ _ hι
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hι
    have : Unique (ι → κ) := Pi.uniqueOfIsEmpty _
    rw [zero_mul, pow_zero, Algebra.discr_def, Matrix.det_unique, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply]
    have h1 : (Basis.piTensorProduct fun _ : ι => b) default = 1 := by
      rw [Basis.piTensorProduct_apply, PiTensorProduct.one_def]
      congr 1
      funext i
      exact isEmptyElim i
    rw [h1, mul_one, ← map_one (algebraMap ℚ_[p] (PiTensorProduct ℚ_[p] fun _ : ι => K)),
      Algebra.trace_algebraMap, packet_finrank p (fun _ : ι => K)]
    simp
  | succ m ih =>
    intro ι _ _ hι
    obtain ⟨s⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    have hι' : Fintype.card {i // i ≠ s} = m := by
      have := tOrdMany_card_eq s
      omega
    have hcomp : (Basis.piTensorProduct fun _ : ι => b) ∘ (Equiv.funSplitAt s κ).symm =
        AlgEquiv.ofBijective _ (tdMany_splitMap_bijective p (fun _ : ι => K) s) ∘
          (b.tensorProduct (Basis.piTensorProduct fun _ : {i // i ≠ s} => b)) := by
      funext ⟨k, j⟩
      simp only [Function.comp_apply, Module.Basis.tensorProduct_apply,
        Basis.piTensorProduct_apply]
      rw [AlgEquiv.ofBijective_apply, tdMany_splitMap_tmul]
      congr 1
      funext i
      by_cases h : i = s
      · subst h
        simp
      · simp [h]
    have h1 := Algebra.discr_reindex ℚ_[p] (Basis.piTensorProduct fun _ : ι => b)
      (Equiv.funSplitAt s κ)
    rw [← h1, hcomp, ← Algebra.discr_eq_discr_of_algEquiv, tOrdIdx_discr_tensor,
      ih _ hι', Fintype.card_fun, hι', ← pow_mul, ← pow_add]
    congr 1
    cases m with
    | zero => simp
    | succ k =>
      rw [Nat.add_sub_cancel, Nat.add_sub_cancel]
      ring

end TensorDisc

/-! ## Theorem 5.1 for `n` factors -/

section Index

variable (p : ℕ) [hp : Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι)
  (K : Type) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
  {κ : Type} [Fintype κ] [DecidableEq κ]

/-- **The two lattices with their discriminants** (Galois case): for an integral basis `b` of `K`
with `|b| = d` and `m = |I| − 1`, `R_I` is the lattice of the tensor basis `B`, `(R_I)^∼` is the
lattice of a basis `N` with the same index set, `disc B = disc b ^ {(m+1) d^m}` and
`disc N = disc b ^ {d^m}`. -/
theorem tOrdMany_lattices [IsGalois ℚ_[p] K] (b : Module.Basis κ ℚ_[p] K)
    (hb : tOrdIdxIntegralBasis p b) :
    ∃ N : Module.Basis (ι → κ) ℚ_[p] (PiTensorProduct ℚ_[p] (fun _ : ι => K)),
      tOrdManyRingGrp p (fun _ : ι => K) s = tOrdIdxLattice (Basis.piTensorProduct fun _ => b) ∧
      tOrdManyNormGrp p (PiTensorProduct ℚ_[p] (fun _ : ι => K)) = tOrdIdxLattice N ∧
      Algebra.discr ℚ_[p] (Basis.piTensorProduct fun _ : ι => b) =
        Algebra.discr ℚ_[p] b ^
          ((Fintype.card {i // i ≠ s} + 1) * Fintype.card κ ^ Fintype.card {i // i ≠ s}) ∧
      Algebra.discr ℚ_[p] N =
        Algebra.discr ℚ_[p] b ^ (Fintype.card κ ^ Fintype.card {i // i ≠ s}) := by
  classical
  have hd : Module.finrank ℚ_[p] K = Fintype.card κ := Module.finrank_eq_card_basis b
  have hcard : Fintype.card (κ × ({i // i ≠ s} → (K ≃ₐ[ℚ_[p]] K))) = Fintype.card (ι → κ) := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, tOrdMany_card_gal, hd,
      tOrdMany_card_eq s, pow_succ, mul_comm]
  let f := Fintype.equivOfCardEq hcard
  refine ⟨(tOrdManyNormBasis p s K b).reindex f, ?_, ?_, ?_, ?_⟩
  · have : Nonempty ι := ⟨s⟩
    exact SetLike.coe_injective (tOrdMany_integers_eq_lattice p K b hb)
  · apply SetLike.coe_injective
    rw [tOrdMany_lattice_reindex]
    exact tOrdMany_norm_eq_lattice p s K b hb
  · rw [tOrdMany_discr_tensor p K b _ ι (tOrdMany_card_eq s), Nat.add_sub_cancel]
  · rw [Module.Basis.coe_reindex, Algebra.discr_reindex, tOrdMany_discr_normBasis,
      Fintype.card_fun, tOrdMany_card_gal, hd]

/-- **Theorem 5.1 of the paper for `n` factors**, on the library's objects: for `K/ℚ_p` finite
Galois of degree `d` with an integral basis `b`, and a finite index set `I` with `n = |I| ≥ 1`
(`s ∈ I`), the index of `R_I` (`tdManyIntegers`) in `(R_I)^∼` (`packetNormalizationSet`) satisfies
`[(R_I)^∼ : R_I]² = (‖disc b‖⁻¹)^{(n−1) d^{n−1}}`, that is,
`ρ_n = |𝔡_K|^{(n−1) d^{n−1}/2}` with `|𝔡_K| = ‖disc b‖⁻¹ = p^{v_p(disc K)}`. -/
theorem tOrdMany_index_sq [IsGalois ℚ_[p] K] (b : Module.Basis κ ℚ_[p] K)
    (hb : tOrdIdxIntegralBasis p b) :
    (((tOrdManyRingGrp p (fun _ : ι => K) s).relIndex
        (tOrdManyNormGrp p (PiTensorProduct ℚ_[p] (fun _ : ι => K))) : ℝ)) ^ 2 =
      (‖Algebra.discr ℚ_[p] b‖⁻¹) ^
        ((Fintype.card ι - 1) * Module.finrank ℚ_[p] K ^ (Fintype.card ι - 1)) := by
  obtain ⟨N, hR, hN, hdB, hdN⟩ := tOrdMany_lattices p s K b hb
  have hle : tOrdIdxLattice (Basis.piTensorProduct fun _ : ι => b) ≤ tOrdIdxLattice N := by
    rw [← hR, ← hN]
    exact fun z hz => tdMany_integers_subset p (fun _ : ι => K) hz
  rw [hR, hN, tOrdIdx_relIndex_eq _ _ hle, tOrdMany_card_eq s, Nat.add_sub_cancel,
    Module.finrank_eq_card_basis b]
  set m := Fintype.card {i // i ≠ s}
  set d := Fintype.card κ
  have hch := tOrdIdx_discr_change (Basis.piTensorProduct fun _ : ι => b) N
  rw [hdB, hdN] at hch
  have hn := congrArg norm hch
  rw [norm_mul, norm_pow, norm_pow, norm_pow] at hn
  set D := ‖Algebra.discr ℚ_[p] b‖
  set t := ‖N.det (Basis.piTensorProduct fun _ : ι => b)‖
  have hD : D ≠ 0 := norm_ne_zero_iff.2 (Algebra.discr_not_zero_of_basis ℚ_[p] b)
  have ht : t ^ 2 = D ^ (m * d ^ m) := by
    have h2 : D ^ ((m + 1) * d ^ m) = D ^ (d ^ m) * D ^ (m * d ^ m) := by
      rw [← pow_add]
      congr 1
      ring
    rw [h2, mul_comm (t ^ 2)] at hn
    exact (mul_left_cancel₀ (pow_ne_zero _ hD) hn).symm
  rw [inv_pow, ht, inv_pow]

end Index

/-! ## The normalized log-volume of `R_I` -/

section MuLog

open MeasureTheory

variable (p : ℕ) [hp : Fact p.Prime]

/-- **A basis lattice is open and compact in coordinates**: for a basis `e` of a
finite-dimensional `ℚ_p`-vector space `W`, the image of its `ℤ_p`-lattice in the coordinates of
`Module.finBasis` (those of `padicPacketMuLog`) is the preimage of the unit polydisc under a
linear isomorphism. -/
theorem tOrdMany_lattice_coord {W : Type*} [AddCommGroup W] [Module ℚ_[p] W]
    [FiniteDimensional ℚ_[p] W] {ι : Type*} [Fintype ι] (e : Module.Basis ι ℚ_[p] W) :
    IsOpen ((Module.finBasis ℚ_[p] W).equivFun '' (tOrdIdxLattice e : Set W)) ∧
      IsCompact ((Module.finBasis ℚ_[p] W).equivFun '' (tOrdIdxLattice e : Set W)) := by
  set c := (Module.finBasis ℚ_[p] W).equivFun
  set T : (Fin (Module.finrank ℚ_[p] W) → ℚ_[p]) ≃L[ℚ_[p]] (ι → ℚ_[p]) :=
    (c.symm.trans e.equivFun).toContinuousLinearEquiv
  set U : Set (ι → ℚ_[p]) := Set.univ.pi fun _ => Metric.closedBall 0 1
  have hU : c '' (tOrdIdxLattice e : Set W) = T ⁻¹' U := by
    ext v
    simp only [Set.mem_image, Set.mem_preimage, U, Set.mem_univ_pi, Metric.mem_closedBall,
      dist_zero_right, SetLike.mem_coe, tOrdIdx_mem_lattice]
    constructor
    · rintro ⟨w, hw, rfl⟩ i
      simpa [T] using hw i
    · intro h
      exact ⟨c.symm v, fun i => by simpa [T] using h i, by simp⟩
  have hUo : IsOpen U :=
    isOpen_set_pi Set.finite_univ fun _ _ => IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hUc : IsCompact U := isCompact_univ_pi fun _ => isCompact_closedBall _ _
  rw [hU]
  refine ⟨hUo.preimage T.continuous, ?_⟩
  rw [← T.image_symm_eq_preimage]
  exact hUc.image T.symm.continuous

/-- **`μ^log` of a sublattice**: for bases `e₁`, `e₂` of `W` with `ℤ_p e₁ ⊆ ℤ_p e₂`, the
log-volume normalized at `ℤ_p e₂` and divided by `dim W` is
`μ^log(ℤ_p e₁) = −log [ℤ_p e₂ : ℤ_p e₁] / dim W`. -/
theorem tOrdMany_muLog_lattice {W : Type*} [AddCommGroup W] [Module ℚ_[p] W]
    [FiniteDimensional ℚ_[p] W] [MeasurableSpace (Fin (Module.finrank ℚ_[p] W) → ℚ_[p])]
    [BorelSpace (Fin (Module.finrank ℚ_[p] W) → ℚ_[p])]
    (μ : Measure (Fin (Module.finrank ℚ_[p] W) → ℚ_[p])) [μ.IsAddHaarMeasure]
    {ι : Type*} [Fintype ι] (e₁ e₂ : Module.Basis ι ℚ_[p] W)
    (h : tOrdIdxLattice e₁ ≤ tOrdIdxLattice e₂) :
    padicPacketMuLog p W μ (tOrdIdxLattice e₂ : Set W) (tOrdIdxLattice e₁ : Set W) =
      -Real.log ((tOrdIdxLattice e₁).relIndex (tOrdIdxLattice e₂)) /
        Module.finrank ℚ_[p] W := by
  set c := (Module.finBasis ℚ_[p] W).equivFun
  set H := (tOrdIdxLattice e₁).map c.toAddEquiv.toAddMonoidHom
  set N := (tOrdIdxLattice e₂).map c.toAddEquiv.toAddMonoidHom
  have hH : (H : Set _) = c '' (tOrdIdxLattice e₁ : Set W) := by
    rw [AddSubgroup.coe_map]
    rfl
  have hN : (N : Set _) = c '' (tOrdIdxLattice e₂ : Set W) := by
    rw [AddSubgroup.coe_map]
    rfl
  have hle : H ≤ N := AddSubgroup.map_mono h
  obtain ⟨hHo, hHc⟩ := tOrdMany_lattice_coord p e₁
  obtain ⟨-, hNc⟩ := tOrdMany_lattice_coord p e₂
  rw [← hH] at hHo hHc
  rw [← hN] at hNc
  have := tensorIdx_finite_quotient hle hHo hNc
  have hmeas := tensorIdx_measure_eq_relIndex μ hle hHo.measurableSet
  have hidx : H.relIndex N = (tOrdIdxLattice e₁).relIndex (tOrdIdxLattice e₂) :=
    AddSubgroup.relIndex_map_map_of_injective _ _ c.toAddEquiv.injective
  have hn : H.relIndex N ≠ 0 := Nat.card_pos.ne'
  rw [hidx, hH, hN] at hmeas
  rw [hidx] at hn
  rw [hH] at hHo hHc
  have h0 : μ (c '' (tOrdIdxLattice e₁ : Set W)) ≠ 0 :=
    hHo.measure_ne_zero μ ⟨0, 0, zero_mem _, map_zero c⟩
  have h1 : μ (c '' (tOrdIdxLattice e₁ : Set W)) ≠ ⊤ := hHc.measure_lt_top.ne
  unfold padicPacketMuLog padicMuLog
  rw [hmeas, ENNReal.toReal_mul, Module.finrank_fin_fun, ENNReal.toReal_natCast]
  have ha := ENNReal.toReal_pos h0 h1
  rw [div_mul_cancel_right₀ ha.ne', Real.log_inv]

variable {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι)
  (K : Type) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
  {κ : Type} [Fintype κ] [DecidableEq κ]

/-- **The normalized log-volume of `R_I` for `n` factors** (Galois case): with `μ^log` normalized
at `(R_I)^∼` and divided by the dimension `d^n` (IUT IV Proposition 1.4 (i), page 13; the
library's `padicPacketMuLog` on the packet `⊗_{i ∈ I} K`), for an integral basis `b` of `K` with
`v = v_p(disc b)`: `μ^log(R_I) = −((n−1)/2) · (v/d) · log p`. -/
theorem tOrdMany_muLog [IsGalois ℚ_[p] K] [Nonempty ι]
    [MeasurableSpace (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] (fun _ : ι => K))) →
      ℚ_[p])]
    [BorelSpace (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] (fun _ : ι => K))) → ℚ_[p])]
    (μ : Measure (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] (fun _ : ι => K))) → ℚ_[p]))
    [μ.IsAddHaarMeasure] (b : Module.Basis κ ℚ_[p] K) (hb : tOrdIdxIntegralBasis p b) :
    padicPacketMuLog p (PiTensorProduct ℚ_[p] (fun _ : ι => K)) μ
        (packetNormalizationSet p (PiTensorProduct ℚ_[p] (fun _ : ι => K)))
        (tdManyIntegers p (fun _ : ι => K)) =
      -(((Fintype.card ι - 1 : ℕ) : ℝ) / 2) *
        ((Algebra.discr ℚ_[p] b).valuation / Module.finrank ℚ_[p] K) * Real.log p := by
  obtain ⟨s⟩ := ‹Nonempty ι›
  obtain ⟨N, hR, hN, -, -⟩ := tOrdMany_lattices p s K b hb
  have hle : tOrdIdxLattice (Basis.piTensorProduct fun _ : ι => b) ≤ tOrdIdxLattice N := by
    rw [← hR, ← hN]
    exact fun z hz => tdMany_integers_subset p (fun _ : ι => K) hz
  have hidx := tOrdMany_index_sq p s K b hb
  rw [hR, hN] at hidx
  rw [← tOrdManyRingGrp_coe p _ s, ← tOrdManyNormGrp_coe, hR, hN,
    tOrdMany_muLog_lattice p μ _ _ hle, packet_finrank p (fun _ : ι => K), Finset.prod_const,
    Finset.card_univ, tOrdMany_card_eq s, Nat.add_sub_cancel]
  set m := Fintype.card {i // i ≠ s}
  rw [tOrdMany_card_eq s, Nat.add_sub_cancel] at hidx
  set x : ℝ := ((tOrdIdxLattice (Basis.piTensorProduct fun _ : ι => b)).relIndex
    (tOrdIdxLattice N) : ℝ)
  set D := ‖Algebra.discr ℚ_[p] b‖
  set d := Module.finrank ℚ_[p] K
  have hD : 0 < D := norm_pos_iff.2 (Algebra.discr_not_zero_of_basis ℚ_[p] b)
  have hx0 : 0 ≤ x := Nat.cast_nonneg _
  have hxpos : 0 < x := by
    rcases hx0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hidx
      have : (0 : ℝ) < (D⁻¹) ^ (m * d ^ m) := pow_pos (inv_pos.2 hD) _
      rw [← hidx] at this
      norm_num at this
  have hl := congrArg Real.log hidx
  rw [Real.log_pow, Real.log_pow, Real.log_inv] at hl
  have hDv : Real.log D = -((Algebra.discr ℚ_[p] b).valuation : ℝ) * Real.log p := by
    rw [show D = ‖Algebra.discr ℚ_[p] b‖ from rfl,
      Padic.norm_eq_zpow_neg_valuation (Algebra.discr_not_zero_of_basis ℚ_[p] b),
      Real.log_zpow]
    push_cast
    ring
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Module.finrank_pos
  rw [hDv] at hl
  push_cast at hl ⊢
  have hlx : Real.log x = (m : ℝ) * (d : ℝ) ^ m *
      (((Algebra.discr ℚ_[p] b).valuation : ℝ) * Real.log p) / 2 := by
    linarith
  rw [hlx]
  field_simp
  ring

end MuLog
end IUT.Audit.TensorOrderIndexMany
