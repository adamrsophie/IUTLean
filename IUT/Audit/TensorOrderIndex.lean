import Mathlib
import IUT.PaperIV.LocalFields.TensorIndex

/-!
# The exact index of `R_E` in its normalization for two factors

Source: C. Zeng, "An Integral-Structure Inflation in the Hull Operation of IUT Corollary 3.12",
hexagon 2610.00646, version 1, Theorem 5.1 (section 5), Lemmas 4.1 and 4.2, identity (0.1),
sections 8.4 and 10. The paper was read from its TeX source and is cited by section and
theorem number; it has no page render here. IUT IV, Proposition 1.1 (pages 9 and 10),
Proposition 1.4 (i) (page 13), the proof of Proposition 1.4 (iii) (page 14) and Remark 1.7.1
(pages 17 and 18); IUT III, Remark 3.1.1 (ii) (pages 94 and 95) and Proposition 3.9 (i), (ii)
(pages 115 and 116). All of these IUT pages were checked against page renders.

For finite extensions `K₁`, `K₂` of `ℚ_p` the library defines `R_E = R₁ ⊗_{ℤ_p} R₂` as a subring
of `K₁ ⊗[ℚ_p] K₂` (`tensorIdxRing`) and its normalization `(R_E)^∼`, the elements integral over
`ℤ_p` (`tensorIdxNormRing`). This file computes the index `[(R_E)^∼ : R_E]` exactly through
discriminants of the trace form. Throughout, `|𝔡_K|` of the paper is read as
`‖disc b‖⁻¹ = p ^ v`, with `b` an integral basis of `K` and `v = v_p(disc K)`.

## What is proved

* `tOrdIdx_relIndex_eq`: for `ℚ_p`-bases `e₁`, `e₂` of a vector space with `ℤ_p`-spans
  `L₁ ≤ L₂`, `[L₂ : L₁] = ‖det_{e₂} e₁‖⁻¹` (Smith normal form over `ℤ_p`).
* `tOrdIdx_discr_change`, `tOrdIdx_discr_tensor`: `disc e₁ = (det_{e₂} e₁)² disc e₂` (the
  identity (0.1) of the paper) and `disc (b ⊗ c) = disc b ^ {d₂} · disc c ^ {d₁}`.
* `tOrdIdxPhiEquiv`, `tOrdIdx_discr_pi`: for `K/F` finite Galois, `K ⊗_F K ≅ ∏_{Gal} K` by
  `x ⊗ y ↦ (x σ(y))_σ`, and the product basis has discriminant `disc b ^ [K : F]`.
* `tOrdIdx_exists_integralBasis`: every finite extension of `ℚ_p` has an integral basis.
* `tOrdIdx_ring_eq_lattice`: `R_E` is the `ℤ_p`-span of the `b_i ⊗ c_k`.
* `tOrdIdx_index_sq_general` (no Galois hypothesis): for any basis `n` whose `ℤ_p`-span is
  `(R_E)^∼`, `[(R_E)^∼ : R_E]² · ‖disc b‖^{d₂} · ‖disc c‖^{d₁} = ‖disc n‖`.
* `tOrdIdx_index_sq_galois`: Theorem 5.1 of the paper for `n = 2`: for `K/ℚ_p` Galois of
  degree `d`, `[(R_E)^∼ : R_E]² = (‖disc b‖⁻¹)^d = p ^ {v d}`.
* `tOrdIdx_muLog_galois`, `tOrdIdx_muLog_galois_valuation`: with the normalization of IUT IV
  Proposition 1.4 (i), page 13, `μ^log(R_E) = log ‖disc b‖ / (2 d) = −(1/2) (v/d) log p`.
* `tOrdIdx_sum_two_pow`: equation (closed) of section 10.2 of the paper,
  `∑_{j ≤ J} j 2^j = (J − 1) 2^{J+1} + 2`, as printed.
* Model tests (real arithmetic, not statements of either paper): the raw exponent
  `(j/2) d^j v` of `n = j + 1` factors and its sum, which is of order `J d^J`
  (`tOrdIdx_rawSum_ge`, `tOrdIdx_sum_pow_bounds`, `tOrdIdx_sum_pow_closed`); the value divided by
  the dimension `d^{j+1}` (`tOrdIdx_norm_eq_raw_div`), which is `(j/2)(v/d)`, half of `j (v/d)`
  (`tOrdIdx_normExp_eq_half`), with sum `(v/d) J (J+1)/4` (`tOrdIdx_normSum_eq`).

## What the IUT pages print about the normalization

* IUT IV page 13, Proposition 1.4 (i): log-volumes are "normalized [i.e., by dividing by the
  degree of the finite extension]", with `μ^log((R_E)^∼) = 0` and `μ^log(p·(R_E)^∼) = −log(p)`
  for tensor products. Page 14 uses `μ^log(R_I) ≤ μ^log((R_I)^∼) = 0`.
* IUT IV page 9, Proposition 1.1: `p^{𝔡_{I*}} · (R_I)^∼ ⊆ R_I ⊆ (R_I)^∼`, with no ceiling.
* IUT IV page 17, Remark 1.7.1: the computations of §1 "are performed relative to normalized
  log-volumes as discussed in Proposition 1.4, (i)", and the weights of IUT III Remark 3.1.1
  (ii) "must be replaced" by `[(F_mod)_v : ℚ_{v_ℚ}]`; page 18 gives the normalized weights.
* IUT III page 94, Remark 3.1.1 (ii): weights `[K_v : (F_mod)_v]^{-1}` and normalized weights,
  for tensor products `1/∏_α [K_{v_α} : (F_mod)_{v_α}]`.
* IUT III page 115, Proposition 3.9 (i): the log-volumes of the local holomorphic integral
  structures are zero, "normalized so that multiplication ... by p_v corresponds to adding
  −log(p_v)" (the packet-normalization); page 116 gives the procession-normalization.

## Not proved

* The `n`-factor formula `ρ_n = |𝔡_K|^{(n−1) d^{n−1}/2}`: the library's `R_E` has two factors;
  the `n`-fold version needs iterated tensor products of the Galois splitting.
* The identification `v/d = 𝔡` of the valuation of the discriminant with the order of the
  different: the pinned Mathlib relates the norm of the different to the discriminant for
  number fields only (`NumberField.absNorm_differentIdeal`). So the statement "half of the
  allowance `𝔡_{I*} log p` of Proposition 1.1" is a model test here.
* Which normalization the hull step of IUT III Corollary 3.12 uses: this file computes the
  index and its value under the normalization of Proposition 1.4 (i) only.
-/

namespace IUT.Audit.TensorOrderIndex



section Index

variable {p : ℕ} [hp : Fact p.Prime]

/-- `|ℤ_p ⧸ (a)| = ‖a‖⁻¹` for `a ≠ 0`. -/
theorem tOrdIdx_card_quot {a : ℤ_[p]} (ha : a ≠ 0) :
    (Nat.card (ℤ_[p] ⧸ Ideal.span ({a} : Set ℤ_[p])) : ℝ) = ‖a‖⁻¹ := by
  have hspan : Ideal.span ({a} : Set ℤ_[p]) = Ideal.span {(p : ℤ_[p]) ^ a.valuation} := by
    have h := PadicInt.unitCoeff_spec ha
    calc Ideal.span ({a} : Set ℤ_[p])
        = Ideal.span {(PadicInt.unitCoeff ha : ℤ_[p]) * (p : ℤ_[p]) ^ a.valuation} := by
          rw [← h]
      _ = _ := Ideal.span_singleton_mul_left_unit (PadicInt.unitCoeff ha).isUnit _
  have hsurj : Function.Surjective (PadicInt.toZModPow (p := p) a.valuation) := by
    intro x
    refine ⟨(x.val : ℤ_[p]), ?_⟩
    rw [map_natCast, ZMod.natCast_zmod_val]
  rw [hspan, ← PadicInt.ker_toZModPow,
    Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv, Nat.card_zmod,
    PadicInt.norm_eq_zpow_neg_valuation ha, zpow_neg, inv_inv, zpow_natCast, Nat.cast_pow]

/-- The norm of `ℤ_p` is multiplicative. -/
theorem tOrdIdx_norm_mul (a b : ℤ_[p]) : ‖a * b‖ = ‖a‖ * ‖b‖ := by
  simp only [PadicInt.norm_def, norm_mul]

/-- Associated elements of `ℤ_p` have the same norm. -/
theorem tOrdIdx_norm_eq_of_associated {a b : ℤ_[p]} (h : Associated a b) : ‖a‖ = ‖b‖ := by
  obtain ⟨u, rfl⟩ := h
  rw [tOrdIdx_norm_mul, PadicInt.isUnit_iff.1 u.isUnit, mul_one]

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- The `ℤ_p`-lattice spanned by a `ℚ_p`-basis `e`: the vectors whose `e`-coordinates all have
`p`-adic norm at most `1`. -/
def tOrdIdxLattice (e : Module.Basis ι ℚ_[p] V) : AddSubgroup V where
  carrier := {v | ∀ i, ‖e.repr v i‖ ≤ 1}
  add_mem' {a b} ha hb i := by
    rw [map_add, Finsupp.add_apply]
    exact (Padic.nonarchimedean _ _).trans (max_le (ha i) (hb i))
  zero_mem' i := by simp
  neg_mem' {a} ha i := by simpa using ha i

omit [Fintype ι] [DecidableEq ι] in
/-- Membership in `tOrdIdxLattice e`: all `e`-coordinates have norm at most `1`. -/
theorem tOrdIdx_mem_lattice (e : Module.Basis ι ℚ_[p] V) (v : V) :
    v ∈ tOrdIdxLattice e ↔ ∀ i, ‖e.repr v i‖ ≤ 1 := Iff.rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The basis vectors lie in the lattice they span. -/
theorem tOrdIdx_basis_mem (e : Module.Basis ι ℚ_[p] V) (j : ι) : e j ∈ tOrdIdxLattice e := by
  classical
  intro i
  rw [e.repr_self, Finsupp.single_apply]
  split_ifs <;> simp

/-- **Index and determinant over `ℤ_p`**: for `ℚ_p`-bases `e₁`, `e₂` with
`ℤ_p e₁ ⊆ ℤ_p e₂`, the index is `‖det_{e₂} e₁‖⁻¹`. -/
theorem tOrdIdx_relIndex_eq (e₁ e₂ : Module.Basis ι ℚ_[p] V)
    (h : tOrdIdxLattice e₁ ≤ tOrdIdxLattice e₂) :
    ((tOrdIdxLattice e₁).relIndex (tOrdIdxLattice e₂) : ℝ) = ‖e₂.det e₁‖⁻¹ := by
  classical
  have hC : ∀ i j, ‖e₂.repr (e₁ j) i‖ ≤ 1 := fun i j => h (tOrdIdx_basis_mem e₁ j) i
  let C : Matrix ι ι ℤ_[p] := fun i j => ⟨e₂.repr (e₁ j) i, hC i j⟩
  have hCmap : C.map (PadicInt.Coe.ringHom (p := p)) = e₂.toMatrix e₁ := by
    ext i j
    rfl
  let ψ : (ι → ℤ_[p]) →+ V :=
    { toFun := fun c => e₂.equivFun.symm (fun i => (c i : ℚ_[p]))
      map_zero' := by simp
      map_add' := fun a b => by
        rw [← map_add]
        congr 1 }
  have hψ : ∀ c, ⇑(e₂.repr (ψ c)) = fun i => (c i : ℚ_[p]) := by
    intro c
    have := e₂.equivFun.apply_symm_apply (fun i => (c i : ℚ_[p]))
    rw [Module.Basis.equivFun_apply] at this
    exact this
  have hcoe : ∀ (a : ι → ℤ_[p]) i, ((Matrix.mulVec C a) i : ℚ_[p]) =
      (Matrix.mulVec (e₂.toMatrix e₁) fun j => (a j : ℚ_[p])) i := by
    intro a i
    rw [← hCmap]
    exact RingHom.map_mulVec (PadicInt.Coe.ringHom (p := p)) C a i
  -- the key identity: `e₂`-coordinates of `e₁.equivFun.symm a` are `C a`
  have hkey : ∀ (a : ι → ℚ_[p]),
      ⇑(e₂.repr (e₁.equivFun.symm a)) = Matrix.mulVec (e₂.toMatrix e₁) a := by
    intro a
    have h := Module.Basis.toMatrix_mulVec_repr e₁ e₂ (e₁.equivFun.symm a)
    have h2 : ⇑(e₁.repr (e₁.equivFun.symm a)) = a := by
      have := e₁.equivFun.apply_symm_apply a
      rwa [Module.Basis.equivFun_apply] at this
    rw [h2] at h
    exact h.symm
  have hrange : (⊤ : AddSubgroup (ι → ℤ_[p])).map ψ = tOrdIdxLattice e₂ := by
    ext v
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_top, true_and]
    constructor
    · rintro ⟨c, rfl⟩ i
      rw [hψ]
      exact PadicInt.norm_le_one (c i)
    · intro hv
      refine ⟨fun i => ⟨e₂.repr v i, hv i⟩, ?_⟩
      apply e₂.repr.injective
      ext i
      exact congrFun (hψ _) i
  have hcomap : (tOrdIdxLattice e₁).comap ψ =
      (LinearMap.range (Matrix.toLin' C)).toAddSubgroup := by
    ext c
    simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, LinearMap.mem_range,
      Matrix.toLin'_apply]
    constructor
    · intro hc
      have hc' : ∀ j, e₁.repr (ψ c) j ∈ PadicInt.subring p := fun j =>
        (PadicInt.mem_subring_iff p).2 ((tOrdIdx_mem_lattice _ _).1 hc j)
      refine ⟨fun j => (⟨e₁.repr (ψ c) j, hc' j⟩ : ℤ_[p]), ?_⟩
      funext i
      apply PadicInt.ext
      refine (hcoe _ i).trans ?_
      have h1 := Module.Basis.toMatrix_mulVec_repr e₁ e₂ (ψ c)
      exact (congrFun h1 i).trans (congrFun (hψ c) i)
    · rintro ⟨a, rfl⟩
      have h2 : ψ (Matrix.mulVec C a) = e₁.equivFun.symm (fun j => (a j : ℚ_[p])) := by
        apply e₂.repr.injective
        ext i
        have := congrFun (hψ (Matrix.mulVec C a)) i
        rw [hkey]
        exact this.trans (hcoe a i)
      intro j
      rw [h2]
      have := e₁.equivFun.apply_symm_apply (fun j => (a j : ℚ_[p]))
      rw [Module.Basis.equivFun_apply] at this
      rw [this]
      exact PadicInt.norm_le_one (a j)
  have hinj : Function.Injective (Matrix.toLin' C) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have h3 : (fun j => (a j : ℚ_[p])) = 0 := by
      apply e₁.equivFun.symm.injective
      rw [map_zero]
      apply e₂.repr.injective
      ext i
      rw [hkey, ← hcoe]
      rw [Matrix.toLin'_apply] at ha
      rw [ha]
      simp
    ext j
    have := congrFun h3 j
    simpa using this
  have hidx : (tOrdIdxLattice e₁).relIndex (tOrdIdxLattice e₂) =
      Nat.card ((ι → ℤ_[p]) ⧸ LinearMap.range (Matrix.toLin' C)) := by
    rw [← hrange, ← AddSubgroup.relIndex_comap, hcomap, AddSubgroup.relIndex_top_right]
    rfl
  -- Smith normal form
  set N := LinearMap.range (Matrix.toLin' C)
  have hrk : Module.finrank ℤ_[p] N = Module.finrank ℤ_[p] (ι → ℤ_[p]) :=
    LinearMap.finrank_range_of_inj hinj
  let b := Pi.basisFun ℤ_[p] ι
  let a := Submodule.smithNormalFormCoeffs b hrk
  have ha0 : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b hrk
  have hcard : (Nat.card ((ι → ℤ_[p]) ⧸ N) : ℝ) = ∏ i, ‖a i‖⁻¹ := by
    rw [Nat.card_congr (Submodule.quotientEquivPiSpan N b hrk).toEquiv, Nat.card_pi]
    push_cast
    exact Finset.prod_congr rfl fun i _ => tOrdIdx_card_quot (ha0 i)
  let b' := Submodule.smithNormalFormTopBasis b hrk
  let ab := Submodule.smithNormalFormBotBasis b hrk
  have ab_eq := Submodule.smithNormalFormBotBasis_def b hrk
  let e' : (ι → ℤ_[p]) ≃ₗ[ℤ_[p]] N := b'.equiv ab (Equiv.refl _)
  have hdiag : LinearMap.det (N.subtype ∘ₗ (e' : (ι → ℤ_[p]) →ₗ[ℤ_[p]] N)) = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Submodule.subtype_apply, Module.Basis.equiv_apply, Equiv.refl_apply, ab_eq, map_smul,
      Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  let f₀ : (ι → ℤ_[p]) ≃ₗ[ℤ_[p]] N := LinearEquiv.ofInjective (Matrix.toLin' C) hinj
  have hf₀ : N.subtype ∘ₗ (f₀ : (ι → ℤ_[p]) →ₗ[ℤ_[p]] N) = Matrix.toLin' C := by
    ext x
    rfl
  have hassoc := LinearMap.associated_det_comp_equiv N.subtype f₀ e'
  rw [hf₀, LinearMap.det_toLin', hdiag] at hassoc
  have hdet : e₂.det e₁ = (C.det : ℚ_[p]) := by
    rw [Module.Basis.det_apply, ← hCmap]
    exact (RingHom.map_det (PadicInt.Coe.ringHom (p := p)) C).symm
  have hm : ∀ s : Finset ι, ‖∏ i ∈ s, a i‖ = ∏ i ∈ s, ‖a i‖ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih => rw [Finset.prod_insert hj, Finset.prod_insert hj, ← ih, tOrdIdx_norm_mul]
  rw [hidx, hcard, hdet, ← PadicInt.norm_def, tOrdIdx_norm_eq_of_associated hassoc, hm,
    Finset.prod_inv_distrib]

end Index

section Trace

variable {F A B : Type*} [Field F] [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
  [FiniteDimensional F A] [FiniteDimensional F B]

/-- `Tr(a ⊗ b) = Tr(a) · Tr(b)` for finite-dimensional commutative algebras over a field. -/
theorem tOrdIdx_trace_tmul (a : A) (b : B) :
    Algebra.trace F (TensorProduct F A B) (a ⊗ₜ[F] b) =
      Algebra.trace F A a * Algebra.trace F B b := by
  rw [Algebra.trace_apply, Algebra.trace_apply, Algebra.trace_apply]
  have : Algebra.lmul F (TensorProduct F A B) (a ⊗ₜ[F] b) =
      TensorProduct.map (Algebra.lmul F A a) (Algebra.lmul F B b) := by
    apply TensorProduct.ext'
    intro x y
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [this, LinearMap.trace_tensorProduct']

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
/-- The trace matrix of a tensor basis is the Kronecker product of the trace matrices. -/
theorem tOrdIdx_traceMatrix_tensor (b : Module.Basis ι F A) (c : Module.Basis κ F B) :
    Algebra.traceMatrix F (b.tensorProduct c) =
      Matrix.kroneckerMap (fun x y => x * y) (Algebra.traceMatrix F b)
        (Algebra.traceMatrix F c) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [Algebra.traceMatrix_apply, Matrix.kronecker_apply, Algebra.traceMatrix_apply,
    Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.traceForm_apply,
    Algebra.traceForm_apply, Module.Basis.tensorProduct_apply, Module.Basis.tensorProduct_apply,
    Algebra.TensorProduct.tmul_mul_tmul, tOrdIdx_trace_tmul]

/-- **Discriminant of a tensor basis** (Lemma 4.2 of the paper for two factors):
`disc (b ⊗ c) = disc b ^ {dim B} · disc c ^ {dim A}`. -/
theorem tOrdIdx_discr_tensor (b : Module.Basis ι F A) (c : Module.Basis κ F B) :
    Algebra.discr F (b.tensorProduct c) =
      Algebra.discr F b ^ Fintype.card κ * Algebra.discr F c ^ Fintype.card ι := by
  rw [Algebra.discr_def, tOrdIdx_traceMatrix_tensor, Matrix.det_kronecker, ← Algebra.discr_def,
    ← Algebra.discr_def]

/-- **Change of basis** (identity (0.1) of the paper): `disc e₁ = (det_{e₂} e₁)² · disc e₂`.
-/
theorem tOrdIdx_discr_change {S : Type*} [CommRing S] [Algebra F S] (e₁ e₂ : Module.Basis ι F S) :
    Algebra.discr F e₁ = e₂.det e₁ ^ 2 * Algebra.discr F e₂ := by
  have h : (⇑e₁ : ι → S) = Matrix.vecMul (⇑e₂) ((e₂.toMatrix e₁).map (algebraMap F S)) := by
    funext j
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply]
    rw [← e₂.sum_toMatrix_smul_self e₁ j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, mul_comm]
  conv_lhs => rw [h]
  rw [Algebra.discr_of_matrix_vecMul, Module.Basis.det_apply]

end Trace



section Galois

open Classical

variable (F K : Type*) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- `Φ(x ⊗ y) = (x · σ(y))_σ`. -/
noncomputable def tOrdIdxPhi : TensorProduct F K K →ₐ[F] ((K ≃ₐ[F] K) → K) :=
  AlgHom.pi fun σ => Algebra.TensorProduct.productMap (AlgHom.id F K) (σ : K →ₐ[F] K)

omit [FiniteDimensional F K] in
/-- `Φ(x ⊗ y)_σ = x · σ(y)`. -/
theorem tOrdIdxPhi_tmul (x y : K) (σ : K ≃ₐ[F] K) :
    tOrdIdxPhi F K (x ⊗ₜ[F] y) σ = x * σ y := rfl

/-- `|Gal(K/F)| = [K : F]` for `K/F` finite Galois. -/
theorem tOrdIdx_card_gal [IsGalois F K] : Fintype.card (K ≃ₐ[F] K) = Module.finrank F K := by
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]

/-- `Φ` is injective for `K/F` finite Galois (independence of characters). -/
theorem tOrdIdxPhi_injective [IsGalois F K] : Function.Injective (tOrdIdxPhi F K) := by
  let b := Module.finBasis F K
  let B := Algebra.TensorProduct.basis K b
  rw [injective_iff_map_eq_zero]
  intro z hz
  set c := B.repr z
  have hz' : z = ∑ j, c j ⊗ₜ[F] b j := by
    conv_lhs => rw [← B.sum_repr z]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hσ : ∀ σ : K ≃ₐ[F] K, ∑ j, c j * σ (b j) = 0 := by
    intro σ
    have := congrFun hz σ
    rw [hz', map_sum, Finset.sum_apply] at this
    simpa only [tOrdIdxPhi_tmul, Pi.zero_apply] using this
  have hli : LinearIndependent K (fun σ : K ≃ₐ[F] K => ((σ : K →ₐ[F] K) : K →ₗ[F] K)) :=
    (linearIndependent_toLinearMap F K K).comp (fun σ : K ≃ₐ[F] K => (σ : K →ₐ[F] K))
      (fun σ τ h => AlgEquiv.coe_toAlgHom_injective h)
  let T : ((K ≃ₐ[F] K) → K) →ₗ[K] (Fin (Module.finrank F K) → K) :=
    { toFun := fun w j => ∑ σ, w σ * σ (b j)
      map_add' := fun v w => by
        ext j
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun a w => by
        ext j
        simp [Finset.mul_sum, mul_assoc] }
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h0 : ∑ σ, w σ • ((σ : K →ₐ[F] K) : K →ₗ[F] K) = 0 := by
      apply b.ext
      intro j
      have := congrFun hw j
      simpa [T, LinearMap.sum_apply] using this
    funext σ
    exact Fintype.linearIndependent_iff.1 hli w h0 σ
  have hcard : Module.finrank K ((K ≃ₐ[F] K) → K) =
      Module.finrank K (Fin (Module.finrank F K) → K) := by
    rw [Module.finrank_pi, Module.finrank_pi, Fintype.card_fin, tOrdIdx_card_gal]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hcard).1 hT
  have hc : ∀ j, c j = 0 := by
    intro j
    obtain ⟨w, hw⟩ := hsurj (Pi.single j 1)
    calc c j = ∑ i, (Pi.single j (1 : K) : Fin (Module.finrank F K) → K) i * c i := by
          simp [Pi.single_apply]
      _ = ∑ i, (∑ σ, w σ * σ (b i)) * c i := by rw [← hw]; rfl
      _ = ∑ σ, w σ * ∑ i, c i * σ (b i) := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_comm.trans
            (Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun i _ => by ring)
      _ = 0 := by simp [hσ]
  rw [hz']
  simp [hc]

/-- `Φ` is bijective for `K/F` finite Galois: it is injective between spaces of dimension
`[K : F]²`. -/
theorem tOrdIdxPhi_bijective [IsGalois F K] : Function.Bijective (tOrdIdxPhi F K) := by
  refine ⟨tOrdIdxPhi_injective F K, ?_⟩
  have h : Module.finrank F (TensorProduct F K K) = Module.finrank F ((K ≃ₐ[F] K) → K) := by
    rw [Module.finrank_tensorProduct, Module.finrank_pi_fintype, Finset.sum_const,
      Finset.card_univ, tOrdIdx_card_gal, smul_eq_mul]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (tOrdIdxPhi F K).toLinearMap) h).1 (tOrdIdxPhi_injective F K)

/-- The isomorphism `K ⊗ K ≅ ∏_{Gal} K` of a finite Galois extension. -/
noncomputable def tOrdIdxPhiEquiv [IsGalois F K] :
    TensorProduct F K K ≃ₐ[F] ((K ≃ₐ[F] K) → K) :=
  AlgEquiv.ofBijective (tOrdIdxPhi F K) (tOrdIdxPhi_bijective F K)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The basis `(k, σ) ↦ b_k` in the `σ`-component. -/
noncomputable def tOrdIdxPiBasis (b : Module.Basis ι F K) :
    Module.Basis (ι × (K ≃ₐ[F] K)) F ((K ≃ₐ[F] K) → K) :=
  (Pi.basis fun _ : K ≃ₐ[F] K => b).reindex
    ((Equiv.sigmaEquivProd _ _).trans (Equiv.prodComm _ _))

variable {F K}

omit [Fintype ι] [DecidableEq ι] in
/-- The vector `(k, σ)` of `tOrdIdxPiBasis b` is `b_k` in the `σ`-component. -/
theorem tOrdIdxPiBasis_apply (b : Module.Basis ι F K) (k : ι) (σ : K ≃ₐ[F] K) :
    tOrdIdxPiBasis F K b (k, σ) = Pi.single σ (b k) := by
  simp [tOrdIdxPiBasis]

omit [Fintype ι] [DecidableEq ι] in
/-- The `(k, σ)`-coordinate of `w` is the `k`-th `b`-coordinate of `w σ`. -/
theorem tOrdIdxPiBasis_repr (b : Module.Basis ι F K) (w : (K ≃ₐ[F] K) → K) (k : ι)
    (σ : K ≃ₐ[F] K) : (tOrdIdxPiBasis F K b).repr w (k, σ) = b.repr (w σ) k := by
  simp [tOrdIdxPiBasis]

/-- The trace of `∏_σ K` over `F` is the sum of the traces of the components. -/
theorem tOrdIdx_trace_pi (b : Module.Basis ι F K) (w : (K ≃ₐ[F] K) → K) :
    Algebra.trace F ((K ≃ₐ[F] K) → K) w = ∑ σ, Algebra.trace F K (w σ) := by
  rw [Algebra.trace_eq_matrix_trace (tOrdIdxPiBasis F K b), Matrix.trace,
    Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, tOrdIdxPiBasis_apply,
    tOrdIdxPiBasis_repr, Pi.mul_apply, Pi.single_eq_same]

/-- The trace matrix of `tOrdIdxPiBasis b` is block diagonal, each block the trace matrix of
`b`. -/
theorem tOrdIdx_traceMatrix_pi (b : Module.Basis ι F K) :
    Algebra.traceMatrix F (tOrdIdxPiBasis F K b) =
      Matrix.blockDiagonal fun _ => Algebra.traceMatrix F b := by
  ext ⟨i, σ⟩ ⟨j, τ⟩
  rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, tOrdIdx_trace_pi b,
    tOrdIdxPiBasis_apply, tOrdIdxPiBasis_apply, Matrix.blockDiagonal_apply]
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

/-- **Discriminant of the split algebra** (Lemma 4.1 of the paper for two factors):
`disc (tOrdIdxPiBasis b) = disc b ^ |Gal(K/F)|`. -/
theorem tOrdIdx_discr_pi (b : Module.Basis ι F K) :
    Algebra.discr F (tOrdIdxPiBasis F K b) =
      Algebra.discr F b ^ Fintype.card (K ≃ₐ[F] K) := by
  rw [Algebra.discr_def, tOrdIdx_traceMatrix_pi, Matrix.det_blockDiagonal, Finset.prod_const,
    Finset.card_univ, ← Algebra.discr_def]

end Galois


/-! ## The library's `R_E` and `(R_E)^∼` as lattices -/

section Library

open MeasureTheory IUT.PaperIV.LocalFields IUT.Prerequisites.PadicVolume

variable (p : ℕ) [hp : Fact p.Prime]

/-- **An integral basis**: a `ℚ_p`-basis `b` of `K` such that `x` is integral over `ℤ_p` if and
only if all its coordinates lie in `ℤ_p`; that is, `b` is a `ℤ_p`-basis of the ring of integers.
-/
def tOrdIdxIntegralBasis {K : Type*} [Field K] [Algebra ℚ_[p] K] {ι : Type*}
    (b : Module.Basis ι ℚ_[p] K) : Prop :=
  ∀ x : K, padicVolIntegral p x ↔ ∀ i, ‖b.repr x i‖ ≤ 1

variable {p}

/-- The vectors of an integral basis are integral over `ℤ_p`. -/
theorem tOrdIdxIntegralBasis_mem {K : Type*} [Field K] [Algebra ℚ_[p] K] {ι : Type*}
    {b : Module.Basis ι ℚ_[p] K} (hb : tOrdIdxIntegralBasis p b) (i : ι) :
    padicVolIntegral p (b i) :=
  (hb _).2 ((tOrdIdx_mem_lattice b _).1 (tOrdIdx_basis_mem b i))

/-- **Integral bases exist**: every finite extension `K` of `ℚ_p` has a `ℚ_p`-basis that is a
`ℤ_p`-basis of its ring of integers (Mathlib's freeness of the integral closure over a
principal ideal domain). -/
theorem tOrdIdx_exists_integralBasis (K : Type*) [Field K] [Algebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℚ_[p] K), tOrdIdxIntegralBasis p b := by
  let _ : Algebra ℤ_[p] K := ((algebraMap ℚ_[p] K).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra
  have : IsScalarTower ℤ_[p] ℚ_[p] K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := isTorsionFree_ringOfIntegers_padic p K
  have : Module.IsTorsionFree ℤ_[p] K := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r x h => ?_
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with hr | hx
    · left
      rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] K, map_eq_zero] at hr
      exact IsFractionRing.injective ℤ_[p] ℚ_[p] (hr.trans (map_zero _).symm)
    · right
      exact hx
  have : Module.Finite ℤ_[p] (integralClosure ℤ_[p] K) :=
    IsIntegralClosure.finite ℤ_[p] ℚ_[p] K (integralClosure ℤ_[p] K)
  have : Module.Free ℤ_[p] (integralClosure ℤ_[p] K) :=
    IsIntegralClosure.module_free ℤ_[p] ℚ_[p] K (integralClosure ℤ_[p] K)
  have : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure ℤ_[p] K)
      (nonZeroDivisors ℤ_[p])) K :=
    IsIntegralClosure.isLocalization ℤ_[p] ℚ_[p] K (integralClosure ℤ_[p] K)
  let B := (Module.Free.chooseBasis ℤ_[p] (integralClosure ℤ_[p] K)).reindex
    (Fintype.equivFin _)
  let b := B.localizationLocalization ℚ_[p] (nonZeroDivisors ℤ_[p]) K
  refine ⟨_, b, fun x => ⟨fun hx i => ?_, fun hx => ?_⟩⟩
  · have hx' : IsIntegral ℤ_[p] x := hx
    have h := B.localizationLocalization_repr_algebraMap ℚ_[p] (nonZeroDivisors ℤ_[p]) K
      ⟨x, hx'⟩ i
    have hx2 : algebraMap (integralClosure ℤ_[p] K) K ⟨x, hx'⟩ = x := rfl
    rw [hx2] at h
    change ‖b.repr x i‖ ≤ 1
    rw [h]
    exact PadicInt.norm_le_one _
  · have hsum := b.sum_repr x
    change IsIntegral ℤ_[p] x
    rw [← hsum]
    refine IsIntegral.sum _ fun i _ => ?_
    let r : ℤ_[p] := ⟨b.repr x i, (PadicInt.mem_subring_iff p).2 (hx i)⟩
    have hc : b.repr x i = algebraMap ℤ_[p] ℚ_[p] r := rfl
    rw [hc, algebraMap_smul, Module.Basis.localizationLocalization_apply]
    exact IsIntegral.smul _ (B i).2

variable {K₁ K₂ : Type*} [Field K₁] [Field K₂] [Algebra ℚ_[p] K₁] [Algebra ℚ_[p] K₂]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
/-- **`R_E` is the lattice of the tensor basis**: for integral bases `b`, `c` of `K₁`, `K₂`,
`R_E = R₁ ⊗_{ℤ_p} R₂` (the library's `tensorIdxRing`) is the `ℤ_p`-span of the `b_i ⊗ c_k`. -/
theorem tOrdIdx_ring_eq_lattice (b : Module.Basis ι ℚ_[p] K₁) (c : Module.Basis κ ℚ_[p] K₂)
    (hb : tOrdIdxIntegralBasis p b) (hc : tOrdIdxIntegralBasis p c) :
    (tensorIdxRing p K₁ K₂).toAddSubgroup = tOrdIdxLattice (b.tensorProduct c) := by
  apply le_antisymm
  · intro z hz
    rw [Subring.mem_toAddSubgroup, ← SetLike.mem_coe, tensorIdxRing_coe] at hz
    unfold padicPacketIntegers at hz
    rw [SetLike.mem_coe] at hz
    induction hz using AddSubmonoid.closure_induction with
    | mem w hw =>
      obtain ⟨x, y, hx, hy, rfl⟩ := hw
      rintro ⟨i, k⟩
      rw [Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul, norm_mul]
      calc _ ≤ (1 : ℝ) * 1 := mul_le_mul ((hc y).1 hy k) ((hb x).1 hx i) (norm_nonneg _)
              zero_le_one
        _ = 1 := one_mul 1
    | zero => exact zero_mem _
    | add a a' _ _ ha ha' => exact add_mem ha ha'
  · intro z hz
    rw [Subring.mem_toAddSubgroup, ← (b.tensorProduct c).sum_repr z]
    refine Subring.sum_mem _ fun ik _ => ?_
    obtain ⟨i, k⟩ := ik
    have hik := (tOrdIdx_mem_lattice _ z).1 hz (i, k)
    have hmem : (b.tensorProduct c) (i, k) ∈ tensorIdxRing p K₁ K₂ := by
      rw [Module.Basis.tensorProduct_apply, ← SetLike.mem_coe, tensorIdxRing_coe]
      exact AddSubmonoid.subset_closure
        ⟨b i, c k, tOrdIdxIntegralBasis_mem hb i, tOrdIdxIntegralBasis_mem hc k, rfl⟩
    exact tensorIdx_smul_mem p K₁ K₂ ⟨_, hik⟩ hmem

/-- **The index formula for two factors, any finite extensions**: let `b`, `c` be integral
bases of `K₁`, `K₂` and `n` a `ℚ_p`-basis of `K₁ ⊗ K₂` whose `ℤ_p`-span is the normalization
`(R_E)^∼`. Then `[(R_E)^∼ : R_E]² · ‖disc b‖^{d₂} · ‖disc c‖^{d₁} = ‖disc n‖` (`p`-adic norms of
discriminants of the trace form; `d_i = [K_i : ℚ_p]`). In valuations:
`2 v_p([(R_E)^∼ : R_E]) = d₂ v_p(disc K₁) + d₁ v_p(disc K₂) − v_p(disc (R_E)^∼)`. -/
theorem tOrdIdx_index_sq_general [FiniteDimensional ℚ_[p] K₁] [FiniteDimensional ℚ_[p] K₂]
    (b : Module.Basis ι ℚ_[p] K₁) (c : Module.Basis κ ℚ_[p] K₂)
    (hb : tOrdIdxIntegralBasis p b) (hc : tOrdIdxIntegralBasis p c)
    (n : Module.Basis (ι × κ) ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂))
    (hn : (tensorIdxNormRing p K₁ K₂).toAddSubgroup = tOrdIdxLattice n) :
    ((tensorIdxRing p K₁ K₂).toAddSubgroup.relIndex (tensorIdxNormRing p K₁ K₂).toAddSubgroup :
        ℝ) ^ 2 * (‖Algebra.discr ℚ_[p] b‖ ^ Fintype.card κ *
          ‖Algebra.discr ℚ_[p] c‖ ^ Fintype.card ι) = ‖Algebra.discr ℚ_[p] n‖ := by
  have hle : tOrdIdxLattice (b.tensorProduct c) ≤ tOrdIdxLattice n := by
    rw [← tOrdIdx_ring_eq_lattice b c hb hc, ← hn]
    exact fun z hz => tensorIdxRing_le p K₁ K₂ hz
  have hd : ‖n.det (b.tensorProduct c)‖ ≠ 0 :=
    norm_ne_zero_iff.2 (n.isUnit_det _).ne_zero
  have key : ‖Algebra.discr ℚ_[p] b‖ ^ Fintype.card κ *
      ‖Algebra.discr ℚ_[p] c‖ ^ Fintype.card ι =
      ‖n.det (b.tensorProduct c)‖ ^ 2 * ‖Algebra.discr ℚ_[p] n‖ := by
    rw [← norm_pow, ← norm_pow, ← norm_mul, ← tOrdIdx_discr_tensor,
      tOrdIdx_discr_change (b.tensorProduct c) n, norm_mul, norm_pow]
  rw [tOrdIdx_ring_eq_lattice b c hb hc, hn, tOrdIdx_relIndex_eq _ _ hle, key]
  field_simp

variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

/-- The basis of `K ⊗ K` that `Φ` sends to `tOrdIdxPiBasis b`. -/
noncomputable def tOrdIdxNormBasis [IsGalois ℚ_[p] K] (b : Module.Basis ι ℚ_[p] K) :
    Module.Basis (ι × (K ≃ₐ[ℚ_[p]] K)) ℚ_[p] (TensorProduct ℚ_[p] K K) :=
  (tOrdIdxPiBasis ℚ_[p] K b).map (tOrdIdxPhiEquiv ℚ_[p] K).symm.toLinearEquiv

omit [Fintype ι] [DecidableEq ι] in
/-- Coordinates in `tOrdIdxNormBasis b` are the `b`-coordinates of the components of `Φ`. -/
theorem tOrdIdxNormBasis_repr [IsGalois ℚ_[p] K] (b : Module.Basis ι ℚ_[p] K)
    (z : TensorProduct ℚ_[p] K K) (k : ι) (σ : K ≃ₐ[ℚ_[p]] K) :
    (tOrdIdxNormBasis b).repr z (k, σ) = b.repr (tOrdIdxPhi ℚ_[p] K z σ) k := by
  rw [tOrdIdxNormBasis, Module.Basis.map_repr]
  exact tOrdIdxPiBasis_repr b _ k σ

omit [Fintype ι] [DecidableEq ι] in
/-- **`(R_E)^∼` is the lattice of `tOrdIdxNormBasis`** (Galois case): `z` is integral if and only
if every component `Φ(z)_σ` is, that is, `Φ((R_E)^∼) = ∏_σ O_K`. -/
theorem tOrdIdx_normRing_eq_lattice [IsGalois ℚ_[p] K] (b : Module.Basis ι ℚ_[p] K)
    (hb : tOrdIdxIntegralBasis p b) :
    (tensorIdxNormRing p K K).toAddSubgroup = tOrdIdxLattice (tOrdIdxNormBasis b) := by
  ext z
  rw [Subring.mem_toAddSubgroup, tOrdIdx_mem_lattice]
  change padicVolIntegral p z ↔ _
  have h1 : padicVolIntegral p z ↔ padicVolIntegral p (tOrdIdxPhiEquiv ℚ_[p] K z) :=
    ⟨fun h => padicVolIntegral_map p (tOrdIdxPhiEquiv ℚ_[p] K).toAlgHom h,
      fun h => by
        simpa using padicVolIntegral_map p (tOrdIdxPhiEquiv ℚ_[p] K).symm.toAlgHom h⟩
  rw [h1, volBridge_padicVolIntegral_pi]
  constructor
  · rintro h ⟨k, σ⟩
    rw [tOrdIdxNormBasis_repr]
    exact (hb _).1 (h σ) k
  · intro h σ
    refine (hb _).2 fun k => ?_
    have := h (k, σ)
    rwa [tOrdIdxNormBasis_repr] at this

/-- **Theorem 5.1 of the paper for two factors**: for `K/ℚ_p` finite Galois of degree `d` with an
integral basis `b`, `[(R_E)^∼ : R_E]² = (‖disc b‖⁻¹)^d`, that is, the index is
`|𝔡_K|^{d/2}` with `|𝔡_K| = ‖disc b‖⁻¹ = p^{v_p(disc K)}`. -/
theorem tOrdIdx_index_sq_galois [IsGalois ℚ_[p] K] (b : Module.Basis ι ℚ_[p] K)
    (hb : tOrdIdxIntegralBasis p b) :
    ((tensorIdxRing p K K).toAddSubgroup.relIndex (tensorIdxNormRing p K K).toAddSubgroup :
        ℝ) ^ 2 = (‖Algebra.discr ℚ_[p] b‖⁻¹) ^ Module.finrank ℚ_[p] K := by
  classical
  have hcard : Fintype.card (K ≃ₐ[ℚ_[p]] K) = Fintype.card ι := by
    rw [tOrdIdx_card_gal, Module.finrank_eq_card_basis b]
  let e : (K ≃ₐ[ℚ_[p]] K) ≃ ι := Fintype.equivOfCardEq hcard
  let n := (tOrdIdxNormBasis b).reindex (Equiv.prodCongr (Equiv.refl ι) e)
  have hn : (tensorIdxNormRing p K K).toAddSubgroup = tOrdIdxLattice n := by
    rw [tOrdIdx_normRing_eq_lattice b hb]
    ext z
    simp only [tOrdIdx_mem_lattice, n, Module.Basis.repr_reindex_apply]
    constructor
    · intro h i
      exact h _
    · rintro h ⟨k, σ⟩
      simpa using h (k, e σ)
  have hdn0 : Algebra.discr ℚ_[p] (tOrdIdxNormBasis b) =
      Algebra.discr ℚ_[p] (tOrdIdxPiBasis ℚ_[p] K b) := by
    rw [Algebra.discr_eq_discr_of_algEquiv (tOrdIdxPiBasis ℚ_[p] K b)
      (tOrdIdxPhiEquiv ℚ_[p] K).symm]
    congr 1
  have hdn : Algebra.discr ℚ_[p] n = Algebra.discr ℚ_[p] b ^ Fintype.card ι := by
    simp only [n, Module.Basis.coe_reindex, Algebra.discr_reindex]
    rw [hdn0, tOrdIdx_discr_pi, hcard]
  have h := tOrdIdx_index_sq_general b b hb hb n hn
  rw [hdn, norm_pow] at h
  have hd0 : ‖Algebra.discr ℚ_[p] b‖ ≠ 0 :=
    norm_ne_zero_iff.2 (Algebra.discr_not_zero_of_basis ℚ_[p] b)
  have hd1 : ‖Algebra.discr ℚ_[p] b‖ ^ Fintype.card ι ≠ 0 := pow_ne_zero _ hd0
  rw [Module.finrank_eq_card_basis b, inv_pow]
  refine eq_inv_of_mul_eq_one_left (mul_left_cancel₀ hd1 ?_)
  linear_combination h

/-- **The normalized log-volume of `R_E` (Galois case)**: with `μ^log` normalized at `(R_E)^∼`
and divided by the dimension `d²` (IUT IV Proposition 1.4 (i), page 13),
`μ^log(R_E) = log ‖disc b‖ / (2 d)`. -/
theorem tOrdIdx_muLog_galois [IsGalois ℚ_[p] K]
    [MeasurableSpace (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K K)) → ℚ_[p])]
    [BorelSpace (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K K)) → ℚ_[p])]
    (μ : Measure (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K K)) → ℚ_[p]))
    [μ.IsAddHaarMeasure] (b : Module.Basis ι ℚ_[p] K) (hb : tOrdIdxIntegralBasis p b) :
    padicPacketMuLog p (TensorProduct ℚ_[p] K K) μ (padicPacketNormalization p K K)
        (padicPacketIntegers p K K) =
      Real.log ‖Algebra.discr ℚ_[p] b‖ / (2 * Module.finrank ℚ_[p] K) := by
  rw [tensorIdx_muLog_eq, padicVol_finrank_tensor p K K]
  have h := tOrdIdx_index_sq_galois b hb
  have hn := tensorIdx_relIndex_ne_zero p K K
  have hpos : (0 : ℝ) < ((tensorIdxRing p K K).toAddSubgroup.relIndex
      (tensorIdxNormRing p K K).toAddSubgroup : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hl := congrArg Real.log h
  rw [Real.log_pow, Real.log_pow, Real.log_inv] at hl
  have hd : (0 : ℝ) < Module.finrank ℚ_[p] K := by exact_mod_cast Module.finrank_pos
  have hl' : Real.log ((tensorIdxRing p K K).toAddSubgroup.relIndex
      (tensorIdxNormRing p K K).toAddSubgroup : ℝ) =
      -((Module.finrank ℚ_[p] K : ℝ) * Real.log ‖Algebra.discr ℚ_[p] b‖) / 2 := by
    push_cast at hl
    linarith
  push_cast
  rw [hl']
  field_simp

/-- **The same value in the valuation of the discriminant**: with `v = v_p(disc b)`,
`μ^log(R_E) = −(v / (2 d)) · log p`, that is, `−(1/2) · (v/d) · log p`. -/
theorem tOrdIdx_muLog_galois_valuation [IsGalois ℚ_[p] K]
    [MeasurableSpace (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K K)) → ℚ_[p])]
    [BorelSpace (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K K)) → ℚ_[p])]
    (μ : Measure (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K K)) → ℚ_[p]))
    [μ.IsAddHaarMeasure] (b : Module.Basis ι ℚ_[p] K) (hb : tOrdIdxIntegralBasis p b) :
    padicPacketMuLog p (TensorProduct ℚ_[p] K K) μ (padicPacketNormalization p K K)
        (padicPacketIntegers p K K) =
      -((Algebra.discr ℚ_[p] b).valuation / (2 * Module.finrank ℚ_[p] K)) * Real.log p := by
  rw [tOrdIdx_muLog_galois μ b hb,
    Padic.norm_eq_zpow_neg_valuation (Algebra.discr_not_zero_of_basis ℚ_[p] b), Real.log_zpow]
  push_cast
  ring

end Library

/-! ## The arithmetic of sections 8.4 and 10 of the paper (model tests) -/

section Growth

/-- The paper's raw exponent for `n = j + 1` factors: `v_p(ρ_{j+1}) = (j/2) · d^j · v`. -/
noncomputable def tOrdIdxRawExp (d v : ℝ) (j : ℕ) : ℝ := (j / 2) * d ^ j * v

/-- The normalized value for `n = j + 1` factors, in units of `log p`: `(j/2) · (v/d)`. -/
noncomputable def tOrdIdxNormExp (d v : ℝ) (j : ℕ) : ℝ := (j / 2) * (v / d)

/-- **Raw and normalized**: the normalized value is the raw exponent divided by the dimension
`d^{j+1}` of the `(j+1)`-fold tensor product. -/
theorem tOrdIdx_norm_eq_raw_div {d : ℝ} (hd : d ≠ 0) (v : ℝ) (j : ℕ) :
    tOrdIdxNormExp d v j = tOrdIdxRawExp d v j / d ^ (j + 1) := by
  unfold tOrdIdxNormExp tOrdIdxRawExp
  field_simp
  ring

/-- **The raw sum grows like `d^J`**: `∑_{j ≤ J} v_p(ρ_{j+1}) ≥ (v/2) · J · d^J` for `d ≥ 1`,
`v ≥ 0`. -/
theorem tOrdIdx_rawSum_ge {d v : ℝ} (hd : 1 ≤ d) (hv : 0 ≤ v) (J : ℕ) :
    (v / 2) * J * d ^ J ≤ ∑ j ∈ Finset.Icc 1 J, tOrdIdxRawExp d v j := by
  rcases Nat.eq_zero_or_pos J with rfl | hJ
  · simp
  · have hmem : J ∈ Finset.Icc 1 J := Finset.mem_Icc.2 ⟨hJ, le_rfl⟩
    have hnn : ∀ j ∈ Finset.Icc 1 J, 0 ≤ tOrdIdxRawExp d v j := fun j _ => by
      unfold tOrdIdxRawExp
      have : (0 : ℝ) ≤ d ^ j := pow_nonneg (by linarith) j
      positivity
    have := Finset.single_le_sum hnn hmem
    unfold tOrdIdxRawExp at this ⊢
    linarith [show (J : ℝ) / 2 * d ^ J * v = v / 2 * J * d ^ J by ring]

/-- **The normalized sum is polynomial**: `∑_{j ≤ J} (j/2)(v/d) = (v/d) · J (J + 1) / 4`. -/
theorem tOrdIdx_normSum_eq (d v : ℝ) (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, tOrdIdxNormExp d v j = (v / d) * (J * (J + 1)) / 4 := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    unfold tOrdIdxNormExp
    push_cast
    ring

/-- **The normalized average is linear**: `(1/J) ∑_{j ≤ J} (j/2)(v/d) = (v/d)(J + 1)/4`. -/
theorem tOrdIdx_normAvg_eq (d v : ℝ) {J : ℕ} (hJ : J ≠ 0) :
    (∑ j ∈ Finset.Icc 1 J, tOrdIdxNormExp d v j) / J = (v / d) * (J + 1) / 4 := by
  rw [tOrdIdx_normSum_eq]
  have : (J : ℝ) ≠ 0 := by exact_mod_cast hJ
  field_simp

/-- **The closed form of section 10.2 of the paper, `d = 2`**:
`∑_{j=1}^{J} j 2^j = (J − 1) 2^{J+1} + 2`. -/
theorem tOrdIdx_sum_two_pow (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, (j : ℤ) * 2 ^ j = ((J : ℤ) - 1) * 2 ^ (J + 1) + 2 := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

/-- **Half of `j · (v/d)`**: the normalized value for `j + 1` factors is `(1/2) · j · (v/d)`.
With `𝔡 = v/d` this is half of `j · 𝔡`, the exponent `𝔡_{I*}` of IUT IV Proposition 1.1
(page 9) for `j + 1` copies of `K`; the identification `𝔡 = v/d` is not proved here. -/
theorem tOrdIdx_normExp_eq_half (d v : ℝ) (j : ℕ) :
    tOrdIdxNormExp d v j = (1 / 2) * (j * (v / d)) := by
  unfold tOrdIdxNormExp
  ring

/-- **The closed form of section 10.2 of the paper, any `d`**:
`(d − 1)² ∑_{j=1}^{J} j d^j = d ((J (d − 1) − 1) d^J + 1)`. -/
theorem tOrdIdx_sum_pow_closed (d : ℝ) (J : ℕ) :
    (d - 1) ^ 2 * ∑ j ∈ Finset.Icc 1 J, (j : ℝ) * d ^ j =
      d * ((J * (d - 1) - 1) * d ^ J + 1) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    push_cast
    ring

/-- **The raw sum is of order `J d^J`**: for `d ≥ 2`,
`J d^J ≤ ∑_{j=1}^{J} j d^j ≤ 2 J d^J`. -/
theorem tOrdIdx_sum_pow_bounds {d : ℝ} (hd : 2 ≤ d) (J : ℕ) :
    (J : ℝ) * d ^ J ≤ ∑ j ∈ Finset.Icc 1 J, (j : ℝ) * d ^ j ∧
      ∑ j ∈ Finset.Icc 1 J, (j : ℝ) * d ^ j ≤ 2 * J * d ^ J := by
  constructor
  · rcases Nat.eq_zero_or_pos J with rfl | hJ
    · simp
    · have hnn : ∀ j ∈ Finset.Icc 1 J, 0 ≤ (j : ℝ) * d ^ j := fun j _ => by
        have : (0 : ℝ) ≤ d ^ j := pow_nonneg (by linarith) j
        positivity
      exact Finset.single_le_sum hnn (Finset.mem_Icc.2 ⟨hJ, le_rfl⟩)
  · have h := tOrdIdx_sum_pow_closed d J
    have hx : 1 ≤ d ^ J := one_le_pow₀ (by linarith)
    have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    have h1 : d * ((J * (d - 1) - 1) * d ^ J + 1) ≤ J * d * (d - 1) * d ^ J := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ d) (by linarith : (0 : ℝ) ≤ d ^ J - 1)]
    have h2 : (J : ℝ) * d * (d - 1) * d ^ J ≤ 2 * J * (d - 1) ^ 2 * d ^ J := by
      have : (0 : ℝ) ≤ J * (d - 1) * d ^ J := by
        have : (0 : ℝ) ≤ d - 1 := by linarith
        positivity
      nlinarith [mul_nonneg this (by linarith : (0 : ℝ) ≤ d - 2)]
    have hpos : (0 : ℝ) < (d - 1) ^ 2 := by nlinarith
    by_contra hc
    rw [not_le] at hc
    nlinarith [mul_lt_mul_of_pos_left hc hpos]

end Growth

end IUT.Audit.TensorOrderIndex
