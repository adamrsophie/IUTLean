import IUT.PaperIV.LocalFields.Bridge
import IUT.Prerequisites.PadicVolume

/-!
# The different and the normalization of a tensor product of two rings of integers

Sources: Mochizuki, *Inter-universal Teichmüller Theory IV*, Proposition 1.1 (page 9) with its
proof (pages 9 and 10), Proposition 1.2 (page 10) with its proof (page 11). Pages read for this
file: 9, 10 and 11. Pages checked against rendered images: 9, 10 and 11. Displays relied on:
* page 9: `R_E = ⊗_{i ∈ E} R_i` over `ℤ_p`, `𝔡_E = ∑_{i ∈ E} 𝔡_i`, `I* = I \ {*}`, and
  `p ^ (𝔡_{I*}) · (R_I)^∼ ⊆ R_I ⊆ (R_I)^∼`, where `(−)^∼` is "the normalization of the
  [reduced] ring in parentheses in its ring of fractions", `𝔡_i` is the order of any generator of
  the different ideal of `R_i` over `ℤ_p`, and `p ^ (𝔡_{I*})` may be taken to be a product of
  elements `p ^ (𝔡_i) ∈ R_i`, `i ∈ I*`. The exponent is `𝔡_{I*}` itself; no floor or ceiling;
* page 10: the proof reduces to `|I| = 2`, where "the desired inclusion follows immediately from
  the definition of the different ideal"; Proposition 1.2 (i) `p ^ (a_i) · R_i ⊆ log_p(R_i^×)`;
* page 11: the first display of the proof of Proposition 1.2 (ii),
  `p ^ (𝔡_I + a_I) · (R_I)^∼ ⊆ ⊗_{i ∈ I} p ^ (a_i) · R_i (⊆ R_I)`, derived from Proposition 1.1.

## The objects

`K₁`, `K₂` are finite extensions of `ℚ_[p]`; `R_i = integralClosure ℤ_[p] K_i`. As in
`IUT.Prerequisites.PadicVolume`, `R_E = R₁ ⊗_{ℤ_p} R₂` is taken as its image in
`K₁ ⊗[ℚ_p] K₂`, the additive span of the `x ⊗ y` with `x`, `y` integral over `ℤ_p`
(`padicPacketIntegers`), and `(R_E)^∼` is the set of elements of `K₁ ⊗[ℚ_p] K₂` integral over
`ℤ_p` (`padicPacketNormalization`); `R_E ⊆ (R_E)^∼` is `padicPacketIntegers_subset` there and is
not repeated here. The different is Mathlib's `differentIdeal ℤ_[p] R₂`. The page's
`p ^ (𝔡_2)` is an element of order `𝔡_2`, that is a generator of this ideal; the main theorem
holds for every element of the ideal, which contains the generators. Two factors only, with
`* = 1` and `I* = {2}`; by symmetry of the argument the case `I* = {1}` is the same statement
with the factors exchanged, which is not separately formalized.

## What is proved

* `tensorDiff_trace_one_tmul`: `Tr_{(A ⊗_R M)/A}(1 ⊗ y) = Tr_{M/R}(y)` for a finite free
  `R`-algebra `M` (from `LinearMap.trace_baseChange`).
* `tensorDiff_isIntegralElem_trace`: the trace over a field `F` of an element of a finite
  `F`-algebra that is integral over `R` (through `R → F`) is integral over `R`. Mathlib's
  `Algebra.isIntegral_trace` asks for a field on top, and `K₁ ⊗ K₂` is not one.
* `tensorDiff_mul_mem_packetIntegers`: for `δ` in the different of `R₂` over `ℤ_p` and `z` in
  `(R_E)^∼`, `(1 ⊗ δ) · z ∈ R_E`. Proof: with a `ℤ_p`-basis `b` of `R₂`, its trace dual basis
  `b^∨` spans `𝔇^{-1}` (`Submodule.traceDual_span_of_basis`, `coeSubmodule_differentIdeal`), so
  `δ b_j^∨ ∈ R₂`; the coordinate of `z` on `1 ⊗ b_j^∨` is `Tr_{(K₁ ⊗ K₂)/K₁}(z (1 ⊗ b_j))`,
  integral by the previous item.
* `tensorDiff_generator_mul_mem_packetIntegers`: the same for a generator `δ` of the different.
* `tensorDiff_order_mul_mem_packetIntegers`: the same for any `y ∈ K₂` with `ord(y) = 𝔡_2`
  (spectral norm `p ^ (−𝔡_2)`, `𝔡_2 = differentOrder` at a prime `P` over `p`), which is the
  page's `p ^ (𝔡_{I*})` for `I* = {2}`: Proposition 1.1 for two factors as printed.
* `tensorDiff_mul_mem_logUnit_span`: for `u_i` with `ord(u_i) = a_i`, `(u₁ ⊗ u₂ δ) · (R_E)^∼` lies
  in the span of `log_p(R₁^×) ⊗ log_p(R₂^×)`: the first display of page 11 for two factors
  (with `𝔡_{I*}` in place of `𝔡_I`; the page's form with `𝔡_I` is not derived), followed by
  Proposition 1.2 (i) (`padicBridge_extLogUnit_image_fractionalIdeal`).

## Not proved

* That `(R_E)^∼` is the normalization of `R_E` in its total ring of fractions: not proved here;
  it is proved in `TensorIndex.lean` (`tensorIdx_isFractionRing`).
* More than two factors (the induction on `|I|` of page 10), and the identification of
  `K₁ ⊗[ℤ_p] K₂` with `K₁ ⊗[ℚ_p] K₂`.
* Proposition 1.2 (ii) to (iv) themselves: not proved here; they are proved for two factors in
  `TensorLogShell.lean`.
-/

namespace IUT.PaperIV.LocalFields

open IUT.Prerequisites.PadicVolume

section Trace

/-- **The trace of a base change on a pure tensor**: for a finite free `R`-algebra `M` and any
commutative `R`-algebra `A`, the trace of `1 ⊗ y` in the `A`-algebra `A ⊗[R] M` is the image of
the trace of `y` in `M` over `R`. -/
theorem tensorDiff_trace_one_tmul {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [CommRing M] [Algebra R M] [Module.Free R M] [Module.Finite R M] (y : M) :
    Algebra.trace A (TensorProduct R A M) (TensorProduct.tmul R (1 : A) y) =
      algebraMap R A (Algebra.trace R M y) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
  congr 1
  refine TensorProduct.AlgebraTensorModule.ext fun a m => ?_
  simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- **The trace of an integral element is integral**, for a finite algebra `S` over a field `F`
that need not be a field (Mathlib's `Algebra.isIntegral_trace` asks for a field): if `w ∈ S` is
a root of a monic polynomial with coefficients in `R` (through a ring map `φ : R → F`), then so
is `Tr_{S/F}(w)`. The proof base changes to an algebraic closure of `F`, where the trace is the
sum of the eigenvalues of the multiplication by `w`, each a root of the same polynomial. -/
theorem tensorDiff_isIntegralElem_trace {R F S : Type*} [CommRing R] [Field F] [CommRing S]
    [Algebra F S] [Module.Finite F S] (φ : R →+* F) {w : S}
    (hw : ((algebraMap F S).comp φ).IsIntegralElem w) :
    φ.IsIntegralElem (Algebra.trace F S w) := by
  obtain ⟨g, hg, hgw⟩ := hw
  have htr := tensorDiff_trace_one_tmul (R := F) (A := AlgebraicClosure F) (M := S) w
  rw [Algebra.trace_apply] at htr
  have h1 : Polynomial.aeval w (g.map φ) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    exact hgw
  have h2 : Polynomial.aeval (TensorProduct.tmul F (1 : AlgebraicClosure F) w) (g.map φ) = 0 := by
    have h := Polynomial.aeval_algHom_apply
      (Algebra.TensorProduct.includeRight : S →ₐ[F] TensorProduct F (AlgebraicClosure F) S) w
      (g.map φ)
    rw [h1, map_zero, Algebra.TensorProduct.includeRight_apply] at h
    exact h
  have hG : Polynomial.aeval (Algebra.lmul (AlgebraicClosure F)
      (TensorProduct F (AlgebraicClosure F) S) (TensorProduct.tmul F (1 : AlgebraicClosure F) w))
      (g.map ((algebraMap F (AlgebraicClosure F)).comp φ)) = 0 := by
    rw [← Polynomial.map_map, Polynomial.aeval_algHom_apply, Polynomial.aeval_map_algebraMap, h2,
      map_zero]
  have hroot : ∀ μ ∈ (LinearMap.charpoly (Algebra.lmul (AlgebraicClosure F)
      (TensorProduct F (AlgebraicClosure F) S)
        (TensorProduct.tmul F (1 : AlgebraicClosure F) w))).roots,
      ((algebraMap F (AlgebraicClosure F)).comp φ).IsIntegralElem μ := by
    intro μ hμ
    have hr := (Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero).1 hμ
    have hm := Module.End.isRoot_of_hasEigenvalue
      ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).2 hr)
    obtain ⟨q, hq⟩ := minpoly.dvd (AlgebraicClosure F) _ hG
    refine ⟨g, hg, ?_⟩
    have h3 : (g.map ((algebraMap F (AlgebraicClosure F)).comp φ)).IsRoot μ := by
      rw [Polynomial.IsRoot.def, hq, Polynomial.eval_mul, Polynomial.IsRoot.def.1 hm, zero_mul]
    rwa [Polynomial.IsRoot.def, Polynomial.eval_map] at h3
  have hsum : ((algebraMap F (AlgebraicClosure F)).comp φ).IsIntegralElem
      (LinearMap.charpoly (Algebra.lmul (AlgebraicClosure F)
        (TensorProduct F (AlgebraicClosure F) S)
          (TensorProduct.tmul F (1 : AlgebraicClosure F) w))).roots.sum := by
    let _ : Algebra R (AlgebraicClosure F) := ((algebraMap F (AlgebraicClosure F)).comp φ).toAlgebra
    exact IsIntegral.multiset_sum hroot
  rw [← Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)] at hsum
  erw [htr] at hsum
  obtain ⟨g', hg', h0⟩ := hsum
  refine ⟨g', hg', (algebraMap F (AlgebraicClosure F)).injective ?_⟩
  rw [Polynomial.hom_eval₂, h0, map_zero]

end Trace

section Packet

variable (p : ℕ) [hp : Fact p.Prime]

/-- For a field `L` with compatible `ℤ_p`- and `ℚ_p`-algebra structures, `padicVolIntegral`
(integrality through `ℤ_p → ℚ_p → L`, used for `R_E` and `(R_E)^∼`) is membership in
`integralClosure ℤ_[p] L`. -/
theorem tensorDiff_padicVolIntegral_iff (L : Type*) [Field L] [Algebra ℚ_[p] L]
    [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] (x : L) :
    padicVolIntegral p x ↔ x ∈ integralClosure ℤ_[p] L := by
  rw [mem_integralClosure_iff]
  show _ ↔ (algebraMap ℤ_[p] L).IsIntegralElem x
  rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] L]
  rfl

variable (K₁ K₂ : Type*) [Field K₁] [Field K₂] [Algebra ℚ_[p] K₁] [Algebra ℚ_[p] K₂]
  [FiniteDimensional ℚ_[p] K₂] [Algebra ℤ_[p] K₂] [IsScalarTower ℤ_[p] ℚ_[p] K₂]

/-- **IUT IV Proposition 1.1 for two factors** (page 9, proof on pages 9 and 10), in ideal form:
let `R₂ = integralClosure ℤ_[p] K₂` and `δ` any element of the different ideal of `R₂` over
`ℤ_p`. For every `z` of `(R_E)^∼` (the elements of `K₁ ⊗[ℚ_p] K₂` integral over `ℤ_p`,
`padicPacketNormalization`), `(1 ⊗ δ) · z` lies in `R_E = R₁ ⊗ R₂` (the additive span of the
`x ⊗ y` with `x`, `y` integral, `padicPacketIntegers`). With `I = {1, 2}` and `* = 1`, so that
`I* = {2}`, this is `p ^ (𝔡_{I*}) · (R_I)^∼ ⊆ R_I` for every choice of `p ^ (𝔡_2)` in the
different (see `tensorDiff_generator_mul_mem_packetIntegers`). -/
theorem tensorDiff_mul_mem_packetIntegers {δ : integralClosure ℤ_[p] K₂}
    (hδ : letI := isDedekindDomain_ringOfIntegers_padic p K₂
      letI := isTorsionFree_ringOfIntegers_padic p K₂
      δ ∈ differentIdeal ℤ_[p] (integralClosure ℤ_[p] K₂))
    {z : TensorProduct ℚ_[p] K₁ K₂} (hz : z ∈ padicPacketNormalization p K₁ K₂) :
    TensorProduct.tmul ℚ_[p] (1 : K₁) (δ : K₂) * z ∈ padicPacketIntegers p K₁ K₂ := by
  classical
  let := isDedekindDomain_ringOfIntegers_padic p K₂
  let := isTorsionFree_ringOfIntegers_padic p K₂
  have : IsFractionRing (integralClosure ℤ_[p] K₂) K₂ :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[p] ℚ_[p] K₂ _
  have : Module.Finite ℤ_[p] (integralClosure ℤ_[p] K₂) :=
    IsIntegralClosure.finite ℤ_[p] ℚ_[p] K₂ _
  have : Module.Free ℤ_[p] (integralClosure ℤ_[p] K₂) := Module.free_of_finite_type_torsion_free'
  have : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure ℤ_[p] K₂)
      (nonZeroDivisors ℤ_[p])) K₂ :=
    IsIntegralClosure.isLocalization ℤ_[p] ℚ_[p] K₂ _
  set b₀ := Module.Free.chooseBasis ℤ_[p] (integralClosure ℤ_[p] K₂)
  set b := b₀.localizationLocalization ℚ_[p] (nonZeroDivisors ℤ_[p]) K₂
  have hbint : ∀ j, padicVolIntegral p (b j) := by
    intro j
    rw [tensorDiff_padicVolIntegral_iff, Module.Basis.localizationLocalization_apply]
    exact (b₀ j).2
  have hspan : (1 : Submodule (integralClosure ℤ_[p] K₂) K₂).restrictScalars ℤ_[p] =
      Submodule.span ℤ_[p] (Set.range b) := by
    rw [Module.Basis.localizationLocalization_span]
    ext x
    simp
  have hd : ∀ j, padicVolIntegral p ((δ : K₂) * b.traceDual j) := by
    intro j
    have hmem : b.traceDual j ∈
        Submodule.traceDual ℤ_[p] ℚ_[p] (1 : Submodule (integralClosure ℤ_[p] K₂) K₂) := by
      have h := Submodule.traceDual_span_of_basis ℤ_[p]
        (1 : Submodule (integralClosure ℤ_[p] K₂) K₂) b hspan
      have h' : b.traceDual j ∈ Submodule.span ℤ_[p] (Set.range b.traceDual) :=
        Submodule.subset_span ⟨j, rfl⟩
      rw [← h] at h'
      exact h'
    have hδ' : (δ : K₂) ∈ IsLocalization.coeSubmodule K₂
        (differentIdeal ℤ_[p] (integralClosure ℤ_[p] K₂)) :=
      (IsLocalization.mem_coeSubmodule K₂ _).2 ⟨δ, hδ, rfl⟩
    rw [coeSubmodule_differentIdeal ℤ_[p] ℚ_[p] (integralClosure ℤ_[p] K₂),
      Submodule.mem_div_iff_forall_mul_mem] at hδ'
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hδ' _ hmem)
    rw [tensorDiff_padicVolIntegral_iff, ← hr]
    exact r.2
  set D := Algebra.TensorProduct.basis K₁ b.traceDual
  have hD : ∀ i, D i = TensorProduct.tmul ℚ_[p] (1 : K₁) (b.traceDual i) := fun i =>
    Algebra.TensorProduct.basis_apply _ i
  have hc : ∀ j, Algebra.trace K₁ (TensorProduct ℚ_[p] K₁ K₂)
      (z * TensorProduct.tmul ℚ_[p] (1 : K₁) (b j)) = D.repr z j := by
    intro j
    conv_lhs => rw [← D.sum_repr z]
    simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, hD,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, tensorDiff_trace_one_tmul,
      Module.Basis.trace_traceDual_mul, smul_eq_mul]
    simp
  have hφ : (algebraMap K₁ (TensorProduct ℚ_[p] K₁ K₂)).comp
      ((algebraMap ℚ_[p] K₁).comp (algebraMap ℤ_[p] ℚ_[p])) =
      (algebraMap ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).comp (algebraMap ℤ_[p] ℚ_[p]) := by
    rw [IsScalarTower.algebraMap_eq ℚ_[p] K₁ (TensorProduct ℚ_[p] K₁ K₂)]
    rfl
  have hcint : ∀ j, padicVolIntegral p (D.repr z j) := by
    intro j
    rw [← hc j]
    have hb := padicVolIntegral_map p
      (Algebra.TensorProduct.includeRight : K₂ →ₐ[ℚ_[p]] TensorProduct ℚ_[p] K₁ K₂) (hbint j)
    rw [Algebra.TensorProduct.includeRight_apply] at hb
    refine tensorDiff_isIntegralElem_trace ((algebraMap ℚ_[p] K₁).comp (algebraMap ℤ_[p] ℚ_[p]))
      ?_
    rw [hφ]
    exact RingHom.IsIntegralElem.mul _ hz hb
  unfold padicPacketIntegers
  rw [SetLike.mem_coe, ← D.sum_repr z, Finset.mul_sum]
  refine sum_mem fun j _ => AddSubmonoid.subset_closure
    ⟨D.repr z j, (δ : K₂) * b.traceDual j, hcint j, hd j, ?_⟩
  rw [hD, mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]

/-- **IUT IV Proposition 1.1 for two factors, for a generator of the different** (page 9):
`p ^ (𝔡_{I*})` with `I* = {2}` taken as a generator of the different ideal of
`R₂ = integralClosure ℤ_[p] K₂` over `ℤ_p`. For any such generator `δ`,
`(1 ⊗ δ) · (R_I)^∼ ⊆ R_I` inside `K₁ ⊗[ℚ_p] K₂`. -/
theorem tensorDiff_generator_mul_mem_packetIntegers {δ : integralClosure ℤ_[p] K₂}
    (hδ : letI := isDedekindDomain_ringOfIntegers_padic p K₂
      letI := isTorsionFree_ringOfIntegers_padic p K₂
      Ideal.span {δ} = differentIdeal ℤ_[p] (integralClosure ℤ_[p] K₂))
    {z : TensorProduct ℚ_[p] K₁ K₂} (hz : z ∈ padicPacketNormalization p K₁ K₂) :
    TensorProduct.tmul ℚ_[p] (1 : K₁) (δ : K₂) * z ∈ padicPacketIntegers p K₁ K₂ := by
  refine tensorDiff_mul_mem_packetIntegers p K₁ K₂ ?_ hz
  let := isDedekindDomain_ringOfIntegers_padic p K₂
  let := isTorsionFree_ringOfIntegers_padic p K₂
  show δ ∈ differentIdeal ℤ_[p] (integralClosure ℤ_[p] K₂)
  rw [← hδ]
  exact Ideal.mem_span_singleton_self δ

/-- **IUT IV Proposition 1.1 for two factors, with `p ^ (𝔡_{I*})` given by its order** (page 9):
let `P` be a prime of `R₂ = integralClosure ℤ_[p] K₂` over `p` and `𝔡_2 = differentOrder` the
order of the different at `P` (exponent divided by the ramification index, normalized by
`ord(p) = 1`). Every `y ∈ K₂` with `ord(y) = 𝔡_2`, that is `‖y‖ = p ^ (−𝔡_2)` for the spectral
norm, satisfies `(1 ⊗ y) · (R_I)^∼ ⊆ R_I` inside `K₁ ⊗[ℚ_p] K₂`. Such `y` lies in the different:
`R₂` is a discrete valuation ring, the different is `(ϖ ^ n)` with `n` its exponent, and
`y / ϖ ^ n` has norm one. -/
theorem tensorDiff_order_mul_mem_packetIntegers (P : Ideal (integralClosure ℤ_[p] K₂))
    [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] {y : K₂}
    (hy : letI := isDedekindDomain_ringOfIntegers_padic p K₂;
      letI := isTorsionFree_ringOfIntegers_padic p K₂;
      letI := spectralNorm.normedField ℚ_[p] K₂;
      ‖y‖ = (p : ℝ) ^ (-differentOrder ℤ_[p] (integralClosure ℤ_[p] K₂) P))
    {z : TensorProduct ℚ_[p] K₁ K₂} (hz : z ∈ padicPacketNormalization p K₁ K₂) :
    TensorProduct.tmul ℚ_[p] (1 : K₁) y * z ∈ padicPacketIntegers p K₁ K₂ := by
  let := isDedekindDomain_ringOfIntegers_padic p K₂
  let := isTorsionFree_ringOfIntegers_padic p K₂
  let := spectralNorm.normedField ℚ_[p] K₂
  have := padicBridge_isLocalRing p K₂
  have := padicBridge_isDiscreteValuationRing p K₂
  have hy' : ‖y‖ = (p : ℝ) ^ (-((differentExponent ℤ_[p] (integralClosure ℤ_[p] K₂) P : ℝ) /
      (P.ramificationIdx ℤ_[p] : ℝ))) := hy
  obtain ⟨ϖ, hirr, hPϖ, -, hpos, -, hpe, -, -⟩ := padicBridge_uniformizer p K₂ P
  have hD := differentIdeal_ne_bot_of_isIntegralClosure ℤ_[p] ℚ_[p] K₂
    (integralClosure ℤ_[p] K₂)
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hD hirr
  have hP0 : P ≠ ⊥ := by
    rw [hPϖ, Ne, Ideal.span_singleton_eq_bot]
    exact hirr.ne_zero
  have hexp : differentExponent ℤ_[p] (integralClosure ℤ_[p] K₂) P = n := by
    unfold differentExponent
    rw [hn, ← Ideal.span_singleton_pow, ← hPϖ,
      multiplicity_pow_self_of_prime (Ideal.prime_of_isPrime hP0 inferInstance)]
  have he : P.ramificationIdx ℤ_[p] ≠ 0 :=
    (ramificationIdx_pos_of_liesOver (IsDiscreteValuationRing.not_a_field ℤ_[p]) P).ne'
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hr := padicBridge_rpow_of_pow_eq p hpos.le he hpe
  have hyn : ‖y‖ = ‖(ϖ : K₂)‖ ^ n := by
    rw [hy', hexp, hr, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    congr 1
    ring
  have hint : IsIntegral ℤ_[p] (y / (ϖ : K₂) ^ n) := by
    refine (padicBridge_norm_le_one_iff_isIntegral p K₂ _).1 ?_
    rw [norm_div, norm_pow, hyn, div_self (pow_ne_zero _ hpos.ne')]
  set u : integralClosure ℤ_[p] K₂ := ⟨y / (ϖ : K₂) ^ n, hint⟩
  have hyδ : ((ϖ ^ n * u : integralClosure ℤ_[p] K₂) : K₂) = y := by
    rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
    exact mul_div_cancel₀ y (pow_ne_zero n (norm_pos_iff.mp hpos))
  have hmem : ϖ ^ n * u ∈ differentIdeal ℤ_[p] (integralClosure ℤ_[p] K₂) := by
    rw [hn]
    exact Ideal.mul_mem_right u _ (Ideal.mem_span_singleton_self _)
  rw [← hyδ]
  exact tensorDiff_mul_mem_packetIntegers p K₁ K₂ hmem hz

/-- **The first display of the proof of IUT IV Proposition 1.2 (ii), for two factors** (page 11),
combined with Proposition 1.2 (i): with `R_i = integralClosure ℤ_[p] K_i`, `e_i` the ramification
index of a prime `P_i` of `R_i` over `p`, `a_i` the constant of page 10, any `u_i ∈ K_i` with
`ord(u_i) = a_i` (that is `‖u_i‖ = p ^ (-a_i)` for the spectral norm), and `δ` in the different
of `R₂` over `ℤ_p`: for every `z` of `(R_E)^∼`, `(u₁ ⊗ u₂ δ) · z` lies in the additive span of
the `x ⊗ y` with `x ∈ log_p(R₁^×)` and `y ∈ log_p(R₂^×)`, the image of
`log_p(R₁^×) ⊗_{ℤ_p} log_p(R₂^×)` in `K₁ ⊗[ℚ_p] K₂`. The page multiplies by `p ^ (𝔡_I + a_I)`;
here only the different of the second factor is used (`I* = {2}`), which is stronger. -/
theorem tensorDiff_mul_mem_logUnit_span [FiniteDimensional ℚ_[p] K₁] [Algebra ℤ_[p] K₁]
    [IsScalarTower ℤ_[p] ℚ_[p] K₁]
    (P₁ : Ideal (integralClosure ℤ_[p] K₁)) [P₁.IsPrime]
    [P₁.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (P₂ : Ideal (integralClosure ℤ_[p] K₂)) [P₂.IsPrime]
    [P₂.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    {δ : integralClosure ℤ_[p] K₂}
    (hδ : letI := isDedekindDomain_ringOfIntegers_padic p K₂
      letI := isTorsionFree_ringOfIntegers_padic p K₂
      δ ∈ differentIdeal ℤ_[p] (integralClosure ℤ_[p] K₂))
    {u₁ : K₁} {u₂ : K₂}
    (hu₁ : letI := spectralNorm.normedField ℚ_[p] K₁;
      ‖u₁‖ = (p : ℝ) ^ (-Proposition1_2.a p (P₁.ramificationIdx ℤ_[p])))
    (hu₂ : letI := spectralNorm.normedField ℚ_[p] K₂;
      ‖u₂‖ = (p : ℝ) ^ (-Proposition1_2.a p (P₂.ramificationIdx ℤ_[p])))
    {z : TensorProduct ℚ_[p] K₁ K₂} (hz : z ∈ padicPacketNormalization p K₁ K₂) :
    TensorProduct.tmul ℚ_[p] u₁ (u₂ * δ) * z ∈ AddSubmonoid.closure
      {w | ∃ x y, x ∈ @extLogUnit K₁ (spectralNorm.normedField ℚ_[p] K₁) '' Set.range
          (fun u : (integralClosure ℤ_[p] K₁)ˣ => ((u : integralClosure ℤ_[p] K₁) : K₁)) ∧
        y ∈ @extLogUnit K₂ (spectralNorm.normedField ℚ_[p] K₂) '' Set.range
          (fun u : (integralClosure ℤ_[p] K₂)ˣ => ((u : integralClosure ℤ_[p] K₂) : K₂)) ∧
        w = TensorProduct.tmul ℚ_[p] x y} := by
  obtain ⟨-, ⟨w₁, hw₁⟩, H₁⟩ := padicBridge_extLogUnit_image_fractionalIdeal p K₁ P₁
  obtain ⟨-, ⟨w₂, hw₂⟩, H₂⟩ := padicBridge_extLogUnit_image_fractionalIdeal p K₂ P₂
  have hS₁ := (H₁ u₁ w₁ hu₁ hw₁).1
  have hS₂ := (H₂ u₂ w₂ hu₂ hw₂).1
  have hmem := tensorDiff_mul_mem_packetIntegers p K₁ K₂ hδ hz
  have heq : TensorProduct.tmul ℚ_[p] u₁ (u₂ * δ) * z =
      TensorProduct.tmul ℚ_[p] u₁ u₂ * (TensorProduct.tmul ℚ_[p] (1 : K₁) (δ : K₂) * z) := by
    rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [heq]
  unfold padicPacketIntegers at hmem
  rw [SetLike.mem_coe] at hmem
  generalize TensorProduct.tmul ℚ_[p] (1 : K₁) (δ : K₂) * z = t at hmem ⊢
  induction hmem using AddSubmonoid.closure_induction with
  | mem w hw =>
    obtain ⟨x, y, hx, hy, rfl⟩ := hw
    refine AddSubmonoid.subset_closure
      ⟨u₁ * x, u₂ * y, hS₁ ⟨⟨x, ?_⟩, rfl⟩, hS₂ ⟨⟨y, ?_⟩, rfl⟩, ?_⟩
    · exact (tensorDiff_padicVolIntegral_iff p K₁ x).1 hx
    · exact (tensorDiff_padicVolIntegral_iff p K₂ y).1 hy
    · rw [Algebra.TensorProduct.tmul_mul_tmul]
  | zero =>
    rw [mul_zero]
    exact zero_mem _
  | add a b _ _ ha hb =>
    rw [mul_add]
    exact add_mem ha hb

end Packet

end IUT.PaperIV.LocalFields
