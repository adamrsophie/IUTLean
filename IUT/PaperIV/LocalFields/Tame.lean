import IUT.PaperIV.LocalFields.Bridge
import IUT.PaperIV.Proposition1_3

/-!
# IUT IV, Proposition 1.3 (i) for `k_0 = ℚ_p`: the tame equality and the wild inequality

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Propositions 1.1 and 1.3, pages 9 to
13 of the April 2020 manuscript. Pages read for this file: 8 to 13. Pages checked against
rendered images: 8 to 13 (the normalization `ord(p) = 1` and the definition of `𝔡_i` on page 9;
Proposition 1.1 on page 9; Proposition 1.3 (i), `𝔡_i ≥ 𝔡_0 + (e_{i/0} - 1)/e_i` with equality
when `k_i` is tamely ramified over `k_0`, on pages 11 and 12; Proposition 1.3 (ii),
`𝔡_i ≤ 𝔡_0 + n_i + 1/e_0`, on page 12, with its proof on pages 12 and 13).

The objects are those of `IUT.PaperIV.LocalFields.Padic`: `L = k_i` a finite extension of `ℚ_[p]`,
`R = integralClosure ℤ_[p] L` its ring of integers, `P` a prime of `R` over `pℤ_p`, `e` its
ramification index, `differentExponent ℤ_[p] R P` the exponent of `P` in the different, and
`𝔡 = differentOrder ℤ_[p] R P` (that exponent divided by `e`, the normalization `ord(p) = 1`).
Here `k_0 = ℚ_p`, so `𝔡_0 = 0`, `e_0 = 1` and `e_{i/0} = e`; `k_i` is tamely ramified over `ℚ_p`
exactly when `p` does not divide `e`. The locality of `R` and the uniqueness of `P` come from
`IUT.PaperIV.LocalFields.Bridge`.

What is proved:

* `trace_eq_add_of_exact`, `trace_quotient_eq_add_of_mul_exact`: the trace of an endomorphism is
  additive along a short exact sequence of finite-dimensional vector spaces, and the trace over
  `R ⧸ m` of a quotient `S ⧸ I` splits along `0 → S ⧸ K → S ⧸ I → S ⧸ J → 0` (multiplication by
  an element);
* `map_maximalIdeal_eq_pow_padic`: `pR = P ^ e`;
* `trace_quotient_pow_padic`, `intTrace_mk_eq_padic`: the trace from `R ⧸ P ^ n` to `𝔽_p` is `n`
  times the trace from `R ⧸ P` (`1 ≤ n ≤ e`), so the trace from `R` to `ℤ_[p]` is, modulo `p`,
  `e` times the residue field trace;
* `differentExponent_lt_of_intTrace_notMem_padic`: an element whose trace is a unit of `ℤ_[p]`
  forces `differentExponent < e`;
* `differentExponent_eq_of_not_dvd_ramificationIdx_padic`: **the tame equality** of Proposition
  1.3 (i): if `p ∤ e` then `differentExponent = e - 1`; and
  `differentOrder_eq_of_not_dvd_ramificationIdx_padic`, the same as `𝔡 = (e - 1)/e`;
* `ramificationIdx_le_differentExponent_of_dvd_padic`: **the wild inequality**: if `p ∣ e` then
  `differentExponent ≥ e`; and `one_le_differentOrder_of_dvd_ramificationIdx_padic`, `𝔡 ≥ 1`;
* `differentExponent_eq_ramificationIdx_sub_one_iff_padic`: the equality of Proposition 1.3 (i)
  holds exactly in the tame case;
* `differentOrder_le_one_of_not_dvd_ramificationIdx_padic`: Proposition 1.3 (ii) in its base case
  `k_0 = ℚ_p`, `k_1 = k_i` tame (`n_i = 0`): `𝔡 ≤ 1`, through `Proposition1_3.ii_base`.

Not formalized here: Proposition 1.3 over a general base `k_0`, which is in `Tower.lean` ((i),
and (ii) in the tame and `n_i = 0` cases); Proposition 1.1, of which the first inclusion for two
factors is in `TensorDifferent.lean`.
-/

open Ideal nonZeroDivisors

namespace IUT.PaperIV.LocalFields

/-! ## Additivity of the trace along a short exact sequence -/

section TraceAdditivity

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- **Additivity of the trace**: for an endomorphism `f` of a finite-dimensional vector space `V`
preserving a subspace `W`, `tr f = tr (f|W) + tr (f on V/W)`. -/
theorem trace_eq_trace_restrict_add_trace_mapQ (W : Submodule k V) (f : V →ₗ[k] V)
    (hf : W ≤ W.comap f) :
    LinearMap.trace k V f =
      LinearMap.trace k W (f.restrict hf) + LinearMap.trace k (V ⧸ W) (W.mapQ W f hf) := by
  classical
  obtain ⟨bW⟩ : Nonempty (Module.Basis (Fin (Module.finrank k W)) k W) :=
    ⟨Module.finBasis k W⟩
  obtain ⟨bQ⟩ : Nonempty (Module.Basis (Fin (Module.finrank k (V ⧸ W))) k (V ⧸ W)) :=
    ⟨Module.finBasis k (V ⧸ W)⟩
  rw [LinearMap.trace_eq_matrix_trace k (Module.Basis.sumQuot bW bQ),
    LinearMap.trace_eq_matrix_trace k bW, LinearMap.trace_eq_matrix_trace k bQ]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, LinearMap.toMatrix_apply]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.Basis.sumQuot_inl,
      Module.Basis.sumQuot_repr_inl_of_mem bW bQ _ (hf (bW i).2) i]
    rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Module.Basis.sumQuot_repr_inr, ← Module.Basis.sumQuot_inr bW bQ j, Submodule.mapQ_apply]
    rfl

/-- **Additivity of the trace along a short exact sequence** `0 → U → V → X → 0` of
finite-dimensional vector spaces, for compatible endomorphisms `g`, `f`, `h` of `U`, `V`, `X`:
`tr f = tr g + tr h`. -/
theorem trace_eq_add_of_exact {U X : Type*} [AddCommGroup U] [Module k U] [AddCommGroup X]
    [Module k X] (i : U →ₗ[k] V) (q : V →ₗ[k] X) (hi : Function.Injective i)
    (hq : Function.Surjective q) (hex : LinearMap.range i = LinearMap.ker q)
    (f : V →ₗ[k] V) (g : U →ₗ[k] U) (h : X →ₗ[k] X) (hfi : ∀ u, f (i u) = i (g u))
    (hfq : ∀ v, q (f v) = h (q v)) :
    LinearMap.trace k V f = LinearMap.trace k U g + LinearMap.trace k X h := by
  have hf : LinearMap.range i ≤ (LinearMap.range i).comap f := by
    rintro _ ⟨u, rfl⟩
    exact ⟨g u, (hfi u).symm⟩
  rw [trace_eq_trace_restrict_add_trace_mapQ _ f hf]
  let e1 : U ≃ₗ[k] LinearMap.range i := LinearEquiv.ofInjective i hi
  let e2 : (V ⧸ LinearMap.range i) ≃ₗ[k] X :=
    (Submodule.quotEquivOfEq _ _ hex).trans (q.quotKerEquivOfSurjective hq)
  have he2 : ∀ v, e2 (Submodule.Quotient.mk v) = q v := fun v => rfl
  congr 1
  · rw [← LinearMap.trace_conj' g e1]
    congr 1
    refine LinearMap.ext fun w => ?_
    obtain ⟨u, rfl⟩ := e1.surjective w
    apply Subtype.ext
    simp only [LinearMap.coe_restrict_apply, LinearEquiv.conj_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, e1, LinearEquiv.ofInjective_apply, hfi]
  · rw [← LinearMap.trace_conj' (Submodule.mapQ _ _ f hf) e2]
    congr 1
    refine LinearMap.ext fun x => ?_
    obtain ⟨v, rfl⟩ := hq x
    have h1 : e2.symm (q v) = Submodule.Quotient.mk v := by
      rw [← he2 v, LinearEquiv.symm_apply_apply]
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, h1,
      Submodule.mapQ_apply, he2, hfq]

end TraceAdditivity

/-- In a quotient `S ⧸ I` with `m ≤ I ∩ R`, the action of `R ⧸ m` through
`Ideal.Quotient.algebraQuotientOfLEComap` is the action of `R` through `S`. -/
theorem quotient_smul_eq_of_le_comap {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {m : Ideal R} {I : Ideal S} (h : m ≤ I.comap (algebraMap R S)) (a : R) (x : S ⧸ I) :
    letI := Ideal.Quotient.algebraQuotientOfLEComap h
    Ideal.Quotient.mk m a • x = algebraMap R S a • x := by
  let := Ideal.Quotient.algebraQuotientOfLEComap h
  rw [Algebra.smul_def, Algebra.smul_def]
  rfl

/-- **Additivity of the trace on quotients along multiplication by an element.** Let `m` be a
maximal ideal of `R`, mapping into the ideals `I`, `J`, `K` of the `R`-algebra `S`, with `I ≤ J`,
`π * b ∈ I ↔ b ∈ K` and `v ∈ J ↔ ∃ b, v - π * b ∈ I`. Then `0 → S ⧸ K → S ⧸ I → S ⧸ J → 0`
(the first map is multiplication by `π`) is exact, and the traces over the field `R ⧸ m` add:
`Tr_{S ⧸ I} = Tr_{S ⧸ K} + Tr_{S ⧸ J}`. -/
theorem trace_quotient_eq_add_of_mul_exact {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {m : Ideal R} [m.IsMaximal] {I J K : Ideal S} (hI : m ≤ I.comap (algebraMap R S))
    (hJ : m ≤ J.comap (algebraMap R S)) (hK : m ≤ K.comap (algebraMap R S)) (π : S)
    (hle : I ≤ J) (hKI : ∀ b, π * b ∈ I ↔ b ∈ K) (hJI : ∀ v, v ∈ J ↔ ∃ b, v - π * b ∈ I)
    (hfin : letI := Ideal.Quotient.algebraQuotientOfLEComap hI
      Module.Finite (R ⧸ m) (S ⧸ I)) (y : S) :
    letI := Ideal.Quotient.algebraQuotientOfLEComap hI
    letI := Ideal.Quotient.algebraQuotientOfLEComap hJ
    letI := Ideal.Quotient.algebraQuotientOfLEComap hK
    Algebra.trace (R ⧸ m) (S ⧸ I) (Ideal.Quotient.mk I y) =
      Algebra.trace (R ⧸ m) (S ⧸ K) (Ideal.Quotient.mk K y) +
        Algebra.trace (R ⧸ m) (S ⧸ J) (Ideal.Quotient.mk J y) := by
  let := Ideal.Quotient.field m
  let := Ideal.Quotient.algebraQuotientOfLEComap hI
  let := Ideal.Quotient.algebraQuotientOfLEComap hJ
  let := Ideal.Quotient.algebraQuotientOfLEComap hK
  have : FiniteDimensional (R ⧸ m) (S ⧸ I) := hfin
  let iS : (S ⧸ K) →ₗ[S] (S ⧸ I) :=
    K.liftQ ((Ideal.Quotient.mkₐ S I).toLinearMap ∘ₗ LinearMap.mulLeft S π) (by
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulLeft_apply,
        AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact (hKI x).mpr hx)
  let i : (S ⧸ K) →ₗ[R ⧸ m] (S ⧸ I) :=
    { toFun := iS
      map_add' := iS.map_add
      map_smul' := fun c x => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
        rw [RingHom.id_apply, quotient_smul_eq_of_le_comap hK, quotient_smul_eq_of_le_comap hI,
          iS.map_smul] }
  let q : (S ⧸ I) →ₗ[R ⧸ m] (S ⧸ J) :=
    { toFun := fun x => Ideal.Quotient.factor hle x
      map_add' := (Ideal.Quotient.factor hle).map_add
      map_smul' := fun c x => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
        rw [RingHom.id_apply, quotient_smul_eq_of_le_comap hI, quotient_smul_eq_of_le_comap hJ,
          Algebra.smul_def, Algebra.smul_def, RingHom.map_mul, Ideal.Quotient.algebraMap_eq,
          Ideal.Quotient.algebraMap_eq, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk] }
  have hiapp : ∀ b, i (Ideal.Quotient.mk K b) = Ideal.Quotient.mk I (π * b) := fun b => rfl
  have hqapp : ∀ b, q (Ideal.Quotient.mk I b) = Ideal.Quotient.mk J b := fun b => rfl
  have hi : Function.Injective i := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective u
    rw [hiapp, Ideal.Quotient.eq_zero_iff_mem, hKI] at hu
    rwa [Ideal.Quotient.eq_zero_iff_mem]
  have hq : Function.Surjective q := fun x => by
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk I v, hqapp v⟩
  have hex : LinearMap.range i = LinearMap.ker q := by
    ext w
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective w
    rw [LinearMap.mem_range, LinearMap.mem_ker, hqapp, Ideal.Quotient.eq_zero_iff_mem, hJI]
    constructor
    · rintro ⟨u, hu⟩
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective u
      rw [hiapp, Ideal.Quotient.eq] at hu
      refine ⟨b, ?_⟩
      rw [← neg_sub]
      exact I.neg_mem hu
    · rintro ⟨b, hb⟩
      refine ⟨Ideal.Quotient.mk K b, ?_⟩
      rw [hiapp, Ideal.Quotient.eq, ← neg_sub]
      exact I.neg_mem hb
  have : FiniteDimensional (R ⧸ m) (S ⧸ J) := Module.Finite.of_surjective q hq
  have : FiniteDimensional (R ⧸ m) (S ⧸ K) := Module.Finite.of_injective i hi
  have hfi : ∀ u, Algebra.lmul (R ⧸ m) (S ⧸ I) (Ideal.Quotient.mk I y) (i u) =
      i (Algebra.lmul (R ⧸ m) (S ⧸ K) (Ideal.Quotient.mk K y) u) := by
    intro u
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective u
    simp only [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
    show Ideal.Quotient.mk I y * Ideal.Quotient.mk I (π * b) = Ideal.Quotient.mk I (π * (y * b))
    rw [← RingHom.map_mul]
    congr 1
    ring
  have hfq : ∀ v, q (Algebra.lmul (R ⧸ m) (S ⧸ I) (Ideal.Quotient.mk I y) v) =
      Algebra.lmul (R ⧸ m) (S ⧸ J) (Ideal.Quotient.mk J y) (q v) := by
    intro v
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
    simp only [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
    show Ideal.Quotient.mk J (y * b) = Ideal.Quotient.mk J y * Ideal.Quotient.mk J b
    rw [RingHom.map_mul]
  have key := trace_eq_add_of_exact i q hi hq hex _ _ _ hfi hfq
  rw [Algebra.trace_apply, Algebra.trace_apply, Algebra.trace_apply]
  exact key

variable (p : ℕ) [Fact p.Prime] (L : Type*) [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
  [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L]

/-! ## The prime over `p` and `p·R = P ^ e` -/

/-- The ring of integers of a finite extension of `ℚ_[p]` is a finite `ℤ_[p]`-module. -/
theorem moduleFinite_padicIntegers : Module.Finite ℤ_[p] (integralClosure ℤ_[p] L) :=
  IsIntegralClosure.finite ℤ_[p] ℚ_[p] L _

/-- `p·R = P^e` for the prime `P` of the ring of integers `R` over `p`, `e` its ramification
index. -/
theorem map_maximalIdeal_eq_pow_padic (P : Ideal (integralClosure ℤ_[p] L)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    (IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] (integralClosure ℤ_[p] L)) =
      P ^ P.ramificationIdx ℤ_[p] := by
  have := isDedekindDomain_ringOfIntegers_padic p L
  have := padicBridge_isLocalRing p L
  have := isTorsionFree_ringOfIntegers_padic p L
  have hp : IsLocalRing.maximalIdeal ℤ_[p] ≠ ⊥ := IsDiscreteValuationRing.not_a_field ℤ_[p]
  have hp' : (IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] (integralClosure ℤ_[p] L)) ≠ ⊥
      :=
    map_ne_bot_of_ne_bot hp
  have hPm : P = IsLocalRing.maximalIdeal _ := padicBridge_prime_eq_maximalIdeal p L P
  have : P.IsMaximal := hPm ▸ inferInstance
  obtain ⟨Q, h1, h2⟩ := Ideal.eq_prime_pow_mul_coprime hp' P
  rw [← IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count _ _ hp'] at h2
  have hQ : Q = ⊤ := by
    by_contra hQ
    have : Q ≤ P := hPm ▸ IsLocalRing.le_maximalIdeal hQ
    rw [sup_eq_left.mpr this] at h1
    exact IsPrime.ne_top inferInstance h1
  rw [h2, hQ, mul_top]

/-! ## The different exponent is `e - 1` when a trace is a unit -/

/-- If some element of the ring of integers has trace (to `ℤ_[p]`) not divisible by `p`, then
`P^e` does not divide the different, so the exponent of the different is `< e`. -/
theorem differentExponent_lt_of_intTrace_notMem_padic (P : Ideal (integralClosure ℤ_[p] L))
    [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] (x : integralClosure ℤ_[p] L)
    (hx : letI := isDedekindDomain_ringOfIntegers_padic p L
      haveI := isTorsionFree_ringOfIntegers_padic p L
      haveI := moduleFinite_padicIntegers p L
      Algebra.intTrace ℤ_[p] (integralClosure ℤ_[p] L) x ∉ IsLocalRing.maximalIdeal ℤ_[p]) :
    letI := isDedekindDomain_ringOfIntegers_padic p L
    letI := isTorsionFree_ringOfIntegers_padic p L
    differentExponent ℤ_[p] (integralClosure ℤ_[p] L) P < P.ramificationIdx ℤ_[p] := by
  have := isDedekindDomain_ringOfIntegers_padic p L
  have := isTorsionFree_ringOfIntegers_padic p L
  have : IsFractionRing (integralClosure ℤ_[p] L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[p] ℚ_[p] L _
  have : Module.Finite ℤ_[p] (integralClosure ℤ_[p] L) :=
    IsIntegralClosure.finite ℤ_[p] ℚ_[p] L _
  let := FractionRing.liftAlgebra ℤ_[p] (FractionRing (integralClosure ℤ_[p] L))
  have : IsScalarTower ℤ_[p] (FractionRing ℤ_[p]) (FractionRing (integralClosure ℤ_[p] L)) :=
    FractionRing.isScalarTower_liftAlgebra _ _
  have H : RingHom.comp (algebraMap (FractionRing ℤ_[p]) (FractionRing (integralClosure ℤ_[p] L)))
      ↑(FractionRing.algEquiv ℤ_[p] ℚ_[p]).symm.toRingEquiv =
        RingHom.comp ↑(FractionRing.algEquiv (integralClosure ℤ_[p] L) L).symm.toRingEquiv
          (algebraMap ℚ_[p] L) := by
    apply IsLocalization.ringHom_ext ℤ_[p]⁰
    ext
    simp only [RingHom.coe_comp, RingHom.coe_coe,
      AlgEquiv.coe_toRingEquiv, Function.comp_apply, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply ℤ_[p] (integralClosure ℤ_[p] L) L, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
  have : Algebra.IsSeparable (FractionRing ℤ_[p]) (FractionRing (integralClosure ℤ_[p] L)) :=
    Algebra.IsSeparable.of_equiv_equiv _ _ H
  have hmap := map_maximalIdeal_eq_pow_padic p L P
  have hnd := not_dvd_differentIdeal_of_intTrace_notMem ℤ_[p] (P ^ P.ramificationIdx ℤ_[p]) ⊤
    (by rw [mul_top]; exact hmap.symm) x Submodule.mem_top hx
  exact lt_of_not_ge fun hle => hnd ((pow_dvd_pow P hle).trans (pow_multiplicity_dvd P _))


/-! ## The trace on `R ⧸ P ^ n` -/

/-- The maximal ideal of `ℤ_[p]` maps into `P ^ n` for `n ≤ e`. -/
theorem le_comap_pow_padic (P : Ideal (integralClosure ℤ_[p] L)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] {n : ℕ} (hn : n ≤ P.ramificationIdx ℤ_[p]) :
    IsLocalRing.maximalIdeal ℤ_[p] ≤ (P ^ n).comap (algebraMap ℤ_[p] (integralClosure ℤ_[p] L)) :=
        by
  rw [← Ideal.map_le_iff_le_comap, map_maximalIdeal_eq_pow_padic p L P]
  exact Ideal.pow_le_pow_right hn

/-- The prime `P` over `p` is principal, generated by a nonzero element. -/
theorem exists_span_eq_padic (P : Ideal (integralClosure ℤ_[p] L)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    ∃ π : integralClosure ℤ_[p] L, π ≠ 0 ∧ P = Ideal.span {π} := by
  have := isDedekindDomain_ringOfIntegers_padic p L
  have := padicBridge_isLocalRing p L
  have := padicBridge_isDiscreteValuationRing p L
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := integralClosure ℤ_[p] L)
  exact ⟨π, hπ.ne_zero, (padicBridge_prime_eq_maximalIdeal p L P).trans hπ.maximalIdeal_eq⟩

/-- **The trace of `R ⧸ P ^ n` over the residue field `𝔽_p` of `ℤ_[p]`** (`1 ≤ n ≤ e`): the
trace of the class of `y` is `n` times the trace of its class in `R ⧸ P`. The filtration
`P ^ i / P ^ n` has graded pieces `P ^ i / P ^ (i + 1) ≅ R ⧸ P` (multiplication by `π ^ i`). -/
theorem trace_quotient_pow_padic (P : Ideal (integralClosure ℤ_[p] L)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] (he : 1 ≤ P.ramificationIdx ℤ_[p])
    (y : integralClosure ℤ_[p] L)
    (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ P.ramificationIdx ℤ_[p]) :
    letI := Ideal.Quotient.algebraQuotientOfLEComap (le_comap_pow_padic p L P hn)
    letI := Ideal.Quotient.algebraQuotientOfLEComap (le_comap_pow_padic p L P he)
    Algebra.trace (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) (integralClosure ℤ_[p] L ⧸ P ^ n)
        (Ideal.Quotient.mk _ y) =
      n • Algebra.trace (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) (integralClosure ℤ_[p] L ⧸ P ^ 1)
        (Ideal.Quotient.mk _ y) := by
  obtain ⟨π, hπ0, hP⟩ := exists_span_eq_padic p L P
  have hpow : ∀ m, P ^ m = Ideal.span {π ^ m} := fun m => by rw [hP, Ideal.span_singleton_pow]
  have : Module.Finite ℤ_[p] (integralClosure ℤ_[p] L) := IsIntegralClosure.finite ℤ_[p] ℚ_[p] L _
  induction n, hn1 using Nat.le_induction with
  | base =>
    rw [one_smul]
  | succ n hn1 ih =>
    have hn' : n ≤ P.ramificationIdx ℤ_[p] := by omega
    have hKI : ∀ b, π ^ n * b ∈ P ^ (n + 1) ↔ b ∈ P ^ 1 := fun b => by
      rw [hpow, hpow, Ideal.mem_span_singleton, Ideal.mem_span_singleton, pow_succ, pow_one]
      exact mul_dvd_mul_iff_left (pow_ne_zero n hπ0)
    have hJI : ∀ v, v ∈ P ^ n ↔ ∃ b, v - π ^ n * b ∈ P ^ (n + 1) := fun v => by
      rw [hpow, Ideal.mem_span_singleton]
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨b, by rw [sub_self]; exact Ideal.zero_mem _⟩
      · rintro ⟨b, hb⟩
        rw [hpow, Ideal.mem_span_singleton] at hb
        have h1 : π ^ n ∣ v - π ^ n * b := (pow_dvd_pow π (Nat.le_succ n)).trans hb
        simpa using dvd_add h1 (dvd_mul_right (π ^ n) b)
    have hfin : letI := Ideal.Quotient.algebraQuotientOfLEComap (le_comap_pow_padic p L P hn)
        Module.Finite (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) (integralClosure ℤ_[p] L ⧸ P ^ (n +
            1)) := by
      let := Ideal.Quotient.algebraQuotientOfLEComap (le_comap_pow_padic p L P hn)
      have : IsScalarTower ℤ_[p] (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p])
          (integralClosure ℤ_[p] L ⧸ P ^ (n + 1)) := .of_algebraMap_eq' rfl
      have : Module.Finite ℤ_[p] (integralClosure ℤ_[p] L ⧸ P ^ (n + 1)) :=
        Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ_[p] _).toLinearMap
          Ideal.Quotient.mk_surjective
      exact Module.Finite.of_restrictScalars_finite ℤ_[p] _ _
    have key := trace_quotient_eq_add_of_mul_exact (le_comap_pow_padic p L P hn)
      (le_comap_pow_padic p L P hn') (le_comap_pow_padic p L P he) (π ^ n)
      (Ideal.pow_le_pow_right (I := P) (Nat.le_succ n)) hKI hJI hfin y
    rw [key, ih hn', succ_nsmul, add_comm]

/-- **The trace from `R` to `ℤ_[p]`, modulo `p`**: for `z` in the ring of integers `R`, the class
of its trace in `ℤ_[p] ⧸ (p) = 𝔽_p` is `e` times the trace of the class of `z` in `R ⧸ P` (here
written `R ⧸ P ^ 1`), `e` the ramification index. -/
theorem intTrace_mk_eq_padic (P : Ideal (integralClosure ℤ_[p] L)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] (he : 1 ≤ P.ramificationIdx ℤ_[p])
    (z : integralClosure ℤ_[p] L) :
    letI := isDedekindDomain_ringOfIntegers_padic p L
    haveI := isTorsionFree_ringOfIntegers_padic p L
    haveI := moduleFinite_padicIntegers p L
    letI := Ideal.Quotient.algebraQuotientOfLEComap (le_comap_pow_padic p L P he)
    P.ramificationIdx ℤ_[p] • Algebra.trace (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p])
        (integralClosure ℤ_[p] L ⧸ P ^ 1) (Ideal.Quotient.mk _ z) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal ℤ_[p])
        (Algebra.intTrace ℤ_[p] (integralClosure ℤ_[p] L) z) := by
  have := isDedekindDomain_ringOfIntegers_padic p L
  have := isTorsionFree_ringOfIntegers_padic p L
  have := moduleFinite_padicIntegers p L
  let := Ideal.Quotient.algebraQuotientOfLEComap (le_comap_pow_padic p L P he)
  let := Ideal.Quotient.algebraQuotientOfLEComap (le_comap_pow_padic p L P (le_refl _))
  have htr : Algebra.trace (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p])
      (integralClosure ℤ_[p] L ⧸ P ^ P.ramificationIdx ℤ_[p]) (Ideal.Quotient.mk _ z) =
      P.ramificationIdx ℤ_[p] • Algebra.trace (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p])
        (integralClosure ℤ_[p] L ⧸ P ^ 1) (Ideal.Quotient.mk _ z) :=
    trace_quotient_pow_padic p L P he z _ he le_rfl
  have hmap := map_maximalIdeal_eq_pow_padic p L P
  let φ : (integralClosure ℤ_[p] L ⧸
      (IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] (integralClosure ℤ_[p] L))) ≃ₐ[ℤ_[p] ⧸
        IsLocalRing.maximalIdeal ℤ_[p]] (integralClosure ℤ_[p] L ⧸ P ^ P.ramificationIdx ℤ_[p]) :=
    { Ideal.quotEquivOfEq hmap with commutes' := Quotient.ind fun _ => rfl }
  rw [← htr, ← Algebra.trace_quotient_eq_of_isDedekindDomain, ← Algebra.trace_eq_of_algEquiv φ]
  rfl

/-- **Proposition 1.3 (i), the tame equality for `k_0 = ℚ_p`** (pages 11 and 12): if `p` does
not divide the ramification index `e` of the prime `P` over `p`, then the exponent of `P` in the
different is `e - 1`, that is `𝔡 = (e - 1)/e`. The trace from `R ⧸ P` to `𝔽_p` is not zero
(`R ⧸ P` is a finite, hence separable, extension of `𝔽_p`), so by `intTrace_mk_eq_padic` some
trace from `R` to `ℤ_[p]` is a unit, and `P ^ e` does not divide the different. -/
theorem differentExponent_eq_of_not_dvd_ramificationIdx_padic
    (P : Ideal (integralClosure ℤ_[p] L)) [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (hp : ¬ p ∣ P.ramificationIdx ℤ_[p]) :
    letI := isDedekindDomain_ringOfIntegers_padic p L
    letI := isTorsionFree_ringOfIntegers_padic p L
    differentExponent ℤ_[p] (integralClosure ℤ_[p] L) P = P.ramificationIdx ℤ_[p] - 1 := by
  have := isDedekindDomain_ringOfIntegers_padic p L
  have := isTorsionFree_ringOfIntegers_padic p L
  have := moduleFinite_padicIntegers p L
  have he : 1 ≤ P.ramificationIdx ℤ_[p] :=
    ramificationIdx_pos_of_liesOver (IsDiscreteValuationRing.not_a_field ℤ_[p]) P
  let := Ideal.Quotient.field (IsLocalRing.maximalIdeal ℤ_[p])
  have : Finite (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) :=
    Finite.of_equiv _ PadicInt.residueField.symm.toEquiv
  have hP1 : (P ^ 1).IsMaximal := by
    rw [pow_one]
    exact IsPrime.isMaximal inferInstance
      (ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field ℤ_[p]) P)
  let := Ideal.Quotient.field (P ^ 1)
  let := Ideal.Quotient.algebraQuotientOfLEComap (le_comap_pow_padic p L P he)
  have : IsScalarTower ℤ_[p] (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p])
      (integralClosure ℤ_[p] L ⧸ P ^ 1) := .of_algebraMap_eq' rfl
  have : Module.Finite ℤ_[p] (integralClosure ℤ_[p] L ⧸ P ^ 1) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ_[p] _).toLinearMap
      Ideal.Quotient.mk_surjective
  have : FiniteDimensional (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) (integralClosure ℤ_[p] L ⧸ P ^
      1) :=
    Module.Finite.of_restrictScalars_finite ℤ_[p] _ _
  have : PerfectField (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) := PerfectField.ofFinite
  have : Algebra.IsAlgebraic (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) (integralClosure ℤ_[p] L ⧸ P
      ^ 1) :=
    Algebra.IsAlgebraic.of_finite _ _
  have : Algebra.IsSeparable (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) (integralClosure ℤ_[p] L ⧸ P
      ^ 1) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨t, ht⟩ : ∃ t : integralClosure ℤ_[p] L ⧸ P ^ 1,
      Algebra.trace (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) (integralClosure ℤ_[p] L ⧸ P ^ 1) t ≠
          0 := by
    simpa [LinearMap.ext_iff] using
      Algebra.trace_ne_zero (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) (integralClosure ℤ_[p] L ⧸ P ^
          1)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective t
  have hek : (P.ramificationIdx ℤ_[p] : ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) ≠ 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ℤ_[p])), Ne,
      Ideal.Quotient.eq_zero_iff_mem, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, not_lt]
    exact (PadicInt.norm_natCast_eq_one_iff.mpr
      (((Fact.out : p.Prime).coprime_iff_not_dvd).mpr hp)).ge
  have hy : P.ramificationIdx ℤ_[p] • Algebra.trace (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p])
      (integralClosure ℤ_[p] L ⧸ P ^ 1) (Ideal.Quotient.mk _ y) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal ℤ_[p])
        (Algebra.intTrace ℤ_[p] (integralClosure ℤ_[p] L) y) := intTrace_mk_eq_padic p L P he y
  have hx : Algebra.intTrace ℤ_[p] (integralClosure ℤ_[p] L) y ∉ IsLocalRing.maximalIdeal ℤ_[p] :=
      by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hy, nsmul_eq_mul]
    exact mul_ne_zero hek ht
  have hlt : differentExponent ℤ_[p] (integralClosure ℤ_[p] L) P < P.ramificationIdx ℤ_[p] :=
    differentExponent_lt_of_intTrace_notMem_padic p L P y hx
  have hge := ramificationIdx_sub_one_le_differentExponent ℤ_[p] ℚ_[p] L
    (integralClosure ℤ_[p] L) (IsDiscreteValuationRing.not_a_field ℤ_[p]) P
  omega

/-- **Proposition 1.3 (i) in the wildly ramified case, `k_0 = ℚ_p`**: if `p` divides the
ramification index `e` of the prime `P` over `p`, then `P ^ e` divides the different, so the
exponent of the different is at least `e` (that is, `𝔡 ≥ 1`). Every trace from `R` to `ℤ_[p]`
is then divisible by `p`, because the trace from `R ⧸ P ^ e` is `e` times a trace. -/
theorem ramificationIdx_le_differentExponent_of_dvd_padic
    (P : Ideal (integralClosure ℤ_[p] L)) [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (hp : p ∣ P.ramificationIdx ℤ_[p]) :
    letI := isDedekindDomain_ringOfIntegers_padic p L
    letI := isTorsionFree_ringOfIntegers_padic p L
    P.ramificationIdx ℤ_[p] ≤ differentExponent ℤ_[p] (integralClosure ℤ_[p] L) P := by
  have := isDedekindDomain_ringOfIntegers_padic p L
  have := isTorsionFree_ringOfIntegers_padic p L
  have := moduleFinite_padicIntegers p L
  have : IsFractionRing (integralClosure ℤ_[p] L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[p] ℚ_[p] L _
  have he : 1 ≤ P.ramificationIdx ℤ_[p] :=
    ramificationIdx_pos_of_liesOver (IsDiscreteValuationRing.not_a_field ℤ_[p]) P
  have hpm : IsLocalRing.maximalIdeal ℤ_[p] ≠ ⊥ := IsDiscreteValuationRing.not_a_field ℤ_[p]
  have hP0 : P ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hpm P
  let := Ideal.Quotient.algebraQuotientOfLEComap (le_comap_pow_padic p L P he)
  have hek : (P.ramificationIdx ℤ_[p] : ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) = 0 := by
    obtain ⟨c, hc⟩ := hp
    have h0 : ((p : ℕ) : ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ℤ_[p])),
          Ideal.Quotient.eq_zero_iff_mem,
        PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    rw [hc, Nat.cast_mul, h0, zero_mul]
  have hall : ∀ z : integralClosure ℤ_[p] L,
      Algebra.intTrace ℤ_[p] (integralClosure ℤ_[p] L) z ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    intro z
    have hz : P.ramificationIdx ℤ_[p] • Algebra.trace (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p])
        (integralClosure ℤ_[p] L ⧸ P ^ 1) (Ideal.Quotient.mk _ z) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal ℤ_[p])
          (Algebra.intTrace ℤ_[p] (integralClosure ℤ_[p] L) z) := intTrace_mk_eq_padic p L P he z
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hz, nsmul_eq_mul, hek, zero_mul]
  have hmap := map_maximalIdeal_eq_pow_padic p L P
  have hp' : (IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] (integralClosure ℤ_[p] L)) ≠ ⊥
      :=
    map_ne_bot_of_ne_bot hpm
  have hP : ((P ^ P.ramificationIdx ℤ_[p] : Ideal (integralClosure ℤ_[p] L)) :
      FractionalIdeal (integralClosure ℤ_[p] L)⁰ L)⁻¹ =
      ((⊤ : Ideal (integralClosure ℤ_[p] L)) : FractionalIdeal (integralClosure ℤ_[p] L)⁰ L) /
        ((IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] (integralClosure ℤ_[p] L)) :
          FractionalIdeal (integralClosure ℤ_[p] L)⁰ L) := by
    rw [← hmap, FractionalIdeal.coeIdeal_top, one_div]
  have hdvd : P ^ P.ramificationIdx ℤ_[p] ∣ differentIdeal ℤ_[p] (integralClosure ℤ_[p] L) := by
    rw [Ideal.dvd_iff_le, differentialIdeal_le_iff (K := ℚ_[p]) (L := L) (pow_ne_zero _ hP0), hP,
      Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.restrictScalars_mem, FractionalIdeal.mem_coeToSubmodule,
      FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp')] at hx
    rw [Submodule.mem_comap, LinearMap.coe_restrictScalars, ← FractionalIdeal.coeToSubmodule_one,
      ← div_self (G₀ := FractionalIdeal ℤ_[p]⁰ ℚ_[p]) (a := IsLocalRing.maximalIdeal ℤ_[p])
        (by simpa using hpm),
      FractionalIdeal.mem_coeToSubmodule,
      FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hpm)]
    simp only [FractionalIdeal.mem_coeIdeal, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hx
    intro y hy'
    obtain ⟨y, hy, rfl : algebraMap ℤ_[p] ℚ_[p] _ = _⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy'
    obtain ⟨z, -, hz'⟩ := hx _ (Ideal.mem_map_of_mem _ hy)
    have : Algebra.trace ℚ_[p] L (algebraMap (integralClosure ℤ_[p] L) L z) ∈
        (IsLocalRing.maximalIdeal ℤ_[p] : FractionalIdeal ℤ_[p]⁰ ℚ_[p]) := by
      rw [← Algebra.algebraMap_intTrace (A := ℤ_[p])]
      exact ⟨Algebra.intTrace ℤ_[p] (integralClosure ℤ_[p] L) z, hall z, rfl⟩
    rwa [mul_comm, ← smul_eq_mul, ← map_smul, Algebra.smul_def, mul_comm,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[p]
        (integralClosure ℤ_[p] L) L, ← hz']
  have hPr : Prime P := prime_of_isPrime hP0 inferInstance
  exact (FiniteMultiplicity.of_prime_left hPr (differentIdeal_ne_bot_of_isIntegralClosure ℤ_[p]
    ℚ_[p] L (integralClosure ℤ_[p] L))).le_multiplicity_of_pow_dvd hdvd

/-! ## Corollaries on `differentOrder` -/

/-- **Proposition 1.3 (i), equality case, in the normalized form `𝔡 = (e - 1)/e`** for
`k_0 = ℚ_p` (`𝔡_0 = 0`, `e_0 = 1`): if `p` does not divide the ramification index `e`, then
`differentOrder = (e - 1)/e`. -/
theorem differentOrder_eq_of_not_dvd_ramificationIdx_padic
    (P : Ideal (integralClosure ℤ_[p] L)) [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (hp : ¬ p ∣ P.ramificationIdx ℤ_[p]) :
    letI := isDedekindDomain_ringOfIntegers_padic p L
    letI := isTorsionFree_ringOfIntegers_padic p L
    differentOrder ℤ_[p] (integralClosure ℤ_[p] L) P =
      ((P.ramificationIdx ℤ_[p] : ℝ) - 1) / P.ramificationIdx ℤ_[p] := by
  have := isDedekindDomain_ringOfIntegers_padic p L
  have := isTorsionFree_ringOfIntegers_padic p L
  have he : 1 ≤ P.ramificationIdx ℤ_[p] :=
    ramificationIdx_pos_of_liesOver (IsDiscreteValuationRing.not_a_field ℤ_[p]) P
  rw [differentOrder, differentExponent_eq_of_not_dvd_ramificationIdx_padic p L P hp,
    Nat.cast_sub he, Nat.cast_one]

/-- **Proposition 1.3 (ii) in its base case `k_0 = ℚ_p`, `k_1 = k_i`** (page 12; `𝔡_0 = 0`,
`e_0 = 1`, `n_i = 0`): if `p` does not divide the ramification index, then `differentOrder ≤ 1`.
The arithmetic step is `Proposition1_3.ii_base`; its hypothesis is discharged by
`differentOrder_eq_of_not_dvd_ramificationIdx_padic`. -/
theorem differentOrder_le_one_of_not_dvd_ramificationIdx_padic
    (P : Ideal (integralClosure ℤ_[p] L)) [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (hp : ¬ p ∣ P.ramificationIdx ℤ_[p]) :
    letI := isDedekindDomain_ringOfIntegers_padic p L
    letI := isTorsionFree_ringOfIntegers_padic p L
    differentOrder ℤ_[p] (integralClosure ℤ_[p] L) P ≤ 1 := by
  have := isDedekindDomain_ringOfIntegers_padic p L
  have := isTorsionFree_ringOfIntegers_padic p L
  have he : 1 ≤ P.ramificationIdx ℤ_[p] :=
    ramificationIdx_pos_of_liesOver (IsDiscreteValuationRing.not_a_field ℤ_[p]) P
  have he' : (1 : ℝ) ≤ P.ramificationIdx ℤ_[p] := by exact_mod_cast he
  have h := IUT.PaperIV.Proposition1_3.ii_base
    (di := differentOrder ℤ_[p] (integralClosure ℤ_[p] L) P) (d0 := 0) he' le_rfl
    (by rw [differentOrder_eq_of_not_dvd_ramificationIdx_padic p L P hp, mul_one, zero_add])
  simpa using h

/-- **Proposition 1.3 (i), wild case, in the normalized form `𝔡 ≥ 1`** for `k_0 = ℚ_p`: if `p`
divides the ramification index, then `differentOrder ≥ 1`, strictly above `(e - 1)/e`. -/
theorem one_le_differentOrder_of_dvd_ramificationIdx_padic
    (P : Ideal (integralClosure ℤ_[p] L)) [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (hp : p ∣ P.ramificationIdx ℤ_[p]) :
    letI := isDedekindDomain_ringOfIntegers_padic p L
    letI := isTorsionFree_ringOfIntegers_padic p L
    1 ≤ differentOrder ℤ_[p] (integralClosure ℤ_[p] L) P := by
  have := isDedekindDomain_ringOfIntegers_padic p L
  have := isTorsionFree_ringOfIntegers_padic p L
  have he : 1 ≤ P.ramificationIdx ℤ_[p] :=
    ramificationIdx_pos_of_liesOver (IsDiscreteValuationRing.not_a_field ℤ_[p]) P
  have he' : (0 : ℝ) < P.ramificationIdx ℤ_[p] := by exact_mod_cast he
  have hle := ramificationIdx_le_differentExponent_of_dvd_padic p L P hp
  rw [differentOrder, le_div_iff₀ he', one_mul]
  exact_mod_cast hle

/-- **The equality case of Proposition 1.3 (i) is exactly the tame case**, for `k_0 = ℚ_p`: the
exponent of the different is `e - 1` if and only if `p` does not divide `e`. -/
theorem differentExponent_eq_ramificationIdx_sub_one_iff_padic
    (P : Ideal (integralClosure ℤ_[p] L)) [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
        :
    letI := isDedekindDomain_ringOfIntegers_padic p L
    letI := isTorsionFree_ringOfIntegers_padic p L
    differentExponent ℤ_[p] (integralClosure ℤ_[p] L) P = P.ramificationIdx ℤ_[p] - 1 ↔
      ¬ p ∣ P.ramificationIdx ℤ_[p] := by
  have := isDedekindDomain_ringOfIntegers_padic p L
  have := isTorsionFree_ringOfIntegers_padic p L
  have he : 1 ≤ P.ramificationIdx ℤ_[p] :=
    ramificationIdx_pos_of_liesOver (IsDiscreteValuationRing.not_a_field ℤ_[p]) P
  refine ⟨fun h hp => ?_, differentExponent_eq_of_not_dvd_ramificationIdx_padic p L P⟩
  have := ramificationIdx_le_differentExponent_of_dvd_padic p L P hp
  omega

end IUT.PaperIV.LocalFields
