import IUT.PaperIV.LocalFields.Tame

/-!
# IUT IV, Proposition 1.3 over a general base field `k_0`

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Proposition 1.3 and its proof,
pages 11 and 12 of the April 2020 manuscript, with the notation of Proposition 1.1 (page 9).
Pages read for this file: 9, 11, 12 and 13. Pages checked against rendered images: 9, 11, 12
and 13 (the normalization `ord(p) = 1` and the definition of the order `𝔡_i` of the different on
page 9; the notation `R_0`, `𝔡_0`, `e_0`, `e_{i/0} = e_i/e_0`, `[k_i : k_0]`, `n_i` and the
inequality of (i) on page 11; the tame equality of (i), assertion (ii) and the proof on page 12;
Remark 1.3.1 on page 13).

## The statement of the paper

Page 11: for a subfield `ℚ_p ⊆ k_0 ⊆ k_i`, `R_0` is the ring of integers of `k_0`, `𝔡_0` the
order (`ord`, with `ord(p) = 1`) of a generator of the different of `R_0` over `ℤ_p`, `e_0` the
ramification index of `k_0` over `ℚ_p`, `e_{i/0} = e_i/e_0`, and `n_i` the nonnegative integer
with `[k_i : k_0]/p^{n_i}` an integer prime to `p`. Then
(i) `𝔡_i ≥ 𝔡_0 + (e_{i/0} - 1)/(e_{i/0}·e_0) = 𝔡_0 + (e_{i/0} - 1)/e_i`, with equality if `k_i`
is tamely ramified over `k_0` (page 12); (ii) if `k_i` is a finite Galois extension of a subfield
`k_1` with `k_0 ⊆ k_1` and `k_1` tamely ramified over `k_0`, then `𝔡_i ≤ 𝔡_0 + n_i + 1/e_0`.

## The objects

`K = k_0` and `L = k_i` are fields with finite-dimensional `ℚ_[p]`-algebra structures, an algebra
map `K → L` compatible with them, and compatible `ℤ_[p]`-algebra structures.
`R_K = integralClosure ℤ_[p] K` and `R_L = integralClosure ℤ_[p] L` are the rings of integers;
`towerAlgebra` is the inclusion `R_K → R_L` (a definition of the algebra map, used with `letI`).
`P₀` and `P` are primes of `R_K` and `R_L` over `pℤ_p` (each is the maximal ideal, by
`padicBridge_prime_eq_maximalIdeal`; `tower_liesOver` shows that `P` lies over `P₀`).
`e_K = e_0` and `e_L = e_i` are the ramification indices of `P₀` and `P` over `pℤ_p`, and
`e_{L/K} = e_{i/0}` is that of `P` over `P₀`; `towerRamificationIdx_eq_mul` proves
`e_L = e_K·e_{L/K}`, so the paper's `e_i/e_0` is this relative index. `𝔡_K = differentOrder ℤ_[p]
R_K P₀` and `𝔡_L = differentOrder ℤ_[p] R_L P` (exponent of the different divided by the
ramification index; the normalization `ord(p) = 1` of page 9). The residue fields are finite, so
`L` is tamely ramified over `K` exactly when `p` does not divide `e_{L/K}`; this is the reading of
"tamely ramified" used below. `n_i = multiplicity p [L : K]`.

## What is proved

General local results (a Dedekind domain `A`, the integral closure `B` of `A` in a finite
separable extension of `Frac(A)`, `B` local, `p ⊆ A` maximal and nonzero, `P` the prime of `B`):
`tower_map_eq_pow` (`pB = P^e`), `tower_trace_quotient_pow`, `tower_intTrace_mk_eq` (the trace
to `A ⧸ p` is `e` times the residue trace), and `tower_differentExponent_eq_of_ne_zero`, the tame
equality `v_P(𝔇_{B/A}) = e - 1` when `A ⧸ p` is finite and `e ≠ 0` in `A ⧸ p`. These adapt the
argument of `IUT.PaperIV.LocalFields.Tame` from the base `ℤ_[p]` to a general base.

For `ℚ_p ⊆ K ⊆ L`:

1. Transitivity: `towerRamificationIdx_eq_mul` (`e_L = e_K·e_{L/K}`), `towerDifferentExponent_eq`
   (`v_P(𝔇_{L/ℚ_p}) = v_P(𝔇_{L/K}) + e_{L/K}·v_{P₀}(𝔇_{K/ℚ_p})`), and `towerDifferentOrder_eq`,
   `𝔡_L = 𝔡_K + 𝔡_{L/K}/e_K`, where `𝔡_{L/K} = differentOrder R_K R_L P` is the order of the
   relative different normalized by `ord(π_K) = 1`.
2. Proposition 1.3 (i): `towerProp1_3i_ge`, `𝔡_L ≥ 𝔡_K + (e_{L/K} - 1)/e_L`; the relative tame
   equality `towerDifferentExponent_rel_eq_of_tame`; and `towerProp1_3i_eq_of_tame`,
   `𝔡_L = 𝔡_K + (e_{L/K} - 1)/e_L` when `p ∤ e_{L/K}`.
3. Proposition 1.3 (ii), special cases: `towerProp1_3ii_of_tame` (`L/K` tame; this is the case
   `k_1 = k_i`, where the Galois hypothesis holds trivially), `towerProp1_3ii_of_not_dvd_finrank`
   (`n_i = 0`, the base case of the paper's induction, without the Galois hypothesis; it uses
   `towerRamificationIdx_dvd_finrank`, `e_{L/K} ∣ [L : K]`), and the conditional
   `towerProp1_3ii_of_exponent_bound`: (ii) for every finite `L/K`, with no Galois hypothesis,
   from the hypothesis `v_P(𝔇_{L/K}) ≤ e_{L/K} - 1 + e_L·v_p(e_{L/K})`. That hypothesis is the
   classical upper bound for the different of an extension of local fields; it is not in Mathlib
   at the pinned version and it is not proved here.

`towerProp1_3iiStatement` states assertion (ii) with the hypotheses of page 12 (an intermediate
field `K₁` with `L/K₁` Galois and `K₁/K` tame). It is a definition, not a theorem.

## Not proved

* Proposition 1.3 (ii) in the wild case: `L/K₁` Galois with `p ∣ e_{L/K₁}`. The paper's proof
  (page 12) reduces to totally ramified extensions, then inducts on `n_i` through a Galois
  `p`-subextension of degree `p`, enlarges `k_1` to contain a primitive `p`-th root of unity with
  `e_1 ≥ p/ε`, and computes the different of a Kummer extension `x^p - ϖ_*`. None of this
  (maximal unramified subextensions, Galois `p`-subextensions, Kummer generators) is formalized
  here. Equivalently, the missing piece is the bound assumed in
  `towerProp1_3ii_of_exponent_bound`.
* The converse of the tame equality over a general base (that equality in (i) forces tameness)
  is not formalized here; for `k_0 = ℚ_p` it is
  `differentExponent_eq_ramificationIdx_sub_one_iff_padic`.
-/

open Ideal nonZeroDivisors

namespace IUT.PaperIV.LocalFields

/-! ## The tame equality for a local extension of Dedekind domains -/

section TowerLocal

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [IsDedekindDomain A]
  [IsDedekindDomain B] [Module.IsTorsionFree A B] [IsLocalRing B]

/-- For a local Dedekind domain `B` over `A` and the prime `P` of `B` over the nonzero maximal
ideal `p` of `A`: `pB = P ^ e`, `e` the ramification index. -/
theorem tower_map_eq_pow {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    p.map (algebraMap A B) = P ^ P.ramificationIdx A := by
  have hp' : p.map (algebraMap A B) ≠ ⊥ := map_ne_bot_of_ne_bot hp
  have hP0 : P ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp P
  have : P.IsMaximal := IsPrime.isMaximal inferInstance hP0
  have hPm : P = IsLocalRing.maximalIdeal B := IsLocalRing.eq_maximalIdeal this
  obtain ⟨Q, h1, h2⟩ := Ideal.eq_prime_pow_mul_coprime hp' P
  rw [← IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count _ _ hp'] at h2
  have hQ : Q = ⊤ := by
    by_contra hQ
    have : Q ≤ P := hPm ▸ IsLocalRing.le_maximalIdeal hQ
    rw [sup_eq_left.mpr this] at h1
    exact IsPrime.ne_top inferInstance h1
  rw [h2, hQ, mul_top]

/-- `p` maps into `P ^ n` for `n ≤ e`. -/
theorem tower_le_comap_pow {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal B) [P.IsPrime] [P.LiesOver p] {n : ℕ} (hn : n ≤ P.ramificationIdx A) :
    p ≤ (P ^ n).comap (algebraMap A B) := by
  rw [← Ideal.map_le_iff_le_comap, tower_map_eq_pow A B hp P]
  exact Ideal.pow_le_pow_right hn

/-- The prime `P` of the local Dedekind domain `B` over the nonzero `p` is principal. -/
theorem tower_exists_span_eq {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal B) [P.IsPrime] [P.LiesOver p] : ∃ π : B, π ≠ 0 ∧ P = Ideal.span {π} := by
  have hP0 : P ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp P
  have hPm : P = IsLocalRing.maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal (IsPrime.isMaximal inferInstance hP0)
  have hnf : ¬ IsField B := fun hF =>
    hP0 (hPm.trans ((IsLocalRing.isField_iff_maximalIdeal_eq).mp hF))
  have : IsDiscreteValuationRing B :=
    ((IsDiscreteValuationRing.TFAE B hnf).out 1 3).mpr (show IsDedekindDomain B from inferInstance)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  exact ⟨π, hπ.ne_zero, hPm.trans hπ.maximalIdeal_eq⟩

end TowerLocal

section TowerGeneral

variable (A K L B : Type*) [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L] [IsFractionRing A K]
  [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L] [IsLocalRing B]

include K L

/-- **The trace of `B ⧸ P ^ n` over `A ⧸ p`** (`1 ≤ n ≤ e`, `B` local): the trace of the class
of `y` is `n` times the trace of its class in `B ⧸ P`. This is the argument of
`trace_quotient_pow_padic` over a general base. -/
theorem tower_trace_quotient_pow {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal B) [P.IsPrime] [P.LiesOver p] (he : 1 ≤ P.ramificationIdx A) (y : B)
    (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ P.ramificationIdx A) :
    letI := Ideal.Quotient.algebraQuotientOfLEComap (tower_le_comap_pow A B hp P hn)
    letI := Ideal.Quotient.algebraQuotientOfLEComap (tower_le_comap_pow A B hp P he)
    Algebra.trace (A ⧸ p) (B ⧸ P ^ n) (Ideal.Quotient.mk _ y) =
      n • Algebra.trace (A ⧸ p) (B ⧸ P ^ 1) (Ideal.Quotient.mk _ y) := by
  obtain ⟨π, hπ0, hP⟩ := tower_exists_span_eq A B hp P
  have hpow : ∀ m, P ^ m = Ideal.span {π ^ m} := fun m => by rw [hP, Ideal.span_singleton_pow]
  have : Module.Finite A B := IsIntegralClosure.finite A K L B
  induction n, hn1 using Nat.le_induction with
  | base =>
    rw [one_smul]
  | succ n hn1 ih =>
    have hn' : n ≤ P.ramificationIdx A := by omega
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
    have hfin : letI := Ideal.Quotient.algebraQuotientOfLEComap (tower_le_comap_pow A B hp P hn)
        Module.Finite (A ⧸ p) (B ⧸ P ^ (n + 1)) := by
      let := Ideal.Quotient.algebraQuotientOfLEComap (tower_le_comap_pow A B hp P hn)
      have : IsScalarTower A (A ⧸ p) (B ⧸ P ^ (n + 1)) := .of_algebraMap_eq' rfl
      have : Module.Finite A (B ⧸ P ^ (n + 1)) :=
        Module.Finite.of_surjective (Ideal.Quotient.mkₐ A _).toLinearMap
          Ideal.Quotient.mk_surjective
      exact Module.Finite.of_restrictScalars_finite A _ _
    have key := trace_quotient_eq_add_of_mul_exact (tower_le_comap_pow A B hp P hn)
      (tower_le_comap_pow A B hp P hn') (tower_le_comap_pow A B hp P he) (π ^ n)
      (Ideal.pow_le_pow_right (I := P) (Nat.le_succ n)) hKI hJI hfin y
    rw [key, ih hn', succ_nsmul, add_comm]

/-- **The trace from `B` to `A`, modulo `p`** (`B` local): the class of the trace of `z` in
`A ⧸ p` is `e` times the trace of the class of `z` in `B ⧸ P`. -/
theorem tower_intTrace_mk_eq {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal B) [P.IsPrime] [P.LiesOver p] (he : 1 ≤ P.ramificationIdx A) (z : B) :
    haveI := IsIntegralClosure.finite A K L B
    letI := Ideal.Quotient.algebraQuotientOfLEComap (tower_le_comap_pow A B hp P he)
    P.ramificationIdx A • Algebra.trace (A ⧸ p) (B ⧸ P ^ 1) (Ideal.Quotient.mk _ z) =
      Ideal.Quotient.mk p (Algebra.intTrace A B z) := by
  have := IsIntegralClosure.finite A K L B
  let := Ideal.Quotient.algebraQuotientOfLEComap (tower_le_comap_pow A B hp P he)
  let := Ideal.Quotient.algebraQuotientOfLEComap (tower_le_comap_pow A B hp P (le_refl _))
  have htr : Algebra.trace (A ⧸ p) (B ⧸ P ^ P.ramificationIdx A) (Ideal.Quotient.mk _ z) =
      P.ramificationIdx A • Algebra.trace (A ⧸ p) (B ⧸ P ^ 1) (Ideal.Quotient.mk _ z) :=
    tower_trace_quotient_pow A K L B hp P he z _ he le_rfl
  have hmap := tower_map_eq_pow A B hp P
  let φ : (B ⧸ p.map (algebraMap A B)) ≃ₐ[A ⧸ p] (B ⧸ P ^ P.ramificationIdx A) :=
    { Ideal.quotEquivOfEq hmap with commutes' := Quotient.ind fun _ => rfl }
  rw [← htr, ← Algebra.trace_quotient_eq_of_isDedekindDomain, ← Algebra.trace_eq_of_algEquiv φ]
  rfl

/-- If some element of the local ring `B` has trace (to `A`) outside `p`, then
`differentExponent A B P < e`. -/
theorem tower_differentExponent_lt_of_intTrace_notMem {p : Ideal A}
    [p.IsMaximal] (hp : p ≠ ⊥) (P : Ideal B) [P.IsPrime] [P.LiesOver p] (x : B)
    (hx : haveI := IsIntegralClosure.finite A K L B
      Algebra.intTrace A B x ∉ p) :
    differentExponent A B P < P.ramificationIdx A := by
  have := IsIntegralClosure.finite A K L B
  have : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let := FractionRing.liftAlgebra A (FractionRing B)
  have : IsScalarTower A (FractionRing A) (FractionRing B) :=
    FractionRing.isScalarTower_liftAlgebra _ _
  have H : RingHom.comp (algebraMap (FractionRing A) (FractionRing B))
      ↑(FractionRing.algEquiv A K).symm.toRingEquiv =
        RingHom.comp ↑(FractionRing.algEquiv B L).symm.toRingEquiv (algebraMap K L) := by
    apply IsLocalization.ringHom_ext A⁰
    ext
    simp only [RingHom.coe_comp, RingHom.coe_coe,
      AlgEquiv.coe_toRingEquiv, Function.comp_apply, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply A B L, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  have : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    Algebra.IsSeparable.of_equiv_equiv _ _ H
  have hmap := tower_map_eq_pow A B hp P
  have hnd := not_dvd_differentIdeal_of_intTrace_notMem A (P ^ P.ramificationIdx A) ⊤
    (by rw [mul_top]; exact hmap.symm) x Submodule.mem_top hx
  exact lt_of_not_ge fun hle => hnd ((pow_dvd_pow P hle).trans (pow_multiplicity_dvd P _))

/-- **The tame equality over a general base** (`B` local, `A ⧸ p` finite): if the ramification
index `e` of `P` over `p` is nonzero in `A ⧸ p` (that is, the residue characteristic does not
divide `e`), then `differentExponent A B P = e - 1`. -/
theorem tower_differentExponent_eq_of_ne_zero {p : Ideal A} [p.IsMaximal]
    [Finite (A ⧸ p)] (hp : p ≠ ⊥) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (hpe : ((P.ramificationIdx A : ℕ) : A ⧸ p) ≠ 0) :
    differentExponent A B P = P.ramificationIdx A - 1 := by
  have := IsIntegralClosure.finite A K L B
  have he : 1 ≤ P.ramificationIdx A := ramificationIdx_pos_of_liesOver hp P
  let := Ideal.Quotient.field p
  have hP0 : P ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp P
  have hP1 : (P ^ 1).IsMaximal := by
    rw [pow_one]
    exact IsPrime.isMaximal inferInstance hP0
  let := Ideal.Quotient.field (P ^ 1)
  let := Ideal.Quotient.algebraQuotientOfLEComap (tower_le_comap_pow A B hp P he)
  have : IsScalarTower A (A ⧸ p) (B ⧸ P ^ 1) := .of_algebraMap_eq' rfl
  have : Module.Finite A (B ⧸ P ^ 1) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A _).toLinearMap
      Ideal.Quotient.mk_surjective
  have : FiniteDimensional (A ⧸ p) (B ⧸ P ^ 1) :=
    Module.Finite.of_restrictScalars_finite A _ _
  have : PerfectField (A ⧸ p) := PerfectField.ofFinite
  have : Algebra.IsAlgebraic (A ⧸ p) (B ⧸ P ^ 1) := Algebra.IsAlgebraic.of_finite _ _
  have : Algebra.IsSeparable (A ⧸ p) (B ⧸ P ^ 1) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨t, ht⟩ : ∃ t : B ⧸ P ^ 1, Algebra.trace (A ⧸ p) (B ⧸ P ^ 1) t ≠ 0 := by
    simpa [LinearMap.ext_iff] using Algebra.trace_ne_zero (A ⧸ p) (B ⧸ P ^ 1)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective t
  have hy := tower_intTrace_mk_eq A K L B hp P he y
  have hx : Algebra.intTrace A B y ∉ p := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hy, nsmul_eq_mul]
    exact mul_ne_zero hpe ht
  have hlt := tower_differentExponent_lt_of_intTrace_notMem A K L B hp P y hx
  have hge := ramificationIdx_sub_one_le_differentExponent A K L B hp P
  omega

end TowerGeneral

/-! ## Two finite extensions `K ⊆ L` of `ℚ_[p]` and their rings of integers -/

section PadicTower

variable (p : ℕ) [Fact p.Prime] (K L : Type*) [Field K] [Field L]
  [Algebra ℚ_[p] K] [Algebra ℚ_[p] L] [Algebra K L] [IsScalarTower ℚ_[p] K L]
  [Algebra ℤ_[p] K] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] K]
  [IsScalarTower ℤ_[p] ℚ_[p] L]

/-- The `ℤ_[p]`-algebra structures on `K` and `L` are compatible with `K → L`. -/
theorem tower_isScalarTower_padicInt : IsScalarTower ℤ_[p] K L :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] L, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] K,
      ← IsScalarTower.algebraMap_apply ℚ_[p] K L]

/-- The image in `L` of an integer of `K` is an integer of `L`. -/
theorem tower_algebraMap_mem (x : integralClosure ℤ_[p] K) :
    algebraMap K L x ∈ integralClosure ℤ_[p] L := by
  have := tower_isScalarTower_padicInt p K L
  exact x.2.algebraMap

/-- The inclusion `R_K → R_L` of the rings of integers, as an algebra structure. -/
noncomputable abbrev towerAlgebra : Algebra (integralClosure ℤ_[p] K) (integralClosure ℤ_[p] L) :=
  (((algebraMap K L).comp (algebraMap (integralClosure ℤ_[p] K) K)).codRestrict
    (integralClosure ℤ_[p] L) (tower_algebraMap_mem p K L)).toAlgebra

/-- `R_L` is torsion free over `R_K`. -/
theorem tower_isTorsionFree :
    letI := towerAlgebra p K L
    Module.IsTorsionFree (integralClosure ℤ_[p] K) (integralClosure ℤ_[p] L) := by
  let := towerAlgebra p K L
  refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
  rw [Algebra.smul_def] at h
  rcases mul_eq_zero.mp h with hr | hm
  · left
    have h1 : algebraMap K L (r : K) = 0 := congrArg Subtype.val hr
    exact Subtype.ext ((map_eq_zero _).mp h1)
  · right
    exact hm

/-- `R_K ⊆ R_L ⊆ L` is a scalar tower. -/
theorem tower_isScalarTower_int_int :
    letI := towerAlgebra p K L
    IsScalarTower (integralClosure ℤ_[p] K) (integralClosure ℤ_[p] L) L := by
  let := towerAlgebra p K L
  refine ⟨fun x y z => ?_⟩
  rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]
  rfl

/-- `ℤ_[p] ⊆ R_K ⊆ R_L` is a scalar tower. -/
theorem tower_isScalarTower_padicInt_int :
    letI := towerAlgebra p K L
    IsScalarTower ℤ_[p] (integralClosure ℤ_[p] K) (integralClosure ℤ_[p] L) := by
  let := towerAlgebra p K L
  have := tower_isScalarTower_padicInt p K L
  refine IsScalarTower.of_algebraMap_eq fun x => Subtype.ext ?_
  exact IsScalarTower.algebraMap_apply ℤ_[p] K L x

/-- `R_L` is the integral closure of `R_K` in `L`. -/
theorem tower_isIntegralClosure :
    IsIntegralClosure (integralClosure ℤ_[p] L) (integralClosure ℤ_[p] K) L := by
  have := tower_isScalarTower_padicInt p K L
  exact IsIntegralClosure.tower_top (R := ℤ_[p])

omit [Algebra ℤ_[p] K] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] K]
  [IsScalarTower ℤ_[p] ℚ_[p] L] in
/-- `L/K` is separable (characteristic zero). -/
theorem tower_isSeparable [FiniteDimensional ℚ_[p] L] : Algebra.IsSeparable K L := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  have : FiniteDimensional K L := Module.Finite.right ℚ_[p] K L
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

end PadicTower

/-! ## The primes, the residue field and the context of the tower -/

section PadicTowerMain

variable (p : ℕ) [Fact p.Prime] (K L : Type*) [Field K] [Field L]
  [Algebra ℚ_[p] K] [Algebra ℚ_[p] L] [Algebra K L] [IsScalarTower ℚ_[p] K L]
  [Algebra ℤ_[p] K] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] K]
  [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] L]

omit [FiniteDimensional ℚ_[p] L] in
/-- The prime `P` of `R_L` over `p` lies over the prime `P₀` of `R_K` over `p` (both are the
maximal ideals, by `padicBridge_prime_eq_maximalIdeal`). -/
theorem tower_liesOver (P₀ : Ideal (integralClosure ℤ_[p] K)) [P₀.IsPrime]
    [P₀.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] (P : Ideal (integralClosure ℤ_[p] L))
    [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    letI := towerAlgebra p K L
    P.LiesOver P₀ := by
  let := towerAlgebra p K L
  have := tower_isScalarTower_padicInt_int p K L
  have : (P.under (integralClosure ℤ_[p] K)).LiesOver (IsLocalRing.maximalIdeal ℤ_[p]) :=
    ⟨by rw [Ideal.under_under, ← Ideal.over_def P (IsLocalRing.maximalIdeal ℤ_[p])]⟩
  have h2 := padicBridge_prime_eq_maximalIdeal p K (P.under (integralClosure ℤ_[p] K))
  have h3 := padicBridge_prime_eq_maximalIdeal p K P₀
  exact ⟨h3.trans h2.symm⟩

/-- The residue field `R_K ⧸ P₀` is finite. -/
theorem tower_finite_quotient (P₀ : Ideal (integralClosure ℤ_[p] K)) [P₀.IsPrime]
    [P₀.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] : Finite (integralClosure ℤ_[p] K ⧸ P₀) := by
  have hle : IsLocalRing.maximalIdeal ℤ_[p] ≤ P₀.comap (algebraMap ℤ_[p] _) :=
    (P₀.over_def (IsLocalRing.maximalIdeal ℤ_[p])).le
  let := Ideal.Quotient.algebraQuotientOfLEComap hle
  have : IsScalarTower ℤ_[p] (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p])
      (integralClosure ℤ_[p] K ⧸ P₀) := .of_algebraMap_eq' rfl
  have := moduleFinite_padicIntegers p K
  have : Module.Finite ℤ_[p] (integralClosure ℤ_[p] K ⧸ P₀) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ_[p] P₀).toLinearMap
      Ideal.Quotient.mk_surjective
  have : Module.Finite (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p])
      (integralClosure ℤ_[p] K ⧸ P₀) := Module.Finite.of_restrictScalars_finite ℤ_[p] _ _
  have : Finite (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) :=
    Finite.of_equiv _ PadicInt.residueField.symm.toEquiv
  exact Module.finite_of_finite (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p])

omit [Algebra ℚ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
  [FiniteDimensional ℚ_[p] L] in
/-- A natural number prime to `p` is nonzero in the residue field `R_K ⧸ P₀`. -/
theorem tower_natCast_ne_zero (P₀ : Ideal (integralClosure ℤ_[p] K)) [P₀.IsPrime] {n : ℕ}
    (hn : ¬ p ∣ n) : ((n : ℕ) : integralClosure ℤ_[p] K ⧸ P₀) ≠ 0 := by
  have hu : IsUnit ((n : ℕ) : ℤ_[p]) := PadicInt.isUnit_iff.mpr
    (PadicInt.norm_natCast_eq_one_iff.mpr (((Fact.out : p.Prime).coprime_iff_not_dvd).mpr hn))
  have hu' := hu.map (algebraMap ℤ_[p] (integralClosure ℤ_[p] K ⧸ P₀))
  rw [map_natCast] at hu'
  exact hu'.ne_zero

/-! ## 1. Transitivity in the local tower -/

/-- **The ramification indices multiply**: `e_{L/ℚ_p} = e_{K/ℚ_p}·e_{L/K}` for the primes
`P₀ ⊆ R_K` and `P ⊆ R_L` over `p`. -/
theorem towerRamificationIdx_eq_mul (P₀ : Ideal (integralClosure ℤ_[p] K)) [P₀.IsPrime]
    [P₀.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] (P : Ideal (integralClosure ℤ_[p] L))
    [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    letI := towerAlgebra p K L
    P.ramificationIdx ℤ_[p] =
      P₀.ramificationIdx ℤ_[p] * P.ramificationIdx (integralClosure ℤ_[p] K) := by
  have := isDedekindDomain_ringOfIntegers_padic p K
  have := isDedekindDomain_ringOfIntegers_padic p L
  have := isTorsionFree_ringOfIntegers_padic p K
  have := isTorsionFree_ringOfIntegers_padic p L
  let := towerAlgebra p K L
  have := tower_isTorsionFree p K L
  have := tower_isScalarTower_padicInt_int p K L
  have := tower_liesOver p K L P₀ P
  exact ramificationIdx_tower P₀ P

/-- **Transitivity of the exponent of the different**: with `𝔇_{L/ℚ_p}`, `𝔇_{L/K}`,
`𝔇_{K/ℚ_p}` the differents of `R_L` over `ℤ_[p]`, of `R_L` over `R_K` and of `R_K` over `ℤ_[p]`,
`v_P(𝔇_{L/ℚ_p}) = v_P(𝔇_{L/K}) + e_{L/K}·v_{P₀}(𝔇_{K/ℚ_p})`. -/
theorem towerDifferentExponent_eq (P₀ : Ideal (integralClosure ℤ_[p] K)) [P₀.IsPrime]
    [P₀.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] (P : Ideal (integralClosure ℤ_[p] L))
    [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    letI := isDedekindDomain_ringOfIntegers_padic p K
    letI := isDedekindDomain_ringOfIntegers_padic p L
    letI := isTorsionFree_ringOfIntegers_padic p K
    letI := isTorsionFree_ringOfIntegers_padic p L
    letI := towerAlgebra p K L
    letI := tower_isTorsionFree p K L
    differentExponent ℤ_[p] (integralClosure ℤ_[p] L) P =
      differentExponent (integralClosure ℤ_[p] K) (integralClosure ℤ_[p] L) P +
        P.ramificationIdx (integralClosure ℤ_[p] K) *
          differentExponent ℤ_[p] (integralClosure ℤ_[p] K) P₀ := by
  have := isDedekindDomain_ringOfIntegers_padic p K
  have := isDedekindDomain_ringOfIntegers_padic p L
  have := isTorsionFree_ringOfIntegers_padic p K
  have := isTorsionFree_ringOfIntegers_padic p L
  let := towerAlgebra p K L
  have := tower_isTorsionFree p K L
  have := tower_isScalarTower_int_int p K L
  have := tower_isScalarTower_padicInt_int p K L
  have := tower_isIntegralClosure p K L
  have := tower_isSeparable p K L
  have : FiniteDimensional K L := Module.Finite.right ℚ_[p] K L
  have := tower_liesOver p K L P₀ P
  exact differentExponent_tower ℤ_[p] ℚ_[p] _ K _ L (IsDiscreteValuationRing.not_a_field ℤ_[p])
    P₀ P

/-- **Transitivity in the normalization `ord(p) = 1` of page 9**: `𝔡_L = 𝔡_K + 𝔡_{L/K}/e_K`,
with `𝔡_L = differentOrder ℤ_[p] R_L P`, `𝔡_K = differentOrder ℤ_[p] R_K P₀`, `e_K` the
ramification index of `P₀` over `p`, and `𝔡_{L/K} = differentOrder R_K R_L P` the order of the
relative different normalized by `ord(π_K) = 1` for a uniformizer `π_K` of `R_K` (so that it
contributes `𝔡_{L/K}/e_K` in the normalization `ord(p) = 1`). -/
theorem towerDifferentOrder_eq (P₀ : Ideal (integralClosure ℤ_[p] K)) [P₀.IsPrime]
    [P₀.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] (P : Ideal (integralClosure ℤ_[p] L))
    [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    letI := isDedekindDomain_ringOfIntegers_padic p K
    letI := isDedekindDomain_ringOfIntegers_padic p L
    letI := isTorsionFree_ringOfIntegers_padic p K
    letI := isTorsionFree_ringOfIntegers_padic p L
    letI := towerAlgebra p K L
    letI := tower_isTorsionFree p K L
    differentOrder ℤ_[p] (integralClosure ℤ_[p] L) P =
      differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P₀ +
        differentOrder (integralClosure ℤ_[p] K) (integralClosure ℤ_[p] L) P /
          P₀.ramificationIdx ℤ_[p] := by
  have := isDedekindDomain_ringOfIntegers_padic p K
  have := isDedekindDomain_ringOfIntegers_padic p L
  have := isTorsionFree_ringOfIntegers_padic p K
  have := isTorsionFree_ringOfIntegers_padic p L
  let := towerAlgebra p K L
  have := tower_isTorsionFree p K L
  have := tower_liesOver p K L P₀ P
  have hexp := towerDifferentExponent_eq p K L P₀ P
  have htow := towerRamificationIdx_eq_mul p K L P₀ P
  have hpm : IsLocalRing.maximalIdeal ℤ_[p] ≠ ⊥ := IsDiscreteValuationRing.not_a_field ℤ_[p]
  have he₀ : 0 < P₀.ramificationIdx ℤ_[p] := ramificationIdx_pos_of_liesOver hpm P₀
  have he' : 0 < P.ramificationIdx (integralClosure ℤ_[p] K) :=
    ramificationIdx_pos_of_liesOver (ne_bot_of_liesOver_of_ne_bot hpm P₀) P
  unfold differentOrder
  rw [hexp, htow]
  have h0 : (0 : ℝ) < P₀.ramificationIdx ℤ_[p] := by exact_mod_cast he₀
  have h1 : (0 : ℝ) < P.ramificationIdx (integralClosure ℤ_[p] K) := by exact_mod_cast he'
  push_cast
  field_simp
  ring

/-! ## 2. Proposition 1.3 (i) over a general base `k_0 = K` -/

/-- **Proposition 1.3 (i), the inequality** (pages 11 and 12) for finite extensions
`ℚ_p ⊆ K ⊆ L`: `𝔡_L ≥ 𝔡_K + (e_{L/K} - 1)/e_L`. -/
theorem towerProp1_3i_ge (P₀ : Ideal (integralClosure ℤ_[p] K)) [P₀.IsPrime]
    [P₀.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] (P : Ideal (integralClosure ℤ_[p] L))
    [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    letI := isDedekindDomain_ringOfIntegers_padic p K
    letI := isDedekindDomain_ringOfIntegers_padic p L
    letI := isTorsionFree_ringOfIntegers_padic p K
    letI := isTorsionFree_ringOfIntegers_padic p L
    letI := towerAlgebra p K L
    differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P₀ +
        ((P.ramificationIdx (integralClosure ℤ_[p] K) : ℝ) - 1) / P.ramificationIdx ℤ_[p] ≤
      differentOrder ℤ_[p] (integralClosure ℤ_[p] L) P := by
  have := isDedekindDomain_ringOfIntegers_padic p K
  have := isDedekindDomain_ringOfIntegers_padic p L
  have := isTorsionFree_ringOfIntegers_padic p K
  have := isTorsionFree_ringOfIntegers_padic p L
  let := towerAlgebra p K L
  have := tower_isTorsionFree p K L
  have := tower_isScalarTower_int_int p K L
  have := tower_isScalarTower_padicInt_int p K L
  have := tower_isIntegralClosure p K L
  have := tower_isSeparable p K L
  have : FiniteDimensional K L := Module.Finite.right ℚ_[p] K L
  have := tower_liesOver p K L P₀ P
  exact differentOrder_ge_tower ℤ_[p] ℚ_[p] _ K _ L (IsDiscreteValuationRing.not_a_field ℤ_[p])
    P₀ P

/-- **The tame equality for the relative different**: if `p` does not divide the ramification
index `e_{L/K}`, the exponent of `P` in the different of `R_L` over `R_K` is `e_{L/K} - 1`. -/
theorem towerDifferentExponent_rel_eq_of_tame (P₀ : Ideal (integralClosure ℤ_[p] K))
    [P₀.IsPrime] [P₀.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (P : Ideal (integralClosure ℤ_[p] L)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (hp : letI := towerAlgebra p K L
      ¬ p ∣ P.ramificationIdx (integralClosure ℤ_[p] K)) :
    letI := isDedekindDomain_ringOfIntegers_padic p K
    letI := isDedekindDomain_ringOfIntegers_padic p L
    letI := towerAlgebra p K L
    letI := tower_isTorsionFree p K L
    differentExponent (integralClosure ℤ_[p] K) (integralClosure ℤ_[p] L) P =
      P.ramificationIdx (integralClosure ℤ_[p] K) - 1 := by
  have := isDedekindDomain_ringOfIntegers_padic p K
  have := isDedekindDomain_ringOfIntegers_padic p L
  have := isTorsionFree_ringOfIntegers_padic p K
  have := isTorsionFree_ringOfIntegers_padic p L
  let := towerAlgebra p K L
  have := tower_isTorsionFree p K L
  have := tower_isScalarTower_int_int p K L
  have := tower_isIntegralClosure p K L
  have := tower_isSeparable p K L
  have : FiniteDimensional K L := Module.Finite.right ℚ_[p] K L
  have : IsFractionRing (integralClosure ℤ_[p] K) K :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[p] ℚ_[p] K _
  have := padicBridge_isLocalRing p L
  have := tower_liesOver p K L P₀ P
  have := tower_finite_quotient p K P₀
  have hpm : IsLocalRing.maximalIdeal ℤ_[p] ≠ ⊥ := IsDiscreteValuationRing.not_a_field ℤ_[p]
  have hP₀ : P₀ ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hpm P₀
  have : P₀.IsMaximal := IsPrime.isMaximal inferInstance hP₀
  exact tower_differentExponent_eq_of_ne_zero _ K L _ hP₀ P
    (tower_natCast_ne_zero p K P₀ hp)

/-- **Proposition 1.3 (i), the equality in the tame case** (page 12) for finite extensions
`ℚ_p ⊆ K ⊆ L`: if `L` is tamely ramified over `K` (`p ∤ e_{L/K}`), then
`𝔡_L = 𝔡_K + (e_{L/K} - 1)/e_L`. -/
theorem towerProp1_3i_eq_of_tame (P₀ : Ideal (integralClosure ℤ_[p] K)) [P₀.IsPrime]
    [P₀.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] (P : Ideal (integralClosure ℤ_[p] L))
    [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (hp : letI := towerAlgebra p K L
      ¬ p ∣ P.ramificationIdx (integralClosure ℤ_[p] K)) :
    letI := isDedekindDomain_ringOfIntegers_padic p K
    letI := isDedekindDomain_ringOfIntegers_padic p L
    letI := isTorsionFree_ringOfIntegers_padic p K
    letI := isTorsionFree_ringOfIntegers_padic p L
    letI := towerAlgebra p K L
    differentOrder ℤ_[p] (integralClosure ℤ_[p] L) P =
      differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P₀ +
        ((P.ramificationIdx (integralClosure ℤ_[p] K) : ℝ) - 1) / P.ramificationIdx ℤ_[p] := by
  have := isDedekindDomain_ringOfIntegers_padic p K
  have := isDedekindDomain_ringOfIntegers_padic p L
  have := isTorsionFree_ringOfIntegers_padic p K
  have := isTorsionFree_ringOfIntegers_padic p L
  let := towerAlgebra p K L
  have := tower_isTorsionFree p K L
  have := tower_liesOver p K L P₀ P
  have hexp := towerDifferentExponent_eq p K L P₀ P
  have hrel := towerDifferentExponent_rel_eq_of_tame p K L P₀ P hp
  have htow := towerRamificationIdx_eq_mul p K L P₀ P
  have hpm : IsLocalRing.maximalIdeal ℤ_[p] ≠ ⊥ := IsDiscreteValuationRing.not_a_field ℤ_[p]
  have he₀ : 0 < P₀.ramificationIdx ℤ_[p] := ramificationIdx_pos_of_liesOver hpm P₀
  have he' : 0 < P.ramificationIdx (integralClosure ℤ_[p] K) :=
    ramificationIdx_pos_of_liesOver (ne_bot_of_liesOver_of_ne_bot hpm P₀) P
  unfold differentOrder
  rw [hexp, hrel, htow]
  have h0 : (0 : ℝ) < P₀.ramificationIdx ℤ_[p] := by exact_mod_cast he₀
  have h1 : (0 : ℝ) < P.ramificationIdx (integralClosure ℤ_[p] K) := by exact_mod_cast he'
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub he', Nat.cast_one]
  field_simp
  ring

/-! ## 3. Proposition 1.3 (ii): the cases that are proved -/

/-- **Proposition 1.3 (ii) when `L/K` is tame** (page 12; the case `k_1 = k_i`, where the Galois
hypothesis is empty): if `p ∤ e_{L/K}`, then `𝔡_L ≤ 𝔡_K + n + 1/e_K` with
`n = v_p([L : K])` (the paper's `n_i`). In fact `𝔡_L ≤ 𝔡_K + 1/e_K`. -/
theorem towerProp1_3ii_of_tame (P₀ : Ideal (integralClosure ℤ_[p] K)) [P₀.IsPrime]
    [P₀.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] (P : Ideal (integralClosure ℤ_[p] L))
    [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (hp : letI := towerAlgebra p K L
      ¬ p ∣ P.ramificationIdx (integralClosure ℤ_[p] K)) :
    letI := isDedekindDomain_ringOfIntegers_padic p K
    letI := isDedekindDomain_ringOfIntegers_padic p L
    letI := isTorsionFree_ringOfIntegers_padic p K
    letI := isTorsionFree_ringOfIntegers_padic p L
    differentOrder ℤ_[p] (integralClosure ℤ_[p] L) P ≤
      differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P₀ + (multiplicity p (Module.finrank K L) : ℝ)
        + 1 / P₀.ramificationIdx ℤ_[p] := by
  have := isDedekindDomain_ringOfIntegers_padic p K
  have := isDedekindDomain_ringOfIntegers_padic p L
  have := isTorsionFree_ringOfIntegers_padic p K
  have := isTorsionFree_ringOfIntegers_padic p L
  let := towerAlgebra p K L
  have := tower_isTorsionFree p K L
  have := tower_liesOver p K L P₀ P
  have heq := towerProp1_3i_eq_of_tame p K L P₀ P hp
  have htow := towerRamificationIdx_eq_mul p K L P₀ P
  have hpm : IsLocalRing.maximalIdeal ℤ_[p] ≠ ⊥ := IsDiscreteValuationRing.not_a_field ℤ_[p]
  have he₀ : 1 ≤ P₀.ramificationIdx ℤ_[p] := ramificationIdx_pos_of_liesOver hpm P₀
  have he' : 1 ≤ P.ramificationIdx (integralClosure ℤ_[p] K) :=
    ramificationIdx_pos_of_liesOver (ne_bot_of_liesOver_of_ne_bot hpm P₀) P
  have h0 : (1 : ℝ) ≤ P₀.ramificationIdx ℤ_[p] := by exact_mod_cast he₀
  have h1 : (1 : ℝ) ≤ P.ramificationIdx (integralClosure ℤ_[p] K) := by exact_mod_cast he'
  have hn : (0 : ℝ) ≤ multiplicity p (Module.finrank K L) := Nat.cast_nonneg _
  have hle : ((P.ramificationIdx (integralClosure ℤ_[p] K) : ℝ) - 1) / P.ramificationIdx ℤ_[p] ≤
      1 / P₀.ramificationIdx ℤ_[p] := by
    rw [htow, Nat.cast_mul, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [heq]
  linarith

/-- `e_{L/K}` divides `[L : K]` (the fundamental identity `e·f = [L : K]`, with one prime). -/
theorem towerRamificationIdx_dvd_finrank (P₀ : Ideal (integralClosure ℤ_[p] K)) [P₀.IsPrime]
    [P₀.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] (P : Ideal (integralClosure ℤ_[p] L))
    [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    letI := towerAlgebra p K L
    P.ramificationIdx (integralClosure ℤ_[p] K) ∣ Module.finrank K L := by
  have := isDedekindDomain_ringOfIntegers_padic p K
  have := isDedekindDomain_ringOfIntegers_padic p L
  have := isTorsionFree_ringOfIntegers_padic p K
  have := isTorsionFree_ringOfIntegers_padic p L
  let := towerAlgebra p K L
  have := tower_isTorsionFree p K L
  have := tower_isScalarTower_int_int p K L
  have := tower_isScalarTower_padicInt_int p K L
  have := tower_isIntegralClosure p K L
  have := tower_isSeparable p K L
  have : FiniteDimensional K L := Module.Finite.right ℚ_[p] K L
  have : IsFractionRing (integralClosure ℤ_[p] K) K :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[p] ℚ_[p] K _
  have : IsFractionRing (integralClosure ℤ_[p] L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[p] ℚ_[p] L _
  have : Module.Finite (integralClosure ℤ_[p] K) (integralClosure ℤ_[p] L) :=
    IsIntegralClosure.finite (integralClosure ℤ_[p] K) K L _
  have := tower_liesOver p K L P₀ P
  have : P₀.IsMaximal := IsPrime.isMaximal inferInstance
    (ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field ℤ_[p]) P₀)
  rw [IsFractionRing.finrank_eq (integralClosure ℤ_[p] K) K (integralClosure ℤ_[p] L) L,
    ← Ideal.sum_ramification_inertia_eq_finrank P₀ (integralClosure ℤ_[p] L)]
  refine Finset.dvd_sum fun q _ => ?_
  have : q.1.LiesOver (IsLocalRing.maximalIdeal ℤ_[p]) := LiesOver.trans q.1 P₀ _
  have hq : q.1 = P := (padicBridge_prime_eq_maximalIdeal p L q.1).trans
    (padicBridge_prime_eq_maximalIdeal p L P).symm
  rw [hq]
  exact dvd_mul_right _ _

/-- **Proposition 1.3 (ii) when `n_i = 0`** (page 12; the base case of the paper's induction, here
without the Galois hypothesis): if `p ∤ [L : K]`, then `𝔡_L ≤ 𝔡_K + n + 1/e_K` with
`n = v_p([L : K]) = 0`. -/
theorem towerProp1_3ii_of_not_dvd_finrank (P₀ : Ideal (integralClosure ℤ_[p] K)) [P₀.IsPrime]
    [P₀.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] (P : Ideal (integralClosure ℤ_[p] L))
    [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (hn : ¬ p ∣ Module.finrank K L) :
    letI := isDedekindDomain_ringOfIntegers_padic p K
    letI := isDedekindDomain_ringOfIntegers_padic p L
    letI := isTorsionFree_ringOfIntegers_padic p K
    letI := isTorsionFree_ringOfIntegers_padic p L
    differentOrder ℤ_[p] (integralClosure ℤ_[p] L) P ≤
      differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P₀ + (multiplicity p (Module.finrank K L) : ℝ)
        + 1 / P₀.ramificationIdx ℤ_[p] :=
  towerProp1_3ii_of_tame p K L P₀ P fun h =>
    hn (h.trans (towerRamificationIdx_dvd_finrank p K L P₀ P))

end PadicTowerMain

/-! ## Proposition 1.3 (ii) from the classical bound on the relative different -/

section PadicTowerBound

variable (p : ℕ) [Fact p.Prime] (K L : Type*) [Field K] [Field L]
  [Algebra ℚ_[p] K] [Algebra ℚ_[p] L] [Algebra K L] [IsScalarTower ℚ_[p] K L]
  [Algebra ℤ_[p] K] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] K]
  [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] L]

/-- **Proposition 1.3 (ii) from an upper bound on the relative different** (page 12). Assume the
exponent of `P` in the different of `R_L` over `R_K` is at most `e_{L/K} - 1 + e_L·v_p(e_{L/K})`,
where `e_L = e_{L/ℚ_p}`, so that `e_L·v_p(e_{L/K})` is the valuation at `P` of the integer
`e_{L/K}` (this is the classical upper bound for the different of an extension of local fields;
it is not in Mathlib at the pinned version and it is not proved here). Then
`𝔡_L ≤ 𝔡_K + n + 1/e_K` with `n = v_p([L : K])`, with no Galois or tameness hypothesis. -/
theorem towerProp1_3ii_of_exponent_bound (P₀ : Ideal (integralClosure ℤ_[p] K)) [P₀.IsPrime]
    [P₀.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] (P : Ideal (integralClosure ℤ_[p] L))
    [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (hbound : letI := isDedekindDomain_ringOfIntegers_padic p K
      letI := isDedekindDomain_ringOfIntegers_padic p L
      letI := towerAlgebra p K L
      letI := tower_isTorsionFree p K L
      differentExponent (integralClosure ℤ_[p] K) (integralClosure ℤ_[p] L) P ≤
        P.ramificationIdx (integralClosure ℤ_[p] K) - 1 +
          P.ramificationIdx ℤ_[p] * multiplicity p (P.ramificationIdx (integralClosure ℤ_[p] K))) :
    letI := isDedekindDomain_ringOfIntegers_padic p K
    letI := isDedekindDomain_ringOfIntegers_padic p L
    letI := isTorsionFree_ringOfIntegers_padic p K
    letI := isTorsionFree_ringOfIntegers_padic p L
    differentOrder ℤ_[p] (integralClosure ℤ_[p] L) P ≤
      differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P₀ + (multiplicity p (Module.finrank K L) : ℝ)
        + 1 / P₀.ramificationIdx ℤ_[p] := by
  have := isDedekindDomain_ringOfIntegers_padic p K
  have := isDedekindDomain_ringOfIntegers_padic p L
  have := isTorsionFree_ringOfIntegers_padic p K
  have := isTorsionFree_ringOfIntegers_padic p L
  let := towerAlgebra p K L
  have := tower_isTorsionFree p K L
  have := tower_liesOver p K L P₀ P
  have hord := towerDifferentOrder_eq p K L P₀ P
  have htow := towerRamificationIdx_eq_mul p K L P₀ P
  have hdvd := towerRamificationIdx_dvd_finrank p K L P₀ P
  have hpm : IsLocalRing.maximalIdeal ℤ_[p] ≠ ⊥ := IsDiscreteValuationRing.not_a_field ℤ_[p]
  have he₀ : 1 ≤ P₀.ramificationIdx ℤ_[p] := ramificationIdx_pos_of_liesOver hpm P₀
  have he' : 1 ≤ P.ramificationIdx (integralClosure ℤ_[p] K) :=
    ramificationIdx_pos_of_liesOver (ne_bot_of_liesOver_of_ne_bot hpm P₀) P
  have : FiniteDimensional K L := Module.Finite.right ℚ_[p] K L
  have hfin : Module.finrank K L ≠ 0 := Module.finrank_pos.ne'
  have hv : multiplicity p (P.ramificationIdx (integralClosure ℤ_[p] K)) ≤
      multiplicity p (Module.finrank K L) := by
    rw [← multiplicity_dvd_iff_le hfin]
    exact (pow_multiplicity_dvd _ _).trans hdvd
  rw [htow] at hbound
  rw [hord]
  set a := differentExponent (integralClosure ℤ_[p] K) (integralClosure ℤ_[p] L) P with ha_def
  set e₀ := P₀.ramificationIdx ℤ_[p]
  set e₁ := P.ramificationIdx (integralClosure ℤ_[p] K)
  set v := multiplicity p e₁
  set n := multiplicity p (Module.finrank K L)
  have hrel : differentOrder (integralClosure ℤ_[p] K) (integralClosure ℤ_[p] L) P =
      (a : ℝ) / e₁ := rfl
  have h0 : (1 : ℝ) ≤ e₀ := by exact_mod_cast he₀
  have h1 : (1 : ℝ) ≤ e₁ := by exact_mod_cast he'
  have ha : (a : ℝ) ≤ e₁ - 1 + e₀ * e₁ * v := by
    have : ((e₁ - 1 + e₀ * e₁ * v : ℕ) : ℝ) = e₁ - 1 + e₀ * e₁ * v := by
      rw [Nat.cast_add, Nat.cast_sub he', Nat.cast_mul, Nat.cast_mul, Nat.cast_one]
    rw [← this]
    exact_mod_cast hbound
  have hvn : (v : ℝ) ≤ n := by exact_mod_cast hv
  have key : (a : ℝ) / e₁ / e₀ ≤ n + 1 / e₀ := by
    rw [div_div, div_le_iff₀ (by positivity)]
    have : (1 / (e₀ : ℝ)) * (e₁ * e₀) = e₁ := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hvn (by positivity : (0 : ℝ) ≤ e₀ * e₁)]
  rw [hrel]
  linarith

end PadicTowerBound

/-! ## The statement of Proposition 1.3 (ii) -/

section Statement

variable (p : ℕ) [Fact p.Prime] (K K₁ L : Type*) [Field K] [Field K₁] [Field L]
  [Algebra ℚ_[p] K] [Algebra ℚ_[p] K₁] [Algebra ℚ_[p] L]
  [Algebra K K₁] [Algebra K₁ L] [Algebra K L]
  [IsScalarTower ℚ_[p] K K₁] [IsScalarTower ℚ_[p] K₁ L] [IsScalarTower ℚ_[p] K L]
  [IsScalarTower K K₁ L]
  [Algebra ℤ_[p] K] [Algebra ℤ_[p] K₁] [Algebra ℤ_[p] L]
  [IsScalarTower ℤ_[p] ℚ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K₁] [IsScalarTower ℤ_[p] ℚ_[p] L]
  [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] K₁] [FiniteDimensional ℚ_[p] L]

/-- **The statement of IUT IV, Proposition 1.3 (ii)** (page 12), for finite extensions
`ℚ_p ⊆ K ⊆ K₁ ⊆ L` (the paper's `k_0 ⊆ k_1 ⊆ k_i`): if `L` is Galois over `K₁` and `K₁` is
tamely ramified over `K` (`p` does not divide the ramification index of the prime of `R_{K₁}`
over `R_K`), then `𝔡_L ≤ 𝔡_K + n + 1/e_K`, where `n = v_p([L : K])` (the paper's `n_i`, defined
on page 11), `𝔡_K`, `𝔡_L` are the orders of the differents normalized by `ord(p) = 1`, and `e_K`
is the ramification index of `K` over `ℚ_p`. Stated, not proved. -/
def towerProp1_3iiStatement : Prop :=
  IsGalois K₁ L →
    (∀ P₁ : Ideal (integralClosure ℤ_[p] K₁), P₁.IsPrime →
      P₁.LiesOver (IsLocalRing.maximalIdeal ℤ_[p]) →
      letI := towerAlgebra p K K₁
      ¬ p ∣ P₁.ramificationIdx (integralClosure ℤ_[p] K)) →
    ∀ (P₀ : Ideal (integralClosure ℤ_[p] K)) (P : Ideal (integralClosure ℤ_[p] L)),
      P₀.IsPrime → P₀.LiesOver (IsLocalRing.maximalIdeal ℤ_[p]) →
      P.IsPrime → P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p]) →
      letI := isDedekindDomain_ringOfIntegers_padic p K
      letI := isDedekindDomain_ringOfIntegers_padic p L
      letI := isTorsionFree_ringOfIntegers_padic p K
      letI := isTorsionFree_ringOfIntegers_padic p L
      differentOrder ℤ_[p] (integralClosure ℤ_[p] L) P ≤
        differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P₀ +
          (multiplicity p (Module.finrank K L) : ℝ) + 1 / P₀.ramificationIdx ℤ_[p]

end Statement

end IUT.PaperIV.LocalFields
