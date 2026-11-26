import IUT.PaperIV.LocalFields.Tower
import IUT.PaperIV.LocalFields.UnitVolume

/-!
# IUT IV, Proposition 1.3 (ii) for finite extensions of `ℚ_p`, and the bound for the different

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Proposition 1.3 and its proof,
pages 11 and 12 of the April 2020 manuscript, and Remark 1.3.1 on page 13. Pages read for this
file: 11, 12 and 13. Pages checked against rendered images: 11, 12 and 13 (the notation `R_0`,
`𝔡_0`, `e_0`, `e_{i/0}`, `[k_i : k_0]`, `n_i` and the inequality of (i) on page 11; the tame
equality of (i), assertion (ii) and its proof on page 12; Remark 1.3.1 on page 13). The setting,
the normalization `ord(p) = 1` and the notation are those of `IUT.PaperIV.LocalFields.Tower`.

## The statement of the paper

Page 12, assertion (ii): "Suppose that `k_i` is a finite Galois extension of a subfield
`k_1 ⊆ k_i` such that `k_0 ⊆ k_1`, and `k_1` is tamely ramified over `k_0`. Then we have:
`𝔡_i ≤ 𝔡_0 + n_i + 1/e_0`", where (page 11) `n_i` is the nonnegative integer with
`[k_i : k_0]/p^{n_i}` an integer prime to `p`. The proof on page 12 first replaces `k_0` by an
unramified extension of `k_0` contained in `k_i`, so that `k_i` is totally ramified over `k_0`;
for (ii) it inducts on `n_i` through Galois `p`-subextensions and computes the different of a
Kummer extension `x^p - ϖ_*`. Remark 1.3.1 refers to [Ih], Lemma A, for similar estimates.

## What is proved

The proof here is not the paper's induction. It rests on the classical upper bound for the
different of an extension of local fields, `v_P(𝔇_{L/K}) ≤ e - 1 + v_P(e)` with `e = e_{L/K}`.
That bound is not printed in IUT IV; it is proved here from the trace, as follows.

1. `diffBound_differentExponent_lt` (a local extension of Dedekind domains `B/A`, `p ⊆ A`
   maximal, `P` the prime of `B`): if the integer `n = [L : K]` generates `P ^ m` in `B`, then
   `v_P(𝔇_{B/A}) < m + e`. The trace of `1` is `n`, which does not lie in the ideal `n·p`, and
   `(n·p) B = P ^ (m + e)`; Mathlib's `not_dvd_differentIdeal_of_intTrace_notMem` concludes.
2. `diffBound_exponent_le_finrank`: for `ℚ_p ⊆ K ⊆ L`,
   `v_P(𝔇_{L/K}) ≤ e_{L/K} - 1 + e_L·v_p([L : K])` (`diffBound_map_span_natCast`: the integer
   `n` generates `P ^ (e_L·v_p(n))`). With `[L : K] = e_{L/K}` this is the classical bound in the
   totally ramified case, `diffBound_exponent_le_of_totallyRamified`.
3. The classical bound in general, `diffBound_exponent_le`: `v_P(𝔇_{L/K}) ≤ e_{L/K} - 1 +
   e_L·v_p(e_{L/K})`, in the exact form of the hypothesis of `towerProp1_3ii_of_exponent_bound`.
   As on page 12, the proof passes through an unramified subextension `K₁ = K(a)`, where `a` is a
   root of unity of order `N` prime to `p` whose powers represent the nonzero residues of `L`
   (`diffBound_exists_residue_root`, by Hensel's lemma in the complete ring `R_L`). Then:
   `K₁/K` is unramified, since the derivative of the minimal polynomial of `a` at `a` divides
   `N a ^ (N - 1)`, a unit, and lies in the different (`diffBound_ramificationIdx_eq_one`);
   `[L : K₁] = e_{L/K₁}`, since the residue field extension of `L/K₁` is trivial
   (`diffBound_finrank_eq_ramificationIdx`); and `diffBound_exponent_le_of_intermediate` glues
   these by the transitivity of the different (`towerDifferentExponent_eq`).
4. Proposition 1.3 (ii) for every finite `L/K`, with no Galois or tameness hypothesis:
   `diffBound_prop1_3ii`, from item 2 alone, since `(e_{L/K} - 1)/e_L < 1/e_K`. Consequently
   `diffBound_towerProp1_3iiStatement` proves `towerProp1_3iiStatement` (the form of page 12) for
   all its parameters.
5. `diffBound_prop1_3i`: Proposition 1.3 (i) over a general base in one statement, the
   inequality together with the equality in the tame case.

## Not proved

* The paper's own route to (ii) (the induction on `n_i`, Galois `p`-subextensions and Kummer
  generators) is not formalized; the statement is proved by the different route above.
* The equality case of the classical bound (for example `ℚ_2(√2)/ℚ_2`) is not checked here.
-/

open Ideal nonZeroDivisors

namespace IUT.PaperIV.LocalFields

section DiffBoundGeneral

variable (A K L B : Type*) [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L] [IsFractionRing A K]
  [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]

include K L

/-- The trace from `B` to `A` of `1` is the degree `[L : K]`. -/
theorem diffBound_intTrace_one :
    haveI := IsIntegralClosure.finite A K L B
    Algebra.intTrace A B 1 = (Module.finrank K L : A) := by
  have := IsIntegralClosure.finite A K L B
  apply IsFractionRing.injective A K
  rw [Algebra.algebraMap_intTrace (K := K) (L := L), map_one, ← map_one (algebraMap K L),
    Algebra.trace_algebraMap, map_natCast, nsmul_eq_mul, mul_one]

/-- **The trace bound for the different.** Let `p` be a nonzero maximal ideal of `A` and `P` a
prime of `B` over `p`, with ramification index `e`. If the integer `n = [L : K]` generates in `B`
the ideal `P ^ m`, then the exponent of `P` in the different of `B` over `A` is less than `m + e`.
The proof: the trace of `1` is `n`, which does not lie in `n·p`, while `(n·p) B = P ^ (m + e)`
when `B` is local. -/
theorem diffBound_differentExponent_lt [IsLocalRing B] {p : Ideal A} [p.IsMaximal]
    (hp : p ≠ ⊥) (P : Ideal B) [P.IsPrime] [P.LiesOver p] {m : ℕ}
    (hm : (Ideal.span {((Module.finrank K L : ℕ) : A)}).map (algebraMap A B) = P ^ m) :
    differentExponent A B P < m + P.ramificationIdx A := by
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
  have hP0 : P ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp P
  set n : A := ((Module.finrank K L : ℕ) : A) with hn
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.map_bot] at hm
    exact pow_ne_zero m hP0 hm.symm
  have hmap : P ^ (m + P.ramificationIdx A) * ⊤ =
      (Ideal.span {n} * p).map (algebraMap A B) := by
    rw [mul_top, Ideal.map_mul, hm, tower_map_eq_pow A B hp P, pow_add]
  have htr : Algebra.intTrace A B 1 ∉ Ideal.span {n} * p := by
    rw [diffBound_intTrace_one A K L B, ← hn, Ideal.mem_span_singleton_mul]
    rintro ⟨z, hz, hnz⟩
    have hz1 : z = 1 := by
      have : n * z = n * 1 := by rw [mul_one]; exact hnz
      exact mul_left_cancel₀ hn0 this
    exact (Ideal.IsMaximal.ne_top inferInstance) ((Ideal.eq_top_iff_one p).mpr (hz1 ▸ hz))
  have hnd := not_dvd_differentIdeal_of_intTrace_notMem A (P ^ (m + P.ramificationIdx A)) ⊤
    hmap 1 Submodule.mem_top htr
  exact lt_of_not_ge fun hle => hnd ((pow_dvd_pow P hle).trans (pow_multiplicity_dvd P _))

end DiffBoundGeneral

section DiffBoundPadic

variable (p : ℕ) [Fact p.Prime] (K L : Type*) [Field K] [Field L]
  [Algebra ℚ_[p] K] [Algebra ℚ_[p] L] [Algebra K L] [IsScalarTower ℚ_[p] K L]
  [Algebra ℤ_[p] K] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] K]
  [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] L]

omit [FiniteDimensional ℚ_[p] K] in
/-- A nonzero natural number `n` generates in `R_L` the ideal `P ^ (e_L·v_p(n))`, where `e_L` is
the ramification index of `P` over `p` and `v_p(n)` the exponent of `p` in `n`. -/
theorem diffBound_map_span_natCast (P : Ideal (integralClosure ℤ_[p] L)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] {n : ℕ} (hn : n ≠ 0) :
    letI := towerAlgebra p K L
    (Ideal.span {((n : ℕ) : integralClosure ℤ_[p] K)}).map
        (algebraMap (integralClosure ℤ_[p] K) (integralClosure ℤ_[p] L)) =
      P ^ (P.ramificationIdx ℤ_[p] * multiplicity p n) := by
  let := towerAlgebra p K L
  have := isDedekindDomain_ringOfIntegers_padic p L
  have := isTorsionFree_ringOfIntegers_padic p L
  have := padicBridge_isLocalRing p L
  have hpp : p.Prime := Fact.out
  have hpm : IsLocalRing.maximalIdeal ℤ_[p] ≠ ⊥ := IsDiscreteValuationRing.not_a_field ℤ_[p]
  rw [Ideal.map_span, Set.image_singleton, map_natCast,
    Nat.multiplicity_eq_factorization hpp (n := n)]
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n p]
  set u := n / p ^ (n.factorization p)
  have hu : ¬ p ∣ u := Nat.not_dvd_ordCompl hpp hn
  have hunit : IsUnit ((u : ℕ) : integralClosure ℤ_[p] L) := by
    have h1 : IsUnit ((u : ℕ) : ℤ_[p]) := PadicInt.isUnit_iff.mpr
      (PadicInt.norm_natCast_eq_one_iff.mpr ((hpp.coprime_iff_not_dvd).mpr hu))
    have h2 := h1.map (algebraMap ℤ_[p] (integralClosure ℤ_[p] L))
    rwa [map_natCast] at h2
  have hP : Ideal.span {((p : ℕ) : integralClosure ℤ_[p] L)} = P ^ P.ramificationIdx ℤ_[p] := by
    rw [← tower_map_eq_pow ℤ_[p] (integralClosure ℤ_[p] L) hpm P,
      PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]
  rw [Nat.cast_mul, Ideal.span_singleton_mul_right_unit hunit, Nat.cast_pow,
    ← Ideal.span_singleton_pow, hP, ← pow_mul]

/-- **The bound for the relative different by the degree**: for finite extensions
`ℚ_p ⊆ K ⊆ L`, `v_P(𝔇_{L/K}) ≤ e_{L/K} - 1 + e_L·v_p([L : K])`, where `𝔇_{L/K}` is the
different of `R_L` over `R_K`, `e_{L/K}` the ramification index of `P` over `P₀`, and `e_L` that of
`P` over `p`. -/
theorem diffBound_exponent_le_finrank (P₀ : Ideal (integralClosure ℤ_[p] K)) [P₀.IsPrime]
    [P₀.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] (P : Ideal (integralClosure ℤ_[p] L))
    [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    letI := isDedekindDomain_ringOfIntegers_padic p K
    letI := isDedekindDomain_ringOfIntegers_padic p L
    letI := towerAlgebra p K L
    letI := tower_isTorsionFree p K L
    differentExponent (integralClosure ℤ_[p] K) (integralClosure ℤ_[p] L) P ≤
      P.ramificationIdx (integralClosure ℤ_[p] K) - 1 +
        P.ramificationIdx ℤ_[p] * multiplicity p (Module.finrank K L) := by
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
  have hpm : IsLocalRing.maximalIdeal ℤ_[p] ≠ ⊥ := IsDiscreteValuationRing.not_a_field ℤ_[p]
  have hP₀ : P₀ ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hpm P₀
  have : P₀.IsMaximal := IsPrime.isMaximal inferInstance hP₀
  have hfin : Module.finrank K L ≠ 0 := Module.finrank_pos.ne'
  have hlt := diffBound_differentExponent_lt _ K L _ hP₀ P
    (diffBound_map_span_natCast p K L P hfin)
  have he' : 1 ≤ P.ramificationIdx (integralClosure ℤ_[p] K) :=
    ramificationIdx_pos_of_liesOver hP₀ P
  omega

/-- **The classical bound in the totally ramified case**: if `[L : K] = e_{L/K}`, then
`v_P(𝔇_{L/K}) ≤ e_{L/K} - 1 + e_L·v_p(e_{L/K})`, where `e_L·v_p(e_{L/K})` is the valuation at `P`
of the integer `e_{L/K}`. This is the hypothesis of `towerProp1_3ii_of_exponent_bound`. -/
theorem diffBound_exponent_le_of_totallyRamified (P₀ : Ideal (integralClosure ℤ_[p] K))
    [P₀.IsPrime] [P₀.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (P : Ideal (integralClosure ℤ_[p] L)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (htot : letI := towerAlgebra p K L
      Module.finrank K L = P.ramificationIdx (integralClosure ℤ_[p] K)) :
    letI := isDedekindDomain_ringOfIntegers_padic p K
    letI := isDedekindDomain_ringOfIntegers_padic p L
    letI := towerAlgebra p K L
    letI := tower_isTorsionFree p K L
    differentExponent (integralClosure ℤ_[p] K) (integralClosure ℤ_[p] L) P ≤
      P.ramificationIdx (integralClosure ℤ_[p] K) - 1 +
        P.ramificationIdx ℤ_[p] * multiplicity p (P.ramificationIdx (integralClosure ℤ_[p] K)) := by
  have h := diffBound_exponent_le_finrank p K L P₀ P
  rw [htot] at h
  exact h

/-- **Proposition 1.3 (ii) for every finite extension** `ℚ_p ⊆ K ⊆ L` (page 12), with no Galois
or tameness hypothesis: `𝔡_L ≤ 𝔡_K + n + 1/e_K`, with `n = v_p([L : K])` (the paper's `n_i`),
`𝔡_K`, `𝔡_L` the orders of the differents normalized by `ord(p) = 1`, and `e_K` the ramification
index of `K` over `ℚ_p`. From `diffBound_exponent_le_finrank` and the transitivity
`towerDifferentOrder_eq`: `𝔡_L - 𝔡_K = v_P(𝔇_{L/K})/e_L ≤ (e_{L/K} - 1)/e_L + n < 1/e_K + n`;
the statement exports only the non-strict `≤`. -/
theorem diffBound_prop1_3ii (P₀ : Ideal (integralClosure ℤ_[p] K)) [P₀.IsPrime]
    [P₀.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] (P : Ideal (integralClosure ℤ_[p] L))
    [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
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
  have hbound := diffBound_exponent_le_finrank p K L P₀ P
  have hord := towerDifferentOrder_eq p K L P₀ P
  have htow := towerRamificationIdx_eq_mul p K L P₀ P
  have hpm : IsLocalRing.maximalIdeal ℤ_[p] ≠ ⊥ := IsDiscreteValuationRing.not_a_field ℤ_[p]
  have he₀ : 1 ≤ P₀.ramificationIdx ℤ_[p] := ramificationIdx_pos_of_liesOver hpm P₀
  have he' : 1 ≤ P.ramificationIdx (integralClosure ℤ_[p] K) :=
    ramificationIdx_pos_of_liesOver (ne_bot_of_liesOver_of_ne_bot hpm P₀) P
  rw [htow] at hbound
  rw [hord]
  set a := differentExponent (integralClosure ℤ_[p] K) (integralClosure ℤ_[p] L) P
  set e₀ := P₀.ramificationIdx ℤ_[p]
  set e₁ := P.ramificationIdx (integralClosure ℤ_[p] K)
  set n := multiplicity p (Module.finrank K L)
  have hrel : differentOrder (integralClosure ℤ_[p] K) (integralClosure ℤ_[p] L) P =
      (a : ℝ) / e₁ := rfl
  have h0 : (1 : ℝ) ≤ e₀ := by exact_mod_cast he₀
  have h1 : (1 : ℝ) ≤ e₁ := by exact_mod_cast he'
  have ha : (a : ℝ) ≤ e₁ - 1 + e₀ * e₁ * n := by
    have : ((e₁ - 1 + e₀ * e₁ * n : ℕ) : ℝ) = e₁ - 1 + e₀ * e₁ * n := by
      rw [Nat.cast_add, Nat.cast_sub he', Nat.cast_mul, Nat.cast_mul, Nat.cast_one]
    rw [← this]
    exact_mod_cast hbound
  have key : (a : ℝ) / e₁ / e₀ ≤ n + 1 / e₀ := by
    rw [div_div, div_le_iff₀ (by positivity)]
    have : (1 / (e₀ : ℝ)) * (e₁ * e₀) = e₁ := by field_simp
    nlinarith
  rw [hrel]
  linarith

/-- **Proposition 1.3 (i) over a general base, in one statement** (pages 11 and 12): for finite
extensions `ℚ_p ⊆ K ⊆ L`, `𝔡_L ≥ 𝔡_K + (e_{L/K} - 1)/e_L`, and if `L` is tamely ramified over `K`
(`p ∤ e_{L/K}`) this is an equality. The conjunction of `towerProp1_3i_ge` and
`towerProp1_3i_eq_of_tame`. -/
theorem diffBound_prop1_3i (P₀ : Ideal (integralClosure ℤ_[p] K)) [P₀.IsPrime]
    [P₀.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] (P : Ideal (integralClosure ℤ_[p] L))
    [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    letI := isDedekindDomain_ringOfIntegers_padic p K
    letI := isDedekindDomain_ringOfIntegers_padic p L
    letI := isTorsionFree_ringOfIntegers_padic p K
    letI := isTorsionFree_ringOfIntegers_padic p L
    letI := towerAlgebra p K L
    differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P₀ +
        ((P.ramificationIdx (integralClosure ℤ_[p] K) : ℝ) - 1) / P.ramificationIdx ℤ_[p] ≤
      differentOrder ℤ_[p] (integralClosure ℤ_[p] L) P ∧
    (¬ p ∣ P.ramificationIdx (integralClosure ℤ_[p] K) →
      differentOrder ℤ_[p] (integralClosure ℤ_[p] L) P =
        differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P₀ +
          ((P.ramificationIdx (integralClosure ℤ_[p] K) : ℝ) - 1) / P.ramificationIdx ℤ_[p]) :=
  ⟨towerProp1_3i_ge p K L P₀ P, fun hp => towerProp1_3i_eq_of_tame p K L P₀ P hp⟩

end DiffBoundPadic

section DiffBoundStatement

variable (p : ℕ) [Fact p.Prime] (K K₁ L : Type*) [Field K] [Field K₁] [Field L]
  [Algebra ℚ_[p] K] [Algebra ℚ_[p] K₁] [Algebra ℚ_[p] L]
  [Algebra K K₁] [Algebra K₁ L] [Algebra K L]
  [IsScalarTower ℚ_[p] K K₁] [IsScalarTower ℚ_[p] K₁ L] [IsScalarTower ℚ_[p] K L]
  [IsScalarTower K K₁ L]
  [Algebra ℤ_[p] K] [Algebra ℤ_[p] K₁] [Algebra ℤ_[p] L]
  [IsScalarTower ℤ_[p] ℚ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K₁] [IsScalarTower ℤ_[p] ℚ_[p] L]
  [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] K₁] [FiniteDimensional ℚ_[p] L]

omit [IsScalarTower K K₁ L] in
/-- **Reduction to the totally ramified case.** Let `ℚ_p ⊆ K ⊆ K₁ ⊆ L` be finite extensions with
`K₁/K` unramified at the primes over `p` (`e_{K₁/K} = 1`) and `[L : K₁] = e_{L/K₁}`. Then the
classical bound `v_P(𝔇_{L/K}) ≤ e_{L/K} - 1 + e_L·v_p(e_{L/K})` holds. The proof: the different
of `K₁/K` is trivial (the tame equality with `e = 1`), so transitivity gives
`v_P(𝔇_{L/K}) = v_P(𝔇_{L/K₁})` and `e_{L/K₁} = e_{L/K}`; then apply the totally ramified case. -/
theorem diffBound_exponent_le_of_intermediate (P₀ : Ideal (integralClosure ℤ_[p] K))
    [P₀.IsPrime] [P₀.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (P₁ : Ideal (integralClosure ℤ_[p] K₁)) [P₁.IsPrime]
    [P₁.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (P : Ideal (integralClosure ℤ_[p] L)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (he : letI := towerAlgebra p K K₁
      P₁.ramificationIdx (integralClosure ℤ_[p] K) = 1)
    (htot : letI := towerAlgebra p K₁ L
      Module.finrank K₁ L = P.ramificationIdx (integralClosure ℤ_[p] K₁)) :
    letI := isDedekindDomain_ringOfIntegers_padic p K
    letI := isDedekindDomain_ringOfIntegers_padic p L
    letI := towerAlgebra p K L
    letI := tower_isTorsionFree p K L
    differentExponent (integralClosure ℤ_[p] K) (integralClosure ℤ_[p] L) P ≤
      P.ramificationIdx (integralClosure ℤ_[p] K) - 1 +
        P.ramificationIdx ℤ_[p] * multiplicity p (P.ramificationIdx (integralClosure ℤ_[p] K)) := by
  have := isDedekindDomain_ringOfIntegers_padic p K
  have := isDedekindDomain_ringOfIntegers_padic p K₁
  have := isDedekindDomain_ringOfIntegers_padic p L
  have := isTorsionFree_ringOfIntegers_padic p K
  have := isTorsionFree_ringOfIntegers_padic p K₁
  have := isTorsionFree_ringOfIntegers_padic p L
  have hKL := towerDifferentExponent_eq p K L P₀ P
  have hK₁L := towerDifferentExponent_eq p K₁ L P₁ P
  have hKK₁ := towerDifferentExponent_eq p K K₁ P₀ P₁
  have hrel := towerDifferentExponent_rel_eq_of_tame p K K₁ P₀ P₁
    (by rw [he]; exact (Fact.out : p.Prime).not_dvd_one)
  have r1 := towerRamificationIdx_eq_mul p K L P₀ P
  have r2 := towerRamificationIdx_eq_mul p K₁ L P₁ P
  have r3 := towerRamificationIdx_eq_mul p K K₁ P₀ P₁
  have hb := diffBound_exponent_le_of_totallyRamified p K₁ L P₁ P htot
  have hpm : IsLocalRing.maximalIdeal ℤ_[p] ≠ ⊥ := IsDiscreteValuationRing.not_a_field ℤ_[p]
  have he₀ : 0 < P₀.ramificationIdx ℤ_[p] := ramificationIdx_pos_of_liesOver hpm P₀
  rw [he, mul_one] at r3
  rw [hrel, he, Nat.sub_self, zero_add, one_mul] at hKK₁
  rw [r3] at r2
  have heq := Nat.eq_of_mul_eq_mul_left he₀ (r2.symm.trans r1)
  rw [heq] at hb hK₁L
  rw [hKK₁] at hK₁L
  have hd := hKL.symm.trans hK₁L
  have hd' := Nat.add_right_cancel hd
  rw [hd']
  exact hb

omit [IsScalarTower ℚ_[p] K₁ L] [IsScalarTower K K₁ L] [FiniteDimensional ℚ_[p] K₁] in
/-- **IUT IV, Proposition 1.3 (ii), as printed** (page 12): `towerProp1_3iiStatement` holds for
all finite extensions `ℚ_p ⊆ K ⊆ K₁ ⊆ L`. The Galois and tameness hypotheses are not used: the
conclusion holds for every finite `L/K` (`diffBound_prop1_3ii`). -/
theorem diffBound_towerProp1_3iiStatement : towerProp1_3iiStatement p K K₁ L := by
  intro _ _ P₀ P h₀ h₀' h h'
  exact @diffBound_prop1_3ii p _ K L _ _ _ _ _ _ _ _ _ _ _ _ P₀ h₀ h₀' P h h'

end DiffBoundStatement

/-! ## The unramified subextension generated by a root of unity -/

section DiffBoundRoots

variable (p : ℕ) [Fact p.Prime] (L : Type*) [Field L] [Algebra ℚ_[p] L]
  [FiniteDimensional ℚ_[p] L] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L]

/-- **Roots of unity of order prime to `p` represent the residue field.** For a finite extension
`L` of `ℚ_[p]` and the prime `P` of `R_L` over `p`, there are `a ∈ R_L` and `N > 0` with
`p ∤ N` and `a ^ N = 1` such that every element of `R_L` lies in `P` or is congruent modulo `P`
to a power of `a`. In the proof (not in the statement, which only asserts existence), `N + 1` is
the cardinality of the residue field and `a` is the Hensel
lift (Mathlib's `IsAdicComplete.henselianRing` with `unitVol_isAdicComplete`) of a generator of
the cyclic group of units of the residue field. -/
theorem diffBound_exists_residue_root (P : Ideal (integralClosure ℤ_[p] L)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    ∃ (a : integralClosure ℤ_[p] L) (N : ℕ), 0 < N ∧ ¬ p ∣ N ∧ a ^ N = 1 ∧
      ∀ y : integralClosure ℤ_[p] L, y ∈ P ∨ ∃ j : ℕ, y - a ^ j ∈ P := by
  have := padicBridge_isLocalRing p L
  have hPm := padicBridge_prime_eq_maximalIdeal p L P
  have hAC := unitVol_isAdicComplete p L
  have hPmax : P.IsMaximal := by rw [hPm]; exact IsLocalRing.maximalIdeal.isMaximal _
  let _ : Field (integralClosure ℤ_[p] L ⧸ P) := Ideal.Quotient.field P
  have := tower_finite_quotient p L P
  classical
  let _ : Fintype (integralClosure ℤ_[p] L ⧸ P) := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := (integralClosure ℤ_[p] L ⧸ P)ˣ)
  have hq1 : 1 < Fintype.card (integralClosure ℤ_[p] L ⧸ P) := Fintype.one_lt_card
  obtain ⟨N, hqN⟩ : ∃ N, Fintype.card (integralClosure ℤ_[p] L ⧸ P) = N + 1 :=
    ⟨_, (Nat.sub_add_cancel hq1.le).symm⟩
  have hN : 0 < N := by omega
  have hNq : (N : integralClosure ℤ_[p] L ⧸ P) = -1 := by
    have h := FiniteField.cast_card_eq_zero (integralClosure ℤ_[p] L ⧸ P)
    rw [hqN, Nat.cast_add, Nat.cast_one] at h
    exact eq_neg_of_add_eq_zero_left h
  have hpP : ((p : ℕ) : integralClosure ℤ_[p] L ⧸ P) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem,
      ← map_natCast (algebraMap ℤ_[p] (integralClosure ℤ_[p] L))]
    have hmem : ((p : ℕ) : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.subset_span rfl
    rw [P.over_def (IsLocalRing.maximalIdeal ℤ_[p])] at hmem
    exact hmem
  have hNne : (N : integralClosure ℤ_[p] L ⧸ P) ≠ 0 := by
    rw [hNq]
    exact neg_ne_zero.mpr one_ne_zero
  have hpN : ¬ p ∣ N := by
    rintro ⟨k, hk⟩
    apply hNne
    rw [hk, Nat.cast_mul, hpP, zero_mul]
  obtain ⟨a₀, ha₀⟩ :=
    Ideal.Quotient.mk_surjective
      ((g : (integralClosure ℤ_[p] L ⧸ P)ˣ) : integralClosure ℤ_[p] L ⧸ P)
  let F : Polynomial (integralClosure ℤ_[p] L) := Polynomial.X ^ N - Polynomial.C 1
  have hF : F.Monic := Polynomial.monic_X_pow_sub_C 1 hN.ne'
  have hg1 : ((g : (integralClosure ℤ_[p] L ⧸ P)ˣ) : integralClosure ℤ_[p] L ⧸ P) ^ N = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one
      ((g : (integralClosure ℤ_[p] L ⧸ P)ˣ) : integralClosure ℤ_[p] L ⧸ P) g.ne_zero
    rwa [hqN, Nat.add_sub_cancel] at h
  have h₁ : F.eval a₀ ∈ IsLocalRing.maximalIdeal (integralClosure ℤ_[p] L) := by
    rw [← hPm, ← Ideal.Quotient.eq_zero_iff_mem]
    simp [F, ha₀, hg1]
  have h₂ : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (integralClosure ℤ_[p] L))
      (F.derivative.eval a₀)) := by
    rw [← hPm, isUnit_iff_ne_zero]
    simp only [F, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_C, sub_zero, Polynomial.eval_mul, Polynomial.eval_natCast,
      Polynomial.eval_pow, Polynomial.eval_X, map_mul, map_pow, map_natCast, ha₀]
    exact mul_ne_zero hNne (pow_ne_zero _ g.ne_zero)
  obtain ⟨a, ha, haa⟩ :=
    HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal (integralClosure ℤ_[p] L)) F hF a₀
      h₁ h₂
  rw [← hPm] at haa
  have haN : a ^ N = 1 := by
    have := ha.eq_zero
    simp only [F, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at this
    exact sub_eq_zero.mp this
  have hag : Ideal.Quotient.mk P a =
      ((g : (integralClosure ℤ_[p] L ⧸ P)ˣ) : integralClosure ℤ_[p] L ⧸ P) := by
    rw [← ha₀]
    exact Ideal.Quotient.eq.mpr haa
  refine ⟨a, N, hN, hpN, haN, fun y => ?_⟩
  by_cases hy : y ∈ P
  · exact Or.inl hy
  · right
    have hy0 : Ideal.Quotient.mk P y ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨j, hj⟩ := hg (Units.mk0 _ hy0)
    refine ⟨j, Ideal.Quotient.eq.mp ?_⟩
    rw [map_pow, hag]
    have := congrArg Units.val hj
    rw [Units.val_pow_eq_pow_val, Units.val_mk0] at this
    exact this.symm

end DiffBoundRoots

section DiffBoundUnramified

variable (p : ℕ) [Fact p.Prime] (K L : Type*) [Field K] [Field L]
  [Algebra ℚ_[p] K] [Algebra ℚ_[p] L] [Algebra K L] [IsScalarTower ℚ_[p] K L]
  [Algebra ℤ_[p] K] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] K]
  [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] L]

/-- **An extension generated by a root of unity of order prime to `p` is unramified.** If `L` is
generated over `K` by an integer `ζ` with `ζ ^ N = 1` and `p ∤ N`, then `e_{L/K} = 1`. The
proof: the minimal polynomial `g` of `ζ` over `R_K` divides `X ^ N - 1`, so `g'(ζ)` divides
`N ζ ^ (N - 1)`, a unit; `g'(ζ)` lies in the different (Mathlib's
`aeval_derivative_mem_differentIdeal`), so the different is trivial, and
`e_{L/K} - 1 ≤ v_P(𝔇_{L/K}) = 0`. -/
theorem diffBound_ramificationIdx_eq_one (P₀ : Ideal (integralClosure ℤ_[p] K)) [P₀.IsPrime]
    [P₀.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] (P : Ideal (integralClosure ℤ_[p] L))
    [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (ζ : integralClosure ℤ_[p] L) {N : ℕ} (hN : 0 < N) (hpN : ¬ p ∣ N) (hζ : ζ ^ N = 1)
    (hgen : Algebra.adjoin K {(ζ : L)} = ⊤) :
    letI := towerAlgebra p K L
    P.ramificationIdx (integralClosure ℤ_[p] K) = 1 := by
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
  have := tower_liesOver p K L P₀ P
  have hpm : IsLocalRing.maximalIdeal ℤ_[p] ≠ ⊥ := IsDiscreteValuationRing.not_a_field ℤ_[p]
  have hP₀ : P₀ ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hpm P₀
  have : P₀.IsMaximal := IsPrime.isMaximal inferInstance hP₀
  have : Module.Finite (integralClosure ℤ_[p] K) (integralClosure ℤ_[p] L) :=
    IsIntegralClosure.finite (integralClosure ℤ_[p] K) K L _
  have : Algebra.IsIntegral (integralClosure ℤ_[p] K) (integralClosure ℤ_[p] L) :=
    Algebra.IsIntegral.of_finite _ _
  have hint : IsIntegral (integralClosure ℤ_[p] K) ζ := Algebra.IsIntegral.isIntegral ζ
  have hroot :
      Polynomial.aeval ζ (Polynomial.X ^ N - 1 : Polynomial (integralClosure ℤ_[p] K)) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, map_one, hζ, sub_self]
  obtain ⟨h, hh⟩ := minpoly.isIntegrallyClosed_dvd hint hroot
  have hder : Polynomial.aeval ζ
      (Polynomial.derivative (Polynomial.X ^ N - 1 : Polynomial (integralClosure ℤ_[p] K))) =
      Polynomial.aeval ζ (Polynomial.derivative (minpoly (integralClosure ℤ_[p] K) ζ)) *
        Polynomial.aeval ζ h := by
    rw [hh, Polynomial.derivative_mul, map_add, map_mul, map_mul, minpoly.aeval, zero_mul,
      add_zero]
  have hunitN : IsUnit ((N : ℕ) : (integralClosure ℤ_[p] L)) := by
    have h1 : IsUnit ((N : ℕ) : ℤ_[p]) := PadicInt.isUnit_iff.mpr
      (PadicInt.norm_natCast_eq_one_iff.mpr (((Fact.out : p.Prime).coprime_iff_not_dvd).mpr hpN))
    have h2 := h1.map (algebraMap ℤ_[p] (integralClosure ℤ_[p] L))
    rwa [map_natCast] at h2
  have hunitζ : IsUnit ζ := IsUnit.of_pow_eq_one hζ hN.ne'
  have hunit :
      IsUnit (Polynomial.aeval ζ
        (Polynomial.derivative (minpoly (integralClosure ℤ_[p] K) ζ))) := by
    apply isUnit_of_mul_isUnit_left (y := Polynomial.aeval ζ h)
    rw [← hder]
    simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_one, sub_zero, map_mul, map_natCast, map_pow, Polynomial.aeval_X]
    exact hunitN.mul (hunitζ.pow _)
  have hmem := aeval_derivative_mem_differentIdeal (integralClosure ℤ_[p] K) K L ζ hgen
  have htop : differentIdeal (integralClosure ℤ_[p] K) (integralClosure ℤ_[p] L) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ hmem hunit
  have hP : P ≠ ⊤ := IsPrime.ne_top inferInstance
  have h0 : differentExponent (integralClosure ℤ_[p] K) (integralClosure ℤ_[p] L) P = 0 := by
    unfold differentExponent
    rw [htop]
    refine multiplicity_eq_zero_of_not_dvd fun hd => ?_
    exact hP (top_le_iff.mp (Ideal.le_of_dvd hd))
  have hle := ramificationIdx_sub_one_le_differentExponent (integralClosure ℤ_[p] K) K L
    (integralClosure ℤ_[p] L) hP₀ P
  have hpos := ramificationIdx_pos_of_liesOver hP₀ P
  omega

/-- **Residue degree one forces `[L : K] = e_{L/K}`.** If every element of `R_L` is congruent
modulo `P` to an element of `R_K` (the residue field extension is trivial), then the degree
`[L : K]` equals the ramification index `e_{L/K}` (the fundamental identity
`Ideal.sum_ramification_inertia_eq_finrank`, with one prime and inertia degree one). -/
theorem diffBound_finrank_eq_ramificationIdx (P₀ : Ideal (integralClosure ℤ_[p] K))
    [P₀.IsPrime] [P₀.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (P : Ideal (integralClosure ℤ_[p] L)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (hres : letI := towerAlgebra p K L
      ∀ y : integralClosure ℤ_[p] L, ∃ x : integralClosure ℤ_[p] K,
        y - algebraMap (integralClosure ℤ_[p] K) (integralClosure ℤ_[p] L) x ∈ P) :
    letI := towerAlgebra p K L
    Module.finrank K L = P.ramificationIdx (integralClosure ℤ_[p] K) := by
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
  have hpm : IsLocalRing.maximalIdeal ℤ_[p] ≠ ⊥ := IsDiscreteValuationRing.not_a_field ℤ_[p]
  have hP₀ : P₀ ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hpm P₀
  have : P₀.IsMaximal := IsPrime.isMaximal inferInstance hP₀
  have : P.IsMaximal := IsPrime.isMaximal inferInstance (ne_bot_of_liesOver_of_ne_bot hP₀ P)
  have hf : P.inertiaDeg (integralClosure ℤ_[p] K) = 1 := by
    rw [Ideal.inertiaDeg_eq_of_isMaximal P₀ P]
    let _ : Field (integralClosure ℤ_[p] K ⧸ P₀) := Ideal.Quotient.field P₀
    let _ : Field (integralClosure ℤ_[p] L ⧸ P) := Ideal.Quotient.field P
    rw [finrank_eq_one_iff']
    refine ⟨1, one_ne_zero, fun w => ?_⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨x, hx⟩ := hres y
    refine ⟨Ideal.Quotient.mk P₀ x, ?_⟩
    rw [Algebra.smul_def, mul_one]
    exact (Ideal.Quotient.eq.mpr hx).symm
  rw [IsFractionRing.finrank_eq (integralClosure ℤ_[p] K) K (integralClosure ℤ_[p] L) L,
    ← Ideal.sum_ramification_inertia_eq_finrank P₀ (integralClosure ℤ_[p] L)]
  have huniq : ∀ q : P₀.primesOver (integralClosure ℤ_[p] L), q.1 = P := by
    intro q
    have : q.1.LiesOver (IsLocalRing.maximalIdeal ℤ_[p]) := LiesOver.trans q.1 P₀ _
    exact (padicBridge_prime_eq_maximalIdeal p L q.1).trans
      (padicBridge_prime_eq_maximalIdeal p L P).symm
  have : Subsingleton (P₀.primesOver (integralClosure ℤ_[p] L)) :=
    ⟨fun a b => Subtype.ext ((huniq a).trans (huniq b).symm)⟩
  rw [Fintype.sum_subsingleton _ ⟨P, ⟨inferInstance, inferInstance⟩⟩, hf, mul_one]

end DiffBoundUnramified

section DiffBoundGeneralCase

variable (p : ℕ) [Fact p.Prime] (K L : Type*) [Field K] [Field L]
  [Algebra ℚ_[p] K] [Algebra ℚ_[p] L] [Algebra K L] [IsScalarTower ℚ_[p] K L]
  [Algebra ℤ_[p] K] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] K]
  [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] L]

/-- **The classical upper bound for the different** of a finite extension `ℚ_p ⊆ K ⊆ L`:
`v_P(𝔇_{L/K}) ≤ e_{L/K} - 1 + e_L·v_p(e_{L/K})`, where `e_L·v_p(e_{L/K})` is the valuation at `P`
of the integer `e_{L/K}`. This is exactly the hypothesis of `towerProp1_3ii_of_exponent_bound`.
The proof: let `a ∈ R_L` be a root of unity of order `N` prime to `p` whose powers represent the
nonzero residues (`diffBound_exists_residue_root`) and `K₁ = K(a)`; then `K₁/K` is unramified
(`diffBound_ramificationIdx_eq_one`), `L/K₁` has trivial residue extension, so
`[L : K₁] = e_{L/K₁}` (`diffBound_finrank_eq_ramificationIdx`), and
`diffBound_exponent_le_of_intermediate` reduces to the totally ramified case. -/
theorem diffBound_exponent_le (P₀ : Ideal (integralClosure ℤ_[p] K)) [P₀.IsPrime]
    [P₀.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] (P : Ideal (integralClosure ℤ_[p] L))
    [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    letI := isDedekindDomain_ringOfIntegers_padic p K
    letI := isDedekindDomain_ringOfIntegers_padic p L
    letI := towerAlgebra p K L
    letI := tower_isTorsionFree p K L
    differentExponent (integralClosure ℤ_[p] K) (integralClosure ℤ_[p] L) P ≤
      P.ramificationIdx (integralClosure ℤ_[p] K) - 1 +
        P.ramificationIdx ℤ_[p] * multiplicity p (P.ramificationIdx (integralClosure ℤ_[p] K)) := by
  have := tower_isScalarTower_padicInt p K L
  have : FiniteDimensional K L := Module.Finite.right ℚ_[p] K L
  obtain ⟨a, N, hN, hpN, haN, hres⟩ := diffBound_exists_residue_root p L P
  set θ : L := (a : L) with hθdef
  set E : IntermediateField K L := IntermediateField.adjoin K {θ}
  have hEz : IsScalarTower ℤ_[p] ℚ_[p] E := IsScalarTower.of_algebraMap_eq fun x =>
    Subtype.ext (IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] L x)
  have hEL : IsScalarTower ℤ_[p] E L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hEq : IsScalarTower ℚ_[p] E L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hEfd : FiniteDimensional ℚ_[p] E := FiniteDimensional.of_injective
    (IsScalarTower.toAlgHom ℚ_[p] E L).toLinearMap (RingHom.injective _)
  have := padicBridge_isLocalRing p E
  have := padicBridge_maximalIdeal_liesOver p E
  have hθint : IsIntegral K θ := Algebra.IsIntegral.isIntegral θ
  have hgenint : IsIntegral ℤ_[p] (IntermediateField.AdjoinSimple.gen K θ) := by
    refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ_[p] E L)
      (RingHom.injective _)).mp ?_
    rw [IsScalarTower.coe_toAlgHom', IntermediateField.AdjoinSimple.algebraMap_gen]
    exact a.2
  let ζ : integralClosure ℤ_[p] E := ⟨_, hgenint⟩
  have hζval : ((ζ : E) : L) = θ := rfl
  have hζN : ζ ^ N = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, IntermediateField.coe_pow, hζval, hθdef]
    exact congrArg Subtype.val haN
  have hgen : Algebra.adjoin K {(ζ : E)} = ⊤ :=
    PowerBasis.adjoin_gen_eq_top (IntermediateField.adjoin.powerBasis hθint)
  have he := diffBound_ramificationIdx_eq_one p K E P₀
    (IsLocalRing.maximalIdeal (integralClosure ℤ_[p] E)) ζ hN hpN hζN hgen
  have htot := diffBound_finrank_eq_ramificationIdx p E L
    (IsLocalRing.maximalIdeal (integralClosure ℤ_[p] E)) P (by
      intro y
      rcases hres y with hy | ⟨j, hj⟩
      · exact ⟨0, by rw [map_zero, sub_zero]; exact hy⟩
      · refine ⟨ζ ^ j, ?_⟩
        have hmap : (letI := towerAlgebra p E L
            algebraMap (integralClosure ℤ_[p] E) (integralClosure ℤ_[p] L) (ζ ^ j)) = a ^ j := by
          rw [map_pow]
          congr 1
        rw [hmap]
        exact hj)
  exact diffBound_exponent_le_of_intermediate p K E L P₀
    (IsLocalRing.maximalIdeal (integralClosure ℤ_[p] E)) P he htot

/-- **Proposition 1.3 (ii) from the classical bound**: the hypothesis of
`towerProp1_3ii_of_exponent_bound` is discharged by `diffBound_exponent_le`. -/
theorem diffBound_prop1_3ii_of_classical (P₀ : Ideal (integralClosure ℤ_[p] K)) [P₀.IsPrime]
    [P₀.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] (P : Ideal (integralClosure ℤ_[p] L))
    [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    letI := isDedekindDomain_ringOfIntegers_padic p K
    letI := isDedekindDomain_ringOfIntegers_padic p L
    letI := isTorsionFree_ringOfIntegers_padic p K
    letI := isTorsionFree_ringOfIntegers_padic p L
    differentOrder ℤ_[p] (integralClosure ℤ_[p] L) P ≤
      differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P₀ + (multiplicity p (Module.finrank K L) : ℝ)
        + 1 / P₀.ramificationIdx ℤ_[p] :=
  towerProp1_3ii_of_exponent_bound p K L P₀ P (diffBound_exponent_le p K L P₀ P)

end DiffBoundGeneralCase

end IUT.PaperIV.LocalFields
