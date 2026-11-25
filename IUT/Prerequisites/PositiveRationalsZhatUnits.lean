import Mathlib

/-!
# The elementary fact `ℚ_{>0} ∩ Ẑ^× = {1}`

Source: Mochizuki, *Inter-universal Teichmüller Theory I*, Example 5.1 (v), PDF page 127
(rendered and read), where the injectivity of a Kummer map is deduced "from the elementary
observation that, relative to the natural inclusion `ℚ ↪ Ẑ ⊗ ℚ`, `ℚ_{>0} ∩ Ẑ^× = {1}`".
The same fact is invoked in *Inter-universal Teichmüller Theory III*, Remark 2.3.3 (vi), (vii),
(viii), PDF pages 81 to 83 (text only, from the extracted text), and in Remark 3.12.1 (iii),
PDF pages 186 and 187 (rendered and read), where it is described as playing a key role in the
multiradial algorithms for cyclotomic rigidity isomorphisms in the number field case, and as an
immediate consequence of an interpretation of the product formula.

This file is not a formalization of Example 5.1; it proves only the elementary arithmetic fact
quoted above.

## Interpretation choices, recorded

* Mathlib has no `Ẑ`. We model `Ẑ` as the product `∏_p ℤ_p`, written `Zhat`, indexed by the
  nonzero primes of `ℤ` (`IsDedekindDomain.HeightOneSpectrum ℤ`), with `ℤ_p` the ring
  `v.adicCompletionIntegers ℚ` of Mathlib.
* `Ẑ ⊗ ℚ` is modeled by Mathlib's finite adele ring `IsDedekindDomain.FiniteAdeleRing ℤ ℚ`,
  the restricted product of the `ℚ_p` with respect to the `ℤ_p`. The isomorphism
  `Ẑ ⊗ ℚ ≅ 𝔸_f` is standard but is not proved here. The inclusion `ℚ ↪ Ẑ ⊗ ℚ` is Mathlib's
  `algebraMap ℚ (FiniteAdeleRing ℤ ℚ)`, and `Ẑ ↪ Ẑ ⊗ ℚ` is the ring map `Zhat.toFiniteAdeles`
  defined below (the restricted product contains the full product of the integer rings).
* `ℚ_{>0} ∩ Ẑ^×` is read as the set of positive rationals whose image in `𝔸_f` is the image of a
  unit of `Ẑ`. The main theorem `posRat_inter_zhatUnits` says this set is `{1}`.

The core of the proof is `eq_one_of_forall_valuation_eq_one`: a positive rational number that is
a unit at every prime is `1`. It uses Mathlib's
`IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one`.
-/

namespace IUT.Prerequisites

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

/-- `Ẑ`, modeled as the product `∏_p ℤ_p` of the rings of `p`-adic integers over the nonzero
primes of `ℤ`. -/
abbrev Zhat : Type := Π v : HeightOneSpectrum ℤ, v.adicCompletionIntegers ℚ

/-- The natural ring map `Ẑ → Ẑ ⊗ ℚ`, with `Ẑ ⊗ ℚ` modeled by the finite adeles of `ℚ`: an element
of `∏_p ℤ_p` is integral at every prime, so it lies in the restricted product. -/
noncomputable def Zhat.toFiniteAdeles : Zhat →+* FiniteAdeleRing ℤ ℚ where
  toFun x := ⟨fun v => (x v : v.adicCompletion ℚ), Filter.Eventually.of_forall fun v => (x v).2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem Zhat.toFiniteAdeles_apply (x : Zhat) (v : HeightOneSpectrum ℤ) :
    Zhat.toFiniteAdeles x v = (x v : v.adicCompletion ℚ) := rfl

/-- A positive rational number whose `v`-adic valuation is `1` at every nonzero prime `v` of `ℤ`
is equal to `1`. -/
theorem eq_one_of_forall_valuation_eq_one {q : ℚ} (hq : 0 < q)
    (h : ∀ v : HeightOneSpectrum ℤ, v.valuation ℚ q = 1) : q = 1 := by
  obtain ⟨n, hn⟩ := mem_integers_of_valuation_le_one ℚ q fun v => (h v).le
  obtain ⟨m, hm⟩ := mem_integers_of_valuation_le_one ℚ q⁻¹ fun v => by
    rw [map_inv₀, h v, inv_one]
  simp only [algebraMap_int_eq, eq_intCast] at hn hm
  have hnm : n * m = 1 := by
    have : ((n * m : ℤ) : ℚ) = 1 := by
      rw [Int.cast_mul, hn, hm, mul_inv_cancel₀ hq.ne']
    exact_mod_cast this
  have hn0 : 0 < n := by
    have : (0 : ℚ) < n := hn ▸ hq
    exact_mod_cast this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hnm with h1 | h1
  · rw [← hn, h1, Int.cast_one]
  · omega

/-- **`ℚ_{>0} ∩ Ẑ^× = {1}`** (IUT I, page 127), relative to the natural inclusion
`ℚ ↪ Ẑ ⊗ ℚ = 𝔸_f`: the positive rationals whose image in the finite adeles is the image of a unit
of `Ẑ = ∏_p ℤ_p` are exactly `{1}`. -/
theorem posRat_inter_zhatUnits :
    {q : ℚ | 0 < q ∧ ∃ u : Zhatˣ,
      Zhat.toFiniteAdeles (u : Zhat) = algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q} = {1} := by
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hq, u, hu⟩
    refine eq_one_of_forall_valuation_eq_one hq fun v => ?_
    have hunit : IsUnit ((u : Zhat) v) :=
      u.isUnit.map (Pi.evalMonoidHom (fun w : HeightOneSpectrum ℤ => w.adicCompletionIntegers ℚ) v)
    have hval := adicCompletionIntegers.isUnit_iff_valued_eq_one.mp hunit
    have hcomp : (((u : Zhat) v : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) =
        algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q v :=
      congrArg (fun a : FiniteAdeleRing ℤ ℚ => a v) hu
    rw [hcomp, FiniteAdeleRing.algebraMap_apply, valuedAdicCompletion_eq_valuation'] at hval
    exact hval
  · rintro rfl
    exact ⟨one_pos, 1, by simp⟩

end IUT.Prerequisites
