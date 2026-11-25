import Mathlib
import IUT.PaperIV.ArithmeticDivisor

/-!
# Normalized absolute values and the product formula over `𝕍(F)`

Sources:
* Mochizuki, *Inter-universal Teichmüller Theory IV*, Definition 1.9, PDF pages 21 and 22
  (rendered and read): the set `𝕍(F)` of valuations of a number field `F`, as the disjoint union
  of the nonarchimedean and archimedean valuations, formalized in
  `IUT/PaperIV/ArithmeticDivisor.lean` as `IUT.PaperIV.Valuations F`.
* Mochizuki, *Inter-universal Teichmüller Theory III*, Remark 3.12.1 (iii), PDF pages 186 and 187
  (rendered and read), which describes the fact `ℚ_{>0} ∩ Ẑ^× = {1}` as an immediate consequence
  of an interpretation of the product formula.

This file is not a formalization of any numbered statement of the papers. It transports the
product formula of Mathlib (`NumberField.prod_abs_eq_one`, in
`Mathlib/NumberTheory/NumberField/ProductFormula.lean`) to the index set `IUT.PaperIV.Valuations F`
used for arithmetic divisors in this project, in multiplicative and in additive (logarithmic) form.

## Interpretation choices, recorded

* The normalized absolute value `‖x‖_v` at a nonarchimedean `v` is Mathlib's
  `NumberField.FinitePlace.mk v x`, which equals `q_v ^ (- ord_v x)` with `q_v` the cardinality of
  the residue field (see the module docstring of the Mathlib file above).
* At an archimedean `v` it is `|x|_v ^ m_v`, with `m_v = 1` for a real place and `m_v = 2` for a
  complex place (`NumberField.InfinitePlace.mult`). The papers do not fix this normalization on
  the pages read; it is the one for which the product formula holds with all multiplicities one.
  Note that the degree map of IUT IV Definition 1.9 (i) gives weight `1` to every archimedean
  valuation, real or complex; no relation between the two conventions is asserted here.
-/

namespace IUT.Prerequisites

open NumberField IUT.PaperIV

/-- A finite product over a sum type splits into the two partial products. -/
theorem finprod_sum_type {α β M : Type*} [CommMonoid M] (f : α ⊕ β → M)
    (hf : (Function.mulSupport f).Finite) :
    ∏ᶠ i, f i = (∏ᶠ a, f (.inl a)) * ∏ᶠ b, f (.inr b) := by
  classical
  set s : Finset α := (hf.preimage Sum.inl_injective.injOn).toFinset
  set t : Finset β := (hf.preimage Sum.inr_injective.injOn).toFinset
  have h1 : ∏ᶠ i, f i = ∏ i ∈ s.disjSum t, f i := by
    refine finprod_eq_prod_of_mulSupport_subset f fun i hi => ?_
    cases i with
    | inl a => simpa [s, Finset.mem_disjSum] using hi
    | inr b => simpa [t, Finset.mem_disjSum] using hi
  have h2 : ∏ᶠ a, f (.inl a) = ∏ a ∈ s, f (.inl a) :=
    finprod_eq_prod_of_mulSupport_subset _ fun a ha => by simpa [s] using ha
  have h3 : ∏ᶠ b, f (.inr b) = ∏ b ∈ t, f (.inr b) :=
    finprod_eq_prod_of_mulSupport_subset _ fun b hb => by simpa [t] using hb
  rw [h1, h2, h3, Finset.prod_disjSum]

variable {F : Type*} [Field F] [NumberField F]

/-- The normalized absolute value `‖x‖_v` at a valuation `v ∈ 𝕍(F)`: Mathlib's finite place
absolute value (`q_v ^ (- ord_v x)`) at a nonarchimedean `v`, and `|x|_v ^ m_v` at an archimedean
`v`, where `m_v ∈ {1, 2}` is `1` for a real place and `2` for a complex place. -/
noncomputable def normAbs : Valuations F → F → ℝ
  | .inl v, x => FinitePlace.mk v x
  | .inr w, x => w x ^ w.mult

theorem normAbs_nonneg (v : Valuations F) (x : F) : 0 ≤ normAbs v x := by
  cases v with
  | inl v => exact apply_nonneg _ x
  | inr w => exact pow_nonneg (apply_nonneg _ x) _

theorem normAbs_pos (v : Valuations F) {x : F} (hx : x ≠ 0) : 0 < normAbs v x := by
  cases v with
  | inl v => exact lt_of_le_of_ne (apply_nonneg _ x) ((map_ne_zero (FinitePlace.mk v)).mpr hx).symm
  | inr w => exact pow_pos (w.pos_iff.mpr hx) _

/-- For `x ≠ 0`, `‖x‖_v = 1` for all but finitely many `v ∈ 𝕍(F)`. -/
theorem normAbs_mulSupport_finite {x : F} (hx : x ≠ 0) :
    (Function.mulSupport fun v : Valuations F => normAbs v x).Finite := by
  have hfin : (Function.mulSupport fun v => normAbs (F := F) (.inl v) x).Finite := by
    have := (FinitePlace.hasFiniteMulSupport hx).preimage
      (f := FinitePlace.equivHeightOneSpectrum.symm)
      (FinitePlace.equivHeightOneSpectrum.symm.injective.injOn)
    simpa [Function.mulSupport, normAbs, FinitePlace.mk_apply,
      FinitePlace.equivHeightOneSpectrum_symm_apply] using this
  refine ((hfin.image Sum.inl).union (Set.finite_univ.image Sum.inr)).subset ?_
  rintro (v | w) hv
  · exact Or.inl ⟨v, hv, rfl⟩
  · exact Or.inr ⟨w, trivial, rfl⟩

/-- **Product formula over `𝕍(F)`**: for `x ∈ F` nonzero, `∏_{v ∈ 𝕍(F)} ‖x‖_v = 1`. -/
theorem prod_normAbs_eq_one {x : F} (hx : x ≠ 0) : ∏ᶠ v : Valuations F, normAbs v x = 1 := by
  have hfin : ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), normAbs (.inl v) x =
      ∏ᶠ w : FinitePlace F, w x := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    rfl
  rw [finprod_sum_type _ (normAbs_mulSupport_finite hx), hfin, mul_comm,
    finprod_eq_prod_of_fintype]
  exact prod_abs_eq_one hx

/-- **Product formula over `𝕍(F)`, additive form**: for `x ∈ F` nonzero,
`∑_{v ∈ 𝕍(F)} log ‖x‖_v = 0`. -/
theorem sum_log_normAbs_eq_zero {x : F} (hx : x ≠ 0) :
    ∑ᶠ v : Valuations F, Real.log (normAbs v x) = 0 := by
  classical
  set s := (normAbs_mulSupport_finite hx).toFinset
  have hsub : Function.mulSupport (fun v : Valuations F => normAbs v x) ⊆ s := by simp [s]
  have hprod := prod_normAbs_eq_one hx
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub] at hprod
  rw [finsum_eq_sum_of_support_subset _ (s := s) fun v hv => hsub fun h => hv (by simp [h]),
    ← Real.log_prod fun v _ => (normAbs_pos v hx).ne', hprod, Real.log_one]

end IUT.Prerequisites
