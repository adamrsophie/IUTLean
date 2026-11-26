import Mathlib

/-!
# IUT IV, Definition 1.9 (i): arithmetic divisors on a number field

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Definition 1.9, pages 21 and 22
of the April 2020 manuscript, which recalls notation from [GenEll], §1.

For a number field `F`, the set `𝕍(F)` of valuations is the disjoint union of the
nonarchimedean ones and the archimedean ones. An ℝ-arithmetic divisor is a finite formal sum
`∑ c_v · v` with real coefficients. The degree map sends a nonarchimedean `v` to `log(q_v)`,
with `q_v` the cardinality of the residue field, and an archimedean `v` to `1`.

## Interpretation choices, recorded

* Nonarchimedean valuations are represented by the nonzero prime ideals of the ring of
  integers (`IsDedekindDomain.HeightOneSpectrum (𝓞 F)`), archimedean ones by
  `NumberField.InfinitePlace F`. A pair of complex conjugate embeddings is one valuation.
* The archimedean weight is `1` for real and complex places alike, exactly as in the display
  of Definition 1.9 (i). Other conventions weight a complex place by `2`.
* The pull-back `𝔞|_K` to a finite extension, defined "in the evident fashion", and the
  identity `deg(𝔞|_K) = deg(𝔞)` for the normalized degree are formalized in
  `IUT/PaperIV/DegreePullback.lean`, in one reading of that phrase. Part (ii) of the definition
  is not formalized here.
-/

open NumberField

namespace IUT.PaperIV

variable (F : Type*) [Field F] [NumberField F]

/-- The set `𝕍(F)` of valuations of `F`: nonarchimedean ones on the left, archimedean ones
on the right. -/
abbrev Valuations : Type _ :=
  IsDedekindDomain.HeightOneSpectrum (𝓞 F) ⊕ InfinitePlace F

/-- The group `ADiv_ℝ(F)` of ℝ-arithmetic divisors: finite formal real combinations of
valuations. -/
abbrev ADiv : Type _ := Valuations F →₀ ℝ

variable {F}

/-- The weight of a valuation in the degree map: `log(q_v)` at a nonarchimedean valuation,
where `q_v` is the cardinality of the residue field, and `1` at an archimedean one. -/
noncomputable def degWeight : Valuations F → ℝ
  | .inl v => Real.log (Ideal.absNorm v.asIdeal)
  | .inr _ => 1

theorem degWeight_nonneg (v : Valuations F) : 0 ≤ degWeight v := by
  cases v with
  | inl v => exact Real.log_natCast_nonneg _
  | inr _ => exact zero_le_one

/-- The support `Supp(𝔞)`: the valuations with nonzero coefficient. -/
def ADiv.supp (a : ADiv F) : Finset (Valuations F) := a.support

/-- An arithmetic divisor is effective when all its coefficients are `≥ 0`. -/
def ADiv.Effective (a : ADiv F) : Prop := ∀ v, 0 ≤ a v

/-- The degree map `deg_F : ADiv_ℝ(F) → ℝ`, a homomorphism of groups. -/
noncomputable def degF : ADiv F →+ ℝ :=
  Finsupp.liftAddHom fun v => AddMonoidHom.mulLeft (degWeight v)

theorem degF_single (v : Valuations F) (c : ℝ) :
    degF (Finsupp.single v c) = degWeight v * c := by
  simp [degF]

theorem degF_apply (a : ADiv F) : degF a = a.sum fun v c => degWeight v * c := by
  simp [degF, Finsupp.liftAddHom_apply]

/-- An effective arithmetic divisor has nonnegative degree. -/
theorem degF_nonneg {a : ADiv F} (h : a.Effective) : 0 ≤ degF a := by
  rw [degF_apply]
  exact Finset.sum_nonneg fun v _ => mul_nonneg (degWeight_nonneg v) (h v)

/-- The normalized degree `deg(𝔞) = deg_F(𝔞) / [F : ℚ]`. -/
noncomputable def normalizedDeg (a : ADiv F) : ℝ := degF a / Module.finrank ℚ F

theorem normalizedDeg_add (a b : ADiv F) :
    normalizedDeg (a + b) = normalizedDeg a + normalizedDeg b := by
  simp [normalizedDeg, add_div]

theorem normalizedDeg_nonneg {a : ADiv F} (h : a.Effective) : 0 ≤ normalizedDeg a :=
  div_nonneg (degF_nonneg h) (Nat.cast_nonneg _)

end IUT.PaperIV
