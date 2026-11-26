import IUT.PaperIV.ArithmeticDivisor

/-!
# IUT IV, Definition 1.9 (ii): the degree `deg_E` of an arithmetic divisor relative to a set
# of valuations

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Definition 1.9, pages 21 and 22 of
the April 2020 manuscript, read from the extracted text and from the rendered pages 21 and 22
(with a magnified crop of the display of (ii)).

Definition 1.9 (ii) of the paper: for a nonempty set `E ⊆ 𝕍(F)` of valuations lying over a
single valuation `v_ℚ` of `ℚ`, and an arithmetic divisor `𝔞` on `F`, write `𝔞_E` for the
portion of `𝔞` supported in `E` and set

`deg_E(𝔞) = deg(𝔞_E) / ∑_{v ∈ E} [F_v : ℚ_{v_ℚ}]`.

The paper then states that `deg_{E|K}(𝔞|_K) = deg_E(𝔞)` for a finite extension `K` of `F`, where
`E|K` is the set of valuations of `K` over `E`; part (i) states the analogous invariance
`deg(𝔞|_K) = deg(𝔞)` of the normalized degree.

**Interpretation of the numerator.** In the render of page 22 the line under `deg(𝔞_E)` is the
fraction bar, so the numerator is the degree `deg_F` of Definition 1.9 (i), not the normalized
degree; this file uses `degF` in the numerator.

**Domain.** `degE` is defined only on `PlaceSet F`, the finite sets `E` that are nonempty and
whose elements all lie over one place of `ℚ` (`LiesOverOnePlace`). Interpretation choice: the
place of `ℚ` below a valuation is encoded by `placeBelow` as `some p`, with `p` the residue
characteristic `ringChar (𝓞 F ⧸ 𝔭)`, for a finite place `𝔭`, and as `none` for an archimedean
place.

What is formalized: the domain (`placeBelow`, `LiesOverOnePlace`, `PlaceSet`), the definition
(`degE`), the local degree `[F_v : ℚ_{v_ℚ}]` (`localDeg`, as `e_v·f_v` at finite places and as
`InfinitePlace.mult` at infinite places), basic properties (`degE_add`, `degE_nonneg`), the
identification `deg_E(𝔞) = deg(𝔞_E)` (normalized degree) under the hypothesis that the local
degrees over `E` sum to `[F : ℚ]` (`degE_eq_normalizedDeg`), and its unconditional instance for
the set of all archimedean valuations (`degE_arc_eq_normalizedDeg`).

What is not formalized here: the set `E|K` and the invariance `deg_{E|K}(𝔞|_K) = deg_E(𝔞)` of
(ii). The pull-back `𝔞|_K` along a finite extension and the invariance `deg(𝔞|_K) = deg(𝔞)` of
(i) are in `IUT/PaperIV/DegreePullback.lean`, for one reading of "the evident fashion"; the fact
that the local degrees over all valuations above one finite `v_ℚ` sum to `[F : ℚ]` (fundamental
identity) is used there, through Mathlib's `Ideal.sum_ramification_inertia_eq_finrank`, and is
not proved in this file.
-/

open NumberField

namespace IUT.PaperIV

variable {F : Type*} [Field F] [NumberField F]

/-- The local degree `[F_v : ℚ_{v_ℚ}]`: `e_v·f_v` at a finite place (ramification index times
inertia degree of the prime of `𝓞 F` over `ℤ`), and `1` or `2` at an infinite place. -/
noncomputable def localDeg : Valuations F → ℕ
  | .inl v => v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ
  | .inr w => w.mult

/-- The place of `ℚ` below a valuation of `F`: `some p` for a finite place `𝔭`, where `p` is the
residue characteristic of `𝔭`, and `none` for an archimedean place. -/
noncomputable def placeBelow : Valuations F → Option ℕ
  | .inl v => some (ringChar (𝓞 F ⧸ v.asIdeal))
  | .inr _ => none

/-- The domain condition of Definition 1.9 (ii): `E` is nonempty and all its elements lie over
one place `v_ℚ` of `ℚ`. -/
def LiesOverOnePlace (E : Finset (Valuations F)) : Prop :=
  E.Nonempty ∧ ∃ vQ : Option ℕ, ∀ v ∈ E, placeBelow v = vQ

variable (F) in
/-- The finite sets of valuations on which Definition 1.9 (ii) defines `deg_E`. -/
abbrev PlaceSet : Type _ := {E : Finset (Valuations F) // LiesOverOnePlace E}

open scoped Classical in
/-- `𝔞_E`, the portion of `𝔞` supported in `E`. -/
noncomputable def ADiv.restrict (E : Finset (Valuations F)) (a : ADiv F) : ADiv F :=
  a.filter (· ∈ E)

/-- **Definition 1.9 (ii)**, with the unnormalized degree in the numerator (see the module
docstring): for `E` a nonempty set of valuations over one place of `ℚ`,
`deg_E(𝔞) = deg_F(𝔞_E) / ∑_{v ∈ E} [F_v : ℚ_{v_ℚ}]`. -/
noncomputable def degE (E : PlaceSet F) (a : ADiv F) : ℝ :=
  degF (ADiv.restrict E.1 a) / ∑ v ∈ E.1, (localDeg v : ℝ)

omit [NumberField F] in
theorem ADiv.restrict_add (E : Finset (Valuations F)) (a b : ADiv F) :
    ADiv.restrict E (a + b) = ADiv.restrict E a + ADiv.restrict E b := by
  classical
  simp only [ADiv.restrict]
  exact Finsupp.filter_add

theorem degE_add (E : PlaceSet F) (a b : ADiv F) :
    degE E (a + b) = degE E a + degE E b := by
  simp [degE, ADiv.restrict_add, add_div]

omit [NumberField F] in
theorem ADiv.restrict_effective {E : Finset (Valuations F)} {a : ADiv F} (h : a.Effective) :
    (ADiv.restrict E a).Effective := by
  classical
  intro v
  simp only [ADiv.restrict]
  rw [Finsupp.filter_apply]
  split_ifs
  · exact h v
  · exact le_rfl

theorem degE_nonneg {E : PlaceSet F} {a : ADiv F} (h : a.Effective) :
    0 ≤ degE E a :=
  div_nonneg (degF_nonneg (ADiv.restrict_effective h))
    (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)

/-- If the local degrees over `E` sum to `[F : ℚ]`, then `deg_E(𝔞)` is the normalized degree of
`𝔞_E`. The hypothesis holds when `E` is the set of all valuations over one `v_ℚ`; this file proves
that only for the archimedean place (`sum_localDeg_arc`). -/
theorem degE_eq_normalizedDeg {E : PlaceSet F} (a : ADiv F)
    (hE : ∑ v ∈ E.1, (localDeg v : ℝ) = Module.finrank ℚ F) :
    degE E a = normalizedDeg (ADiv.restrict E.1 a) := by
  rw [degE, hE, normalizedDeg]

/-- The set of all archimedean valuations, i.e. the valuations over the archimedean place of
`ℚ`. -/
noncomputable def arcValuations (F : Type*) [Field F] [NumberField F] :
    Finset (Valuations F) :=
  Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩

/-- The local degrees `[F_w : ℝ]` over all archimedean `w` sum to `[F : ℚ]`. -/
theorem sum_localDeg_arc :
    ∑ v ∈ arcValuations F, (localDeg v : ℝ) = Module.finrank ℚ F := by
  rw [arcValuations, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, localDeg]
  exact_mod_cast InfinitePlace.sum_mult_eq

/-- The set of all archimedean valuations, as an element of `PlaceSet F`: it is nonempty and all
its elements lie over the archimedean place of `ℚ`. -/
noncomputable def arcPlaceSet (F : Type*) [Field F] [NumberField F] : PlaceSet F :=
  ⟨arcValuations F, by
    refine ⟨?_, none, ?_⟩
    · rw [arcValuations, Finset.map_nonempty]; exact Finset.univ_nonempty
    · intro v hv
      rw [arcValuations, Finset.mem_map] at hv
      obtain ⟨w, -, rfl⟩ := hv
      rfl⟩

/-- **Unconditional instance.** For `E` the set of all archimedean valuations,
`deg_E(𝔞) = deg(𝔞_E)`. -/
theorem degE_arc_eq_normalizedDeg (a : ADiv F) :
    degE (arcPlaceSet F) a = normalizedDeg (ADiv.restrict (arcValuations F) a) :=
  degE_eq_normalizedDeg a sum_localDeg_arc

end IUT.PaperIV
