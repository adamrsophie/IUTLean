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
`E|K` is the set of valuations of `K` over `E`.

**Interpretation.** In the render the numerator `deg` is not underlined, so it is the
unnormalized degree `deg_F` of Definition 1.9 (i), not the normalized degree `deg` (underlined).
With `deg_F` in the numerator, passing to `K` multiplies both the numerator and the denominator
by `[K : F]`, so the stated invariance holds; with the normalized degree in the numerator it
would fail by the factor `1/[K : F]`, and the averaging in Steps (v) and (viii) of the proof of
Theorem 1.10 would not be consistent. This file therefore uses `degF` in the numerator
(`degE`). The reading differs from one in which the numerator is the normalized degree.

What is formalized: the definition (`degE`), the local degree `[F_v : ℚ_{v_ℚ}]` (`localDeg`, as
`e_v·f_v` at finite places and as `InfinitePlace.mult` at infinite places), basic properties
(`degE_add`, `degE_nonneg`), the identification `deg_E(𝔞) = deg(𝔞_E)` (normalized degree) when
the local degrees over `E` sum to `[F : ℚ]` (`degE_eq_normalizedDeg`), its unconditional
instance for the set of all archimedean valuations (`degE_arc_eq_normalizedDeg`), and the
scaling fact behind the invariance (`degE_ratio_invariant`). The invariance itself, which needs
pullback of arithmetic divisors along an extension `K/F`, is not formalized.
-/

open NumberField

namespace IUT.PaperIV

variable {F : Type*} [Field F] [NumberField F]

/-- The local degree `[F_v : ℚ_{v_ℚ}]`: `e_v·f_v` at a finite place (ramification index times
inertia degree of the prime of `𝓞 F` over `ℤ`), and `1` or `2` at an infinite place. -/
noncomputable def localDeg : Valuations F → ℕ
  | .inl v => v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ
  | .inr w => w.mult

open scoped Classical in
/-- `𝔞_E`, the portion of `𝔞` supported in `E`. -/
noncomputable def ADiv.restrict (E : Finset (Valuations F)) (a : ADiv F) : ADiv F :=
  a.filter (· ∈ E)

/-- **Definition 1.9 (ii)**, with the unnormalized degree in the numerator (see the module
docstring): `deg_E(𝔞) = deg_F(𝔞_E) / ∑_{v ∈ E} [F_v : ℚ_{v_ℚ}]`. -/
noncomputable def degE (E : Finset (Valuations F)) (a : ADiv F) : ℝ :=
  degF (ADiv.restrict E a) / ∑ v ∈ E, (localDeg v : ℝ)

omit [NumberField F] in
theorem ADiv.restrict_add (E : Finset (Valuations F)) (a b : ADiv F) :
    ADiv.restrict E (a + b) = ADiv.restrict E a + ADiv.restrict E b := by
  classical
  simp only [ADiv.restrict]
  exact Finsupp.filter_add

theorem degE_add (E : Finset (Valuations F)) (a b : ADiv F) :
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

theorem degE_nonneg {E : Finset (Valuations F)} {a : ADiv F} (h : a.Effective) :
    0 ≤ degE E a :=
  div_nonneg (degF_nonneg (ADiv.restrict_effective h))
    (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)

/-- When the local degrees over `E` sum to `[F : ℚ]` (as they do when `E` is the set of all
valuations over a single `v_ℚ`), `deg_E(𝔞)` is the normalized degree of `𝔞_E`. -/
theorem degE_eq_normalizedDeg {E : Finset (Valuations F)} (a : ADiv F)
    (hE : ∑ v ∈ E, (localDeg v : ℝ) = Module.finrank ℚ F) :
    degE E a = normalizedDeg (ADiv.restrict E a) := by
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

/-- **Unconditional instance.** For `E` the set of all archimedean valuations,
`deg_E(𝔞) = deg(𝔞_E)`. -/
theorem degE_arc_eq_normalizedDeg (a : ADiv F) :
    degE (arcValuations F) a = normalizedDeg (ADiv.restrict (arcValuations F) a) :=
  degE_eq_normalizedDeg a sum_localDeg_arc

/-- **The scaling fact behind the invariance `deg_{E|K}(𝔞|_K) = deg_E(𝔞)`.** Passing to a
finite extension of degree `κ` multiplies `deg_F(𝔞_E)` by `κ` and `∑_{v ∈ E} [F_v : ℚ_{v_ℚ}]` by
`κ`; the quotient is unchanged. With the normalized degree in the numerator, the numerator would
be unchanged while the denominator is multiplied by `κ`, and the quotient would change by
`1/κ` (`degE_ratio_normalized`). -/
theorem degE_ratio_invariant {N S κ : ℝ} (hκ : κ ≠ 0) : (κ * N) / (κ * S) = N / S :=
  mul_div_mul_left N S hκ

theorem degE_ratio_normalized {N S κ : ℝ} (hκ : κ ≠ 0) : N / (κ * S) = (1 / κ) * (N / S) := by
  field_simp

end IUT.PaperIV
