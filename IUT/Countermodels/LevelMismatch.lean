import Mathlib

/-!
# Countermodels: an isomorphism at one level and invariants at another

Source context: Mochizuki, *Inter-universal Teichmüller Theory III*, read for this file from
the extracted text: Proposition 1.2 (iii), (v) (compatibility of log-links with log-volumes,
compactness of log-shells; pages 31 and 32), Proposition 3.9 (i) to (iv) (pages 115 to 117),
and Step (xii) of the proof of Corollary 3.12 (pages 185 and 186), where the
Θ×μ_LGP-link is said to preserve only isomorphism classes of objects of local Frobenioids,
so that one cannot tell an open submodule of a log-shell from its `p^N` multiple. No formula
of the papers is transcribed here.

**None of the statements below is a counterexample to a statement of the IUT papers.** Each
refutes the simplified abstraction "an isomorphism of one structure (an additive group, a
field) preserves an invariant defined with the help of further structure (a norm, a valuation,
an archimedean absolute value)". The papers state such compatibilities as separate
assertions (for instance Proposition 1.2 (iii) and Theorem 3.11 (ii) (a)), and the examples
show why they are separate.

Positive statement: `real_ringEquiv_isometry`. For `ℝ`, the field structure alone forces
every automorphism to be the identity, hence to preserve the absolute value.
-/

namespace IUT.Countermodels.Level

/-! ## An additive homeomorphism of `ℚ_p` that changes the norm -/

/-- Multiplication by `p` as an additive automorphism of `ℚ_p`. -/
noncomputable def mulP (p : ℕ) [Fact p.Prime] : ℚ_[p] ≃+ ℚ_[p] where
  toFun x := p * x
  invFun x := (p : ℚ_[p])⁻¹ * x
  left_inv x := by
    have : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    simp [this]
  right_inv x := by
    have : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    simp [this]
  map_add' x y := mul_add _ x y

/-- **Countermodel.** Multiplication by `p` is an automorphism of the additive topological group
`ℚ_p` (continuous with continuous inverse), and it maps the unit `1` of `ℤ_p` to `p`, which
lies in the maximal ideal: it multiplies every norm by `p⁻¹`. So an isomorphism of the additive
topological group does not preserve the `p`-adic norm, the valuation, or the integral structure
`ℤ_p`. It is analogous, in the simplest setting, to the indeterminacy "an open submodule versus
its `p^N` multiple" described in IUT III, Step (xii) of the proof of Corollary 3.12 (pages 185
and 186). -/
theorem mulP_countermodel (p : ℕ) [Fact p.Prime] :
    Continuous (mulP p) ∧ Continuous (mulP p).symm ∧
      (∀ x, ‖mulP p x‖ = (p : ℝ)⁻¹ * ‖x‖) ∧ ‖(1 : ℚ_[p])‖ = 1 ∧ ‖mulP p 1‖ < 1 := by
  refine ⟨continuous_const.mul continuous_id, continuous_const.mul continuous_id, ?_, norm_one,
    ?_⟩
  · intro x
    show ‖(p : ℚ_[p]) * x‖ = _
    rw [norm_mul, Padic.norm_p]
  · show ‖(p : ℚ_[p]) * 1‖ < 1
    rw [mul_one]
    exact Padic.norm_p_lt_one

/-! ## Isomorphic fields, isomorphic value groups, non-isomorphic valued fields -/

/-- **Countermodel.** The valued fields `(ℚ, v₂)` and `(ℚ, v₃)` have the same underlying field
and value groups `ℤ`, yet no field automorphism of `ℚ` carries one valuation to the other: any
ring automorphism fixes `2`, and `v₃(2) = 0 ≠ 1 = v₂(2)`. An isomorphism of fields does not
by itself carry one valuation to another; the valuation is extra structure that a link must be
shown to respect. -/
theorem no_ringEquiv_valuation_two_three :
    ¬ ∃ σ : ℚ ≃+* ℚ, ∀ x : ℚ, padicValRat 3 (σ x) = padicValRat 2 x := by
  rintro ⟨σ, hσ⟩
  have h := hσ 2
  rw [map_ofNat] at h
  have h2 : padicValRat 2 (2 : ℚ) = 1 := by
    have := padicValRat.self (p := 2) (by norm_num)
    exact_mod_cast this
  have h3 : padicValRat 3 (2 : ℚ) = 0 := by
    have : padicValRat 3 ((2 : ℕ) : ℚ) = 0 := by
      rw [padicValRat.of_nat]
      norm_num [multiplicity_eq_zero]
    exact_mod_cast this
  rw [h2, h3] at h
  exact absurd h (by norm_num)

/-! ## A ring automorphism that is not bounded for the archimedean absolute value -/

/-- The real embedding `a + b√2 ↦ a + b·√2` of `ℤ[√2]` into `ℝ`. -/
noncomputable def realEmb : ℤ√2 →+* ℝ :=
  Zsqrtd.lift ⟨Real.sqrt 2, by rw [Real.mul_self_sqrt (by norm_num)]; norm_num⟩

/-- The real embedding on coordinates: `realEmb (a + b√2) = a + b·√2`. -/
theorem realEmb_apply (a : ℤ√2) : realEmb a = a.re + a.im * Real.sqrt 2 :=
  Zsqrtd.lift_apply_apply _ a

/-- **Countermodel.** Conjugation `a + b√2 ↦ a − b√2` is a ring endomorphism of `ℤ[√2]`
(`starRingEnd`) and an involution, hence a ring automorphism, but it is unbounded on the elements whose real embedding has absolute value at
most `1`: the elements `(1 − √2)^n` are small, their conjugates `(1 + √2)^n` are arbitrarily
large. So an isomorphism of rings need not respect the archimedean absolute value induced by an
embedding, and transporting a region defined by an archimedean bound along it can produce an
unbounded region. Bears on the archimedean part of the log-volume compatibility of IUT III,
Proposition 1.2 (iii) (page 31), which the passage read asserts for the specific maps there;
the example shows that such a compatibility does not follow from ring structure alone in
general. Only unboundedness is proved here; discontinuity in the induced topology is not
formalized. -/
theorem conj_unbounded :
    Function.Involutive (starRingEnd (ℤ√2)) ∧ ∀ M : ℝ, ∃ x : ℤ√2, |realEmb x| ≤ 1 ∧ M < |realEmb (starRingEnd (ℤ√2) x)| := by
  refine ⟨fun x => star_star x, fun M => ?_⟩
  have hs : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs2 : Real.sqrt 2 < 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_gt M
  let u : ℤ√2 := ⟨1, 1⟩
  have hu : realEmb u = 1 + Real.sqrt 2 := by simp [realEmb_apply, u]
  have hu' : realEmb (starRingEnd (ℤ√2) u) = 1 - Real.sqrt 2 := by
    rw [starRingEnd_apply, Zsqrtd.star_mk, realEmb_apply]
    push_cast
    ring
  refine ⟨(starRingEnd (ℤ√2) u) ^ n, ?_, ?_⟩
  · rw [map_pow, hu', abs_pow]
    apply pow_le_one₀ (abs_nonneg _)
    rw [abs_le]
    constructor <;> linarith
  · rw [map_pow, map_pow, show starRingEnd (ℤ√2) (starRingEnd (ℤ√2) u) = u from star_star u, hu,
      abs_pow, abs_of_pos (by linarith)]
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ Real.sqrt 2 by linarith) n
    nlinarith

/-! ## The positive statement -/

/-- **Positive statement.** Every ring automorphism of `ℝ` is the identity, hence preserves the
absolute value: for `ℝ`, the archimedean structure is determined by the field structure. The
contrast with `conj_unbounded` is that `ℤ[√2]` carries two real embeddings, and the ring
structure does not single out one of them. -/
theorem real_ringEquiv_isometry (σ : ℝ ≃+* ℝ) (x : ℝ) : |σ x| = |x| := by
  have hx : (σ : ℝ →+* ℝ) x = RingHom.id ℝ x := by
    rw [Subsingleton.elim (σ : ℝ →+* ℝ) (RingHom.id ℝ)]
  simp only [RingEquiv.coe_toRingHom, RingHom.id_apply] at hx
  rw [hx]

end IUT.Countermodels.Level
