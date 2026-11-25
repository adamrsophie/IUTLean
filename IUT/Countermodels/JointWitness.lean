import Mathlib

/-!
# Countermodels: separate witnesses without a common realization

Source context: Mochizuki, *Inter-universal Teichmüller Theory III*, Step (iii) of the proof of
Corollary 3.12, page 176, read for this file: it is "of crucial importance" to relate the unit
portion and the value group portion of the Θ×μ_LGP-links simultaneously, via a single link,
because relating them via different links runs into the non-commutativity of the
log-theta-lattice. Also Step (i), page 175 (the link as a unit portion and a value group
portion), and Theorem 3.11 (i), (ii), pages 153 to 157. No formula of the papers is
transcribed here.

**None of the statements below is a counterexample to a statement of the IUT papers.** They
refute the simplified abstraction "if a transport map compatible with condition `P` exists, and
a transport map compatible with condition `Q` exists, then a transport map compatible with both
exists". `IUT.Countermodels.separate_witnesses_no_joint` in `Basic.lean` gives the bare logical
form; here the conditions are natural compatibility conditions on transport maps.

The positive statement `joint_witness_of_product` records when the abstraction is valid: when
the candidate transports form a product and each condition constrains a different factor. This
is the situation of a poly-isomorphism that is a product of a unit portion and a value group
portion with independent conditions on the two portions, which page 176 is careful to keep
inside a single link.
-/

namespace IUT.Countermodels.Joint

/-! ## Multiplicative automorphisms of `ZMod 7` with prescribed values -/

/-- The automorphism `x ↦ x^5` of the multiplicative monoid of `ZMod 7`. It is its own inverse
because `x^25 = x` for every `x` in `ZMod 7`. -/
def pow5 : ZMod 7 ≃* ZMod 7 where
  toFun x := x ^ 5
  invFun x := x ^ 5
  left_inv := by decide
  right_inv := by decide
  map_mul' x y := mul_pow x y 5

/-- **Countermodel with structure.** Among automorphisms of the multiplicative monoid of the
field `ZMod 7`, the condition "fixes the generator `3`" is satisfiable (by the identity) and the
condition "sends `2` to `4`" is satisfiable (by `x ↦ x^5`), but no automorphism satisfies both:
`2 = 3²`, so fixing `3` forces `2 ↦ 2`.

Read the two conditions as two Kummer-type compatibilities of one transport map, each imposed on
a different element. Each one separately can be met; jointly they cannot, because the elements
are related by the structure that the transport map must respect. -/
theorem zmod7_separate_not_joint :
    (∃ f : ZMod 7 ≃* ZMod 7, f 3 = 3) ∧ (∃ f : ZMod 7 ≃* ZMod 7, f 2 = 4) ∧
      ¬ ∃ f : ZMod 7 ≃* ZMod 7, f 3 = 3 ∧ f 2 = 4 := by
  refine ⟨⟨MulEquiv.refl _, rfl⟩, ⟨pow5, by decide⟩, ?_⟩
  rintro ⟨f, h3, h2⟩
  have : f 2 = f 3 * f 3 := by
    rw [← map_mul]
    rfl
  rw [h2, h3] at this
  exact absurd this (by decide)

/-! ## Ordered linear transports of the real line -/

/-- **Countermodel with real numbers.** Among ordered linear self-maps `x ↦ c x` (`c > 0`) of the
real line, the normalization condition "`1 ↦ 1`" is satisfiable, and for given `θ, q > 0` the
pilot condition "`θ ↦ q`" is satisfiable, but both hold for one map only if `θ = q`.

This is the shape of the transport between copies of `ℝ` discussed in
`IUT.Audit.ScholzeStix.Diagram`: a single positive scalar cannot at once respect a fixed
normalization and send one prescribed real number to a different one. -/
theorem linear_separate_not_joint {θ q : ℝ} (hθ : 0 < θ) (hq : 0 < q) :
    (∃ c : ℝ, 0 < c ∧ c * 1 = 1) ∧ (∃ c : ℝ, 0 < c ∧ c * θ = q) ∧
      ((∃ c : ℝ, 0 < c ∧ c * 1 = 1 ∧ c * θ = q) ↔ θ = q) := by
  refine ⟨⟨1, one_pos, mul_one 1⟩, ⟨q / θ, div_pos hq hθ, div_mul_cancel₀ q hθ.ne'⟩, ?_⟩
  constructor
  · rintro ⟨c, -, h1, h2⟩
    rw [mul_one] at h1
    rw [h1, one_mul] at h2
    exact h2
  · rintro rfl
    exact ⟨1, one_pos, mul_one 1, one_mul θ⟩

/-! ## The positive statement -/

/-- **Positive statement.** If the candidate transports form a product `A × B` and each
condition constrains a different factor, separate witnesses do combine into a joint one. So
conditions on the unit portion and on the value group portion of one poly-isomorphism can be
met independently, provided they really constrain independent portions. The countermodels above
fail exactly this independence. -/
theorem joint_witness_of_product {A B : Type*} (P : A → Prop) (Q : B → Prop)
    (hP : ∃ a, P a) (hQ : ∃ b, Q b) : ∃ x : A × B, P x.1 ∧ Q x.2 := by
  obtain ⟨a, ha⟩ := hP
  obtain ⟨b, hb⟩ := hQ
  exact ⟨(a, b), ha, hb⟩

end IUT.Countermodels.Joint
