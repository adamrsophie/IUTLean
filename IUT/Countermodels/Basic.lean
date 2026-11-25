import Mathlib

/-!
# Countermodels to simplified abstractions

Each statement here is a small, fully checked example showing that some general principle
fails. **None of them is a counterexample to a statement of the IUT papers.** They refute
abstractions: principles that an argument might be tempted to use and that are false without
further hypotheses. In the classification of the project they are all of the kind
"counterexample to a simplified abstraction". For each one the docstring says what the
example satisfies and which question about the papers it bears on.

Where a principle of the same flavor is true, the positive statement is proved next to the
countermodel, so that legitimate identifications are not ruled out by accident.
-/

namespace IUT.Countermodels

/-! ## Multiplicative structure does not determine additive structure -/

/-- On the field `ZMod 5`, cubing is a bijection that preserves `0`, `1` and multiplication
but not addition. So an isomorphism of multiplicative monoids need not be a ring
isomorphism: data that keeps only the multiplicative structure of a ring does not determine
its additive structure.

Bears on: IUT III distinguishes links that preserve multiplicative data only (the Θ-link)
from ring isomorphisms. The example shows the distinction is not vacuous already for finite
fields. It says nothing about whether additive structure can be *reconstructed* from richer
data such as a Galois action. -/
theorem mul_iso_not_additive :
    ∃ f : ZMod 5 → ZMod 5, Function.Bijective f ∧ f 0 = 0 ∧ f 1 = 1 ∧
      (∀ x y, f (x * y) = f x * f y) ∧ ¬ ∀ x y, f (x + y) = f x + f y := by
  refine ⟨fun x => x ^ 3, ?_, by decide, by decide, by decide, by decide⟩
  exact ⟨by decide, by decide⟩

/-! ## Separate witnesses and a joint witness -/

/-- Two existence statements, each true, with no common witness. Existence of an object
compatible with condition `P` and existence of an object compatible with condition `Q` do not
give one object compatible with both.

Bears on: the simultaneous validity of several compatibility conditions in IUT III,
Theorem 3.11, must be proved as a joint statement. It cannot be inferred from the separate
ones. -/
theorem separate_witnesses_no_joint :
    ∃ P Q : Bool → Prop, (∃ x, P x) ∧ (∃ x, Q x) ∧ ¬ ∃ x, P x ∧ Q x :=
  ⟨fun x => x = true, fun x => x = false, ⟨true, rfl⟩, ⟨false, rfl⟩,
    by rintro ⟨x, h1, h2⟩; rw [h1] at h2; exact Bool.noConfusion h2⟩

/-! ## Indeterminacies: separate and combined -/

/-- The positive statement: a quantity invariant under each of two transformations is
invariant under their composite. Invariance under (Ind1) and under (Ind2) separately does
give invariance under the combined action, for a single-valued quantity. -/
theorem invariant_comp {α β : Type*} (F : α → β) (g h : α → α)
    (hg : ∀ x, F (g x) = F x) (hh : ∀ x, F (h x) = F x) : ∀ x, F (g (h x)) = F x :=
  fun x => (hg (h x)).trans (hh x)

/-- The countermodel: the union of the orbits of a point under two transformations taken
separately can be strictly smaller than its orbit under the group they generate. On `Fin 3`
with the transpositions `(0 1)` and `(1 2)`, the point `0` has separate orbits `{0, 1}` and
`{0}`, while the composite `(1 2) ∘ (0 1)` sends `0` to `2`.

Bears on: "the union of the possible images" in IUT III, Corollary 3.12, is taken under
(Ind1), (Ind2), (Ind3) acting together. A region that contains the images under each
indeterminacy separately need not contain the images under their combination, so a volume
bound must be established for the combined action. -/
theorem separate_orbits_ne_joint_orbit :
    let g : Equiv.Perm (Fin 3) := Equiv.swap 0 1
    let h : Equiv.Perm (Fin 3) := Equiv.swap 1 2
    (h (g 0) ∉ ({0, g 0, h 0} : Finset (Fin 3))) := by
  decide

/-! ## Hulls and transport -/

/-- The interval hull of a finite set of `Fin 3`: all points between its least and greatest
elements. A stand-in for any hull operation defined by an order or a ring structure. -/
def intervalHull (s : Finset (Fin 3)) : Finset (Fin 3) :=
  Finset.univ.filter fun x => (∃ a ∈ s, a ≤ x) ∧ (∃ b ∈ s, x ≤ b)

/-- Hull formation does not commute with transport along a bijection that does not respect
the structure defining the hull. With `s = {0, 2}` and `σ = (1 2)`: the hull of `σ(s) = {0, 1}`
is `{0, 1}`, while `σ` of the hull of `s` is everything.

Bears on: in Corollary 3.12 the holomorphic hull is formed relative to one arithmetic
holomorphic structure (labeled `1, ∘`), after transporting data that originates in another.
The order of "transport" and "form the hull" matters, and the proof must say which is used. -/
theorem hull_transport_not_commute :
    let σ : Equiv.Perm (Fin 3) := Equiv.swap 1 2
    let s : Finset (Fin 3) := {0, 2}
    intervalHull (s.map σ.toEmbedding) ≠ (intervalHull s).map σ.toEmbedding := by
  decide

/-! ## Isomorphisms and normalized volumes -/

/-- Doubling is an automorphism of the additive group `ℝ`, and it sends the unit interval to
an interval of twice the length. An isomorphism of topological groups does not preserve a
chosen normalization of Haar measure.

Bears on: log-volumes in IUT III and IV are normalized. Transporting a volume along an
isomorphism that preserves only a weaker structure requires a separate proof that the
normalization is preserved. -/
theorem additive_iso_changes_volume :
    (∀ x y : ℝ, 2 * (x + y) = 2 * x + 2 * y) ∧
      MeasureTheory.volume (Set.Icc (2 * 0 : ℝ) (2 * 1)) ≠ MeasureTheory.volume (Set.Icc (0 : ℝ) 1) := by
  refine ⟨fun x y => by ring, ?_⟩
  rw [Real.volume_Icc, Real.volume_Icc]
  norm_num

/-- The corresponding statement for log-volumes: rescaling a measure by `c > 0` shifts every
log-volume by `log c`. Two normalizations give comparable log-volumes only after the shift
is accounted for. -/
theorem log_volume_shift {c μ : ℝ} (hc : 0 < c) (hμ : 0 < μ) :
    Real.log (c * μ) = Real.log c + Real.log μ :=
  Real.log_mul hc.ne' hμ.ne'

end IUT.Countermodels
