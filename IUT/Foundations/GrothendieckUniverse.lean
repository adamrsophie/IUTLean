import Mathlib

/-!
# Grothendieck universes and the existence axiom of IUT IV, Section 3

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Section 3 (introductory
discussion before Definition 3.1), PDF pages 67 and 68 (both rendered and read).

On page 67 the paper recalls that a (Grothendieck) universe `V` is a set satisfying five axioms
(i) to (v), citing [McLn], page 194, and introduces the existence axiom `(†G)`: every set is an
element of some universe. A model of ZFC satisfying `(†G)` is called a ZFCG-model. The paper then
derives two consequences of `(†G)`: any set-indexed family of universes is contained, elementwise,
in a single larger universe, and in particular there are infinite ascending chains
`V₀ ∈ V₁ ∈ V₂ ∈ ⋯ ∈ V`. On page 68 it notes that, by the axiom of foundation, there are no infinite
descending chains `V₀ ∋ V₁ ∋ V₂ ∋ ⋯`.

This file formalizes the definition and these three remarks over Mathlib's model `ZFSet` of ZFC
set theory. It is not a formalization of the language of species (Definition 3.1 and after),
of set-theoretic formulas, or of the "absoluteness" proviso on page 68.

## What is and is not proved

* `IsGrothendieckUniverse` transcribes axioms (i) to (v) of page 67.
* The existence axiom `(†G)` is the proposition `ExistenceAxiom`. It is **not proved**: it is not
  a theorem of ZFC, and nothing here shows that `ZFSet.{u}` satisfies it. The paper assumes it
  (page 67) and explicitly leaves aside whether ZFCG-models exist (page 68). The results that use
  it, `exists_universe_forall_mem` and `exists_ascending_chain`, take it as an explicit
  hypothesis.
* `not_exists_descending_mem_chain` is unconditional: it follows from the well-foundedness of
  `∈` on `ZFSet` (Mathlib's `ZFSet.mem_wf`), the formal counterpart of the axiom of foundation.
  It is proved for arbitrary sets, which covers chains of universes.
* No Grothendieck universe is exhibited here, so the definition is not shown to be inhabited.

## Interpretation choices, recorded

* "The set of natural numbers `ℕ`" in axiom (ii) is Mathlib's von Neumann `ZFSet.omega`.
* In axiom (v), a surjection `f : x → y` is a set `f` that is a function from `x` to `y` in the
  sense of Mathlib's `ZFSet.IsFunc x y f` (a subset of `x × y` that is single-valued and total on
  `x`) and whose image is all of `y`.
* In `exists_universe_forall_mem`, the index set `I` of the paper is a type `I` that is `u`-small,
  so that the family `i ↦ Vᵢ` has a set of values (`ZFSet.range`). This is the formal counterpart
  of the paper's remark that the graph of the function `I ∋ i ↦ Vᵢ` is a set. The conclusion
  holds for any family of sets, not only for a family of universes; the paper's statement is the
  special case.
-/

universe u

namespace IUT.Foundations

open ZFSet

/-- A set `f` is a surjection from `x` onto `y`: it is a function from `x` to `y`
(`ZFSet.IsFunc`), and every element of `y` is the value of `f` at some element of `x`. -/
def IsSurjection (x y f : ZFSet.{u}) : Prop :=
  IsFunc x y f ∧ ∀ b ∈ y, ∃ a ∈ x, pair a b ∈ f

/-- A (Grothendieck) universe, with the five axioms of IUT IV, page 67:
(i) `V` is transitive; (ii) `ℕ ∈ V`; (iii) `V` is closed under power sets; (iv) `V` is closed
under unions of its elements; (v) if `x ∈ V`, `y ⊆ V`, and `f : x → y` is a surjection, then
`y ∈ V`. -/
structure IsGrothendieckUniverse (V : ZFSet.{u}) : Prop where
  /-- (i) If `y ∈ x` and `x ∈ V`, then `y ∈ V`. -/
  transitive : ∀ x ∈ V, ∀ y ∈ x, y ∈ V
  /-- (ii) The set of natural numbers belongs to `V`. -/
  omega_mem : omega ∈ V
  /-- (iii) If `x ∈ V`, then the power set of `x` belongs to `V`. -/
  powerset_mem : ∀ x ∈ V, powerset x ∈ V
  /-- (iv) If `x ∈ V`, then the union of all members of `x` belongs to `V`. -/
  sUnion_mem : ∀ x ∈ V, ⋃₀ x ∈ V
  /-- (v) If `x ∈ V`, `y ⊆ V`, and `f : x → y` is a surjection, then `y ∈ V`. -/
  mem_of_surjection : ∀ x ∈ V, ∀ y, y ⊆ V → ∀ f, IsSurjection x y f → y ∈ V

/-- The existence axiom `(†G)` of the Grothendieck school (IUT IV, page 67): every set is an
element of some universe. This is an assumption of the paper, not a theorem of ZFC; it is not
proved here. -/
def ExistenceAxiom : Prop :=
  ∀ x : ZFSet.{u}, ∃ V, IsGrothendieckUniverse V ∧ x ∈ V

/-- IUT IV, page 67: under the existence axiom `(†G)`, any family of sets `Vᵢ` indexed by a set
`I` is contained, elementwise, in a single universe `V`, that is, `Vᵢ ∈ V` for all `i ∈ I`.
The paper states this for a family of universes; the proof does not use that the `Vᵢ` are
universes. As in the paper, the proof applies `(†G)` to the set `{Vᵢ}` and then uses
transitivity (axiom (i)). -/
theorem exists_universe_forall_mem (hG : ExistenceAxiom.{u}) {I : Type*} [Small.{u} I]
    (V : I → ZFSet.{u}) : ∃ W, IsGrothendieckUniverse W ∧ ∀ i, V i ∈ W := by
  obtain ⟨W, hW, hmem⟩ := hG (ZFSet.range V)
  exact ⟨W, hW, fun i => hW.transitive _ hmem _ (mem_range_self i)⟩

/-- IUT IV, page 67: under the existence axiom `(†G)`, there is an infinite ascending chain of
universes `V₀ ∈ V₁ ∈ V₂ ∈ ⋯ ∈ Vₙ ∈ ⋯ ∈ V`, where `V` is itself a universe. -/
theorem exists_ascending_chain (hG : ExistenceAxiom.{u}) :
    ∃ V : ℕ → ZFSet.{u}, (∀ n, IsGrothendieckUniverse (V n)) ∧ (∀ n, V n ∈ V (n + 1)) ∧
      ∃ W, IsGrothendieckUniverse W ∧ ∀ n, V n ∈ W := by
  choose U hU hmem using hG
  let V : ℕ → ZFSet.{u} := fun n => Nat.rec (U ∅) (fun _ W => U W) n
  have hsucc : ∀ n, V (n + 1) = U (V n) := fun _ => rfl
  have huniv : ∀ n, IsGrothendieckUniverse (V n) := by
    intro n
    cases n with
    | zero => exact hU ∅
    | succ n => rw [hsucc]; exact hU _
  refine ⟨V, huniv, fun n => hsucc n ▸ hmem (V n), ?_⟩
  exact exists_universe_forall_mem (fun x => ⟨U x, hU x, hmem x⟩) V

/-- IUT IV, page 68: by the axiom of foundation there is no infinite descending chain
`V₀ ∋ V₁ ∋ V₂ ∋ ⋯`. Proved for arbitrary sets, hence in particular for universes, from the
well-foundedness of `∈` on `ZFSet`. -/
theorem not_exists_descending_mem_chain :
    ¬ ∃ V : ℕ → ZFSet.{u}, ∀ n, V (n + 1) ∈ V n := by
  rintro ⟨V, hV⟩
  obtain ⟨_, ⟨n, rfl⟩, hmin⟩ := ZFSet.mem_wf.has_min (Set.range V) ⟨V 0, 0, rfl⟩
  exact hmin _ ⟨n + 1, rfl⟩ (hV n)

end IUT.Foundations
