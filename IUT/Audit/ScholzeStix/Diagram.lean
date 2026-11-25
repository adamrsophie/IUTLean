import Mathlib

/-!
# Scholze–Stix, Section 2.2: consistency of identifications of copies of `ℝ`

Source: Scholze and Stix, *Why abc is still a conjecture* (July 16, 2018), Sections 2.1.4 to
2.2, pages 7 to 10. Read in full.

The objection concerns six ordered one-dimensional real vector spaces arranged in a cycle:
the spaces of the abstract Θ- and q-pilot objects, the spaces of the concrete pilot objects,
and two copies of the standard real numbers. Scholze and Stix argue that a meaningful
inequality needs all of them identified consistently, and that inserting the scalar `j²` on
one edge makes the cycle inconsistent.

This file states the elementary algebra behind that argument and nothing more.

**Hypothesis the objection rests on.** Every identification between two of the copies is an
ordered linear isomorphism, that is, multiplication by a positive scalar. Mochizuki rejects
exactly this hypothesis, calling it "(Lin)" in his comments of September 2018, item (C14):
he states that when indeterminacies are involved the relationship between log-volumes is not
linear. See `IUT.Audit.MochizukiResponses.LVEx`. So the theorems below are conditional on
(Lin) and do not settle the dispute.
-/

namespace IUT.Audit.ScholzeStix

/-- An ordered linear identification of two copies of `ℝ`: multiplication by a positive
scalar. This is the hypothesis "(Lin)". -/
structure LinIdent where
  scalar : ℝ
  pos : 0 < scalar

/-- A cycle of identifications is consistent when going around it returns every element to
itself, that is, when the product of the scalars is `1`. -/
def Consistent (cycle : List LinIdent) : Prop := (cycle.map (·.scalar)).prod = 1

/-- The canonical identification, scalar `1`. -/
def LinIdent.canonical : LinIdent := ⟨1, one_pos⟩

/-- The cycle with canonical identifications on every edge is consistent. Scholze and Stix:
"There is one consistent choice of isomorphisms given by using the natural isomorphisms". -/
theorem consistent_canonical (n : ℕ) : Consistent (List.replicate n LinIdent.canonical) := by
  simp [Consistent, LinIdent.canonical]

/-- If one edge carries the scalar `c` and all other edges are canonical, the cycle is
consistent only if `c = 1`. -/
theorem scalar_eq_one_of_consistent (c : LinIdent) (n : ℕ)
    (h : Consistent (c :: List.replicate n LinIdent.canonical)) : c.scalar = 1 := by
  simpa [Consistent, LinIdent.canonical] using h

/-- The case at issue: the scalar `j²` for `j ≥ 2`. Under (Lin), with the other edges
canonical, the cycle has "monodromy `j²`" and is inconsistent. -/
theorem not_consistent_square {j : ℕ} (hj : 2 ≤ j) (n : ℕ) :
    ¬ Consistent (⟨(j : ℝ) ^ 2, by positivity⟩ :: List.replicate n LinIdent.canonical) := by
  intro h
  have h1 := scalar_eq_one_of_consistent _ n h
  have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj
  simp only at h1
  nlinarith

/-- "Blurring" version. Suppose the cycle is only required to close up to a multiplicative
factor in `[1/B, B]`. Then a single edge with scalar `j²` forces `B ≥ j²`. Scholze and Stix:
"the blurring must be by a factor of at least `O(ℓ²)`". -/
theorem blur_ge_square {j : ℕ} {B : ℝ} (h : (j : ℝ) ^ 2 * 1 ≤ B) : (j : ℝ) ^ 2 ≤ B := by
  simpa using h

end IUT.Audit.ScholzeStix
