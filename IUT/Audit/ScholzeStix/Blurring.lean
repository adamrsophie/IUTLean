import Mathlib
import IUT.Audit.ScholzeStix.Section1_3
import IUT.Audit.ScholzeStix.Diagram

/-!
# Scholze–Stix, end of Section 2.2: the size of the "blurring"

Source: P. Scholze and J. Stix, *Why abc is still a conjecture*, manuscript dated July 16,
2018, Section 1.3 (page 4, displays (1.5), (1.6)) and the last paragraphs of Section 2.2
(page 10). Read in full; the formulas were checked against the rendered pages 4 and 10.

**Whose argument.** Scholze and Stix report that Mochizuki "claimed that up to the
'blurring' given by certain indeterminacies the diagram does commute", and reply that "this
statement means that the blurring must be by a factor of at least `O(ℓ²)` rendering the
inequality thus obtained useless". They do not spell out the computation. This file makes the
two arithmetic facts behind that sentence precise, under the hypothesis (Lin) of
`IUT.Audit.ScholzeStix.Diagram` (every identification of copies of `ℝ` is multiplication by a
positive scalar), which Mochizuki rejects (comments on the 2018-08 version, item (C14)).

1. A cycle with one edge carrying the scalar `s` and all other edges canonical closes up to a
   factor in `[1/B, B]` only if `s ≤ B` and `1/B ≤ s` (`blur_bound`). For the averaged scalar
   `(1/ℓ*) ∑_{j ≤ ℓ*} j² = ℓ(ℓ + 1)/12` (`avgSq_eq`) this forces `B ≥ ℓ(ℓ + 1)/12`.
2. The average (1.5) with the factor `j²` and the average (1.6) without it differ exactly by
   multiplying the `deg(q_E)` term by that same average `ℓ(ℓ + 1)/12`
   (`withSquares_eq_withoutSquares_scaled`). So a blurring by a factor of size
   `ℓ(ℓ + 1)/12` on the `q` side is exactly the difference between (1.5), whose consequence
   is the bound of Claim 6, and (1.6), whose consequence is `0 ≤ d(P)`
   (`IUT.Audit.ScholzeStix.consequence_without_squares`).

**What this file is not.** It does not formalize Mochizuki's notion of indeterminacy or of a
"blurred" diagram, and it does not show that the indeterminacies (Ind1), (Ind2), (Ind3) act on
any copy of `ℝ` by a scalar. Under (Lin) it measures how large such a scalar would have to be.
It does not settle the dispute.
-/

namespace IUT.Audit.ScholzeStix

/-- A cycle of identifications closes up to a "blurring" by the factor `B`: the product of
its scalars lies in `[1/B, B]`. -/
def ConsistentUpTo (B : ℝ) (cycle : List LinIdent) : Prop :=
  1 / B ≤ (cycle.map (·.scalar)).prod ∧ (cycle.map (·.scalar)).prod ≤ B

/-- `ConsistentUpTo 1` is the same as `Consistent`. -/
theorem consistentUpTo_one_iff (cycle : List LinIdent) :
    ConsistentUpTo 1 cycle ↔ Consistent cycle := by
  simp only [ConsistentUpTo, Consistent, div_one]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

/-- One edge with scalar `s`, all others canonical: the cycle closes up to the factor `B`
exactly when `1/B ≤ s ≤ B`. -/
theorem blur_bound (s : LinIdent) (n : ℕ) (B : ℝ) :
    ConsistentUpTo B (s :: List.replicate n LinIdent.canonical) ↔ 1 / B ≤ s.scalar ∧ s.scalar ≤ B := by
  simp [ConsistentUpTo, LinIdent.canonical]

/-- The average of `j²` over `j = 1, …, ℓ*`. -/
noncomputable def avgSq (lh : ℕ) : ℝ := (1 / (lh : ℝ)) * ∑ j ∈ Finset.Icc 1 lh, (j : ℝ) ^ 2

private theorem sum_sq' (k : ℕ) :
    ∑ m ∈ Finset.Icc 1 k, (m : ℝ) ^ 2 = k * (k + 1) * (2 * k + 1) / 6 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; push_cast; ring

/-- With `ℓ = 2ℓ* + 1`, the average of `j²` is `ℓ(ℓ + 1)/12`. -/
theorem avgSq_eq {lh : ℕ} (hlh : 1 ≤ lh) {l : ℝ} (hl : l = 2 * lh + 1) :
    avgSq lh = l * (l + 1) / 12 := by
  have h0 : (lh : ℝ) ≠ 0 := by positivity
  unfold avgSq; rw [sum_sq', hl]; field_simp; ring

/-- Under (Lin), if the averaged scalar `ℓ(ℓ + 1)/12` sits on one edge and the cycle closes up
to the factor `B`, then `B ≥ ℓ(ℓ + 1)/12`: Scholze and Stix's "factor of at least `O(ℓ²)`". -/
theorem blur_ge_avgSq {lh : ℕ} (hlh : 1 ≤ lh) {l : ℝ} (hl : l = 2 * lh + 1) (n : ℕ) (B : ℝ)
    (hpos : 0 < avgSq lh)
    (h : ConsistentUpTo B (⟨avgSq lh, hpos⟩ :: List.replicate n LinIdent.canonical)) :
    l * (l + 1) / 12 ≤ B := by
  rw [← avgSq_eq hlh hl]; exact ((blur_bound _ n B).mp h).2

/-- The `j`-th summand form of (1.5) and (1.6) differ only in the `q` term, and after averaging
the `q` term of (1.5) is the `q` term of (1.6) multiplied by `avgSq ℓ*`:
`thetaWithSquares = (ℓ* + 1)/2 · d − avgSq ℓ* · qE/(2ℓ)` and
`thetaWithoutSquares = (ℓ* + 1)/2 · d − qE/(2ℓ)`. -/
theorem withSquares_eq_withoutSquares_scaled {lh : ℕ} (hlh : 1 ≤ lh) (l d qE : ℝ) :
    thetaWithSquares lh l d qE = ((lh : ℝ) + 1) / 2 * d - avgSq lh * (qE / (2 * l)) ∧
      thetaWithoutSquares lh l d qE = ((lh : ℝ) + 1) / 2 * d - 1 * (qE / (2 * l)) := by
  have h0 : (lh : ℝ) ≠ 0 := by positivity
  refine ⟨?_, by rw [display_1_6 hlh, one_mul]⟩
  unfold thetaWithSquares avgSq
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  have hid : ∑ m ∈ Finset.Icc 1 lh, (m : ℝ) = lh * (lh + 1) / 2 := by
    clear h0
    induction lh with
    | zero => simp
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · rw [Finset.sum_Icc_succ_top (by omega), ih hk]; push_cast; ring
  rw [hid]; field_simp

end IUT.Audit.ScholzeStix
