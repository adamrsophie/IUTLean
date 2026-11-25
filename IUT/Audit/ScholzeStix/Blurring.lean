import Mathlib
import IUT.Audit.ScholzeStix.Section1_3
import IUT.Audit.ScholzeStix.Diagram

/-!
# Scholze–Stix, end of Section 2.2: the size of the "blurring"

Source: P. Scholze and J. Stix, *Why abc is still a conjecture*, manuscript dated July 16,
2018, Section 1.3 (page 4, displays (1.5), (1.6)) and the last paragraphs of Section 2.2
(page 10). Read in full; the formulas were checked against the rendered pages 4 and 10.
Also S. Mochizuki, *Comments on the Manuscript (2018-08 Version) by Scholze–Stix*, September
2018, item (C14), page 4, read for this file in the extracted text.

**Whose argument.** Scholze and Stix report that Mochizuki "claimed that up to the
'blurring' given by certain indeterminacies the diagram does commute", and reply that "this
statement means that the blurring must be by a factor of at least `O(ℓ²)` rendering the
inequality thus obtained useless" (page 10). They do not spell out the computation.

**Three claims kept apart.**

1. *Arithmetic of the average (proved here, no hypothesis).* With `ℓ = 2ℓ* + 1`, the average
   `(1/ℓ*) ∑_{j ≤ ℓ*} j²` equals `ℓ(ℓ + 1)/12` (`avgSq_eq`), and the average (1.5) with the
   factor `j²` differs from the average (1.6) without it exactly by multiplying the
   `deg(q_E)` term by that average (`withSquares_eq_withoutSquares_scaled`).
2. *The hypothesis (Lin) (assumed here, disputed).* Every identification of two copies of `ℝ`
   in the diagram of Section 2.2 is multiplication by a positive scalar; this is the
   structure `IUT.Audit.ScholzeStix.LinIdent`. A "blurring by the factor `B`" is modeled
   by the choice `ConsistentUpTo B`: the product of the scalars around the cycle lies in
   `[1/B, B]`. Neither (Lin) nor this tolerance is derived from the papers. Under them,
   `consistentUpTo_avgSq_iff` evaluates the condition for a cycle carrying the averaged scalar
   on one edge: it holds exactly when `1/B ≤ ℓ(ℓ + 1)/12 ≤ B`. The bound `ℓ(ℓ + 1)/12 ≤ B` is
   therefore the hypothesis `ConsistentUpTo B` itself, after the product of the scalars and
   the average have been computed; it is not derived from anything else.
3. *Mochizuki's objection (not modeled here).* In his comments on the 2018-08 version, item
   (C14), page 4, Mochizuki states that linear relations do exist between the copies of `ℝ`
   arising via the Θ-link from the prime strips, but that the relation between log-volumes of
   regions subject to indeterminacies and regions not subject to them is "highly non-linear";
   he refers to his report, items (MlLV), (LVEx), (DsInd). The example (LVEx)
   (`IUT.Audit.MochizukiResponses.not_linear`) is a nonlinear example in the plane; it is not
   a construction of the actual comparison of IUT III, Corollary 3.12.

**What this file is not.** It does not formalize Mochizuki's notion of indeterminacy or of a
"blurred" diagram, and it does not show that the indeterminacies (Ind1), (Ind2), (Ind3) act on
any copy of `ℝ` by a scalar. Whether a blurring of size `ℓ(ℓ + 1)/12` makes the inequality of
Corollary 3.12 useless, as Scholze and Stix assert, is a quantitative claim about how such a
blurring would enter (1.4); this file does not supply that computation. It does not settle
the dispute.
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

/-- Under (Lin) and the tolerance model `ConsistentUpTo`: a cycle whose one edge carries the
averaged scalar `avgSq ℓ*` and whose other edges are canonical closes up to the factor `B`
exactly when `1/B ≤ ℓ(ℓ + 1)/12 ≤ B`. This is an evaluation of the hypothesis
`ConsistentUpTo B`, not a derivation of a lower bound on `B` from other premises. -/
theorem consistentUpTo_avgSq_iff {lh : ℕ} (hlh : 1 ≤ lh) {l : ℝ} (hl : l = 2 * lh + 1) (n : ℕ)
    (B : ℝ) (hpos : 0 < avgSq lh) :
    ConsistentUpTo B (⟨avgSq lh, hpos⟩ :: List.replicate n LinIdent.canonical) ↔
      1 / B ≤ l * (l + 1) / 12 ∧ l * (l + 1) / 12 ≤ B := by
  rw [← avgSq_eq hlh hl]; exact blur_bound _ n B

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
