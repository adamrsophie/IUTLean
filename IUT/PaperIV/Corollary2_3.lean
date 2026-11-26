import Mathlib

/-!
# IUT IV, Corollary 2.3: the bounded discrepancy logic of the proof

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Corollary 2.3, its proof, and
Remark 2.3.1 (ii), pages 54 and 55 of the April 2020 manuscript, read from the extracted text
and from the rendered pages 54 and 55. The bounded discrepancy relations are those of [GenEll],
Definition 1.2 (ii), with the correction of Remark 2.3.1 (ii): `α ≲ β` on `F` means that there
is a constant `C` with `α(x) - β(x) ≤ C` for all `x ∈ F`.

This file is not a formalization of Corollary 2.3. The proof of the corollary has two parts:

1. By [GenEll], Theorem 2.1 ((ii) implies (i)), it suffices to prove the inequality
   `ht_{ω_X(D)} ≲ (1 + ε)·(log-diff_X + log-cond_D)` on `K_V ∩ U_X(ℚ̄)^{≤d}` for the `λ`-line
   `X = ℙ¹`, `D = {0, 1, ∞}` and a compactly bounded `K_V` as in Corollary 2.2. That reduction
   is an external theorem and is not formalized here.
2. On `K_V ∩ U_X(ℚ̄)^{≤d}`, the inequality follows from Corollary 2.2 (i), (ii) (condition (C2))
   and (iii). This file checks only the logical form of that step, as an abstract lemma about
   real functions on an arbitrary set `S` (`cor2_3_on_KV`): an equality of bounded discrepancy
   classes, a bound outside a finite exceptional set, a bound on a further function outside
   that set and a nonnegativity condition give an inequality of bounded discrepancy classes on
   all of `S`.

Nothing here refers to curves, divisors, points of bounded degree, heights, log-differents or
log-conductors: these are arbitrary real functions on an arbitrary type, and the lemma holds for
every `S`, including `S = ∅`. It says nothing about `K_V` unless the hypotheses are established
for the actual functions, which requires Corollary 2.2 and is not done here. Corollary 2.3 itself
is not stated in Lean; the form to which its proof reduces it (page 55) is stated as an open
proposition in `IUT/Applications/CompactlyBounded.lean` (`iutIVCor2_3ReducedFormStatement`).
-/

namespace IUT.PaperIV.Corollary2_3

variable {α : Type*}

/-- `f ≲ g` on `S` ([GenEll], Definition 1.2 (ii), as corrected by IUT IV, Remark 2.3.1 (ii)):
there is a constant `C` with `f(x) - g(x) ≤ C` for every `x ∈ S`. -/
def BDle (S : Set α) (f g : α → ℝ) : Prop := ∃ C : ℝ, ∀ x ∈ S, f x - g x ≤ C

/-- `f ≈ g` on `S`: there is a constant `C` with `|f(x) - g(x)| ≤ C` for every `x ∈ S`. -/
def BDeq (S : Set α) (f g : α → ℝ) : Prop := ∃ C : ℝ, ∀ x ∈ S, |f x - g x| ≤ C

theorem BDeq.le {S : Set α} {f g : α → ℝ} (h : BDeq S f g) : BDle S f g := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun x hx => le_trans (le_abs_self _) (hC x hx)⟩

theorem BDle.trans {S : Set α} {f g k : α → ℝ} (h1 : BDle S f g) (h2 : BDle S g k) :
    BDle S f k := by
  obtain ⟨C1, h1⟩ := h1
  obtain ⟨C2, h2⟩ := h2
  exact ⟨C1 + C2, fun x hx => by linarith [h1 x hx, h2 x hx]⟩

/-- A bound that holds outside a finite exceptional set gives an inequality of bounded
discrepancy classes on the whole set. -/
theorem BDle_of_finite_exceptions {S : Set α} (Exc : Finset α) {f g : α → ℝ} (C : ℝ)
    (h : ∀ x ∈ S, x ∉ Exc → f x - g x ≤ C) : BDle S f g := by
  refine ⟨max C 0 + ∑ y ∈ Exc, |f y - g y|, fun x hx => ?_⟩
  have hnn : 0 ≤ ∑ y ∈ Exc, |f y - g y| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hm : C ≤ max C 0 := le_max_left _ _
  have hm0 : 0 ≤ max C 0 := le_max_right _ _
  by_cases hxE : x ∈ Exc
  · have h1 : |f x - g x| ≤ ∑ y ∈ Exc, |f y - g y| :=
      Finset.single_le_sum (f := fun y => |f y - g y|) (fun _ _ => abs_nonneg _) hxE
    linarith [le_abs_self (f x - g x)]
  · linarith [h x hx hxE]

/-- **Abstract form of the step of the proof of Corollary 2.3 on `K_V ∩ U_X(ℚ̄)^{≤d}`**
(page 55). This is a lemma about arbitrary real functions on an arbitrary set `S`; it holds for
every `S`, so it carries information about `K_V` only once its hypotheses are proved for the
actual functions. In the intended application `S` is the set of points, `ht` the height
`ht_{ω_X(D)}`, `H` the function `log(𝔮^∀)`, `Λ` the function `log-diff_X + log-cond_D`, and `εE`
the invariant `ε_E` of Corollary 2.2 (ii). Assume:

* (Corollary 2.2 (i)) `ht ≈ (1/6)·H` on `S`;
* (Corollary 2.2 (ii), (C2)) `(1/6)·H(x) ≤ (1 + ε_E(x))·Λ(x) + C_K` for `x ∈ S` outside a
  finite set `Exc`;
* (Corollary 2.2 (iii)) `ε_E(x) ≤ ε` for `x ∈ S` outside `Exc`;
* `Λ ≥ 0` on `S` (log-differents and log-conductors are degrees of effective divisors).

Then `ht ≲ (1 + ε)·Λ` on `S`. -/
theorem cor2_3_on_KV {S : Set α} (Exc : Finset α) {ht H Λ εE : α → ℝ} {ε CK : ℝ}
    (hi : BDeq S ht (fun x => 1 / 6 * H x))
    (hC2 : ∀ x ∈ S, x ∉ Exc → 1 / 6 * H x ≤ (1 + εE x) * Λ x + CK)
    (hiii : ∀ x ∈ S, x ∉ Exc → εE x ≤ ε)
    (hΛ : ∀ x ∈ S, 0 ≤ Λ x) :
    BDle S ht (fun x => (1 + ε) * Λ x) := by
  refine hi.le.trans (BDle_of_finite_exceptions Exc CK fun x hx hxE => ?_)
  have h1 := hC2 x hx hxE
  have h2 : (1 + εE x) * Λ x ≤ (1 + ε) * Λ x :=
    mul_le_mul_of_nonneg_right (by linarith [hiii x hx hxE]) (hΛ x hx)
  linarith

/-- Corollary 2.2 (iii) is stated for `ε ≤ 1`. For `ε > 1` the inequality follows from the case
`ε = 1`, since `Λ ≥ 0`; this monotonicity is the following statement. -/
theorem BDle_mono_eps {S : Set α} {ht Λ : α → ℝ} {ε ε' : ℝ} (hεε' : ε ≤ ε')
    (hΛ : ∀ x ∈ S, 0 ≤ Λ x) (h : BDle S ht (fun x => (1 + ε) * Λ x)) :
    BDle S ht (fun x => (1 + ε') * Λ x) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun x hx => ?_⟩
  have := hC x hx
  have h2 : (1 + ε) * Λ x ≤ (1 + ε') * Λ x :=
    mul_le_mul_of_nonneg_right (by linarith) (hΛ x hx)
  simp only at this ⊢; linarith

end IUT.PaperIV.Corollary2_3
