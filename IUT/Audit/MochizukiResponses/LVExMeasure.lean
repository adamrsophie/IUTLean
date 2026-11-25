import Mathlib
import IUT.Audit.MochizukiResponses.LVEx

/-!
# Mochizuki's example (LVEx), with Lebesgue measure

Source: S. Mochizuki, *Report on Discussions, Held During the Period March 15 to 20, 2018,
Concerning Inter-universal Teichmüller Theory (IUTch)*, version dated February 2019, item
(LVEx), pages 24 to 26. The whole report was read; the definitions of `R_{a,b}`, `S_{a,b}`,
the displayed log-volumes, and the inequalities on `λ` were checked against the rendered
pages 24 and 25.

**Whose argument.** Mochizuki gives (LVEx), together with (MlLV), in reply to what he calls
the assertion (Lin) underlying Section 2.2 of the Scholze–Stix manuscript (comments on the
2018-08 version, item (C14)). The companion file `IUT.Audit.MochizukiResponses.LVEx` takes
the two areas `4a + 2b` and `4a + 4b` as given. This file derives them from the Lebesgue
measure `volume` on `ℝ × ℝ` and then checks the remaining assertions of (LVEx) about `λ` and
`ρ`.

**The example.** `σ (x, y) = (−x, y)`,
`R_{a,b} = {|x| ≤ 1, 0 ≤ |y| ≤ a} ∪ {0 ≤ x ≤ 1, a ≤ |y| ≤ a + b}`,
`S_{a,b} = R_{a,b} ∪ σ(R_{a,b})`, `a, b > 0`. The report states
`μ^log(S_{a,b}) = log(4a + 4b) > μ^log(R_{a,b}) = log(4a + 2b)`, and then takes `λ` with
`μ^log(S) > 0 > λ > μ^log(R)`, `ρ = μ^log(R) · λ⁻¹ > 1`, and the "gluing" `x ↦ x / ρ`
that sends `μ^log(R)` to `λ`.

**What is proved.** The two areas (`volume_R`, `volume_S`); `σ(S) = S` and `σ(R) ≠ R`; the
existence of admissible `(a, b, λ)`; `ρ > 1`; the gluing sends `μ^log(R)` to `λ`; the
inequality `μ^log(S) > λ`.

**Observation (assessment of this project).** In the example the inequality
`μ^log(S) > λ`, which the report describes as "entirely logically consistent" with the gluing,
is one of the hypotheses imposed on `λ` (`μ^log(S) > 0 > λ`); `logVolS_gt_lambda` is
immediate from them. The example shows that such `λ` exist and that the relation between
`μ^log(S)` and `μ^log(R)` is not linear. It does not show, and is not offered as showing, that
the situation of IUT III, Corollary 3.12, has this form. This file does not settle the dispute.
-/

namespace IUT.Audit.MochizukiResponses.LVExMeasure

open MeasureTheory Set

/-- The reflection `σ (x, y) = (−x, y)`. -/
def σ (p : ℝ × ℝ) : ℝ × ℝ := (-p.1, p.2)

theorem σ_σ (p : ℝ × ℝ) : σ (σ p) = p := by simp [σ]

/-- The set `{y | a ≤ |y| ≤ a + b}`. -/
def Y (a b : ℝ) : Set ℝ := {y | a ≤ |y| ∧ |y| ≤ a + b}

/-- `R_{a,b}`, as in the report. -/
def R (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | |p.1| ≤ 1 ∧ 0 ≤ |p.2| ∧ |p.2| ≤ a} ∪ {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ a ≤ |p.2| ∧ |p.2| ≤ a + b}

/-- `S_{a,b} = R_{a,b} ∪ σ(R_{a,b})`. -/
def S (a b : ℝ) : Set (ℝ × ℝ) := R a b ∪ σ '' R a b

theorem image_σ (A : Set (ℝ × ℝ)) : σ '' A = σ ⁻¹' A := by
  rw [Set.image_eq_preimage_of_inverse σ_σ σ_σ]

/-- `Y` as a union of two closed intervals. -/
theorem Y_eq {a b : ℝ} (ha : 0 < a) : Y a b = Icc (-(a + b)) (-a) ∪ Icc a (a + b) := by
  ext y
  simp only [Y, mem_ofPred_eq, mem_union, mem_Icc]
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]; constructor
    · intro h; right; exact h
    · rintro (h | h)
      · linarith [h.2]
      · exact h
  · rw [abs_of_neg hy]; constructor
    · intro h; left; constructor <;> linarith [h.1, h.2]
    · rintro (h | h)
      · constructor <;> linarith [h.1, h.2]
      · linarith [h.1]

theorem volume_Y {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    volume (Y a b) = ENNReal.ofReal (2 * b) := by
  rw [Y_eq ha, measure_union _ measurableSet_Icc, Real.volume_Icc, Real.volume_Icc,
    ← ENNReal.ofReal_add (by linarith) (by linarith)]
  · congr 1; ring
  · rw [Set.disjoint_left]
    intro y h1 h2
    simp only [mem_Icc] at h1 h2
    linarith [h1.2, h2.1]

/-- `S_{a,b}` is the rectangle `[−1, 1] × [−(a + b), a + b]`. -/
theorem S_eq {a b : ℝ} (hb : 0 < b) :
    S a b = Icc (-1) 1 ×ˢ Icc (-(a + b)) (a + b) := by
  ext ⟨x, y⟩
  simp only [S, image_σ, R, σ, mem_union, mem_preimage, mem_ofPred_eq, mem_prod, mem_Icc,
    abs_neg]
  constructor
  · rintro ((⟨h1, -, h2⟩ | ⟨h1, h2, -, h3⟩) | (⟨h1, -, h2⟩ | ⟨h1, h2, -, h3⟩))
    · exact ⟨abs_le.mp h1, abs_le.mp (h2.trans (by linarith))⟩
    · exact ⟨⟨by linarith, h2⟩, abs_le.mp h3⟩
    · exact ⟨abs_le.mp h1, abs_le.mp (h2.trans (by linarith))⟩
    · exact ⟨⟨by linarith, by linarith⟩, abs_le.mp h3⟩
  · rintro ⟨hx, hy⟩
    have hx' : |x| ≤ 1 := abs_le.mpr hx
    have hy' : |y| ≤ a + b := abs_le.mpr hy
    rcases le_or_gt (|y|) a with h | h
    · exact Or.inl (Or.inl ⟨hx', abs_nonneg _, h⟩)
    · rcases le_or_gt 0 x with h0 | h0
      · exact Or.inl (Or.inr ⟨h0, hx.2, h.le, hy'⟩)
      · exact Or.inr (Or.inr ⟨by linarith, by linarith [hx.1], h.le, hy'⟩)

/-- **The area of `S_{a,b}` is `4a + 4b`.** -/
theorem volume_S {a b : ℝ} (hb : 0 < b) :
    volume (S a b) = ENNReal.ofReal (4 * a + 4 * b) := by
  rw [S_eq hb, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; ring

/-- The two pieces of `R_{a,b}` as products. -/
theorem R_eq (a b : ℝ) :
    R a b = Icc (-1) 1 ×ˢ Icc (-a) a ∪ Icc 0 1 ×ˢ Y a b := by
  ext ⟨x, y⟩
  simp only [R, Y, mem_union, mem_ofPred_eq, mem_prod, mem_Icc, abs_nonneg, true_and]
  rw [abs_le, abs_le]
  simp only [and_assoc]

/-- **The area of `R_{a,b}` is `4a + 2b`.** The two pieces meet in the null set
`[0, 1] × {−a, a}`. -/
theorem volume_R {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    volume (R a b) = ENNReal.ofReal (4 * a + 2 * b) := by
  have hYm : MeasurableSet (Y a b) := by
    rw [Y_eq ha]; exact measurableSet_Icc.union measurableSet_Icc
  have hB : MeasurableSet (Icc (0 : ℝ) 1 ×ˢ Y a b) := measurableSet_Icc.prod hYm
  have hinter : volume (Icc (-1 : ℝ) 1 ×ˢ Icc (-a) a ∩ Icc (0 : ℝ) 1 ×ˢ Y a b) = 0 := by
    apply measure_mono_null (t := Icc (0 : ℝ) 1 ×ˢ ({-a, a} : Set ℝ))
    · rintro ⟨x, y⟩ ⟨⟨-, hy1⟩, ⟨hx, hy2⟩⟩
      refine ⟨hx, ?_⟩
      simp only [Y, mem_ofPred_eq, mem_Icc] at hy1 hy2
      have : |y| = a := le_antisymm (abs_le.mpr hy1) hy2.1
      rcases abs_eq ha.le |>.mp this with h | h
      · exact Or.inr h
      · exact Or.inl h
    · rw [Measure.volume_eq_prod, Measure.prod_prod]
      simp [(Set.toFinite ({-a, a} : Set ℝ)).measure_zero]
  have key := measure_union_add_inter (μ := volume) (Icc (-1 : ℝ) 1 ×ˢ Icc (-a) a) hB
  rw [hinter, add_zero, ← R_eq a b] at key
  rw [key, Measure.volume_eq_prod, Measure.prod_prod, Measure.prod_prod,
    Real.volume_Icc, Real.volume_Icc, Real.volume_Icc, volume_Y ha hb,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by nlinarith) (by nlinarith)]
  congr 1; ring

/-- `σ(S_{a,b}) = S_{a,b}`: the symmetrization is "defined over `W`". -/
theorem σ_S (a b : ℝ) : σ '' S a b = S a b := by
  rw [S, Set.image_union, Set.image_image]
  simp only [σ_σ, Set.image_id']
  exact Set.union_comm _ _

/-- `σ(R_{a,b}) ≠ R_{a,b}`: the point `(1, a + b)` lies in `R_{a,b}`, its image `(−1, a + b)`
does not. So `R_{a,b}` is "only defined over `V`". -/
theorem σ_R_ne {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : σ '' R a b ≠ R a b := by
  intro h
  have hmem : ((1 : ℝ), a + b) ∈ R a b := by
    right
    have hab : |a + b| = a + b := abs_of_pos (by linarith)
    exact ⟨by norm_num, le_rfl, by rw [hab]; linarith, by rw [hab]⟩
  have : σ (1, a + b) ∈ R a b := h ▸ Set.mem_image_of_mem σ hmem
  simp only [σ, R, mem_union, mem_ofPred_eq, abs_neg, abs_one] at this
  rcases this with ⟨-, -, h2⟩ | ⟨h1, -⟩
  · rw [abs_of_pos (by linarith)] at h2; linarith
  · linarith

/-- The log-volume `μ^log` (natural logarithm of the Lebesgue measure). -/
noncomputable def μlog (A : Set (ℝ × ℝ)) : ℝ := Real.log (volume A).toReal

/-- The log-volumes agree with those taken as given in `LVEx.lean`. -/
theorem μlog_R {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : μlog (R a b) = logVolR a b := by
  rw [μlog, volume_R ha hb, ENNReal.toReal_ofReal (by positivity), logVolR]

theorem μlog_S {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : μlog (S a b) = logVolS a b := by
  rw [μlog, volume_S hb, ENNReal.toReal_ofReal (by positivity), logVolS]

/-- The displayed inequality of (LVEx), now from Lebesgue measure:
`μ^log(S_{a,b}) > μ^log(R_{a,b})`. -/
theorem μlog_R_lt_S {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : μlog (R a b) < μlog (S a b) := by
  rw [μlog_R ha hb, μlog_S ha hb]; exact logVolR_lt_logVolS ha hb

/-- Admissible data exist: at `a = 1/8`, `b = 1/5` and `λ = −1/20`,
`μ^log(S) > 0 > λ > μ^log(R)`. -/
theorem admissible_exists :
    ∃ a b lam : ℝ, 0 < a ∧ 0 < b ∧ 0 < μlog (S a b) ∧ lam < 0 ∧ μlog (R a b) < lam := by
  refine ⟨1 / 8, 1 / 5, -1 / 20, by norm_num, by norm_num, ?_, by norm_num, ?_⟩
  · rw [μlog_S (by norm_num) (by norm_num), logVolS]; exact Real.log_pos (by norm_num)
  · rw [μlog_R (by norm_num) (by norm_num), logVolR]
    -- `log (9/10) ≤ 9/10 − 1 = −1/10 < −1/20`
    have := Real.log_le_sub_one_of_pos (x := 4 * (1 / 8) + 2 * (1 / 5)) (by norm_num)
    linarith

/-- With `μ^log(S) > 0 > λ > μ^log(R)`: `ρ = μ^log(R) · λ⁻¹ > 1`, the gluing `x ↦ x / ρ`
sends `μ^log(R)` to `λ`, and `μ^log(S) > λ`. -/
theorem gluing {mS mR lam : ℝ} (hS : 0 < mS) (hlam : lam < 0) (hR : mR < lam) :
    1 < mR * lam⁻¹ ∧ mR / (mR * lam⁻¹) = lam ∧ lam < mS := by
  have hmR : mR < 0 := hR.trans hlam
  refine ⟨?_, ?_, by linarith⟩
  · rw [← div_eq_mul_inv, one_lt_div_of_neg hlam]; exact hR
  · have := hmR.ne; field_simp

/-- The inequality `μ^log(S) > λ` is a consequence of the hypotheses on `λ` alone; it does not
use the gluing. -/
theorem logVolS_gt_lambda {mS lam : ℝ} (hS : 0 < mS) (hlam : lam < 0) : lam < mS := by linarith

end IUT.Audit.MochizukiResponses.LVExMeasure
