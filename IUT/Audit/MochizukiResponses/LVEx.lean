import Mathlib

/-!
# Mochizuki's example (LVEx): indeterminacies make log-volumes relate non-linearly

Sources: S. Mochizuki, *Report on Discussions, Held During the Period March 15 – 20, 2018,
Concerning Inter-universal Teichmüller Theory*, September 2018, item (LVEx), pages 24 and 25;
and *Comments on the Manuscript (2018-08 Version) by Scholze–Stix*, September 2018, item
(C14). The passage (LVEx) and the comments were read; the report was not read in full.

In `V = ℝ²` with the reflection `σ(x, y) = (−x, y)`, the example takes the region

`R_{a,b} = {|x| ≤ 1, |y| ≤ a} ∪ {0 ≤ x ≤ 1, a ≤ |y| ≤ a + b}`

and its symmetrization `S_{a,b} = R_{a,b} ∪ σ(R_{a,b})`, for `a, b > 0`. The report states
that their areas are `4a + 2b` and `4a + 4b`. This file takes those two areas as given (they
are not derived here from Lebesgue measure) and checks the claim made about them: the
log-volumes `log(4a + 2b)` and `log(4a + 4b)` are not related by a fixed linear map.

In the analogy of the report, `R` corresponds to the Θ-pilot in the Θ-holomorphic structure
and `S` to the holomorphic hull of its multiradial representation. The example shows that the
hypothesis "(Lin)" of the Scholze–Stix argument (see `IUT.Audit.ScholzeStix.Diagram`) can fail
for a hull under a group of indeterminacies. Whether the situation of IUT III, Corollary 3.12,
behaves like this example is not addressed by this file.
-/

namespace IUT.Audit.MochizukiResponses

/-- Log-volume of the region `R_{a,b}`, from the area `4a + 2b` stated in the report. -/
noncomputable def logVolR (a b : ℝ) : ℝ := Real.log (4 * a + 2 * b)

/-- Log-volume of the symmetrized region `S_{a,b}`, from the stated area `4a + 4b`. -/
noncomputable def logVolS (a b : ℝ) : ℝ := Real.log (4 * a + 4 * b)

/-- `μ^log(S_{a,b}) > μ^log(R_{a,b})`, as displayed in (LVEx). -/
theorem logVolR_lt_logVolS {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : logVolR a b < logVolS a b :=
  Real.log_lt_log (by positivity) (by linarith)

/-- No positive scalar relates the two log-volumes for all `a, b > 0`: there is no `c` with
`μ^log(S_{a,b}) = c · μ^log(R_{a,b})` identically. At `a = 1/8`, `b = 1/4` the region `R` has
area `1`, so log-volume `0`, while `S` has area `3/2`. -/
theorem not_linear : ¬ ∃ c : ℝ, ∀ a b : ℝ, 0 < a → 0 < b → logVolS a b = c * logVolR a b := by
  rintro ⟨c, hc⟩
  have h := hc (1 / 8) (1 / 4) (by norm_num) (by norm_num)
  have hR : logVolR (1 / 8) (1 / 4) = 0 := by unfold logVolR; norm_num
  have hS : 0 < logVolS (1 / 8) (1 / 4) := by
    unfold logVolS; exact Real.log_pos (by norm_num)
  rw [hR, mul_zero] at h
  linarith

/-- Nor are they related by a fixed additive shift, that is, by rescaling the measure:
the difference `μ^log(S) − μ^log(R) = log((4a + 4b)/(4a + 2b))` depends on `(a, b)`. -/
theorem not_affine_shift :
    ¬ ∃ s : ℝ, ∀ a b : ℝ, 0 < a → 0 < b → logVolS a b = logVolR a b + s := by
  rintro ⟨s, hs⟩
  have h1 := hs 1 1 (by norm_num) (by norm_num)
  have h2 := hs 1 2 (by norm_num) (by norm_num)
  unfold logVolS logVolR at h1 h2
  norm_num at h1 h2
  have e1 : Real.log 8 - Real.log 6 = Real.log (8 / 6) :=
    (Real.log_div (by norm_num) (by norm_num)).symm
  have e2 : Real.log 12 - Real.log 8 = Real.log (12 / 8) :=
    (Real.log_div (by norm_num) (by norm_num)).symm
  have hlt : Real.log (8 / 6) < Real.log (12 / 8) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  linarith

end IUT.Audit.MochizukiResponses
