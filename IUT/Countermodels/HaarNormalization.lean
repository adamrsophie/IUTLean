import Mathlib

/-!
# Countermodels: canonical reconstruction and a chosen normalization of volume

Source context: Mochizuki, *Inter-universal Teichmüller Theory III*, Proposition 3.9 (i) to (iv),
pages 115 to 117, read in this session; page 115 was also read from the rendered page. There,
the `p_v`-adic log-volume on a local packet is normalized in two ways at once: the integral
structure `𝒪` has log-volume `0`, and multiplying a region by `p_v` adds `−log(p_v)`.
Proposition 3.9 (ii) states that the log-volumes can be constructed by a functorial algorithm
from mono-analytic data; Theorem 3.11 (ii) (a) (page 155) and Step (x) of the proof of
Corollary 3.12 (page 181) use their compatibility with the relevant isomorphisms.

**None of the statements below is a counterexample to a statement of the IUT papers.** They
refute the simplified abstraction "if an object is reconstructed canonically (up to isomorphism),
a chosen normalization of the volume on it is reconstructed as well". On the real line, which
stands in for a local field here, a Haar measure is unique only up to a positive scalar, and
the scalar is not fixed by the group structure, by the topology, or by the scaling law. It is
fixed by an anchor: the volume of a chosen reference set. In Proposition 3.9 (i) the anchor is
the log-volume `0` of `𝒪`; whether the various isomorphisms of the papers preserve that anchor
is exactly what the compatibility statements there assert, and these examples show that such a
compatibility is a genuine additional property.

Here `logVol μ s` is `log (μ s)` for a set of finite positive measure.
-/

namespace IUT.Countermodels.Haar

open MeasureTheory Measure Set
open scoped Pointwise

/-- The log-volume of a set `s` for a measure `μ` on `ℝ`, meaningful when `0 < μ s < ∞`. -/
noncomputable def logVol (μ : Measure ℝ) (s : Set ℝ) : ℝ := Real.log (μ s).toReal

/-! ## The positive statements: uniqueness up to a scalar, and the anchor -/

/-- **Positive statement.** Every additive Haar measure on `ℝ` is a scalar multiple of
Lebesgue measure (`isAddLeftInvariant_eq_smul`). So Haar measure is canonical up to exactly one
real scalar. -/
theorem haar_eq_smul_volume (μ : Measure ℝ) [μ.IsAddHaarMeasure] :
    μ = μ.addHaarScalarFactor volume • volume :=
  isAddLeftInvariant_eq_smul μ volume

/-- **Positive statement.** An anchor fixes the scalar: an additive Haar measure on `ℝ` that
gives the unit interval volume `1` is Lebesgue measure. This is the analog of the requirement
"the log-volume of `𝒪` is zero" in IUT III, Proposition 3.9 (i), page 115. -/
theorem haar_eq_volume_of_anchor (μ : Measure ℝ) [μ.IsAddHaarMeasure]
    (h : μ (Icc 0 1) = 1) : μ = volume := by
  have hμ := haar_eq_smul_volume μ
  have hc : (μ.addHaarScalarFactor volume : ENNReal) = 1 := by
    have := h
    rw [hμ, smul_apply, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, ENNReal.smul_def,
      smul_eq_mul, mul_one] at this
    exact this
  rw [hμ, ENNReal.smul_def, hc, one_smul]

/-! ## The countermodel: every rescaling is again Haar and satisfies the scaling law -/

/-- **Countermodel.** For every `c > 0`, the measure `c · volume` is again an additive Haar
measure on `ℝ`, it differs from `volume` when `c ≠ 1`, and it shifts every log-volume by
`log c`. So the property "is a Haar measure on the topological group `ℝ`" determines the
log-volume only up to an additive constant. -/
theorem rescaled_haar (c : ℝ) (hc : 0 < c) :
    (ENNReal.ofReal c • volume : Measure ℝ).IsAddHaarMeasure ∧
      (c ≠ 1 → (ENNReal.ofReal c • volume : Measure ℝ) ≠ volume) ∧
      ∀ s : Set ℝ, volume s ≠ 0 → volume s ≠ ⊤ →
        logVol (ENNReal.ofReal c • volume) s = Real.log c + logVol volume s := by
  refine ⟨IsAddHaarMeasure.smul _ (by simpa using hc) ENNReal.ofReal_ne_top, ?_, ?_⟩
  · intro hc1 heq
    have := congrArg (fun μ : Measure ℝ => μ (Icc 0 1)) heq
    simp only [smul_apply, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, smul_eq_mul,
      mul_one] at this
    exact hc1 ((ENNReal.ofReal_eq_one).mp this)
  · intro s h0 htop
    have hpos : 0 < (volume s).toReal := ENNReal.toReal_pos h0 htop
    simp only [logVol, smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le]
    exact Real.log_mul hc.ne' hpos.ne'

/-- **Countermodel.** The scaling law "multiplying a region by `a` adds `log |a|` to its
log-volume" holds for every rescaled Haar measure `c · volume`, whatever `c > 0` is. This law is
the real analog of the packet-normalization rule "multiplication by `p_v` adds `−log(p_v)`" of
IUT III, Proposition 3.9 (i), page 115. Together with `rescaled_haar` it shows that the scaling
law alone does not fix the normalization; only the anchor of `haar_eq_volume_of_anchor` does. -/
theorem scaling_law_all_normalizations (c : ℝ) (hc : 0 < c) (a : ℝ) (ha : a ≠ 0) (s : Set ℝ)
    (h0 : volume s ≠ 0) (htop : volume s ≠ ⊤) :
    logVol (ENNReal.ofReal c • volume) (a • s) =
      Real.log |a| + logVol (ENNReal.ofReal c • volume) s := by
  have hpos : 0 < (volume s).toReal := ENNReal.toReal_pos h0 htop
  have hvol : volume (a • s) = ENNReal.ofReal |a| * volume s := by
    rw [addHaar_smul]
    simp
  simp only [logVol, smul_apply, smul_eq_mul, hvol, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc.le, ENNReal.toReal_ofReal (abs_nonneg a)]
  rw [Real.log_mul hc.ne' (by positivity), Real.log_mul (by positivity) hpos.ne',
    Real.log_mul hc.ne' hpos.ne']
  ring

/-! ## Transport of a normalization along an automorphism -/

/-- **Countermodel.** Transporting Lebesgue measure along the automorphism `x ↦ a x` of the
topological group `ℝ` gives `|a|⁻¹ · volume`, and so shifts every log-volume by `−log |a|`.
If `ℝ` is reconstructed only up to isomorphism of topological groups, the normalization
transported from one copy to another depends on the isomorphism used. -/
theorem transport_shifts_logVol (a : ℝ) (ha : a ≠ 0) (s : Set ℝ) (h0 : volume s ≠ 0)
    (htop : volume s ≠ ⊤) :
    logVol (map (a * ·) volume) s = -Real.log |a| + logVol volume s := by
  have hpos : 0 < (volume s).toReal := ENNReal.toReal_pos h0 htop
  simp only [logVol, Real.map_volume_mul_left ha, smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]
  rw [Real.log_mul (by positivity) hpos.ne', abs_inv, Real.log_inv]

/-- **Positive statement.** Transport along `x ↦ a x` preserves Lebesgue measure exactly when
`|a| = 1`, that is, exactly when it preserves the anchor `volume [0, 1] = 1`. So the
normalization is carried along precisely by the isomorphisms that respect the anchor. -/
theorem transport_preserves_iff (a : ℝ) (ha : a ≠ 0) :
    map (a * ·) volume = volume ↔ |a| = 1 := by
  rw [Real.map_volume_mul_left ha]
  constructor
  · intro h
    have := congrArg (fun μ : Measure ℝ => μ (Icc 0 1)) h
    simp only [smul_apply, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, smul_eq_mul,
      mul_one] at this
    rw [ENNReal.ofReal_eq_one, abs_inv] at this
    exact inv_eq_one.mp this
  · intro h
    rw [abs_inv, h, inv_one, ENNReal.ofReal_one, one_smul]

end IUT.Countermodels.Haar
