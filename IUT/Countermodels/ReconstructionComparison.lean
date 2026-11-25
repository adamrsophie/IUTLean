import Mathlib

/-!
# Countermodel: a link plus per-copy reconstruction does not give a comparison

Source context: Mochizuki, *Inter-universal Teichmüller Theory III*, Corollary 3.12 and its
proof, pages 173 to 186, read in this session from the extracted text; in particular Steps
(xi-a) to (xi-g), pages 181 to 184, and Step (xii), pages 185 and 186. Also Theorem 3.11 (i),
(ii), pages 153 to 157, and Proposition 3.9, pages 115 to 117 (page 115 also read from the
rendered page). No formula of the papers is transcribed here.

## What this file is

**This is a model of an abstraction, not a model of IUT, and it refutes no statement of the
papers.** The abstraction is: "two copies of a structure, each of which reconstructs its own
real-valued invariant, joined by a link that identifies only part of the structure, already
determine a relation between the two invariants". The model:

* a *normalized line* is the additive group `ℝ` equipped with a Haar measure `c · volume`
  (`c > 0`, the normalization) and a pilot region `[0, a]` (`a > 0`);
* its invariant is the log-volume `log ((c · volume) [0, a])` of the pilot region, computed
  from the line's own data;
* per-copy reconstruction holds: the invariant is preserved by every measurable bijection
  that carries the measure to the measure and the pilot region to the pilot region
  (`invariant_of_iso`);
* a *link* between two normalized lines is an automorphism of the additive group `ℝ` (here even
  continuous and order preserving) that carries the pilot region of the first onto the pilot
  region of the second. It identifies the additive structure and the pilot objects, and nothing
  about the normalizations.

Results:

* `link_and_reconstruction_no_relation`: for any pilot lengths and any two real numbers
  `α, β`, there are normalizations such that a link exists and the invariants are `α` and `β`.
  So the link together with per-copy reconstruction implies no relation at all between the
  invariants: not `=`, not `≤`, not `≥`.
* `invariant_le_of_volume_compatible` (positive): if the link is in addition
  *volume compatible* (it carries the first measure to the second) and carries the first pilot
  region into the second, then the first invariant is at most the second; with equality of
  regions it is an equality (`invariant_of_iso`).

## Which hypotheses of the actual theorem the model does and does not satisfy

The model contains: two copies of a structure carrying a real-valued log-volume; a link that
identifies a pilot object of one copy with a pilot object of the other; the internal
computability of each copy's log-volume.

The model does not contain: Hodge theaters, Frobenioids, Kummer theory, the log-link, the
log-Kummer correspondence, tensor packets, the multiradial algorithm of Theorem 3.11, the
indeterminacies (Ind1), (Ind2), (Ind3), the holomorphic hull, or the properties (IPL), (SHE),
(APT) of Remark 3.11.1 (not read for this file) on which Steps (xi-b) to (xi-f) rely. In the
proof of Corollary 3.12 the two log-volumes are not compared through a bare link: Step (xi-b)
to (xi-e) express both, via the multiradial representation and (SHE), relative to the single
arithmetic holomorphic structure of the `1`-column. The named extra compatibility of this model,
volume compatibility of the link, is the toy counterpart of what those steps are meant to
supply. The model therefore shows only that *some* such compatibility is indispensable; it does
not show that the papers fail to supply it. The linearity of the link here also places the model
inside the hypothesis "(Lin)" discussed in `IUT.Audit.ScholzeStix.Diagram`, which Mochizuki
disputes for the situation of the papers.
-/

namespace IUT.Countermodels.Comparison

open MeasureTheory Set

/-- A normalized line: the additive group `ℝ` with the Haar measure `scale · volume` and the
pilot region `[0, pilotLength]`. Only data; no property is assumed. -/
structure NormalizedLine where
  /-- The normalization constant `c` of the Haar measure `c · volume`. -/
  scale : ℝ
  /-- The length `a` of the pilot region `[0, a]`. -/
  pilotLength : ℝ

namespace NormalizedLine

/-- The Haar measure `scale · volume` of a normalized line. -/
noncomputable def measure (T : NormalizedLine) : Measure ℝ := ENNReal.ofReal T.scale • volume

/-- The pilot region `[0, pilotLength]`. -/
def pilot (T : NormalizedLine) : Set ℝ := Icc 0 T.pilotLength

/-- The invariant reconstructed from the line's own data: the log-volume of its pilot region. -/
noncomputable def invariant (T : NormalizedLine) : ℝ := Real.log (T.measure T.pilot).toReal

/-- For positive data, the invariant is `log c + log a`. -/
theorem invariant_eq (T : NormalizedLine) (hc : 0 < T.scale) (ha : 0 < T.pilotLength) :
    T.invariant = Real.log T.scale + Real.log T.pilotLength := by
  simp only [invariant, measure, pilot, smul_apply, Real.volume_Icc, sub_zero,
    smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le, ENNReal.toReal_ofReal ha.le]
  exact Real.log_mul hc.ne' ha.ne'

end NormalizedLine

open NormalizedLine

/-! ## Per-copy reconstruction (positive) -/

/-- **Positive statement: reconstruction.** The invariant is preserved by every measurable
bijection that carries the measure of one normalized line to the measure of the other and the
pilot region onto the pilot region. -/
theorem invariant_of_iso (T₀ T₁ : NormalizedLine) (e : ℝ ≃ᵐ ℝ)
    (hμ : Measure.map e T₀.measure = T₁.measure) (hP : e '' T₀.pilot = T₁.pilot) :
    T₀.invariant = T₁.invariant := by
  unfold invariant
  rw [← hμ, ← hP, MeasurableEquiv.map_apply, e.preimage_image]

/-! ## The countermodel -/

/-- Multiplication by a nonzero real number as an automorphism of the additive group `ℝ`. -/
noncomputable def mulLink (t : ℝ) (ht : t ≠ 0) : ℝ ≃+ ℝ where
  toFun x := t * x
  invFun x := t⁻¹ * x
  left_inv x := by simp [ht]
  right_inv x := by simp [ht]
  map_add' x y := mul_add t x y

/-- **Countermodel.** Fix any pilot lengths `a₀, a₁ > 0` and any real numbers `α, β`. There are
normalizations `c₀, c₁ > 0` such that the normalized lines `T₀ = (c₀, a₀)`, `T₁ = (c₁, a₁)` are
joined by a link (a continuous, strictly increasing automorphism of the additive group `ℝ`
carrying the pilot region of `T₀` onto that of `T₁`), and `T₀.invariant = α`,
`T₁.invariant = β`. Each invariant is reconstructed inside its own line
(`invariant_of_iso`), yet the link plus the two reconstructions impose no relation between
them. -/
theorem link_and_reconstruction_no_relation (a₀ a₁ : ℝ) (h₀ : 0 < a₀) (h₁ : 0 < a₁)
    (α β : ℝ) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      (∃ φ : ℝ ≃+ ℝ, Continuous φ ∧ StrictMono φ ∧
        φ '' (NormalizedLine.mk c₀ a₀).pilot = (NormalizedLine.mk c₁ a₁).pilot) ∧
      (NormalizedLine.mk c₀ a₀).invariant = α ∧ (NormalizedLine.mk c₁ a₁).invariant = β := by
  have ht : 0 < a₁ / a₀ := div_pos h₁ h₀
  refine ⟨Real.exp α / a₀, Real.exp β / a₁, div_pos (Real.exp_pos α) h₀,
    div_pos (Real.exp_pos β) h₁, ⟨mulLink (a₁ / a₀) ht.ne', continuous_const.mul continuous_id,
    fun x y hxy => mul_lt_mul_of_pos_left hxy ht, ?_⟩, ?_, ?_⟩
  · show (fun x => a₁ / a₀ * x) '' Icc 0 a₀ = Icc 0 a₁
    rw [image_mul_left_Icc ht.le h₀.le, mul_zero, div_mul_cancel₀ a₁ h₀.ne']
  · rw [invariant_eq _ (div_pos (Real.exp_pos α) h₀) h₀]
    simp only
    rw [Real.log_div (Real.exp_pos α).ne' h₀.ne', Real.log_exp]
    ring
  · rw [invariant_eq _ (div_pos (Real.exp_pos β) h₁) h₁]
    simp only
    rw [Real.log_div (Real.exp_pos β).ne' h₁.ne', Real.log_exp]
    ring

/-- The countermodel in the form relevant to an inequality: a link and per-copy reconstruction
are compatible both with `T₀.invariant < T₁.invariant` and with `T₁.invariant < T₀.invariant`,
for the same pilot lengths. -/
theorem link_compatible_with_both_orders (a₀ a₁ : ℝ) (h₀ : 0 < a₀) (h₁ : 0 < a₁) :
    (∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      (∃ φ : ℝ ≃+ ℝ, Continuous φ ∧ StrictMono φ ∧
        φ '' (NormalizedLine.mk c₀ a₀).pilot = (NormalizedLine.mk c₁ a₁).pilot) ∧
      (NormalizedLine.mk c₀ a₀).invariant < (NormalizedLine.mk c₁ a₁).invariant) ∧
    (∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      (∃ φ : ℝ ≃+ ℝ, Continuous φ ∧ StrictMono φ ∧
        φ '' (NormalizedLine.mk c₀ a₀).pilot = (NormalizedLine.mk c₁ a₁).pilot) ∧
      (NormalizedLine.mk c₁ a₁).invariant < (NormalizedLine.mk c₀ a₀).invariant) := by
  constructor
  · obtain ⟨c₀, c₁, hc₀, hc₁, hφ, h0, h1⟩ := link_and_reconstruction_no_relation a₀ a₁ h₀ h₁ 0 1
    exact ⟨c₀, c₁, hc₀, hc₁, hφ, by rw [h0, h1]; norm_num⟩
  · obtain ⟨c₀, c₁, hc₀, hc₁, hφ, h0, h1⟩ := link_and_reconstruction_no_relation a₀ a₁ h₀ h₁ 1 0
    exact ⟨c₀, c₁, hc₀, hc₁, hφ, by rw [h0, h1]; norm_num⟩

/-! ## The named extra compatibility (positive) -/

/-- **Positive statement: comparison from volume compatibility.** If a link (any measurable
bijection) is *volume compatible*, that is, carries the measure of `T₀` to the measure of `T₁`,
and carries the pilot region of `T₀` into the pilot region of `T₁`, then
`T₀.invariant ≤ T₁.invariant`, provided the pilot region of `T₀` has positive measure and that of
`T₁` finite measure. Inclusion rather than equality is the toy counterpart of an upper
semi-compatibility such as (Ind3) of IUT III, Theorem 3.11 (ii), page 156. -/
theorem invariant_le_of_volume_compatible (T₀ T₁ : NormalizedLine) (e : ℝ ≃ᵐ ℝ)
    (hμ : Measure.map e T₀.measure = T₁.measure) (hP : e '' T₀.pilot ⊆ T₁.pilot)
    (hpos : T₀.measure T₀.pilot ≠ 0) (hfin : T₁.measure T₁.pilot ≠ ⊤) :
    T₀.invariant ≤ T₁.invariant := by
  have heq : T₀.measure T₀.pilot = T₁.measure (e '' T₀.pilot) := by
    rw [← hμ, MeasurableEquiv.map_apply, e.preimage_image]
  have hle : T₀.measure T₀.pilot ≤ T₁.measure T₁.pilot := heq ▸ measure_mono hP
  have hfin0 : T₀.measure T₀.pilot ≠ ⊤ := ne_top_of_le_ne_top hfin hle
  unfold invariant
  exact Real.log_le_log (ENNReal.toReal_pos hpos hfin0) ((ENNReal.toReal_le_toReal hfin0 hfin).mpr hle)

end IUT.Countermodels.Comparison
