import IUT.PaperIII.Corollary312.Comparison
import IUT.PaperII.Labels

/-!
# IUT III, Corollary 3.12: the average over the labels `j ∈ 𝔽_l^⋇`

Source: Mochizuki, *Inter-universal Teichmüller Theory III*, Proposition 3.9 (i), page 116;
Remark 3.9.3, pages 119 and 120; Theorem 3.11 (i), page 153; the statement of Corollary 3.12,
pages 173 and 174; Steps (x) and (xi-d) of its proof, pages 181 and 183. Pages read for this
file: 116, 119, 120, 153, 154, 173, 174, 181 to 183. Pages checked against rendered images:
116, 153, 154, 173, 174, 181, 183. Pages 119, 120 and 182 were read in text only; no formula of
this file is taken from them. The label sets come from `IUT.PaperII.Labels`, whose sources are
listed there (IUT I, page 3, and IUT II, page 3, both rendered).

## What this file is and is not

**This file is not a formalization of Corollary 3.12.** It instantiates the equal-weight
average of `Comparison.lean` at the index set of the paper. As in `Comparison.lean`, no region
is constructed from initial Θ-data, Hodge theaters, the log-theta-lattice or the multiradial
representation of Theorem 3.11; the regions at the various labels are inputs, and the
comparison of the q-pilot region with the hull of the union of the possible images remains an
**unproved hypothesis**.

## What the pages say

* The statement, page 173 (rendered): `− |log(Θ)|` is the procession-normalized log-volume,
  "where the average is taken over `j ∈ 𝔽_l^⋇`". Step (x), page 181 (rendered), says the same.
  `𝔽_l^⋇` has `l^⋇ = (l − 1)/2` elements, so the average carries the factor `1/l^⋇`.
* Theorem 3.11 (i) (a), page 153 (rendered), indexes the packets by `j ∈ |𝔽_l|`, and page 174
  (rendered) indexes the regions `n,◦U_{j,v_Q}` and the hulls `n,◦Ū_{j,v_Q}` by `j ∈ |𝔽_l|`.
* `|𝔽_l| = {0} ∪ 𝔽_l^⋇` (IUT II, page 3; `IUT.PaperII.Labels.card_nonzero_absLabel`).

## What is typed

* `NonzeroLabel l`: the nonzero elements of `|𝔽_l|` (the type `AbsLabel l` of
  `IUT.PaperII.Labels`), which is `𝔽_l^⋇` through the decomposition `|𝔽_l| = {0} ∪ 𝔽_l^⋇`.
  It has `l^⋇` elements for odd `l` (`card_nonzeroLabel`).
* `labelAverage l v = (1/l^⋇) · ∑_{j ∈ 𝔽_l^⋇} v_j`, the normalization of pages 173 and 181,
  and `labelAverage_eq_average`: it is the `equalWeightAverage` of `Comparison.lean` at this
  index set.
* `conclusion_of_labelContainment`: the averaged bridge of `Comparison.lean` at this index set,
  with the two numbers identified as label averages.
* Nonvacuity for every odd `l ≥ 3`: every hypothesis of the bridge holds (`example_label_conclusion`), and
  every structural hypothesis holds while the conclusion fails
  (`example_label_conclusion_fails`).

## Two gaps that this file does not resolve

1. *Page 183.* Step (xi-d) applies the log-volume "suitably normalized, with respect to
   `j ∈ |𝔽_l|`". No factor is displayed there. An average over `|𝔽_l|` would carry the factor
   `1/(l^⋇ + 1)` (`IUT.PaperII.Labels.card_absLabel`), not `1/l^⋇`; nothing on pages 173, 174,
   181 or 183 displays that factor. This file uses the factor `1/l^⋇` of pages 173 and 181.
2. *The label `0`.* The regions are indexed by `|𝔽_l|`, which contains the label `0`, while the
   average runs over `𝔽_l^⋇`. Page 174 recalls that the symbol `△` results from identifying
   the labels `0` and `⟨𝔽_l^⋇⟩`, and page 181 cites that identification as a source of the
   averages; neither page states how the component at `0` enters the average. It may be
   dropped, or identified with the diagonal label. This file takes families indexed by
   `NonzeroLabel l` only: a family indexed by `|𝔽_l|` must first be turned into one indexed by
   `𝔽_l^⋇`, and no rule for doing so is assumed or provided here.

## What is still omitted

The sum over places (see `Places.lean`), tensor packets and the identification of the
capsule at `j` with a tensor product over `j + 1` labels, the identification of the two sides
through the `Θ^{×μ}_{LGP}`-link (Steps (xi-a), (xi-b), pages 181 and 182), the determinant and
tensor power normalization of Step (xi-d), page 183, and the indeterminacies (see
`Indeterminacy.lean`).
-/

namespace IUT.PaperIII.Corollary312

open MeasureTheory Set IUT.PaperII.Labels

/-- The nonzero labels of `|𝔽_l|`, identified with `𝔽_l^⋇` through `|𝔽_l| = {0} ∪ 𝔽_l^⋇`
(IUT II, page 3). -/
def NonzeroLabel (l : ℕ) : Type := {x : AbsLabel l // x ≠ zeroLabel l}

/-- `𝔽_l^⋇` has `l^⋇` elements for odd `l`. -/
theorem card_nonzeroLabel {l : ℕ} (hl : Odd l) [Fintype (NonzeroLabel l)] :
    Fintype.card (NonzeroLabel l) = lstar l := by
  rw [← Nat.card_eq_fintype_card]; exact card_nonzero_absLabel hl

/-- `𝔽_l^⋇` is finite for odd `l`. -/
theorem finite_nonzeroLabel {l : ℕ} (hl : Odd l) : Finite (NonzeroLabel l) :=
  haveI : Finite (AbsLabel l) := Finite.of_surjective _ (labelRep_bijective hl).2
  Subtype.finite

/-- The average over `j ∈ 𝔽_l^⋇` with factor `1/l^⋇` (statement of Corollary 3.12, page 173;
Step (x), page 181). -/
noncomputable def labelAverage (l : ℕ) (v : NonzeroLabel l → EReal) : EReal :=
  (((lstar l : ℝ)⁻¹ : ℝ) : EReal) * ∑ᶠ j, v j

/-- The label average is the `equalWeightAverage` of `Comparison.lean` over `𝔽_l^⋇`. -/
theorem labelAverage_eq_average {l : ℕ} (hl : Odd l) [Fintype (NonzeroLabel l)]
    (v : NonzeroLabel l → EReal) : labelAverage l v = equalWeightAverage v := by
  rw [labelAverage, equalWeightAverage, card_nonzeroLabel hl, finsum_eq_sum_of_fintype]

/-- The average of a constant real family is that constant, for odd `l ≥ 3`. -/
theorem labelAverage_const {l : ℕ} (hl : Odd l) (h3 : 3 ≤ l) (c : ℝ) :
    labelAverage l (fun _ => (c : EReal)) = c := by
  have := finite_nonzeroLabel hl
  let := Fintype.ofFinite (NonzeroLabel l)
  have hne : (lstar l : ℝ) ≠ 0 := by unfold lstar; norm_cast; omega
  rw [labelAverage_eq_average hl, equalWeightAverage, card_nonzeroLabel hl, Finset.sum_const,
    Finset.card_univ, card_nonzeroLabel hl, ← EReal.coe_nsmul, ← EReal.coe_mul, nsmul_eq_mul,
    inv_mul_cancel_left₀ hne]

section Bridge

variable {l : ℕ} {X : NonzeroLabel l → Type*} [∀ j, MeasurableSpace (X j)] {ι : Type*}
  (S : ∀ j, ComparisonSetting (X j) ι)

/-- **Bridge with the paper's normalization (conditional).** For a family of settings indexed by
`j ∈ 𝔽_l^⋇`, componentwise containment and finiteness of each hull give the conclusion of
Corollary 3.12 for the procession-normalized numbers of `Comparison.lean`, and these numbers
are the label averages with factor `1/l^⋇`: `− |log(Θ)|` is the average of the Θ-side
log-volumes and `− |log(q)|` the average of the q-side ones.

Conditional on `hcont` (Theorem 3.11 and Steps (i) to (xi), not formalized) and `hfin`
(page 175, compactness, not formalized). -/
theorem conclusion_of_labelContainment (hl : Odd l) [Fintype (NonzeroLabel l)]
    (hq : ∀ j, (S j).μ (S j).qPilot ≠ 0 ∧ (S j).μ (S j).qPilot ≠ ⊤)
    (hneg : procQLogVolume S < 0) (hΘ : ∀ j, (S j).μ (S j).hullOfUnion ≠ 0)
    (hfin : ∀ j, (S j).μ (S j).hullOfUnion ≠ ⊤) (hcont : ProcContainment S) :
    Conclusion (procPilotLogVolumes S hq hneg hΘ) ∧
      (procPilotLogVolumes S hq hneg hΘ).negLogTheta =
        labelAverage l (fun j => (S j).thetaLogVolume) ∧
      (((-(procPilotLogVolumes S hq hneg hΘ).absLogQ : ℝ)) : EReal) =
        labelAverage l (fun j => (S j).qLogVolume) := by
  refine ⟨conclusion_of_procContainment S hq hneg hΘ hfin hcont,
    (labelAverage_eq_average hl _).symm, ?_⟩
  have hbot : procQLogVolume S ≠ ⊥ :=
    average_ne_bot fun j => (logVolume_eq_bot_iff _ _).not.mpr (hq j).1
  rw [labelAverage_eq_average hl]
  simp only [procPilotLogVolumes, PilotLogVolumes.ofLogVolumes, neg_neg]
  exact EReal.coe_toReal (hneg.trans EReal.zero_lt_top).ne hbot

end Bridge

/-! ## Nonvacuity for every odd `l ≥ 3` -/

namespace LabelExample

open IntervalExample

variable {l : ℕ} (hl : Odd l) (h3 : 3 ≤ l) [Fintype (NonzeroLabel l)]
include hl h3

omit hl h3 [Fintype (NonzeroLabel l)] in
/-- The constant family of interval settings over `𝔽_l^⋇` with q-pilot region `q`. -/
noncomputable def settings (l : ℕ) (q : Set ℝ) (_ : NonzeroLabel l) : ComparisonSetting ℝ Bool :=
  setting q

omit hl h3 [Fintype (NonzeroLabel l)] in
theorem logVolume_Icc (b : ℝ) (hb : 0 < b) :
    logVolume volume (Icc (0 : ℝ) b) = (Real.log b : EReal) := by
  rw [logVolume, Real.volume_Icc, sub_zero, ENNReal.log_ofReal_of_pos hb]

theorem procQLogVolume_eq (b : ℝ) (hb : 0 < b) :
    procQLogVolume (settings l (Icc 0 b)) = (Real.log b : EReal) := by
  rw [procQLogVolume, ← labelAverage_eq_average hl]
  simp only [settings, ComparisonSetting.qLogVolume, setting, logVolume_Icc b hb]
  exact labelAverage_const hl h3 _

theorem procThetaLogVolume_eq (q : Set ℝ) :
    procThetaLogVolume (settings l q) = (Real.log (1 / 2) : EReal) := by
  rw [procThetaLogVolume, ← labelAverage_eq_average hl]
  simp only [settings, ComparisonSetting.thetaLogVolume, setting_hullOfUnion]
  simp only [setting, logVolume_Icc (1 / 2) (by norm_num)]
  exact labelAverage_const hl h3 _

theorem side_conditions (b : ℝ) (hb : 0 < b) (hb1 : b < 1) :
    (∀ j, (settings l (Icc 0 b) j).μ (settings l (Icc 0 b) j).qPilot ≠ 0 ∧
      (settings l (Icc 0 b) j).μ (settings l (Icc 0 b) j).qPilot ≠ ⊤) ∧
    procQLogVolume (settings l (Icc 0 b)) < 0 ∧
    (∀ j, (settings l (Icc 0 b) j).μ (settings l (Icc 0 b) j).hullOfUnion ≠ 0) ∧
    (∀ j, (settings l (Icc 0 b) j).μ (settings l (Icc 0 b) j).hullOfUnion ≠ ⊤) := by
  refine ⟨fun j => ⟨by simp [settings, setting, Real.volume_Icc, hb], by
      simp [settings, setting, Real.volume_Icc]⟩, ?_, fun j => ?_, fun j => ?_⟩
  · rw [procQLogVolume_eq hl h3 b hb]
    exact_mod_cast Real.log_neg hb hb1
  · simp only [settings, volume_hullOfUnion]; simp
  · simp only [settings, volume_hullOfUnion]; exact ENNReal.ofReal_ne_top

/-- **Nonvacuity (a).** For odd `l ≥ 3` and q-pilot region `[0, 1/2]` at each label, every
hypothesis of `conclusion_of_labelContainment` holds, so the conclusion of Corollary 3.12
holds for the numbers averaged with factor `1/l^⋇`. -/
theorem example_label_conclusion :
    ∃ hq hneg hΘ, Conclusion (procPilotLogVolumes (settings l (Icc 0 (1 / 2))) hq hneg hΘ) := by
  obtain ⟨hq, hneg, hΘ, hfin⟩ := side_conditions hl h3 (1 / 2) (by norm_num) (by norm_num)
  refine ⟨hq, hneg, hΘ, (conclusion_of_labelContainment _ hl hq hneg hΘ hfin
    fun j => ?_).1⟩
  show Icc 0 (1 / 2) ⊆ (setting _).hullOfUnion
  rw [setting_hullOfUnion]

/-- **Nonvacuity (b).** For odd `l ≥ 3` and q-pilot region `[0, 3/4]` at each label, every
structural hypothesis holds (positive finite measures, negative averaged q-side log-volume,
finite hulls), but the averaged comparison and the conclusion of Corollary 3.12 fail. -/
theorem example_label_conclusion_fails :
    ∃ hq hneg hΘ, (∀ j, (settings l (Icc 0 (3 / 4)) j).μ
        (settings l (Icc 0 (3 / 4)) j).hullOfUnion ≠ ⊤) ∧
      ¬ ProcLogVolumeComparison (settings l (Icc 0 (3 / 4))) ∧
      ¬ Conclusion (procPilotLogVolumes (settings l (Icc 0 (3 / 4))) hq hneg hΘ) := by
  obtain ⟨hq, hneg, hΘ, hfin⟩ := side_conditions hl h3 (3 / 4) (by norm_num) (by norm_num)
  have hc : ¬ ProcLogVolumeComparison (settings l (Icc 0 (3 / 4))) := by
    rw [ProcLogVolumeComparison, procQLogVolume_eq hl h3 _ (by norm_num), procThetaLogVolume_eq hl h3,
      EReal.coe_le_coe_iff, not_le]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  exact ⟨hq, hneg, hΘ, hfin, hc, fun h =>
    hc ((PilotLogVolumes.conclusion_ofLogVolumes_iff _ _ _ _ _).mp h).2⟩

end LabelExample

end IUT.PaperIII.Corollary312
