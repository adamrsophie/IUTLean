import IUT.PaperIII.Corollary312.Numerical
import IUT.PaperIII.Remark3_9_5.HullOperator

/-!
# IUT III, Corollary 3.12: an interface for the final comparison of regions

Source: Mochizuki, *Inter-universal Teichmüller Theory III*, Corollary 3.12 and Steps (x) to
(xii) of its proof, pages 173 to 186; Proposition 3.9, pages 115 to 118; Remark 3.9.5 (i) to
(iv), pages 126 to 129. Pages read for this file from the extracted text: 115 to 118, 125 to
129, 173 to 175, 180 to 186. Pages checked against rendered images: 115 to 117,
127, 173 to 175, 181 to 185. Pages 118, 125, 126, 128, 129, 180 and 186 were read in text only;
no formula of this file is taken from them.

## What this file is and is not

**This file is not a formalization of Corollary 3.12.** It is an interface for the last step
of the proof, the passage from regions to the two numbers `− |log(Θ)|` and `− |log(q)|`. It
does not construct any region from initial Θ-data, Hodge theaters, the log-theta-lattice, the
log-Kummer correspondence or the multiradial representation of Theorem 3.11. All such regions
are inputs.

The comparison of the q-pilot region with the hull of the union of the possible images
(`Containment`, `LogVolumeComparison` below) is, in the paper, the content of Theorem 3.11
together with Steps (i) to (xi) of the proof. Here it is an **unproved hypothesis**. Every
theorem below that takes it as a hypothesis is conditional on it, and nothing in this file
gives evidence for or against it.

## What is typed

* `logVolume μ S = ENNReal.log (μ S)`: the log-volume of a region, with `log 0 = −∞` and
  `log ∞ = +∞` (Mathlib's `ENNReal.log`). It is monotone, and finite exactly when
  `0 < μ S < ∞`.
* `ComparisonSetting X ι`: data only. A measure `μ` on a measurable space `X`, a family `𝓟` of
  regions on which a hull is defined, a family `𝓗` of hulls, a hull map with the properties
  (P1), (P2), (P3) of Remark 3.9.5 (ii) (`IsHullMap` from `HullOperator.lean`), the q-pilot
  region, and a family of possible images indexed by an arbitrary type `ι` (the indeterminacy
  data). One regularity field: the union of the possible images lies in `𝓟`.
* `Containment` (region form) and `LogVolumeComparison` (numerical form) of the comparison,
  as separate `Prop`s on a setting; `logVolumeComparison_of_containment`.
* The bridge to `Numerical.lean`: `toPilotLogVolumes` and `conclusion_of_containment`.
* Averaging over a finite set of labels `j` with equal weights (`average`,
  `conclusion_of_procContainment`).
* Nonvacuity on `ℝ` with Lebesgue measure and the interval hull `Icc (sInf P) (sSup P)`:
  a setting where every hypothesis of the bridge holds (`example_bridge_hypotheses`), one where
  all of them except the comparison hold and the conclusion fails
  (`example_comparison_fails`), and one where no single possible image, and not the union
  either, contains the q-pilot region but the hull of the union does (`example_union_matters`).

## Interpretation choices

1. *Regions and log-volume.* Proposition 3.9 (i), pages 115 and 116, defines log-volumes on
   nonempty compact open subsets (nonarchimedean) or compact closures of nonempty open subsets
   (archimedean), normalized so that the integral structure has log-volume `0` and
   multiplication by `p_v` adds `−log(p_v)` (multiplication by `e` adds `1`). Here a region is
   an arbitrary subset and the log-volume is `log` of an arbitrary measure. The normalization
   "integral structure has log-volume `0`" is not part of the setting; it enters only through
   the hypothesis `μ qPilot < 1`, which is what `|log(q)| > 0` (page 174) says once the
   log-volume is `log μ`.
2. *The domain of the hull.* Remark 3.9.5 (i), page 127, defines the hull of any subset that
   contains a relatively compact subset of finite log-volume; (ii) states (P1) to (P3) on the
   set `ℙ` of direct product regions. The paper does not say that the union of the possible
   images is a direct product region. The field `union_mem` takes `𝓟` to be a family on which
   (P1) to (P3) hold and which contains the union; this is a choice.
3. *Possible images.* Page 174 defines `n,◦U_{j,v_Q}` as the union of the possible images of a
   Θ-pilot object subject to (Ind1), (Ind2), (Ind3), without a formula for the set of possible
   images. Here that set is an arbitrary indexed family `image : ι → Set X`; how (Ind1), (Ind2),
   (Ind3) generate it is not modeled.
4. *Signs.* The symbol `− |log(Θ)|` is a name for the log-volume of the hull of the union, not
   the negative of an absolute value: `negLogTheta` is that log-volume itself. The symbol
   `− |log(q)|` is the log-volume of the q-pilot region, so `absLogQ` is minus that log-volume.
5. *Which form the text asserts.* In the reading adopted here, the text never asserts a containment of
   regions. Steps (xi-c) and (xi-d), pages 182 and 183, say that the possible output data in
   `1,◦Ū` are "linked/related" to the representation of the q-pilot object via isomorphisms of
   `F^{⊩▶}`-prime-strips. Step (xi-f), page 184, asserts the numerical inclusion
   `− |log(q)| ∈ ℝ_{≤ −|log(Θ)|}`. So `LogVolumeComparison` is what the text asserts, and
   `Containment` is a region-level sufficient condition, not a quotation.
6. *Averaging.* The statement (page 173) and Step (x) (page 181, rendered) average over
   `j ∈ 𝔽_l^⊛`; page 174 indexes the regions by `j ∈ |𝔽_l|`, and Step (xi-d), page 183,
   normalizes "with respect to `j ∈ |𝔽_l|`". Proposition 3.9 (i), page 116, defines the
   procession-normalization as "the average, over the various capsules". The average here is
   uniform over an arbitrary nonempty finite index type `J`; the statement itself averages over
   `𝔽_l^⊛` with factor `1 / l^⊛` (pages 173 and 181); the file keeps `J` general.

## What the interface omits, and what could be added next

* *The sum over places `v_Q ∈ 𝕍_ℚ`* (Proposition 3.9 (iii), page 117). Elementary to add for
  a finite set of places, in the same way as the average over `j` (a sum with weight `1`); not
  added, because the weights of Remark 3.1.1 (ii) to (iv) were not read.
* *The procession structure.* The labels `j` index capsules of a procession, and the packet at
  `j` is a tensor product over `j + 1` labels. Only the equal-weight average over `j` is here.
* *The identification of the two sides through the `Θ^{×μ}_{LGP}`-link* (Step (xi-a), page
  181) and through the permutation symmetry `0,◦U ≅ 1,◦U` (Step (xi-b), page 181). Here both
  regions live in one space `X` with one measure `μ`; that they can be placed there with a
  common measure is assumed by the typing, not proved. This is where
  `IUT.Countermodels.Comparison` shows some compatibility is indispensable.
* *Tensor packets, determinants and the tensor power of Step (xi-d)*, page 183; not modeled.
* *The indeterminacies themselves.* The invariance of log-volume under (Ind1), (Ind2) and the
  inequality from (Ind3) (Step (x), page 181) are not stated; the family `image` is arbitrary.
  A next step is to generate `image` as `{Y | ∃ g ∈ G, g • R ⊑ Y}` for a group `G` of measure
  preserving maps and a containment relation `⊑`, and to prove the invariance.
-/

namespace IUT.PaperIII.Corollary312

open MeasureTheory Set IUT.PaperIII.Remark3_9_5

/-! ## Log-volume of a region -/

section LogVolume

variable {X : Type*} [MeasurableSpace X]

/-- The log-volume of a region `S` relative to a measure `μ`: `log (μ S)`, with value `−∞` when
`μ S = 0` and `+∞` when `μ S = ∞`. -/
noncomputable def logVolume (μ : Measure X) (S : Set X) : EReal := ENNReal.log (μ S)

/-- Log-volume is monotone with respect to inclusion of regions. -/
theorem logVolume_mono (μ : Measure X) {S T : Set X} (h : S ⊆ T) :
    logVolume μ S ≤ logVolume μ T :=
  ENNReal.log_monotone (measure_mono h)

/-- The log-volume is `−∞` exactly when the region has measure zero. -/
theorem logVolume_eq_bot_iff (μ : Measure X) (S : Set X) :
    logVolume μ S = ⊥ ↔ μ S = 0 :=
  ENNReal.log_eq_bot_iff

/-- The log-volume is `+∞` exactly when the region has infinite measure. -/
theorem logVolume_eq_top_iff (μ : Measure X) (S : Set X) :
    logVolume μ S = ⊤ ↔ μ S = ⊤ :=
  ENNReal.log_eq_top_iff

/-- The log-volume is a real number exactly when the measure lies in `(0, ∞)`. -/
theorem logVolume_finite_iff (μ : Measure X) (S : Set X) :
    (logVolume μ S ≠ ⊥ ∧ logVolume μ S ≠ ⊤) ↔ (μ S ≠ 0 ∧ μ S ≠ ⊤) := by
  rw [Ne, Ne, logVolume_eq_bot_iff, logVolume_eq_top_iff]

/-- The log-volume is negative exactly when the measure is less than `1`. -/
theorem logVolume_neg_iff (μ : Measure X) (S : Set X) :
    logVolume μ S < 0 ↔ μ S < 1 :=
  ENNReal.log_lt_zero_iff

end LogVolume

/-! ## The setting -/

/-- The data for the last step of the proof of Corollary 3.12, for one component.

This is **not** the paper's situation: none of the fields is constructed from Hodge theaters
or the multiradial representation. The fields are data, plus the hull axioms and one
well-posedness condition. No field relates the q-pilot region to the possible images. -/
structure ComparisonSetting (X : Type*) [MeasurableSpace X] (ι : Type*) where
  /-- The measure whose logarithm is the log-volume (Proposition 3.9 (i), (ii), pages 115 to
  117). -/
  μ : Measure X
  /-- The regions to which the hull applies (`ℙ` of Remark 3.9.5 (ii), page 127). -/
  hullDomain : Set (Set X)
  /-- The hulls (`ℍ` of Remark 3.9.5 (ii), page 127). -/
  hulls : Set (Set X)
  /-- The hull map `φ : ℙ → ℍ` of Remark 3.9.5 (ii). -/
  hull : Set X → Set X
  /-- (P1), (P2), (P3) of Remark 3.9.5 (ii), page 127, together with `ℍ ⊆ ℙ`. -/
  isHullMap : IsHullMap hullDomain hulls hull
  /-- The region representing the q-pilot object (`1,◦U^ℚ` side, Step (xi-d), page 183). -/
  qPilot : Set X
  /-- The possible images of a Θ-pilot object, indexed by the indeterminacy data (page 174). -/
  image : ι → Set X
  /-- The hull of the union is defined: the union lies in the domain of the hull map. Remark
  3.9.5 (i), page 127, defines the hull of a subset containing a relatively compact subset of
  finite log-volume; that the union qualifies is an interpretation choice (see the module
  docstring). -/
  union_mem : (⋃ i, image i) ∈ hullDomain

namespace ComparisonSetting

variable {X : Type*} [MeasurableSpace X] {ι : Type*} (S : ComparisonSetting X ι)

/-- The union of the possible images (`n,◦U`, page 174). -/
def unionImages : Set X := ⋃ i, S.image i

/-- The hull of the union of the possible images (`n,◦Ū`, pages 174 and 175). -/
def hullOfUnion : Set X := S.hull S.unionImages

/-- The log-volume of the hull of the union: the quantity named `− |log(Θ)|` (page 173). -/
noncomputable def thetaLogVolume : EReal := logVolume S.μ S.hullOfUnion

/-- The log-volume of the q-pilot region: the quantity named `− |log(q)|` (page 174). -/
noncomputable def qLogVolume : EReal := logVolume S.μ S.qPilot

/-- Each possible image lies in the hull of the union, by (P2). -/
theorem image_subset_hullOfUnion (i : ι) : S.image i ⊆ S.hullOfUnion :=
  (subset_iUnion S.image i).trans (S.isHullMap.P2 _ S.union_mem)

/-- **Comparison, region form.** The q-pilot region is contained in the hull of the union of
the possible images.

In the reading adopted here the text does not assert this; see `LogVolumeComparison`. It is a region-level
condition that implies the numerical form (`logVolumeComparison_of_containment`). Its proof in
the paper, in whatever form, would rest on Theorem 3.11 and Steps (i) to (xi); it is **not**
formalized here. -/
def Containment : Prop := S.qPilot ⊆ S.hullOfUnion

/-- **Comparison, numerical form.** `− |log(q)| ≤ − |log(Θ)|`, i.e. the log-volume of the
q-pilot region is at most that of the hull of the union.

This is what Step (xi-f), page 184, asserts ("the inclusion `− |log(q)| ∈ ℝ_{≤ −|log(Θ)|}`").
Its derivation in the paper rests on Theorem 3.11 and Steps (i) to (xi-e); it is **not**
formalized here. Once the two numbers are defined from a setting, this is the second
conjunct of `Conclusion` (see `conclusion_iff`), so assuming it is assuming that conjunct. -/
def LogVolumeComparison : Prop := S.qLogVolume ≤ S.thetaLogVolume

/-- The region form implies the numerical form, by monotonicity of log-volume. -/
theorem logVolumeComparison_of_containment (h : S.Containment) : S.LogVolumeComparison :=
  logVolume_mono S.μ h

/-- The region form, through the hull axioms: the q-pilot region lies in the hull of the union
exactly when it lies in every hull that contains all possible images. -/
theorem containment_iff_forall_hull :
    S.Containment ↔ ∀ H ∈ S.hulls, (∀ i, S.image i ⊆ H) → S.qPilot ⊆ H := by
  unfold Containment hullOfUnion unionImages
  rw [S.isHullMap.eq_sInter S.union_mem, subset_sInter_iff]
  exact ⟨fun h H hH hU => h H ⟨hH, iUnion_subset hU⟩,
    fun h H hH => h H hH.1 fun i => (subset_iUnion S.image i).trans hH.2⟩

end ComparisonSetting

/-! ## The bridge to `PilotLogVolumes` -/

/-- Two log-volumes `a` (the q side) and `b` (the Θ side) as a `PilotLogVolumes`:
`negLogTheta = b` and `absLogQ = −a`. The hypotheses are the facts `PilotLogVolumes` requires:
`b ≠ −∞` (value set `ℝ ∪ {+∞}`, page 173) and `a` real and negative (`|log(q)| > 0`, page
174). -/
noncomputable def PilotLogVolumes.ofLogVolumes (a b : EReal) (ha : a ≠ ⊥) (hneg : a < 0)
    (hb : b ≠ ⊥) : PilotLogVolumes where
  negLogTheta := b
  negLogTheta_ne_bot := hb
  absLogQ := -a.toReal
  absLogQ_pos := by
    have hcoe := EReal.coe_toReal (hneg.trans EReal.zero_lt_top).ne ha
    rw [← hcoe] at hneg
    linarith [EReal.coe_lt_coe_iff.mp (hneg.trans_eq (EReal.coe_zero).symm)]

/-- For numbers built by `ofLogVolumes`, the conclusion of Corollary 3.12 is exactly
finiteness of `b` together with `a ≤ b`. -/
theorem PilotLogVolumes.conclusion_ofLogVolumes_iff (a b : EReal) (ha : a ≠ ⊥) (hneg : a < 0)
    (hb : b ≠ ⊥) : Conclusion (ofLogVolumes a b ha hneg hb) ↔ b ≠ ⊤ ∧ a ≤ b := by
  have hcoe := EReal.coe_toReal (hneg.trans EReal.zero_lt_top).ne ha
  simp only [Conclusion, ofLogVolumes, neg_neg, hcoe]

namespace ComparisonSetting

variable {X : Type*} [MeasurableSpace X] {ι : Type*} (S : ComparisonSetting X ι)

/-- The two numbers of Corollary 3.12 defined from a setting: `− |log(Θ)|` is the log-volume
of the hull of the union, `|log(q)|` is minus the log-volume of the q-pilot region.

Hypotheses: `hq0`, `hq1`: `0 < μ qPilot < 1`, i.e. `− |log(q)|` is real and negative
(`|log(q)| > 0`, page 174); `hΘ`: the hull of the union has positive measure, i.e.
`− |log(Θ)| ≠ −∞` (value set `ℝ ∪ {+∞}`, page 173). -/
noncomputable def toPilotLogVolumes (hq0 : S.μ S.qPilot ≠ 0) (hq1 : S.μ S.qPilot < 1)
    (hΘ : S.μ S.hullOfUnion ≠ 0) : PilotLogVolumes :=
  PilotLogVolumes.ofLogVolumes S.qLogVolume S.thetaLogVolume
    ((logVolume_eq_bot_iff _ _).not.mpr hq0) ((logVolume_neg_iff _ _).mpr hq1)
    ((logVolume_eq_bot_iff _ _).not.mpr hΘ)

/-- For the numbers defined from a setting, the conclusion of Corollary 3.12 is exactly
finiteness of the hull of the union together with `LogVolumeComparison`. This makes explicit
that the numerical form of the comparison is the inequality of the conclusion itself. -/
theorem conclusion_iff (hq0 : S.μ S.qPilot ≠ 0) (hq1 : S.μ S.qPilot < 1)
    (hΘ : S.μ S.hullOfUnion ≠ 0) :
    Conclusion (S.toPilotLogVolumes hq0 hq1 hΘ) ↔
      S.μ S.hullOfUnion ≠ ⊤ ∧ S.LogVolumeComparison := by
  refine (PilotLogVolumes.conclusion_ofLogVolumes_iff _ _ _ _ _).trans ?_
  rw [thetaLogVolume, Ne, logVolume_eq_top_iff]
  rfl

/-- **Bridge, numerical form.** `LogVolumeComparison` and finiteness give the conclusion of
Corollary 3.12. This is an unfolding of definitions (`conclusion_iff`), recorded because the
task of the last step is exactly to supply these two hypotheses.

* `hfin`: the hull of the union has finite measure. The paper argues this on page 175, from
  "the [easily verified] compactness" of the `1,◦U_{j,v_Q}`; not formalized.
* `hcomp`: asserted by Step (xi-f), page 184, from Theorem 3.11; not formalized. -/
theorem conclusion_of_logVolumeComparison (hq0 : S.μ S.qPilot ≠ 0) (hq1 : S.μ S.qPilot < 1)
    (hΘ : S.μ S.hullOfUnion ≠ 0) (hfin : S.μ S.hullOfUnion ≠ ⊤)
    (hcomp : S.LogVolumeComparison) : Conclusion (S.toPilotLogVolumes hq0 hq1 hΘ) :=
  (S.conclusion_iff hq0 hq1 hΘ).mpr ⟨hfin, hcomp⟩

/-- **Bridge, region form (conditional).** If the q-pilot region is contained in the hull of
the union of the possible images, and that hull has finite measure, then the conclusion of
Corollary 3.12 holds for the numbers defined from the setting.

Conditional on two unproved hypotheses:
* `hcont`: the region form of the comparison; in the paper, the content of Theorem 3.11 and
  Steps (i) to (xi) (the text asserts the numerical form, Step (xi-f), page 184);
* `hfin`: finiteness, argued on page 175 from compactness of the `1,◦U_{j,v_Q}`.

The hypothesis `hΘ` (`− |log(Θ)| ≠ −∞`) is not needed: it follows from `hcont` and
`0 < μ qPilot`. -/
theorem conclusion_of_containment (hq0 : S.μ S.qPilot ≠ 0) (hq1 : S.μ S.qPilot < 1)
    (hfin : S.μ S.hullOfUnion ≠ ⊤) (hcont : S.Containment) :
    Conclusion (S.toPilotLogVolumes hq0 hq1
      (fun h => hq0 (measure_mono_null hcont h))) :=
  S.conclusion_of_logVolumeComparison hq0 hq1 _ hfin (S.logVolumeComparison_of_containment hcont)

end ComparisonSetting

/-! ## Averaging over labels -/

section Average

variable {J : Type*} [Fintype J]

/-- The equal-weight average `(1/|J|) · ∑_j v_j` of a finite family of extended reals: the
procession-normalization of Proposition 3.9 (i), page 116 ("the average, over the various
capsules"). -/
noncomputable def average (v : J → EReal) : EReal :=
  (((Fintype.card J : ℝ)⁻¹ : ℝ) : EReal) * ∑ j, v j

theorem average_mono {v w : J → EReal} (h : ∀ j, v j ≤ w j) : average v ≤ average w :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => h j)
    (EReal.coe_nonneg.mpr (inv_nonneg.mpr (Nat.cast_nonneg _)))

theorem average_ne_bot {v : J → EReal} (h : ∀ j, v j ≠ ⊥) : average v ≠ ⊥ := by
  have hs : ∑ j, v j ≠ ⊥ :=
    Finset.sum_induction _ (· ≠ ⊥) (fun _ _ ha hb => EReal.add_ne_bot_iff.mpr ⟨ha, hb⟩)
      (by simp) fun j _ => h j
  exact (EReal.mul_ne_bot _ _).mpr ⟨Or.inl (EReal.coe_ne_bot _), Or.inr hs,
    Or.inl (EReal.coe_ne_top _),
    Or.inl (EReal.coe_nonneg.mpr (inv_nonneg.mpr (Nat.cast_nonneg _)))⟩

theorem average_ne_top {v : J → EReal} (h : ∀ j, v j ≠ ⊤) : average v ≠ ⊤ := by
  have hs : ∑ j, v j ≠ ⊤ :=
    Finset.sum_induction _ (· ≠ ⊤) (fun _ _ ha hb => EReal.add_ne_top ha hb)
      (by simp) fun j _ => h j
  exact (EReal.mul_ne_top _ _).mpr ⟨Or.inl (EReal.coe_ne_bot _),
    Or.inl (EReal.coe_nonneg.mpr (inv_nonneg.mpr (Nat.cast_nonneg _))),
    Or.inl (EReal.coe_ne_top _), Or.inr hs⟩

variable {X : J → Type*} [∀ j, MeasurableSpace (X j)] {ι : Type*}
  (S : ∀ j, ComparisonSetting (X j) ι)

/-- The averaged log-volume of the hulls of the unions: `− |log(Θ)|` with the
procession-normalization. -/
noncomputable def procThetaLogVolume : EReal := average fun j => (S j).thetaLogVolume

/-- The averaged log-volume of the q-pilot regions: `− |log(q)|` with the
procession-normalization. -/
noncomputable def procQLogVolume : EReal := average fun j => (S j).qLogVolume

/-- Region form of the comparison for a family of components: componentwise containment.
Page 174 writes regions as collections indexed by `(j, v_Q)` and their containment
componentwise. Not proved here; see `ComparisonSetting.Containment`. -/
def ProcContainment : Prop := ∀ j, (S j).Containment

/-- Numerical form of the comparison with the procession-normalization:
`− |log(q)| ≤ − |log(Θ)|` for the averaged log-volumes (Step (xi-f), page 184). -/
def ProcLogVolumeComparison : Prop := procQLogVolume S ≤ procThetaLogVolume S

theorem procLogVolumeComparison_of_procContainment (h : ProcContainment S) :
    ProcLogVolumeComparison S :=
  average_mono fun j => (S j).logVolumeComparison_of_containment (h j)

/-- The two numbers of Corollary 3.12 with the procession-normalization. Hypotheses: each
q-pilot component has measure in `(0, ∞)` and the averaged q-side log-volume is negative
(`|log(q)| > 0`, page 174); each hull component has positive measure. -/
noncomputable def procPilotLogVolumes (hq : ∀ j, (S j).μ (S j).qPilot ≠ 0 ∧
      (S j).μ (S j).qPilot ≠ ⊤) (hneg : procQLogVolume S < 0)
    (hΘ : ∀ j, (S j).μ (S j).hullOfUnion ≠ 0) : PilotLogVolumes :=
  PilotLogVolumes.ofLogVolumes (procQLogVolume S) (procThetaLogVolume S)
    (average_ne_bot fun j => (logVolume_eq_bot_iff _ _).not.mpr (hq j).1) hneg
    (average_ne_bot fun j => (logVolume_eq_bot_iff _ _).not.mpr (hΘ j))

/-- **Bridge with averaging (conditional).** Componentwise containment of the q-pilot regions
in the hulls of the unions, and finiteness of each hull, give the conclusion of Corollary 3.12
for the procession-normalized numbers. Conditional on `hcont` (Theorem 3.11 and Steps (i) to
(xi), not formalized) and `hfin` (page 175, compactness, not formalized). -/
theorem conclusion_of_procContainment (hq : ∀ j, (S j).μ (S j).qPilot ≠ 0 ∧
      (S j).μ (S j).qPilot ≠ ⊤) (hneg : procQLogVolume S < 0)
    (hΘ : ∀ j, (S j).μ (S j).hullOfUnion ≠ 0) (hfin : ∀ j, (S j).μ (S j).hullOfUnion ≠ ⊤)
    (hcont : ProcContainment S) : Conclusion (procPilotLogVolumes S hq hneg hΘ) :=
  (PilotLogVolumes.conclusion_ofLogVolumes_iff _ _ _ _ _).mpr
    ⟨average_ne_top fun j => (logVolume_eq_top_iff _ _).not.mpr (hfin j),
      procLogVolumeComparison_of_procContainment S hcont⟩

end Average

/-! ## Nonvacuity: the interval hull on `ℝ` -/

namespace IntervalExample

/-- Bounded nonempty subsets of `ℝ`: the domain of the interval hull. -/
def domain : Set (Set ℝ) := {P | P.Nonempty ∧ BddBelow P ∧ BddAbove P}

/-- Nonempty closed bounded intervals: the hulls. -/
def hulls : Set (Set ℝ) := {H | ∃ a b, a ≤ b ∧ H = Icc a b}

/-- The interval hull `P ↦ [inf P, sup P]`. -/
noncomputable def hull (P : Set ℝ) : Set ℝ := Icc (sInf P) (sSup P)

/-- The interval hull satisfies (P1), (P2), (P3) of Remark 3.9.5 (ii). -/
theorem isHullMap : IsHullMap domain hulls hull where
  hull_sub := by
    rintro _ ⟨a, b, hab, rfl⟩
    exact ⟨nonempty_Icc.mpr hab, bddBelow_Icc, bddAbove_Icc⟩
  maps_to P hP := ⟨_, _, csInf_le_csSup hP.1 hP.2.1 hP.2.2, rfl⟩
  P1 := by
    rintro _ ⟨a, b, hab, rfl⟩
    simp only [hull, csInf_Icc hab, csSup_Icc hab]
  P2 P hP _ hx := ⟨csInf_le hP.2.1 hx, le_csSup hP.2.2 hx⟩
  P3 P₁ h₁ P₂ h₂ h := Icc_subset_Icc (csInf_le_csInf h₂.2.1 h₁.1 h) (csSup_le_csSup h₂.2.2 h₁.1 h)

/-- The two possible images `[0, 1/8]` and `[3/8, 1/2]`, indexed by `Bool`. -/
noncomputable def image : Bool → Set ℝ
  | false => Icc 0 (1 / 8)
  | true => Icc (3 / 8) (1 / 2)

theorem union_eq : (⋃ i, image i) = Icc 0 (1 / 8) ∪ Icc (3 / 8) (1 / 2) := by
  ext x; simp [image]

theorem hull_union : hull (⋃ i, image i) = Icc 0 (1 / 2) := by
  rw [union_eq, hull]
  have hL : IsLeast (Icc (0 : ℝ) (1 / 8) ∪ Icc (3 / 8) (1 / 2)) 0 :=
    ⟨Or.inl ⟨le_rfl, by norm_num⟩, by
      rintro x (hx | hx) <;> [exact hx.1; linarith [hx.1]]⟩
  have hG : IsGreatest (Icc (0 : ℝ) (1 / 8) ∪ Icc (3 / 8) (1 / 2)) (1 / 2) :=
    ⟨Or.inr ⟨by norm_num, le_rfl⟩, by
      rintro x (hx | hx) <;> [linarith [hx.2]; exact hx.2]⟩
  rw [hL.csInf_eq, hG.csSup_eq]

/-- The setting on `ℝ` with Lebesgue measure, the interval hull, the two possible images above,
and a q-pilot region `q`. -/
noncomputable def setting (q : Set ℝ) : ComparisonSetting ℝ Bool where
  μ := volume
  hullDomain := domain
  hulls := hulls
  hull := hull
  isHullMap := isHullMap
  qPilot := q
  image := image
  union_mem := by
    rw [union_eq]
    exact ⟨⟨0, Or.inl ⟨le_rfl, by norm_num⟩⟩, bddBelow_Icc.union bddBelow_Icc,
      bddAbove_Icc.union bddAbove_Icc⟩

theorem setting_hullOfUnion (q : Set ℝ) : (setting q).hullOfUnion = Icc 0 (1 / 2) :=
  hull_union

theorem volume_hullOfUnion (q : Set ℝ) :
    (setting q).μ (setting q).hullOfUnion = ENNReal.ofReal (1 / 2) := by
  rw [setting_hullOfUnion]
  simp [setting, Real.volume_Icc]

/-- **Nonvacuity (a).** With q-pilot region `[0, 1/2]`, every hypothesis of the region-form
bridge holds: `0 < μ q < 1`, the hull of the union has finite positive measure, and the
q-pilot region is contained in it. Hence `conclusion_of_containment` applies. -/
theorem example_bridge_hypotheses :
    (setting (Icc 0 (1 / 2))).μ (setting (Icc 0 (1 / 2))).qPilot ≠ 0 ∧
    (setting (Icc 0 (1 / 2))).μ (setting (Icc 0 (1 / 2))).qPilot < 1 ∧
    (setting (Icc 0 (1 / 2))).μ (setting (Icc 0 (1 / 2))).hullOfUnion ≠ 0 ∧
    (setting (Icc 0 (1 / 2))).μ (setting (Icc 0 (1 / 2))).hullOfUnion ≠ ⊤ ∧
    (setting (Icc 0 (1 / 2))).Containment := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [setting, Real.volume_Icc]
  · simp only [setting, Real.volume_Icc]
    rw [ENNReal.ofReal_lt_one]; norm_num
  · rw [volume_hullOfUnion]; simp
  · rw [volume_hullOfUnion]; exact ENNReal.ofReal_ne_top
  · show Icc 0 (1 / 2) ⊆ (setting _).hullOfUnion
    rw [setting_hullOfUnion]

/-- The conclusion of Corollary 3.12 for the numbers of example (a), obtained from the bridge. -/
theorem example_conclusion :
    ∃ v : PilotLogVolumes, Conclusion v := by
  obtain ⟨h0, h1, -, hfin, hc⟩ := example_bridge_hypotheses
  exact ⟨_, (setting _).conclusion_of_containment h0 h1 hfin hc⟩

/-- **Nonvacuity (b): the comparison is an extra condition.** With q-pilot region `[0, 3/4]`,
every field of the setting and every side hypothesis of the bridge holds (`0 < μ q < 1`, the
hull of the union has finite positive measure), but `LogVolumeComparison` fails, hence also
`Containment`, and the conclusion of Corollary 3.12 is false for the numbers so defined. -/
theorem example_comparison_fails :
    ∃ (hq0 : (setting (Icc 0 (3 / 4))).μ (setting (Icc 0 (3 / 4))).qPilot ≠ 0)
      (hq1 : (setting (Icc 0 (3 / 4))).μ (setting (Icc 0 (3 / 4))).qPilot < 1)
      (hΘ : (setting (Icc 0 (3 / 4))).μ (setting (Icc 0 (3 / 4))).hullOfUnion ≠ 0),
      (setting (Icc 0 (3 / 4))).μ (setting (Icc 0 (3 / 4))).hullOfUnion ≠ ⊤ ∧
      ¬ (setting (Icc 0 (3 / 4))).LogVolumeComparison ∧
      ¬ (setting (Icc 0 (3 / 4))).Containment ∧
      ¬ Conclusion ((setting (Icc 0 (3 / 4))).toPilotLogVolumes hq0 hq1 hΘ) := by
  have hcomp : ¬ (setting (Icc 0 (3 / 4))).LogVolumeComparison := by
    simp only [ComparisonSetting.LogVolumeComparison, ComparisonSetting.qLogVolume,
      ComparisonSetting.thetaLogVolume, logVolume, ENNReal.log_le_log_iff,
      volume_hullOfUnion]
    simp only [setting, Real.volume_Icc, not_le]
    rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]; norm_num
  refine ⟨by simp [setting, Real.volume_Icc], ?_, by rw [volume_hullOfUnion]; simp,
    by rw [volume_hullOfUnion]; exact ENNReal.ofReal_ne_top, hcomp,
    fun h => hcomp ((setting _).logVolumeComparison_of_containment h), ?_⟩
  · simp only [setting, Real.volume_Icc]
    rw [ENNReal.ofReal_lt_one]; norm_num
  · intro h
    exact hcomp (((setting _).conclusion_iff _ _ _).mp h).2

/-- **Nonvacuity (c): the union and the hull matter.** With q-pilot region `[0, 1/2]`: the hull
of no single possible image contains the q-pilot region, nor does any single image satisfy the
numerical comparison with its own hull; the union itself does not contain the q-pilot region;
but the hull of the union does. -/
theorem example_union_matters :
    (∀ i, ¬ Icc (0 : ℝ) (1 / 2) ⊆ hull (image i)) ∧
    (∀ i, ¬ logVolume volume (Icc (0 : ℝ) (1 / 2)) ≤ logVolume volume (hull (image i))) ∧
    ¬ Icc (0 : ℝ) (1 / 2) ⊆ ⋃ i, image i ∧
    (setting (Icc 0 (1 / 2))).Containment := by
  have himg : ∀ i, hull (image i) = image i := fun i => by
    cases i
    · exact isHullMap.P1 _ ⟨0, 1 / 8, by norm_num, rfl⟩
    · exact isHullMap.P1 _ ⟨3 / 8, 1 / 2, by norm_num, rfl⟩
  refine ⟨fun i h => ?_, fun i h => ?_, fun h => ?_, ?_⟩
  · rw [himg] at h
    cases i
    · have := (h ⟨by norm_num, le_rfl⟩ : (1 / 2 : ℝ) ∈ Icc 0 (1 / 8)).2; norm_num at this
    · have := (h ⟨le_rfl, by norm_num⟩ : (0 : ℝ) ∈ Icc (3 / 8) (1 / 2)).1; norm_num at this
  · rw [himg, logVolume, logVolume, ENNReal.log_le_log_iff] at h
    cases i <;>
    · simp only [image, Real.volume_Icc] at h
      rw [ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h
      norm_num at h
  · rw [union_eq] at h
    rcases h (⟨by norm_num, by norm_num⟩ : (1 / 4 : ℝ) ∈ Icc 0 (1 / 2)) with h | h
    · norm_num at h
    · norm_num at h
  · exact example_bridge_hypotheses.2.2.2.2

end IntervalExample

end IUT.PaperIII.Corollary312
