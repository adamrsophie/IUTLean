import IUT.PaperIII.Corollary312.Numerical
import IUT.PaperIII.Remark3_9_5.HullOperator

/-!
# IUT III, Corollary 3.12: an interface for the final comparison of regions

Source: Mochizuki, *Inter-universal Teichmüller Theory III*, Corollary 3.12 and Steps (x) to
(xii) of its proof, pages 173 to 186; Proposition 3.9, pages 115 to 118; Remark 3.9.5 (i) to
(iv), pages 126 to 129; Remark 3.1.1 (iii), (iv), pages 95 to 97; Remark 3.9.5 (vii), pages 132
and 133; IUT IV, Proposition 1.4 (i), page 13. Pages read for this file from the extracted
text: 115 to 118, 125 to 129, 173 to 175, 180 to 186. Pages checked against rendered images:
IUT III 95 to 97, 115 to 117, 127, 132, 133, 173 to 175, 181 to 185; IUT IV 13. Pages 118, 125,
126, 128, 129, 180 and 186 were read in text only; no formula of this file is taken from them.

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

* `RegionComparison X ι`: data only. A family `𝓟` of regions on which a hull is defined, a
  family `𝓗` of hulls, a hull map with the properties (P1), (P2), (P3) of Remark 3.9.5 (ii)
  (`IsHullMap` from `HullOperator.lean`), an **abstract region log-volume**
  `logVol : Set X → EReal` with one property of the function (monotone into `𝓟`), the q-pilot
  region, and a family of possible images indexed by an arbitrary type `ι` (the indeterminacy
  data). One regularity field: the union of the possible images lies in `𝓟`. The bridge is
  proved at this level (`RegionComparison.conclusion_of_containment`).
* `logVolume μ S = ENNReal.log (μ S)`: the log-volume of a region for a measure, with
  `log 0 = −∞` and `log ∞ = +∞` (Mathlib's `ENNReal.log`). It is monotone, and finite exactly
  when `0 < μ S < ∞`.
* `ComparisonSetting X ι`: the measure instance, with `logVol = logVolume μ`
  (`ComparisonSetting.toRegionComparison`). Its theorems are the `RegionComparison` ones
  specialized; the interval examples below use it.
* `Containment` (region form) and `LogVolumeComparison` (numerical form) of the comparison,
  as separate `Prop`s on a setting; `logVolumeComparison_of_containment`.
* The bridge to `Numerical.lean`: `toPilotLogVolumes`, `conclusion_iff` (the conclusion is the
  conjunction of finiteness and `LogVolumeComparison`; nothing derived) and
  `conclusion_of_containment` (the inequality derived from containment, a sufficient
  condition; finiteness assumed).
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
   (archimedean), determined by the normalized weights of Remark 3.1.1, and normalized so that
   the integral structure has log-volume `0` and multiplication by `p_v` adds `−log(p_v)`
   (multiplication by `e` adds `1`). IUT IV, Proposition 1.4 (i), page 13, obtains such a
   normalization by dividing by the degree of the finite extension. Remark 3.1.1 (iii), page
   95, warns that weighted sums of log-volumes do not in general arise as a positive multiple
   of the logarithm of a measure; (iv), pages 96 and 97, computes them on direct product
   regions as `(1/N_E)` times the logarithm of an `E`-weighted measure on another space. So
   the bridge is stated for an abstract `logVol`, and `log μ` is one instance. Here a region
   is an arbitrary subset.
2. *Normalization is not modeled.* No field or hypothesis fixes the log-volume of an integral
   structure or the scaling law. The hypothesis `μ qPilot < 1` of the measure instance (and
   `qLogVolume < 0` in general) is only the sign condition `|log(q)| > 0` of page 174:
   replacing a q-pilot region of mass `1/4` by one of mass `1/2` keeps it and changes the
   number. A normalized weighted packet log-volume would need: a log-volume on each direct
   summand normalized at the integral structure (Proposition 3.9 (i), pages 115 and 116), the
   weights of Remark 3.1.1 (ii), (iv), and, for comparison with the q-pilot object, the
   determinant raised to a positive tensor power `det_{⊗M}` with the normalization by `O_(−)`
   of Remark 3.9.5 (vii), (Ob3-1) to (Ob3), pages 132 and 133, where the details are left to
   the reader. Constructing it is open.
3. *The domain of the hull.* Remark 3.9.5 (i), page 127, defines the hull of any subset that
   contains a relatively compact subset of finite log-volume; (ii) states (P1) to (P3) on the
   set `ℙ` of direct product regions. The paper does not say that the union of the possible
   images is a direct product region. The field `union_mem` takes `𝓟` to be a family on which
   (P1) to (P3) hold and which contains the union; this is a choice.
4. *Possible images.* Page 174 defines `n,◦U_{j,v_Q}` as the union of the possible images of a
   Θ-pilot object subject to (Ind1), (Ind2), (Ind3), without a formula for the set of possible
   images. Here that set is an arbitrary indexed family `image : ι → Set X`; how (Ind1), (Ind2),
   (Ind3) generate it is not modeled.
5. *Signs.* The symbol `− |log(Θ)|` is a name for the log-volume of the hull of the union, not
   the negative of an absolute value: `negLogTheta` is that log-volume itself. The symbol
   `− |log(q)|` is the log-volume of the q-pilot region, so `absLogQ` is minus that log-volume.
6. *Which form the text asserts.* In the reading adopted here, the text never asserts a containment of
   regions. Steps (xi-c) and (xi-d), pages 182 and 183, say that the possible output data in
   `1,◦Ū` are "linked/related" to the representation of the q-pilot object via isomorphisms of
   `F^{⊩▶}`-prime-strips. Step (xi-f), page 184, asserts the numerical inclusion
   `− |log(q)| ∈ ℝ_{≤ −|log(Θ)|}`. So `LogVolumeComparison` is what the text asserts, and
   `Containment` is a region-level sufficient condition, not a quotation.
7. *Averaging.* The statement (page 173) and Step (x) (page 181, rendered) average over
   `j ∈ 𝔽_l^⊛`; page 174 indexes the regions by `j ∈ |𝔽_l|`, and Step (xi-d), page 183,
   normalizes "with respect to `j ∈ |𝔽_l|`". Proposition 3.9 (i), page 116, defines the
   procession-normalization as "the average, over the various capsules". The average here is
   uniform over an arbitrary finite index type `J` (on an empty `J` the formula gives `0`,
   a value that no theorem uses, see `average`); the statement itself averages over
   `𝔽_l^⊛` with factor `1 / l^⊛` (pages 173 and 181); the file keeps `J` general.

## What the interface omits, and what could be added next

* *The sum over places `v_Q ∈ 𝕍_ℚ`* (Proposition 3.9 (iii), page 117): typed in
  `Places.lean`, for the measure instance.
* *The procession structure.* The labels `j` index capsules of a procession, and the packet at
  `j` is a tensor product over `j + 1` labels. Only the equal-weight average over `j` is here;
  `LabelAverage.lean` instantiates it at `𝔽_l^⋇` with factor `1/l^⋇`.
* *The identification of the two sides through the `Θ^{×μ}_{LGP}`-link* (Step (xi-a), page
  181) and through the permutation symmetry `0,◦U ≅ 1,◦U` (Step (xi-b), page 181). Here both
  regions live in one space `X` with one log-volume `logVol`; that they can be placed there
  with a common log-volume is assumed by the typing, not proved. This is where
  `IUT.Countermodels.Comparison` shows some compatibility is indispensable.
* *Tensor packets, determinants and the tensor power of Step (xi-d)*, page 183, and the
  normalization of the log-volume (interpretation choice 2); not modeled.
* *The indeterminacies themselves.* Here the family `image` is arbitrary. `Indeterminacy.lean`
  generates it as an orbit under the subgroup generated by two subgroups standing for (Ind1)
  and (Ind2), with invariance of log-volume as a hypothesis; (Ind3) is not typed there.
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

/-! ## The setting with an abstract region log-volume -/

/-- The data for the last step of the proof of Corollary 3.12, for one component, with an
abstract log-volume of regions.

This is **not** the paper's situation: none of the fields is constructed from Hodge theaters
or the multiradial representation. The region log-volume `logVol` is an arbitrary function
with values in `EReal`; it need not be the logarithm of a measure (Remark 3.1.1 (iii), page
95: weighted sums of log-volumes are in general not a multiple of the logarithm of a measure).
The fields are data, the hull axioms, one monotonicity property of `logVol`, and one
well-posedness condition. No field relates the q-pilot region to the possible images. -/
structure RegionComparison (X : Type*) (ι : Type*) where
  /-- The regions to which the hull applies (`ℙ` of Remark 3.9.5 (ii), page 127). -/
  hullDomain : Set (Set X)
  /-- The hulls (`ℍ` of Remark 3.9.5 (ii), page 127). -/
  hulls : Set (Set X)
  /-- The hull map `φ : ℙ → ℍ` of Remark 3.9.5 (ii). -/
  hull : Set X → Set X
  /-- (P1), (P2), (P3) of Remark 3.9.5 (ii), page 127, together with `ℍ ⊆ ℙ`. -/
  isHullMap : IsHullMap hullDomain hulls hull
  /-- The log-volume of a region. -/
  logVol : Set X → EReal
  /-- Monotonicity of `logVol` into the hull domain: a region contained in a member of the
  hull domain has at most its log-volume. A property of the function `logVol`, required so
  that containment of regions gives an inequality of log-volumes; it holds for `log` of any
  measure (`ComparisonSetting.toRegionComparison`). -/
  logVol_mono : ∀ S T : Set X, S ⊆ T → T ∈ hullDomain → logVol S ≤ logVol T
  /-- The region representing the q-pilot object (`1,◦U^ℚ` side, Step (xi-d), page 183). -/
  qPilot : Set X
  /-- The possible images of a Θ-pilot object, indexed by the indeterminacy data (page 174). -/
  image : ι → Set X
  /-- The hull of the union is defined: the union lies in the domain of the hull map (an
  interpretation choice; see the module docstring). -/
  union_mem : (⋃ i, image i) ∈ hullDomain

namespace RegionComparison

variable {X : Type*} {ι : Type*} (S : RegionComparison X ι)

/-- The union of the possible images (`n,◦U`, page 174). -/
def unionImages : Set X := ⋃ i, S.image i

/-- The hull of the union of the possible images (`n,◦Ū`, pages 174 and 175). -/
def hullOfUnion : Set X := S.hull S.unionImages

theorem hullOfUnion_mem : S.hullOfUnion ∈ S.hullDomain :=
  S.isHullMap.hull_sub (S.isHullMap.maps_to _ S.union_mem)

/-- The log-volume of the hull of the union: the quantity named `− |log(Θ)|` (page 173). -/
def thetaLogVolume : EReal := S.logVol S.hullOfUnion

/-- The log-volume of the q-pilot region: the quantity named `− |log(q)|` (page 174). -/
def qLogVolume : EReal := S.logVol S.qPilot

/-- Each possible image lies in the hull of the union, by (P2). -/
theorem image_subset_hullOfUnion (i : ι) : S.image i ⊆ S.hullOfUnion :=
  (subset_iUnion S.image i).trans (S.isHullMap.P2 _ S.union_mem)

/-- Each possible image has log-volume at most that of the hull of the union. -/
theorem logVol_image_le (i : ι) : S.logVol (S.image i) ≤ S.thetaLogVolume :=
  S.logVol_mono _ _ (S.image_subset_hullOfUnion i) S.hullOfUnion_mem

/-- **Comparison, region form.** The q-pilot region is contained in the hull of the union of
the possible images. The text does not assert this (see `LogVolumeComparison`); it is a
sufficient condition, **not** formalized here. -/
def Containment : Prop := S.qPilot ⊆ S.hullOfUnion

/-- **Comparison, numerical form.** `− |log(q)| ≤ − |log(Θ)|`. This is what Step (xi-f),
page 184, asserts; it is **not** formalized here. Once the two numbers are defined from a
setting it is the second conjunct of `Conclusion` (see `conclusion_iff`). -/
def LogVolumeComparison : Prop := S.qLogVolume ≤ S.thetaLogVolume

/-- The region form implies the numerical form, by monotonicity of `logVol`. -/
theorem logVolumeComparison_of_containment (h : S.Containment) : S.LogVolumeComparison :=
  S.logVol_mono _ _ h S.hullOfUnion_mem

/-- The region form through the hull axioms: the q-pilot region lies in the hull of the union
exactly when it lies in every hull that contains all possible images. -/
theorem containment_iff_forall_hull :
    S.Containment ↔ ∀ H ∈ S.hulls, (∀ i, S.image i ⊆ H) → S.qPilot ⊆ H := by
  unfold Containment hullOfUnion unionImages
  rw [S.isHullMap.eq_sInter S.union_mem, subset_sInter_iff]
  exact ⟨fun h H hH hU => h H ⟨hH, iUnion_subset hU⟩,
    fun h H hH => h H hH.1 fun i => (subset_iUnion S.image i).trans hH.2⟩

end RegionComparison

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

namespace RegionComparison

variable {X : Type*} {ι : Type*} (S : RegionComparison X ι)

/-- The two numbers of Corollary 3.12 defined from a setting: `− |log(Θ)|` is the log-volume
of the hull of the union, `|log(q)|` is minus the log-volume of the q-pilot region. The
hypotheses `hq`, `hneg` say that `− |log(q)|` is real and negative (`|log(q)| > 0`, page
174); `hΘ` says `− |log(Θ)| ≠ −∞` (value set `ℝ ∪ {+∞}`, page 173). -/
noncomputable def toPilotLogVolumes (hq : S.qLogVolume ≠ ⊥) (hneg : S.qLogVolume < 0)
    (hΘ : S.thetaLogVolume ≠ ⊥) : PilotLogVolumes :=
  PilotLogVolumes.ofLogVolumes S.qLogVolume S.thetaLogVolume hq hneg hΘ

/-- **The conclusion is the conjunction of two assumptions here.** For the numbers defined from
a setting, the conclusion of Corollary 3.12 (page 174) is exactly the conjunction of its two
conjuncts: finiteness of `− |log(Θ)|` and `LogVolumeComparison`. Nothing is derived: the
statement only unfolds definitions. -/
theorem conclusion_iff (hq : S.qLogVolume ≠ ⊥) (hneg : S.qLogVolume < 0)
    (hΘ : S.thetaLogVolume ≠ ⊥) :
    Conclusion (S.toPilotLogVolumes hq hneg hΘ) ↔
      S.thetaLogVolume ≠ ⊤ ∧ S.LogVolumeComparison :=
  PilotLogVolumes.conclusion_ofLogVolumes_iff _ _ _ _ _

/-- The conclusion from its own two conjuncts. The hypotheses `hfin` (finiteness of
`− |log(Θ)|`) and `hcomp` (the numerical inequality, asserted in Step (xi-f), page 184) **are**
the two conjuncts of the conclusion of Corollary 3.12 (page 174); this theorem derives
nothing and records only that no further hypothesis is involved. The one route below that
derives a conjunct is `conclusion_of_containment`. -/
theorem conclusion_of_logVolumeComparison (hq : S.qLogVolume ≠ ⊥) (hneg : S.qLogVolume < 0)
    (hΘ : S.thetaLogVolume ≠ ⊥) (hfin : S.thetaLogVolume ≠ ⊤)
    (hcomp : S.LogVolumeComparison) : Conclusion (S.toPilotLogVolumes hq hneg hΘ) :=
  (S.conclusion_iff hq hneg hΘ).mpr ⟨hfin, hcomp⟩

/-- **Bridge, region form (conditional).** Containment of the q-pilot region in the hull of the
union, and finiteness of the log-volume of that hull, give the conclusion of Corollary 3.12.
The inequality conjunct is derived from `hcont` by monotonicity of `logVol`; finiteness is
assumed. Containment is a sufficient condition, not what the text asserts: Step (xi-f),
page 184, asserts the numerical inclusion `− |log(q)| ∈ ℝ_{≤ −|log(Θ)|}`. Both `hcont` and
`hfin` are unproved hypotheses. `− |log(Θ)| ≠ −∞` is derived from `hcont` and `hq`. -/
theorem conclusion_of_containment (hq : S.qLogVolume ≠ ⊥) (hneg : S.qLogVolume < 0)
    (hfin : S.thetaLogVolume ≠ ⊤) (hcont : S.Containment) :
    Conclusion (S.toPilotLogVolumes hq hneg
      (ne_bot_of_le_ne_bot hq (S.logVolumeComparison_of_containment hcont))) :=
  S.conclusion_of_logVolumeComparison _ _ _ hfin (S.logVolumeComparison_of_containment hcont)

end RegionComparison

/-! ## The measure instance -/

/-- The data of `RegionComparison` with the log-volume `log (μ S)` of one measure `μ`.

This is **not** the paper's situation; see `RegionComparison`. The paper's packet log-volumes
are weighted sums (Remark 3.1.1 (ii) to (iv), pages 94 to 97) and need not have this form. -/
structure ComparisonSetting (X : Type*) [MeasurableSpace X] (ι : Type*) where
  /-- The measure whose logarithm is the log-volume. -/
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
  finite log-volume; the setting has no topology, and that the union lies in `hullDomain` is
  an interpretation choice (see the module docstring). -/
  union_mem : (⋃ i, image i) ∈ hullDomain

namespace ComparisonSetting

variable {X : Type*} [MeasurableSpace X] {ι : Type*} (S : ComparisonSetting X ι)

/-- The measure setting as a `RegionComparison` with `logVol S = log (μ S)`. -/
noncomputable def toRegionComparison : RegionComparison X ι where
  hullDomain := S.hullDomain
  hulls := S.hulls
  hull := S.hull
  isHullMap := S.isHullMap
  logVol := logVolume S.μ
  logVol_mono _ _ h _ := logVolume_mono S.μ h
  qPilot := S.qPilot
  image := S.image
  union_mem := S.union_mem

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
  S.toRegionComparison.image_subset_hullOfUnion i

/-- **Comparison, region form.** The q-pilot region is contained in the hull of the union of
the possible images. In the reading adopted here the text does not assert this; see
`LogVolumeComparison`. It is a sufficient condition for the numerical form
(`logVolumeComparison_of_containment`); **not** formalized here. -/
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
  S.toRegionComparison.logVolumeComparison_of_containment h

/-- The region form, through the hull axioms: the q-pilot region lies in the hull of the union
exactly when it lies in every hull that contains all possible images. -/
theorem containment_iff_forall_hull :
    S.Containment ↔ ∀ H ∈ S.hulls, (∀ i, S.image i ⊆ H) → S.qPilot ⊆ H :=
  S.toRegionComparison.containment_iff_forall_hull

/-- The two numbers of Corollary 3.12 defined from a measure setting: `− |log(Θ)|` is the
log-volume of the hull of the union, `|log(q)|` is minus the log-volume of the q-pilot region.

Hypotheses: `hq0`, `hq1`: `0 < μ qPilot < 1`, i.e. `− |log(q)|` is real and negative. This is
the sign condition `|log(q)| > 0` of page 174 and nothing more: it fixes no normalization
(see the module docstring). `hΘ`: the hull of the union has positive measure, i.e.
`− |log(Θ)| ≠ −∞` (value set `ℝ ∪ {+∞}`, page 173). -/
noncomputable def toPilotLogVolumes (hq0 : S.μ S.qPilot ≠ 0) (hq1 : S.μ S.qPilot < 1)
    (hΘ : S.μ S.hullOfUnion ≠ 0) : PilotLogVolumes :=
  S.toRegionComparison.toPilotLogVolumes ((logVolume_eq_bot_iff _ _).not.mpr hq0)
    ((logVolume_neg_iff _ _).mpr hq1) ((logVolume_eq_bot_iff _ _).not.mpr hΘ)

/-- **The conclusion is the conjunction of two assumptions here.** For the numbers defined from
a measure setting, the conclusion of Corollary 3.12 (page 174) is exactly finiteness of the
measure of the hull of the union together with `LogVolumeComparison`: these are its two
conjuncts, and nothing is derived. -/
theorem conclusion_iff (hq0 : S.μ S.qPilot ≠ 0) (hq1 : S.μ S.qPilot < 1)
    (hΘ : S.μ S.hullOfUnion ≠ 0) :
    Conclusion (S.toPilotLogVolumes hq0 hq1 hΘ) ↔
      S.μ S.hullOfUnion ≠ ⊤ ∧ S.LogVolumeComparison := by
  refine (S.toRegionComparison.conclusion_iff _ _ _).trans ?_
  show logVolume S.μ S.hullOfUnion ≠ ⊤ ∧ _ ↔ _
  rw [Ne, logVolume_eq_top_iff]
  rfl

/-- The conclusion from its own two conjuncts. The hypotheses `hfin` (the hull of the union has
finite measure, i.e. `− |log(Θ)| ∈ ℝ`) and `hcomp` (the numerical inequality) **are** the two
conjuncts of the conclusion of Corollary 3.12 (page 174); this theorem derives nothing.

* `hfin`: the paper argues finiteness on page 175 from "the [easily verified] compactness" of
  the `1,◦U_{j,v_Q}`; the setting has no topology, so here finiteness is a separate
  hypothesis on the measure. Not formalized.
* `hcomp`: asserted by Step (xi-f), page 184, from Theorem 3.11; not formalized.

The only route here that derives the inequality conjunct is `conclusion_of_containment`. -/
theorem conclusion_of_logVolumeComparison (hq0 : S.μ S.qPilot ≠ 0) (hq1 : S.μ S.qPilot < 1)
    (hΘ : S.μ S.hullOfUnion ≠ 0) (hfin : S.μ S.hullOfUnion ≠ ⊤)
    (hcomp : S.LogVolumeComparison) : Conclusion (S.toPilotLogVolumes hq0 hq1 hΘ) :=
  (S.conclusion_iff hq0 hq1 hΘ).mpr ⟨hfin, hcomp⟩

/-- **Bridge, region form (conditional).** If the q-pilot region is contained in the hull of
the union of the possible images, and that hull has finite measure, then the conclusion of
Corollary 3.12 holds for the numbers defined from the setting. The inequality conjunct is
derived from `hcont`; finiteness is assumed.

Conditional on two unproved hypotheses:
* `hcont`: the region form of the comparison, a sufficient condition and not what the text
  asserts (Step (xi-f), page 184, asserts a numerical inclusion); in the paper the comparison
  rests on Theorem 3.11 and Steps (i) to (xi);
* `hfin`: finite measure of the hull of the union; the paper argues finiteness on page 175
  from compactness of the `1,◦U_{j,v_Q}`, which has no counterpart in this setting.

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
capsules"). The paper's index set is nonempty. On an empty `J` the formula gives `0`
(`average_of_isEmpty`); no theorem below uses that value: the bridge assumes the averaged
q-side log-volume is negative, which excludes an empty `J` (`nonempty_of_average_neg`). -/
noncomputable def average (v : J → EReal) : EReal :=
  (((Fintype.card J : ℝ)⁻¹ : ℝ) : EReal) * ∑ j, v j

/-- On an empty index type the average is `0`, a value of the formula, not of the paper. -/
theorem average_of_isEmpty [IsEmpty J] (v : J → EReal) : average v = 0 := by
  simp [average]

/-- A negative average forces a nonempty index type. -/
theorem nonempty_of_average_neg {v : J → EReal} (h : average v < 0) : Nonempty J := by
  by_contra hJ
  rw [not_nonempty_iff] at hJ
  rw [average_of_isEmpty] at h
  exact lt_irrefl _ h

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

/-- Some value of `PilotLogVolumes` satisfies `Conclusion`. The statement is only this
existential: it does not name the witness and says nothing about example (a), and any `v` with
a finite nonnegative `negLogTheta` would also witness it. The proof uses the numbers of
example (a), through `conclusion_of_containment`, but that choice is not part of what is
stated. -/
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
