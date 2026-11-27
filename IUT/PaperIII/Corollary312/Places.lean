import IUT.PaperIII.Corollary312.Comparison

/-!
# IUT III, Corollary 3.12: the sum over places in the interface of the final comparison

Source: Mochizuki, *Inter-universal Teichmüller Theory III*, Remark 3.1.1 (ii) to (iv), pages
94 to 97; Proposition 3.9 (i) to (iii), pages 115 to 117; the statement of Corollary 3.12 and
the opening of its proof, pages 173 to 175; Step (xi-d), page 183. Pages read for this file:
94 to 97, 115 to 120, 173 to 175, 181 to 183. Pages checked against rendered images: 94 to 97,
116, 117, 173 to 175, 181, 183. Pages 115, 118, 119 and 120 were read in text only; no formula
of this file is taken from them.

## What this file is and is not

**This file is not a formalization of Corollary 3.12, nor of Proposition 3.9 (iii).** It adds
one feature to the interface of `Comparison.lean`: the passage from local log-volumes, one for
each place, to a global log-volume. As in `Comparison.lean`, no region is constructed from
initial Θ-data, Hodge theaters, the log-theta-lattice or the multiradial representation of
Theorem 3.11; every region and every measure is an input. The comparison of the q-pilot region
with the hull of the union of the possible images remains an **unproved hypothesis**, now
placewise (`PlacewiseContainment`) or global (`GlobalLogVolumeComparison`); nothing here gives
evidence for or against it.

## What the pages say

* Proposition 3.9 (iii), page 117 (rendered): on the families indexed by `v_Q ∈ 𝕍_ℚ` whose
  components have zero log-volume for all but finitely many `v_Q`, adding the local
  log-volumes of (i) ("all but finitely many of which are zero!") gives a global log-volume
  with values in `ℝ`.
* Proposition 3.9 (i), pages 115 and 116 (page 116 rendered): the local log-volumes are
  defined on nonempty compact open subsets (nonarchimedean) or compact closures of nonempty
  open subsets (archimedean), with values in `ℝ`, and are determined by the normalized weights
  of Remark 3.1.1 (ii), (iii), (iv).
* Remark 3.1.1 (ii), page 94 (rendered): the portion corresponding to `K_v` gets the weight
  `[K_v : (F_mod)_v]⁻¹`; a direct sum over the `v` above `v_Q` gets the normalized weight
  `1 / ([K_v : (F_mod)_v] · ∑_{w | v_Q} [(F_mod)_w : ℚ_{v_Q}])`, and tensor products over `A`
  get the analogous products. Remark 3.1.1 (iv), page 97 (rendered): for a direct product
  region `∏_v S_v`, `(1/N_E) · μ^log_E(S) = ∑_{v ∈ V} (1/N_v) · μ^log_v(S_v)`.

## What is typed

* `PlaceWeights P`: a positive real weight at each place of an index type `P`. Two readings
  are covered. If `P` is `𝕍_ℚ`, page 117 adds the local log-volumes with weight `1`
  (`unitPlaceWeights`), the weights of Remark 3.1.1 being already inside each local
  log-volume. If `P` is a set of places `v` lying over `𝕍_ℚ`, the weight at `v` is a normalized
  weight of Remark 3.1.1 (ii) or the `1/N_v` of (iv). Positivity is the one regularity field;
  each displayed weight on page 94 is the reciprocal of a positive number.
* `LogVolumeAlmostAllZero μ R`: the condition of page 117, "zero log-volume for all but
  finitely many" places, for a family of regions `R v` with measures `μ v`.
* `globalLogVolume w μ R = ∑ᶠ v, w v · log μ_v (R v)`, with value in `EReal`.
* Monotonicity under placewise containment (`globalLogVolume_mono`), finiteness when every
  local term is finite (`globalLogVolume_ne_bot`, `globalLogVolume_ne_top`), and the bridge to
  `Conclusion` (`conclusion_of_placewiseContainment`).
* Examples on two places, built from `IntervalExample.setting` of `Comparison.lean`: one where
  every hypothesis of the bridge holds, one where every structural hypothesis holds and the
  global comparison and the conclusion fail, and one where the global comparison holds while
  the placewise comparison fails at one place.

## The values `−∞` and `+∞`

The paper's local log-volumes are real (page 116: values in `ℝ` on `𝔐(−)`), so the paper's
hypotheses exclude `±∞` at every place, and the sum of page 117 is a finite sum of real
numbers. Here a local log-volume is `log` of an arbitrary measure (`logVolume` of
`Comparison.lean`), so it can be `−∞` (measure zero) or `+∞` (infinite measure). In `EReal`,
Mathlib's convention is `⊥ + ⊤ = ⊥` (`EReal.bot_add`): a sum containing both `−∞` and `+∞`
is `−∞`. Nothing below depends on that case being meaningful:

* `globalLogVolume_mono` holds in `EReal` with no finiteness hypothesis, because addition on
  `EReal` is monotone in each argument whatever the convention for `⊥ + ⊤`;
* finiteness of the global value is proved only from finiteness of each local term;
* the bridge assumes every q-pilot component has positive measure and every hull component
  has positive finite measure, so the case `⊥ + ⊤` does not arise on either side.

If the support condition `LogVolumeAlmostAllZero` fails, `∑ᶠ` returns `0` by Mathlib's
convention (`globalLogVolume_eq_zero_of_not_almostAllZero`).

## Limits

A global log-volume `0` does not mean that the local terms are small: with infinitely many
places and every local term negative, the value is `0`
(`globalLogVolume_infinite_support_example`). `globalLogVolume_mono` and the bridge
`conclusion_of_placewiseContainment` assume the support condition for both families. The
finiteness lemmas `globalLogVolume_ne_bot`, `globalLogVolume_ne_top`, `globalLogVolume_finite`
and the definitions `globalPilotLogVolumes`, `conclusion_globalPilotLogVolumes_iff` do not; on an
infinite support they are true because the value is `0`. In particular, if the hull family
violates the support condition, the conclusion of Corollary 3.12 holds for the global numbers as
soon as the global q-side log-volume is negative
(`conclusion_globalPilotLogVolumes_of_not_almostAllZero`): that case is an artifact of the
convention, not a comparison of regions. A use of these numbers that is meant to carry content
needs the support condition for the hull family (part (b) of the finiteness obligation).

## Interpretation choices

1. *Which places.* The index type `P` and the weights are arbitrary; the reading of page 117
   (`P = 𝕍_ℚ`, weight `1`) is the instance `unitPlaceWeights`. Remark 3.1.1 (iii), page 95,
   warns that weighted sums of log-volumes are not in general the logarithm of one measure;
   here only weighted sums of logarithms of measures, one measure per place, are formed, and
   no product measure is used. The local log-volume is the measure instance `logVolume` of
   `Comparison.lean`; the abstract `RegionComparison` there is not used here, and the
   normalization of the local log-volumes (Proposition 3.9 (i), pages 115 and 116) is not
   modeled.
2. *Placewise containment.* Page 174 writes the regions `n,◦U` and `n,◦Ū` as collections
   indexed by `(j, v_Q)` with `j ∈ |𝔽_l|` and `v_Q ∈ 𝕍_ℚ`, and their inclusions componentwise.
   `PlacewiseContainment` is that componentwise inclusion over the places. Step (xi-f),
   page 184, asserts only the global numerical inequality; `example_global_not_placewise`
   shows that the global inequality does not imply the placewise one.
3. *Labels and places together.* The procession-normalization (average over labels, see
   `LabelAverage.lean`) and the sum over places are typed separately. For finitely many labels
   and places of finite support the two operations commute; that is not stated here.

## What is still omitted

* No construction from initial Θ-data; the comparison is a hypothesis.
* Finiteness of the global value needs the support condition for the hull family; page 175
  argues finiteness from "the [easily verified] compactness" of the `1,◦U_{j,v_Q}`, which
  gives finiteness at each place but not the support condition; not formalized.
* Tensor packets, the identification of the two sides through the `Θ^{×μ}_{LGP}`-link and the
  permutation symmetry (Steps (xi-a), (xi-b), pages 181 and 182), and the determinant and
  tensor power normalization of Step (xi-d), page 183.
* The invariance of the global log-volume under multiplication by elements of `(M_MOD)_α` and
  its equality with an arithmetic degree (page 117).
-/

namespace IUT.PaperIII.Corollary312

open MeasureTheory Set

/-- A positive real weight at each place (Remark 3.1.1 (ii), (iv), pages 94 and 97; weight `1`
at each `v_Q` in the sum of Proposition 3.9 (iii), page 117). -/
structure PlaceWeights (P : Type*) where
  /-- The weight at a place. -/
  placeWeight : P → ℝ
  /-- Each weight displayed on page 94 is the reciprocal of a positive number. -/
  placeWeight_pos : ∀ v, 0 < placeWeight v

/-- The weights of Proposition 3.9 (iii), page 117: the local log-volumes at the various
`v_Q ∈ 𝕍_ℚ` are added, each with weight `1`. -/
def unitPlaceWeights (P : Type*) : PlaceWeights P := ⟨fun _ => 1, fun _ => one_pos⟩

section Global

variable {P : Type*} {X : P → Type*} [∀ v, MeasurableSpace (X v)]

/-- The condition of Proposition 3.9 (iii), page 117: the family has zero log-volume at all
but finitely many places. -/
def LogVolumeAlmostAllZero (μ : ∀ v, Measure (X v)) (R : ∀ v, Set (X v)) : Prop :=
  {v | logVolume (μ v) (R v) ≠ 0}.Finite

/-- The weighted local log-volume `w_v · log μ_v (R_v)` at a place. -/
noncomputable def weightedLocalLogVolume (w : PlaceWeights P) (μ : ∀ v, Measure (X v))
    (R : ∀ v, Set (X v)) (v : P) : EReal :=
  ((w.placeWeight v : ℝ) : EReal) * logVolume (μ v) (R v)

/-- The global log-volume `∑_v w_v · log μ_v (R_v)` (Proposition 3.9 (iii), page 117), as a
finite sum. It is meaningful under `LogVolumeAlmostAllZero`; otherwise `∑ᶠ` returns `0`.

Limits: the value `0` is ambiguous. It is returned whenever infinitely many local terms are
nonzero (`globalLogVolume_eq_zero_of_not_almostAllZero`), for instance when all of them are
negative (`globalLogVolume_infinite_support_example`). -/
noncomputable def globalLogVolume (w : PlaceWeights P) (μ : ∀ v, Measure (X v))
    (R : ∀ v, Set (X v)) : EReal :=
  ∑ᶠ v, weightedLocalLogVolume w μ R v

/-- **Limits: the value `0` on an infinite support.** If infinitely many local log-volumes are
nonzero, the global log-volume is `0`, Mathlib's value of `∑ᶠ` on an infinite support. -/
theorem globalLogVolume_eq_zero_of_not_almostAllZero (w : PlaceWeights P)
    {μ : ∀ v, Measure (X v)} {R : ∀ v, Set (X v)} (h : ¬ LogVolumeAlmostAllZero μ R) :
    globalLogVolume w μ R = 0 := by
  refine finsum_of_infinite_support fun hfin => h (hfin.subset fun v hv => ?_)
  have hw : ((w.placeWeight v : ℝ) : EReal) ≠ 0 := by
    exact_mod_cast (w.placeWeight_pos v).ne'
  exact Function.mem_support.mpr fun h0 => hv ((mul_eq_zero.mp h0).resolve_left hw)

/-- **Limits, an example.** On the places `ℕ` with unit weights, the region `[0, 1/2]` of
Lebesgue measure at every place has negative local log-volume at every place and global
log-volume `0`. -/
theorem globalLogVolume_infinite_support_example :
    logVolume (volume : Measure ℝ) (Icc 0 (1 / 2)) < 0 ∧
      globalLogVolume (unitPlaceWeights ℕ) (fun _ => (volume : Measure ℝ))
        (fun _ => Icc (0 : ℝ) (1 / 2)) = 0 := by
  have hneg : logVolume (volume : Measure ℝ) (Icc 0 (1 / 2)) < 0 := by
    rw [logVolume_neg_iff, Real.volume_Icc, ENNReal.ofReal_lt_one]; norm_num
  refine ⟨hneg, globalLogVolume_eq_zero_of_not_almostAllZero _ fun hfin => ?_⟩
  exact Set.infinite_univ (hfin.subset fun _ _ => hneg.ne)

theorem hasFiniteSupport_weightedLocalLogVolume (w : PlaceWeights P) {μ : ∀ v, Measure (X v)}
    {R : ∀ v, Set (X v)} (h : LogVolumeAlmostAllZero μ R) :
    Function.HasFiniteSupport (weightedLocalLogVolume w μ R) :=
  h.subset fun v hv h0 => hv (by simp only [weightedLocalLogVolume, h0, mul_zero])

/-- **Monotonicity.** Placewise containment of two families, both of zero log-volume at all but
finitely many places, gives the inequality of the global log-volumes. No finiteness is
needed. -/
theorem globalLogVolume_mono (w : PlaceWeights P) (μ : ∀ v, Measure (X v))
    {R R' : ∀ v, Set (X v)} (hR : LogVolumeAlmostAllZero μ R)
    (hR' : LogVolumeAlmostAllZero μ R') (h : ∀ v, R v ⊆ R' v) :
    globalLogVolume w μ R ≤ globalLogVolume w μ R' :=
  finsum_le_finsum (hasFiniteSupport_weightedLocalLogVolume w hR)
    (hasFiniteSupport_weightedLocalLogVolume w hR') fun v =>
      mul_le_mul_of_nonneg_left (logVolume_mono (μ v) (h v))
        (EReal.coe_nonneg.mpr (w.placeWeight_pos v).le)

/-- If no local log-volume is `−∞`, the global log-volume is not `−∞`. -/
theorem globalLogVolume_ne_bot (w : PlaceWeights P) {μ : ∀ v, Measure (X v)}
    {R : ∀ v, Set (X v)} (h : ∀ v, logVolume (μ v) (R v) ≠ ⊥) :
    globalLogVolume w μ R ≠ ⊥ :=
  finsum_induction (· ≠ ⊥) (by simp) (fun _ _ ha hb => EReal.add_ne_bot_iff.mpr ⟨ha, hb⟩)
    fun v => (EReal.mul_ne_bot _ _).mpr ⟨Or.inl (EReal.coe_ne_bot _), Or.inr (h v),
      Or.inl (EReal.coe_ne_top _),
      Or.inl (EReal.coe_nonneg.mpr (w.placeWeight_pos v).le)⟩

/-- If no local log-volume is `+∞`, the global log-volume is not `+∞`. -/
theorem globalLogVolume_ne_top (w : PlaceWeights P) {μ : ∀ v, Measure (X v)}
    {R : ∀ v, Set (X v)} (h : ∀ v, logVolume (μ v) (R v) ≠ ⊤) :
    globalLogVolume w μ R ≠ ⊤ :=
  finsum_induction (· ≠ ⊤) (by simp) (fun _ _ ha hb => EReal.add_ne_top ha hb)
    fun v => (EReal.mul_ne_top _ _).mpr ⟨Or.inl (EReal.coe_ne_bot _),
      Or.inl (EReal.coe_nonneg.mpr (w.placeWeight_pos v).le),
      Or.inl (EReal.coe_ne_top _), Or.inr (h v)⟩

/-- Finiteness: if every local log-volume is finite (`0 < μ_v (R_v) < ∞` at each place), the
global log-volume is a real number. -/
theorem globalLogVolume_finite (w : PlaceWeights P) {μ : ∀ v, Measure (X v)}
    {R : ∀ v, Set (X v)} (h0 : ∀ v, μ v (R v) ≠ 0) (htop : ∀ v, μ v (R v) ≠ ⊤) :
    globalLogVolume w μ R ≠ ⊥ ∧ globalLogVolume w μ R ≠ ⊤ :=
  ⟨globalLogVolume_ne_bot w fun v => (logVolume_eq_bot_iff _ _).not.mpr (h0 v),
    globalLogVolume_ne_top w fun v => (logVolume_eq_top_iff _ _).not.mpr (htop v)⟩

end Global

/-! ## The comparison over places -/

section Bridge

variable {P : Type*} {X : P → Type*} [∀ v, MeasurableSpace (X v)] {ι : P → Type*}
  (S : ∀ v, ComparisonSetting (X v) (ι v)) (w : PlaceWeights P)

/-- The global log-volume of the q-pilot family: `− |log(q)|` summed over places. -/
noncomputable def globalQLogVolume : EReal :=
  globalLogVolume w (fun v => (S v).μ) fun v => (S v).qPilot

/-- The global log-volume of the family of hulls of unions: `− |log(Θ)|` summed over places. -/
noncomputable def globalThetaLogVolume : EReal :=
  globalLogVolume w (fun v => (S v).μ) fun v => (S v).hullOfUnion

/-- Region form of the comparison over places: at every place, the q-pilot region lies in the
hull of the union of the possible images (componentwise inclusion, page 174). Not proved here;
see `ComparisonSetting.Containment`. -/
def PlacewiseContainment : Prop := ∀ v, (S v).Containment

/-- Numerical form of the comparison for the global log-volumes:
`− |log(q)| ≤ − |log(Θ)|` (Step (xi-f), page 184). Not proved here. -/
def GlobalLogVolumeComparison : Prop := globalQLogVolume S w ≤ globalThetaLogVolume S w

/-- Placewise containment gives the global comparison, provided both families satisfy the
support condition of page 117. -/
theorem globalLogVolumeComparison_of_placewiseContainment
    (hqs : LogVolumeAlmostAllZero (fun v => (S v).μ) fun v => (S v).qPilot)
    (hΘs : LogVolumeAlmostAllZero (fun v => (S v).μ) fun v => (S v).hullOfUnion)
    (h : PlacewiseContainment S) : GlobalLogVolumeComparison S w :=
  globalLogVolume_mono w _ hqs hΘs h

/-- The two numbers of Corollary 3.12 from the global log-volumes. Hypotheses: every q-pilot
component and every hull component has positive measure (no local term is `−∞`), and the
global q-side log-volume is negative (`|log(q)| > 0`, page 174). -/
noncomputable def globalPilotLogVolumes (hq0 : ∀ v, (S v).μ (S v).qPilot ≠ 0)
    (hneg : globalQLogVolume S w < 0) (hΘ0 : ∀ v, (S v).μ (S v).hullOfUnion ≠ 0) :
    PilotLogVolumes :=
  PilotLogVolumes.ofLogVolumes (globalQLogVolume S w) (globalThetaLogVolume S w)
    (globalLogVolume_ne_bot w fun v => (logVolume_eq_bot_iff _ _).not.mpr (hq0 v)) hneg
    (globalLogVolume_ne_bot w fun v => (logVolume_eq_bot_iff _ _).not.mpr (hΘ0 v))

/-- For the global numbers, the conclusion of Corollary 3.12 is finiteness of the global
Θ-side log-volume together with `GlobalLogVolumeComparison`. -/
theorem conclusion_globalPilotLogVolumes_iff (hq0 : ∀ v, (S v).μ (S v).qPilot ≠ 0)
    (hneg : globalQLogVolume S w < 0) (hΘ0 : ∀ v, (S v).μ (S v).hullOfUnion ≠ 0) :
    Conclusion (globalPilotLogVolumes S w hq0 hneg hΘ0) ↔
      globalThetaLogVolume S w ≠ ⊤ ∧ GlobalLogVolumeComparison S w :=
  PilotLogVolumes.conclusion_ofLogVolumes_iff _ _ _ _ _

/-- **Bridge over places (conditional).** Placewise containment of the q-pilot regions in the
hulls of the unions, finiteness of each hull, and the support condition of page 117 for both
families give the conclusion of Corollary 3.12 for the global numbers.

Conditional on `hcont` (Theorem 3.11 and Steps (i) to (xi); the text asserts only the global
numerical form, Step (xi-f), page 184), on `hfin` (page 175, compactness; not formalized) and
on `hΘs` (the support condition for the hulls; not argued on the pages read). -/
theorem conclusion_of_placewiseContainment (hq0 : ∀ v, (S v).μ (S v).qPilot ≠ 0)
    (hneg : globalQLogVolume S w < 0) (hΘ0 : ∀ v, (S v).μ (S v).hullOfUnion ≠ 0)
    (hfin : ∀ v, (S v).μ (S v).hullOfUnion ≠ ⊤)
    (hqs : LogVolumeAlmostAllZero (fun v => (S v).μ) fun v => (S v).qPilot)
    (hΘs : LogVolumeAlmostAllZero (fun v => (S v).μ) fun v => (S v).hullOfUnion)
    (hcont : PlacewiseContainment S) : Conclusion (globalPilotLogVolumes S w hq0 hneg hΘ0) :=
  (conclusion_globalPilotLogVolumes_iff S w hq0 hneg hΘ0).mpr
    ⟨globalLogVolume_ne_top w fun v => (logVolume_eq_top_iff _ _).not.mpr (hfin v),
      globalLogVolumeComparison_of_placewiseContainment S w hqs hΘs hcont⟩

/-- **Limits: the conclusion on an infinite support.** If the hull family violates the support
condition, the global Θ-side log-volume is `0`, and the conclusion of Corollary 3.12 holds for
the global numbers from the sign condition `hneg` alone. This is an artifact of the value of
`∑ᶠ` on an infinite support, not a comparison of regions. -/
theorem conclusion_globalPilotLogVolumes_of_not_almostAllZero
    (hq0 : ∀ v, (S v).μ (S v).qPilot ≠ 0)
    (hneg : globalQLogVolume S w < 0) (hΘ0 : ∀ v, (S v).μ (S v).hullOfUnion ≠ 0)
    (hΘs : ¬ LogVolumeAlmostAllZero (fun v => (S v).μ) fun v => (S v).hullOfUnion) :
    Conclusion (globalPilotLogVolumes S w hq0 hneg hΘ0) := by
  have h0 : globalThetaLogVolume S w = 0 := globalLogVolume_eq_zero_of_not_almostAllZero w hΘs
  refine (conclusion_globalPilotLogVolumes_iff S w hq0 hneg hΘ0).mpr ⟨?_, ?_⟩
  · rw [h0]; exact EReal.zero_ne_top
  · rw [GlobalLogVolumeComparison, h0]; exact hneg.le

end Bridge

/-! ## Examples on two places -/

namespace TwoPlaceExample

open IntervalExample

/-- Two places, indexed by `Bool`, each carrying the interval setting of `Comparison.lean` with
q-pilot region `q v`. -/
noncomputable def settings (q : Bool → Set ℝ) (v : Bool) : ComparisonSetting ℝ Bool :=
  setting (q v)

/-- Every family on two places satisfies the support condition. -/
theorem almostAllZero (μ : Bool → Measure ℝ) (R : Bool → Set ℝ) :
    LogVolumeAlmostAllZero μ R :=
  Set.toFinite _

/-- With unit weights, the global log-volume on two places is the log of the product of the
two measures. -/
theorem globalLogVolume_bool (μ : Bool → Measure ℝ) (R : Bool → Set ℝ) :
    globalLogVolume (unitPlaceWeights Bool) μ R = ENNReal.log (μ false (R false) * μ true (R true)) := by
  rw [globalLogVolume, finsum_eq_sum_of_fintype, Fintype.sum_bool, ENNReal.log_mul_add]
  simp [weightedLocalLogVolume, unitPlaceWeights, logVolume, add_comm]

/-- The two q-pilot regions `[0, a]` (place `false`) and `[0, b]` (place `true`). -/
noncomputable def qPair (a b : ℝ) : Bool → Set ℝ := fun v => bif v then Icc 0 b else Icc 0 a

theorem volume_Icc_zero (b : ℝ) : volume (Icc (0 : ℝ) b) = ENNReal.ofReal b := by
  rw [Real.volume_Icc, sub_zero]

/-- The Θ-side global log-volume is `log (1/2 · 1/2)` whatever the q-pilot regions. -/
theorem globalThetaLogVolume_eq (q : Bool → Set ℝ) :
    globalThetaLogVolume (settings q) (unitPlaceWeights Bool) =
      ENNReal.log (ENNReal.ofReal (1 / 2) * ENNReal.ofReal (1 / 2)) := by
  rw [globalThetaLogVolume, globalLogVolume_bool]
  simp only [settings, volume_hullOfUnion]

/-- The q-side global log-volume for q-pilot regions `[0, a]` and `[0, b]`. -/
theorem globalQLogVolume_eq (a b : ℝ) :
    globalQLogVolume (settings (qPair a b))
        (unitPlaceWeights Bool) = ENNReal.log (ENNReal.ofReal a * ENNReal.ofReal b) := by
  rw [globalQLogVolume, globalLogVolume_bool]
  simp only [settings, setting, qPair, Bool.cond_false, Bool.cond_true, volume_Icc_zero]

/-- The global q-side log-volume is negative when `a · b < 1`. -/
theorem globalQLogVolume_neg (a b : ℝ) (ha : 0 ≤ a) (hab : a * b < 1) :
    globalQLogVolume (settings (qPair a b))
      (unitPlaceWeights Bool) < 0 := by
  rw [globalQLogVolume_eq a b, ENNReal.log_lt_zero_iff, ← ENNReal.ofReal_mul ha,
    ENNReal.ofReal_lt_one]
  exact hab

/-- The global comparison for q-pilot regions `[0, a]`, `[0, b]` holds exactly when
`a · b ≤ 1/4`. -/
theorem globalComparison_iff (a b : ℝ) (ha : 0 ≤ a) :
    GlobalLogVolumeComparison (settings (qPair a b))
      (unitPlaceWeights Bool) ↔ a * b ≤ 1 / 4 := by
  rw [GlobalLogVolumeComparison, globalQLogVolume_eq a b, globalThetaLogVolume_eq,
    ENNReal.log_le_log_iff, ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_le_ofReal_iff (by norm_num)]
  norm_num

theorem hullOfUnion_volume_ne_zero (q : Bool → Set ℝ) (v : Bool) :
    (settings q v).μ (settings q v).hullOfUnion ≠ 0 := by
  simp only [settings, volume_hullOfUnion]; simp

theorem hullOfUnion_volume_ne_top (q : Bool → Set ℝ) (v : Bool) :
    (settings q v).μ (settings q v).hullOfUnion ≠ ⊤ := by
  simp only [settings, volume_hullOfUnion]; exact ENNReal.ofReal_ne_top

theorem qPair_volume_ne_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (v : Bool) :
    (settings (qPair a b) v).μ (settings (qPair a b) v).qPilot ≠ 0 := by
  cases v <;> simp [settings, setting, qPair, Real.volume_Icc, ha, hb]

/-- **Nonvacuity (a).** With q-pilot region `[0, 1/2]` at both places, every hypothesis of
`conclusion_of_placewiseContainment` holds, so the conclusion of Corollary 3.12 holds for the
global numbers. -/
theorem example_global_conclusion :
    ∃ (hq0 : ∀ v, (settings (qPair (1 / 2) (1 / 2)) v).μ
        (settings (qPair (1 / 2) (1 / 2)) v).qPilot ≠ 0)
      (hneg : globalQLogVolume (settings (qPair (1 / 2) (1 / 2))) (unitPlaceWeights Bool) < 0)
      (hΘ0 : ∀ v, (settings (qPair (1 / 2) (1 / 2)) v).μ
        (settings (qPair (1 / 2) (1 / 2)) v).hullOfUnion ≠ 0),
      Conclusion (globalPilotLogVolumes (settings (qPair (1 / 2) (1 / 2)))
        (unitPlaceWeights Bool) hq0 hneg hΘ0) := by
  refine ⟨qPair_volume_ne_zero (by norm_num) (by norm_num),
    globalQLogVolume_neg _ _ (by norm_num) (by norm_num),
    hullOfUnion_volume_ne_zero _, ?_⟩
  refine conclusion_of_placewiseContainment _ _ _ _ _ (hullOfUnion_volume_ne_top _)
    (almostAllZero _ _) (almostAllZero _ _) fun v => ?_
  cases v <;>
  · unfold ComparisonSetting.Containment settings
    rw [setting_hullOfUnion]; exact subset_rfl

/-- **Nonvacuity (b).** With q-pilot region `[0, 3/4]` at both places, every structural
hypothesis holds (positive measures, finite hulls, the support condition, negative global
q-side log-volume), but the global comparison fails, and so does the conclusion of
Corollary 3.12 for the global numbers. -/
theorem example_global_comparison_fails :
    ∃ (hq0 : ∀ v, (settings (qPair (3 / 4) (3 / 4)) v).μ
        (settings (qPair (3 / 4) (3 / 4)) v).qPilot ≠ 0)
      (hneg : globalQLogVolume (settings (qPair (3 / 4) (3 / 4))) (unitPlaceWeights Bool) < 0)
      (hΘ0 : ∀ v, (settings (qPair (3 / 4) (3 / 4)) v).μ
        (settings (qPair (3 / 4) (3 / 4)) v).hullOfUnion ≠ 0),
      (∀ v, (settings (qPair (3 / 4) (3 / 4)) v).μ
        (settings (qPair (3 / 4) (3 / 4)) v).hullOfUnion ≠ ⊤) ∧
      ¬ GlobalLogVolumeComparison (settings (qPair (3 / 4) (3 / 4))) (unitPlaceWeights Bool) ∧
      ¬ Conclusion (globalPilotLogVolumes (settings (qPair (3 / 4) (3 / 4)))
        (unitPlaceWeights Bool) hq0 hneg hΘ0) := by
  have hc : ¬ GlobalLogVolumeComparison (settings (qPair (3 / 4) (3 / 4)))
      (unitPlaceWeights Bool) := by
    rw [globalComparison_iff _ _ (by norm_num)]; norm_num
  refine ⟨qPair_volume_ne_zero (by norm_num) (by norm_num),
    globalQLogVolume_neg _ _ (by norm_num) (by norm_num),
    hullOfUnion_volume_ne_zero _, hullOfUnion_volume_ne_top _, hc, fun h => hc ?_⟩
  exact ((conclusion_globalPilotLogVolumes_iff _ _ _ _ _).mp h).2

/-- **The global inequality does not imply the placewise one.** With q-pilot regions `[0, 3/4]`
at place `false` and `[0, 1/8]` at place `true`, the global comparison holds
(`3/4 · 1/8 ≤ 1/4`) while the placewise comparison fails at place `false`: the deficit at one
place is compensated at the other. -/
theorem example_global_not_placewise :
    GlobalLogVolumeComparison (settings (qPair (3 / 4) (1 / 8))) (unitPlaceWeights Bool) ∧
      ¬ (settings (qPair (3 / 4) (1 / 8)) false).LogVolumeComparison ∧
      ¬ PlacewiseContainment (settings (qPair (3 / 4) (1 / 8))) := by
  have hf : ¬ (settings (qPair (3 / 4) (1 / 8)) false).LogVolumeComparison := by
    obtain ⟨-, -, -, -, h, -⟩ := example_comparison_fails
    exact h
  refine ⟨?_, hf, fun h => hf ((settings _ false).logVolumeComparison_of_containment (h false))⟩
  rw [globalComparison_iff _ _ (by norm_num)]; norm_num

end TwoPlaceExample

end IUT.PaperIII.Corollary312
