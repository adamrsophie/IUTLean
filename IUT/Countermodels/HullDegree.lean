import IUT.PaperIII.Corollary312.PacketHull

/-!
# Countermodels: is the log-volume of a hull determined by the log-volume of the region?

Sources: Mochizuki, *Inter-universal Teichmüller Theory III*, Remark 3.9.5 (i), (ii), page 127
(the holomorphic hull of a relatively compact region is the smallest set `λ · 𝒪` containing
it, with every component of `λ` nonzero relative to the direct sum decomposition into fields),
and Steps (xi-c), (xi-d) of the proof of Corollary 3.12, pages 182 and 183 (the collection of
possibilities of output data is "slightly" enlarged by passing to the holomorphic hull; page 183
then forms the determinant of a suitable positive tensor power of the resulting localizations
of arithmetic vector bundles and applies a suitably normalized log-volume to the hull region).
Pages read for this file: IUT III pages 127, 182 and
183. Pages checked against rendered images: the same. No formula of the papers is transcribed
here beyond the shape `λ · 𝒪` of page 127.

## The question

At Step (xi) the log-volume is applied to the hull of a region, not to the region. A careful
reader asks whether the first number is a function of the second: is `μ^log(hull U)` determined
by `μ^log(U)`, up to a fixed factor or a fixed additive constant? This file answers the
question on the model of `IUT.PaperIII.Corollary312.PacketHull`: a finite product
`V = Π s, L s` of normed fields that are finite-dimensional normed `ℚ_p`-algebras (finite
extensions of `ℚ_p` with their spectral norms, or copies of `ℚ_p`), the integral structure
`𝒪 = pktHullIntegers`, the hull `pktHull`, the product of Haar measures and the normalized
log-volume `padicMuLog` normalized at `𝒪`, as in `pktHull_muLog_principal`.

* `hullDegRigid p μ U = μ^log(U)` and `hullDegHull p μ U = μ^log(pktHull U)`.
* A *region* (`hullDegRegion`) is a relatively compact `U` of positive product measure (outer
  measure, so this is the same as containing a subset of positive measure, the reading of
  page 127 used in `PacketHull.lean`).

## What is proved

1. *Monotonicity* (`hullDeg_rigid_le_hull`, and `hullDeg_rigid_le_hull_spectral` for finite
   extensions with the spectral norm): `μ^log(U) ≤ μ^log(hull U)` for every region. *Equality*
   holds exactly when `U` and its hull have the same measure (`hullDeg_rigid_eq_hull_iff`), that
   is, for null-measurable `U`, when `hull U \ U` is a null set
   (`hullDeg_rigid_eq_hull_iff_sdiff`). For every set `λ · 𝒪` the hull is the set itself
   (`hullDeg_hull_principal`), so equality holds there.
2. *The three descent statements fail on `ℚ_p²`*, for every prime `p` and every Haar measure:
   (a) `hullDegScalarDescent`: some `c > 0` with `μ^log(hull U) = c · μ^log(U)` for all regions;
   (b) `hullDegShiftDescent`: some `c` with `μ^log(hull U) = μ^log(U) + c` for all regions;
   (c) `hullDegDetermined`: regions with the same `μ^log` have hulls with the same `μ^log`.
   The negations are `hullDeg_not_scalarDescent`, `hullDeg_not_shiftDescent`,
   `hullDeg_not_determined`. These three statements do not occur on the pages read; they are
   formulations of the question above, made here. The witnesses, with their values
   (`μ^log(U)`, `μ^log(hull U)`):
   * `𝒪 = ℤ_p²`: `(0, 0)` (`hullDeg_padic_integers`);
   * `p𝒪`: `(−log p, −log p)` (`hullDeg_padic_pO`);
   * `(1, 1) + p𝒪`: `(−log p, 0)`; its hull is `𝒪` (`hullDeg_padic_shifted`);
   * `((1, p) + p²𝒪) ∪ ((p, 1) + p²𝒪)`: `((log 2)/2 − 2 log p, 0)`; its hull is `𝒪`
     (`hullDeg_padic_twoBalls`), the disjoint union of two balls around the points
     `(1, p)`, `(p, 1)` of `pktHull_union_strict_padic`;
   * `pℤ_p × p⁻¹ℤ_p`: `(0, 0)`, the same values as `𝒪` (`hullDeg_padic_pp`).
   The rows `𝒪` and `(1, 1) + p𝒪` decide (a) and (b); the rows `p𝒪` and `(1, 1) + p𝒪` decide
   (c). The theorems on `ℚ_p` take a Borel measurable structure on `ℚ_p` and a Haar measure
   `ν` as hypotheses; both exist (`padicVol_borelSpace`, and `addHaarMeasure padicVolZp`).
3. *What does hold.* On the family of sets `λ · 𝒪`, the hull is the set itself
   (`hullDeg_hull_principal`, all products), so (c) holds trivially there, with
   `μ^log(hull) = μ^log` (`hullDeg_principal_determined`, stated on `ℚ_p^n`). For two sets
   `λ · 𝒪`, `λ' · 𝒪`: the hull of the union is `m · 𝒪` with `‖m_s‖ = max (‖λ_s‖, ‖λ'_s‖)`
   (`hullDeg_hull_union_principal`), the intersection is the box of the coordinatewise minima
   (`hullDeg_inter_principal`), and `μ(λ𝒪 ∪ λ'𝒪) + μ(min) = μ(λ𝒪) + μ(λ'𝒪)`
   (`hullDeg_measure_union_principal`). For finite extensions of degrees `d_s`, `D = Σ d_s`,
   `μ^log(hull) = (Σ_s d_s log max (‖λ_s‖, ‖λ'_s‖)) / D` (`hullDeg_union_principal_spectral`);
   on `ℚ_p^n`, `μ^log(λ𝒪 ∪ λ'𝒪) = log (Π‖λ_s‖ + Π‖λ'_s‖ − Π min (‖λ_s‖, ‖λ'_s‖)) / n`
   (`hullDeg_padic_union_principal`), against `μ^log(hull) = (Σ log max (‖λ_s‖, ‖λ'_s‖)) / n`
   (`hullDeg_padic_union_principal_hull`). The first depends on the overlap of the boxes, the
   second only on the coordinatewise maxima.
4. *Measure-preserving automorphisms.* Every continuous `ℚ_p`-linear automorphism `h` of `V`
   with `μ(h 𝒪) = μ(𝒪)` preserves `μ^log` of every set (`hullDeg_rigid_image_equiv`). Whether
   it preserves the log-volume of hulls depends on whether it respects the decomposition of `V`
   as a product of fields:
   * multiplication by a unit `g` of `V` with `‖g_s‖ = 1` for all `s` preserves both
     (`hullDeg_units`), because the hull is equivariant (`pktHull_smul`);
   * a permutation of the coordinates of `K^ι` preserves both (`hullDeg_perm`);
   * the shear `(x, y) ↦ (x + y, y)` of `ℚ_p²` maps `𝒪` onto `𝒪`, preserves `μ^log` of every
     set, and does not preserve the log-volume of hulls: `U₀ = ℤ_p × p⁻¹ℤ_p` has
     `μ^log(U₀) = μ^log(hull U₀) = (log p)/2`, while its image has `μ^log = (log p)/2` and
     hull `p⁻¹𝒪`, of log-volume `log p` (`hullDeg_shear`).

## What this does and does not say

These are facts about hulls of regions in a finite product of local fields, with the hull of
page 127 and the normalized Haar log-volume. They show that `μ^log(hull U)` is not a function of
`μ^log(U)` on all regions, and that the hull is not invariant under measure-preserving linear
automorphisms that mix the direct summands. They do not decide whether the regions that arise
in the proof of Corollary 3.12 (unions of possible images under the indeterminacies (Ind1),
(Ind2), (Ind3), in tensor packets of log-shells) behave like the examples here, and they are
not a statement for or against either side of the discussion of that corollary. In the
classification of the project these are counterexamples to simplified abstractions (category
5): none of (a), (b), (c) is a statement of the papers. The automorphisms here are arbitrary
linear maps of the model; the papers' indeterminacies are not modeled.

Relation to other modules: `IUT.Countermodels.Hull.shear_countermodel` concerns the
`ℤ[i]`-span (an integral hull, not the hull of page 127) and states no log-volume;
`IUT.PaperIII.Corollary312.IntervalExample.example_union_matters` concerns interval hulls
on `ℝ`; `IUT.Audit.MochizukiResponses.LVEx` concerns Lebesgue areas of a symmetrized region
of `ℝ²`. None computes log-volumes of the hull of page 127.

## Not proved

* Nothing about tensor packets, log-shells, the archimedean places, the averaged
  log-volume over places and labels of Corollary 3.12, or the determinant of a tensor power
  of arithmetic vector bundles of page 183 that stands between the hull and the log-volume
  there; here the log-volume is applied to the hull region directly.
* The behavior under a unit `g` with some `‖g_s‖ ≠ 1` is not computed here (the hull is still
  equivariant, `pktHull_smul`).
* The witnesses are on `ℚ_p²`; no witness is given on a product of ramified extensions.
-/

namespace IUT.Countermodels.HullDegree

open MeasureTheory Set IUT.PaperIII.Corollary312 IUT.Prerequisites.PadicVolume
open scoped Pointwise

/-! ## Definitions -/

section Defs

variable (p : ℕ) [Fact p.Prime] {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ s, NormedField (L s)] [∀ s, NormedAlgebra ℚ_[p] (L s)] [∀ s, MeasurableSpace (L s)]
  (μ : ∀ s, Measure (L s))

/-- The log-volume of the region itself, `μ^log(U)`, for the product measure and normalized at
`𝒪` (the normalization of `pktHull_muLog_principal`). -/
noncomputable def hullDegRigid (U : Set (∀ s, L s)) : ℝ :=
  padicMuLog p (Measure.pi μ) pktHullIntegers U

/-- The log-volume of the hull of page 127, `μ^log(pktHull U)`, in the same normalization. -/
noncomputable def hullDegHull (U : Set (∀ s, L s)) : ℝ :=
  padicMuLog p (Measure.pi μ) pktHullIntegers (pktHull U)

/-- A region: relatively compact, of positive (outer) product measure. -/
def hullDegRegion (U : Set (∀ s, L s)) : Prop :=
  IsCompact (closure U) ∧ Measure.pi μ U ≠ 0

/-- (a): the log-volume of the hull is a fixed positive multiple of that of the region. -/
def hullDegScalarDescent : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ U, hullDegRegion μ U → hullDegHull p μ U = c * hullDegRigid p μ U

/-- (b): the log-volume of the hull is that of the region plus a fixed constant. -/
def hullDegShiftDescent : Prop :=
  ∃ c : ℝ, ∀ U, hullDegRegion μ U → hullDegHull p μ U = hullDegRigid p μ U + c

/-- (c): regions of equal log-volume have hulls of equal log-volume. -/
def hullDegDetermined : Prop :=
  ∀ U V, hullDegRegion μ U → hullDegRegion μ V → hullDegRigid p μ U = hullDegRigid p μ V →
    hullDegHull p μ U = hullDegHull p μ V

end Defs

/-! ## Hulls computed from an attained bound -/

section Hull

variable {ι : Type*} {L : ι → Type*} [∀ s, NormedField (L s)] [∀ s, ProperSpace (L s)]

/-- **The workhorse.** If `U ⊆ λ · 𝒪` and every coordinate bound `‖λ_s‖` is attained on `U`,
then the hull of `U` is `λ · 𝒪`. No discreteness of the value groups is needed. -/
theorem hullDeg_hull_eq_of_attained {U : Set (∀ s, L s)} {c : ∀ s, (L s)ˣ}
    (hU : U ⊆ pktHullPrincipal c) (hatt : ∀ s, ∃ x ∈ U, ‖x s‖ = ‖((c s : (L s)ˣ) : L s)‖) :
    pktHull U = pktHullPrincipal c := by
  have hcomp := pktHull_isCompact_principal c
  have hrc : IsCompact (closure U) :=
    hcomp.of_isClosed_subset isClosed_closure (closure_minimal hU hcomp.isClosed)
  refine Subset.antisymm (pktHull_subset_of_form ⟨c, rfl⟩ hU) fun y hy => ?_
  rw [pktHull_of_relCompact hrc]
  rintro H ⟨⟨c', rfl⟩, hUH⟩
  refine pktHull_mem_principal.mpr fun s => ?_
  obtain ⟨x, hx, hxs⟩ := hatt s
  calc ‖y s‖ ≤ ‖((c s : (L s)ˣ) : L s)‖ := pktHull_mem_principal.mp hy s
    _ = ‖x s‖ := hxs.symm
    _ ≤ ‖((c' s : (L s)ˣ) : L s)‖ := pktHull_mem_principal.mp (hUH hx) s

omit [∀ s, ProperSpace (L s)] in
/-- The point `λ` lies in `λ · 𝒪`. -/
theorem hullDeg_self_mem_principal (c : ∀ s, (L s)ˣ) :
    (fun s => ((c s : (L s)ˣ) : L s)) ∈ pktHullPrincipal c :=
  pktHull_mem_principal.mpr fun _ => le_rfl

/-- **The hull of `λ · 𝒪` is `λ · 𝒪`.** -/
theorem hullDeg_hull_principal (c : ∀ s, (L s)ˣ) :
    pktHull (pktHullPrincipal c) = pktHullPrincipal c :=
  hullDeg_hull_eq_of_attained subset_rfl fun _ => ⟨_, hullDeg_self_mem_principal c, rfl⟩

/-- The coordinatewise larger of two units, by norm. -/
noncomputable def hullDegMax (c c' : ∀ s, (L s)ˣ) : ∀ s, (L s)ˣ := fun s =>
  if ‖((c s : (L s)ˣ) : L s)‖ ≤ ‖((c' s : (L s)ˣ) : L s)‖ then c' s else c s

/-- The coordinatewise smaller of two units, by norm. -/
noncomputable def hullDegMin (c c' : ∀ s, (L s)ˣ) : ∀ s, (L s)ˣ := fun s =>
  if ‖((c s : (L s)ˣ) : L s)‖ ≤ ‖((c' s : (L s)ˣ) : L s)‖ then c s else c' s

omit [∀ s, ProperSpace (L s)] in
/-- The norm of `hullDegMax c c'` at `s` is the larger of the two norms. -/
theorem hullDegMax_norm (c c' : ∀ s, (L s)ˣ) (s : ι) :
    ‖((hullDegMax c c' s : (L s)ˣ) : L s)‖ =
      max ‖((c s : (L s)ˣ) : L s)‖ ‖((c' s : (L s)ˣ) : L s)‖ := by
  unfold hullDegMax
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (le_of_not_ge h)).symm

omit [∀ s, ProperSpace (L s)] in
/-- The norm of `hullDegMin c c'` at `s` is the smaller of the two norms. -/
theorem hullDegMin_norm (c c' : ∀ s, (L s)ˣ) (s : ι) :
    ‖((hullDegMin c c' s : (L s)ˣ) : L s)‖ =
      min ‖((c s : (L s)ˣ) : L s)‖ ‖((c' s : (L s)ˣ) : L s)‖ := by
  unfold hullDegMin
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_not_ge h)).symm

/-- **The hull of a union of two sets `λ · 𝒪`, `λ' · 𝒪`** is `m · 𝒪` with
`‖m_s‖ = max (‖λ_s‖, ‖λ'_s‖)`. -/
theorem hullDeg_hull_union_principal (c c' : ∀ s, (L s)ˣ) :
    pktHull (pktHullPrincipal c ∪ pktHullPrincipal c') = pktHullPrincipal (hullDegMax c c') := by
  apply hullDeg_hull_eq_of_attained
  · rintro x (hx | hx) <;> refine pktHull_mem_principal.mpr fun s => ?_ <;>
      rw [hullDegMax_norm]
    · exact (pktHull_mem_principal.mp hx s).trans (le_max_left _ _)
    · exact (pktHull_mem_principal.mp hx s).trans (le_max_right _ _)
  · intro s
    rw [hullDegMax_norm]
    rcases le_total ‖((c s : (L s)ˣ) : L s)‖ ‖((c' s : (L s)ˣ) : L s)‖ with h | h
    · exact ⟨_, Or.inr (hullDeg_self_mem_principal c'), (max_eq_right h).symm⟩
    · exact ⟨_, Or.inl (hullDeg_self_mem_principal c), (max_eq_left h).symm⟩

omit [∀ s, ProperSpace (L s)] in
/-- The intersection of two sets `λ · 𝒪`, `λ' · 𝒪` is the box of the coordinatewise minima. -/
theorem hullDeg_inter_principal (c c' : ∀ s, (L s)ˣ) :
    pktHullPrincipal c ∩ pktHullPrincipal c' = pktHullPrincipal (hullDegMin c c') := by
  ext x
  simp only [Set.mem_inter_iff, pktHull_mem_principal, hullDegMin_norm, le_min_iff]
  exact ⟨fun h s => ⟨h.1 s, h.2 s⟩, fun h => ⟨fun s => (h s).1, fun s => (h s).2⟩⟩

omit [∀ s, ProperSpace (L s)] in
/-- **Hulls are transported by homeomorphisms that permute the sets `λ · 𝒪`.** -/
theorem hullDeg_hull_image (f : (∀ s, L s) ≃ₜ (∀ s, L s))
    (hf : ∀ H ∈ pktHullForms (L := L), f '' H ∈ pktHullForms (L := L))
    (hf' : ∀ H ∈ pktHullForms (L := L), f.symm '' H ∈ pktHullForms (L := L))
    (U : Set (∀ s, L s)) : pktHull (f '' U) = f '' pktHull U := by
  have hcomp : IsCompact (closure (f '' U)) ↔ IsCompact (closure U) := by
    rw [← f.image_closure, f.isCompact_image]
  by_cases hU : IsCompact (closure U)
  · rw [pktHull_of_relCompact (hcomp.mpr hU), pktHull_of_relCompact hU]
    ext x
    rw [f.image_eq_preimage_symm (⋂₀ _), Set.mem_preimage]
    simp only [Set.mem_sInter, Set.mem_ofPred_eq, and_imp]
    constructor
    · intro hx H hH hUH
      have := hx (f '' H) (hf H hH) (Set.image_mono hUH)
      rwa [f.image_eq_preimage_symm, Set.mem_preimage] at this
    · intro hx H hH hUH
      have hsub : U ⊆ f.symm '' H := fun u hu =>
        ⟨f u, hUH (Set.mem_image_of_mem f hu), f.symm_apply_apply u⟩
      obtain ⟨y, hy, hyx⟩ := hx _ (hf' H hH) hsub
      rwa [f.symm.injective hyx] at hy
  · rw [pktHull_of_not_relCompact (fun h => hU (hcomp.mp h)), pktHull_of_not_relCompact hU,
      Set.image_univ_of_surjective f.surjective]

end Hull

/-! ## Monotonicity, the equality case, invariance -/

section General

variable (p : ℕ) [Fact p.Prime] {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ s, NormedField (L s)] [∀ s, NormedAlgebra ℚ_[p] (L s)] [∀ s, FiniteDimensional ℚ_[p] (L s)]
  [∀ s, MeasurableSpace (L s)] [∀ s, BorelSpace (L s)] [∀ s, ProperSpace (L s)]
  (μ : ∀ s, Measure (L s)) [∀ s, (μ s).IsAddHaarMeasure]

omit [∀ s, BorelSpace (L s)] in
/-- A set `λ · 𝒪` has positive product measure. -/
theorem hullDeg_principal_measure_ne_zero (c : ∀ s, (L s)ˣ) :
    Measure.pi μ (pktHullPrincipal c) ≠ 0 := by
  rw [pktHullPrincipal_eq_pi, Measure.pi_pi]
  exact Finset.prod_ne_zero_iff.mpr fun s _ =>
    (Metric.measure_closedBall_pos (μ s) 0 (norm_pos_iff.mpr (c s).ne_zero)).ne'

omit [∀ s, BorelSpace (L s)] in
/-- A set `λ · 𝒪` has finite product measure. -/
theorem hullDeg_principal_measure_ne_top (c : ∀ s, (L s)ˣ) :
    Measure.pi μ (pktHullPrincipal c) ≠ ⊤ :=
  (pktHull_isCompact_principal c).measure_lt_top.ne

omit [∀ s, ProperSpace (L s)] in
/-- A set `λ · 𝒪` is measurable. -/
theorem hullDeg_principal_measurableSet (c : ∀ s, (L s)ˣ) :
    MeasurableSet (pktHullPrincipal c) := by
  rw [pktHullPrincipal_eq_pi]
  exact MeasurableSet.univ_pi fun s => Metric.isClosed_closedBall.measurableSet

omit [∀ s, ProperSpace (L s)] [∀ s, (μ s).IsAddHaarMeasure] in
/-- **Inclusion and exclusion for two sets `λ · 𝒪`, `λ' · 𝒪`**:
`μ(λ𝒪 ∪ λ'𝒪) + μ(m · 𝒪) = μ(λ𝒪) + μ(λ'𝒪)`, with `m` the coordinatewise minimum. -/
theorem hullDeg_measure_union_principal (c c' : ∀ s, (L s)ˣ) :
    Measure.pi μ (pktHullPrincipal c ∪ pktHullPrincipal c') +
        Measure.pi μ (pktHullPrincipal (hullDegMin c c')) =
      Measure.pi μ (pktHullPrincipal c) + Measure.pi μ (pktHullPrincipal c') := by
  rw [← hullDeg_inter_principal]
  exact measure_union_add_inter _ (hullDeg_principal_measurableSet c')

omit [∀ s, BorelSpace (L s)] [∀ s, (μ s).IsAddHaarMeasure] in
/-- A subset of positive measure of some `λ · 𝒪` is a region. -/
theorem hullDeg_region_of_subset {U : Set (∀ s, L s)} {c : ∀ s, (L s)ˣ}
    (hU : U ⊆ pktHullPrincipal c) (h0 : Measure.pi μ U ≠ 0) : hullDegRegion μ U :=
  ⟨(pktHull_isCompact_principal c).of_isClosed_subset isClosed_closure
    (closure_minimal hU (pktHull_isCompact_principal c).isClosed), h0⟩

omit [∀ s, BorelSpace (L s)] in
/-- The hull of a region has finite measure. -/
theorem hullDeg_hull_measure_ne_top (hd : ∀ s, pktHullDiscrete (L s)) {U : Set (∀ s, L s)}
    (hU : IsCompact (closure U)) : Measure.pi μ (pktHull U) ≠ ⊤ := by
  obtain ⟨c, hc⟩ := pktHull_exists_form_superset hd (pktHull_isBounded_of_relCompact hU)
  exact ne_top_of_le_ne_top (hullDeg_principal_measure_ne_top μ c)
    (measure_mono (pktHull_subset_of_form ⟨c, rfl⟩ hc))

omit [∀ s, FiniteDimensional ℚ_[p] (L s)] [∀ s, BorelSpace (L s)] in
/-- **Monotonicity**: `μ^log(U) ≤ μ^log(hull U)` for every region. -/
theorem hullDeg_rigid_le_hull (hd : ∀ s, pktHullDiscrete (L s)) {U : Set (∀ s, L s)}
    (hU : hullDegRegion μ U) : hullDegRigid p μ U ≤ hullDegHull p μ U := by
  have hO := hullDeg_principal_measure_ne_zero μ 1
  have hO' := hullDeg_principal_measure_ne_top μ 1
  rw [pktHullPrincipal_one] at hO hO'
  exact padicMuLog_mono p _ (pktHull_extensive U) hO hO' hU.2
    (hullDeg_hull_measure_ne_top μ hd hU.1)

omit [∀ s, BorelSpace (L s)] in
/-- **The equality case**: for a region, `μ^log(U) = μ^log(hull U)` exactly when `U` and its
hull have the same measure. -/
theorem hullDeg_rigid_eq_hull_iff [Nonempty ι] (hd : ∀ s, pktHullDiscrete (L s))
    {U : Set (∀ s, L s)} (hU : hullDegRegion μ U) :
    hullDegRigid p μ U = hullDegHull p μ U ↔ Measure.pi μ U = Measure.pi μ (pktHull U) := by
  refine ⟨fun h => ?_, fun h => by simp only [hullDegRigid, hullDegHull, padicMuLog, h]⟩
  have hO := hullDeg_principal_measure_ne_zero μ 1
  have hO' := hullDeg_principal_measure_ne_top μ 1
  rw [pktHullPrincipal_one] at hO hO'
  have hH := hullDeg_hull_measure_ne_top μ hd hU.1
  have hUt : Measure.pi μ U ≠ ⊤ := ne_top_of_le_ne_top hH (measure_mono (pktHull_extensive U))
  have hH0 : Measure.pi μ (pktHull U) ≠ 0 := fun h0 =>
    hU.2 (measure_mono_null (pktHull_extensive U) h0)
  have : Nontrivial (∀ s, L s) := by
    obtain ⟨s⟩ := ‹Nonempty ι›
    exact Pi.nontrivial_at s
  have hD : (Module.finrank ℚ_[p] (∀ s, L s) : ℝ) ≠ 0 := by
    exact_mod_cast Module.finrank_pos.ne'
  have hOpos := ENNReal.toReal_pos hO hO'
  unfold hullDegRigid hullDegHull padicMuLog at h
  rw [div_left_inj₀ hD] at h
  have h1 := Real.log_injOn_pos (Set.mem_Ioi.mpr (div_pos (ENNReal.toReal_pos hU.2 hUt) hOpos))
    (Set.mem_Ioi.mpr (div_pos (ENNReal.toReal_pos hH0 hH) hOpos)) h
  rw [div_left_inj₀ hOpos.ne'] at h1
  exact (ENNReal.toReal_eq_toReal_iff' hUt hH).mp h1

omit [∀ s, BorelSpace (L s)] in
/-- **The equality case, null-measurable regions**: `μ^log(U) = μ^log(hull U)` exactly when
`hull U \ U` is a null set, that is, when `U` has full measure in its hull. -/
theorem hullDeg_rigid_eq_hull_iff_sdiff [Nonempty ι] (hd : ∀ s, pktHullDiscrete (L s))
    {U : Set (∀ s, L s)} (hU : hullDegRegion μ U) (hm : NullMeasurableSet U (Measure.pi μ)) :
    hullDegRigid p μ U = hullDegHull p μ U ↔ Measure.pi μ (pktHull U \ U) = 0 := by
  have hUt : Measure.pi μ U ≠ ⊤ := ne_top_of_le_ne_top (hullDeg_hull_measure_ne_top μ hd hU.1)
    (measure_mono (pktHull_extensive U))
  rw [hullDeg_rigid_eq_hull_iff p μ hd hU, measure_sdiff (pktHull_extensive U) hm hUt,
    tsub_eq_zero_iff_le]
  exact ⟨fun h => h.ge, fun h => le_antisymm (measure_mono (pktHull_extensive U)) h⟩

/-- **Linear automorphisms that preserve the measure of `𝒪` preserve `μ^log` of every set.** -/
theorem hullDeg_rigid_image_equiv (h : (∀ s, L s) ≃L[ℚ_[p]] (∀ s, L s))
    (hO : Measure.pi μ (h '' pktHullIntegers) = Measure.pi μ pktHullIntegers)
    (U : Set (∀ s, L s)) : hullDegRigid p μ (h '' U) = hullDegRigid p μ U := by
  have := padicMuLog_image_equiv p (Measure.pi μ) h pktHullIntegers U
  unfold hullDegRigid
  unfold padicMuLog at this ⊢
  rwa [hO] at this

/-- **Units of norm one preserve both log-volumes**: for a unit `g` of `V` with `‖g_s‖ = 1`
for all `s`, `μ^log(g U) = μ^log(U)` and `μ^log(hull (g U)) = μ^log(hull U)`. -/
theorem hullDeg_units (g : (∀ s, L s)ˣ) (hg : ∀ s, ‖(g : ∀ s, L s) s‖ = 1)
    (U : Set (∀ s, L s)) :
    hullDegRigid p μ (g • U) = hullDegRigid p μ U ∧
      hullDegHull p μ (g • U) = hullDegHull p μ U := by
  let e : (∀ s, L s) ≃L[ℚ_[p]] (∀ s, L s) :=
    (DistribMulAction.toLinearEquiv ℚ_[p] (∀ s, L s) g).toContinuousLinearEquiv
  have himg : ∀ S : Set (∀ s, L s), e '' S = g • S := fun S => by rw [← Set.image_smul]; rfl
  have hgO : g • (pktHullIntegers : Set (∀ s, L s)) = pktHullIntegers := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [pktHullIntegers, Set.mem_ofPred_eq, Units.smul_def, smul_eq_mul, Pi.mul_apply,
      pktHull_units_inv_apply, norm_mul, norm_inv, hg, inv_one, one_mul]
  have hO : Measure.pi μ (e '' pktHullIntegers) = Measure.pi μ pktHullIntegers := by
    rw [himg, hgO]
  refine ⟨by rw [← himg]; exact hullDeg_rigid_image_equiv p μ e hO U, ?_⟩
  have := hullDeg_rigid_image_equiv p μ e hO (pktHull U)
  rw [himg, ← pktHull_smul] at this
  exact this

end General

/-! ## Permutations of the coordinates of `K^ι` -/

section Perm

variable (p : ℕ) [Fact p.Prime] {ι : Type*} [Fintype ι] {K : Type*} [NormedField K]
  [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] [MeasurableSpace K] [ProperSpace K]
  (ν : Measure K)

/-- The permutation `x ↦ x ∘ σ` of the coordinates, as a continuous linear automorphism. -/
noncomputable def hullDegPermEquiv (σ : Equiv.Perm ι) : (ι → K) ≃L[ℚ_[p]] (ι → K) :=
  (LinearEquiv.funCongrLeft ℚ_[p] K σ).toContinuousLinearEquiv

omit [MeasurableSpace K] [ProperSpace K] in
/-- A permutation of coordinates maps `λ · 𝒪` to `(λ ∘ σ) · 𝒪`. -/
theorem hullDeg_perm_principal (σ : Equiv.Perm ι) (c : ι → Kˣ) :
    hullDegPermEquiv p σ '' pktHullPrincipal c =
      pktHullPrincipal (L := fun _ : ι => K) (c ∘ σ) := by
  ext y
  rw [ContinuousLinearEquiv.image_eq_preimage_symm, Set.mem_preimage, pktHull_mem_principal,
    pktHull_mem_principal]
  simp only [hullDegPermEquiv, LinearEquiv.coe_toContinuousLinearEquiv_symm',
    LinearEquiv.funCongrLeft_symm, LinearEquiv.funCongrLeft_apply, Function.comp_apply]
  constructor
  · intro h s
    simpa using h (σ s)
  · intro h t
    simpa using h (σ.symm t)

omit [MeasurableSpace K] [ProperSpace K] in
/-- The hull is equivariant under permutations of coordinates. -/
theorem hullDeg_hull_perm (σ : Equiv.Perm ι) (U : Set (ι → K)) :
    pktHull (hullDegPermEquiv p σ '' U) = hullDegPermEquiv p σ '' pktHull U := by
  have key : ∀ τ : Equiv.Perm ι, ∀ H ∈ pktHullForms (L := fun _ : ι => K),
      hullDegPermEquiv p τ '' H ∈ pktHullForms (L := fun _ : ι => K) := by
    rintro τ _ ⟨c, rfl⟩
    exact ⟨c ∘ τ, (hullDeg_perm_principal p τ c).symm⟩
  have hsymm : ∀ H : Set (ι → K), (hullDegPermEquiv p σ).toHomeomorph.symm '' H =
      hullDegPermEquiv p σ.symm '' H := by
    intro H
    rfl
  exact hullDeg_hull_image (hullDegPermEquiv p σ).toHomeomorph (key σ)
    (fun H hH => (hsymm H) ▸ key σ.symm H hH) U

variable [BorelSpace K] [ν.IsAddHaarMeasure]

/-- **Permutations of coordinates preserve both log-volumes.** -/
theorem hullDeg_perm (σ : Equiv.Perm ι) (U : Set (ι → K)) :
    hullDegRigid p (fun _ : ι => ν) (hullDegPermEquiv p σ '' U) =
        hullDegRigid p (fun _ : ι => ν) U ∧
      hullDegHull p (fun _ : ι => ν) (hullDegPermEquiv p σ '' U) =
        hullDegHull p (fun _ : ι => ν) U := by
  have hO : hullDegPermEquiv p σ '' (pktHullIntegers : Set (ι → K)) = pktHullIntegers := by
    rw [← pktHullPrincipal_one, hullDeg_perm_principal]
    rfl
  have hO' : Measure.pi (fun _ : ι => ν) (hullDegPermEquiv p σ '' pktHullIntegers) =
      Measure.pi (fun _ : ι => ν) pktHullIntegers := by rw [hO]
  refine ⟨hullDeg_rigid_image_equiv p _ _ hO' U, ?_⟩
  have := hullDeg_rigid_image_equiv p _ _ hO' (pktHull U)
  rw [← hullDeg_hull_perm] at this
  exact this

end Perm

/-! ## Copies of `ℚ_p` -/

section Padic

variable (p : ℕ) [hp : Fact p.Prime]

/-- `p` as a unit of `ℚ_p`. -/
noncomputable def hullDegP : ℚ_[p]ˣ := Units.mk0 (p : ℚ_[p]) (by exact_mod_cast hp.out.ne_zero)

/-- `‖p‖ = p⁻¹`. -/
theorem hullDegP_norm : ‖((hullDegP p : ℚ_[p]ˣ) : ℚ_[p])‖ = (p : ℝ)⁻¹ := by
  simp [hullDegP, Padic.norm_p]

/-- `‖p⁻¹‖ = p`. -/
theorem hullDegP_inv_norm : ‖(((hullDegP p)⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ = p := by
  rw [Units.val_inv_eq_inv_val, norm_inv, hullDegP_norm, inv_inv]

/-- `‖p²‖ = p⁻²`. -/
theorem hullDegP_sq_norm : ‖((hullDegP p ^ 2 : ℚ_[p]ˣ) : ℚ_[p])‖ = (p : ℝ)⁻¹ ^ 2 := by
  rw [Units.val_pow_eq_pow_val, norm_pow, hullDegP_norm]

/-- `p⁻¹ < 1`. -/
theorem hullDeg_p_inv_lt_one : (p : ℝ)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

/-- `log p > 0`. -/
theorem hullDeg_log_p_pos : 0 < Real.log p :=
  Real.log_pos (by exact_mod_cast hp.out.one_lt)

/-- The region `p𝒪 = pℤ_p × pℤ_p` of `ℚ_p²`. -/
noncomputable def hullDegPO : Set (Fin 2 → ℚ_[p]) := pktHullPrincipal fun _ => hullDegP p

/-- The region `(1, 1) + p𝒪` of `ℚ_p²`. -/
noncomputable def hullDegShifted : Set (Fin 2 → ℚ_[p]) :=
  (fun _ : Fin 2 => (1 : ℚ_[p])) +ᵥ hullDegPO p

/-- The region `((1, p) + p²𝒪) ∪ ((p, 1) + p²𝒪)` of `ℚ_p²`. -/
noncomputable def hullDegTwoBalls : Set (Fin 2 → ℚ_[p]) :=
  (![1, (p : ℚ_[p])] +ᵥ pktHullPrincipal fun _ => hullDegP p ^ 2) ∪
    (![(p : ℚ_[p]), 1] +ᵥ pktHullPrincipal fun _ => hullDegP p ^ 2)

/-- The shear `(x, y) ↦ (x + y, y)` of `ℚ_p²`. -/
noncomputable def hullDegShear : (Fin 2 → ℚ_[p]) ≃L[ℚ_[p]] (Fin 2 → ℚ_[p]) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => ![x 0 + x 1, x 1]
      invFun := fun x => ![x 0 - x 1, x 1]
      map_add' := fun x y => by ext i; fin_cases i <;> simp; ring
      map_smul' := fun c x => by ext i; fin_cases i <;> simp [mul_add]
      left_inv := fun x => by ext i; fin_cases i <;> simp
      right_inv := fun x => by ext i; fin_cases i <;> simp }

/-- The shear in coordinates. -/
theorem hullDegShear_apply (x : Fin 2 → ℚ_[p]) : hullDegShear p x = ![x 0 + x 1, x 1] := rfl


variable [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]] (ν : Measure ℚ_[p]) [ν.IsAddHaarMeasure]

/-- **Measure of `λ · 𝒪` in `ℚ_p^ι`**: `μ(λ · 𝒪) / μ(𝒪) = Π_s ‖λ_s‖`. -/
theorem hullDeg_padic_ratio {ι : Type*} [Fintype ι] (c : ι → ℚ_[p]ˣ) :
    (Measure.pi (fun _ : ι => ν) (pktHullPrincipal c)).toReal /
      (Measure.pi (fun _ : ι => ν) pktHullIntegers).toReal =
        ∏ s, ‖((c s : ℚ_[p]ˣ) : ℚ_[p])‖ := by
  have hsc : ∀ (_ : ι) (y : ℚ_[p]), y ≠ 0 → ∀ A : Set ℚ_[p],
      ν (y • A) = ((‖y‖₊ ^ 1 : NNReal) : ENNReal) * ν A := fun _ y hy A => by
    rw [padicVol_measure_smul p ν hy A, Module.finrank_self]
  have hB : {y : ℚ_[p] | ‖y‖ ≤ 1} = Metric.closedBall 0 1 := by ext y; simp
  have hB0 : ν {y : ℚ_[p] | ‖y‖ ≤ 1} ≠ 0 := by
    rw [hB]; exact (Metric.measure_closedBall_pos ν 0 one_pos).ne'
  have hBt : ν {y : ℚ_[p] | ‖y‖ ≤ 1} ≠ ⊤ := by
    rw [hB]; exact (isCompact_closedBall (0 : ℚ_[p]) 1).measure_lt_top.ne
  have hpos := ENNReal.toReal_pos hB0 hBt
  have hO := pktHull_measure_principal (L := fun _ : ι => ℚ_[p]) (fun _ => 1) (fun _ => ν) hsc 1
  rw [pktHullPrincipal_one] at hO
  rw [hO, pktHull_measure_principal (fun _ => 1) (fun _ => ν) hsc c, ENNReal.toReal_prod,
    ENNReal.toReal_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [Units.val_one, Pi.one_apply, nnNorm_one, ENNReal.coe_one, one_mul,
    pow_one, ENNReal.toReal_mul, ENNReal.coe_toReal, coe_nnNorm]
  field_simp

/-- **Log-volume of `λ · 𝒪` in `ℚ_p^ι`**: `(Σ_s log ‖λ_s‖) / |ι|`. -/
theorem hullDeg_padic_principal {ι : Type*} [Fintype ι] (c : ι → ℚ_[p]ˣ) :
    hullDegRigid p (fun _ : ι => ν) (pktHullPrincipal c) =
      (∑ s, Real.log ‖((c s : ℚ_[p]ˣ) : ℚ_[p])‖) / Fintype.card ι := by
  unfold hullDegRigid padicMuLog
  rw [hullDeg_padic_ratio p ν c, Real.log_prod fun s _ => norm_ne_zero_iff.mpr (c s).ne_zero,
    Module.finrank_fintype_fun_eq_card]

/-- **Union of two sets `λ · 𝒪`, `λ' · 𝒪` in `ℚ_p^ι`**: its log-volume is
`log (Π‖λ_s‖ + Π‖λ'_s‖ − Π min (‖λ_s‖, ‖λ'_s‖)) / |ι|`. -/
theorem hullDeg_padic_union_principal {ι : Type*} [Fintype ι] (c c' : ι → ℚ_[p]ˣ) :
    hullDegRigid p (fun _ : ι => ν) (pktHullPrincipal c ∪ pktHullPrincipal c') =
      Real.log (∏ s, ‖((c s : ℚ_[p]ˣ) : ℚ_[p])‖ + ∏ s, ‖((c' s : ℚ_[p]ˣ) : ℚ_[p])‖ -
        ∏ s, min ‖((c s : ℚ_[p]ˣ) : ℚ_[p])‖ ‖((c' s : ℚ_[p]ˣ) : ℚ_[p])‖) / Fintype.card ι := by
  have hm := hullDeg_measure_union_principal (fun _ : ι => ν) c c'
  have hU : Measure.pi (fun _ : ι => ν) (pktHullPrincipal c ∪ pktHullPrincipal c') ≠ ⊤ :=
    measure_union_ne_top (hullDeg_principal_measure_ne_top _ c)
      (hullDeg_principal_measure_ne_top _ c')
  have hreal : (Measure.pi (fun _ : ι => ν) (pktHullPrincipal c ∪ pktHullPrincipal c')).toReal =
      (Measure.pi (fun _ : ι => ν) (pktHullPrincipal c)).toReal +
        (Measure.pi (fun _ : ι => ν) (pktHullPrincipal c')).toReal -
        (Measure.pi (fun _ : ι => ν) (pktHullPrincipal (hullDegMin c c'))).toReal := by
    have := congrArg ENNReal.toReal hm
    rw [ENNReal.toReal_add hU (hullDeg_principal_measure_ne_top _ _),
      ENNReal.toReal_add (hullDeg_principal_measure_ne_top _ _)
        (hullDeg_principal_measure_ne_top _ _)] at this
    linarith
  unfold hullDegRigid padicMuLog
  rw [hreal, add_sub_assoc, add_div, sub_div, hullDeg_padic_ratio p ν c,
    hullDeg_padic_ratio p ν c', hullDeg_padic_ratio p ν (hullDegMin c c'),
    Module.finrank_fintype_fun_eq_card, add_sub_assoc]
  simp only [hullDegMin_norm]

/-- **Its hull** has log-volume `(Σ_s log max (‖λ_s‖, ‖λ'_s‖)) / |ι|`: only the coordinatewise
maxima enter. -/
theorem hullDeg_padic_union_principal_hull {ι : Type*} [Fintype ι] (c c' : ι → ℚ_[p]ˣ) :
    hullDegHull p (fun _ : ι => ν) (pktHullPrincipal c ∪ pktHullPrincipal c') =
      (∑ s, Real.log (max ‖((c s : ℚ_[p]ˣ) : ℚ_[p])‖ ‖((c' s : ℚ_[p]ˣ) : ℚ_[p])‖)) /
        Fintype.card ι := by
  unfold hullDegHull
  rw [hullDeg_hull_union_principal]
  have := hullDeg_padic_principal p ν (hullDegMax c c')
  unfold hullDegRigid at this
  rw [this]
  simp only [hullDegMax_norm]

omit [BorelSpace ℚ_[p]] [ν.IsAddHaarMeasure] in
/-- **On the sets `λ · 𝒪`, (c) holds**: the hull is the set, so the two log-volumes agree, and
sets `λ · 𝒪` of equal log-volume have hulls of equal log-volume. -/
theorem hullDeg_principal_determined {ι : Type*} [Fintype ι] (c c' : ι → ℚ_[p]ˣ) :
    hullDegHull p (fun _ : ι => ν) (pktHullPrincipal c) =
        hullDegRigid p (fun _ : ι => ν) (pktHullPrincipal c) ∧
      (hullDegRigid p (fun _ : ι => ν) (pktHullPrincipal c) =
          hullDegRigid p (fun _ : ι => ν) (pktHullPrincipal c') →
        hullDegHull p (fun _ : ι => ν) (pktHullPrincipal c) =
          hullDegHull p (fun _ : ι => ν) (pktHullPrincipal c')) := by
  have h1 : ∀ d : ι → ℚ_[p]ˣ, hullDegHull p (fun _ : ι => ν) (pktHullPrincipal d) =
      hullDegRigid p (fun _ : ι => ν) (pktHullPrincipal d) := fun d => by
    rw [hullDegHull, hullDegRigid, hullDeg_hull_principal]
  exact ⟨h1 c, fun h => by rw [h1, h1, h]⟩

omit [BorelSpace ℚ_[p]] in
/-- **`𝒪 = ℤ_p²`**: a region, with `μ^log(𝒪) = μ^log(hull 𝒪) = 0`. -/
theorem hullDeg_padic_integers :
    hullDegRegion (fun _ : Fin 2 => ν) pktHullIntegers ∧
      hullDegRigid p (fun _ : Fin 2 => ν) pktHullIntegers = 0 ∧
      hullDegHull p (fun _ : Fin 2 => ν) pktHullIntegers = 0 := by
  rw [← pktHullPrincipal_one]
  refine ⟨hullDeg_region_of_subset _ subset_rfl (hullDeg_principal_measure_ne_zero _ 1), ?_, ?_⟩
  · rw [pktHullPrincipal_one]; exact padicMuLog_self p _ _
  · rw [hullDegHull, hullDeg_hull_principal, pktHullPrincipal_one]; exact padicMuLog_self p _ _

/-- **`p𝒪`**: a region, with `μ^log(p𝒪) = μ^log(hull p𝒪) = −log p`. -/
theorem hullDeg_padic_pO :
    hullDegRegion (fun _ : Fin 2 => ν) (hullDegPO p) ∧
      hullDegRigid p (fun _ : Fin 2 => ν) (hullDegPO p) = -Real.log p ∧
      hullDegHull p (fun _ : Fin 2 => ν) (hullDegPO p) = -Real.log p := by
  have hr : hullDegRigid p (fun _ : Fin 2 => ν) (hullDegPO p) = -Real.log p := by
    rw [hullDegPO, hullDeg_padic_principal, Fin.sum_univ_two, hullDegP_norm, Real.log_inv,
      Fintype.card_fin]
    push_cast
    ring
  refine ⟨hullDeg_region_of_subset _ subset_rfl (hullDeg_principal_measure_ne_zero _ _), hr, ?_⟩
  rw [← hr, hullDegHull, hullDegRigid, hullDegPO, hullDeg_hull_principal]

/-- **`pℤ_p × p⁻¹ℤ_p`**: a region with `μ^log = μ^log(hull) = 0`, the values of `𝒪`. -/
theorem hullDeg_padic_pp :
    hullDegRegion (fun _ : Fin 2 => ν) (pktHullPrincipal ![hullDegP p, (hullDegP p)⁻¹]) ∧
      hullDegRigid p (fun _ : Fin 2 => ν) (pktHullPrincipal ![hullDegP p, (hullDegP p)⁻¹]) = 0 ∧
      hullDegHull p (fun _ : Fin 2 => ν) (pktHullPrincipal ![hullDegP p, (hullDegP p)⁻¹]) = 0 := by
  have hr : hullDegRigid p (fun _ : Fin 2 => ν)
      (pktHullPrincipal ![hullDegP p, (hullDegP p)⁻¹]) = 0 := by
    rw [hullDeg_padic_principal, Fin.sum_univ_two]
    simp [hullDegP_norm]
  refine ⟨hullDeg_region_of_subset _ subset_rfl (hullDeg_principal_measure_ne_zero _ _), hr, ?_⟩
  rw [← hr, hullDegHull, hullDegRigid, hullDeg_hull_principal]

/-- **`(1, 1) + p𝒪`**: a region whose hull is `𝒪`, with `μ^log = −log p` and
`μ^log(hull) = 0`. -/
theorem hullDeg_padic_shifted :
    hullDegRegion (fun _ : Fin 2 => ν) (hullDegShifted p) ∧
      hullDegRigid p (fun _ : Fin 2 => ν) (hullDegShifted p) = -Real.log p ∧
      hullDegHull p (fun _ : Fin 2 => ν) (hullDegShifted p) = 0 ∧
      pktHull (hullDegShifted p) = pktHullIntegers := by
  have hp1 := hullDeg_p_inv_lt_one p
  have hhull : pktHull (hullDegShifted p) = pktHullIntegers := by
    rw [← pktHullPrincipal_one]
    apply hullDeg_hull_eq_of_attained
    · intro x hx
      rw [hullDegShifted, Set.mem_vadd_set] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      refine pktHull_mem_principal.mpr fun s => ?_
      have hys := pktHull_mem_principal.mp hy s
      rw [hullDegP_norm] at hys
      simp only [vadd_eq_add, Pi.add_apply, Units.val_one, Pi.one_apply, norm_one]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) (hys.trans hp1.le))
    · intro s
      refine ⟨(fun _ : Fin 2 => (1 : ℚ_[p])) +ᵥ (0 : Fin 2 → ℚ_[p]),
        ⟨0, pktHull_mem_principal.mpr fun t => by simp, rfl⟩,
        by simp⟩
  have h0 := hullDeg_principal_measure_ne_zero (fun _ : Fin 2 => ν) (fun _ => hullDegP p)
  refine ⟨hullDeg_region_of_subset (c := 1) _ ?_ ?_, ?_, ?_, hhull⟩
  · rw [pktHullPrincipal_one, ← hhull]; exact pktHull_extensive _
  · rw [hullDegShifted, measure_vadd]; exact h0
  · rw [hullDegRigid, hullDegShifted, padicMuLog_vadd]; exact (hullDeg_padic_pO p ν).2.1
  · rw [hullDegHull, hhull]; exact padicMuLog_self p _ _

/-- **`((1, p) + p²𝒪) ∪ ((p, 1) + p²𝒪)`**, a disjoint union of two balls: a region whose hull is
`𝒪`, with `μ^log = (log 2)/2 − 2 log p` and `μ^log(hull) = 0`. -/
theorem hullDeg_padic_twoBalls :
    hullDegRegion (fun _ : Fin 2 => ν) (hullDegTwoBalls p) ∧
      hullDegRigid p (fun _ : Fin 2 => ν) (hullDegTwoBalls p) =
        Real.log 2 / 2 - 2 * Real.log p ∧
      hullDegHull p (fun _ : Fin 2 => ν) (hullDegTwoBalls p) = 0 ∧
      pktHull (hullDegTwoBalls p) = pktHullIntegers := by
  have hp1 := hullDeg_p_inv_lt_one p
  have hp0 : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.out.pos)
  have hsq : (p : ℝ)⁻¹ ^ 2 < (p : ℝ)⁻¹ := by nlinarith
  set B : Set (Fin 2 → ℚ_[p]) := pktHullPrincipal fun _ => hullDegP p ^ 2 with hBdef
  have hB : ∀ y ∈ B, ∀ s, ‖y s‖ ≤ (p : ℝ)⁻¹ ^ 2 := fun y hy s => by
    have := pktHull_mem_principal.mp hy s
    rwa [hullDegP_sq_norm] at this
  have hnp : ‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹ := Padic.norm_p
  have hsub : hullDegTwoBalls p ⊆ pktHullPrincipal 1 := by
    rintro _ (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩) <;> refine pktHull_mem_principal.mpr fun s => ?_ <;>
      simp only [vadd_eq_add, Pi.add_apply, Units.val_one, Pi.one_apply, norm_one] <;>
      refine (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le ?_ ((hB y hy s).trans (hsq.trans hp1).le)) <;>
      fin_cases s <;> simp [hnp, hp1.le]
  have hhull : pktHull (hullDegTwoBalls p) = pktHullIntegers := by
    rw [← pktHullPrincipal_one]
    refine hullDeg_hull_eq_of_attained hsub fun s => ?_
    have h0B : (0 : Fin 2 → ℚ_[p]) ∈ B := pktHull_mem_principal.mpr fun t => by simp
    fin_cases s
    · exact ⟨_, Or.inl ⟨0, h0B, rfl⟩, by simp⟩
    · exact ⟨_, Or.inr ⟨0, h0B, rfl⟩, by simp⟩
  have hdisj : Disjoint (![1, (p : ℚ_[p])] +ᵥ B) (![(p : ℚ_[p]), 1] +ᵥ B) := by
    rw [Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ ⟨z, hz, hyz⟩
    have h1 : ‖(![1, (p : ℚ_[p])] +ᵥ y) 0‖ = 1 := by
      simp only [vadd_eq_add, Pi.add_apply, Matrix.cons_val_zero]
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, norm_one]
      · exact max_eq_left ((hB y hy 0).trans (hsq.trans hp1).le)
      · rw [norm_one]; exact ((hB y hy 0).trans_lt (hsq.trans hp1)).ne'
    have h2 : ‖(![(p : ℚ_[p]), 1] +ᵥ z) 0‖ < 1 := by
      simp only [vadd_eq_add, Pi.add_apply, Matrix.cons_val_zero]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
      · rw [hnp]; exact hp1
      · exact (hB z hz 0).trans_lt (hsq.trans hp1)
    have hyz' : ![(p : ℚ_[p]), 1] +ᵥ z = ![1, (p : ℚ_[p])] +ᵥ y := hyz
    rw [hyz', h1] at h2
    exact lt_irrefl _ h2
  have hmeas : Measure.pi (fun _ : Fin 2 => ν) (hullDegTwoBalls p) =
      Measure.pi (fun _ : Fin 2 => ν) B + Measure.pi (fun _ : Fin 2 => ν) B := by
    rw [hullDegTwoBalls, measure_union hdisj
      ((hullDeg_principal_measurableSet _).const_vadd _), measure_vadd, measure_vadd]
  have hBt := hullDeg_principal_measure_ne_top (fun _ : Fin 2 => ν) (fun _ => hullDegP p ^ 2)
  have hB0 := hullDeg_principal_measure_ne_zero (fun _ : Fin 2 => ν) (fun _ => hullDegP p ^ 2)
  refine ⟨hullDeg_region_of_subset _ hsub ?_, ?_, ?_, hhull⟩
  · rw [hmeas]; exact fun h => hB0 (add_eq_zero.mp h).1
  · have hr := hullDeg_padic_ratio p ν (fun _ : Fin 2 => hullDegP p ^ 2)
    rw [Fin.prod_univ_two, hullDegP_sq_norm] at hr
    unfold hullDegRigid padicMuLog
    rw [hmeas, ENNReal.toReal_add hBt hBt, ← two_mul, mul_div_assoc, hr,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
      Real.log_mul two_ne_zero (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_inv]
    push_cast
    ring
  · rw [hullDegHull, hhull]; exact padicMuLog_self p _ _

/-- **(a) fails on `ℚ_p²`**: no `c > 0` has `μ^log(hull U) = c · μ^log(U)` for all regions
(witness `(1, 1) + p𝒪`). -/
theorem hullDeg_not_scalarDescent : ¬ hullDegScalarDescent p (fun _ : Fin 2 => ν) := by
  rintro ⟨c, hc, h⟩
  obtain ⟨hT, hr, hh, -⟩ := hullDeg_padic_shifted p ν
  have := h _ hT
  rw [hr, hh] at this
  nlinarith [mul_pos hc (hullDeg_log_p_pos p)]

/-- **(b) fails on `ℚ_p²`**: no `c` has `μ^log(hull U) = μ^log(U) + c` for all regions
(witnesses `𝒪` and `(1, 1) + p𝒪`). -/
theorem hullDeg_not_shiftDescent : ¬ hullDegShiftDescent p (fun _ : Fin 2 => ν) := by
  rintro ⟨c, h⟩
  obtain ⟨hO, hOr, hOh⟩ := hullDeg_padic_integers p ν
  obtain ⟨hT, hr, hh, -⟩ := hullDeg_padic_shifted p ν
  have h1 := h _ hO
  have h2 := h _ hT
  rw [hOr, hOh] at h1
  rw [hr, hh] at h2
  linarith [hullDeg_log_p_pos p]

/-- **(c) fails on `ℚ_p²`**: `p𝒪` and `(1, 1) + p𝒪` both have log-volume `−log p`, and their hulls
have log-volumes `−log p` and `0`. -/
theorem hullDeg_not_determined : ¬ hullDegDetermined p (fun _ : Fin 2 => ν) := by
  intro h
  obtain ⟨hP, hPr, hPh⟩ := hullDeg_padic_pO p ν
  obtain ⟨hT, hr, hh, -⟩ := hullDeg_padic_shifted p ν
  have := h _ _ hP hT (hPr.trans hr.symm)
  rw [hPh, hh] at this
  linarith [hullDeg_log_p_pos p]

/-- **The shear preserves `μ^log` and not the log-volume of hulls.** It maps `𝒪` onto `𝒪` and
preserves `μ^log` of every set. For `U₀ = ℤ_p × p⁻¹ℤ_p`: `μ^log(U₀) = μ^log(hull U₀) = (log p)/2`;
the image of `U₀` has `μ^log = (log p)/2`, hull `p⁻¹𝒪` and `μ^log(hull) = log p`. -/
theorem hullDeg_shear :
    hullDegShear p '' pktHullIntegers = pktHullIntegers ∧
      (∀ U, hullDegRigid p (fun _ : Fin 2 => ν) (hullDegShear p '' U) =
        hullDegRigid p (fun _ : Fin 2 => ν) U) ∧
      hullDegRigid p (fun _ : Fin 2 => ν) (pktHullPrincipal ![1, (hullDegP p)⁻¹]) =
        Real.log p / 2 ∧
      hullDegHull p (fun _ : Fin 2 => ν) (pktHullPrincipal ![1, (hullDegP p)⁻¹]) =
        Real.log p / 2 ∧
      hullDegRigid p (fun _ : Fin 2 => ν)
        (hullDegShear p '' pktHullPrincipal ![1, (hullDegP p)⁻¹]) = Real.log p / 2 ∧
      pktHull (hullDegShear p '' pktHullPrincipal ![1, (hullDegP p)⁻¹]) =
        pktHullPrincipal (fun _ : Fin 2 => (hullDegP p)⁻¹) ∧
      hullDegHull p (fun _ : Fin 2 => ν)
        (hullDegShear p '' pktHullPrincipal ![1, (hullDegP p)⁻¹]) = Real.log p := by
  have hp1 := hullDeg_p_inv_lt_one p
  have hpge : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hO : hullDegShear p '' pktHullIntegers = pktHullIntegers := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ s
      fin_cases s
      · simp only [hullDegShear_apply]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx 0) (hx 1))
      · exact hx 1
    · intro hy
      refine ⟨![y 0 - y 1, y 1], fun s => ?_, ?_⟩
      · fin_cases s
        · rw [sub_eq_add_neg]
          refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
          rw [norm_neg]
          exact max_le (hy 0) (hy 1)
        · exact hy 1
      · ext i; fin_cases i <;> simp [hullDegShear_apply]
  have hrig : ∀ U, hullDegRigid p (fun _ : Fin 2 => ν) (hullDegShear p '' U) =
      hullDegRigid p (fun _ : Fin 2 => ν) U :=
    hullDeg_rigid_image_equiv p _ (hullDegShear p) (by rw [hO])
  have hU0 : hullDegRigid p (fun _ : Fin 2 => ν) (pktHullPrincipal ![1, (hullDegP p)⁻¹]) =
      Real.log p / 2 := by
    rw [hullDeg_padic_principal, Fin.sum_univ_two, Fintype.card_fin]
    simp [hullDegP_norm]
  have hhull : pktHull (hullDegShear p '' pktHullPrincipal ![1, (hullDegP p)⁻¹]) =
      pktHullPrincipal (fun _ : Fin 2 => (hullDegP p)⁻¹) := by
    apply hullDeg_hull_eq_of_attained
    · rintro _ ⟨x, hx, rfl⟩
      have h0 := pktHull_mem_principal.mp hx 0
      have h1 := pktHull_mem_principal.mp hx 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_one, norm_one,
        hullDegP_inv_norm] at h0 h1
      refine pktHull_mem_principal.mpr fun s => ?_
      rw [hullDegP_inv_norm]
      fin_cases s
      · simp only [hullDegShear_apply]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h0.trans hpge) h1)
      · exact h1
    · have hx : (![0, (p : ℚ_[p])⁻¹] : Fin 2 → ℚ_[p]) ∈ pktHullPrincipal ![1, (hullDegP p)⁻¹] := by
        refine pktHull_mem_principal.mpr fun s => ?_
        fin_cases s
        · simp
        · simp [hullDegP]
      intro s
      refine ⟨_, ⟨_, hx, rfl⟩, ?_⟩
      rw [hullDegP_inv_norm]
      fin_cases s <;> simp [hullDegShear_apply, Padic.norm_p]
  refine ⟨hO, hrig, hU0, ?_, (hrig _).trans hU0, hhull, ?_⟩
  · rw [← hU0, hullDegHull, hullDegRigid, hullDeg_hull_principal]
  · rw [hullDegHull, hhull]
    have := hullDeg_padic_principal p ν (fun _ : Fin 2 => (hullDegP p)⁻¹)
    unfold hullDegRigid at this
    rw [this, Fin.sum_univ_two, hullDegP_inv_norm, Fintype.card_fin]
    ring

end Padic

/-! ## Finite extensions of `ℚ_p` with the spectral norm -/

section Spectral

variable (p : ℕ) [hp : Fact p.Prime] {ι : Type*} [Fintype ι] (L : ι → Type*)
  [∀ s, Field (L s)] [∀ s, Algebra ℚ_[p] (L s)] [∀ s, FiniteDimensional ℚ_[p] (L s)]
  [∀ s, Algebra ℤ_[p] (L s)] [∀ s, IsScalarTower ℤ_[p] ℚ_[p] (L s)]

/-- **Monotonicity for finite extensions of `ℚ_p`** with the spectral norm and any Haar
measures: `μ^log(U) ≤ μ^log(hull U)` for every region. -/
theorem hullDeg_rigid_le_hull_spectral :
    letI : ∀ s, NormedField (L s) := fun s => spectralNorm.normedField ℚ_[p] (L s)
    letI : ∀ s, NormedAlgebra ℚ_[p] (L s) := fun s => spectralNorm.normedAlgebra ℚ_[p] (L s)
    letI : ∀ s, MeasurableSpace (L s) := fun s => borel (L s)
    ∀ (μ : ∀ s, Measure (L s)) [∀ s, (μ s).IsAddHaarMeasure] (U : Set (∀ s, L s)),
      hullDegRegion μ U → hullDegRigid p μ U ≤ hullDegHull p μ U := by
  let _ : ∀ s, NormedField (L s) := fun s => spectralNorm.normedField ℚ_[p] (L s)
  let _ : ∀ s, NormedAlgebra ℚ_[p] (L s) := fun s => spectralNorm.normedAlgebra ℚ_[p] (L s)
  let _ : ∀ s, MeasurableSpace (L s) := fun s => borel (L s)
  have _ : ∀ s, BorelSpace (L s) := fun s => ⟨rfl⟩
  have _ : ∀ s, ProperSpace (L s) := fun s => FiniteDimensional.proper ℚ_[p] (L s)
  intro μ _ U hU
  exact hullDeg_rigid_le_hull p μ (fun s => pktHullDiscrete_spectral p (L s)) hU

/-- **The hull of a union of two sets `λ · 𝒪`, `λ' · 𝒪`** for finite extensions of degrees
`d_s`: `μ^log(hull) = (Σ_s d_s log max (‖λ_s‖, ‖λ'_s‖)) / Σ_s d_s`. -/
theorem hullDeg_union_principal_spectral :
    letI : ∀ s, NormedField (L s) := fun s => spectralNorm.normedField ℚ_[p] (L s)
    letI : ∀ s, NormedAlgebra ℚ_[p] (L s) := fun s => spectralNorm.normedAlgebra ℚ_[p] (L s)
    letI : ∀ s, MeasurableSpace (L s) := fun s => borel (L s)
    ∀ (μ : ∀ s, Measure (L s)) [∀ s, (μ s).IsAddHaarMeasure] (c c' : ∀ s, (L s)ˣ),
      hullDegHull p μ (pktHullPrincipal c ∪ pktHullPrincipal c') =
        (∑ s, (Module.finrank ℚ_[p] (L s) : ℝ) *
          Real.log (max ‖((c s : (L s)ˣ) : L s)‖ ‖((c' s : (L s)ˣ) : L s)‖)) /
            ∑ s, (Module.finrank ℚ_[p] (L s) : ℝ) := by
  let _ : ∀ s, NormedField (L s) := fun s => spectralNorm.normedField ℚ_[p] (L s)
  let _ : ∀ s, NormedAlgebra ℚ_[p] (L s) := fun s => spectralNorm.normedAlgebra ℚ_[p] (L s)
  let _ : ∀ s, MeasurableSpace (L s) := fun s => borel (L s)
  have _ : ∀ s, ProperSpace (L s) := fun s => FiniteDimensional.proper ℚ_[p] (L s)
  intro μ _ c c'
  rw [hullDegHull, hullDeg_hull_union_principal, pktHull_muLog_principal p L μ]
  simp only [hullDegMax_norm]

end Spectral

end IUT.Countermodels.HullDegree
