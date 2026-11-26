import IUT.PaperIII.Corollary312.Indeterminacy
import IUT.PaperIV.LocalFields.Logarithm

/-!
# IUT III, upper semi-compatibility and the indeterminacy (Ind3)

Sources: Mochizuki, *Inter-universal Teichmüller Theory III*: Remark 1.1.1 (i), page 28;
Proposition 1.2 (v), (vi), pages 31 and 32; Remark 1.2.2 (i), (iii), pages 36 and 37;
Proposition 3.5 (ii), pages 104 to 106; Theorem 3.11 (i), (ii), pages 154 to 156 and 158;
Remark 3.11.1, pages 160, 161 and 166; proof of Corollary 3.12, Steps (iv) to (x), pages 177
to 181. Pages read for this file: 28, 29, 31, 32, 36, 37, 103 to 106, 154 to 156, 158, 160, 161,
166, 177 to 181. Pages checked against rendered images: all of these.

## What this file is and is not

**This file is not a formalization of Proposition 3.5, Theorem 3.11 or Corollary 3.12.** It
proves the local nonarchimedean inclusions behind "upper semi-compatibility" in one local field
(the normed-field model of `IUT.PaperIV.LocalFields.Logarithm`, and `ℚ_p`), and it types (Ind3)
by one faithful reading as a family of regions inside a container, combined with the orbit of
`Indeterminacy.lean`. No region is constructed from Hodge theaters, Kummer isomorphisms or the
log-theta-lattice. The results bound the log-volume of the hull of the possible images **from
above** (the direction of Step (x), page 181); they say nothing about the comparison of the
q-pilot region with that hull, which remains an unproved hypothesis of `Comparison.lean`.

## What the pages say

* Remark 1.1.1 (i), page 28: the log-links "that appear in such iterates are to be understood as
  being defined only on the [local] units" in their domains.
* Proposition 1.2 (v), pages 31 and 32: at `v ∈ 𝕍^non` the log-shell is compact (a_non), contains
  the submonoid of `Π_v`-invariants of `Ψ_{log(F_v)}` (b_non), and contains the image of the
  `Π_v`-invariants of `Ψ^×_{F_v}` (c_non).
* Remark 1.2.2 (i), page 36: concretely `I_k = (p*)⁻¹ · log_k(O_k^×) ⊆ k`, and (b_non), (c_non)
  are the inclusions `O_k^▷ = O_k \ {0} ⊆ O_k ⊆ I_k` and `log_k(O_k^×) ⊆ I_k`.
* Remark 1.2.2 (iii), page 37: the coric log-shells contain "not only the images, via the Kummer
  isomorphisms", of the `O^▷`, "but also the images, via the composite of the Kummer isomorphisms
  with the various iterates" of the log-link, "of the portions of the various `O^▷` ... on which
  these iterates are defined"; this is called "upper semi-commutativity".
* Proposition 3.5 (ii) (a), pages 104 and 105: for `v_ℚ ∈ 𝕍_ℚ^non` the module
  `I(𝕊^±_{j+1} F(n,∘𝔇_≻)_{v_ℚ})` "contains the images" of the Galois invariants of the groups of
  units `(Ψ_cns(n,m 𝔉_≻)_{|t|})^×_v`, via both (1) the tensor product over `|t|` of the Kummer
  isomorphisms and (2) the tensor product over `|t|` of their pre-composite "with the `m'`-th
  iterates ... of the log-links, for `m' ≥ 1`". Part (b), page 105, at archimedean places, is
  a statement about closed balls and **surjections** onto units; part (c) concerns bad places.
* (Ind3), Theorem 3.11 (ii), page 156: "as one varies `m ∈ ℤ`, the isomorphisms of (a) are
  'upper semi-compatible', relative to the log-links of the `n`-th column ..., in a sense that
  involves certain natural inclusions '⊆' at `v_ℚ ∈ 𝕍_ℚ^non` and certain natural surjections
  '↠' at `v_ℚ ∈ 𝕍_ℚ^arc`", with details in Proposition 3.5 (ii) (a), (b). The next sentence: the
  isomorphisms of (a) are "[precisely!] compatible" with the respective log-volumes as `m` varies.
* Step (iv), page 177: vertical coricity is available "only at the cost of admitting the
  'indeterminacy' constituted by the upper semi-compatibility of (Ind3)". Step (v), page 177:
  the mono-analytic log-shells serve as "multiradial mono-analytic containers". Step (x),
  page 181: the procession-normalized log-volumes are invariant under (Ind1), (Ind2) and convert
  (Ind3) into an inequality "[from above]".

## What is proved on real objects (part 1)

`logUnitIterateRegion start units log` is the sequence `S 0 = start`,
`S (n + 1) = log '' (S n ∩ units)`: the `n`-th iterate of the log-link, defined only on units as
Remark 1.1.1 (i) says, applied to `start`. For `start ⊆ O` (the units of Proposition 3.5 (ii) (a)
or the `O^▷` of Remark 1.2.2 (iii)), every `S n` lies in the log-shell:

* `extLogShell_contains_logUnitIterateRegion`: in a complete, locally compact normed
  `ℚ_p`-algebra field `K` (the model of finite extensions of `ℚ_p` in `Logarithm.lean`), with
  `O` the closed unit ball, units the unit sphere and `log = extLogUnit`;
* `padicLogShell_contains_logUnitIterateRegion`: the same over `ℚ_p` with `padicLogUnit` and
  `padicLogShell p = ℤ_p`.

This is Proposition 3.5 (ii) (a) and Remark 1.2.2 (iii) for **one** tensor factor (`j = 0`,
`|t| = 0`), with the Kummer isomorphisms taken to be identities and every level `m` of the
column identified with the same field. It rests on (b_non) and (c_non) only: `S 0 ⊆ O ⊆ I`
and `S (n + 1) ⊆ log(O^×) ⊆ I` (`logUnitIterateRegion_succ_subset`). Not covered: tensor
products over `|t|` and the Galois invariants in them, Kummer isomorphisms and vertical
coricity, part (b) (archimedean surjections), part (c) (bad places).

Over `ℚ_p` the chain is explicit: `S 1 = log(ℤ_p^×) = {‖z‖ ≤ 1 / p*}`
(`padic_logUnitIterateRegion_one`), which is strictly smaller than the container `ℤ_p`
(`padic_logUnitIterateRegion_one_ssubset`), and `S n = ∅` for `n ≥ 2`
(`padic_logUnitIterateRegion_add_two`), because `log(ℤ_p^×)` contains no unit. Over a ramified
finite extension the image `log(O^×)` can meet the units, so the chain need not stop; that is
not computed here.

## The typed (Ind3) (part 2): one faithful reading

`VerticalRegionFamily X ι` is data only: a container (the log-shell in the nonarchimedean
reading) and regions indexed by a vertical coordinate `ι` (the paper varies `m ∈ ℤ`; the iterate
family above is indexed by `m' ∈ ℕ`). `UpperSemiCompatible` is the named proposition that every
region lies in the container; it is proved for the iterate families (`padicIterateFamily`,
`extIterateFamily`) and is a hypothesis elsewhere. The possible image under (Ind3) is the hull
of `columnUnion`. Theorems: the hull of the union bounds every member; under
`UpperSemiCompatible` and with the container a hull, the hull of the union lies in the container
and its log-volume is at most that of the container, for any region log-volume monotone into the
hull domain (the condition `logVol_mono` of `RegionComparison`).

Combination with (Ind1), (Ind2): for an `IndeterminacyOrbit` `O`, the joint possible images are
`a • R_m` (`jointColumnImage`). Without further hypotheses their union lies in the orbit union
of the container (`jointColumnUnion_subset_containerOrbit`), so the log-volume of its hull is at
most that of the hull of the container's orbit. Under `ContainerStable` (every element of `ind1`
and of `ind2` maps the container onto itself), that orbit union is the container. Measure
preservation by `ind1`, `ind2` (the abstract form of the invariance of Step (x)) gives the bound
`logVolume (a • R_m) ≤ logVolume container` for every member
(`logVolume_jointColumnImage_le_shellContainer`): (Ind3) becomes an inequality from above.

**Stability is a hypothesis.** Proposition 1.2 (vi), page 32, asserts that the `Ism`-orbit of
isomorphisms of mono-analytic log-shells is compatible with "the respective log-shells", which is
the nonarchimedean (Ind2) of page 154 acting on one factor; it is not proved here. No page read
for this file asserts that the automorphisms of the procession (Ind1) preserve the log-shell of
the tensor packet.

**Alternatives not chosen.** (i) The upward closure `{Y | ∃ a, a • base ⊑ Y}` for a relation
`⊑` (mentioned in `Indeterminacy.lean`); (ii) a relation between regions at consecutive `m`
(`R_m ⊆ R_{m+1}`), which the pages do not assert: they assert containment of every image in one
coric container; (iii) at archimedean places, a surjection from a closed ball onto the units
(Proposition 3.5 (ii) (b)), which is not a containment and is not modeled; (iv) indexing by
`ℤ` with a translation symmetry (page 106), not modeled.

## Examples (part 3)

* `padic_iUnion_nonzeroIntegers`: with `start = O^▷ = ℤ_p \ {0}` (Remark 1.2.2), the union of
  the chain is the container `ℤ_p`, for every `p`.
* `padic_two_iUnion_units_ssubset`: with `start` the units (Proposition 3.5 (ii) (a)) and
  `p = 2`, the union `ℤ_2^× ∪ 4ℤ_2` is strictly smaller than the container `ℤ_2` (it misses `2`).
* On `ℝ` with the interval hull of `Comparison.lean`: a family whose union is strictly smaller
  than the container while the hull of the union equals it (`example_gap_union`), and one whose
  hull is strictly smaller than the container (`example_hull_ssubset`).
-/

namespace IUT.PaperIII.Corollary312

open MeasureTheory Set Pointwise IUT.PaperIII.Remark3_9_5 IUT.Prerequisites.PadicLog
  IUT.PaperIV.LocalFields

/-! ## Part 1: iterates of the log-link on units, inside the log-shell -/

section LogUnitIterate

variable {K : Type*}

/-- The regions along a vertical line: `S 0 = start` and `S (n + 1) = log '' (S n ∩ units)`, the
`(n + 1)`-th iterate of the log-link applied to the part of `start` on which it is defined (the
log-link is defined only on units, Remark 1.1.1 (i), page 28). -/
def logUnitIterateRegion (start units : Set K) (log : K → K) : ℕ → Set K
  | 0 => start
  | n + 1 => log '' (logUnitIterateRegion start units log n ∩ units)

/-- Every iterate of positive order lies in the image of the units (the pre-log-shell). -/
theorem logUnitIterateRegion_succ_subset (start units : Set K) (log : K → K) (n : ℕ) :
    logUnitIterateRegion start units log (n + 1) ⊆ log '' units := by
  rw [logUnitIterateRegion]
  exact image_mono inter_subset_right

/-- If `start` and the image of the units lie in `I`, every iterate lies in `I`. -/
theorem logUnitIterateRegion_subset_of {start units I : Set K} {log : K → K}
    (hstart : start ⊆ I) (hlog : log '' units ⊆ I) :
    ∀ n, logUnitIterateRegion start units log n ⊆ I
  | 0 => hstart
  | n + 1 => (logUnitIterateRegion_succ_subset start units log n).trans hlog

end LogUnitIterate

section ExtField

variable (p : ℕ) [Fact p.Prime] {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K]

/-- **Upper semi-compatibility, one factor, finite extension model.** In a complete, locally
compact normed `ℚ_p`-algebra field `K`, for any `start` in the closed unit ball `O`, every iterate
of `extLogUnit` on the unit sphere applied to `start` lies in the log-shell `extLogShell p K`.
From (b_non) `O ⊆ I` (`extLogShell_unitBall_subset`) and (c_non) `log(O^×) ⊆ I`
(`extLogUnit_image_subset_extLogShell`); Proposition 3.5 (ii) (a), pages 104 and 105, for
`j = 0` with identity Kummer maps. -/
theorem extLogShell_contains_logUnitIterateRegion [CompleteSpace K] [ProperSpace K]
    {start : Set K} (hstart : start ⊆ {x | ‖x‖ ≤ 1}) (n : ℕ) :
    logUnitIterateRegion start {u : K | ‖u‖ = 1} extLogUnit n ⊆ extLogShell p K :=
  logUnitIterateRegion_subset_of (hstart.trans (extLogShell_unitBall_subset p))
    (extLogUnit_image_subset_extLogShell p) n

end ExtField

section PadicBase

variable (p : ℕ) [Fact p.Prime]

/-- The image of the unit sphere of `ℚ_p` under `padicLogUnit` is `log(ℤ_p^×)`. -/
theorem padicLogUnit_image_unitSphere :
    padicLogUnit p '' {u : ℚ_[p] | ‖u‖ = 1} =
      Set.range (fun u : ℤ_[p]ˣ => padicLogUnit p ((u : ℤ_[p]) : ℚ_[p])) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' : ‖u‖ = 1 := hu
    exact ⟨PadicInt.mkUnits hu', rfl⟩
  · rintro ⟨u, rfl⟩
    refine ⟨_, ?_, rfl⟩
    show ‖((u : ℤ_[p]) : ℚ_[p])‖ = 1
    rw [← PadicInt.norm_def]
    exact PadicInt.norm_units u

/-- **Upper semi-compatibility, one factor, over `ℚ_p`.** For any `start ⊆ ℤ_p`, every iterate
of `padicLogUnit` on the units applied to `start` lies in the log-shell `padicLogShell p`. -/
theorem padicLogShell_contains_logUnitIterateRegion {start : Set ℚ_[p]}
    (hstart : start ⊆ {x | ‖x‖ ≤ 1}) (n : ℕ) :
    logUnitIterateRegion start {u : ℚ_[p] | ‖u‖ = 1} (padicLogUnit p) n ⊆ padicLogShell p :=
  logUnitIterateRegion_subset_of (hstart.trans (padicLogShell_eq (p := p)).symm.subset)
    (by rw [padicLogUnit_image_unitSphere]; exact padicLogUnit_range_subset_padicLogShell) n

/-- The first iterate over `ℚ_p`: if `start` contains the units, `S 1 = log(ℤ_p^×)`, the closed
ball of radius `1 / p*`. -/
theorem padic_logUnitIterateRegion_one {start : Set ℚ_[p]}
    (h : {u : ℚ_[p] | ‖u‖ = 1} ⊆ start) :
    logUnitIterateRegion start {u : ℚ_[p] | ‖u‖ = 1} (padicLogUnit p) 1 =
      {z : ℚ_[p] | ‖z‖ ≤ ((padicLogPStar p : ℕ) : ℝ)⁻¹} := by
  show padicLogUnit p '' (start ∩ {u : ℚ_[p] | ‖u‖ = 1}) = _
  rw [inter_eq_right.mpr h, padicLogUnit_image_unitSphere, padicLogUnit_range]

/-- Over `ℚ_p` no iterate of positive order contains a unit: `log(ℤ_p^×)` has norm `≤ 1 / p* < 1`. -/
theorem padic_logUnitIterateRegion_succ_inter_unitSphere (start : Set ℚ_[p]) (k : ℕ) :
    logUnitIterateRegion start {u : ℚ_[p] | ‖u‖ = 1} (padicLogUnit p) (k + 1) ∩
      {u : ℚ_[p] | ‖u‖ = 1} = ∅ := by
  refine eq_empty_of_forall_notMem fun z hz => ?_
  have h := logUnitIterateRegion_succ_subset start _ (padicLogUnit p) k hz.1
  rw [padicLogUnit_image_unitSphere, padicLogUnit_range] at h
  have h1 : ‖z‖ = 1 := hz.2
  have h2 : ‖z‖ ≤ ((padicLogPStar p : ℕ) : ℝ)⁻¹ := h
  linarith [padicLog_inv_pStar_lt_one (p := p)]

/-- Over `ℚ_p` the chain stops: `S n = ∅` for `n ≥ 2`. -/
theorem padic_logUnitIterateRegion_add_two (start : Set ℚ_[p]) (k : ℕ) :
    logUnitIterateRegion start {u : ℚ_[p] | ‖u‖ = 1} (padicLogUnit p) (k + 2) = ∅ := by
  show padicLogUnit p '' (logUnitIterateRegion start _ _ (k + 1) ∩ _) = ∅
  rw [padic_logUnitIterateRegion_succ_inter_unitSphere, image_empty]

/-- The container is strictly larger than the first image: `log(ℤ_p^×) ⊊ ℤ_p` (`1` is missing). -/
theorem padic_logUnitIterateRegion_one_ssubset {start : Set ℚ_[p]}
    (h : {u : ℚ_[p] | ‖u‖ = 1} ⊆ start) :
    logUnitIterateRegion start {u : ℚ_[p] | ‖u‖ = 1} (padicLogUnit p) 1 ⊂ padicLogShell p := by
  rw [padic_logUnitIterateRegion_one p h, padicLogShell_eq]
  refine Set.ssubset_iff_subset_ne.mpr
    ⟨fun z (hz : ‖z‖ ≤ _) => hz.trans padicLog_inv_pStar_lt_one.le, fun heq => ?_⟩
  have hmem : (1 : ℚ_[p]) ∈ {z : ℚ_[p] | ‖z‖ ≤ ((padicLogPStar p : ℕ) : ℝ)⁻¹} := by
    rw [heq]; show ‖(1 : ℚ_[p])‖ ≤ 1; rw [norm_one]
  have h1 : ‖(1 : ℚ_[p])‖ ≤ ((padicLogPStar p : ℕ) : ℝ)⁻¹ := hmem
  rw [norm_one] at h1
  linarith [padicLog_inv_pStar_lt_one (p := p)]

end PadicBase

/-! ## Part 2: (Ind3) as a family of regions in a container -/

/-- One faithful reading of the (Ind3) data (page 156): a container (the log-shell, the
"multiradial mono-analytic container" of Step (v), page 177) and regions indexed by a vertical
coordinate. Data only; containment is the separate proposition `UpperSemiCompatible`. -/
structure VerticalRegionFamily (X ι : Type*) where
  /-- The container. -/
  shellContainer : Set X
  /-- The region at vertical coordinate `m`. -/
  columnRegion : ι → Set X

namespace VerticalRegionFamily

variable {X ι : Type*} (F : VerticalRegionFamily X ι)

/-- Upper semi-compatibility in the nonarchimedean reading: every region lies in the container
(Proposition 3.5 (ii) (a), pages 104 and 105). A proposition about the family, proved for the
iterate families of part 1 and a hypothesis elsewhere. -/
def UpperSemiCompatible : Prop := ∀ m, F.columnRegion m ⊆ F.shellContainer

/-- The union of the regions along the vertical line. -/
def columnUnion : Set X := ⋃ m, F.columnRegion m

theorem columnUnion_subset_shellContainer (h : F.UpperSemiCompatible) :
    F.columnUnion ⊆ F.shellContainer :=
  iUnion_subset h

variable {hullDomain hulls : Set (Set X)} {hull : Set X → Set X}

/-- Every region lies in the hull of the union, by (P2). -/
theorem columnRegion_subset_hull_columnUnion (isHull : IsHullMap hullDomain hulls hull)
    (hU : F.columnUnion ∈ hullDomain) (m : ι) : F.columnRegion m ⊆ hull F.columnUnion :=
  (subset_iUnion F.columnRegion m).trans (isHull.P2 _ hU)

/-- If the family is upper semi-compatible and the container is a hull, the hull of the union
lies in the container, by (P3) and (P1). -/
theorem hull_columnUnion_subset_shellContainer (isHull : IsHullMap hullDomain hulls hull)
    (hU : F.columnUnion ∈ hullDomain) (hC : F.shellContainer ∈ hulls)
    (h : F.UpperSemiCompatible) : hull F.columnUnion ⊆ F.shellContainer := by
  have := isHull.P3 _ hU _ (isHull.hull_sub hC) (F.columnUnion_subset_shellContainer h)
  rwa [isHull.P1 _ hC] at this

/-- For a region log-volume monotone into the hull domain, every region has log-volume at most
that of the hull of the union. -/
theorem logVol_columnRegion_le_hull (isHull : IsHullMap hullDomain hulls hull)
    (logVol : Set X → EReal) (hmono : ∀ S T : Set X, S ⊆ T → T ∈ hullDomain → logVol S ≤ logVol T)
    (hU : F.columnUnion ∈ hullDomain) (m : ι) :
    logVol (F.columnRegion m) ≤ logVol (hull F.columnUnion) :=
  hmono _ _ (F.columnRegion_subset_hull_columnUnion isHull hU m)
    (isHull.hull_sub (isHull.maps_to _ hU))

/-- **The container bounds the possible image.** Under upper semi-compatibility, with the
container a hull, the log-volume of the hull of the union is at most that of the container. -/
theorem logVol_hull_columnUnion_le_shellContainer (isHull : IsHullMap hullDomain hulls hull)
    (logVol : Set X → EReal) (hmono : ∀ S T : Set X, S ⊆ T → T ∈ hullDomain → logVol S ≤ logVol T)
    (hU : F.columnUnion ∈ hullDomain) (hC : F.shellContainer ∈ hulls)
    (h : F.UpperSemiCompatible) : logVol (hull F.columnUnion) ≤ logVol F.shellContainer :=
  hmono _ _ (F.hull_columnUnion_subset_shellContainer isHull hU hC h) (isHull.hull_sub hC)

end VerticalRegionFamily

namespace IndeterminacyOrbit

variable {X A ι : Type*} [Group A] [MulAction A X] (O : IndeterminacyOrbit X A)
  (F : VerticalRegionFamily X ι)

/-- The orbit of the container under the same (Ind1), (Ind2). -/
def containerOrbit : IndeterminacyOrbit X A := { O with baseRegion := F.shellContainer }

/-- The possible image indexed by an element of the joint group of (Ind1), (Ind2) and a
vertical coordinate (Ind3). -/
def jointColumnImage (g : O.jointGroup) (m : ι) : Set X := (g : A) • F.columnRegion m

/-- The union of all possible images under (Ind1), (Ind2), (Ind3). -/
def jointColumnUnion : Set X := ⋃ (g : O.jointGroup) (m : ι), O.jointColumnImage F g m

/-- Under upper semi-compatibility, the union of all possible images lies in the orbit union of
the container. No stability of the container is needed. -/
theorem jointColumnUnion_subset_containerOrbit (h : F.UpperSemiCompatible) :
    O.jointColumnUnion F ⊆ (O.containerOrbit F).orbitUnion := by
  intro x hx
  obtain ⟨g, hg⟩ := mem_iUnion.mp hx
  obtain ⟨m, hm⟩ := mem_iUnion.mp hg
  rw [orbitUnion]
  exact mem_iUnion.mpr ⟨⟨g, g.2⟩, smul_set_mono (h m) hm⟩

/-- Stability of the container under (Ind1) and (Ind2): every element of `ind1` and every
element of `ind2` maps the container onto itself. A hypothesis; see the module docstring for
what the pages say about it. -/
def ContainerStable : Prop :=
  (∀ a ∈ O.ind1, a • F.shellContainer = F.shellContainer) ∧
    ∀ a ∈ O.ind2, a • F.shellContainer = F.shellContainer

/-- Under stability, the orbit union of the container is the container. -/
theorem orbitUnion_containerOrbit_eq (hs : O.ContainerStable F) :
    (O.containerOrbit F).orbitUnion = F.shellContainer := by
  have hle : O.jointGroup ≤ MulAction.stabilizer A F.shellContainer :=
    sup_le (fun a ha => MulAction.mem_stabilizer_iff.mpr (hs.1 a ha))
      (fun a ha => MulAction.mem_stabilizer_iff.mpr (hs.2 a ha))
  apply Subset.antisymm
  · rw [orbitUnion]
    refine iUnion_subset fun g => ?_
    show (g : A) • F.shellContainer ⊆ F.shellContainer
    rw [MulAction.mem_stabilizer_iff.mp (hle g.2)]
  · exact (O.containerOrbit F).baseRegion_subset_orbitUnion

variable {hullDomain hulls : Set (Set X)} {hull : Set X → Set X}

/-- Every joint possible image lies in the hull of the union of all of them, by (P2). -/
theorem jointColumnImage_subset_hull (isHull : IsHullMap hullDomain hulls hull)
    (hJ : O.jointColumnUnion F ∈ hullDomain) (g : O.jointGroup) (m : ι) :
    O.jointColumnImage F g m ⊆ hull (O.jointColumnUnion F) :=
  (subset_iUnion₂ (s := fun (g : O.jointGroup) (m : ι) => O.jointColumnImage F g m) g m).trans
    (isHull.P2 _ hJ)

/-- **(Ind1), (Ind2), (Ind3) together, without stability.** Under upper semi-compatibility, the
log-volume of the hull of the union of all possible images is at most the log-volume of the hull
of the orbit union of the container. -/
theorem logVol_hull_jointColumnUnion_le_hull_containerOrbit
    (isHull : IsHullMap hullDomain hulls hull) (logVol : Set X → EReal)
    (hmono : ∀ S T : Set X, S ⊆ T → T ∈ hullDomain → logVol S ≤ logVol T)
    (hJ : O.jointColumnUnion F ∈ hullDomain) (hO : (O.containerOrbit F).orbitUnion ∈ hullDomain)
    (h : F.UpperSemiCompatible) :
    logVol (hull (O.jointColumnUnion F)) ≤ logVol (hull (O.containerOrbit F).orbitUnion) :=
  hmono _ _ (isHull.P3 _ hJ _ hO (O.jointColumnUnion_subset_containerOrbit F h))
    (isHull.hull_sub (isHull.maps_to _ hO))

/-- **(Ind1), (Ind2), (Ind3) together, with stability.** If moreover the container is a hull
and is stable under (Ind1) and (Ind2), the log-volume of the hull of the union of all possible
images is at most the log-volume of the container. -/
theorem logVol_hull_jointColumnUnion_le_shellContainer
    (isHull : IsHullMap hullDomain hulls hull) (logVol : Set X → EReal)
    (hmono : ∀ S T : Set X, S ⊆ T → T ∈ hullDomain → logVol S ≤ logVol T)
    (hJ : O.jointColumnUnion F ∈ hullDomain) (hC : F.shellContainer ∈ hulls)
    (hs : O.ContainerStable F) (h : F.UpperSemiCompatible) :
    logVol (hull (O.jointColumnUnion F)) ≤ logVol F.shellContainer := by
  have hO : (O.containerOrbit F).orbitUnion ∈ hullDomain := by
    rw [O.orbitUnion_containerOrbit_eq F hs]; exact isHull.hull_sub hC
  have := O.logVol_hull_jointColumnUnion_le_hull_containerOrbit F isHull logVol hmono hJ hO h
  rwa [O.orbitUnion_containerOrbit_eq F hs, isHull.P1 _ hC] at this

/-- **(Ind3) as an inequality from above.** If every element of `ind1` and of `ind2` preserves
`μ` (the abstract form of the invariance asserted in Step (x), page 181, a hypothesis) and the
family is upper semi-compatible, every joint possible image has log-volume at most that of the
container. -/
theorem logVolume_jointColumnImage_le_shellContainer [MeasurableSpace X] (μ : Measure X)
    (h1 : ∀ a ∈ O.ind1, ∀ S : Set X, μ (a • S) = μ S)
    (h2 : ∀ a ∈ O.ind2, ∀ S : Set X, μ (a • S) = μ S) (h : F.UpperSemiCompatible)
    (g : O.jointGroup) (m : ι) :
    logVolume μ (O.jointColumnImage F g m) ≤ logVolume μ F.shellContainer := by
  have hle : O.jointGroup ≤ measureInvariantSubgroup A μ :=
    sup_le (fun a ha => h1 a ha) (fun a ha => h2 a ha)
  rw [jointColumnImage, logVolume, hle g.2]
  exact logVolume_mono μ (h m)

end IndeterminacyOrbit

/-! ## Part 3: the iterate families as instances, and examples -/

section Instances

/-- The iterate family over `ℚ_p`: container `padicLogShell p`, regions the iterates of part 1. -/
noncomputable def padicIterateFamily (p : ℕ) [Fact p.Prime] (start : Set ℚ_[p]) :
    VerticalRegionFamily ℚ_[p] ℕ :=
  ⟨padicLogShell p, logUnitIterateRegion start {u : ℚ_[p] | ‖u‖ = 1} (padicLogUnit p)⟩

theorem padicIterateFamily_upperSemiCompatible (p : ℕ) [Fact p.Prime] {start : Set ℚ_[p]}
    (hstart : start ⊆ {x | ‖x‖ ≤ 1}) : (padicIterateFamily p start).UpperSemiCompatible :=
  padicLogShell_contains_logUnitIterateRegion p hstart

/-- The iterate family in the finite extension model: container `extLogShell p K`. -/
noncomputable def extIterateFamily (p : ℕ) (K : Type*) [NormedField K] (start : Set K) :
    VerticalRegionFamily K ℕ :=
  ⟨extLogShell p K, logUnitIterateRegion start {u : K | ‖u‖ = 1} extLogUnit⟩

theorem extIterateFamily_upperSemiCompatible (p : ℕ) [Fact p.Prime] {K : Type*} [NormedField K]
    [NormedAlgebra ℚ_[p] K] [CompleteSpace K] [ProperSpace K] {start : Set K}
    (hstart : start ⊆ {x | ‖x‖ ≤ 1}) : (extIterateFamily p K start).UpperSemiCompatible :=
  extLogShell_contains_logUnitIterateRegion p hstart

/-- `O^▷ = ℤ_p \ {0}` of Remark 1.2.2 (i), page 36, as a subset of `ℚ_p`. -/
def padicNonzeroIntegers (p : ℕ) [Fact p.Prime] : Set ℚ_[p] := {x | x ≠ 0 ∧ ‖x‖ ≤ 1}

/-- **Union equal to the container.** Starting from `O^▷` (Remark 1.2.2 (iii)), the union of
the chain over `ℚ_p` is the container `ℤ_p`: `S 0 = ℤ_p \ {0}` and `0 ∈ S 1`. -/
theorem padic_iUnion_nonzeroIntegers (p : ℕ) [Fact p.Prime] :
    (padicIterateFamily p (padicNonzeroIntegers p)).columnUnion =
      (padicIterateFamily p (padicNonzeroIntegers p)).shellContainer := by
  apply Subset.antisymm
  · exact VerticalRegionFamily.columnUnion_subset_shellContainer _
      (padicIterateFamily_upperSemiCompatible p fun x hx => hx.2)
  · intro y hy
    have hy' : ‖y‖ ≤ 1 := by
      have : y ∈ padicLogShell p := hy
      rw [padicLogShell_eq] at this; exact this
    by_cases h0 : y = 0
    · have hsph : {u : ℚ_[p] | ‖u‖ = 1} ⊆ padicNonzeroIntegers p := by
        intro u hu
        have hu' : ‖u‖ = 1 := hu
        refine ⟨fun hu0 => ?_, hu'.le⟩
        rw [hu0, norm_zero] at hu'
        exact zero_ne_one hu'
      refine mem_iUnion.mpr ⟨1, ?_⟩
      show y ∈ logUnitIterateRegion (padicNonzeroIntegers p) {u : ℚ_[p] | ‖u‖ = 1}
        (padicLogUnit p) 1
      rw [padic_logUnitIterateRegion_one p hsph]
      show ‖y‖ ≤ _
      rw [h0, norm_zero]
      positivity
    · exact mem_iUnion.mpr ⟨0, show y ≠ 0 ∧ ‖y‖ ≤ 1 from ⟨h0, hy'⟩⟩

/-- **Union strictly smaller than the container.** Starting from the units (Proposition 3.5 (ii)
(a)) with `p = 2`, the union `ℤ_2^× ∪ 4ℤ_2` of the chain misses `2 ∈ ℤ_2`. -/
theorem padic_two_iUnion_units_ssubset :
    (padicIterateFamily 2 {u : ℚ_[2] | ‖u‖ = 1}).columnUnion ⊂
      (padicIterateFamily 2 {u : ℚ_[2] | ‖u‖ = 1}).shellContainer := by
  have h2 : ‖(2 : ℚ_[2])‖ = 1 / 2 := by
    have := Padic.norm_p (p := 2)
    push_cast at this
    rw [this]; norm_num
  refine Set.ssubset_iff_subset_ne.mpr ⟨VerticalRegionFamily.columnUnion_subset_shellContainer _
    (padicIterateFamily_upperSemiCompatible 2 fun x (hx : ‖x‖ = 1) => hx.le), fun heq => ?_⟩
  have hmem : (2 : ℚ_[2]) ∈ (padicIterateFamily 2 {u : ℚ_[2] | ‖u‖ = 1}).shellContainer := by
    show (2 : ℚ_[2]) ∈ padicLogShell 2
    rw [padicLogShell_eq]
    show ‖(2 : ℚ_[2])‖ ≤ 1
    rw [h2]; norm_num
  rw [← heq] at hmem
  obtain ⟨n, hn⟩ := mem_iUnion.mp hmem
  match n, hn with
  | 0, hn =>
    have h1 : ‖(2 : ℚ_[2])‖ = 1 := hn
    rw [h2] at h1; norm_num at h1
  | 1, hn =>
    have hn' : (2 : ℚ_[2]) ∈ logUnitIterateRegion {u : ℚ_[2] | ‖u‖ = 1}
        {u : ℚ_[2] | ‖u‖ = 1} (padicLogUnit 2) 1 := hn
    rw [padic_logUnitIterateRegion_one 2 subset_rfl] at hn'
    have h1 : ‖(2 : ℚ_[2])‖ ≤ ((padicLogPStar 2 : ℕ) : ℝ)⁻¹ := hn'
    rw [h2] at h1; norm_num [padicLogPStar] at h1
  | k + 2, hn =>
    have hn' : (2 : ℚ_[2]) ∈ logUnitIterateRegion {u : ℚ_[2] | ‖u‖ = 1}
        {u : ℚ_[2] | ‖u‖ = 1} (padicLogUnit 2) (k + 2) := hn
    rw [padic_logUnitIterateRegion_add_two] at hn'
    exact hn'

end Instances

namespace VerticalExample

open IntervalExample

/-- The regions `[0, 1/8]` and `[3/8, 1/2]` of `IntervalExample.intervalImage`, with container
`c`. -/
noncomputable def gapFamily (c : Set ℝ) : VerticalRegionFamily ℝ Bool := ⟨c, intervalImage⟩

theorem gapFamily_upperSemiCompatible {c : Set ℝ} (hc : Icc 0 (1 / 2) ⊆ c) :
    (gapFamily c).UpperSemiCompatible := by
  rintro (_ | _)
  · exact (Icc_subset_Icc le_rfl (by norm_num)).trans hc
  · exact (Icc_subset_Icc (by norm_num) le_rfl).trans hc

/-- **Union strictly smaller, hull equal.** With container `[0, 1/2]`, the union misses `1/4`,
while the interval hull of the union is the container. -/
theorem example_gap_union :
    (gapFamily (Icc 0 (1 / 2))).columnUnion ⊂ (gapFamily (Icc 0 (1 / 2))).shellContainer ∧
      hull (gapFamily (Icc 0 (1 / 2))).columnUnion = (gapFamily (Icc 0 (1 / 2))).shellContainer := by
  refine ⟨Set.ssubset_iff_subset_ne.mpr ⟨VerticalRegionFamily.columnUnion_subset_shellContainer _
    (gapFamily_upperSemiCompatible subset_rfl), fun heq => ?_⟩, hull_union⟩
  have h : (1 / 4 : ℝ) ∈ (gapFamily (Icc 0 (1 / 2))).columnUnion := by
    rw [heq]; show (1 / 4 : ℝ) ∈ Icc 0 (1 / 2); exact ⟨by norm_num, by norm_num⟩
  have h' : (1 / 4 : ℝ) ∈ ⋃ i, intervalImage i := h
  rw [union_eq] at h'
  rcases h' with h' | h'
  · exact absurd h'.2 (by norm_num)
  · exact absurd h'.1 (by norm_num)

/-- **Hull strictly smaller.** With container `[0, 1]`, the family is upper semi-compatible and
the hull `[0, 1/2]` of the union is strictly smaller than the container. -/
theorem example_hull_ssubset :
    (gapFamily (Icc 0 1)).UpperSemiCompatible ∧
      hull (gapFamily (Icc 0 1)).columnUnion ⊂ (gapFamily (Icc 0 1)).shellContainer := by
  refine ⟨gapFamily_upperSemiCompatible (Icc_subset_Icc le_rfl (by norm_num)), ?_⟩
  show hull (⋃ i, intervalImage i) ⊂ Icc 0 1
  rw [hull_union]
  refine Set.ssubset_iff_subset_ne.mpr ⟨Icc_subset_Icc le_rfl (by norm_num), fun heq => ?_⟩
  have h : (1 : ℝ) ∈ Icc (0 : ℝ) (1 / 2) := by rw [heq]; exact ⟨by norm_num, le_rfl⟩
  exact absurd h.2 (by norm_num)

end VerticalExample

end IUT.PaperIII.Corollary312
