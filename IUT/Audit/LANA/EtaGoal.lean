import Mathlib
import IUT.Audit.ScholzeStix.Diagram
import IUT.Audit.ScholzeStix.Blurring
import IUT.Prerequisites.PadicVolume

/-!
# The LANA report's simplified model: basic prime strips, pointed lines, the main goal

Source: the LANA project (F. Kato, J. Commelin, Y. Hoshi, K. Kedlaya, A. Topaz), *Project LANA
Interim Report on IUT Theory*, July 2026. The TeX source was read; no page was rendered, so
places are cited by section number of the report (counted from its section headings), not by
page. Sections read for this file: 1.4 (notation, morphisms of actions), 4.7 to 4.10 (GM-data,
abstract copies, compact structure, prime-strips), 5 (basic prime strips, the q-pilot BPS),
6 (log-shells, volume containers, log-links), 7.2 (steps 5 to 8 of the Θ-value action), 8.1
(the Θ-pilot BPS, the Θ-link), 9 (from Theorem 3.11 to Corollary 3.12, the properties (IPL),
(SHE), (APT)), 10 (the η algorithm and the main goal), 11 (the Scholze–Stix hexagon). Also
read: issue 2 of the report's repository (an open idea, no argument).

**Category of this file: a model.** The report replaces the prime-strips of IUT by simplified
objects ("basic prime strips", BPS) and says so (section 5.1). Everything below is about those
simplified objects, or about a further simplification of them stated in each docstring. No
statement of IUT I to IV is formalized here, and nothing here proves or refutes IUT III,
Corollary 3.12, the main goal of the report, or any position in the discussion of that
corollary.

## What is defined and proved

1. *Étale BPS* (section 5.1.1): a family of topological groups indexed by places, each
   isomorphic to a reference group (`lanaIsEtaleBPS`); isomorphisms are families of continuous
   group isomorphisms. Any two étale BPS are isomorphic (`lana_etaleBPS_iso_exists`).
2. *Étale-unit BPS* (sections 4.7, 4.9, 5.1.1): per place, GM-data `G ⟳ M` (a topological
   group acting continuously on a topological monoid) with a family of submonoids indexed by
   the open subgroups (the compact structure). An isomorphism (`LanaGMIso`) is a pair of
   continuous isomorphisms compatible with the actions (section 1.4.3) and carrying `N_H` to
   `N'_{φ_G(H)}`. Inverses and composites (`lanaGMIsoInv`, `lanaGMIsoComp`), and: any two
   étale-unit BPS isomorphic to the same reference are isomorphic
   (`lana_etUnitBPS_iso_exists`).
3. *Value-group BPS with local pilots* (section 5.1.2): a one-dimensional oriented real
   vector space `C` with nonzero local pilots whose sum over the bad places is nonzero
   (`LanaValBPS`), the product formula `PF` (`lanaPF`, the kernel of `⊕_v ℝ → C`), and
   isomorphisms (`LanaValBPSIso`, linear isomorphisms sending each local pilot to the
   corresponding one, with no orientation clause, as printed). The report's lemma of section
   5.1.3: two such BPS are isomorphic exactly when their product formulas agree
   (`lana_valBPS_iso_iff_PF`).
4. *Pointed oriented real lines* (the remark at the end of section 5.1.2: with the product
   formula fixed, a value-group BPS "is simply given by" an oriented line and a negative
   pilot): `LanaPointedLine`, `LanaPointedLineIso`. Rigidity: a linear map out of a line is
   determined by its value on a nonzero vector (`lana_linearMap_eq_iff_pilot`), so an
   isomorphism of pointed lines is unique (`lana_pointedLineIso_unique`); one exists between
   any two (`lana_pointedLineIso_exists`), and a linear isomorphism that sends a negative pilot
   to a negative pilot preserves the orientations (`lana_mapOrient_of_mapPilot`).
5. *The remark of section 9.2* ("linked" is vacuous because the category of BPS is a connected
   groupoid). Precise form: for BPS whose étale-unit portions are isomorphic to one reference
   and whose value-group portions are pointed lines, any two are isomorphic
   (`lana_bps_iso_exists`). What it shows: the property (IPL), read as the mere existence of an
   isomorphism to the input prime strip, holds for every pair of such BPS and so distinguishes
   none. For the local-pilot form the groupoid is not connected: its isomorphism classes are
   the product formulas (`lana_valBPS_iso_iff_PF`); the report's remark presupposes the
   convention of section 5.1.2 that the product formula is fixed.
6. *`ℝ^ss`* (section 10.2): measurable sets of a measure space modulo equal volume
   (`lanaRss`, `lanaRssClass`, `lanaRssClass_eq_iff`). For any placement of these classes in a
   real line, two linear maps `η, η'` out of a line `ℝ^val` that send the pilot to the classes
   of `T` and `T'` are equal exactly when `T` and `T'` have the same volume
   (`lana_eta_eq_iff_class`, `lana_eta_eq_iff_volume`). So the report's equality
   `η^q = η^anab_S` is, in the model, the equality of two volumes, that is, of two
   log-volumes.
7. *A schema for the main goal of section 10.2*, `lanaEtaGoalFor`, with the action of
   `ℕ` on the volume container taken as **data**: the action is given by the map `θ` by which
   the generator `1 ∈ ℕ` acts on subsets (the action of `n` is the `n`-th iterate). The report
   constructs this action by the η algorithm, whose anabelian steps 2 to 6 the report states
   without construction (section 10.1); they are not formalized, so the action cannot be
   defined here. The report's goal is the instance of this schema for the action the η
   algorithm would produce; that action is not constructed, so the goal itself is not stated
   here. To show that the definition alone carries no content, both
   outcomes occur for concrete actions on the container `ℚ_p` with the Haar measure normalized
   on `ℤ_p`, the log-shell `I = ℤ_p` and the q-pilot region `p · ℤ_p`: multiplication by `p`
   admits a suitable `S` (`lanaEtaGoalFor_padic_holds`), multiplication by `p ^ 2` admits none
   (`lanaEtaGoalFor_padic_fails`).
8. *Issue 2 of the report's repository* (the `j²` scaling "need not be preserved under the
   abstract Θ-link"). Model statement (`lana_issue2_model`): the abstract isomorphism `Φ` of
   two pointed lines is unique and sends pilot to pilot, so it has factor `1` on pilots; if
   degree maps send the Θ-pilot to `s · D` and the q-pilot to `D` with `D ≠ 0`, where
   `s = (1² + ⋯ + (ℓ*)²)/ℓ*` is `IUT.Audit.ScholzeStix.avgSq ℓ*` (the factor of the Θ-pilot BPS
   of section 8.1.1 and of the hexagon of section 11.2), then `d_Θ = s · (d_q ∘ Φ)`, and the
   square commutes exactly when `s = 1`, that is, for `ℓ* = 1` only; for `ℓ* ≥ 2` it does not
   commute and the corresponding cycle of `IUT.Audit.ScholzeStix.Diagram` is inconsistent
   (`lana_issue2_not_commute`). This is the non-commutativity of the hexagon already recorded
   in `IUT.Audit.ScholzeStix`; it is neither an argument for nor an argument against the
   corollary, and it does not test the second half of the issue (a one-directional comparison
   inside the common container), which is the main goal in other words.

## Interpretation choices

* *References as parameters.* "Isomorphic to the local Galois group at `v`" and "isomorphic to
  `(G_v ⟳ Ō^{×μ}_v, {I^κ_H})`" (sections 4.9, 5.1.1) are taken relative to a reference family
  given as a parameter. The reference objects themselves (the absolute Galois group of `K_v`
  for initial Θ-data, the monoid `Ō^×_v/μ` and its Kummer structure) are not constructed; this
  clause of the definitions is missing.
* *Compact structure.* A family of submonoids indexed by open subgroups. The report's
  condition that it "corresponds to `{I^κ_H}`" under some isomorphism is the clause of the
  previous item.
* *Actions.* The report says "continuous group action"; here `MulAction` with
  `ContinuousSMul`, not necessarily by monoid automorphisms.
* *Orientation.* An orientation of a line is a ray (`Module.Ray ℝ C`); "negative" means that
  `−φ` spans the chosen ray. In the pointed form the orientation is determined by the pilot.
  The report's isomorphisms of value-group BPS (section 5.1.2) carry no orientation clause;
  `lana_mapOrient_of_mapPilot` shows that for negative pilots the clause is automatic.
* *Sign of the q-pilot.* Section 5.2.3 gives the q-pilot value-group BPS as `C = ℝ` with local
  pilots `deg(q_v)`, `deg(p_v)`, `2π`, all positive, while the remark of section 5.1.2 calls the
  pilot negative. The report does not say how the two agree. This file therefore takes degrees
  as data without a sign claim (item 8) and does not construct the q-pilot BPS.
* *`ℝ^ss`.* "Adelic and measurable" (section 10.2): "adelic" is not defined in the report; for
  a container with one place it is empty, and only measurability is kept. The report does not
  say how `ℝ^ss` is a real vector space; item 6 assumes only that the classes are placed
  injectively in some real line. "Suitable" in "there exists some suitable `S`" is not defined;
  the definition asks for `S` inside the log-shell, as in "`S ⊂ VC(I_v)`".
* *The pilot of `ℝ^ss` under `η^q`* is "the class of `{q_v O_v}`"; in the model it is the class
  of a measurable set `Q` given as a parameter.

## Not proved, not represented

* The η algorithm (section 10.1, steps 1 to 9), in particular the anabelian steps 2 to 6
  (subgroups, Kummer maps, cyclotomic rigidity, decomposition groups, Galois evaluation): the
  report gives them without construction. So `η^anab_S` is not defined from a BPS; the action
  of `ℕ` is a parameter.
* The large volume container `VC(K)`, its log-shell and `O`-versions, the holomorphic hull, the
  procession normalization and the LGP element (section 6.2): only a one-place, one-factor
  container (`ℚ_p` with log-shell `ℤ_p`) is used, for the two examples of item 7.
* The q-pilot and Θ-pilot value-group BPS of sections 5.2.3 and 8.1.1 as constructions from
  initial Θ-data, and Hodge theaters, Θ-links, log-links: not formalized.
* The properties (SHE) and (APT) of section 9.2: the report quotes them in words that are not
  definitions; nothing is stated about them.
* Whether `lanaEtaGoalFor` holds for the action that the η algorithm would produce: this
  is the open problem the report isolates; the file says nothing about it.
-/

namespace IUT.Audit.LANA

open MeasureTheory

/-! ### Étale BPS (section 5.1.1) -/

section Etale

variable {V : Type*}

/-- An *étale BPS* (report, section 5.1.1): a family of topological groups `G v`, indexed by
the places, each isomorphic to the local Galois group at `v`. The local Galois groups are the
reference family `Gref`, a parameter; they are not constructed here. -/
def lanaIsEtaleBPS (Gref G : V → Type*) [∀ v, Group (Gref v)] [∀ v, TopologicalSpace (Gref v)]
    [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)] : Prop :=
  ∀ v, Nonempty (G v ≃ₜ* Gref v)

/-- An isomorphism of étale BPS (report, section 5.1.1): a family of isomorphisms of
topological groups. -/
def LanaEtaleBPSIso (G G' : V → Type*) [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
    [∀ v, Group (G' v)] [∀ v, TopologicalSpace (G' v)] : Type _ :=
  ∀ v, G v ≃ₜ* G' v

/-- Any two étale BPS with the same reference are isomorphic. -/
theorem lana_etaleBPS_iso_exists {Gref G G' : V → Type*} [∀ v, Group (Gref v)]
    [∀ v, TopologicalSpace (Gref v)] [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
    [∀ v, Group (G' v)] [∀ v, TopologicalSpace (G' v)]
    (h : lanaIsEtaleBPS Gref G) (h' : lanaIsEtaleBPS Gref G') :
    Nonempty (LanaEtaleBPSIso G G') :=
  ⟨fun v => (h v).some.trans (h' v).some.symm⟩

end Etale

/-! ### GM-data with compact structure and étale-unit BPS (sections 4.7, 4.9, 5.1.1) -/

section GMData

/-- An isomorphism of GM-data with compact structure (report, sections 1.4.3, 4.7, 4.9 and
5.1.1): continuous isomorphisms `φ_G : G ≃ G'` and `φ_M : M ≃ M'` with
`φ_M (g • m) = φ_G g • φ_M m`, carrying the submonoid `N_H` of the compact structure onto
`N'_{φ_G(H)}` for every open subgroup `H` (the open subgroup `φ_G(H)` is written as the preimage
under `φ_G⁻¹`). -/
structure LanaGMIso (G M G' M' : Type*) [Group G] [TopologicalSpace G] [Monoid M]
    [TopologicalSpace M] [SMul G M] [Group G'] [TopologicalSpace G'] [Monoid M']
    [TopologicalSpace M'] [SMul G' M'] (N : OpenSubgroup G → Submonoid M)
    (N' : OpenSubgroup G' → Submonoid M') where
  /-- The isomorphism of the étale-like portions. -/
  lanaGrp : G ≃ₜ* G'
  /-- The isomorphism of the Frobenius-like portions. -/
  lanaMon : M ≃ₜ* M'
  /-- Compatibility with the actions (section 1.4.3). -/
  lanaAct : ∀ g m, lanaMon (g • m) = lanaGrp g • lanaMon m
  /-- Compatibility with the compact structures (section 5.1.1). -/
  lanaKummer : ∀ H : OpenSubgroup G,
    (N H).map lanaMon = N' (H.comap lanaGrp.symm.toMulEquiv.toMonoidHom lanaGrp.symm.continuous)

variable {G M G' M' G'' M'' : Type*} [Group G] [TopologicalSpace G] [Monoid M]
  [TopologicalSpace M] [SMul G M] [Group G'] [TopologicalSpace G'] [Monoid M']
  [TopologicalSpace M'] [SMul G' M'] [Group G''] [TopologicalSpace G''] [Monoid M'']
  [TopologicalSpace M''] [SMul G'' M'']
  {N : OpenSubgroup G → Submonoid M} {N' : OpenSubgroup G' → Submonoid M'}
  {N'' : OpenSubgroup G'' → Submonoid M''}

/-- The inverse of an isomorphism of GM-data with compact structure. -/
def lanaGMIsoInv (e : LanaGMIso G M G' M' N N') : LanaGMIso G' M' G M N' N where
  lanaGrp := e.lanaGrp.symm
  lanaMon := e.lanaMon.symm
  lanaAct g m := by
    apply e.lanaMon.injective
    rw [e.lanaAct]
    simp
  lanaKummer H := by
    have h := congrArg (fun S : Submonoid M' => (S : Set M'))
      (e.lanaKummer (H.comap e.lanaGrp.toMulEquiv.toMonoidHom e.lanaGrp.continuous))
    have hH : (H.comap e.lanaGrp.toMulEquiv.toMonoidHom e.lanaGrp.continuous).comap
        e.lanaGrp.symm.toMulEquiv.toMonoidHom e.lanaGrp.symm.continuous = H := by
      ext x
      show e.lanaGrp (e.lanaGrp.symm x) ∈ H ↔ x ∈ H
      rw [ContinuousMulEquiv.apply_symm_apply]
    simp only [hH, Submonoid.coe_map] at h
    apply SetLike.coe_injective
    rw [Submonoid.coe_map, ← h, Set.image_image]
    simp only [ContinuousMulEquiv.symm_apply_apply, Set.image_id']
    congr 2

/-- The composite of two isomorphisms of GM-data with compact structure. -/
def lanaGMIsoComp (e : LanaGMIso G M G' M' N N') (f : LanaGMIso G' M' G'' M'' N' N'') :
    LanaGMIso G M G'' M'' N N'' where
  lanaGrp := e.lanaGrp.trans f.lanaGrp
  lanaMon := e.lanaMon.trans f.lanaMon
  lanaAct g m := by
    simp only [ContinuousMulEquiv.trans_apply]
    rw [e.lanaAct, f.lanaAct]
  lanaKummer H := by
    have h1 := congrArg (fun S : Submonoid M' => (S : Set M')) (e.lanaKummer H)
    have h2 := congrArg (fun S : Submonoid M'' => (S : Set M''))
      (f.lanaKummer (H.comap e.lanaGrp.symm.toMulEquiv.toMonoidHom e.lanaGrp.symm.continuous))
    simp only [Submonoid.coe_map] at h1 h2
    apply SetLike.coe_injective
    rw [Submonoid.coe_map]
    have hc : ⇑(e.lanaMon.trans f.lanaMon) = f.lanaMon ∘ e.lanaMon := rfl
    rw [hc, Set.image_comp, h1, h2]
    congr 2

variable {V : Type*}

/-- An *étale-unit BPS* (report, section 5.1.1): per place, GM-data `G v ⟳ M v` (a topological
group acting continuously on a topological monoid) with a compact structure `N v`, isomorphic
to the reference `(Gr v ⟳ Mr v, Nr v)`. The reference stands for
`(G_v ⟳ Ō^{×μ}_v, {I^κ_H}_H)` of the report; it is a parameter and is not constructed here. -/
def lanaIsEtUnitBPS (Gr Mr G M : V → Type*) [∀ v, Group (Gr v)] [∀ v, TopologicalSpace (Gr v)]
    [∀ v, IsTopologicalGroup (Gr v)] [∀ v, Monoid (Mr v)] [∀ v, TopologicalSpace (Mr v)]
    [∀ v, ContinuousMul (Mr v)] [∀ v, MulAction (Gr v) (Mr v)] [∀ v, ContinuousSMul (Gr v) (Mr v)]
    [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)] [∀ v, IsTopologicalGroup (G v)]
    [∀ v, Monoid (M v)] [∀ v, TopologicalSpace (M v)] [∀ v, ContinuousMul (M v)]
    [∀ v, MulAction (G v) (M v)] [∀ v, ContinuousSMul (G v) (M v)]
    (Nr : ∀ v, OpenSubgroup (Gr v) → Submonoid (Mr v))
    (N : ∀ v, OpenSubgroup (G v) → Submonoid (M v)) : Prop :=
  ∀ v, Nonempty (LanaGMIso (G v) (M v) (Gr v) (Mr v) (N v) (Nr v))

/-- Any two étale-unit BPS with the same reference are isomorphic. This is the first sentence
of the proof of the report's lemma in section 5.1.3 ("we always have an isomorphism of the
étale-unit portions"). -/
theorem lana_etUnitBPS_iso_exists {Gr Mr G M G₁ M₁ : V → Type*} [∀ v, Group (Gr v)]
    [∀ v, TopologicalSpace (Gr v)] [∀ v, IsTopologicalGroup (Gr v)] [∀ v, Monoid (Mr v)]
    [∀ v, TopologicalSpace (Mr v)] [∀ v, ContinuousMul (Mr v)] [∀ v, MulAction (Gr v) (Mr v)]
    [∀ v, ContinuousSMul (Gr v) (Mr v)] [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
    [∀ v, IsTopologicalGroup (G v)] [∀ v, Monoid (M v)] [∀ v, TopologicalSpace (M v)]
    [∀ v, ContinuousMul (M v)] [∀ v, MulAction (G v) (M v)] [∀ v, ContinuousSMul (G v) (M v)]
    [∀ v, Group (G₁ v)] [∀ v, TopologicalSpace (G₁ v)] [∀ v, IsTopologicalGroup (G₁ v)]
    [∀ v, Monoid (M₁ v)] [∀ v, TopologicalSpace (M₁ v)] [∀ v, ContinuousMul (M₁ v)]
    [∀ v, MulAction (G₁ v) (M₁ v)] [∀ v, ContinuousSMul (G₁ v) (M₁ v)]
    {Nr : ∀ v, OpenSubgroup (Gr v) → Submonoid (Mr v)}
    {N : ∀ v, OpenSubgroup (G v) → Submonoid (M v)}
    {N₁ : ∀ v, OpenSubgroup (G₁ v) → Submonoid (M₁ v)}
    (h : lanaIsEtUnitBPS Gr Mr G M Nr N) (h₁ : lanaIsEtUnitBPS Gr Mr G₁ M₁ Nr N₁) :
    Nonempty (∀ v, LanaGMIso (G v) (M v) (G₁ v) (M₁ v) (N v) (N₁ v)) :=
  ⟨fun v => lanaGMIsoComp (h v).some (lanaGMIsoInv (h₁ v).some)⟩

end GMData

/-! ### Value-group BPS with local pilots (section 5.1.2) and the lemma of section 5.1.3 -/

section ValueGroup

variable {V : Type*} (bad : Finset V)

/-- A *value-group BPS* (report, section 5.1.2): a one-dimensional oriented real vector space
`C` (here: the type `C` with `finrank ℝ C = 1` and a ray `lanaOrient`) and local pilots
`φ_v ∈ C`, all nonzero, whose sum over the bad places (the *pilot*) is nonzero. -/
structure LanaValBPS (C : Type*) [AddCommGroup C] [Module ℝ C] where
  /-- `C` is one-dimensional. -/
  lanaFinrank : Module.finrank ℝ C = 1
  /-- The orientation of `C`. -/
  lanaOrient : Module.Ray ℝ C
  /-- The local pilots. -/
  lanaLocalPilot : V → C
  /-- Every local pilot is nonzero. -/
  lanaLocalPilot_ne : ∀ v, lanaLocalPilot v ≠ 0
  /-- The pilot `φ_C = ∑_{v bad} φ_v` is nonzero. -/
  lanaPilot_ne : ∑ v ∈ bad, lanaLocalPilot v ≠ 0

variable {bad} {C C' : Type*} [AddCommGroup C] [Module ℝ C] [AddCommGroup C'] [Module ℝ C']

/-- The *product formula* `PF(B)` (report, section 5.1.2): the kernel of the linear map
`⊕_v ℝ_v → C`, `a ↦ ∑_v a_v φ_v`. -/
noncomputable def lanaPF (B : LanaValBPS bad C) : Submodule ℝ (V →₀ ℝ) :=
  LinearMap.ker (Finsupp.linearCombination ℝ B.lanaLocalPilot)

/-- An isomorphism of value-group BPS (report, section 5.1.2): a linear isomorphism sending each
local pilot to the corresponding local pilot. As printed, no orientation clause. -/
structure LanaValBPSIso (B : LanaValBPS bad C) (B' : LanaValBPS bad C') where
  /-- The underlying linear isomorphism. -/
  lanaEquiv : C ≃ₗ[ℝ] C'
  /-- Local pilots go to local pilots. -/
  lanaMapLocal : ∀ v, lanaEquiv (B.lanaLocalPilot v) = B'.lanaLocalPilot v

/-- The map `⊕_v ℝ_v → C` of a value-group BPS is surjective ("it is immediate", section
5.1.2). -/
theorem lanaValBPS_surjective (B : LanaValBPS bad C) :
    Function.Surjective (Finsupp.linearCombination ℝ B.lanaLocalPilot) := by
  obtain ⟨v, -⟩ : bad.Nonempty := by
    by_contra h
    obtain rfl := Finset.not_nonempty_iff_eq_empty.mp h
    exact B.lanaPilot_ne Finset.sum_empty
  intro w
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' _ (B.lanaLocalPilot_ne v)).mp B.lanaFinrank w
  exact ⟨Finsupp.single v c, by rw [Finsupp.linearCombination_single, hc]⟩

/-- The report's lemma of section 5.1.3, for the value-group portions: two value-group BPS are
isomorphic if and only if their product formulas agree. -/
theorem lana_valBPS_iso_iff_PF (B : LanaValBPS bad C) (B' : LanaValBPS bad C') :
    Nonempty (LanaValBPSIso B B') ↔ lanaPF B = lanaPF B' := by
  constructor
  · rintro ⟨Φ, hΦ⟩
    have hcomp : Φ.toLinearMap ∘ₗ Finsupp.linearCombination ℝ B.lanaLocalPilot =
        Finsupp.linearCombination ℝ B'.lanaLocalPilot := by
      ext v
      simp [hΦ]
    unfold lanaPF
    rw [← hcomp, LinearEquiv.ker_comp]
  · intro h
    let f := Finsupp.linearCombination ℝ B.lanaLocalPilot
    let f' := Finsupp.linearCombination ℝ B'.lanaLocalPilot
    let Φ : C ≃ₗ[ℝ] C' :=
      ((f.quotKerEquivOfSurjective (lanaValBPS_surjective B)).symm.trans
        (Submodule.quotEquivOfEq _ _ h)).trans
        (f'.quotKerEquivOfSurjective (lanaValBPS_surjective B'))
    refine ⟨⟨Φ, fun v => ?_⟩⟩
    have hv : B.lanaLocalPilot v = f (Finsupp.single v 1) := by
      simp [f]
    have hv' : B'.lanaLocalPilot v = f' (Finsupp.single v 1) := by
      simp [f']
    have hs : (f.quotKerEquivOfSurjective (lanaValBPS_surjective B)).symm
        (f (Finsupp.single v 1)) = Submodule.Quotient.mk (Finsupp.single v 1) := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    rw [hv, hv']
    change f'.quotKerEquivOfSurjective (lanaValBPS_surjective B')
      (Submodule.quotEquivOfEq _ _ h ((f.quotKerEquivOfSurjective (lanaValBPS_surjective B)).symm
        (f (Finsupp.single v 1)))) = _
    rw [hs]
    exact LinearMap.quotKerEquivOfSurjective_apply_mk f' _ _

end ValueGroup

/-! ### Pointed oriented real lines (end of section 5.1.2) and rigidity -/

section PointedLine

variable {C C' : Type*} [AddCommGroup C] [Module ℝ C] [AddCommGroup C'] [Module ℝ C']

/-- A *pointed oriented real line* (report, remark at the end of section 5.1.2): a
one-dimensional real vector space with an orientation (a ray) and a negative element, the
pilot ("negative": `−φ` spans the chosen ray). -/
structure LanaPointedLine (C : Type*) [AddCommGroup C] [Module ℝ C] where
  /-- `C` is one-dimensional. -/
  lanaFinrank : Module.finrank ℝ C = 1
  /-- The orientation. -/
  lanaOrient : Module.Ray ℝ C
  /-- The pilot. -/
  lanaPilot : C
  /-- The pilot is nonzero. -/
  lanaPilot_ne : lanaPilot ≠ 0
  /-- The pilot is negative for the orientation. -/
  lanaPilot_neg : rayOfNeZero ℝ (-lanaPilot) (neg_ne_zero.mpr lanaPilot_ne) = lanaOrient

/-- An isomorphism of pointed oriented real lines: a linear isomorphism preserving the
orientations and sending pilot to pilot. -/
structure LanaPointedLineIso (L : LanaPointedLine C) (L' : LanaPointedLine C') where
  /-- The underlying linear isomorphism. -/
  lanaEquiv : C ≃ₗ[ℝ] C'
  /-- It preserves the orientations. -/
  lanaMapOrient : Module.Ray.map lanaEquiv L.lanaOrient = L'.lanaOrient
  /-- It sends the pilot to the pilot. -/
  lanaMapPilot : lanaEquiv L.lanaPilot = L'.lanaPilot

/-- Rigidity: a linear map out of a one-dimensional space is determined by its value on one
nonzero vector `φ`. -/
theorem lana_linearMap_eq_iff_pilot (hC : Module.finrank ℝ C = 1) {φ : C} (hφ : φ ≠ 0)
    (f g : C →ₗ[ℝ] C') : f = g ↔ f φ = g φ := by
  refine ⟨fun h => h ▸ rfl, fun h => LinearMap.ext fun x => ?_⟩
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' φ hφ).mp hC x
  rw [map_smul, map_smul, h]

/-- An isomorphism of pointed oriented real lines is unique. -/
theorem lana_pointedLineIso_unique {L : LanaPointedLine C} {L' : LanaPointedLine C'}
    (e e' : LanaPointedLineIso L L') : e = e' := by
  obtain ⟨f, hfo, hf⟩ := e
  obtain ⟨g, hgo, hg⟩ := e'
  have : f = g := LinearEquiv.toLinearMap_injective
    ((lana_linearMap_eq_iff_pilot L.lanaFinrank L.lanaPilot_ne _ _).mpr (hf.trans hg.symm))
  subst this
  rfl

private theorem lana_rayOfNeZero_congr {a b : C'} (h : a = b) (ha : a ≠ 0) (hb : b ≠ 0) :
    rayOfNeZero ℝ a ha = rayOfNeZero ℝ b hb := by
  subst h; rfl

/-- A linear isomorphism that sends a negative pilot to a negative pilot preserves the
orientations. So the orientation clause, absent from the report's isomorphisms of value-group
BPS, is automatic in the pointed form. -/
theorem lana_mapOrient_of_mapPilot (L : LanaPointedLine C) (L' : LanaPointedLine C')
    (e : C ≃ₗ[ℝ] C') (he : e L.lanaPilot = L'.lanaPilot) :
    Module.Ray.map e L.lanaOrient = L'.lanaOrient := by
  rw [← L.lanaPilot_neg, ← L'.lanaPilot_neg, Module.Ray.map_apply]
  exact lana_rayOfNeZero_congr (by rw [map_neg, he]) _ _

/-- The linear isomorphism `ℝ ≃ C`, `c ↦ c • φ`, of a pointed line. -/
noncomputable def lanaLineCoord (L : LanaPointedLine C) : ℝ ≃ₗ[ℝ] C :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℝ C L.lanaPilot)
    ⟨fun _ _ h => smul_left_injective ℝ L.lanaPilot_ne h, fun w =>
      (finrank_eq_one_iff_of_ne_zero' _ L.lanaPilot_ne).mp L.lanaFinrank w⟩

/-- `lanaLineCoord L` sends `1` to the pilot. -/
theorem lanaLineCoord_one (L : LanaPointedLine C) : lanaLineCoord L 1 = L.lanaPilot := by
  show (1 : ℝ) • L.lanaPilot = L.lanaPilot
  exact one_smul ℝ _

/-- Between any two pointed oriented real lines there is an isomorphism. -/
theorem lana_pointedLineIso_exists (L : LanaPointedLine C) (L' : LanaPointedLine C') :
    Nonempty (LanaPointedLineIso L L') := by
  let e := (lanaLineCoord L).symm.trans (lanaLineCoord L')
  have he : e L.lanaPilot = L'.lanaPilot := by
    have h1 : (lanaLineCoord L).symm L.lanaPilot = 1 := by
      rw [LinearEquiv.symm_apply_eq, lanaLineCoord_one]
    show lanaLineCoord L' ((lanaLineCoord L).symm L.lanaPilot) = _
    rw [h1, lanaLineCoord_one]
  exact ⟨⟨e, lana_mapOrient_of_mapPilot L L' e he, he⟩⟩

/-- The real line `ℝ` with its standard orientation (the ray of `1`) and a negative pilot `a`:
pointed lines exist. -/
noncomputable def lanaRealPointedLine (a : ℝ) (ha : a < 0) : LanaPointedLine ℝ where
  lanaFinrank := Module.finrank_self ℝ
  lanaOrient := rayOfNeZero ℝ 1 one_ne_zero
  lanaPilot := a
  lanaPilot_ne := ha.ne
  lanaPilot_neg := by
    rw [ray_eq_iff]
    have : -a = (-a) • (1 : ℝ) := by simp
    rw [this]
    exact SameRay.sameRay_pos_smul_left _ (by linarith)

end PointedLine

/-! ### The remark of section 9.2: BPS form a connected groupoid -/

section Connected

variable {V : Type*} {Gr Mr G M G₁ M₁ : V → Type*} [∀ v, Group (Gr v)]
  [∀ v, TopologicalSpace (Gr v)] [∀ v, IsTopologicalGroup (Gr v)] [∀ v, Monoid (Mr v)]
  [∀ v, TopologicalSpace (Mr v)] [∀ v, ContinuousMul (Mr v)] [∀ v, MulAction (Gr v) (Mr v)]
  [∀ v, ContinuousSMul (Gr v) (Mr v)] [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, IsTopologicalGroup (G v)] [∀ v, Monoid (M v)] [∀ v, TopologicalSpace (M v)]
  [∀ v, ContinuousMul (M v)] [∀ v, MulAction (G v) (M v)] [∀ v, ContinuousSMul (G v) (M v)]
  [∀ v, Group (G₁ v)] [∀ v, TopologicalSpace (G₁ v)] [∀ v, IsTopologicalGroup (G₁ v)]
  [∀ v, Monoid (M₁ v)] [∀ v, TopologicalSpace (M₁ v)] [∀ v, ContinuousMul (M₁ v)]
  [∀ v, MulAction (G₁ v) (M₁ v)] [∀ v, ContinuousSMul (G₁ v) (M₁ v)]
  {Nr : ∀ v, OpenSubgroup (Gr v) → Submonoid (Mr v)}
  {N : ∀ v, OpenSubgroup (G v) → Submonoid (M v)}
  {N₁ : ∀ v, OpenSubgroup (G₁ v) → Submonoid (M₁ v)}
  {C C₁ : Type*} [AddCommGroup C] [Module ℝ C] [AddCommGroup C₁] [Module ℝ C₁]

/-- The remark of section 9.2, in the form the definitions support: two BPS (report, section
5.1.3: an étale-unit portion and a value-group portion) whose étale-unit portions are
isomorphic to one reference and whose value-group portions are pointed oriented lines are
isomorphic. Every pair of such BPS is linked by an isomorphism; so the property (IPL), read as
the mere existence of an isomorphism to the input prime strip, holds for all of them and
distinguishes none. With local pilots instead of pointed lines the statement fails, and the
isomorphism classes are the product formulas (`lana_valBPS_iso_iff_PF`). -/
theorem lana_bps_iso_exists (h : lanaIsEtUnitBPS Gr Mr G M Nr N)
    (h₁ : lanaIsEtUnitBPS Gr Mr G₁ M₁ Nr N₁) (L : LanaPointedLine C) (L₁ : LanaPointedLine C₁) :
    Nonempty ((∀ v, LanaGMIso (G v) (M v) (G₁ v) (M₁ v) (N v) (N₁ v)) ×
      LanaPointedLineIso L L₁) :=
  ⟨((lana_etUnitBPS_iso_exists h h₁).some, (lana_pointedLineIso_exists L L₁).some)⟩

end Connected

/-! ### `ℝ^ss` and the reduction of `η^q = η^anab_S` to volumes (section 10.2) -/

section Rss

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- Equal volume, on measurable sets: the relation defining `ℝ^ss` (report, section 10.2). -/
def lanaSSSetoid : Setoid {T : Set X // MeasurableSet T} where
  r T T' := μ T.1 = μ T'.1
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩

/-- `ℝ^ss` (report, section 10.2): measurable subsets of the volume container modulo equality
of volumes. "Adelic" is not represented (see the module docstring). -/
def lanaRss : Type _ := Quotient (lanaSSSetoid μ)

/-- The class in `ℝ^ss` of a measurable set. -/
def lanaRssClass (T : Set X) (hT : MeasurableSet T) : lanaRss μ :=
  Quotient.mk (lanaSSSetoid μ) ⟨T, hT⟩

/-- Two measurable sets have the same class in `ℝ^ss` exactly when they have the same volume. -/
theorem lanaRssClass_eq_iff {T T' : Set X} (hT : MeasurableSet T) (hT' : MeasurableSet T') :
    lanaRssClass μ T hT = lanaRssClass μ T' hT' ↔ μ T = μ T' :=
  Quotient.eq (r := lanaSSSetoid μ)

variable {C C' R : Type*} [AddCommGroup C] [Module ℝ C] [AddCommGroup C'] [Module ℝ C']

/-- Item 3 of the main goal in abstract form: for a line `C` with nonzero pilot `φ` (the role
of `ℝ^val`), elements `a`, `b` of a set `R` placed injectively in a real line `C'` (the role of
`ℝ^ss`), and linear maps `η`, `η'` sending the pilot to `a` and to `b`: `η = η'` exactly when
`a = b`. -/
theorem lana_eta_eq_iff_class (hC : Module.finrank ℝ C = 1) {φ : C} (hφ : φ ≠ 0) (ι : R → C')
    (hι : Function.Injective ι) (η η' : C →ₗ[ℝ] C') {a b : R} (ha : η φ = ι a)
    (hb : η' φ = ι b) : η = η' ↔ a = b := by
  rw [lana_linearMap_eq_iff_pilot hC hφ, ha, hb]
  exact hι.eq_iff

/-- The report's equality `η^q = η^anab_S` in the model (section 10.2): if the classes of
`ℝ^ss` are placed injectively in a real line `C'`, `η^anab_S` sends the pilot of `ℝ^val` to the
class of `θ S` (the action of `1 ∈ ℕ` on `S`) and `η^q` sends it to the class of the q-pilot
region `Q`, then `η^q = η^anab_S` exactly when `θ S` and `Q` have the same volume. -/
theorem lana_eta_eq_iff_volume (hC : Module.finrank ℝ C = 1) {φ : C} (hφ : φ ≠ 0)
    (ι : lanaRss μ → C') (hι : Function.Injective ι) (ηq ηS : C →ₗ[ℝ] C') {T Q : Set X}
    (hT : MeasurableSet T) (hQ : MeasurableSet Q) (hηq : ηq φ = ι (lanaRssClass μ Q hQ))
    (hηS : ηS φ = ι (lanaRssClass μ T hT)) : ηq = ηS ↔ μ Q = μ T := by
  rw [lana_eta_eq_iff_class hC hφ ι hι ηq ηS hηq hηS, lanaRssClass_eq_iff]

/-- **A schema for the main goal of section 10.2, with the action as data** (the report's goal is
its instance for the action of the η algorithm, which is not constructed). Data: a measure space
(the volume container with its volume), the log-shell `I`, the q-pilot region `Q` (the report's
`{q_v O_v}`), and the map `θ` by which the
generator `1 ∈ ℕ` acts on subsets (the action of `ℕ` that the η algorithm of section 10.1
constructs; its anabelian steps 2 to 6 are not constructed in the report, so here the action is
a parameter). Statement: there is a measurable `S ⊆ I` with `θ S` measurable and of the same
class in `ℝ^ss` as `Q`; by `lana_eta_eq_iff_volume` this is the equality `η^q = η^anab_S`.
For some actions it holds and for others it fails (`lanaEtaGoalFor_padic_holds`,
`lanaEtaGoalFor_padic_fails`): the content of the report's goal lies in the action the algorithm
would produce, which this definition does not contain. -/
def lanaEtaGoalFor (I Q : Set X) (hQ : MeasurableSet Q) (θ : Set X → Set X) : Prop :=
  ∃ S : Set X, S ⊆ I ∧ MeasurableSet S ∧
    ∃ hθ : MeasurableSet (θ S), lanaRssClass μ (θ S) hθ = lanaRssClass μ Q hQ

end Rss

/-! ### Both outcomes of the main goal for concrete actions on `ℚ_p` -/

section Padic

open IUT.Prerequisites.PadicVolume Pointwise

variable (p : ℕ) [Fact p.Prime] [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]

/-- The q-pilot region `p · ℤ_p` of the one-place model (`q = p`) is measurable. -/
theorem lana_padicQ_measurable :
    MeasurableSet ((p : ℚ_[p]) • {x : ℚ_[p] | ‖x‖ ≤ 1}) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hc : IsClosed {x : ℚ_[p] | ‖x‖ ≤ 1} := isClosed_le continuous_norm continuous_const
  exact (hc.smul_of_ne_zero hp0).measurableSet

/-- The main goal holds for the action of `1 ∈ ℕ` by multiplication by `p` on the container
`ℚ_p` (Haar measure normalized on `ℤ_p`), with log-shell `I = ℤ_p` and q-pilot region
`Q = p · ℤ_p`: take `S = I`. A model test, not a statement about the report's action. -/
theorem lanaEtaGoalFor_padic_holds :
    lanaEtaGoalFor (MeasureTheory.Measure.addHaarMeasure (padicVolZp p))
      {x : ℚ_[p] | ‖x‖ ≤ 1} ((p : ℚ_[p]) • {x : ℚ_[p] | ‖x‖ ≤ 1})
      (lana_padicQ_measurable p) (fun S => (p : ℚ_[p]) • S) :=
  ⟨{x : ℚ_[p] | ‖x‖ ≤ 1}, subset_rfl, isClosed_le continuous_norm continuous_const |>.measurableSet,
    lana_padicQ_measurable p, rfl⟩

/-- The main goal fails for the action of `1 ∈ ℕ` by multiplication by `p ^ 2` on the same
container, log-shell and q-pilot region: every `S ⊆ ℤ_p` has `vol(p² S) ≤ p⁻² < p⁻¹ = vol(Q)`.
A model test, not a statement about the report's action. -/
theorem lanaEtaGoalFor_padic_fails :
    ¬ lanaEtaGoalFor (MeasureTheory.Measure.addHaarMeasure (padicVolZp p))
      {x : ℚ_[p] | ‖x‖ ≤ 1} ((p : ℚ_[p]) • {x : ℚ_[p] | ‖x‖ ≤ 1})
      (lana_padicQ_measurable p) (fun S => ((p : ℚ_[p]) ^ 2) • S) := by
  rintro ⟨S, hSI, -, hθ, h⟩
  rw [lanaRssClass_eq_iff] at h
  set μ := MeasureTheory.Measure.addHaarMeasure (padicVolZp p)
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have h2 : (μ (((p : ℚ_[p]) ^ 2) • {x : ℚ_[p] | ‖x‖ ≤ 1})).toReal = (p : ℝ) ^ (-2 : ℤ) := by
    have := padicVol_padic_p_zpow p 2
    simpa using this
  have h1 : (μ ((p : ℚ_[p]) • {x : ℚ_[p] | ‖x‖ ≤ 1})).toReal = (p : ℝ) ^ (-1 : ℤ) := by
    have := padicVol_padic_p_zpow p 1
    simpa using this
  have hfin : μ (((p : ℚ_[p]) ^ 2) • {x : ℚ_[p] | ‖x‖ ≤ 1}) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at h2
    exact (zpow_pos (by linarith) _).ne' h2.symm
  have hle : μ (((p : ℚ_[p]) ^ 2) • S) ≤ μ (((p : ℚ_[p]) ^ 2) • {x : ℚ_[p] | ‖x‖ ≤ 1}) :=
    measure_mono (Set.smul_set_mono hSI)
  rw [h] at hle
  have hle' := ENNReal.toReal_mono hfin hle
  rw [h1, h2] at hle'
  have hlt : (p : ℝ) ^ (-2 : ℤ) < (p : ℝ) ^ (-1 : ℤ) :=
    zpow_lt_zpow_right₀ hp (by norm_num)
  linarith

end Padic

/-! ### Issue 2 of the report's repository: abstract link and concrete degree maps -/

section Issue2

open IUT.Audit.ScholzeStix

variable {Cθ Cq : Type*} [AddCommGroup Cθ] [Module ℝ Cθ] [AddCommGroup Cq] [Module ℝ Cq]

/-- Model of issue 2. `Φ` is the abstract isomorphism of the Θ-pilot and q-pilot value-group
BPS in pointed form (unique by `lana_pointedLineIso_unique`, pilot to pilot: factor `1`).
`dθ`, `dq` are concrete degree maps; `dθ` sends the Θ-pilot to `s · D` with
`s = avgSq ℓ* = (1² + ⋯ + (ℓ*)²)/ℓ*` (the factor of section 8.1.1 and of the hexagon of
section 11.2), and `dq` sends the q-pilot to `D ≠ 0`. Then `dθ = s · (dq ∘ Φ)`, and the square
`dq ∘ Φ = dθ` commutes exactly when `s = 1`. -/
theorem lana_issue2_model {Lθ : LanaPointedLine Cθ} {Lq : LanaPointedLine Cq}
    (Φ : LanaPointedLineIso Lθ Lq) (lh : ℕ) {D : ℝ} (hD : D ≠ 0) (dθ : Cθ →ₗ[ℝ] ℝ)
    (dq : Cq →ₗ[ℝ] ℝ) (hθ : dθ Lθ.lanaPilot = avgSq lh * D) (hq : dq Lq.lanaPilot = D) :
    dθ = avgSq lh • (dq ∘ₗ Φ.lanaEquiv.toLinearMap) ∧
      (dq ∘ₗ Φ.lanaEquiv.toLinearMap = dθ ↔ avgSq lh = 1) := by
  have hpil : (dq ∘ₗ Φ.lanaEquiv.toLinearMap) Lθ.lanaPilot = D := by
    simp [Φ.lanaMapPilot, hq]
  have hreg := lana_linearMap_eq_iff_pilot (C' := ℝ) Lθ.lanaFinrank Lθ.lanaPilot_ne
  refine ⟨(hreg _ _).mpr ?_, ?_⟩
  · rw [LinearMap.smul_apply, hpil, hθ, smul_eq_mul]
  · rw [hreg, hpil, hθ]
    constructor
    · intro h
      have : (avgSq lh - 1) * D = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · linarith
      · exact absurd h' hD
    · intro h; rw [h, one_mul]

/-- For `ℓ* ≥ 2` (that is, `ℓ = 2ℓ* + 1 ≥ 5`) the square of `lana_issue2_model` does not
commute, and the cycle of identifications of `IUT.Audit.ScholzeStix.Diagram` with the scalar
`avgSq ℓ*` on one edge and canonical edges elsewhere is inconsistent. This is the
non-commutativity of the Scholze–Stix hexagon (report, section 11.2), which the report accepts;
it is not an argument for or against IUT III, Corollary 3.12. For `ℓ* = 1` the factor is `1`
and the square commutes. -/
theorem lana_issue2_not_commute {Lθ : LanaPointedLine Cθ} {Lq : LanaPointedLine Cq}
    (Φ : LanaPointedLineIso Lθ Lq) {lh : ℕ} (hlh : 2 ≤ lh) {D : ℝ} (hD : D ≠ 0)
    (dθ : Cθ →ₗ[ℝ] ℝ) (dq : Cq →ₗ[ℝ] ℝ) (hθ : dθ Lθ.lanaPilot = avgSq lh * D)
    (hq : dq Lq.lanaPilot = D) (hpos : 0 < avgSq lh) (n : ℕ) :
    dq ∘ₗ Φ.lanaEquiv.toLinearMap ≠ dθ ∧
      ¬ Consistent (⟨avgSq lh, hpos⟩ :: List.replicate n LinIdent.canonical) := by
  have hs : avgSq lh ≠ 1 := by
    rw [avgSq_eq (by omega) rfl]
    have : (2 : ℝ) ≤ lh := by exact_mod_cast hlh
    nlinarith
  refine ⟨fun h => hs (((lana_issue2_model Φ lh hD dθ dq hθ hq).2).mp h), fun h => hs ?_⟩
  exact scalar_eq_one_of_consistent _ n h

/-- For `ℓ* = 1` (`ℓ = 3`) the factor `avgSq 1` is `1`. -/
theorem lana_avgSq_one : avgSq 1 = 1 := by
  simp [avgSq]

end Issue2

end IUT.Audit.LANA
