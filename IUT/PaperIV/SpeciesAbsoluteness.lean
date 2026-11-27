import Mathlib
import IUT.PaperIV.SpeciesExamples

/-!
# Absoluteness of power-set-bounded formulas and composites of mutations (IUT IV, Section 3)

This module continues `IUT.PaperIV.Species` and `IUT.PaperIV.SpeciesExamples` on Definition 3.1
(pages 67 to 70), Example 3.2 (page 72), Definition 3.3 (pages 72 to 74) and Example 3.4 (page 77)
of IUT IV. All of these pages (67 to 74 and 77) were checked against renders of the manuscript.

## Power-set-bounded formulas

The proviso of Definition 3.1 (page 68) asks that a formula define the same set in the models of
universes `V ∈ W`. Formulas whose quantifiers are bounded by variables (`IsSpeciesDelta0`) satisfy
it. Here the quantifiers may also be bounded by iterated power sets `P^k(w₁ ∪ w₂)` of variables
(`SaIsPowBounded`). `saPowBounded_realize_iff` shows that such a formula means the same in a
transitive model closed under power sets and binary unions as in all of `ZFSet`, and
`saAbsolute_of_powBounded` derives the proviso. The hypotheses used are transitivity,
closure under power sets and closure under binary unions; every Grothendieck universe and the
whole of `ZFSet` have them. The proof uses that each `P^k(w₁ ∪ w₂)` is itself an element of the
model, which closure under subsets of elements does not give for `k ≥ 2`.

## Example 3.2: categories

`saCatSpecies` encodes the species of small categories: species-objects are pairs `(A, C)` of a
set `A` of arrows and a set `C` of composition relations `((f, g), g ∘ f)` (the arrows-only
description), species-morphisms are isomorphism classes of functors, given as sets of graphs of
maps on arrows. Membership in an isomorphism class quantifies over all functors, which are
elements of `P³(A ∪ A')`; this is the motivating instance of a power-set bound.
`saCatSpecies_absolute` proves the provisos of all three formulas, and `saCat_zeroSpecimen_iff`,
`saCat_oneSpecimen_iff` compute their meaning in every model. The remaining assertions of
Example 3.2 (that these formulas satisfy the axioms of a species, and that species-isomorphisms
correspond to isomorphism classes of equivalences of categories) and Example 3.4 (ii) (groups with
outer homomorphisms) are not formalized here.

## Definition 3.3 (i): composites of mutations

The composite `mutationAfter` of `IUT.PaperIV.Species` omits the condition `Φ₀(E)` on the source
species-object in its object formula and the conditions `Φ₀(E)`, `Φ₀(E')`, `Φ₁(E, E', F)` in its
morphism formula. `saMutationComp` adds them, `saComp_obj_agree` and `saComp_mor_agree` show
that it agrees with `mutationAfter` on species-objects and species-morphisms of the source
species, and `saMutationComp_isMutation` proves that the composite of two mutations between
species is a mutation (page 72 says "Let 𝔖, 𝔖̲ be species").

## Definition 3.3 (ii): morphisms of mutations

`saIsMutationIso_of_inverse` proves the direction "if" of the characterization of isomorphisms
of mutations by inverses (page 73), with "the composites are identities" read model by model.
The direction "only if" and the composite of morphisms of mutations are stated, not proved, as
`saMutationIsoInverseClaim` and `saMutationMorphismCompClaim`.
-/

universe u

namespace IUT.PaperIV.SpeciesAbsoluteness

open IUT.Foundations IUT.PaperIV.Species IUT.PaperIV.SpeciesExamples

/-! ## Formulas with quantifiers bounded by iterated power sets -/

/-- The `k`-fold power set `P^k(s)`. -/
def saPowIter (s : ZFSet.{u}) : ℕ → ZFSet.{u}
  | 0 => s
  | k + 1 => ZFSet.powerset (saPowIter s k)

section PowLibrary

variable {α : Type*}

/-- The guard `x ∈ P^k(w₁ ∪ w₂)`, written with bounded quantifiers only: for `k = 0` it is
`x ∈ w₁ ∨ x ∈ w₂`, and `x ∈ P^{k+1}(w₁ ∪ w₂)` is `∀ y ∈ x, y ∈ P^k(w₁ ∪ w₂)`. -/
def saMemPowF : (k : ℕ) → {n : ℕ} → (x w₁ w₂ : α ⊕ Fin n) → speciesLang.BoundedFormula α n
  | 0, _, x, w₁, w₂ => sxMemF x w₁ ⊔ sxMemF x w₂
  | k + 1, _, x, w₁, w₂ => speciesBall x (saMemPowF k sxTop (sxLift w₁) (sxLift w₂))

/-- The quantifier `∀ x ∈ P^k(w₁ ∪ w₂), φ`, that is `∀ x, x ∈ P^k(w₁ ∪ w₂) → φ`, where `w₁`,
`w₂` are variables other than `x`. The quantifier itself is unbounded; only its guard is. -/
def saPAll (k : ℕ) {n : ℕ} (w₁ w₂ : α ⊕ Fin n) (φ : speciesLang.BoundedFormula α (n + 1)) :
    speciesLang.BoundedFormula α n :=
  FirstOrder.Language.BoundedFormula.all
    ((saMemPowF k sxTop (sxLift w₁) (sxLift w₂)).imp φ)

/-- Formulas all of whose quantifiers are bounded by a variable (`∀ x ∈ w`) or by an iterated
power set of the union of two variables (`∀ x ∈ P^k(w₁ ∪ w₂)`). Every formula of
`IsSpeciesDelta0` is one (`saIsPowBounded_of_delta0`). -/
inductive SaIsPowBounded {α : Type*} : {n : ℕ} → speciesLang.BoundedFormula α n → Prop
  | falsum {n : ℕ} :
      SaIsPowBounded
        (FirstOrder.Language.BoundedFormula.falsum : speciesLang.BoundedFormula α n)
  | equal {n : ℕ} (t₁ t₂ : speciesLang.Term (α ⊕ Fin n)) :
      SaIsPowBounded (FirstOrder.Language.BoundedFormula.equal t₁ t₂)
  | rel {n l : ℕ} (R : speciesLang.Relations l) (ts : Fin l → speciesLang.Term (α ⊕ Fin n)) :
      SaIsPowBounded (FirstOrder.Language.BoundedFormula.rel R ts)
  | imp {n : ℕ} {φ ψ : speciesLang.BoundedFormula α n} :
      SaIsPowBounded φ → SaIsPowBounded ψ → SaIsPowBounded (φ.imp ψ)
  | ball {n : ℕ} (w : α ⊕ Fin n) {φ : speciesLang.BoundedFormula α (n + 1)} :
      SaIsPowBounded φ → SaIsPowBounded (speciesBall w φ)
  | pall {n : ℕ} (k : ℕ) (w₁ w₂ : α ⊕ Fin n) {φ : speciesLang.BoundedFormula α (n + 1)} :
      SaIsPowBounded φ → SaIsPowBounded (saPAll k w₁ w₂ φ)

theorem saIsPowBounded_of_delta0 {n : ℕ} {φ : speciesLang.BoundedFormula α n}
    (h : IsSpeciesDelta0 φ) : SaIsPowBounded φ := by
  induction h with
  | falsum => exact SaIsPowBounded.falsum
  | equal t₁ t₂ => exact SaIsPowBounded.equal t₁ t₂
  | rel R ts => exact SaIsPowBounded.rel R ts
  | imp _ _ ih₁ ih₂ => exact SaIsPowBounded.imp ih₁ ih₂
  | ball w _ ih => exact SaIsPowBounded.ball w ih

/-- In a transitive domain the guard `saMemPowF` means `x ∈ P^k(w₁ ∪ w₂)`. -/
theorem saMemPowF_realize {D : Set ZFSet.{u}} (htr : ∀ x ∈ D, ∀ y ∈ x, y ∈ D) (k : ℕ) :
    ∀ {n : ℕ} (v : α → D) (xs : Fin n → D) (x w₁ w₂ : α ⊕ Fin n),
      speciesRealizeAt D (saMemPowF k x w₁ w₂) v xs ↔
        sxEnv v xs x ∈ saPowIter (sxEnv v xs w₁ ∪ sxEnv v xs w₂) k := by
  induction k with
  | zero =>
    intro n v xs x w₁ w₂
    rw [saMemPowF, saPowIter, sxRealize_sup, sxMemF_realize, sxMemF_realize, ZFSet.mem_union]
  | succ k ih =>
    intro n v xs x w₁ w₂
    rw [saMemPowF, saPowIter, speciesBall_realize, ZFSet.mem_powerset, ZFSet.subset_def]
    constructor
    · intro H y hy
      have hyD : y ∈ D := htr _ (Sum.elim v xs x).2 y hy
      have := (ih v (Fin.snoc xs ⟨y, hyD⟩) sxTop (sxLift w₁) (sxLift w₂)).1 (H ⟨y, hyD⟩ hy)
      rwa [sxEnv_top, sxEnv_lift, sxEnv_lift] at this
    · intro H y hy
      refine (ih v (Fin.snoc xs y) sxTop (sxLift w₁) (sxLift w₂)).2 ?_
      rw [sxEnv_top, sxEnv_lift, sxEnv_lift]
      exact H hy

/-- The power-set-bounded quantifier means `∀ x ∈ P^k(w₁ ∪ w₂), φ` in every transitive domain. -/
theorem saPAll_realize {D : Set ZFSet.{u}} (htr : ∀ x ∈ D, ∀ y ∈ x, y ∈ D) {n : ℕ} (k : ℕ)
    (w₁ w₂ : α ⊕ Fin n) (φ : speciesLang.BoundedFormula α (n + 1)) (v : α → D)
    (xs : Fin n → D) :
    speciesRealizeAt D (saPAll k w₁ w₂ φ) v xs ↔
      ∀ y : D, y.1 ∈ saPowIter (sxEnv v xs w₁ ∪ sxEnv v xs w₂) k →
        speciesRealizeAt D φ v (Fin.snoc xs y) := by
  show (∀ y : D, speciesRealizeAt D (saMemPowF k sxTop (sxLift w₁) (sxLift w₂)) v
      (Fin.snoc xs y) → speciesRealizeAt D φ v (Fin.snoc xs y)) ↔ _
  refine forall_congr' fun y => imp_congr ?_ Iff.rfl
  rw [saMemPowF_realize htr, sxEnv_top, sxEnv_lift, sxEnv_lift]

theorem saPowIter_mem {D : Set ZFSet.{u}} (hpow : ∀ x ∈ D, ZFSet.powerset x ∈ D)
    {s : ZFSet.{u}} (hs : s ∈ D) : ∀ k, saPowIter s k ∈ D
  | 0 => hs
  | k + 1 => hpow _ (saPowIter_mem hpow hs k)

theorem saEnv_incl {D : Set ZFSet.{u}} {n : ℕ} (v : α → D) (xs : Fin n → D) (r : α ⊕ Fin n) :
    sxEnv (Set.inclusion (Set.subset_univ D) ∘ v) (Set.inclusion (Set.subset_univ D) ∘ xs) r =
      sxEnv v xs r := by
  rcases r with a | i <;> rfl

/-- Absoluteness of power-set-bounded formulas: in a transitive domain `D` closed under power
sets and binary unions, a formula of `SaIsPowBounded` has, at every assignment of sets of
`D`, the same truth value as in the model `ZFSet.{u}`. -/
theorem saPowBounded_realize_iff {D : Set ZFSet.{u}} (htr : ∀ x ∈ D, ∀ y ∈ x, y ∈ D)
    (hpow : ∀ x ∈ D, ZFSet.powerset x ∈ D) (hunion : ∀ x ∈ D, ∀ y ∈ D, x ∪ y ∈ D)
    (v : α → D) {n : ℕ} {φ : speciesLang.BoundedFormula α n} (hφ : SaIsPowBounded φ) :
    ∀ xs : Fin n → D, speciesRealizeAt D φ v xs ↔
      speciesRealizeAt sxUniv φ (Set.inclusion (Set.subset_univ D) ∘ v)
        (Set.inclusion (Set.subset_univ D) ∘ xs) := by
  induction hφ with
  | falsum => exact speciesDelta0_realize_iff (Set.subset_univ D) htr v IsSpeciesDelta0.falsum
  | equal t₁ t₂ =>
    exact speciesDelta0_realize_iff (Set.subset_univ D) htr v (IsSpeciesDelta0.equal t₁ t₂)
  | rel R ts =>
    exact speciesDelta0_realize_iff (Set.subset_univ D) htr v (IsSpeciesDelta0.rel R ts)
  | imp _ _ ih₁ ih₂ => intro xs; exact imp_congr (ih₁ xs) (ih₂ xs)
  | ball w _ ih =>
    intro xs
    rw [speciesBall_realize, speciesBall_realize]
    have hmem : ∀ y : ZFSet.{u},
        y ∈ (Sum.elim (Set.inclusion (Set.subset_univ D) ∘ v)
          (Set.inclusion (Set.subset_univ D) ∘ xs) w).1 ↔ y ∈ (Sum.elim v xs w).1 := by
      intro y; rw [← Sum.comp_elim]; exact Iff.rfl
    constructor
    · intro H x' hx'
      have hx'D : x'.1 ∈ D := htr _ (Sum.elim v xs w).2 _ ((hmem _).1 hx')
      have hx : Set.inclusion (Set.subset_univ D) ⟨x'.1, hx'D⟩ = x' := Subtype.ext rfl
      have := (ih (Fin.snoc xs ⟨x'.1, hx'D⟩)).1 (H _ ((hmem _).1 hx'))
      rwa [Fin.comp_snoc, hx] at this
    · intro H x hx
      have := H (Set.inclusion (Set.subset_univ D) x) ((hmem _).2 hx)
      rw [← Fin.comp_snoc] at this
      exact (ih (Fin.snoc xs x)).2 this
  | pall k w₁ w₂ _ ih =>
    intro xs
    rw [saPAll_realize htr, saPAll_realize (D := sxUniv) (fun _ _ _ _ => Set.mem_univ _),
      saEnv_incl, saEnv_incl]
    have hP : saPowIter (sxEnv v xs w₁ ∪ sxEnv v xs w₂) k ∈ D :=
      saPowIter_mem hpow (hunion _ (Sum.elim v xs w₁).2 _ (Sum.elim v xs w₂).2) k
    constructor
    · intro H x' hx'
      have hx'D : x'.1 ∈ D := htr _ hP _ hx'
      have hx : Set.inclusion (Set.subset_univ D) ⟨x'.1, hx'D⟩ = x' := Subtype.ext rfl
      have := (ih (Fin.snoc xs ⟨x'.1, hx'D⟩)).1 (H _ hx')
      rwa [Fin.comp_snoc, hx] at this
    · intro H x hx
      have := H (Set.inclusion (Set.subset_univ D) x) hx
      rw [← Fin.comp_snoc] at this
      exact (ih (Fin.snoc xs x)).2 this

/-- Transfer to `ZFSet.{u}` for power-set-bounded formulas (compare `sxHolds_iff`). -/
theorem saHolds_iff {β : Type*} {D : Set ZFSet.{u}} (htr : ∀ x ∈ D, ∀ y ∈ x, y ∈ D)
    (hpow : ∀ x ∈ D, ZFSet.powerset x ∈ D) (hunion : ∀ x ∈ D, ∀ y ∈ D, x ∪ y ∈ D)
    {φ : speciesLang.Formula β} (hφ : SaIsPowBounded φ) (x : β → ZFSet.{u}) :
    speciesHolds D φ x ↔ (∀ b, x b ∈ D) ∧
      speciesRealizeAt sxUniv φ (fun b => ⟨x b, Set.mem_univ _⟩) default := by
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    have := (saPowBounded_realize_iff htr hpow hunion (fun b => ⟨x b, hx b⟩) hφ default).1 h
    rwa [Subsingleton.elim (Set.inclusion (Set.subset_univ D) ∘ default) default] at this
  · rintro ⟨hx, h⟩
    refine ⟨hx, (saPowBounded_realize_iff htr hpow hunion (fun b => ⟨x b, hx b⟩) hφ
      default).2 ?_⟩
    rwa [Subsingleton.elim (Set.inclusion (Set.subset_univ D) ∘ default) default]

/-- A Grothendieck universe is closed under binary unions (by axioms (iv) and (v) of page 67). -/
theorem saUniv_union_mem {V : ZFSet.{u}} (hV : IsGrothendieckUniverse V) {x y : ZFSet.{u}}
    (hx : x ∈ V) (hy : y ∈ V) : x ∪ y ∈ V :=
  ZFSet.sUnion_pair x y ▸ hV.sUnion_mem _ (sxUniv_pairSet_mem hV hx hy)

/-- Every model of `IsSpeciesModel` is closed under power sets and binary unions. -/
theorem saModel_closed {D : Set ZFSet.{u}} (hD : IsSpeciesModel D) :
    (∀ x ∈ D, ZFSet.powerset x ∈ D) ∧ ∀ x ∈ D, ∀ y ∈ D, x ∪ y ∈ D := by
  rcases hD with rfl | ⟨V, hV, rfl⟩
  · exact ⟨fun _ _ => Set.mem_univ _, fun _ _ _ _ => Set.mem_univ _⟩
  · exact ⟨hV.powerset_mem, fun _ ha _ hb => saUniv_union_mem hV ha hb⟩

/-- In every model of `IsSpeciesModel`, a power-set-bounded formula holds exactly when it holds
in `ZFSet.{u}` at the same sets of the model. -/
theorem saModel_holds_iff {β : Type*} {D : Set ZFSet.{u}} (hD : IsSpeciesModel D)
    {φ : speciesLang.Formula β} (hφ : SaIsPowBounded φ) (x : β → ZFSet.{u}) :
    speciesHolds D φ x ↔ (∀ b, x b ∈ D) ∧
      speciesRealizeAt sxUniv φ (fun b => ⟨x b, Set.mem_univ _⟩) default :=
  saHolds_iff (isSpeciesModel_transitive hD) (saModel_closed hD).1 (saModel_closed hD).2 hφ x

/-- A power-set-bounded formula satisfies the absoluteness proviso of page 68. -/
theorem saAbsolute_of_powBounded {β : Type*} {φ : speciesLang.Formula β}
    (hφ : SaIsPowBounded φ) : SpeciesAbsolute.{u} φ := by
  intro V W hV hW hVW x hx
  rw [saHolds_iff (D := {y | y ∈ V}) hV.transitive hV.powerset_mem
      (fun _ ha _ hb => saUniv_union_mem hV ha hb) hφ,
    saHolds_iff (D := {y | y ∈ W}) hW.transitive hW.powerset_mem
      (fun _ ha _ hb => saUniv_union_mem hW ha hb) hφ]
  exact ⟨fun h => ⟨fun b => hW.transitive V hVW _ (hx b), h.2⟩, fun h => ⟨hx, h.2⟩⟩

/-- The formula `P(w) ⊆ z`: `∀ s ∈ P(w ∪ w), s ∈ z`. It is power-set-bounded but its
quantifier is not bounded by a variable. -/
def saPowSubF {n : ℕ} (z w : α ⊕ Fin n) : speciesLang.BoundedFormula α n :=
  saPAll 1 w w (sxMemF sxTop (sxLift z))

theorem saPowSubF_powBounded {n : ℕ} (z w : α ⊕ Fin n) : SaIsPowBounded (saPowSubF z w) :=
  SaIsPowBounded.pall 1 w w (saIsPowBounded_of_delta0 (sxMemF_delta0 _ _))

theorem saPowSubF_realizeU {n : ℕ} (v : α → sxUniv.{u}) (xs : Fin n → sxUniv.{u})
    (z w : α ⊕ Fin n) :
    speciesRealizeAt sxUniv (saPowSubF z w) v xs ↔
      ZFSet.powerset (sxEnv v xs w) ⊆ sxEnv v xs z := by
  rw [saPowSubF, saPAll_realize (D := sxUniv) (fun _ _ _ _ => Set.mem_univ _), ZFSet.subset_def]
  constructor
  · intro H s hs
    have hs' : (⟨s, Set.mem_univ s⟩ : sxUniv.{u}).1 ∈
        saPowIter (sxEnv v xs w ∪ sxEnv v xs w) 1 := by
      show s ∈ ZFSet.powerset _
      rw [ZFSet.mem_powerset] at hs
      rw [ZFSet.mem_powerset]
      exact fun t ht => ZFSet.mem_union.2 (Or.inl (hs ht))
    have := H _ hs'
    rwa [sxMemF_realize, sxEnv_top, sxEnv_lift] at this
  · intro H y hy
    rw [sxMemF_realize, sxEnv_top, sxEnv_lift]
    apply H
    have hy' : y.1 ∈ ZFSet.powerset (sxEnv v xs w ∪ sxEnv v xs w) := hy
    rw [ZFSet.mem_powerset] at hy'
    rw [ZFSet.mem_powerset]
    exact fun t ht => (ZFSet.mem_union.1 (hy' ht)).elim id id

end PowLibrary

/-! ## The composite of two mutations -/

section Composite

variable {S T U : SpeciesData}

/-- The guard `Φ₀(E) ∧ Φ₀(E') ∧ Φ₁(E, E', F)` of the morphism formula of a composite: the
morphism `F : E → E'` is a species-morphism of the source species. -/
noncomputable def saMorGuard (S U : SpeciesData) :
    speciesLang.Formula (Fin S.objArity ⊕ Fin S.objArity ⊕ Fin S.morArity ⊕ Fin U.morArity) :=
  FirstOrder.Language.Formula.relabel Sum.inl S.spZero.zsFormula ⊓
    FirstOrder.Language.Formula.relabel (Sum.inr ∘ Sum.inl) S.spZero.zsFormula ⊓
    FirstOrder.Language.Formula.relabel
      (Sum.elim Sum.inl (Sum.elim (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inr ∘ Sum.inl)))
      S.spOne.osFormula

/-- The corrected composite `𝔑 ∘ 𝔐` of `𝔐 : 𝔖 ⇝ 𝔗` and `𝔑 : 𝔗 ⇝ 𝔘`: the formulas of
`mutationAfter`, with the conjunct `Φ₀(E)` added to the object formula and the conjuncts
`Φ₀(E)`, `Φ₀(E')`, `Φ₁(E, E', F)` added to the morphism formula. -/
noncomputable def saMutationComp (N : MutationData T U) (M : MutationData S T) :
    MutationData S U where
  mutObjFormula :=
    FirstOrder.Language.Formula.relabel Sum.inl S.spZero.zsFormula ⊓
      (mutationAfter N M).mutObjFormula
  mutMorFormula := saMorGuard S U ⊓ (mutationAfter N M).mutMorFormula

section Model

variable {D : Set ZFSet.{u}}

theorem saMorGuard_holds (E E' : Fin S.objArity → ZFSet.{u}) (F : Fin S.morArity → ZFSet.{u})
    (H : Fin U.morArity → ZFSet.{u}) (hx : ∀ a, Sum.elim E (Sum.elim E' (Sum.elim F H)) a ∈ D) :
    speciesHolds D (saMorGuard S U) (Sum.elim E (Sum.elim E' (Sum.elim F H))) ↔
      oneSpecimen D S E E' F := by
  unfold saMorGuard oneSpecimen
  rw [speciesHolds_inf, speciesHolds_inf, speciesHolds_relabel _ _ hx,
    speciesHolds_relabel _ _ hx, speciesHolds_relabel _ _ hx]
  have e : Sum.elim E (Sum.elim E' (Sum.elim F H)) ∘
      Sum.elim Sum.inl (Sum.elim (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inr ∘ Sum.inl)) =
        Sum.elim E (Sum.elim E' F) := by
    funext c; rcases c with a | a | a <;> rfl
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    exact ⟨h₁, h₂, sxHolds_congr h₃ e⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨⟨h₁, h₂⟩, sxHolds_congr h₃ e.symm⟩

/-- The object formula of the corrected composite: `Φ₀(E)` and the object formula of
`mutationAfter`. -/
theorem saComp_obj_holds (N : MutationData T U) (M : MutationData S T)
    (E : Fin S.objArity → ZFSet.{u}) (C : Fin U.objArity → ZFSet.{u}) (hE : ∀ i, E i ∈ D)
    (hC : ∀ i, C i ∈ D) :
    speciesHolds D (saMutationComp N M).mutObjFormula (Sum.elim E C) ↔
      zeroSpecimen D S.spZero E ∧
        speciesHolds D (mutationAfter N M).mutObjFormula (Sum.elim E C) := by
  have hEC : ∀ a, Sum.elim E C a ∈ D := by
    rintro (a | a)
    exacts [hE a, hC a]
  change speciesHolds D (FirstOrder.Language.Formula.relabel Sum.inl S.spZero.zsFormula ⊓ _) _ ↔ _
  rw [speciesHolds_inf, speciesHolds_relabel _ _ hEC]
  exact Iff.rfl

/-- The morphism formula of the corrected composite: `F : E → E'` is a species-morphism, and
the morphism formula of `mutationAfter` holds. -/
theorem saComp_mor_holds (N : MutationData T U) (M : MutationData S T)
    (E E' : Fin S.objArity → ZFSet.{u}) (F : Fin S.morArity → ZFSet.{u})
    (H : Fin U.morArity → ZFSet.{u}) (hx : ∀ a, Sum.elim E (Sum.elim E' (Sum.elim F H)) a ∈ D) :
    speciesHolds D (saMutationComp N M).mutMorFormula (Sum.elim E (Sum.elim E' (Sum.elim F H))) ↔
      oneSpecimen D S E E' F ∧
        speciesHolds D (mutationAfter N M).mutMorFormula
          (Sum.elim E (Sum.elim E' (Sum.elim F H))) := by
  change speciesHolds D (saMorGuard S U ⊓ _) _ ↔ _
  rw [speciesHolds_inf, saMorGuard_holds E E' F H hx]

/-- Agreement with `mutationAfter` on species-objects of the source species: at a 0-specimen
`E`, the object formulas of `saMutationComp N M` and `mutationAfter N M` are equivalent. -/
theorem saComp_obj_agree (N : MutationData T U) (M : MutationData S T)
    {E : Fin S.objArity → ZFSet.{u}} (hE : zeroSpecimen D S.spZero E)
    (C : Fin U.objArity → ZFSet.{u}) :
    speciesHolds D (saMutationComp N M).mutObjFormula (Sum.elim E C) ↔
      speciesHolds D (mutationAfter N M).mutObjFormula (Sum.elim E C) := by
  constructor
  · intro h
    exact ((saComp_obj_holds N M E C (fun i => speciesHolds_mem h (Sum.inl i))
      (fun i => speciesHolds_mem h (Sum.inr i))).1 h).2
  · intro h
    exact (saComp_obj_holds N M E C (fun i => speciesHolds_mem h (Sum.inl i))
      (fun i => speciesHolds_mem h (Sum.inr i))).2 ⟨hE, h⟩

/-- Agreement with `mutationAfter` on species-morphisms of the source species: at a 1-specimen
`F : E → E'`, the morphism formulas of `saMutationComp N M` and `mutationAfter N M` are
equivalent. -/
theorem saComp_mor_agree (N : MutationData T U) (M : MutationData S T)
    {E E' : Fin S.objArity → ZFSet.{u}} {F : Fin S.morArity → ZFSet.{u}}
    (hF : oneSpecimen D S E E' F) (H : Fin U.morArity → ZFSet.{u}) :
    speciesHolds D (saMutationComp N M).mutMorFormula (Sum.elim E (Sum.elim E' (Sum.elim F H))) ↔
      speciesHolds D (mutationAfter N M).mutMorFormula
        (Sum.elim E (Sum.elim E' (Sum.elim F H))) := by
  constructor
  · intro h
    exact ((saComp_mor_holds N M E E' F H (speciesHolds_mem h)).1 h).2
  · intro h
    exact (saComp_mor_holds N M E E' F H (speciesHolds_mem h)).2 ⟨hF, h⟩

theorem saComp_objRel_iff (N : MutationData T U) (M : MutationData S T)
    {E : Fin S.objArity → ZFSet.{u}} (hE : zeroSpecimen D S.spZero E)
    (A : Fin U.objArity → ZFSet.{u}) :
    mutationObjRel D (saMutationComp N M) E A ↔ mutationObjRel D (mutationAfter N M) E A :=
  and_congr_right fun _ => saComp_obj_agree N M hE A

theorem saComp_morRel_iff (N : MutationData T U) (M : MutationData S T)
    {E E' : Fin S.objArity → ZFSet.{u}} {F : Fin S.morArity → ZFSet.{u}}
    (hF : oneSpecimen D S E E' F) (A A' : Fin U.objArity → ZFSet.{u})
    (G : Fin U.morArity → ZFSet.{u}) :
    mutationMorRel D (saMutationComp N M) E E' F A A' G ↔
      mutationMorRel D (mutationAfter N M) E E' F A A' G := by
  unfold mutationMorRel
  rw [saComp_objRel_iff N M hF.1, saComp_objRel_iff N M hF.2.1, saComp_mor_agree N M hF]

/-- In a model where `mutationAfter N M` satisfies conditions (a) and (b) of Definition 3.3 (i),
so does the corrected composite. -/
theorem saComp_axiomsAt {N : MutationData T U} {M : MutationData S T}
    (h : MutationAxiomsAt D (mutationAfter N M)) : MutationAxiomsAt D (saMutationComp N M) := by
  obtain ⟨ha, hb, hc, hd⟩ := h
  refine ⟨fun E hE => ?_, fun E E' F A A' hF hA hA' => ?_, ?_, ?_⟩
  · exact (existsUnique_congr (saComp_objRel_iff N M hE)).2 (ha E hE)
  · rw [saComp_objRel_iff N M hF.1] at hA
    rw [saComp_objRel_iff N M hF.2.1] at hA'
    exact (existsUnique_congr (saComp_morRel_iff N M hF A A')).2 (hb E E' F A A' hF hA hA')
  · intro E E' E'' F F' F'' A A' A'' G G' G'' hcomp h₁ h₂ h₃
    exact hc _ _ _ _ _ _ _ _ _ _ _ _ hcomp ((saComp_morRel_iff N M hcomp.1 _ _ _).1 h₁)
      ((saComp_morRel_iff N M hcomp.2.1 _ _ _).1 h₂)
      ((saComp_morRel_iff N M hcomp.2.2.1 _ _ _).1 h₃)
  · intro E I A J hI hIJ
    exact hd E I A J hI ((saComp_morRel_iff N M hI.1 _ _ _).1 hIJ)

end Model

/-! ### Transfer between universes `V ∈ W` -/

section Transfer

variable {V W : ZFSet.{u}}

theorem saUnivModel (hV : IsGrothendieckUniverse V) : IsSpeciesModel {y | y ∈ V} :=
  Or.inr ⟨V, hV, rfl⟩

theorem saElimMem {β γ : Type*} {f : β → ZFSet.{u}} {g : γ → ZFSet.{u}} (hf : ∀ i, f i ∈ V)
    (hg : ∀ i, g i ∈ V) : ∀ a, Sum.elim f g a ∈ V := by
  rintro (a | a)
  exacts [hf a, hg a]

theorem saUp {β : Type*} {φ : speciesLang.Formula β} (hφ : SpeciesAbsolute.{u} φ)
    (hV : IsGrothendieckUniverse V) (hW : IsGrothendieckUniverse W) (hVW : V ∈ W)
    {x : β → ZFSet.{u}} (h : speciesHolds {y | y ∈ V} φ x) : speciesHolds {y | y ∈ W} φ x :=
  (hφ V W hV hW hVW x (speciesHolds_mem h)).1 h

theorem saDown {β : Type*} {φ : speciesLang.Formula β} (hφ : SpeciesAbsolute.{u} φ)
    (hV : IsGrothendieckUniverse V) (hW : IsGrothendieckUniverse W) (hVW : V ∈ W)
    {x : β → ZFSet.{u}} (hx : ∀ b, x b ∈ V) (h : speciesHolds {y | y ∈ W} φ x) :
    speciesHolds {y | y ∈ V} φ x :=
  (hφ V W hV hW hVW x hx).2 h

theorem saOneSpecimen_transfer (hS : IsSpecies.{u} S) (hV : IsGrothendieckUniverse V)
    (hW : IsGrothendieckUniverse W) (hVW : V ∈ W) {E E' : Fin S.objArity → ZFSet.{u}}
    {F : Fin S.morArity → ZFSet.{u}} (hE : ∀ i, E i ∈ V) (hE' : ∀ i, E' i ∈ V)
    (hF : ∀ i, F i ∈ V) :
    oneSpecimen {y | y ∈ V} S E E' F ↔ oneSpecimen {y | y ∈ W} S E E' F :=
  and_congr (hS.1.2 V W hV hW hVW E hE) (and_congr (hS.1.2 V W hV hW hVW E' hE')
    (hS.2.2.1 V W hV hW hVW _ (saElimMem hE (saElimMem hE' hF))))

theorem saObjRel_transfer (hT : IsSpecies.{u} T) {M : MutationData S T} (hM : IsMutation.{u} M)
    (hV : IsGrothendieckUniverse V) (hW : IsGrothendieckUniverse W) (hVW : V ∈ W)
    {E : Fin S.objArity → ZFSet.{u}} {B : Fin T.objArity → ZFSet.{u}} (hE : ∀ i, E i ∈ V)
    (hB : ∀ i, B i ∈ V) :
    mutationObjRel {y | y ∈ V} M E B ↔ mutationObjRel {y | y ∈ W} M E B :=
  and_congr (hT.1.2 V W hV hW hVW B hB) (hM.1 V W hV hW hVW _ (saElimMem hE hB))

theorem saMorRel_transfer (hT : IsSpecies.{u} T) {M : MutationData S T} (hM : IsMutation.{u} M)
    (hV : IsGrothendieckUniverse V) (hW : IsGrothendieckUniverse W) (hVW : V ∈ W)
    {E E' : Fin S.objArity → ZFSet.{u}} {F : Fin S.morArity → ZFSet.{u}}
    {B B' : Fin T.objArity → ZFSet.{u}} {G : Fin T.morArity → ZFSet.{u}} (hE : ∀ i, E i ∈ V)
    (hE' : ∀ i, E' i ∈ V) (hF : ∀ i, F i ∈ V) (hB : ∀ i, B i ∈ V) (hB' : ∀ i, B' i ∈ V)
    (hG : ∀ i, G i ∈ V) :
    mutationMorRel {y | y ∈ V} M E E' F B B' G ↔ mutationMorRel {y | y ∈ W} M E E' F B B' G :=
  and_congr (saObjRel_transfer hT hM hV hW hVW hE hB)
    (and_congr (saObjRel_transfer hT hM hV hW hVW hE' hB')
      (and_congr (saOneSpecimen_transfer hT hV hW hVW hB hB' hG)
        (hM.2.1 V W hV hW hVW _ (saElimMem hE (saElimMem hE' (saElimMem hF hG))))))

variable {M : MutationData S T} {N : MutationData T U}

/-- The object formula of the corrected composite is absolute between universes `V ∈ W`. In the
direction from `W` to `V`, the witness `B` lies in `V`: `E` is a species-object in both models,
and `B` is the unique `𝔐(E)` of the model `W`, which is the `𝔐(E)` of the model `V`. -/
theorem saComp_obj_transfer (hS : IsSpecies.{u} S) (hT : IsSpecies.{u} T)
    (hM : IsMutation.{u} M) (hN : IsMutation.{u} N) (hV : IsGrothendieckUniverse V)
    (hW : IsGrothendieckUniverse W) (hVW : V ∈ W) (E : Fin S.objArity → ZFSet.{u})
    (C : Fin U.objArity → ZFSet.{u}) (hE : ∀ i, E i ∈ V) (hC : ∀ i, C i ∈ V) :
    speciesHolds {y | y ∈ V} (saMutationComp N M).mutObjFormula (Sum.elim E C) ↔
      speciesHolds {y | y ∈ W} (saMutationComp N M).mutObjFormula (Sum.elim E C) := by
  have hEW : ∀ i, E i ∈ W := fun i => hW.transitive V hVW _ (hE i)
  have hCW : ∀ i, C i ∈ W := fun i => hW.transitive V hVW _ (hC i)
  rw [saComp_obj_holds (D := {y | y ∈ V}) N M E C hE hC,
    saComp_obj_holds (D := {y | y ∈ W}) N M E C hEW hCW,
    mutationAfter_obj_holds (D := {y | y ∈ V}) N M E C hE hC,
    mutationAfter_obj_holds (D := {y | y ∈ W}) N M E C hEW hCW]
  constructor
  · rintro ⟨hz, B, hB, h₁, h₂⟩
    exact ⟨saUp hS.1.2 hV hW hVW hz, B, saUp hT.1.2 hV hW hVW hB, saUp hM.1 hV hW hVW h₁,
      saUp hN.1 hV hW hVW h₂⟩
  · rintro ⟨hz, B, hB, h₁, h₂⟩
    have hzV := saDown hS.1.2 hV hW hVW hE hz
    obtain ⟨B₀, hB₀, -⟩ := (hM.2.2 _ (saUnivModel hV)).1 E hzV
    have hB₀V : ∀ i, B₀ i ∈ V := speciesHolds_mem hB₀.1
    have e : B = B₀ := ((hM.2.2 _ (saUnivModel hW)).1 E hz).unique ⟨hB, h₁⟩
      ((saObjRel_transfer hT hM hV hW hVW hE hB₀V).1 hB₀)
    rw [e] at h₂
    exact ⟨hzV, B₀, hB₀.1, hB₀.2, saDown hN.1 hV hW hVW (saElimMem hB₀V hC) h₂⟩

/-- The morphism formula of the corrected composite is absolute between universes `V ∈ W`. In
the direction from `W` to `V`, the witnesses `B`, `B'`, `G` lie in `V` by the uniqueness clauses
(a) and (b) of Definition 3.3 (i) for `𝔐` in the two models. -/
theorem saComp_mor_transfer (hS : IsSpecies.{u} S) (hT : IsSpecies.{u} T)
    (hM : IsMutation.{u} M) (hN : IsMutation.{u} N) (hV : IsGrothendieckUniverse V)
    (hW : IsGrothendieckUniverse W) (hVW : V ∈ W) (E E' : Fin S.objArity → ZFSet.{u})
    (F : Fin S.morArity → ZFSet.{u}) (H : Fin U.morArity → ZFSet.{u}) (hE : ∀ i, E i ∈ V)
    (hE' : ∀ i, E' i ∈ V) (hF : ∀ i, F i ∈ V) (hH : ∀ i, H i ∈ V) :
    speciesHolds {y | y ∈ V} (saMutationComp N M).mutMorFormula
        (Sum.elim E (Sum.elim E' (Sum.elim F H))) ↔
      speciesHolds {y | y ∈ W} (saMutationComp N M).mutMorFormula
        (Sum.elim E (Sum.elim E' (Sum.elim F H))) := by
  have hx : ∀ a, Sum.elim E (Sum.elim E' (Sum.elim F H)) a ∈ V :=
    saElimMem hE (saElimMem hE' (saElimMem hF hH))
  have hxW : ∀ a, Sum.elim E (Sum.elim E' (Sum.elim F H)) a ∈ W :=
    fun a => hW.transitive V hVW _ (hx a)
  rw [saComp_mor_holds (D := {y | y ∈ V}) N M E E' F H hx,
    saComp_mor_holds (D := {y | y ∈ W}) N M E E' F H hxW,
    sxAfter_mor_holds (D := {y | y ∈ V}) N M E E' F H hx,
    sxAfter_mor_holds (D := {y | y ∈ W}) N M E E' F H hxW]
  constructor
  · rintro ⟨h1, B, B', G, k₁, k₂, k₃, k₄, k₅, k₆, k₇⟩
    exact ⟨(saOneSpecimen_transfer hS hV hW hVW hE hE' hF).1 h1, B, B', G,
      saUp hT.1.2 hV hW hVW k₁, saUp hT.1.2 hV hW hVW k₂, saUp hT.2.2.1 hV hW hVW k₃,
      saUp hM.1 hV hW hVW k₄, saUp hM.1 hV hW hVW k₅, saUp hM.2.1 hV hW hVW k₆,
      saUp hN.2.1 hV hW hVW k₇⟩
  · rintro ⟨h1, B, B', G, k₁, k₂, k₃, k₄, k₅, k₆, k₇⟩
    have h1V := (saOneSpecimen_transfer hS hV hW hVW hE hE' hF).2 h1
    have hMV := hM.2.2 _ (saUnivModel hV)
    have hMW := hM.2.2 _ (saUnivModel hW)
    obtain ⟨B₀, hB₀, -⟩ := hMV.1 E h1V.1
    obtain ⟨B₀', hB₀', -⟩ := hMV.1 E' h1V.2.1
    have hB₀V : ∀ i, B₀ i ∈ V := speciesHolds_mem hB₀.1
    have hB₀'V : ∀ i, B₀' i ∈ V := speciesHolds_mem hB₀'.1
    have e₁ : B = B₀ := (hMW.1 E h1.1).unique ⟨k₁, k₄⟩
      ((saObjRel_transfer hT hM hV hW hVW hE hB₀V).1 hB₀)
    have e₂ : B' = B₀' := (hMW.1 E' h1.2.1).unique ⟨k₂, k₅⟩
      ((saObjRel_transfer hT hM hV hW hVW hE' hB₀'V).1 hB₀')
    obtain ⟨G₀, hG₀, -⟩ := hMV.2.1 E E' F B₀ B₀' h1V hB₀ hB₀'
    have hG₀V : ∀ i, G₀ i ∈ V := fun i => speciesHolds_mem hG₀.2.2.1.2.2 (Sum.inr (Sum.inr i))
    have hG₀W := (saMorRel_transfer hT hM hV hW hVW hE hE' hF hB₀V hB₀'V hG₀V).1 hG₀
    rw [← e₁, ← e₂] at hG₀W
    rw [← e₁] at hB₀V
    rw [← e₂] at hB₀'V
    have e₃ : G = G₀ := (hMW.2.1 E E' F B B' h1 ⟨k₁, k₄⟩ ⟨k₂, k₅⟩).unique
      ⟨⟨k₁, k₄⟩, ⟨k₂, k₅⟩, ⟨k₁, k₂, k₃⟩, k₆⟩ hG₀W
    rw [← e₃] at hG₀V
    exact ⟨h1V, B, B', G, saDown hT.1.2 hV hW hVW hB₀V k₁, saDown hT.1.2 hV hW hVW hB₀'V k₂,
      saDown hT.2.2.1 hV hW hVW (saElimMem hB₀V (saElimMem hB₀'V hG₀V)) k₃,
      saDown hM.1 hV hW hVW (saElimMem hE hB₀V) k₄,
      saDown hM.1 hV hW hVW (saElimMem hE' hB₀'V) k₅,
      saDown hM.2.1 hV hW hVW (saElimMem hE (saElimMem hE' (saElimMem hF hG₀V))) k₆,
      saDown hN.2.1 hV hW hVW (saElimMem hB₀V (saElimMem hB₀'V (saElimMem hG₀V hH))) k₇⟩

end Transfer

/-- The composite of two mutations is a mutation (Definition 3.3 (i), "evident notions" of
page 73), for the corrected composite `saMutationComp`: if `𝔖`, `𝔗` are species and
`𝔐 : 𝔖 ⇝ 𝔗`, `𝔑 : 𝔗 ⇝ 𝔘` are mutations, then `𝔑 ∘ 𝔐` is a mutation. -/
theorem saMutationComp_isMutation {M : MutationData S T} {N : MutationData T U}
    (hS : IsSpecies.{u} S) (hT : IsSpecies.{u} T) (hM : IsMutation.{u} M)
    (hN : IsMutation.{u} N) : IsMutation.{u} (saMutationComp N M) := by
  refine ⟨?_, ?_, fun D hD => saComp_axiomsAt (sxAfter_axiomsAt (hM.2.2 D hD) (hN.2.2 D hD))⟩
  · intro V W hV hW hVW x hx
    have e : Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) = x := by
      funext c; rcases c with a | a <;> rfl
    have := saComp_obj_transfer hS hT hM hN hV hW hVW (x ∘ Sum.inl) (x ∘ Sum.inr)
      (fun i => hx _) (fun i => hx _)
    rwa [e] at this
  · intro V W hV hW hVW x hx
    have e : Sum.elim (x ∘ Sum.inl) (Sum.elim (x ∘ Sum.inr ∘ Sum.inl)
        (Sum.elim (x ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl) (x ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr))) = x := by
      funext c; rcases c with a | a | a | a <;> rfl
    have := saComp_mor_transfer hS hT hM hN hV hW hVW (x ∘ Sum.inl) (x ∘ Sum.inr ∘ Sum.inl)
      (x ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl) (x ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr) (fun i => hx _)
      (fun i => hx _) (fun i => hx _) (fun i => hx _)
    rwa [e] at this

end Composite

/-! ## Example 3.2: the formulas of the species of categories -/

section Categories

variable {α : Type*} {n : ℕ}

/-- `∃ x ∈ P^k(w₁ ∪ w₂), φ`, written as `¬ ∀ x ∈ P^k(w₁ ∪ w₂), ¬ φ`. -/
def saPEx (k : ℕ) (w₁ w₂ : α ⊕ Fin n) (φ : speciesLang.BoundedFormula α (n + 1)) :
    speciesLang.BoundedFormula α n :=
  (saPAll k w₁ w₂ φ.not).not

theorem saPEx_powBounded (k : ℕ) (w₁ w₂ : α ⊕ Fin n)
    {φ : speciesLang.BoundedFormula α (n + 1)} (h : SaIsPowBounded φ) :
    SaIsPowBounded (saPEx k w₁ w₂ φ) :=
  (SaIsPowBounded.pall k w₁ w₂ (h.imp SaIsPowBounded.falsum)).imp
    SaIsPowBounded.falsum

theorem saInf_powBounded {φ ψ : speciesLang.BoundedFormula α n} (h₁ : SaIsPowBounded φ)
    (h₂ : SaIsPowBounded ψ) : SaIsPowBounded (φ ⊓ ψ) :=
  (h₁.imp (h₂.imp SaIsPowBounded.falsum)).imp SaIsPowBounded.falsum

section Univ

variable (v : α → sxUniv.{u}) (xs : Fin n → sxUniv.{u})

@[simp] theorem saPAll_realizeU (k : ℕ) (w₁ w₂ : α ⊕ Fin n)
    (φ : speciesLang.BoundedFormula α (n + 1)) :
    speciesRealizeAt sxUniv (saPAll k w₁ w₂ φ) v xs ↔
      ∀ a : ZFSet.{u}, a ∈ saPowIter (sxEnv v xs w₁ ∪ sxEnv v xs w₂) k →
        speciesRealizeAt sxUniv φ v (Fin.snoc xs ⟨a, Set.mem_univ a⟩) := by
  rw [saPAll_realize (D := sxUniv) (fun _ _ _ _ => Set.mem_univ _)]
  exact ⟨fun h a ha => h ⟨a, Set.mem_univ a⟩ ha, fun h x hx => h x.1 hx⟩

@[simp] theorem saPEx_realizeU (k : ℕ) (w₁ w₂ : α ⊕ Fin n)
    (φ : speciesLang.BoundedFormula α (n + 1)) :
    speciesRealizeAt sxUniv (saPEx k w₁ w₂ φ) v xs ↔
      ∃ a : ZFSet.{u}, a ∈ saPowIter (sxEnv v xs w₁ ∪ sxEnv v xs w₂) k ∧
        speciesRealizeAt sxUniv φ v (Fin.snoc xs ⟨a, Set.mem_univ a⟩) := by
  unfold saPEx
  rw [sxRealize_not, saPAll_realizeU]
  simp only [sxRealize_not, not_forall, not_not, exists_prop]

end Univ

/-- `((f, g), h) ∈ c`: in the composition relation `c`, `h` is the composite of `f` with `g`
(`h = g ∘ f`). -/
def saComp3F (c f g h : α ⊕ Fin n) : speciesLang.BoundedFormula α n :=
  sxBex c (sxBex sxTop (sxBex sxTop
    (sxKPairF sxTop (sxLift (sxLift (sxLift f))) (sxLift (sxLift (sxLift g))) ⊓
      sxKPairF (sxLift (sxLift sxTop)) sxTop (sxLift (sxLift (sxLift h))))))

/-- `u` is an identity arrow of `(a, c)`: for all `f, h ∈ a`, `((u, f), h) ∈ c` implies `h = f`
and `((f, u), h) ∈ c` implies `h = f`. -/
def saIdArF (a c u : α ⊕ Fin n) : speciesLang.BoundedFormula α n :=
  speciesBall a (speciesBall (sxLift a)
    ((saComp3F (sxLift (sxLift c)) (sxLift (sxLift u)) (sxLift sxTop) sxTop).imp
        (sxEqF sxTop (sxLift sxTop)) ⊓
      (saComp3F (sxLift (sxLift c)) (sxLift sxTop) (sxLift (sxLift u)) sxTop).imp
        (sxEqF sxTop (sxLift sxTop))))

/-- `c ⊆ (a × a) × a`, written as: every `p ∈ c` is `((f, g), h)` with `f, g, h ∈ a`. -/
def saCatSubF (a c : α ⊕ Fin n) : speciesLang.BoundedFormula α n :=
  speciesBall c (sxBex sxTop (sxBex sxTop (sxBex (sxLift (sxLift (sxLift a)))
    (sxBex (sxLift (sxLift (sxLift (sxLift a))))
      (sxBex (sxLift (sxLift (sxLift (sxLift (sxLift a)))))
        (sxKPairF (sxLift (sxLift (sxLift sxTop))) (sxLift (sxLift sxTop)) (sxLift sxTop) ⊓
          sxKPairF (sxLift (sxLift (sxLift (sxLift (sxLift sxTop)))))
            (sxLift (sxLift (sxLift sxTop))) sxTop))))))

/-- Composites are unique: `((f, g), h) ∈ c` and `((f, g), h') ∈ c` imply `h' = h`. -/
def saCatFunF (a c : α ⊕ Fin n) : speciesLang.BoundedFormula α n :=
  speciesBall a (speciesBall (sxLift a) (speciesBall (sxLift (sxLift a))
    (speciesBall (sxLift (sxLift (sxLift a)))
      ((saComp3F (sxLift (sxLift (sxLift (sxLift c)))) (sxLift (sxLift (sxLift sxTop)))
          (sxLift (sxLift sxTop)) (sxLift sxTop)).imp
        ((saComp3F (sxLift (sxLift (sxLift (sxLift c)))) (sxLift (sxLift (sxLift sxTop)))
          (sxLift (sxLift sxTop)) sxTop).imp (sxEqF sxTop (sxLift sxTop)))))))

/-- If `g ∘ f` and `k ∘ g` are defined, then `k ∘ (g ∘ f)` and `(k ∘ g) ∘ f` are defined and
equal. -/
def saCatAssocAF (a c : α ⊕ Fin n) : speciesLang.BoundedFormula α n :=
  speciesBall a (speciesBall (sxLift a) (speciesBall (sxLift (sxLift a))
    (speciesBall (sxLift (sxLift (sxLift a))) (speciesBall (sxLift (sxLift (sxLift (sxLift a))))
      ((saComp3F (sxLift (sxLift (sxLift (sxLift (sxLift c)))))
          (sxLift (sxLift (sxLift (sxLift sxTop)))) (sxLift (sxLift (sxLift sxTop)))
          (sxLift sxTop)).imp
        ((saComp3F (sxLift (sxLift (sxLift (sxLift (sxLift c)))))
            (sxLift (sxLift (sxLift sxTop))) (sxLift (sxLift sxTop)) sxTop).imp
          (sxBex (sxLift (sxLift (sxLift (sxLift (sxLift a)))))
            (saComp3F (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift c))))))
                (sxLift (sxLift sxTop)) (sxLift (sxLift (sxLift sxTop))) sxTop ⊓
              saComp3F (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift c))))))
                (sxLift (sxLift (sxLift (sxLift (sxLift sxTop))))) (sxLift sxTop) sxTop))))))))

/-- If `g ∘ f` and `k ∘ (g ∘ f)` are defined, then `k ∘ g` is defined and
`(k ∘ g) ∘ f = k ∘ (g ∘ f)`. -/
def saCatAssocBF (a c : α ⊕ Fin n) : speciesLang.BoundedFormula α n :=
  speciesBall a (speciesBall (sxLift a) (speciesBall (sxLift (sxLift a))
    (speciesBall (sxLift (sxLift (sxLift a))) (speciesBall (sxLift (sxLift (sxLift (sxLift a))))
      ((saComp3F (sxLift (sxLift (sxLift (sxLift (sxLift c)))))
          (sxLift (sxLift (sxLift (sxLift sxTop)))) (sxLift (sxLift (sxLift sxTop)))
          (sxLift sxTop)).imp
        ((saComp3F (sxLift (sxLift (sxLift (sxLift (sxLift c))))) (sxLift sxTop)
            (sxLift (sxLift sxTop)) sxTop).imp
          (sxBex (sxLift (sxLift (sxLift (sxLift (sxLift a)))))
            (saComp3F (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift c))))))
                (sxLift (sxLift (sxLift (sxLift sxTop)))) (sxLift (sxLift (sxLift sxTop))) sxTop ⊓
              saComp3F (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift c))))))
                (sxLift (sxLift (sxLift (sxLift (sxLift sxTop))))) sxTop (sxLift sxTop)))))))))

/-- If `k ∘ g` and `(k ∘ g) ∘ f` are defined, then `g ∘ f` is defined and
`k ∘ (g ∘ f) = (k ∘ g) ∘ f`. -/
def saCatAssocCF (a c : α ⊕ Fin n) : speciesLang.BoundedFormula α n :=
  speciesBall a (speciesBall (sxLift a) (speciesBall (sxLift (sxLift a))
    (speciesBall (sxLift (sxLift (sxLift a))) (speciesBall (sxLift (sxLift (sxLift (sxLift a))))
      ((saComp3F (sxLift (sxLift (sxLift (sxLift (sxLift c)))))
          (sxLift (sxLift (sxLift sxTop))) (sxLift (sxLift sxTop)) (sxLift sxTop)).imp
        ((saComp3F (sxLift (sxLift (sxLift (sxLift (sxLift c)))))
            (sxLift (sxLift (sxLift (sxLift sxTop)))) (sxLift sxTop) sxTop).imp
          (sxBex (sxLift (sxLift (sxLift (sxLift (sxLift a)))))
            (saComp3F (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift c))))))
                (sxLift (sxLift (sxLift (sxLift (sxLift sxTop)))))
                (sxLift (sxLift (sxLift (sxLift sxTop)))) sxTop ⊓
              saComp3F (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift c)))))) sxTop
                (sxLift (sxLift (sxLift sxTop))) (sxLift sxTop)))))))))

/-- Every arrow `g` has identity arrows `u`, `u'` with `g ∘ u` and `u' ∘ g` defined. -/
def saCatUnitF (a c : α ⊕ Fin n) : speciesLang.BoundedFormula α n :=
  speciesBall a (sxBex (sxLift a) (sxBex (sxLift (sxLift a))
    (saIdArF (sxLift (sxLift (sxLift a))) (sxLift (sxLift (sxLift c))) (sxLift sxTop) ⊓
      saIdArF (sxLift (sxLift (sxLift a))) (sxLift (sxLift (sxLift c))) sxTop ⊓
      sxBex (sxLift (sxLift (sxLift a)))
        (saComp3F (sxLift (sxLift (sxLift (sxLift c)))) (sxLift (sxLift sxTop))
          (sxLift (sxLift (sxLift sxTop))) sxTop) ⊓
      sxBex (sxLift (sxLift (sxLift a)))
        (saComp3F (sxLift (sxLift (sxLift (sxLift c)))) (sxLift (sxLift (sxLift sxTop)))
          (sxLift sxTop) sxTop))))

/-- The formula `Φ₀(A, C)` of Example 3.2: `(A, C)` is a small category given by its set `A` of
arrows and its set `C` of composition relations `((f, g), g ∘ f)` (the arrows-only description
of a category). -/
def saCatF (a c : α ⊕ Fin n) : speciesLang.BoundedFormula α n :=
  saCatSubF a c ⊓ saCatFunF a c ⊓ saCatAssocAF a c ⊓ saCatAssocBF a c ⊓ saCatAssocCF a c ⊓
    saCatUnitF a c

/-- `φ` is (the graph of the map on arrows of) a functor from `(a, c)` to `(a', c')`: a function
from `a` to `a'` that preserves composites and identity arrows. -/
def saFunctorF (a c a' c' φ : α ⊕ Fin n) : speciesLang.BoundedFormula α n :=
  sxFuncF a a' φ ⊓
    speciesBall a (speciesBall (sxLift a) (speciesBall (sxLift (sxLift a))
      (speciesBall (sxLift (sxLift (sxLift a'))) (speciesBall (sxLift (sxLift (sxLift (sxLift a'))))
        (speciesBall (sxLift (sxLift (sxLift (sxLift (sxLift a')))))
          ((saComp3F (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift c))))))
              (sxLift (sxLift (sxLift (sxLift (sxLift sxTop)))))
              (sxLift (sxLift (sxLift (sxLift sxTop)))) (sxLift (sxLift (sxLift sxTop)))).imp
            ((sxAppF (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift φ))))))
                (sxLift (sxLift (sxLift (sxLift (sxLift sxTop))))) (sxLift (sxLift sxTop))).imp
              ((sxAppF (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift φ))))))
                  (sxLift (sxLift (sxLift (sxLift sxTop)))) (sxLift sxTop)).imp
                ((sxAppF (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift φ))))))
                    (sxLift (sxLift (sxLift sxTop))) sxTop).imp
                  (saComp3F (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift c'))))))
                    (sxLift (sxLift sxTop)) (sxLift sxTop) sxTop)))))))))) ⊓
    speciesBall a (speciesBall (sxLift a')
      ((saIdArF (sxLift (sxLift a)) (sxLift (sxLift c)) (sxLift sxTop)).imp
        ((sxAppF (sxLift (sxLift φ)) (sxLift sxTop) sxTop).imp
          (saIdArF (sxLift (sxLift a')) (sxLift (sxLift c')) sxTop))))

/-- `τ` is a natural isomorphism from the functor `φ` to the functor `ψ`: a function from `a` to
`a'` whose value `τ(u)` at an identity arrow `u` is an isomorphism, natural in the sense that
`ψ(f) ∘ τ(u) = τ(v) ∘ φ(f)` for every arrow `f` from `u` to `v` (the values of `τ` at
arrows that are not identities play no role). -/
def saNatIsoF (a c a' c' φ ψ τ : α ⊕ Fin n) : speciesLang.BoundedFormula α n :=
  sxFuncF a a' τ ⊓
    speciesBall a (speciesBall (sxLift a) (speciesBall (sxLift (sxLift a))
      (speciesBall (sxLift (sxLift (sxLift a'))) (speciesBall (sxLift (sxLift (sxLift (sxLift a'))))
        (speciesBall (sxLift (sxLift (sxLift (sxLift (sxLift a')))))
          (speciesBall (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift a'))))))
            ((saIdArF (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift a)))))))
                (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift c)))))))
                (sxLift (sxLift (sxLift (sxLift (sxLift sxTop)))))).imp
              ((saIdArF (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift a)))))))
                  (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift c)))))))
                  (sxLift (sxLift (sxLift (sxLift sxTop))))).imp
                ((saComp3F (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift c)))))))
                    (sxLift (sxLift (sxLift (sxLift (sxLift sxTop)))))
                    (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift sxTop))))))
                    (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift sxTop))))))).imp
                  ((saComp3F (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift c)))))))
                      (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift sxTop))))))
                      (sxLift (sxLift (sxLift (sxLift sxTop))))
                      (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift sxTop))))))).imp
                    ((sxAppF (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift φ)))))))
                        (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift sxTop))))))
                        (sxLift (sxLift (sxLift sxTop)))).imp
                      ((sxAppF (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift ψ)))))))
                          (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift sxTop))))))
                          (sxLift (sxLift sxTop))).imp
                        ((sxAppF (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift τ)))))))
                            (sxLift (sxLift (sxLift (sxLift (sxLift sxTop))))) (sxLift sxTop)).imp
                          ((sxAppF (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift τ)))))))
                              (sxLift (sxLift (sxLift (sxLift sxTop)))) sxTop).imp
                            (sxBex (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift a')))))))
                              (saComp3F (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift
                                    (sxLift c'))))))))
                                  (sxLift (sxLift sxTop)) (sxLift (sxLift (sxLift sxTop))) sxTop ⊓
                                saComp3F (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift (sxLift
                                    (sxLift c'))))))))
                                  (sxLift (sxLift (sxLift (sxLift sxTop)))) (sxLift sxTop)
                                  sxTop)))))))))))))))) ⊓
    speciesBall a (speciesBall (sxLift a')
      ((saIdArF (sxLift (sxLift a)) (sxLift (sxLift c)) (sxLift sxTop)).imp
        ((sxAppF (sxLift (sxLift τ)) (sxLift sxTop) sxTop).imp
          (sxBex (sxLift (sxLift a'))
            (sxBex (sxLift (sxLift (sxLift a')))
                (saComp3F (sxLift (sxLift (sxLift (sxLift c')))) (sxLift (sxLift sxTop))
                    (sxLift sxTop) sxTop ⊓
                  saIdArF (sxLift (sxLift (sxLift (sxLift a'))))
                    (sxLift (sxLift (sxLift (sxLift c')))) sxTop) ⊓
              sxBex (sxLift (sxLift (sxLift a')))
                (saComp3F (sxLift (sxLift (sxLift (sxLift c')))) (sxLift sxTop)
                    (sxLift (sxLift sxTop)) sxTop ⊓
                  saIdArF (sxLift (sxLift (sxLift (sxLift a'))))
                    (sxLift (sxLift (sxLift (sxLift c')))) sxTop))))))

/-- The functors `φ`, `ψ` are isomorphic: there is a natural isomorphism `τ ∈ P³(a ∪ a')` from
`φ` to `ψ` (every function from `a` to `a'` lies in `P³(a ∪ a')`). The quantifier over `τ` is
bounded by an iterated power set, not by a variable. -/
def saIsoFunF (a c a' c' φ ψ : α ⊕ Fin n) : speciesLang.BoundedFormula α n :=
  saPEx 3 a a' (saNatIsoF (sxLift a) (sxLift c) (sxLift a') (sxLift c') (sxLift φ) (sxLift ψ)
    sxTop)

/-- The formula `Φ₁(E, E', F)` of Example 3.2: `F` is an isomorphism class of functors from
`(a, c)` to `(a', c')`: `F` is nonempty, its members are functors, any two members are isomorphic,
and every functor (an element of `P³(a ∪ a')`) isomorphic to a member is a member. -/
def saIsoClassF (a c a' c' F : α ⊕ Fin n) : speciesLang.BoundedFormula α n :=
  sxBex F ⊤ ⊓
    speciesBall F (saFunctorF (sxLift a) (sxLift c) (sxLift a') (sxLift c') sxTop) ⊓
    speciesBall F (speciesBall (sxLift F)
      (saIsoFunF (sxLift (sxLift a)) (sxLift (sxLift c)) (sxLift (sxLift a'))
        (sxLift (sxLift c')) (sxLift sxTop) sxTop)) ⊓
    speciesBall F (saPAll 3 (sxLift a) (sxLift a')
      ((saFunctorF (sxLift (sxLift a)) (sxLift (sxLift c)) (sxLift (sxLift a'))
          (sxLift (sxLift c')) sxTop).imp
        ((saIsoFunF (sxLift (sxLift a)) (sxLift (sxLift c)) (sxLift (sxLift a'))
            (sxLift (sxLift c')) (sxLift sxTop) sxTop).imp
          (sxMemF sxTop (sxLift (sxLift F))))))

/-- The formula `Φ₁∘₁` used here for Example 3.2: `F''` is a composite of `F` with `F'` when it
contains `ψ ∘ φ` for all `φ ∈ F`, `ψ ∈ F'` (with `sxCompF`). -/
def saClassCompF (a a' a'' F F' F'' : α ⊕ Fin n) : speciesLang.BoundedFormula α n :=
  speciesBall F (speciesBall (sxLift F') (sxBex (sxLift (sxLift F''))
    (sxCompF (sxLift (sxLift (sxLift a))) (sxLift (sxLift (sxLift a')))
      (sxLift (sxLift (sxLift a''))) (sxLift (sxLift sxTop)) (sxLift sxTop) sxTop)))

/-! ### The meaning of these formulas in `ZFSet` -/

/-- `u` is an identity arrow of `(A, C)`. -/
def saIsIdAr (A C u : ZFSet.{u}) : Prop :=
  ∀ f, f ∈ A → ∀ h, h ∈ A →
    (ZFSet.pair (ZFSet.pair u f) h ∈ C → h = f) ∧ (ZFSet.pair (ZFSet.pair f u) h ∈ C → h = f)

/-- `(A, C)` is a small category in the arrows-only description. -/
def saIsCat (A C : ZFSet.{u}) : Prop :=
  (∀ p, p ∈ C → ∃ s, s ∈ p ∧ ∃ q, q ∈ s ∧ ∃ f, f ∈ A ∧ ∃ g, g ∈ A ∧ ∃ h, h ∈ A ∧
    q = ZFSet.pair f g ∧ p = ZFSet.pair q h) ∧
  (∀ f, f ∈ A → ∀ g, g ∈ A → ∀ h, h ∈ A → ∀ h', h' ∈ A →
    ZFSet.pair (ZFSet.pair f g) h ∈ C → ZFSet.pair (ZFSet.pair f g) h' ∈ C → h' = h) ∧
  (∀ f, f ∈ A → ∀ g, g ∈ A → ∀ k, k ∈ A → ∀ gf, gf ∈ A → ∀ kg, kg ∈ A →
    ZFSet.pair (ZFSet.pair f g) gf ∈ C → ZFSet.pair (ZFSet.pair g k) kg ∈ C →
      ∃ x, x ∈ A ∧ ZFSet.pair (ZFSet.pair gf k) x ∈ C ∧ ZFSet.pair (ZFSet.pair f kg) x ∈ C) ∧
  (∀ f, f ∈ A → ∀ g, g ∈ A → ∀ k, k ∈ A → ∀ gf, gf ∈ A → ∀ x, x ∈ A →
    ZFSet.pair (ZFSet.pair f g) gf ∈ C → ZFSet.pair (ZFSet.pair gf k) x ∈ C →
      ∃ kg, kg ∈ A ∧ ZFSet.pair (ZFSet.pair g k) kg ∈ C ∧ ZFSet.pair (ZFSet.pair f kg) x ∈ C) ∧
  (∀ f, f ∈ A → ∀ g, g ∈ A → ∀ k, k ∈ A → ∀ kg, kg ∈ A → ∀ x, x ∈ A →
    ZFSet.pair (ZFSet.pair g k) kg ∈ C → ZFSet.pair (ZFSet.pair f kg) x ∈ C →
      ∃ gf, gf ∈ A ∧ ZFSet.pair (ZFSet.pair f g) gf ∈ C ∧ ZFSet.pair (ZFSet.pair gf k) x ∈ C) ∧
  (∀ g, g ∈ A → ∃ u, u ∈ A ∧ ∃ u', u' ∈ A ∧ saIsIdAr A C u ∧ saIsIdAr A C u' ∧
    (∃ h, h ∈ A ∧ ZFSet.pair (ZFSet.pair u g) h ∈ C) ∧
    ∃ h, h ∈ A ∧ ZFSet.pair (ZFSet.pair g u') h ∈ C)

/-- `φ` is a functor from `(A, C)` to `(A', C')`. -/
def saIsFunctor (A C A' C' φ : ZFSet.{u}) : Prop :=
  ZFSet.IsFunc A A' φ ∧
  (∀ f, f ∈ A → ∀ g, g ∈ A → ∀ h, h ∈ A → ∀ x, x ∈ A' → ∀ y, y ∈ A' → ∀ z, z ∈ A' →
    ZFSet.pair (ZFSet.pair f g) h ∈ C → ZFSet.pair f x ∈ φ → ZFSet.pair g y ∈ φ →
      ZFSet.pair h z ∈ φ → ZFSet.pair (ZFSet.pair x y) z ∈ C') ∧
  ∀ u, u ∈ A → ∀ x, x ∈ A' → saIsIdAr A C u → ZFSet.pair u x ∈ φ → saIsIdAr A' C' x

/-- `τ` is a natural isomorphism from `φ` to `ψ`. -/
def saIsNatIso (A C A' C' φ ψ τ : ZFSet.{u}) : Prop :=
  ZFSet.IsFunc A A' τ ∧
  (∀ f, f ∈ A → ∀ u, u ∈ A → ∀ v, v ∈ A → ∀ p, p ∈ A' → ∀ q, q ∈ A' → ∀ r, r ∈ A' →
    ∀ s, s ∈ A' → saIsIdAr A C u → saIsIdAr A C v → ZFSet.pair (ZFSet.pair u f) f ∈ C →
      ZFSet.pair (ZFSet.pair f v) f ∈ C → ZFSet.pair f p ∈ φ → ZFSet.pair f q ∈ ψ →
        ZFSet.pair u r ∈ τ → ZFSet.pair v s ∈ τ →
          ∃ w, w ∈ A' ∧ ZFSet.pair (ZFSet.pair r q) w ∈ C' ∧
            ZFSet.pair (ZFSet.pair p s) w ∈ C') ∧
  ∀ u, u ∈ A → ∀ r, r ∈ A' → saIsIdAr A C u → ZFSet.pair u r ∈ τ →
    ∃ t, t ∈ A' ∧ (∃ e, e ∈ A' ∧ ZFSet.pair (ZFSet.pair r t) e ∈ C' ∧ saIsIdAr A' C' e) ∧
      ∃ e, e ∈ A' ∧ ZFSet.pair (ZFSet.pair t r) e ∈ C' ∧ saIsIdAr A' C' e

/-- The functors `φ`, `ψ` are isomorphic. -/
def saIsoFunctors (A C A' C' φ ψ : ZFSet.{u}) : Prop :=
  ∃ τ, τ ∈ saPowIter (A ∪ A') 3 ∧ saIsNatIso A C A' C' φ ψ τ

/-- `F` is an isomorphism class of functors from `(A, C)` to `(A', C')`. -/
def saIsIsoClass (A C A' C' F : ZFSet.{u}) : Prop :=
  (∃ φ, φ ∈ F) ∧ (∀ φ, φ ∈ F → saIsFunctor A C A' C' φ) ∧
  (∀ φ, φ ∈ F → ∀ ψ, ψ ∈ F → saIsoFunctors A C A' C' φ ψ) ∧
  ∀ φ, φ ∈ F → ∀ ψ, ψ ∈ saPowIter (A ∪ A') 3 → saIsFunctor A C A' C' ψ →
    saIsoFunctors A C A' C' φ ψ → ψ ∈ F

section Univ

variable (v : α → sxUniv.{u}) (xs : Fin n → sxUniv.{u})

@[simp] theorem saComp3F_realizeU (c f g h : α ⊕ Fin n) :
    speciesRealizeAt sxUniv (saComp3F c f g h) v xs ↔
      ZFSet.pair (ZFSet.pair (sxEnv v xs f) (sxEnv v xs g)) (sxEnv v xs h) ∈ sxEnv v xs c := by
  simp only [saComp3F, sxBex_realizeU, sxRealize_inf, sxKPairF_realizeU, sxEnv_lift, sxEnv_top]
  constructor
  · rintro ⟨p, hp, s, hs, q, hq, rfl, rfl⟩
    exact hp
  · intro h
    exact ⟨_, h, {ZFSet.pair (sxEnv v xs f) (sxEnv v xs g)}, ZFSet.mem_pair.2 (Or.inl rfl),
      ZFSet.pair (sxEnv v xs f) (sxEnv v xs g), ZFSet.mem_singleton.2 rfl, rfl, rfl⟩

@[simp] theorem saIdArF_realizeU (a c w : α ⊕ Fin n) :
    speciesRealizeAt sxUniv (saIdArF a c w) v xs ↔
      saIsIdAr (sxEnv v xs a) (sxEnv v xs c) (sxEnv v xs w) := by
  simp only [saIdArF, saIsIdAr, sxBall_realizeU, sxRealize_inf, sxRealize_imp, saComp3F_realizeU,
    sxEqF_realize, sxEnv_lift, sxEnv_top]

theorem saCatF_realizeU (a c : α ⊕ Fin n) :
    speciesRealizeAt sxUniv (saCatF a c) v xs ↔ saIsCat (sxEnv v xs a) (sxEnv v xs c) := by
  simp only [saCatF, saCatSubF, saCatFunF, saCatAssocAF, saCatAssocBF, saCatAssocCF, saCatUnitF,
    saIsCat, sxBall_realizeU, sxBex_realizeU, sxRealize_inf, sxRealize_imp, saComp3F_realizeU,
    saIdArF_realizeU, sxKPairF_realizeU, sxEqF_realize, sxEnv_lift, sxEnv_top, and_assoc]

@[simp] theorem saFunctorF_realizeU (a c a' c' φ : α ⊕ Fin n) :
    speciesRealizeAt sxUniv (saFunctorF a c a' c' φ) v xs ↔
      saIsFunctor (sxEnv v xs a) (sxEnv v xs c) (sxEnv v xs a') (sxEnv v xs c')
        (sxEnv v xs φ) := by
  simp only [saFunctorF, saIsFunctor, sxBall_realizeU, sxRealize_inf, sxRealize_imp,
    saComp3F_realizeU, saIdArF_realizeU, sxAppF_realizeU, sxFuncF_realizeU, sxEnv_lift,
    sxEnv_top, and_assoc]

@[simp] theorem saNatIsoF_realizeU (a c a' c' φ ψ τ : α ⊕ Fin n) :
    speciesRealizeAt sxUniv (saNatIsoF a c a' c' φ ψ τ) v xs ↔
      saIsNatIso (sxEnv v xs a) (sxEnv v xs c) (sxEnv v xs a') (sxEnv v xs c')
        (sxEnv v xs φ) (sxEnv v xs ψ) (sxEnv v xs τ) := by
  simp only [saNatIsoF, saIsNatIso, sxBall_realizeU, sxBex_realizeU, sxRealize_inf,
    sxRealize_imp, saComp3F_realizeU, saIdArF_realizeU, sxAppF_realizeU, sxFuncF_realizeU,
    sxEnv_lift, sxEnv_top, and_assoc]

@[simp] theorem saIsoFunF_realizeU (a c a' c' φ ψ : α ⊕ Fin n) :
    speciesRealizeAt sxUniv (saIsoFunF a c a' c' φ ψ) v xs ↔
      saIsoFunctors (sxEnv v xs a) (sxEnv v xs c) (sxEnv v xs a') (sxEnv v xs c')
        (sxEnv v xs φ) (sxEnv v xs ψ) := by
  simp only [saIsoFunF, saIsoFunctors, saPEx_realizeU, saNatIsoF_realizeU, sxEnv_lift,
    sxEnv_top]

theorem saIsoClassF_realizeU (a c a' c' F : α ⊕ Fin n) :
    speciesRealizeAt sxUniv (saIsoClassF a c a' c' F) v xs ↔
      saIsIsoClass (sxEnv v xs a) (sxEnv v xs c) (sxEnv v xs a') (sxEnv v xs c')
        (sxEnv v xs F) := by
  simp only [saIsoClassF, saIsIsoClass, sxBall_realizeU, sxBex_realizeU, sxRealize_inf,
    sxRealize_imp, sxRealize_top, and_true, saPAll_realizeU, saFunctorF_realizeU,
    saIsoFunF_realizeU, sxMemF_realize, sxEnv_lift, sxEnv_top, and_assoc]

theorem saClassCompF_realizeU (a a' a'' F F' F'' : α ⊕ Fin n) :
    speciesRealizeAt sxUniv (saClassCompF a a' a'' F F' F'') v xs ↔
      ∀ φ, φ ∈ sxEnv v xs F → ∀ ψ, ψ ∈ sxEnv v xs F' → ∃ χ, χ ∈ sxEnv v xs F'' ∧
        ∀ x, x ∈ sxEnv v xs a → ∀ y, y ∈ sxEnv v xs a' → ∀ z, z ∈ sxEnv v xs a'' →
          ZFSet.pair x y ∈ φ → ZFSet.pair y z ∈ ψ → ZFSet.pair x z ∈ χ := by
  simp only [saClassCompF, sxBall_realizeU, sxBex_realizeU, sxCompF_realizeU, sxEnv_lift,
    sxEnv_top]

end Univ

/-! ### Boundedness -/

theorem saComp3F_delta0 (c f g h : α ⊕ Fin n) : IsSpeciesDelta0 (saComp3F c f g h) :=
  sxBex_delta0 _ (sxBex_delta0 _ (sxBex_delta0 _
    (sxInf_delta0 (sxKPairF_delta0 _ _ _) (sxKPairF_delta0 _ _ _))))

theorem saIdArF_delta0 (a c w : α ⊕ Fin n) : IsSpeciesDelta0 (saIdArF a c w) :=
  IsSpeciesDelta0.ball _ (IsSpeciesDelta0.ball _ (sxInf_delta0
    ((saComp3F_delta0 _ _ _ _).imp (sxEqF_delta0 _ _))
    ((saComp3F_delta0 _ _ _ _).imp (sxEqF_delta0 _ _))))

theorem saCatF_delta0 (a c : α ⊕ Fin n) : IsSpeciesDelta0 (saCatF a c) := by
  unfold saCatF saCatSubF saCatFunF saCatAssocAF saCatAssocBF saCatAssocCF saCatUnitF
  repeat (first
    | exact saComp3F_delta0 _ _ _ _
    | exact saIdArF_delta0 _ _ _
    | exact sxKPairF_delta0 _ _ _
    | exact sxEqF_delta0 _ _
    | apply sxInf_delta0
    | apply sxBex_delta0
    | apply IsSpeciesDelta0.ball
    | apply IsSpeciesDelta0.imp)

theorem saFunctorF_delta0 (a c a' c' φ : α ⊕ Fin n) :
    IsSpeciesDelta0 (saFunctorF a c a' c' φ) := by
  unfold saFunctorF
  repeat (first
    | exact saComp3F_delta0 _ _ _ _
    | exact saIdArF_delta0 _ _ _
    | exact sxAppF_delta0 _ _ _
    | exact sxFuncF_delta0 _ _ _
    | apply sxInf_delta0
    | apply IsSpeciesDelta0.ball
    | apply IsSpeciesDelta0.imp)

theorem saNatIsoF_delta0 (a c a' c' φ ψ τ : α ⊕ Fin n) :
    IsSpeciesDelta0 (saNatIsoF a c a' c' φ ψ τ) := by
  unfold saNatIsoF
  repeat (first
    | exact saComp3F_delta0 _ _ _ _
    | exact saIdArF_delta0 _ _ _
    | exact sxAppF_delta0 _ _ _
    | exact sxFuncF_delta0 _ _ _
    | apply sxInf_delta0
    | apply sxBex_delta0
    | apply IsSpeciesDelta0.ball
    | apply IsSpeciesDelta0.imp)

theorem saIsoFunF_powBounded (a c a' c' φ ψ : α ⊕ Fin n) :
    SaIsPowBounded (saIsoFunF a c a' c' φ ψ) :=
  saPEx_powBounded 3 a a' (saIsPowBounded_of_delta0 (saNatIsoF_delta0 _ _ _ _ _ _ _))

theorem saIsoClassF_powBounded (a c a' c' F : α ⊕ Fin n) :
    SaIsPowBounded (saIsoClassF a c a' c' F) := by
  unfold saIsoClassF
  refine saInf_powBounded (saInf_powBounded (saInf_powBounded ?_ ?_) ?_) ?_
  · exact saIsPowBounded_of_delta0 (sxBex_delta0 _ sxTop_delta0)
  · exact SaIsPowBounded.ball _
      (saIsPowBounded_of_delta0 (saFunctorF_delta0 _ _ _ _ _))
  · exact SaIsPowBounded.ball _ (SaIsPowBounded.ball _ (saIsoFunF_powBounded _ _ _ _ _ _))
  · exact SaIsPowBounded.ball _ (SaIsPowBounded.pall _ _ _
      ((saIsPowBounded_of_delta0 (saFunctorF_delta0 _ _ _ _ _)).imp
        ((saIsoFunF_powBounded _ _ _ _ _ _).imp
          (saIsPowBounded_of_delta0 (sxMemF_delta0 _ _)))))

theorem saClassCompF_delta0 (a a' a'' F F' F'' : α ⊕ Fin n) :
    IsSpeciesDelta0 (saClassCompF a a' a'' F F' F'') :=
  IsSpeciesDelta0.ball _ (IsSpeciesDelta0.ball _ (sxBex_delta0 _ (sxCompF_delta0 _ _ _ _ _ _)))

end Categories

/-- The species data of Example 3.2 as encoded here: species-objects `(A, C)` (arrows and
composition relations of a small category), species-morphisms `F` (isomorphism classes of
functors), and `F''` a composite of `F` with `F'` when it contains the composites of their
members. -/
abbrev saCatSpecies : SpeciesData where
  spZero := { zsArity := 2, zsFormula := saCatF (Sum.inl 0) (Sum.inl 1) }
  spOne :=
    { osArity := 1
      osFormula := saIsoClassF (Sum.inl (Sum.inl 0)) (Sum.inl (Sum.inl 1))
        (Sum.inl (Sum.inr (Sum.inl 0))) (Sum.inl (Sum.inr (Sum.inl 1)))
        (Sum.inl (Sum.inr (Sum.inr 0)))
      osCompFormula := saClassCompF (Sum.inl (Sum.inl (Sum.inl 0)))
        (Sum.inl (Sum.inl (Sum.inr (Sum.inl 0)))) (Sum.inl (Sum.inl (Sum.inr (Sum.inr 0))))
        (Sum.inl (Sum.inr (Sum.inl 0))) (Sum.inl (Sum.inr (Sum.inr (Sum.inl 0))))
        (Sum.inl (Sum.inr (Sum.inr (Sum.inr 0)))) }

/-- The three formulas of `saCatSpecies` satisfy the absoluteness proviso of page 68; the
object formula is a 0-species in the sense of Definition 3.1 (i). The formula of the
species-morphisms (isomorphism classes of functors) is not bounded by variables; its proviso
comes from `saAbsolute_of_powBounded`. -/
theorem saCatSpecies_absolute :
    IsZeroSpecies.{u} saCatSpecies.spZero ∧ SpeciesAbsolute.{u} saCatSpecies.spOne.osFormula ∧
      SpeciesAbsolute.{u} saCatSpecies.spOne.osCompFormula :=
  ⟨⟨by decide, speciesAbsolute_of_delta0 (saCatF_delta0 _ _)⟩,
    saAbsolute_of_powBounded (saIsoClassF_powBounded _ _ _ _ _),
    speciesAbsolute_of_delta0 (saClassCompF_delta0 _ _ _ _ _ _)⟩

/-- In every model of `IsSpeciesModel`, the species-objects of `saCatSpecies` are the pairs
`(A, C)` of sets of the model that form a small category (computed in `ZFSet`). -/
theorem saCat_zeroSpecimen_iff {D : Set ZFSet.{u}} (hD : IsSpeciesModel D)
    (E : Fin 2 → ZFSet.{u}) :
    zeroSpecimen D saCatSpecies.spZero E ↔ (∀ i, E i ∈ D) ∧ saIsCat (E 0) (E 1) := by
  unfold zeroSpecimen
  rw [saModel_holds_iff hD (saIsPowBounded_of_delta0 (saCatF_delta0 _ _)), saCatF_realizeU]
  exact Iff.rfl

/-- In every model of `IsSpeciesModel`, the species-morphisms `F : E → E'` of `saCatSpecies` are
the isomorphism classes of functors from `E` to `E'` (computed in `ZFSet`) that are sets of the
model; in particular, "isomorphic" and "closed under isomorphism" mean the same in every model,
although their quantifiers range over `P³(A ∪ A')`. -/
theorem saCat_oneSpecimen_iff {D : Set ZFSet.{u}} (hD : IsSpeciesModel D)
    (E E' : Fin 2 → ZFSet.{u}) (F : Fin 1 → ZFSet.{u}) :
    oneSpecimen D saCatSpecies E E' F ↔ zeroSpecimen D saCatSpecies.spZero E ∧
      zeroSpecimen D saCatSpecies.spZero E' ∧ F 0 ∈ D ∧
        saIsIsoClass (E 0) (E 1) (E' 0) (E' 1) (F 0) := by
  unfold oneSpecimen
  rw [saModel_holds_iff hD (saIsoClassF_powBounded _ _ _ _ _), saIsoClassF_realizeU]
  constructor
  · rintro ⟨hE, hE', hx, h⟩
    exact ⟨hE, hE', hx (Sum.inr (Sum.inr 0)), h⟩
  · rintro ⟨hE, hE', hF, h⟩
    refine ⟨hE, hE', ?_, h⟩
    rintro (a | a | a)
    · exact speciesHolds_mem hE a
    · exact speciesHolds_mem hE' a
    · rw [Subsingleton.elim a 0]; exact hF

/-! ## Definition 3.3 (ii): composites and inverses of morphisms of mutations -/

section MutationMorphisms

/-- Definition 3.3 (ii), page 73, the direction "if" of the characterization of isomorphisms of
mutations: if `ℨ' : 𝔐' → 𝔐` is a morphism of mutations whose composites with `ℨ` are, in every
model and at every species-object, identity species-morphisms, then `ℨ` is an isomorphism of
mutations. ("The composites are identities" is read model by model, through
`SpeciesIsIdentityAt`.) -/
theorem saIsMutationIso_of_inverse {S T : SpeciesData} {M M' : MutationData S T}
    {Z Z' : MutationMorphismData S T} (hZ : IsMutationMorphism.{u} M M' Z)
    (hZ' : IsMutationMorphism.{u} M' M Z')
    (hinv : ∀ D : Set ZFSet.{u}, IsSpeciesModel D → ∀ E A B G G', zeroSpecimen D S.spZero E →
      mutationMorphismRel D M M' Z E A B G → mutationMorphismRel D M' M Z' E B A G' →
      (∃ H, speciesComposite D T A B A G G' H ∧ SpeciesIsIdentityAt D T A H) ∧
        ∃ H', speciesComposite D T B A B G' G H' ∧ SpeciesIsIdentityAt D T B H') :
    IsMutationIso.{u} M M' Z := by
  refine ⟨hZ, fun D hD E A B G hE hG => ?_⟩
  obtain ⟨G', hG'⟩ := ((hZ'.2 D hD).1 E B A hE hG.2.1 hG.1).exists
  exact ⟨hG.2.2.1, G', hG'.2.2.1, hinv D hD E A B G G' hE hG hG'⟩

/-- Definition 3.3 (ii), page 73, the direction "only if", stated and not proved: an isomorphism
of mutations `ℨ : 𝔐 → 𝔐'` between mutations of species has an inverse morphism of mutations
`ℨ' : 𝔐' → 𝔐`, whose composites with `ℨ` are identities in every model. -/
def saMutationIsoInverseClaim : Prop :=
  ∀ (S T : SpeciesData) (M M' : MutationData S T) (Z : MutationMorphismData S T),
    IsSpecies.{u} S → IsSpecies.{u} T → IsMutation.{u} M → IsMutation.{u} M' →
    IsMutationIso.{u} M M' Z → ∃ Z' : MutationMorphismData S T, IsMutationMorphism.{u} M' M Z' ∧
      ∀ D : Set ZFSet.{u}, IsSpeciesModel D → ∀ E A B G G', zeroSpecimen D S.spZero E →
        mutationMorphismRel D M M' Z E A B G → mutationMorphismRel D M' M Z' E B A G' →
        (∃ H, speciesComposite D T A B A G G' H ∧ SpeciesIsIdentityAt D T A H) ∧
          ∃ H', speciesComposite D T B A B G' G H' ∧ SpeciesIsIdentityAt D T B H'

/-- The composite of morphisms of mutations (one of the "evident notions" of page 73), stated
and not proved: for morphisms `ℨ : 𝔐 → 𝔐'` and `ℨ' : 𝔐' → 𝔐''` of mutations between species
there is a morphism of mutations `𝔐 → 𝔐''` whose value at every species-object `E`, in every
model, is the composite `ℨ'(E) ∘ ℨ(E)`. -/
def saMutationMorphismCompClaim : Prop :=
  ∀ (S T : SpeciesData) (M M' M'' : MutationData S T) (Z Z' : MutationMorphismData S T),
    IsSpecies.{u} S → IsSpecies.{u} T → IsMutation.{u} M → IsMutation.{u} M' →
    IsMutation.{u} M'' → IsMutationMorphism.{u} M M' Z → IsMutationMorphism.{u} M' M'' Z' →
    ∃ Z'' : MutationMorphismData S T, IsMutationMorphism.{u} M M'' Z'' ∧
      ∀ D : Set ZFSet.{u}, IsSpeciesModel D → ∀ E A B C G G' H, zeroSpecimen D S.spZero E →
        mutationMorphismRel D M M' Z E A B G → mutationMorphismRel D M' M'' Z' E B C G' →
        (mutationMorphismRel D M M'' Z'' E A C H ↔ speciesComposite D T A B C G G' H)

end MutationMorphisms

end IUT.PaperIV.SpeciesAbsoluteness
