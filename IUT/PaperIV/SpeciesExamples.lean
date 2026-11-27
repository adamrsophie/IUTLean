import Mathlib
import IUT.PaperIV.Species

/-!
# Examples of species and mutations (IUT IV, Section 3)

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Section 3: Definition 3.1
(pages 68 to 70), Example 3.2 and Remark 3.2.1 (page 72), Definition 3.3 (i) to (iii)
(pages 72 and 73) and Example 3.4 (pages 76 and 77). Pages read for this file: 68 to 73, 76
and 77. Pages checked against rendered images: 68, 69, 70, 71, 72, 73, 76 and 77.

This file builds on `IUT.PaperIV.Species` (the definitions of species, mutations and their
morphisms). It does **not** formalize Example 3.2 or Example 3.4 of the paper: those examples
(small categories with isomorphism classes of functors; topological spaces, universal
coverings, groups with outer homomorphisms, the fundamental group as a mutation) are not
reached. What it contains is a library of bounded set-theoretic formulas, a family of species
built with it (sets satisfying a bounded formula, with all maps), a mutation between two
distinct such species, and three general facts about species and mutations.

## Formalized and proved

* A library of bounded formulas of `speciesLang` (`IsSpeciesDelta0`, so that
  `speciesAbsolute_of_delta0` gives the proviso of page 68 for each of them): `sxMemF`
  (`a ∈ b`), `sxEqF` (`a = b`), `sxBex` (bounded `∃`), `sxSglF` (`z = {a}`), `sxDblF`
  (`z = {a, b}`), `sxKPairF` (`z` is the Kuratowski pair `(a, b)` of Mathlib's `ZFSet.pair`),
  `sxAppF` (`(a, b)` lies in the graph `f`), `sxFuncF` (`f` is a function from `x` to `y` in the
  sense of Mathlib's `ZFSet.IsFunc`), `sxCompF` (the composition condition; for functions it
  says `h` is the graph of `g ∘ f`, `sx_eq_graphComp_iff`) and `sxIdF` (the identity condition,
  `sx_eq_idGraph_iff`). Each has a correctness lemma in the model `ZFSet.{u}`
  (`sx…_realizeU`) and a boundedness lemma (`sx…_delta0`); `sxHolds_iff` transfers truth from
  any transitive domain to `ZFSet.{u}`.
* Closure of Grothendieck universes under unordered pairs (from axiom (v) of page 67, with a
  surjection from `{∅, {∅}}`), binary unions, products and subsets (`sxUniv_*`), and hence of
  every model of `IsSpeciesModel` under the graphs used here (`sxModel_*`).
* `sxSetSpecies φ`, for a formula `φ` in one variable: species-objects are the sets satisfying
  `φ`, species-morphisms the graphs of functions, composites the graphs of composite functions.
  For bounded `φ` it is a species in the sense of Definition 3.1 (iii)
  (`sxSetSpecies_isSpecies`), it is 1-small (`sxSetSpecies_isOneSmall`), and its identity
  species-morphisms are exactly the graphs of identity functions (`sxSet_isIdentityAt_iff`).
  The species of sets `sxSets` (`φ = ⊤`) is a species and is not 0-small
  (`sxSets_not_isZeroSmall`); in every model it has a species-object with two distinct
  species-morphisms to itself (`sxSets_two_morphisms`). This tests the morphism formula on more
  than one morphism, which the one-object species of `IUT.PaperIV.Species` could not.
* The inclusion mutation `sxInclusion φ ψ` (`Ψ₀` and `Ψ₁` are equalities) is a mutation
  whenever every `φ`-set is a `ψ`-set (`sxInclusion_isMutation`). For the species of nonempty
  sets and the species of sets it is a mutation between two distinct species
  (`sxNonemptyInclusion_isMutation`), it misses the species-object `∅`
  (`sxNonemptyInclusion_not_surjective`), and it is evaluated on two distinct
  species-morphisms with two distinct values (`sxNonemptyInclusion_two_morphisms`).
* Definition 3.1 (iii), page 69, "one verifies immediately that composites of
  species-isomorphisms are species-isomorphisms": `sxIsIsoAt_composite`, in every model in
  which conditions (c), (d), (e) hold, through `sxIsIsoAt_iff_isIso` (a species-isomorphism is
  an isomorphism of the category of Definition 3.1 (iv)).
* Composite of mutations, model by model: if two formula collections satisfy conditions (a) and
  (b) of Definition 3.3 (i) in a model, so does their composite `mutationAfter`
  (`sxAfter_axiomsAt`), with the meaning of the composite morphism formula
  (`sxAfter_mor_holds`).

## Not proved, with the obstacle

* Example 3.2 (page 72). The only example printed there is that of small categories, with
  isomorphism classes of functors as species-morphisms. A small category can be written with
  bounded formulas (a set of arrows and a set of composition triples), but "the functors `φ`,
  `ψ` are isomorphic" quantifies over natural isomorphisms, which are subsets of
  `Ob × Ar'`, and "`F` contains every functor isomorphic to one of its members" quantifies over
  all functors: both quantifiers are bounded only by a power set, not by a set variable, so the
  formulas are not in `IsSpeciesDelta0` and `speciesAbsolute_of_delta0` does not apply. The
  missing step is an absoluteness theorem for formulas with quantifiers bounded by power sets
  (true between universes `V ∈ W`, since both are transitive and closed under power sets, so
  `P(x)` is computed alike), followed by conditions (c) to (e) for the encodings. The claim of
  page 72 that species-isomorphisms correspond to isomorphism classes of equivalences of
  categories is not addressed.
* Example 3.4 (pages 76 and 77). (i) Topological spaces: closure of a topology under arbitrary
  unions quantifies over subsets of the topology, again a power-set bound; universal coverings
  and deck transformations are not in the formula library. (ii) Groups with outer
  homomorphisms: the group laws, homomorphisms, and "any two members of `F` differ by an inner
  automorphism" are expressible with bounded quantifiers, but the encoding of a group (a set
  and the graph of its multiplication) and the proofs of (c) to (e) for classes of
  homomorphisms are not written. (iii) The fundamental group mutation needs (i) and (ii).
* That the composite of two mutations is a mutation. `sxAfter_axiomsAt` gives (a) and (b) in
  each model; the absoluteness proviso for the formulas of `mutationAfter` is open. In the
  direction from the larger universe `W` to `V`, the witness `B` of `∃ B, Φ₀(B) ∧ Ψ₀(E, B) ∧ …`
  must be shown to lie in `V`; uniqueness (a) of the first mutation gives this when `E` is a
  species-object, but `SpeciesAbsolute` quantifies over all assignments, and the formula of
  `mutationAfter` does not require `Φ₀(E)`. A composite formula with the conjunct `Φ₀(E)` added
  would remove this case; that is a change to `IUT.PaperIV.Species`, not made here. The
  morphism formula of `mutationAfter` likewise does not require `Φ₀(E)`, `Φ₀(E')`,
  `Φ₁(E, E', F)`. The composite with these conditions added is `saMutationComp` of
  `IUT.PaperIV.SpeciesAbsoluteness`, and it is a mutation between species
  (`saMutationComp_isMutation`).
* That an isomorphism of mutations is one with an inverse morphism of mutations
  (Definition 3.3 (ii)): composition and identity morphisms of mutations are not defined in
  `IUT.PaperIV.Species`, and a formula for the inverse would quantify over identity
  species-morphisms (an unbounded quantifier), so its absoluteness is again open.

## Reading choices, recorded

* The species of sets and the species of nonempty sets are not printed in the paper; they are
  test cases of Definitions 3.1 and 3.3 chosen here. Example 3.2 lists only categories, and
  groups appear in Example 3.4 (ii).
* The composition formula `Φ₁∘₁` of `sxSetSpecies` is the condition
  `∀ a ∈ E₁, ∀ b ∈ E'₁, ∀ c ∈ E''₁, (a, b) ∈ F₁ → (b, c) ∈ F'₁ → (a, c) ∈ F''₁`; together with
  the conditions that `F₁`, `F'₁`, `F''₁` are functions (part of the definition of a composite),
  it says that `F''₁` is the graph of the composite function.

-/

universe u

namespace IUT.PaperIV.SpeciesExamples

open IUT.Foundations IUT.PaperIV.Species

/-! ## Variables under bounded quantifiers -/

section Library

variable {α : Type*} {n : ℕ}

/-- The model of set theory with domain all of `ZFSet.{u}`. -/
abbrev sxUniv : Set ZFSet.{u} := Set.univ

/-- A free or bound variable, seen one bounded quantifier deeper. -/
def sxLift (r : α ⊕ Fin n) : α ⊕ Fin (n + 1) := Sum.map id Fin.castSucc r

/-- The variable bound by the innermost quantifier. -/
def sxTop : α ⊕ Fin (n + 1) := Sum.inr (Fin.last n)

/-- The set assigned to a variable by the assignments `v` (free variables) and `xs` (bound
variables). -/
def sxEnv {D : Set ZFSet.{u}} (v : α → D) (xs : Fin n → D) (r : α ⊕ Fin n) : ZFSet.{u} :=
  (Sum.elim v xs r).1

@[simp] theorem sxEnv_lift {D : Set ZFSet.{u}} (v : α → D) (xs : Fin n → D) (y : D)
    (r : α ⊕ Fin n) : sxEnv v (Fin.snoc xs y) (sxLift r) = sxEnv v xs r := by
  rcases r with a | i
  · rfl
  · simp [sxEnv, sxLift, Fin.snoc_castSucc]

@[simp] theorem sxEnv_top {D : Set ZFSet.{u}} (v : α → D) (xs : Fin n → D) (y : D) :
    sxEnv v (Fin.snoc xs y) sxTop = y.1 := by
  simp [sxEnv, sxTop]

@[simp] theorem sxEnv_inl {D : Set ZFSet.{u}} (v : α → D) (xs : Fin n → D) (a : α) :
    sxEnv v xs (Sum.inl a) = (v a).1 := rfl

/-! ## The formula library -/

/-- The atomic formula `a ∈ b`. -/
def sxMemF (a b : α ⊕ Fin n) : speciesLang.BoundedFormula α n :=
  speciesMemF (FirstOrder.Language.Term.var a) (FirstOrder.Language.Term.var b)

/-- The atomic formula `a = b`. -/
def sxEqF (a b : α ⊕ Fin n) : speciesLang.BoundedFormula α n :=
  FirstOrder.Language.Term.bdEqual (FirstOrder.Language.Term.var a)
    (FirstOrder.Language.Term.var b)

/-- The bounded existential quantifier `∃ x ∈ w, φ`, written as `¬ ∀ x ∈ w, ¬ φ`. -/
def sxBex (w : α ⊕ Fin n) (φ : speciesLang.BoundedFormula α (n + 1)) :
    speciesLang.BoundedFormula α n :=
  (speciesBall w φ.not).not

/-- `z = {a}`: `a ∈ z ∧ ∀ y ∈ z, y = a`. -/
def sxSglF (z a : α ⊕ Fin n) : speciesLang.BoundedFormula α n :=
  sxMemF a z ⊓ speciesBall z (sxEqF sxTop (sxLift a))

/-- `z = {a, b}`: `a ∈ z ∧ b ∈ z ∧ ∀ y ∈ z, y = a ∨ y = b`. -/
def sxDblF (z a b : α ⊕ Fin n) : speciesLang.BoundedFormula α n :=
  sxMemF a z ⊓ sxMemF b z ⊓ speciesBall z (sxEqF sxTop (sxLift a) ⊔ sxEqF sxTop (sxLift b))

/-- `z` is the Kuratowski pair `(a, b) = {{a}, {a, b}}`:
`∃ s ∈ z, ∃ t ∈ z, s = {a} ∧ t = {a, b} ∧ ∀ y ∈ z, y = s ∨ y = t`. -/
def sxKPairF (z a b : α ⊕ Fin n) : speciesLang.BoundedFormula α n :=
  sxBex z (sxBex (sxLift z)
    (sxSglF (sxLift sxTop) (sxLift (sxLift a)) ⊓
      sxDblF sxTop (sxLift (sxLift a)) (sxLift (sxLift b))
      ⊓ speciesBall (sxLift (sxLift z))
        (sxEqF sxTop (sxLift (sxLift sxTop)) ⊔ sxEqF sxTop (sxLift sxTop))))

/-- The graph `f` contains the pair `(a, b)` ("`f(a) = b`"): `∃ p ∈ f, p = (a, b)`. -/
def sxAppF (f a b : α ⊕ Fin n) : speciesLang.BoundedFormula α n :=
  sxBex f (sxKPairF sxTop (sxLift a) (sxLift b))

/-- `f` is a function from `x` to `y`: every element of `f` is a pair `(a, b)` with `a ∈ x`,
`b ∈ y`; every `a ∈ x` has some `b ∈ y` with `(a, b) ∈ f`; and that `b` is unique. -/
def sxFuncF (x y f : α ⊕ Fin n) : speciesLang.BoundedFormula α n :=
  speciesBall f (sxBex (sxLift x) (sxBex (sxLift (sxLift y))
      (sxKPairF (sxLift (sxLift sxTop)) (sxLift sxTop) sxTop))) ⊓
    speciesBall x (sxBex (sxLift y) (sxAppF (sxLift (sxLift f)) (sxLift sxTop) sxTop)) ⊓
    speciesBall x (speciesBall (sxLift y) (speciesBall (sxLift (sxLift y))
      ((sxAppF (sxLift (sxLift (sxLift f))) (sxLift (sxLift sxTop)) (sxLift sxTop)).imp
        ((sxAppF (sxLift (sxLift (sxLift f))) (sxLift (sxLift sxTop)) sxTop).imp
          (sxEqF (sxLift sxTop) sxTop)))))

/-- The composition condition for graphs `f ⊆ x × y`, `g ⊆ y × z`, `h ⊆ x × z`:
`∀ a ∈ x, ∀ b ∈ y, ∀ c ∈ z, (a, b) ∈ f → (b, c) ∈ g → (a, c) ∈ h`. For functions it says that
`h` is the composite `g ∘ f` (`sx_eq_graphComp_iff`). -/
def sxCompF (x y z f g h : α ⊕ Fin n) : speciesLang.BoundedFormula α n :=
  speciesBall x (speciesBall (sxLift y) (speciesBall (sxLift (sxLift z))
    ((sxAppF (sxLift (sxLift (sxLift f))) (sxLift (sxLift sxTop)) (sxLift sxTop)).imp
      ((sxAppF (sxLift (sxLift (sxLift g))) (sxLift sxTop) sxTop).imp
        (sxAppF (sxLift (sxLift (sxLift h))) (sxLift (sxLift sxTop)) sxTop)))))

/-- The identity condition `∀ a ∈ x, (a, a) ∈ h`. For a function `h` from `x` to `x` it says
that `h` is the identity function of `x` (`sx_eq_idGraph_iff`). -/
def sxIdF (x h : α ⊕ Fin n) : speciesLang.BoundedFormula α n :=
  speciesBall x (sxAppF (sxLift h) sxTop sxTop)

/-! ### Boundedness -/

theorem sxMemF_delta0 (a b : α ⊕ Fin n) : IsSpeciesDelta0 (sxMemF a b) :=
  IsSpeciesDelta0.rel _ _

theorem sxEqF_delta0 (a b : α ⊕ Fin n) : IsSpeciesDelta0 (sxEqF a b) :=
  IsSpeciesDelta0.equal _ _

theorem sxNot_delta0 {φ : speciesLang.BoundedFormula α n} (h : IsSpeciesDelta0 φ) :
    IsSpeciesDelta0 φ.not :=
  h.imp IsSpeciesDelta0.falsum

theorem sxInf_delta0 {φ ψ : speciesLang.BoundedFormula α n} (h₁ : IsSpeciesDelta0 φ)
    (h₂ : IsSpeciesDelta0 ψ) : IsSpeciesDelta0 (φ ⊓ ψ) :=
  (h₁.imp (h₂.imp IsSpeciesDelta0.falsum)).imp IsSpeciesDelta0.falsum

theorem sxSup_delta0 {φ ψ : speciesLang.BoundedFormula α n} (h₁ : IsSpeciesDelta0 φ)
    (h₂ : IsSpeciesDelta0 ψ) : IsSpeciesDelta0 (φ ⊔ ψ) :=
  (h₁.imp IsSpeciesDelta0.falsum).imp h₂

theorem sxTop_delta0 : IsSpeciesDelta0 (⊤ : speciesLang.BoundedFormula α n) :=
  IsSpeciesDelta0.imp IsSpeciesDelta0.falsum IsSpeciesDelta0.falsum

theorem sxBex_delta0 (w : α ⊕ Fin n) {φ : speciesLang.BoundedFormula α (n + 1)}
    (h : IsSpeciesDelta0 φ) : IsSpeciesDelta0 (sxBex w φ) :=
  sxNot_delta0 (IsSpeciesDelta0.ball w (sxNot_delta0 h))

theorem sxSglF_delta0 (z a : α ⊕ Fin n) : IsSpeciesDelta0 (sxSglF z a) :=
  sxInf_delta0 (sxMemF_delta0 _ _) (IsSpeciesDelta0.ball _ (sxEqF_delta0 _ _))

theorem sxDblF_delta0 (z a b : α ⊕ Fin n) : IsSpeciesDelta0 (sxDblF z a b) :=
  sxInf_delta0 (sxInf_delta0 (sxMemF_delta0 _ _) (sxMemF_delta0 _ _))
    (IsSpeciesDelta0.ball _ (sxSup_delta0 (sxEqF_delta0 _ _) (sxEqF_delta0 _ _)))

theorem sxKPairF_delta0 (z a b : α ⊕ Fin n) : IsSpeciesDelta0 (sxKPairF z a b) :=
  sxBex_delta0 _ (sxBex_delta0 _ (sxInf_delta0 (sxInf_delta0 (sxSglF_delta0 _ _)
    (sxDblF_delta0 _ _ _)) (IsSpeciesDelta0.ball _
      (sxSup_delta0 (sxEqF_delta0 _ _) (sxEqF_delta0 _ _)))))

theorem sxAppF_delta0 (f a b : α ⊕ Fin n) : IsSpeciesDelta0 (sxAppF f a b) :=
  sxBex_delta0 _ (sxKPairF_delta0 _ _ _)

theorem sxFuncF_delta0 (x y f : α ⊕ Fin n) : IsSpeciesDelta0 (sxFuncF x y f) :=
  sxInf_delta0 (sxInf_delta0
    (IsSpeciesDelta0.ball _ (sxBex_delta0 _ (sxBex_delta0 _ (sxKPairF_delta0 _ _ _))))
    (IsSpeciesDelta0.ball _ (sxBex_delta0 _ (sxAppF_delta0 _ _ _))))
    (IsSpeciesDelta0.ball _ (IsSpeciesDelta0.ball _ (IsSpeciesDelta0.ball _
      ((sxAppF_delta0 _ _ _).imp ((sxAppF_delta0 _ _ _).imp (sxEqF_delta0 _ _))))))

theorem sxCompF_delta0 (x y z f g h : α ⊕ Fin n) : IsSpeciesDelta0 (sxCompF x y z f g h) :=
  IsSpeciesDelta0.ball _ (IsSpeciesDelta0.ball _ (IsSpeciesDelta0.ball _
    ((sxAppF_delta0 _ _ _).imp ((sxAppF_delta0 _ _ _).imp (sxAppF_delta0 _ _ _)))))

theorem sxIdF_delta0 (x h : α ⊕ Fin n) : IsSpeciesDelta0 (sxIdF x h) :=
  IsSpeciesDelta0.ball _ (sxAppF_delta0 _ _ _)

/-! ### Connectives -/

section Connectives

variable {D : Set ZFSet.{u}} (v : α → D) (xs : Fin n → D)

theorem sxRealize_not (φ : speciesLang.BoundedFormula α n) :
    speciesRealizeAt D φ.not v xs ↔ ¬ speciesRealizeAt D φ v xs := by
  let _ := speciesStructure D
  exact FirstOrder.Language.BoundedFormula.realize_not

theorem sxRealize_inf (φ ψ : speciesLang.BoundedFormula α n) :
    speciesRealizeAt D (φ ⊓ ψ) v xs ↔ speciesRealizeAt D φ v xs ∧ speciesRealizeAt D ψ v xs := by
  let _ := speciesStructure D
  exact FirstOrder.Language.BoundedFormula.realize_inf

theorem sxRealize_sup (φ ψ : speciesLang.BoundedFormula α n) :
    speciesRealizeAt D (φ ⊔ ψ) v xs ↔ speciesRealizeAt D φ v xs ∨ speciesRealizeAt D ψ v xs := by
  let _ := speciesStructure D
  exact FirstOrder.Language.BoundedFormula.realize_sup

theorem sxRealize_imp (φ ψ : speciesLang.BoundedFormula α n) :
    speciesRealizeAt D (φ.imp ψ) v xs ↔
      (speciesRealizeAt D φ v xs → speciesRealizeAt D ψ v xs) := by
  let _ := speciesStructure D
  exact FirstOrder.Language.BoundedFormula.realize_imp

theorem sxRealize_top : speciesRealizeAt D (⊤ : speciesLang.BoundedFormula α n) v xs := by
  let _ := speciesStructure D
  exact FirstOrder.Language.BoundedFormula.realize_top.2 trivial

theorem sxMemF_realize (a b : α ⊕ Fin n) :
    speciesRealizeAt D (sxMemF a b) v xs ↔ sxEnv v xs a ∈ sxEnv v xs b :=
  Iff.rfl

theorem sxEqF_realize (a b : α ⊕ Fin n) :
    speciesRealizeAt D (sxEqF a b) v xs ↔ sxEnv v xs a = sxEnv v xs b :=
  Subtype.ext_iff

end Connectives

/-! ### Realization in the model `ZFSet.{u}` -/

section Univ

variable (v : α → sxUniv.{u}) (xs : Fin n → sxUniv.{u})

theorem sxBall_realizeU (w : α ⊕ Fin n) (φ : speciesLang.BoundedFormula α (n + 1)) :
    speciesRealizeAt sxUniv (speciesBall w φ) v xs ↔
      ∀ a : ZFSet.{u}, a ∈ sxEnv v xs w →
        speciesRealizeAt sxUniv φ v (Fin.snoc xs ⟨a, Set.mem_univ a⟩) := by
  rw [speciesBall_realize]
  exact ⟨fun h a ha => h ⟨a, Set.mem_univ a⟩ ha, fun h x hx => h x.1 hx⟩

theorem sxBex_realizeU (w : α ⊕ Fin n) (φ : speciesLang.BoundedFormula α (n + 1)) :
    speciesRealizeAt sxUniv (sxBex w φ) v xs ↔
      ∃ a : ZFSet.{u}, a ∈ sxEnv v xs w ∧
        speciesRealizeAt sxUniv φ v (Fin.snoc xs ⟨a, Set.mem_univ a⟩) := by
  unfold sxBex
  rw [sxRealize_not, sxBall_realizeU]
  simp only [sxRealize_not, not_forall, not_not, exists_prop]

theorem sx_eq_singleton_iff (z a : ZFSet.{u}) : z = {a} ↔ a ∈ z ∧ ∀ y, y ∈ z → y = a := by
  constructor
  · rintro rfl
    exact ⟨ZFSet.mem_singleton.2 rfl, fun y hy => ZFSet.mem_singleton.1 hy⟩
  · rintro ⟨ha, h⟩
    apply ZFSet.ext
    intro y
    rw [ZFSet.mem_singleton]
    exact ⟨h y, fun e => e ▸ ha⟩

theorem sx_eq_pairSet_iff (z a b : ZFSet.{u}) :
    z = {a, b} ↔ (a ∈ z ∧ b ∈ z) ∧ ∀ y, y ∈ z → y = a ∨ y = b := by
  constructor
  · rintro rfl
    exact ⟨⟨ZFSet.mem_pair.2 (Or.inl rfl), ZFSet.mem_pair.2 (Or.inr rfl)⟩,
      fun y hy => ZFSet.mem_pair.1 hy⟩
  · rintro ⟨⟨ha, hb⟩, h⟩
    apply ZFSet.ext
    intro y
    rw [ZFSet.mem_pair]
    exact ⟨h y, fun e => e.elim (fun e => e ▸ ha) (fun e => e ▸ hb)⟩

theorem sx_eq_kpair_iff (z a b : ZFSet.{u}) :
    z = ZFSet.pair a b ↔ ∃ s, s ∈ z ∧ ∃ t, t ∈ z ∧ (s = {a} ∧ t = {a, b}) ∧
      ∀ y, y ∈ z → y = s ∨ y = t := by
  constructor
  · rintro rfl
    exact ⟨{a}, ZFSet.mem_pair.2 (Or.inl rfl), {a, b}, ZFSet.mem_pair.2 (Or.inr rfl),
      ⟨rfl, rfl⟩, fun y hy => ZFSet.mem_pair.1 hy⟩
  · rintro ⟨s, hs, t, ht, ⟨rfl, rfl⟩, h⟩
    apply ZFSet.ext
    intro y
    show y ∈ z ↔ y ∈ ({{a}, {a, b}} : ZFSet.{u})
    rw [ZFSet.mem_pair]
    exact ⟨h y, fun e => e.elim (fun e => e ▸ hs) (fun e => e ▸ ht)⟩

@[simp] theorem sxSglF_realizeU (z a : α ⊕ Fin n) :
    speciesRealizeAt sxUniv (sxSglF z a) v xs ↔ sxEnv v xs z = {sxEnv v xs a} := by
  rw [sx_eq_singleton_iff]
  simp only [sxSglF, sxRealize_inf, sxMemF_realize, sxBall_realizeU, sxEqF_realize, sxEnv_lift,
    sxEnv_top]

@[simp] theorem sxDblF_realizeU (z a b : α ⊕ Fin n) :
    speciesRealizeAt sxUniv (sxDblF z a b) v xs ↔
      sxEnv v xs z = {sxEnv v xs a, sxEnv v xs b} := by
  rw [sx_eq_pairSet_iff]
  simp only [sxDblF, sxRealize_inf, sxRealize_sup, sxMemF_realize, sxBall_realizeU,
    sxEqF_realize, sxEnv_lift, sxEnv_top]

@[simp] theorem sxKPairF_realizeU (z a b : α ⊕ Fin n) :
    speciesRealizeAt sxUniv (sxKPairF z a b) v xs ↔
      sxEnv v xs z = ZFSet.pair (sxEnv v xs a) (sxEnv v xs b) := by
  rw [sx_eq_kpair_iff]
  simp only [sxKPairF, sxBex_realizeU, sxRealize_inf, sxRealize_sup, sxSglF_realizeU,
    sxDblF_realizeU, sxBall_realizeU, sxEqF_realize, sxEnv_lift, sxEnv_top]

@[simp] theorem sxAppF_realizeU (f a b : α ⊕ Fin n) :
    speciesRealizeAt sxUniv (sxAppF f a b) v xs ↔
      ZFSet.pair (sxEnv v xs a) (sxEnv v xs b) ∈ sxEnv v xs f := by
  simp only [sxAppF, sxBex_realizeU, sxKPairF_realizeU, sxEnv_lift, sxEnv_top]
  exact ⟨fun ⟨p, hp, e⟩ => e ▸ hp, fun h => ⟨_, h, rfl⟩⟩

theorem sx_isFunc_iff (x y f : ZFSet.{u}) :
    (((∀ p, p ∈ f → ∃ a, a ∈ x ∧ ∃ b, b ∈ y ∧ p = ZFSet.pair a b) ∧
      ∀ a, a ∈ x → ∃ b, b ∈ y ∧ ZFSet.pair a b ∈ f) ∧
      ∀ a, a ∈ x → ∀ b, b ∈ y → ∀ c, c ∈ y → ZFSet.pair a b ∈ f → ZFSet.pair a c ∈ f → b = c) ↔
      ZFSet.IsFunc x y f := by
  constructor
  · rintro ⟨⟨hA, hB⟩, hC⟩
    refine ⟨fun p hp => ?_, fun a ha => ?_⟩
    · obtain ⟨a, ha, b, hb, rfl⟩ := hA p hp
      exact ZFSet.pair_mem_prod.2 ⟨ha, hb⟩
    · obtain ⟨b, hb, hab⟩ := hB a ha
      refine ⟨b, hab, fun c hc => ?_⟩
      obtain ⟨a', -, c', hc', he⟩ := hA _ hc
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 he
      exact (hC _ ha b hb _ hc' hab hc).symm
  · rintro ⟨hsub, hu⟩
    refine ⟨⟨fun p hp => ?_, fun a ha => ?_⟩, ?_⟩
    · obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.1 (hsub hp)
      exact ⟨a, ha, b, hb, rfl⟩
    · obtain ⟨b, hb, -⟩ := hu a ha
      exact ⟨b, (ZFSet.pair_mem_prod.1 (hsub hb)).2, hb⟩
    · intro a ha b _ c _ hb hc
      exact (hu a ha).unique hb hc

@[simp] theorem sxFuncF_realizeU (x y f : α ⊕ Fin n) :
    speciesRealizeAt sxUniv (sxFuncF x y f) v xs ↔
      ZFSet.IsFunc (sxEnv v xs x) (sxEnv v xs y) (sxEnv v xs f) := by
  rw [← sx_isFunc_iff]
  simp only [sxFuncF, sxRealize_inf, sxRealize_imp, sxBall_realizeU, sxBex_realizeU,
    sxKPairF_realizeU, sxAppF_realizeU, sxEqF_realize, sxEnv_lift, sxEnv_top]

@[simp] theorem sxCompF_realizeU (x y z f g h : α ⊕ Fin n) :
    speciesRealizeAt sxUniv (sxCompF x y z f g h) v xs ↔
      ∀ a, a ∈ sxEnv v xs x → ∀ b, b ∈ sxEnv v xs y → ∀ c, c ∈ sxEnv v xs z →
        ZFSet.pair a b ∈ sxEnv v xs f → ZFSet.pair b c ∈ sxEnv v xs g →
          ZFSet.pair a c ∈ sxEnv v xs h := by
  simp only [sxCompF, sxRealize_imp, sxBall_realizeU, sxAppF_realizeU, sxEnv_lift, sxEnv_top]

@[simp] theorem sxIdF_realizeU (x h : α ⊕ Fin n) :
    speciesRealizeAt sxUniv (sxIdF x h) v xs ↔
      ∀ a, a ∈ sxEnv v xs x → ZFSet.pair a a ∈ sxEnv v xs h := by
  simp only [sxIdF, sxBall_realizeU, sxAppF_realizeU, sxEnv_lift, sxEnv_top]

end Univ

/-- Transfer to `ZFSet.{u}`: in a transitive domain `D`, a formula with bounded quantifiers
holds at an assignment of sets of `D` exactly when it holds in the model `ZFSet.{u}`. -/
theorem sxHolds_iff {β : Type*} {D : Set ZFSet.{u}} (htr : ∀ x ∈ D, ∀ y ∈ x, y ∈ D)
    {φ : speciesLang.Formula β} (hφ : IsSpeciesDelta0 φ) (x : β → ZFSet.{u}) :
    speciesHolds D φ x ↔ (∀ b, x b ∈ D) ∧
      speciesRealizeAt sxUniv φ (fun b => ⟨x b, Set.mem_univ _⟩) default := by
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    have := (speciesDelta0_realize_iff (Set.subset_univ D) htr (fun b => ⟨x b, hx b⟩) hφ
      default).1 h
    rwa [Subsingleton.elim (Set.inclusion (Set.subset_univ D) ∘ default) default] at this
  · rintro ⟨hx, h⟩
    refine ⟨hx, (speciesDelta0_realize_iff (Set.subset_univ D) htr (fun b => ⟨x b, hx b⟩) hφ
      default).2 ?_⟩
    rwa [Subsingleton.elim (Set.inclusion (Set.subset_univ D) ∘ default) default]

end Library

/-! ## Graphs of functions -/

section Graphs

/-- The graph of the composite `g ∘ f` of `f : x → y` and `g : y → z`. -/
def sxGraphComp (x y z f g : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pairSep (fun a c => ∃ b, b ∈ y ∧ ZFSet.pair a b ∈ f ∧ ZFSet.pair b c ∈ g) x z

/-- The graph of the identity function of `x`. -/
def sxIdGraph (x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pairSep (fun a b => a = b) x x

variable {x y z w f g h : ZFSet.{u}}

theorem sx_mem_graphComp {p : ZFSet.{u}} :
    p ∈ sxGraphComp x y z f g ↔ ∃ a ∈ x, ∃ c ∈ z, p = ZFSet.pair a c ∧
      ∃ b, b ∈ y ∧ ZFSet.pair a b ∈ f ∧ ZFSet.pair b c ∈ g :=
  ZFSet.mem_pairSep

theorem sx_mem_idGraph {p : ZFSet.{u}} :
    p ∈ sxIdGraph x ↔ ∃ a ∈ x, ∃ b ∈ x, p = ZFSet.pair a b ∧ a = b :=
  ZFSet.mem_pairSep

theorem sx_pair_mem_idGraph {a b : ZFSet.{u}} : ZFSet.pair a b ∈ sxIdGraph x ↔ a ∈ x ∧ a = b := by
  rw [sx_mem_idGraph]
  constructor
  · rintro ⟨a', ha', b', -, he, e⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 he
    exact ⟨ha', e⟩
  · rintro ⟨ha, rfl⟩
    exact ⟨a, ha, a, ha, rfl, rfl⟩

theorem sx_isFunc_graphComp (hf : ZFSet.IsFunc x y f) (hg : ZFSet.IsFunc y z g) :
    ZFSet.IsFunc x z (sxGraphComp x y z f g) := by
  refine ⟨fun p hp => ?_, fun a ha => ?_⟩
  · obtain ⟨a, ha, c, hc, rfl, -⟩ := sx_mem_graphComp.1 hp
    exact ZFSet.pair_mem_prod.2 ⟨ha, hc⟩
  · obtain ⟨b, hab, hbu⟩ := hf.2 a ha
    have hb : b ∈ y := (ZFSet.pair_mem_prod.1 (hf.1 hab)).2
    obtain ⟨c, hbc, hcu⟩ := hg.2 b hb
    have hc : c ∈ z := (ZFSet.pair_mem_prod.1 (hg.1 hbc)).2
    refine ⟨c, sx_mem_graphComp.2 ⟨a, ha, c, hc, rfl, b, hb, hab, hbc⟩, fun c' hc' => ?_⟩
    obtain ⟨a', -, c'', -, he, b', -, hab', hbc'⟩ := sx_mem_graphComp.1 hc'
    obtain ⟨e₁, e₂⟩ := ZFSet.pair_inj.1 he
    rw [← e₁] at hab'
    rw [← e₂, hbu b' hab'] at hbc'
    exact hcu c' hbc'

theorem sx_isFunc_idGraph (x : ZFSet.{u}) : ZFSet.IsFunc x x (sxIdGraph x) := by
  refine ⟨fun p hp => ?_, fun a ha => ⟨a, sx_pair_mem_idGraph.2 ⟨ha, rfl⟩, fun c hc => ?_⟩⟩
  · obtain ⟨a, ha, b, hb, rfl, -⟩ := sx_mem_idGraph.1 hp
    exact ZFSet.pair_mem_prod.2 ⟨ha, hb⟩
  · exact (sx_pair_mem_idGraph.1 hc).2.symm

/-- For functions `f : x → y`, `g : y → z`, `h : x → z`, the composition condition of
`sxCompF` holds exactly when `h` is the graph of `g ∘ f`. -/
theorem sx_eq_graphComp_iff (hf : ZFSet.IsFunc x y f) (hg : ZFSet.IsFunc y z g)
    (hh : ZFSet.IsFunc x z h) :
    (∀ a, a ∈ x → ∀ b, b ∈ y → ∀ c, c ∈ z → ZFSet.pair a b ∈ f → ZFSet.pair b c ∈ g →
      ZFSet.pair a c ∈ h) ↔ h = sxGraphComp x y z f g := by
  constructor
  · intro H
    apply ZFSet.ext
    intro p
    rw [sx_mem_graphComp]
    constructor
    · intro hp
      obtain ⟨a, ha, c, hc, rfl⟩ := ZFSet.mem_prod.1 (hh.1 hp)
      obtain ⟨b, hab, -⟩ := hf.2 a ha
      have hb : b ∈ y := (ZFSet.pair_mem_prod.1 (hf.1 hab)).2
      obtain ⟨c', hbc', -⟩ := hg.2 b hb
      have hc' : c' ∈ z := (ZFSet.pair_mem_prod.1 (hg.1 hbc')).2
      have e : c = c' := (hh.2 a ha).unique hp (H a ha b hb c' hc' hab hbc')
      exact ⟨a, ha, c, hc, rfl, b, hb, hab, e ▸ hbc'⟩
    · rintro ⟨a, ha, c, hc, rfl, b, hb, hab, hbc⟩
      exact H a ha b hb c hc hab hbc
  · rintro rfl a ha b hb c hc hab hbc
    exact sx_mem_graphComp.2 ⟨a, ha, c, hc, rfl, b, hb, hab, hbc⟩

/-- For a function `h : x → x`, the identity condition of `sxIdF` holds exactly when `h` is the
graph of the identity of `x`. -/
theorem sx_eq_idGraph_iff (hh : ZFSet.IsFunc x x h) :
    (∀ a, a ∈ x → ZFSet.pair a a ∈ h) ↔ h = sxIdGraph x := by
  constructor
  · intro H
    apply ZFSet.ext
    intro p
    rw [sx_mem_idGraph]
    constructor
    · intro hp
      obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.1 (hh.1 hp)
      exact ⟨a, ha, b, hb, rfl, (hh.2 a ha).unique (H a ha) hp⟩
    · rintro ⟨a, ha, b, -, rfl, rfl⟩
      exact H a ha
  · rintro rfl a ha
    exact sx_pair_mem_idGraph.2 ⟨ha, rfl⟩

theorem sx_graphComp_id_left (hf : ZFSet.IsFunc x y f) :
    sxGraphComp x x y (sxIdGraph x) f = f := by
  apply ZFSet.ext
  intro p
  rw [sx_mem_graphComp]
  constructor
  · rintro ⟨a, -, c, -, rfl, b, -, hab, hbc⟩
    rw [(sx_pair_mem_idGraph.1 hab).2]
    exact hbc
  · intro hp
    obtain ⟨a, ha, c, hc, rfl⟩ := ZFSet.mem_prod.1 (hf.1 hp)
    exact ⟨a, ha, c, hc, rfl, a, ha, sx_pair_mem_idGraph.2 ⟨ha, rfl⟩, hp⟩

theorem sx_graphComp_id_right (hf : ZFSet.IsFunc x y f) :
    sxGraphComp x y y f (sxIdGraph y) = f := by
  apply ZFSet.ext
  intro p
  rw [sx_mem_graphComp]
  constructor
  · rintro ⟨a, -, c, -, rfl, b, -, hab, hbc⟩
    rw [← (sx_pair_mem_idGraph.1 hbc).2]
    exact hab
  · intro hp
    obtain ⟨a, ha, c, hc, rfl⟩ := ZFSet.mem_prod.1 (hf.1 hp)
    exact ⟨a, ha, c, hc, rfl, c, hc, hp, sx_pair_mem_idGraph.2 ⟨hc, rfl⟩⟩

theorem sx_graphComp_assoc :
    sxGraphComp x z w (sxGraphComp x y z f g) h = sxGraphComp x y w f (sxGraphComp y z w g h) := by
  apply ZFSet.ext
  intro p
  rw [sx_mem_graphComp, sx_mem_graphComp]
  constructor
  · rintro ⟨a, ha, d, hd, rfl, c, hc, hac, hcd⟩
    obtain ⟨a', -, c', -, he, b, hb, hab, hbc⟩ := sx_mem_graphComp.1 hac
    obtain ⟨e₁, e₂⟩ := ZFSet.pair_inj.1 he
    rw [← e₁] at hab
    rw [← e₂] at hbc
    exact ⟨a, ha, d, hd, rfl, b, hb, hab, sx_mem_graphComp.2 ⟨b, hb, d, hd, rfl, c, hc, hbc, hcd⟩⟩
  · rintro ⟨a, ha, d, hd, rfl, b, hb, hab, hbd⟩
    obtain ⟨b', -, d', -, he, c, hc, hbc, hcd⟩ := sx_mem_graphComp.1 hbd
    obtain ⟨e₁, e₂⟩ := ZFSet.pair_inj.1 he
    rw [← e₁] at hbc
    rw [← e₂] at hcd
    exact ⟨a, ha, d, hd, rfl, c, hc, sx_mem_graphComp.2 ⟨a, ha, c, hc, rfl, b, hb, hab, hbc⟩, hcd⟩

end Graphs

/-! ## Closure of the models under the constructions used -/

section Closure

/-- The set `{∅, {∅}}`, written as the power set of the power set of `∅`. -/
def sxTwo : ZFSet.{u} := ZFSet.powerset (ZFSet.powerset ∅)

theorem sx_empty_mem_two : (∅ : ZFSet.{u}) ∈ sxTwo :=
  ZFSet.mem_powerset.2 (ZFSet.empty_subset _)

theorem sx_single_mem_two : ({∅} : ZFSet.{u}) ∈ sxTwo := by
  refine ZFSet.mem_powerset.2 fun y hy => ?_
  rw [ZFSet.mem_singleton.1 hy]
  exact ZFSet.mem_powerset.2 (ZFSet.empty_subset _)

theorem sx_empty_ne_single : (∅ : ZFSet.{u}) ≠ {∅} := by
  intro h
  have : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := ZFSet.mem_singleton.2 rfl
  rw [← h] at this
  exact ZFSet.notMem_empty _ this

theorem sx_mem_two {w : ZFSet.{u}} (hw : w ∈ sxTwo) : w = ∅ ∨ w = {∅} := by
  have hel : ∀ y ∈ w, y = ∅ := fun y hy =>
    (ZFSet.eq_empty y).2 fun z hz =>
      ZFSet.notMem_empty z (ZFSet.mem_powerset.1 (ZFSet.mem_powerset.1 hw hy) hz)
  by_cases h : (∅ : ZFSet.{u}) ∈ w
  · right
    apply ZFSet.ext
    intro y
    rw [ZFSet.mem_singleton]
    exact ⟨hel y, fun e => e ▸ h⟩
  · left
    exact (ZFSet.eq_empty w).2 fun y hy => h (hel y hy ▸ hy)

variable {V : ZFSet.{u}}

theorem sxUniv_empty_mem (hV : IsGrothendieckUniverse V) : (∅ : ZFSet.{u}) ∈ V :=
  hV.transitive _ hV.omega_mem _ ZFSet.omega_zero

theorem sxUniv_two_mem (hV : IsGrothendieckUniverse V) : (sxTwo : ZFSet.{u}) ∈ V :=
  hV.powerset_mem _ (hV.powerset_mem _ (sxUniv_empty_mem hV))

/-- A universe contains `{a, b}` for all its elements `a`, `b` (by axiom (v) of page 67, with a
surjection from `{∅, {∅}}`). -/
theorem sxUniv_pairSet_mem (hV : IsGrothendieckUniverse V) {a b : ZFSet.{u}} (ha : a ∈ V)
    (hb : b ∈ V) : ({a, b} : ZFSet.{u}) ∈ V := by
  refine hV.mem_of_surjection sxTwo (sxUniv_two_mem hV) {a, b}
    (ZFSet.subset_def.2 fun y hy => ?_) {ZFSet.pair ∅ a, ZFSet.pair {∅} b}
    ⟨⟨ZFSet.subset_def.2 fun p hp => ?_, fun w hw => ?_⟩, fun c hc => ?_⟩
  · rcases ZFSet.mem_pair.1 hy with rfl | rfl
    · exact ha
    · exact hb
  · rcases ZFSet.mem_pair.1 hp with rfl | rfl
    · exact ZFSet.pair_mem_prod.2 ⟨sx_empty_mem_two, ZFSet.mem_pair.2 (Or.inl rfl)⟩
    · exact ZFSet.pair_mem_prod.2 ⟨sx_single_mem_two, ZFSet.mem_pair.2 (Or.inr rfl)⟩
  · rcases sx_mem_two hw with rfl | rfl
    · refine ⟨a, ZFSet.mem_pair.2 (Or.inl rfl), fun c hc => ?_⟩
      rcases ZFSet.mem_pair.1 hc with e | e
      · exact (ZFSet.pair_inj.1 e).2
      · exact absurd (ZFSet.pair_inj.1 e).1 sx_empty_ne_single
    · refine ⟨b, ZFSet.mem_pair.2 (Or.inr rfl), fun c hc => ?_⟩
      rcases ZFSet.mem_pair.1 hc with e | e
      · exact absurd (ZFSet.pair_inj.1 e).1.symm sx_empty_ne_single
      · exact (ZFSet.pair_inj.1 e).2
  · rcases ZFSet.mem_pair.1 hc with rfl | rfl
    · exact ⟨∅, sx_empty_mem_two, ZFSet.mem_pair.2 (Or.inl rfl)⟩
    · exact ⟨{∅}, sx_single_mem_two, ZFSet.mem_pair.2 (Or.inr rfl)⟩

theorem sxUniv_subset_mem (hV : IsGrothendieckUniverse V) {s t : ZFSet.{u}} (ht : t ∈ V)
    (hs : s ⊆ t) : s ∈ V :=
  hV.transitive _ (hV.powerset_mem _ ht) _ (ZFSet.mem_powerset.2 hs)

theorem sxUniv_prod_mem (hV : IsGrothendieckUniverse V) {x y : ZFSet.{u}} (hx : x ∈ V)
    (hy : y ∈ V) : ZFSet.prod x y ∈ V := by
  have hu : x ∪ y ∈ V := ZFSet.sUnion_pair x y ▸ hV.sUnion_mem _ (sxUniv_pairSet_mem hV hx hy)
  refine sxUniv_subset_mem hV (hV.powerset_mem _ (hV.powerset_mem _ hu)) ?_
  unfold ZFSet.prod ZFSet.pairSep
  exact ZFSet.sep_subset

variable {D : Set ZFSet.{u}}

/-- In a model of `IsSpeciesModel`, a subset of `x × y` with `x`, `y` in the model is in the
model. -/
theorem sxModel_mem_of_subset_prod (hD : IsSpeciesModel D) {x y s : ZFSet.{u}} (hx : x ∈ D)
    (hy : y ∈ D) (hs : s ⊆ ZFSet.prod x y) : s ∈ D := by
  rcases hD with rfl | ⟨V, hV, rfl⟩
  · exact Set.mem_univ _
  · exact sxUniv_subset_mem hV (sxUniv_prod_mem hV hx hy) hs

theorem sxModel_funs_mem (hD : IsSpeciesModel D) {x y : ZFSet.{u}} (hx : x ∈ D) (hy : y ∈ D) :
    ZFSet.funs x y ∈ D := by
  rcases hD with rfl | ⟨V, hV, rfl⟩
  · exact Set.mem_univ _
  · exact sxUniv_subset_mem hV (hV.powerset_mem _ (sxUniv_prod_mem hV hx hy)) ZFSet.sep_subset

theorem sxModel_two_mem (hD : IsSpeciesModel D) : (sxTwo : ZFSet.{u}) ∈ D := by
  rcases hD with rfl | ⟨V, hV, rfl⟩
  · exact Set.mem_univ _
  · exact sxUniv_two_mem hV

end Closure

/-! ## The species of sets satisfying a bounded formula, with all maps -/

/-- The species whose species-objects are the sets `E₁` satisfying the formula `φ`, whose
species-morphisms `F : E → E'` are the graphs `F₁` of functions `E₁ → E'₁` (`sxFuncF`), and in
which `F''` is a composite of `F` with `F'` when `sxCompF` holds. For `φ = ⊤` this is the species
of sets and maps. -/
abbrev sxSetSpecies (φ : speciesLang.Formula (Fin 1)) : SpeciesData where
  spZero := { zsArity := 1, zsFormula := φ }
  spOne :=
    { osArity := 1
      osFormula := sxFuncF (Sum.inl (Sum.inl 0)) (Sum.inl (Sum.inr (Sum.inl 0)))
        (Sum.inl (Sum.inr (Sum.inr 0)))
      osCompFormula := sxCompF (Sum.inl (Sum.inl (Sum.inl 0)))
        (Sum.inl (Sum.inl (Sum.inr (Sum.inl 0)))) (Sum.inl (Sum.inl (Sum.inr (Sum.inr 0))))
        (Sum.inl (Sum.inr (Sum.inl 0))) (Sum.inl (Sum.inr (Sum.inr (Sum.inl 0))))
        (Sum.inl (Sum.inr (Sum.inr (Sum.inr 0)))) }

theorem sxFin1_ext (F G : Fin 1 → ZFSet.{u}) (h : F 0 = G 0) : F = G :=
  funext fun i => by rw [Subsingleton.elim i 0]; exact h

section SetSpecies

variable {D : Set ZFSet.{u}} {φ : speciesLang.Formula (Fin 1)}

theorem sxSet_oneSpecimen_iff (htr : ∀ x ∈ D, ∀ y ∈ x, y ∈ D) (E E' F : Fin 1 → ZFSet.{u}) :
    oneSpecimen D (sxSetSpecies φ) E E' F ↔
      zeroSpecimen D (sxSetSpecies φ).spZero E ∧ zeroSpecimen D (sxSetSpecies φ).spZero E' ∧
        F 0 ∈ D ∧ ZFSet.IsFunc (E 0) (E' 0) (F 0) := by
  have key := sxHolds_iff htr (sxFuncF_delta0 (Sum.inl (Sum.inl (0 : Fin 1)))
    (Sum.inl (Sum.inr (Sum.inl (0 : Fin 1)))) (Sum.inl (Sum.inr (Sum.inr (0 : Fin 1)))))
    (Sum.elim E (Sum.elim E' F))
  rw [sxFuncF_realizeU] at key
  unfold oneSpecimen
  rw [key]
  constructor
  · rintro ⟨hE, hE', hx, h⟩
    exact ⟨hE, hE', hx (Sum.inr (Sum.inr 0)), h⟩
  · rintro ⟨hE, hE', hF, h⟩
    refine ⟨hE, hE', ?_, h⟩
    rintro (a | a | a) <;> rw [Subsingleton.elim a 0]
    exacts [speciesHolds_mem hE 0, speciesHolds_mem hE' 0, hF]

theorem sxSet_composite_iff (htr : ∀ x ∈ D, ∀ y ∈ x, y ∈ D)
    (E E' E'' F F' F'' : Fin 1 → ZFSet.{u}) :
    speciesComposite D (sxSetSpecies φ) E E' E'' F F' F'' ↔
      oneSpecimen D (sxSetSpecies φ) E E' F ∧ oneSpecimen D (sxSetSpecies φ) E' E'' F' ∧
        oneSpecimen D (sxSetSpecies φ) E E'' F'' ∧
          F'' 0 = sxGraphComp (E 0) (E' 0) (E'' 0) (F 0) (F' 0) := by
  have key := sxHolds_iff htr (sxCompF_delta0 (Sum.inl (Sum.inl (Sum.inl (0 : Fin 1))))
    (Sum.inl (Sum.inl (Sum.inr (Sum.inl (0 : Fin 1)))))
    (Sum.inl (Sum.inl (Sum.inr (Sum.inr (0 : Fin 1)))))
    (Sum.inl (Sum.inr (Sum.inl (0 : Fin 1)))) (Sum.inl (Sum.inr (Sum.inr (Sum.inl (0 : Fin 1)))))
    (Sum.inl (Sum.inr (Sum.inr (Sum.inr (0 : Fin 1))))))
    (Sum.elim (Sum.elim E (Sum.elim E' E'')) (Sum.elim F (Sum.elim F' F'')))
  rw [sxCompF_realizeU] at key
  unfold speciesComposite
  rw [key]
  constructor
  · rintro ⟨h₁, h₂, h₃, -, H⟩
    have f₁ := ((sxSet_oneSpecimen_iff htr _ _ _).1 h₁).2.2.2
    have f₂ := ((sxSet_oneSpecimen_iff htr _ _ _).1 h₂).2.2.2
    have f₃ := ((sxSet_oneSpecimen_iff htr _ _ _).1 h₃).2.2.2
    exact ⟨h₁, h₂, h₃, (sx_eq_graphComp_iff f₁ f₂ f₃).1 H⟩
  · rintro ⟨h₁, h₂, h₃, H⟩
    have g₁ := (sxSet_oneSpecimen_iff htr _ _ _).1 h₁
    have g₂ := (sxSet_oneSpecimen_iff htr _ _ _).1 h₂
    have g₃ := (sxSet_oneSpecimen_iff htr _ _ _).1 h₃
    refine ⟨h₁, h₂, h₃, ?_, (sx_eq_graphComp_iff g₁.2.2.2 g₂.2.2.2 g₃.2.2.2).2 H⟩
    rintro ((a | a | a) | (a | a | a)) <;> rw [Subsingleton.elim a 0]
    exacts [speciesHolds_mem g₁.1 0, speciesHolds_mem g₁.2.1 0, speciesHolds_mem g₂.2.1 0,
      g₁.2.2.1, g₂.2.2.1, g₃.2.2.1]

theorem sxSet_idSpecimen (hD : IsSpeciesModel D) {E : Fin 1 → ZFSet.{u}}
    (hE : zeroSpecimen D (sxSetSpecies φ).spZero E) :
    oneSpecimen D (sxSetSpecies φ) E E (fun _ => sxIdGraph (E 0)) := by
  have hE0 : E 0 ∈ D := speciesHolds_mem hE 0
  exact (sxSet_oneSpecimen_iff (isSpeciesModel_transitive hD) _ _ _).2 ⟨hE, hE,
    sxModel_mem_of_subset_prod hD hE0 hE0 (sx_isFunc_idGraph _).1, sx_isFunc_idGraph _⟩

theorem sxSet_isIdentityAt_id (hD : IsSpeciesModel D) {E : Fin 1 → ZFSet.{u}}
    (hE : zeroSpecimen D (sxSetSpecies φ).spZero E) :
    SpeciesIsIdentityAt D (sxSetSpecies φ) E (fun _ => sxIdGraph (E 0)) := by
  have htr := isSpeciesModel_transitive hD
  have hI := sxSet_idSpecimen hD hE
  refine ⟨hI, fun E' F' hF' => ?_, fun E'' F'' hF'' => ?_⟩
  · have f := ((sxSet_oneSpecimen_iff htr _ _ _).1 hF').2.2.2
    exact (sxSet_composite_iff htr _ _ _ _ _ _).2 ⟨hF', hI, hF', (sx_graphComp_id_right f).symm⟩
  · have f := ((sxSet_oneSpecimen_iff htr _ _ _).1 hF'').2.2.2
    exact (sxSet_composite_iff htr _ _ _ _ _ _).2 ⟨hI, hF'', hF'', (sx_graphComp_id_left f).symm⟩

/-- In every model of `IsSpeciesModel`, `sxSetSpecies φ` satisfies conditions (c), (d), (e) of
Definition 3.1 (ii): composites exist and are unique (the graph of the composite function),
composition is associative, and the graph of the identity function is an identity. -/
theorem sxSet_axiomsAt (hD : IsSpeciesModel D) : SpeciesAxiomsAt D (sxSetSpecies φ) := by
  have htr := isSpeciesModel_transitive hD
  refine ⟨?_, ?_, fun E hE => ⟨_, sxSet_isIdentityAt_id hD hE⟩⟩
  · intro E E' E'' F F' hF hF'
    have g₁ := (sxSet_oneSpecimen_iff htr _ _ _).1 hF
    have g₂ := (sxSet_oneSpecimen_iff htr _ _ _).1 hF'
    have hc := sx_isFunc_graphComp g₁.2.2.2 g₂.2.2.2
    have h₃ : oneSpecimen D (sxSetSpecies φ) E E''
        (fun _ => sxGraphComp (E 0) (E' 0) (E'' 0) (F 0) (F' 0)) :=
      (sxSet_oneSpecimen_iff htr _ _ _).2 ⟨g₁.1, g₂.2.1, sxModel_mem_of_subset_prod hD
        (speciesHolds_mem g₁.1 0) (speciesHolds_mem g₂.2.1 0) hc.1, hc⟩
    refine ⟨_, (sxSet_composite_iff htr _ _ _ _ _ _).2 ⟨hF, hF', h₃, rfl⟩, fun G hG => ?_⟩
    exact sxFin1_ext _ _ ((sxSet_composite_iff htr _ _ _ _ _ _).1 hG).2.2.2
  · intro E₁ E₂ E₃ E₄ F₁ F₂ F₃ G H G' H' h₁ h₂ h₃ h₄
    refine sxFin1_ext _ _ ?_
    rw [((sxSet_composite_iff htr _ _ _ _ _ _).1 h₂).2.2.2,
      ((sxSet_composite_iff htr _ _ _ _ _ _).1 h₄).2.2.2,
      ((sxSet_composite_iff htr _ _ _ _ _ _).1 h₁).2.2.2,
      ((sxSet_composite_iff htr _ _ _ _ _ _).1 h₃).2.2.2]
    exact sx_graphComp_assoc

/-- The identity species-morphisms of `sxSetSpecies φ` are exactly the graphs of identity
functions. -/
theorem sxSet_isIdentityAt_iff (hD : IsSpeciesModel D) (E I : Fin 1 → ZFSet.{u}) :
    SpeciesIsIdentityAt D (sxSetSpecies φ) E I ↔
      zeroSpecimen D (sxSetSpecies φ).spZero E ∧ I = fun _ => sxIdGraph (E 0) := by
  constructor
  · intro h
    have hE := ((sxSet_oneSpecimen_iff (isSpeciesModel_transitive hD) _ _ _).1 h.1).1
    exact ⟨hE, speciesIdentity_unique (sxSet_axiomsAt hD).1 h (sxSet_isIdentityAt_id hD hE)⟩
  · rintro ⟨hE, rfl⟩
    exact sxSet_isIdentityAt_id hD hE

/-- `sxSetSpecies φ` is a species (Definition 3.1 (iii)) whenever `φ` has bounded quantifiers:
its three formulas satisfy the proviso of page 68 and conditions (c), (d), (e) hold in every
model of `IsSpeciesModel`. -/
theorem sxSetSpecies_isSpecies (hφ : IsSpeciesDelta0 φ) : IsSpecies.{u} (sxSetSpecies φ) :=
  ⟨⟨le_rfl, speciesAbsolute_of_delta0 hφ⟩, le_rfl,
    speciesAbsolute_of_delta0 (sxFuncF_delta0 _ _ _),
    speciesAbsolute_of_delta0 (sxCompF_delta0 _ _ _ _ _ _), fun _ hD => sxSet_axiomsAt hD⟩

/-- `sxSetSpecies φ` is 1-small: the species-morphisms `E → E'` are coded by the elements of the
set `funs E₁ E'₁` of the model. -/
theorem sxSetSpecies_isOneSmall : IsOneSmall.{u} (sxSetSpecies φ) := by
  intro D hD E E' hE hE'
  have htr := isSpeciesModel_transitive hD
  refine ⟨ZFSet.funs (E 0) (E' 0), sxModel_funs_mem hD (speciesHolds_mem hE 0)
    (speciesHolds_mem hE' 0), fun F hF => ?_⟩
  rw [sxSet_oneSpecimen_iff htr]
  show _ ↔ F 0 ∈ ZFSet.funs (E 0) (E' 0)
  rw [ZFSet.mem_funs]
  exact ⟨fun h => h.2.2.2, fun h => ⟨hE, hE', hF 0, h⟩⟩

end SetSpecies

/-! ## The species of sets and maps -/

/-- The species of all sets and all maps between them (`Φ₀ = ⊤`). -/
abbrev sxSets : SpeciesData := sxSetSpecies ⊤

theorem sxSets_isSpecies : IsSpecies.{u} sxSets :=
  sxSetSpecies_isSpecies sxTop_delta0

/-- The species of sets is not 0-small: in the model `ZFSet.{u}`, a set containing (the code of)
every species-object would contain itself. -/
theorem sxSets_not_isZeroSmall : ¬ IsZeroSmall.{u} sxSets.spZero := by
  intro h
  obtain ⟨s, -, hs⟩ := h Set.univ isSpeciesModel_univ
  have hmem : speciesTupleCode 1 (fun _ => s) ∈ s :=
    (hs (fun _ => s) (fun _ => Set.mem_univ _)).1 ((speciesHolds_top _).2 fun _ => Set.mem_univ _)
  exact ZFSet.mem_irrefl s hmem

/-- The constant map from `x` to `x` with value `∅`. -/
def sxConstGraph (x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pairSep (fun _ b => b = ∅) x x

theorem sx_isFunc_constGraph {x : ZFSet.{u}} (h0 : (∅ : ZFSet.{u}) ∈ x) :
    ZFSet.IsFunc x x (sxConstGraph x) := by
  refine ⟨fun p hp => ?_, fun a ha => ⟨∅, ZFSet.mem_pairSep.2 ⟨a, ha, ∅, h0, rfl, rfl⟩,
    fun c hc => ?_⟩⟩
  · obtain ⟨a, ha, b, hb, rfl, -⟩ := ZFSet.mem_pairSep.1 hp
    exact ZFSet.pair_mem_prod.2 ⟨ha, hb⟩
  · obtain ⟨a', -, b', -, he, e⟩ := ZFSet.mem_pairSep.1 hc
    rw [(ZFSet.pair_inj.1 he).2, e]

/-- Non-degeneracy: in every model of `IsSpeciesModel`, if the set `{∅, {∅}}` is a
species-object of `sxSetSpecies φ`, it has two distinct species-morphisms to itself (the
identity and the constant map with value `∅`). -/
theorem sxSet_two_morphisms {D : Set ZFSet.{u}} {φ : speciesLang.Formula (Fin 1)}
    (hD : IsSpeciesModel D) (hφ : zeroSpecimen D (sxSetSpecies φ).spZero fun _ => sxTwo) :
    ∃ F G : Fin 1 → ZFSet.{u}, oneSpecimen D (sxSetSpecies φ) (fun _ => sxTwo) (fun _ => sxTwo) F ∧
      oneSpecimen D (sxSetSpecies φ) (fun _ => sxTwo) (fun _ => sxTwo) G ∧ F ≠ G := by
  have htr := isSpeciesModel_transitive hD
  have h2 := sxModel_two_mem hD
  have hc := sx_isFunc_constGraph (sx_empty_mem_two : (∅ : ZFSet.{u}) ∈ sxTwo)
  refine ⟨fun _ => sxIdGraph sxTwo, fun _ => sxConstGraph sxTwo, sxSet_idSpecimen hD hφ,
    (sxSet_oneSpecimen_iff htr _ _ _).2 ⟨hφ, hφ, sxModel_mem_of_subset_prod hD h2 h2 hc.1, hc⟩,
    fun e => ?_⟩
  have hid : ZFSet.pair {∅} {∅} ∈ sxIdGraph (sxTwo : ZFSet.{u}) :=
    sx_pair_mem_idGraph.2 ⟨sx_single_mem_two, rfl⟩
  rw [congrFun e 0] at hid
  obtain ⟨a', -, b', -, he, hb⟩ := ZFSet.mem_pairSep.1 hid
  exact sx_empty_ne_single ((ZFSet.pair_inj.1 he).2.trans hb).symm

/-- In every model of `IsSpeciesModel`, the species of sets has a species-object with two
distinct species-morphisms to itself. -/
theorem sxSets_two_morphisms {D : Set ZFSet.{u}} (hD : IsSpeciesModel D) :
    ∃ E F G : Fin 1 → ZFSet.{u}, oneSpecimen D sxSets E E F ∧ oneSpecimen D sxSets E E G ∧
      F ≠ G := by
  obtain ⟨F, G, h⟩ := sxSet_two_morphisms (φ := ⊤) hD
    ((speciesHolds_top _).2 fun _ => sxModel_two_mem hD)
  exact ⟨_, F, G, h⟩

/-! ## Nonempty sets and the inclusion mutation -/

/-- The formula `∃ y ∈ E₁, ⊤`: `E₁` is nonempty. -/
def sxNonemptyF : speciesLang.Formula (Fin 1) := sxBex (Sum.inl 0) ⊤

theorem sxNonemptyF_delta0 : IsSpeciesDelta0 sxNonemptyF :=
  sxBex_delta0 _ sxTop_delta0

/-- The species of nonempty sets and all maps between them. -/
abbrev sxNonemptySets : SpeciesData := sxSetSpecies sxNonemptyF

theorem sxNonemptySets_isSpecies : IsSpecies.{u} sxNonemptySets :=
  sxSetSpecies_isSpecies sxNonemptyF_delta0

theorem sxNonempty_zeroSpecimen_iff {D : Set ZFSet.{u}} (htr : ∀ x ∈ D, ∀ y ∈ x, y ∈ D)
    (E : Fin 1 → ZFSet.{u}) :
    zeroSpecimen D sxNonemptySets.spZero E ↔ E 0 ∈ D ∧ ∃ y, y ∈ E 0 := by
  unfold zeroSpecimen
  rw [sxHolds_iff htr sxNonemptyF_delta0]
  have key : speciesRealizeAt sxUniv sxNonemptyF (fun b => ⟨E b, Set.mem_univ _⟩) default ↔
      ∃ y, y ∈ E 0 := by
    unfold sxNonemptyF
    rw [sxBex_realizeU]
    exact ⟨fun ⟨y, hy, _⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy, sxRealize_top _ _⟩⟩
  rw [key]
  exact ⟨fun h => ⟨h.1 0, h.2⟩, fun h => ⟨fun a => by rw [Subsingleton.elim a 0]; exact h.1, h.2⟩⟩

/-- The inclusion mutation `sxSetSpecies φ ⇝ sxSetSpecies ψ`: `Ψ₀(E, E̲)` is `E₁ = E̲₁` and
`Ψ₁(E, E', F, F̲)` is `F₁ = F̲₁`. -/
def sxInclusion (φ ψ : speciesLang.Formula (Fin 1)) :
    MutationData (sxSetSpecies φ) (sxSetSpecies ψ) where
  mutObjFormula := sxEqF (Sum.inl (Sum.inl 0)) (Sum.inl (Sum.inr 0))
  mutMorFormula := sxEqF (Sum.inl (Sum.inr (Sum.inr (Sum.inl 0))))
    (Sum.inl (Sum.inr (Sum.inr (Sum.inr 0))))

section Inclusion

variable {D : Set ZFSet.{u}} {φ ψ : speciesLang.Formula (Fin 1)}

theorem sxInclusion_objRel_iff (htr : ∀ x ∈ D, ∀ y ∈ x, y ∈ D) (E A : Fin 1 → ZFSet.{u}) :
    mutationObjRel D (sxInclusion φ ψ) E A ↔ zeroSpecimen D (sxSetSpecies ψ).spZero A ∧ E = A := by
  unfold mutationObjRel
  have key := sxHolds_iff htr (sxEqF_delta0 (Sum.inl (Sum.inl (0 : Fin 1)))
    (Sum.inl (Sum.inr (0 : Fin 1)))) (Sum.elim E A)
  rw [sxEqF_realize] at key
  change zeroSpecimen D (sxSetSpecies ψ).spZero A ∧
    speciesHolds D (sxEqF (Sum.inl (Sum.inl (0 : Fin 1))) (Sum.inl (Sum.inr (0 : Fin 1))))
      (Sum.elim E A) ↔ _
  rw [key]
  constructor
  · rintro ⟨hA, -, e⟩
    exact ⟨hA, sxFin1_ext _ _ e⟩
  · rintro ⟨hA, rfl⟩
    exact ⟨hA, fun b => by rcases b with a | a <;> exact speciesHolds_mem hA a, rfl⟩

theorem sxInclusion_morRel_iff (htr : ∀ x ∈ D, ∀ y ∈ x, y ∈ D)
    (E E' F A A' G : Fin 1 → ZFSet.{u}) :
    mutationMorRel D (sxInclusion φ ψ) E E' F A A' G ↔
      E = A ∧ E' = A' ∧ F = G ∧ oneSpecimen D (sxSetSpecies ψ) A A' G := by
  unfold mutationMorRel
  have key := sxHolds_iff htr (sxEqF_delta0 (Sum.inl (Sum.inr (Sum.inr (Sum.inl (0 : Fin 1)))))
    (Sum.inl (Sum.inr (Sum.inr (Sum.inr (0 : Fin 1)))))) (Sum.elim E (Sum.elim E' (Sum.elim F G)))
  rw [sxEqF_realize] at key
  rw [sxInclusion_objRel_iff htr, sxInclusion_objRel_iff htr]
  change _ ∧ _ ∧ _ ∧ speciesHolds D (sxEqF (Sum.inl (Sum.inr (Sum.inr (Sum.inl (0 : Fin 1)))))
    (Sum.inl (Sum.inr (Sum.inr (Sum.inr (0 : Fin 1)))))) (Sum.elim E (Sum.elim E' (Sum.elim F G)))
    ↔ _
  rw [key]
  constructor
  · rintro ⟨⟨-, rfl⟩, ⟨-, rfl⟩, hG, -, e⟩
    exact ⟨rfl, rfl, sxFin1_ext _ _ e, hG⟩
  · rintro ⟨rfl, rfl, rfl, hG⟩
    have g := (sxSet_oneSpecimen_iff htr _ _ _).1 hG
    refine ⟨⟨g.1, rfl⟩, ⟨g.2.1, rfl⟩, hG, ?_, rfl⟩
    rintro (a | a | a | a) <;> rw [Subsingleton.elim a 0]
    exacts [speciesHolds_mem g.1 0, speciesHolds_mem g.2.1 0, g.2.2.1, g.2.2.1]

/-- If every species-object of `sxSetSpecies φ` is one of `sxSetSpecies ψ` (in every model), the
inclusion is a mutation (Definition 3.3 (i)). -/
theorem sxInclusion_isMutation
    (himp : ∀ D : Set ZFSet.{u}, IsSpeciesModel D → ∀ E : Fin 1 → ZFSet.{u},
      speciesHolds D φ E → speciesHolds D ψ E) :
    IsMutation.{u} (sxInclusion φ ψ) := by
  refine ⟨speciesAbsolute_of_delta0 (sxEqF_delta0 _ _), speciesAbsolute_of_delta0
    (sxEqF_delta0 _ _), fun D hD => ⟨?_, ?_, ?_, ?_⟩⟩
  all_goals have htr := isSpeciesModel_transitive hD
  · intro E hE
    refine ⟨E, (sxInclusion_objRel_iff htr E E).2 ⟨himp D hD E hE, rfl⟩, fun A hA => ?_⟩
    exact ((sxInclusion_objRel_iff htr E A).1 hA).2.symm
  · intro E E' F A A' hF hA hA'
    obtain ⟨-, rfl⟩ := (sxInclusion_objRel_iff htr E A).1 hA
    obtain ⟨-, rfl⟩ := (sxInclusion_objRel_iff htr E' A').1 hA'
    have g := (sxSet_oneSpecimen_iff htr _ _ _).1 hF
    have hG : oneSpecimen D (sxSetSpecies ψ) E E' F :=
      (sxSet_oneSpecimen_iff htr _ _ _).2 ⟨himp D hD E g.1, himp D hD E' g.2.1, g.2.2⟩
    refine ⟨F, (sxInclusion_morRel_iff htr _ _ _ _ _ _).2 ⟨rfl, rfl, rfl, hG⟩, fun G hG' => ?_⟩
    exact ((sxInclusion_morRel_iff htr _ _ _ _ _ _).1 hG').2.2.1.symm
  · intro E E' E'' F F' F'' A A' A'' G G' G'' hc h₁ h₂ h₃
    obtain ⟨rfl, rfl, rfl, k₁⟩ := (sxInclusion_morRel_iff htr _ _ _ _ _ _).1 h₁
    obtain ⟨-, rfl, rfl, k₂⟩ := (sxInclusion_morRel_iff htr _ _ _ _ _ _).1 h₂
    obtain ⟨-, -, rfl, k₃⟩ := (sxInclusion_morRel_iff htr _ _ _ _ _ _).1 h₃
    exact (sxSet_composite_iff htr _ _ _ _ _ _).2
      ⟨k₁, k₂, k₃, ((sxSet_composite_iff htr _ _ _ _ _ _).1 hc).2.2.2⟩
  · intro E I A J hI h
    obtain ⟨rfl, -, rfl, k⟩ := (sxInclusion_morRel_iff htr _ _ _ _ _ _).1 h
    have hE := ((sxSet_oneSpecimen_iff htr _ _ _).1 k).1
    exact (sxSet_isIdentityAt_iff hD _ _).2 ⟨hE, ((sxSet_isIdentityAt_iff hD _ _).1 hI).2⟩

end Inclusion

/-- The inclusion of the species of nonempty sets into the species of sets is a mutation
between two distinct species. -/
theorem sxNonemptyInclusion_isMutation : IsMutation.{u} (sxInclusion sxNonemptyF ⊤) :=
  sxInclusion_isMutation fun _ _ _ h => (speciesHolds_top _).2 (speciesHolds_mem h)

/-- The inclusion mutation is not essentially surjective in any model: the species-object `∅` of
the species of sets is not the image of a species-object of the species of nonempty sets. -/
theorem sxNonemptyInclusion_not_surjective {D : Set ZFSet.{u}} (hD : IsSpeciesModel D) :
    ∃ A : Fin 1 → ZFSet.{u}, zeroSpecimen D sxSets.spZero A ∧
      ∀ E, zeroSpecimen D sxNonemptySets.spZero E →
        ¬ mutationObjRel D (sxInclusion sxNonemptyF ⊤) E A := by
  have htr := isSpeciesModel_transitive hD
  refine ⟨fun _ => ∅, (speciesHolds_top _).2 fun _ => isSpeciesModel_empty_mem hD,
    fun E hE hEA => ?_⟩
  obtain ⟨-, rfl⟩ := (sxInclusion_objRel_iff htr E _).1 hEA
  obtain ⟨-, y, hy⟩ := (sxNonempty_zeroSpecimen_iff htr _).1 hE
  exact ZFSet.notMem_empty y hy

/-- The inclusion mutation sends two distinct species-morphisms of the species of nonempty sets
to two distinct species-morphisms of the species of sets (in every model): `Ψ₁` is tested on more
than one morphism. -/
theorem sxNonemptyInclusion_two_morphisms {D : Set ZFSet.{u}} (hD : IsSpeciesModel D) :
    ∃ E F G A H₁ H₂ : Fin 1 → ZFSet.{u},
      mutationMorRel D (sxInclusion sxNonemptyF ⊤) E E F A A H₁ ∧
      mutationMorRel D (sxInclusion sxNonemptyF ⊤) E E G A A H₂ ∧ F ≠ G ∧ H₁ ≠ H₂ := by
  have htr := isSpeciesModel_transitive hD
  have hE : zeroSpecimen D sxNonemptySets.spZero fun _ => sxTwo :=
    (sxNonempty_zeroSpecimen_iff htr _).2 ⟨sxModel_two_mem hD, ∅, sx_empty_mem_two⟩
  obtain ⟨F, G, hF, hG, hne⟩ := sxSet_two_morphisms hD hE
  have hM := sxNonemptyInclusion_isMutation.{u}.2.2 D hD
  obtain ⟨H₁, k₁, -⟩ := hM.2.1 _ _ F _ _ hF
    ((sxInclusion_objRel_iff htr _ _).2 ⟨(speciesHolds_top _).2 (speciesHolds_mem hE), rfl⟩)
    ((sxInclusion_objRel_iff htr _ _).2 ⟨(speciesHolds_top _).2 (speciesHolds_mem hE), rfl⟩)
  obtain ⟨H₂, k₂, -⟩ := hM.2.1 _ _ G _ _ hG
    ((sxInclusion_objRel_iff htr _ _).2 ⟨(speciesHolds_top _).2 (speciesHolds_mem hE), rfl⟩)
    ((sxInclusion_objRel_iff htr _ _).2 ⟨(speciesHolds_top _).2 (speciesHolds_mem hE), rfl⟩)
  refine ⟨_, F, G, _, H₁, H₂, k₁, k₂, hne, fun e => hne ?_⟩
  rw [((sxInclusion_morRel_iff htr _ _ _ _ _ _).1 k₁).2.2.1,
    ((sxInclusion_morRel_iff htr _ _ _ _ _ _).1 k₂).2.2.1, e]

/-! ## Composites of species-isomorphisms (Definition 3.1 (iii)) -/

section Isomorphisms

variable {D : Set ZFSet.{u}} {S : SpeciesData}

/-- In a model satisfying (c), (d), (e), a species-morphism is a species-isomorphism exactly
when it is an isomorphism of the category determined by the species (Definition 3.1 (iv)). -/
theorem sxIsIsoAt_iff_isIso (h : SpeciesAxiomsAt D S) {X Y : SpeciesObjAt D S}
    (f : SpeciesHomAt D S X Y) :
    SpeciesIsIsoAt D S X.1 Y.1 f.1 ↔ @CategoryTheory.IsIso _ (speciesCategoryAt h) X Y f := by
  let _ := speciesCategoryAt h
  constructor
  · rintro ⟨-, G, hG, ⟨H, hH, hHid⟩, ⟨H', hH', hH'id⟩⟩
    let g : SpeciesHomAt D S Y X := ⟨G, hG⟩
    refine ⟨⟨g, Subtype.ext ?_, Subtype.ext ?_⟩⟩
    · show (speciesCompAt h f g).1 = speciesIdAt h X
      rw [speciesCompAt_eq h f g hH]
      exact speciesIdentity_unique h.1 hHid (speciesIdAt_spec h X)
    · show (speciesCompAt h g f).1 = speciesIdAt h Y
      rw [speciesCompAt_eq h g f hH']
      exact speciesIdentity_unique h.1 hH'id (speciesIdAt_spec h Y)
  · rintro ⟨⟨g, hfg, hgf⟩⟩
    have e₁ : (speciesCompAt h f g).1 = speciesIdAt h X := congrArg Subtype.val hfg
    have e₂ : (speciesCompAt h g f).1 = speciesIdAt h Y := congrArg Subtype.val hgf
    refine ⟨f.2, g.1, g.2, ⟨_, speciesCompAt_spec h f g, ?_⟩, ⟨_, speciesCompAt_spec h g f, ?_⟩⟩
    · rw [e₁]; exact speciesIdAt_spec h X
    · rw [e₂]; exact speciesIdAt_spec h Y

/-- Definition 3.1 (iii), page 69: "composites of species-isomorphisms are
species-isomorphisms", in any model where conditions (c), (d), (e) hold. -/
theorem sxIsIsoAt_composite (h : SpeciesAxiomsAt D S)
    {E E' E'' : Fin S.objArity → ZFSet.{u}} {F F' F'' : Fin S.morArity → ZFSet.{u}}
    (hF : SpeciesIsIsoAt D S E E' F) (hF' : SpeciesIsIsoAt D S E' E'' F')
    (hc : speciesComposite D S E E' E'' F F' F'') : SpeciesIsIsoAt D S E E'' F'' := by
  let X : SpeciesObjAt D S := ⟨E, hF.1.1⟩
  let Y : SpeciesObjAt D S := ⟨E', hF.1.2.1⟩
  let Z : SpeciesObjAt D S := ⟨E'', hF'.1.2.1⟩
  let f : SpeciesHomAt D S X Y := ⟨F, hF.1⟩
  let g : SpeciesHomAt D S Y Z := ⟨F', hF'.1⟩
  have hfg := (sxIsIsoAt_iff_isIso h (speciesCompAt h f g)).2
    (@CategoryTheory.IsIso.comp_isIso (SpeciesObjAt D S) (speciesCategoryAt h) X Y Z f g
      ((sxIsIsoAt_iff_isIso h f).1 hF) ((sxIsIsoAt_iff_isIso h g).1 hF'))
  rw [← speciesCompAt_eq h f g hc]
  exact hfg

end Isomorphisms

/-! ## Composites of mutations in a model (Definition 3.3 (i)) -/

section MutationComposite

variable {D : Set ZFSet.{u}} {S T U : SpeciesData}

theorem sxHolds_congr {β : Type*} {φ : speciesLang.Formula β} {x y : β → ZFSet.{u}}
    (h : speciesHolds D φ x) (e : x = y) : speciesHolds D φ y :=
  e ▸ h

/-- The morphism formula of a composite mutation means what the docstring of `mutationAfter`
says. -/
theorem sxAfter_mor_holds (N : MutationData T U) (M : MutationData S T)
    (E E' : Fin S.objArity → ZFSet.{u}) (F : Fin S.morArity → ZFSet.{u})
    (H : Fin U.morArity → ZFSet.{u}) (hx : ∀ a, Sum.elim E (Sum.elim E' (Sum.elim F H)) a ∈ D) :
    speciesHolds D (mutationAfter N M).mutMorFormula (Sum.elim E (Sum.elim E' (Sum.elim F H))) ↔
      ∃ B B' : Fin T.objArity → ZFSet.{u}, ∃ G : Fin T.morArity → ZFSet.{u},
        zeroSpecimen D T.spZero B ∧ zeroSpecimen D T.spZero B' ∧
        speciesHolds D T.spOne.osFormula (Sum.elim B (Sum.elim B' G)) ∧
        speciesHolds D M.mutObjFormula (Sum.elim E B) ∧
        speciesHolds D M.mutObjFormula (Sum.elim E' B') ∧
        speciesHolds D M.mutMorFormula (Sum.elim E (Sum.elim E' (Sum.elim F G))) ∧
        speciesHolds D N.mutMorFormula (Sum.elim B (Sum.elim B' (Sum.elim G H))) := by
  change speciesHolds D (FirstOrder.Language.Formula.iExs _ _) _ ↔ _
  rw [speciesHolds_iExs _ hx]
  constructor
  · rintro ⟨y, h⟩
    have hm := speciesHolds_mem h
    simp only [speciesHolds_inf, speciesHolds_relabel _ _ hm] at h
    obtain ⟨⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩, h₇⟩ := h
    refine ⟨y ∘ Sum.inl, y ∘ Sum.inr ∘ Sum.inl, y ∘ Sum.inr ∘ Sum.inr,
      sxHolds_congr h₁ rfl, sxHolds_congr h₂ rfl, sxHolds_congr h₃ ?_, sxHolds_congr h₄ ?_,
      sxHolds_congr h₅ ?_, sxHolds_congr h₆ ?_, sxHolds_congr h₇ ?_⟩
    all_goals funext c
    · rcases c with a | a | a <;> rfl
    · rcases c with a | a <;> rfl
    · rcases c with a | a <;> rfl
    · rcases c with a | a | a | a <;> rfl
    · rcases c with a | a | a | a <;> rfl
  · rintro ⟨B, B', G, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
    refine ⟨Sum.elim B (Sum.elim B' G), ?_⟩
    have hm : ∀ a, Sum.elim (Sum.elim E (Sum.elim E' (Sum.elim F H)))
        (Sum.elim B (Sum.elim B' G)) a ∈ D := by
      rintro (a | a | a | a)
      · exact hx a
      · exact speciesHolds_mem h₁ a
      · exact speciesHolds_mem h₂ a
      · exact speciesHolds_mem h₃ (Sum.inr (Sum.inr a))
    simp only [speciesHolds_inf, speciesHolds_relabel _ _ hm]
    refine ⟨⟨⟨⟨⟨⟨sxHolds_congr h₁ rfl, sxHolds_congr h₂ rfl⟩, sxHolds_congr h₃ ?_⟩,
      sxHolds_congr h₄ ?_⟩, sxHolds_congr h₅ ?_⟩, sxHolds_congr h₆ ?_⟩, sxHolds_congr h₇ ?_⟩
    all_goals funext c
    · rcases c with a | a | a <;> rfl
    · rcases c with a | a <;> rfl
    · rcases c with a | a <;> rfl
    · rcases c with a | a | a | a <;> rfl
    · rcases c with a | a | a | a <;> rfl

theorem sxAfter_objRel_iff (N : MutationData T U) (M : MutationData S T)
    (E : Fin S.objArity → ZFSet.{u}) (C : Fin U.objArity → ZFSet.{u}) (hE : ∀ i, E i ∈ D) :
    mutationObjRel D (mutationAfter N M) E C ↔
      ∃ B, mutationObjRel D M E B ∧ mutationObjRel D N B C := by
  unfold mutationObjRel
  constructor
  · rintro ⟨hC, h⟩
    obtain ⟨B, hB, h₁, h₂⟩ := (mutationAfter_obj_holds N M E C hE (speciesHolds_mem hC)).1 h
    exact ⟨B, ⟨hB, h₁⟩, hC, h₂⟩
  · rintro ⟨B, ⟨hB, h₁⟩, hC, h₂⟩
    exact ⟨hC, (mutationAfter_obj_holds N M E C hE (speciesHolds_mem hC)).2 ⟨B, hB, h₁, h₂⟩⟩

theorem sxAfter_morRel_of {N : MutationData T U} {M : MutationData S T}
    {E E' : Fin S.objArity → ZFSet.{u}} {F : Fin S.morArity → ZFSet.{u}}
    {B B' : Fin T.objArity → ZFSet.{u}} {G : Fin T.morArity → ZFSet.{u}}
    {A A' : Fin U.objArity → ZFSet.{u}} {H : Fin U.morArity → ZFSet.{u}}
    (hM : mutationMorRel D M E E' F B B' G) (hN : mutationMorRel D N B B' G A A' H) :
    mutationMorRel D (mutationAfter N M) E E' F A A' H := by
  have hE : ∀ i, E i ∈ D := fun i => speciesHolds_mem hM.1.2 (Sum.inl i)
  have hE' : ∀ i, E' i ∈ D := fun i => speciesHolds_mem hM.2.1.2 (Sum.inl i)
  refine ⟨(sxAfter_objRel_iff N M E A hE).2 ⟨B, hM.1, hN.1⟩,
    (sxAfter_objRel_iff N M E' A' hE').2 ⟨B', hM.2.1, hN.2.1⟩, hN.2.2.1, ?_⟩
  have hx : ∀ a, Sum.elim E (Sum.elim E' (Sum.elim F H)) a ∈ D := by
    rintro (a | a | a | a)
    · exact hE a
    · exact hE' a
    · exact speciesHolds_mem hM.2.2.2 (Sum.inr (Sum.inr (Sum.inl a)))
    · exact speciesHolds_mem hN.2.2.2 (Sum.inr (Sum.inr (Sum.inr a)))
  exact (sxAfter_mor_holds N M E E' F H hx).2 ⟨B, B', G, hM.1.1, hM.2.1.1, hM.2.2.1.2.2,
    hM.1.2, hM.2.1.2, hM.2.2.2, hN.2.2.2⟩

theorem sxAfter_morRel_dest {N : MutationData T U} {M : MutationData S T}
    (hMa : MutationObjUniqueAt D M) {E E' : Fin S.objArity → ZFSet.{u}}
    {F : Fin S.morArity → ZFSet.{u}} {A A' : Fin U.objArity → ZFSet.{u}}
    {H : Fin U.morArity → ZFSet.{u}} (hE : zeroSpecimen D S.spZero E)
    (hE' : zeroSpecimen D S.spZero E') (h : mutationMorRel D (mutationAfter N M) E E' F A A' H) :
    ∃ B B' G, mutationMorRel D M E E' F B B' G ∧ mutationMorRel D N B B' G A A' H := by
  obtain ⟨hA, hA', hH, hmor⟩ := h
  obtain ⟨B₀, hB₀, hB₀A⟩ := (sxAfter_objRel_iff N M E A (speciesHolds_mem hE)).1 hA
  obtain ⟨B₀', hB₀', hB₀A'⟩ := (sxAfter_objRel_iff N M E' A' (speciesHolds_mem hE')).1 hA'
  obtain ⟨B, B', G, k₁, k₂, k₃, k₄, k₅, k₆, k₇⟩ :=
    (sxAfter_mor_holds N M E E' F H (speciesHolds_mem hmor)).1 hmor
  have e₁ : B = B₀ := (hMa E hE).unique ⟨k₁, k₄⟩ hB₀
  have e₂ : B' = B₀' := (hMa E' hE').unique ⟨k₂, k₅⟩ hB₀'
  subst e₁ e₂
  exact ⟨B, B', G, ⟨hB₀, hB₀', ⟨k₁, k₂, k₃⟩, k₆⟩, ⟨hB₀A, hB₀A', hH, k₇⟩⟩

/-- In every model, the composite `𝔑 ∘ 𝔐` (`mutationAfter`) of two formula collections that
satisfy conditions (a) and (b) of Definition 3.3 (i) in that model satisfies them too. The
absoluteness proviso for the composite formulas is not proved (see the module docstring). -/
theorem sxAfter_axiomsAt {N : MutationData T U} {M : MutationData S T}
    (hM : MutationAxiomsAt D M) (hN : MutationAxiomsAt D N) :
    MutationAxiomsAt D (mutationAfter N M) := by
  obtain ⟨hMa, hMb, hMc, hMd⟩ := hM
  obtain ⟨hNa, hNb, hNc, hNd⟩ := hN
  refine ⟨fun E hE => ?_, fun E E' F A A' hF hA hA' => ?_, ?_, ?_⟩
  · obtain ⟨B, hB, hBu⟩ := hMa E hE
    obtain ⟨C, hC, hCu⟩ := hNa B hB.1
    have hEm : ∀ i, E i ∈ D := speciesHolds_mem hE
    refine ⟨C, (sxAfter_objRel_iff N M E C hEm).2 ⟨B, hB, hC⟩, fun C' hC' => ?_⟩
    obtain ⟨B', hB', hC''⟩ := (sxAfter_objRel_iff N M E C' hEm).1 hC'
    rw [hBu B' hB'] at hC''
    exact hCu C' hC''
  · obtain ⟨B, hB, hBA⟩ := (sxAfter_objRel_iff N M E A (speciesHolds_mem hF.1)).1 hA
    obtain ⟨B', hB', hBA'⟩ := (sxAfter_objRel_iff N M E' A' (speciesHolds_mem hF.2.1)).1 hA'
    obtain ⟨G, hG, hGu⟩ := hMb E E' F B B' hF hB hB'
    obtain ⟨H, hH, hHu⟩ := hNb B B' G A A' hG.2.2.1 hBA hBA'
    refine ⟨H, sxAfter_morRel_of hG hH, fun H' hH' => ?_⟩
    obtain ⟨B₁, B₁', G₁, k₁, k₂⟩ := sxAfter_morRel_dest hMa hF.1 hF.2.1 hH'
    have e₁ : B₁ = B := (hMa E hF.1).unique k₁.1 hB
    have e₂ : B₁' = B' := (hMa E' hF.2.1).unique k₁.2.1 hB'
    subst e₁ e₂
    have e₃ : G₁ = G := hGu G₁ k₁
    subst e₃
    exact hHu H' k₂
  · intro E E' E'' F F' F'' A A' A'' H H' H'' hc h₁ h₂ h₃
    have hE := hc.1.1
    have hE' := hc.1.2.1
    have hE'' := hc.2.1.2.1
    obtain ⟨B₁, B₁', G₁, k₁, l₁⟩ := sxAfter_morRel_dest hMa hE hE' h₁
    obtain ⟨B₂, B₂', G₂, k₂, l₂⟩ := sxAfter_morRel_dest hMa hE' hE'' h₂
    obtain ⟨B₃, B₃', G₃, k₃, l₃⟩ := sxAfter_morRel_dest hMa hE hE'' h₃
    have e₁ : B₂ = B₁' := (hMa E' hE').unique k₂.1 k₁.2.1
    have e₂ : B₃ = B₁ := (hMa E hE).unique k₃.1 k₁.1
    have e₃ : B₃' = B₂' := (hMa E'' hE'').unique k₃.2.1 k₂.2.1
    subst e₁ e₂ e₃
    exact hNc _ _ _ _ _ _ _ _ _ _ _ _ (hMc _ _ _ _ _ _ _ _ _ _ _ _ hc k₁ k₂ k₃) l₁ l₂ l₃
  · intro E I A J hI h
    have hE := hI.1.1
    obtain ⟨B, B', G, k, l⟩ := sxAfter_morRel_dest hMa hE hE h
    have e : B' = B := (hMa E hE).unique k.2.1 k.1
    subst e
    exact hNd _ _ _ _ (hMd _ _ _ _ hI k) l

end MutationComposite

end IUT.PaperIV.SpeciesExamples
