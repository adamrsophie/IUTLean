import Mathlib
import IUT.Foundations.GrothendieckUniverse
import IUT.Prerequisites.SemiGraph

/-!
# Species, mutations, mutation-histories, observables and cores (IUT IV, Section 3)

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Section 3: the introductory
discussion (pages 67 and 68), Definition 3.1 (pages 68 to 70), Remarks 3.1.1 to 3.1.5
(pages 70 and 71), Example 3.2 and Remark 3.2.1 (page 72), Definition 3.3 (pages 72 to 74) and
Example 3.4 (pages 76 and 77). Pages read for this file: 67 to 77. Pages checked against
rendered images: 67, 68, 69, 70, 72, 73, 74, 76 and 77; every clause represented below was
compared with the rendered page it cites.

This is a definitions module. It does not formalize any theorem of the papers; the only
results proved here are facts that the pages state as "one verifies immediately" or that follow
from the definitions, each listed below.

## Set-theoretic formulas and ZFC-models

* A *set-theoretic formula* is a first-order formula, in Mathlib's `FirstOrder.Language`, of
  the language `speciesLang` with no function symbols and one binary relation symbol, read as
  `∈`. Its free variables are indexed by a type (`Fin n` for an ordered collection of `n`
  indeterminate sets, sums of such types for several collections). This makes "given by a
  set-theoretic formula" a real condition: a species is a finite piece of syntax, and the
  specimens are whatever satisfies it.
* A *ZFC-model* is represented by a domain `D : Set ZFSet.{u}`, a class of sets of Mathlib's
  model `ZFSet` of ZFC, with `∈` interpreted as membership of `ZFSet` and quantifiers ranging
  over `D` (`speciesStructure`, `speciesHolds`). The page asks for "any ZFC-model"; here the
  ZFC-models quantified over are those of `IsSpeciesModel`: the ambient model `ZFSet.{u}`
  itself (the domain `Set.univ`) and the models determined by the Grothendieck universes of
  `IUT.Foundations.IsGrothendieckUniverse`, following page 67: the ZFC-models "may be thought
  of as [but are not restricted to be!] the ZFC-models determined by various universes that are
  sets relative to some ambient ZFC-model". ZFC as a first-order theory and its models in
  general are not defined here; this class is narrower than "any ZFC-model". The ambient model
  is included so that the class is provably nonempty: `ZFSet.{u}` may contain no
  Grothendieck universe
  (see `IUT.Foundations.GrothendieckUniverse`), and without it every condition of the form
  "in any ZFC-model" could hold vacuously.
* The proviso of page 68 (every set-theoretic formula is "absolute": its validity for sets of a
  universe `V` is the same relative to `V` and relative to any universe `W` with `V ∈ W`) is
  `SpeciesAbsolute`, and it is part of the definitions of a 0-species, a 1-species, a mutation
  and a morphism of mutations. `speciesAbsolute_of_delta0` proves that every formula all of
  whose quantifiers are bounded (`IsSpeciesDelta0`) satisfies it; the underlying theorem
  `speciesDelta0_realize_iff` is the absoluteness of such formulas between a transitive domain
  and any larger domain.
* "The 0-specimens form a set" (smallness) is read through the coding `speciesTupleCode` of an
  ordered collection of `n` sets as one set (iterated Kuratowski pairs; a 1-tuple is coded by
  its entry): there is a set `s` of the model such that a tuple of the model is a specimen
  exactly when its code is an element of `s`.

## Formalized

* Definition 3.1 (i): 0-species (`ZeroSpeciesData`, `IsZeroSpecies`), species-data (tuples
  `Fin n → ZFSet`), 0-specimens in a model (`zeroSpecimen`), 0-small (`IsZeroSmall`).
* Definition 3.1 (ii): 1-species acting on a 0-species (`OneSpeciesData`, `IsOneSpecies`):
  the formulas `Φ₁`, `Φ₁∘₁`, 1-specimens (`oneSpecimen`, which includes `Φ₀(E)`, `Φ₀(E')`),
  composites (`speciesComposite`, which includes the six conditions listed in (b)), and
  conditions (c) unique composites, (d) associativity and (e) identities
  (`SpeciesCompExistsUniqueAt`, `SpeciesCompAssocAt`, `SpeciesIdentityExistsAt`), each a
  predicate of one model and required in every model of `IsSpeciesModel`; 1-small
  (`IsOneSmall`).
* Definition 3.1 (iii): species (`SpeciesData`, `IsSpecies`), species-objects and
  species-morphisms (0- and 1-specimens), species-isomorphisms, species-isomorphic objects and
  species-automorphisms (`SpeciesIsIsoAt`, `SpeciesIsomorphicAt`, `SpeciesIsAutoAt`), and
  model-free specimens (`SpeciesModelFreeDescription`, `IsModelFreeZeroSpecimen`,
  `IsModelFreeOneSpecimen`).
* Definition 3.1 (iv): the category determined by a species in a model,
  `speciesCategoryAt`. The page's remark that this "does indeed determine a category" is the
  construction itself: the category laws are proved from (c), (d), (e). The identity
  1-specimen is unique (`speciesIdentity_unique`, the "necessarily unique" of (e)).
* Definition 3.3 (i): mutations (`MutationData`, `IsMutation`), with the uniqueness clauses of
  (a) and (b), compatibility with composites and preservation of identities. The functor that a
  mutation determines in a fixed model ("In particular, ...") is `mutationFunctorAt`.
* Definition 3.3 (ii): morphisms of mutations (`MutationMorphismData`, `IsMutationMorphism`),
  conditions (a) and (b); the natural transformation they determine ("In particular, ...") is
  `mutationNatTransAt`; isomorphisms of mutations (`IsMutationIso`).
* Definition 3.3 (iii): mutation-equivalences (`IsMutationEquivalence`), using the composite
  and identity mutations of the next item.
* The "evident notions" of composition of mutations and identity mutations, which the page
  does not write out, are fixed here (`mutationAfter`, `mutationIdentity`). They are choices
  made in this file. `isMutation_mutationIdentity` proves that the identity mutation of a
  species is a mutation; `mutationAfter_obj_holds` computes the object formula of a composite.
* Definition 3.3 (iv): oriented graphs and mutation-histories (`MutationHistoryData`,
  `IsMutationHistory`), built on the semi-graphs of `IUT.Prerequisites.SemiGraph`.
* Definition 3.3 (v): simply connected underlying graph (`IsSimplyConnectedGraph`), covariant
  and contravariant observables (`ObservableData`, `IsCovariantObservable`,
  `IsContravariantObservable`) and cores (`IsCore`).
* Examples. `pointSpecies` is a species in the sense of `IsSpecies`, 0-small and 1-small, with
  exactly one species-object in every model of `IsSpeciesModel`
  (`pointSpecies_existsUnique_object`); its only species-morphism is `(∅)`
  (`pointSpecies_oneSpecimen_iff`), and its defining formula is a model-free description of its
  species-object (`pointSpecies_modelFree`). Its identity mutation is a mutation
  (`pointSpecies_isMutation_identity`). It is a species of the kind
  described in Remark 3.1.1 (page 70), a species "all of whose species-morphisms are identity
  species-morphisms" with "a unique species-object in any given ZFC-model"; it is not one of the
  species named there (`ℕ`, `ℤ`, `ℚ`, `ℚ_p`, `ℝ`).
* Witnesses for Definition 3.3 (ii) to (v). For any species datum `S` and any two formula
  collections `M`, `M'` from `S` to `pointSpecies`, the formula `Ξ = ⊤` (`pointMorphism`) is an
  isomorphism of mutations `M → M'` (`isMutationIso_toPoint`). Hence the identity mutation of
  `pointSpecies` is a mutation-equivalence (`pointSpecies_isMutationEquivalence_identity`), and
  on any simply connected graph with an orientation, the mutation-history with `pointSpecies`
  at every vertex and identity mutations, with the identity observation mutations and the
  morphisms `pointMorphism`, is a core (`pointObservable_isCore`); `pointGraph`, one vertex and
  no edge, is such a graph (`pointGraph_isSimplyConnected`, `pointGraph_isCore`). These
  witnesses are degenerate: they show that the definitions can be satisfied, but because every
  morphism of `pointSpecies` is the same, they do not test the formula `Ψ₁` of `mutationAfter`,
  and the instance on `pointGraph` does not test the edge clauses.

## Not proved, with the reason

* Example 3.2 (categories and isomorphism classes of functors as a species) and Example 3.4
  (topological spaces, universal coverings, groups with outer homomorphisms, the
  fundamental-group mutation). Writing these as `∈`-formulas needs a library of formula
  combinators with realization lemmas (Kuratowski pairs and triples, graphs of maps, sets of
  composition relations, natural isomorphisms, quotients by deck transformations or inner
  automorphisms), followed by proofs of conditions (c) to (e) of Definition 3.1 (ii) for the
  set-theoretic encodings. None of this is built here. A version with Mathlib predicates on
  `ZFSet` in place of formulas would not be a species in the sense of the page, so none is given.
* The species-theoretic claim of Example 3.2 that species-isomorphisms correspond to
  isomorphism classes of equivalences of categories.
* The claim of Definition 3.1 (iii) that composites of species-isomorphisms are
  species-isomorphisms, here; it is proved in every model where conditions (c) to (e) hold in
  `IUT.PaperIV.SpeciesExamples` (`sxIsIsoAt_composite`).
* The claim of Definition 3.3 (ii) that `Z` is an isomorphism of mutations if and only if it
  has an inverse morphism of mutations; composition of morphisms of mutations and identity
  morphisms of mutations (also "evident notions" of the page) are not defined.
* The claim of Definition 3.3 (iii) that a mutation-equivalence between 1-small species
  induces bijections on species-morphisms and species-isomorphisms.
* That the composite of two mutations is a mutation (in particular that its formulas satisfy
  the absoluteness proviso), for `mutationAfter` as defined here. For the composite with the
  conditions on the source species added, it is proved in `IUT.PaperIV.SpeciesAbsoluteness`
  (`saMutationComp_isMutation`). The definitions of observables and mutation-equivalences use
  the composite formulas without this claim.
* "Model-free" for an `i`-specimen is stated for pairs of universes `V₁ ∈ V₂`, as on page 69;
  if `ZFSet.{u}` contains no such pair, the condition is vacuous.
* Absoluteness: the formula combinators `mutationAfter` use unbounded quantifiers over tuples,
  so `speciesAbsolute_of_delta0` does not apply to them.
* "2-species" and "n-species" (Remark 3.2.1) are mentioned on page 72 but not defined there;
  Definition 3.1 defines only 0-species, 1-species and species, so nothing else is defined
  here.
* Remarks 3.1.2 to 3.1.5, 3.3.1 and 3.3.2 are discussion and are not formalized.

## Reading choices, recorded

* Page 73, Definition 3.3 (i) (b) prints "such that `Ψ₀(E, E', F, F̲)` holds"; the formula with
  these four arguments is `Ψ₁`, and it is read as `Ψ₁`. This looks like a misprint.
* Following the displays `Ψ₁(𝔈, 𝔈', 𝔉, 𝔉̲)` (page 72) and `Ξ(𝔈, 𝔉̲)` (page 73), the formula `Ψ₁`
  has free variables for `E`, `E'`, `F` and the morphism part `F̲` only, the domain and codomain
  of `F̲` being `M(E)` and `M(E')`; likewise `Ξ` has free variables for `E` and the morphism part
  of `Z(E)`.
* "The composites `F ∘ F'`, `F' ∘ F` are identity species-morphisms" (page 69) is read as: some
  composite is an identity 1-specimen; by (c) composites are unique.
* Clause (d) (associativity) is read as: whenever the four composites `F' ∘ F`, `F'' ∘ (F' ∘ F)`,
  `F'' ∘ F'` and `(F'' ∘ F') ∘ F` are formed, the two triple composites are equal.
* The total ordering of the two branches of an edge (page 74) is given by a choice of the first
  branch; the edge runs from the vertex of the first branch to the vertex of the second.
* "Simply connected" for the underlying graph is read as: no edge is a loop and the incidence
  graph of `IUT.Prerequisites.SemiGraph` is a tree (`SimpleGraph.IsTree`). Without loops the
  incidence graph is the barycentric subdivision of the graph, whose topological realization is
  simply connected exactly when it is a tree; that equivalence is not proved here.
* Definition 3.3 opens with "Let 𝔖, 𝔖̲ be species" (page 72). `IsMutation`, `IsMutationMorphism`,
  `IsMutationIso` and `IsMutationEquivalence` do not include the conditions `IsSpecies` on the
  source and target; mutation-histories and observables require `IsSpecies` separately.
* In Definition 3.3 (iii) the direction of the isomorphisms between the composites and the
  identity mutations is not specified; here they run from the composites to the identities.
* The morphism and isomorphism conditions of Definition 3.3 (ii) are stated for any pair of
  formula collections `M`, `M'`, so that they apply to the composites `V^{v₂} ∘ M^e` of (v),
  which are not proved to be mutations.
-/

universe u w

namespace IUT.PaperIV.Species

open IUT.Foundations

/-! ## Set-theoretic formulas -/

/-- The first-order language of set theory: no function symbols and one binary relation
symbol, read as membership. -/
def speciesLang : FirstOrder.Language.{0, 0} where
  Functions := fun _ => Empty
  Relations := fun n => PLift (n = 2)

/-- The membership symbol of `speciesLang`. -/
def speciesMemSymbol : speciesLang.Relations 2 := ⟨rfl⟩

/-- The structure on a domain `D` of sets determined by the membership relation of `ZFSet`:
the model of set theory with universe of discourse `D`. -/
@[reducible] def speciesStructure (D : Set ZFSet.{u}) : speciesLang.Structure D where
  funMap := fun f _ => Empty.elim f
  RelMap := fun r xs =>
    (xs ⟨0, by have := r.down; omega⟩).1 ∈ (xs ⟨1, by have := r.down; omega⟩).1

/-- The atomic formula `t₁ ∈ t₂`. -/
def speciesMemF {α : Type*} {n : ℕ} (t₁ t₂ : speciesLang.Term (α ⊕ Fin n)) :
    speciesLang.BoundedFormula α n :=
  FirstOrder.Language.Relations.boundedFormula₂ speciesMemSymbol t₁ t₂

/-- The bounded universal quantifier `∀ x ∈ w, φ`, where `w` is a variable other than `x`. -/
def speciesBall {α : Type*} {n : ℕ} (w : α ⊕ Fin n) (φ : speciesLang.BoundedFormula α (n + 1)) :
    speciesLang.BoundedFormula α n :=
  FirstOrder.Language.BoundedFormula.all
    ((speciesMemF (FirstOrder.Language.Term.var (Sum.inr (Fin.last n)))
      (FirstOrder.Language.Term.var (Sum.map id Fin.castSucc w))).imp φ)

/-- Formulas all of whose quantifiers are bounded (`Δ₀`-formulas): built from atomic formulas
by implication, falsity and bounded universal quantification. -/
inductive IsSpeciesDelta0 {α : Type*} : {n : ℕ} → speciesLang.BoundedFormula α n → Prop
  | falsum {n : ℕ} :
      IsSpeciesDelta0 (FirstOrder.Language.BoundedFormula.falsum : speciesLang.BoundedFormula α n)
  | equal {n : ℕ} (t₁ t₂ : speciesLang.Term (α ⊕ Fin n)) :
      IsSpeciesDelta0 (FirstOrder.Language.BoundedFormula.equal t₁ t₂)
  | rel {n l : ℕ} (R : speciesLang.Relations l) (ts : Fin l → speciesLang.Term (α ⊕ Fin n)) :
      IsSpeciesDelta0 (FirstOrder.Language.BoundedFormula.rel R ts)
  | imp {n : ℕ} {φ ψ : speciesLang.BoundedFormula α n} :
      IsSpeciesDelta0 φ → IsSpeciesDelta0 ψ → IsSpeciesDelta0 (φ.imp ψ)
  | ball {n : ℕ} (w : α ⊕ Fin n) {φ : speciesLang.BoundedFormula α (n + 1)} :
      IsSpeciesDelta0 φ → IsSpeciesDelta0 (speciesBall w φ)

/-- Realization of a bounded formula in the model with domain `D`. -/
def speciesRealizeAt {α : Type*} {n : ℕ} (D : Set ZFSet.{u})
    (φ : speciesLang.BoundedFormula α n) (v : α → D) (xs : Fin n → D) : Prop :=
  letI := speciesStructure D
  φ.Realize v xs

/-- Value of a term in the model with domain `D`. -/
def speciesTermAt {β : Type*} (D : Set ZFSet.{u}) (t : speciesLang.Term β) (w : β → D) : D :=
  letI := speciesStructure D
  t.realize w

/-- A formula `φ` holds in the model with domain `D` at the assignment `x` of sets to its free
variables: all the values of `x` lie in `D`, and `φ` is true in `D` at `x`. -/
def speciesHolds {α : Type*} (D : Set ZFSet.{u}) (φ : speciesLang.Formula α)
    (x : α → ZFSet.{u}) : Prop :=
  ∃ hx : ∀ a, x a ∈ D, letI := speciesStructure D; φ.Realize fun a => (⟨x a, hx a⟩ : D)

theorem speciesTermAt_var {β : Type*} (D : Set ZFSet.{u}) (b : β) (w : β → D) :
    speciesTermAt D (FirstOrder.Language.Term.var b) w = w b := rfl

theorem speciesMemF_realize {α : Type*} {n : ℕ} (D : Set ZFSet.{u})
    (t₁ t₂ : speciesLang.Term (α ⊕ Fin n)) (v : α → D) (xs : Fin n → D) :
    speciesRealizeAt D (speciesMemF t₁ t₂) v xs ↔
      (speciesTermAt D t₁ (Sum.elim v xs)).1 ∈ (speciesTermAt D t₂ (Sum.elim v xs)).1 :=
  Iff.rfl

/-- The bounded quantifier `speciesBall w φ` means `∀ x ∈ w, φ` in every domain. -/
theorem speciesBall_realize {α : Type*} {n : ℕ} (D : Set ZFSet.{u}) (w : α ⊕ Fin n)
    (φ : speciesLang.BoundedFormula α (n + 1)) (v : α → D) (xs : Fin n → D) :
    speciesRealizeAt D (speciesBall w φ) v xs ↔
      ∀ x : D, x.1 ∈ (Sum.elim v xs w).1 → speciesRealizeAt D φ v (Fin.snoc xs x) := by
  have key : ∀ x : D,
      Sum.elim v (Fin.snoc xs x : Fin (n + 1) → D) (Sum.map id Fin.castSucc w) =
        Sum.elim v xs w := by
    intro x
    rcases w with a | i
    · rfl
    · simp [Fin.snoc_castSucc]
  show (∀ x : D, speciesRealizeAt D (speciesMemF _ _) v (Fin.snoc xs x) →
    speciesRealizeAt D φ v (Fin.snoc xs x)) ↔ _
  refine forall_congr' fun x => imp_congr ?_ Iff.rfl
  rw [speciesMemF_realize, speciesTermAt_var, speciesTermAt_var, Sum.elim_inr, Fin.snoc_last,
    key x]

theorem speciesTermAt_inclusion {β : Type*} {D D' : Set ZFSet.{u}} (h : D ⊆ D')
    (t : speciesLang.Term β) (w : β → D) :
    speciesTermAt D' t (Set.inclusion h ∘ w) = Set.inclusion h (speciesTermAt D t w) := by
  cases t with
  | var a => rfl
  | func f _ => exact Empty.elim f

/-- Absoluteness of `Δ₀`-formulas: if `D ⊆ D'` and `D` is transitive, a formula with bounded
quantifiers has the same truth value in `D` and in `D'` at every assignment of elements of `D`.
This is the formal content of the absoluteness proviso of page 68 for such formulas. -/
theorem speciesDelta0_realize_iff {α : Type*} {D D' : Set ZFSet.{u}} (h : D ⊆ D')
    (htr : ∀ x ∈ D, ∀ y ∈ x, y ∈ D) (v : α → D) {n : ℕ}
    {φ : speciesLang.BoundedFormula α n} (hφ : IsSpeciesDelta0 φ) :
    ∀ xs : Fin n → D, speciesRealizeAt D φ v xs ↔
      speciesRealizeAt D' φ (Set.inclusion h ∘ v) (Set.inclusion h ∘ xs) := by
  induction hφ with
  | falsum => intro xs; exact Iff.rfl
  | equal t₁ t₂ =>
    intro xs
    show speciesTermAt D t₁ (Sum.elim v xs) = speciesTermAt D t₂ (Sum.elim v xs) ↔
      speciesTermAt D' t₁ (Sum.elim (Set.inclusion h ∘ v) (Set.inclusion h ∘ xs)) =
        speciesTermAt D' t₂ (Sum.elim (Set.inclusion h ∘ v) (Set.inclusion h ∘ xs))
    rw [← Sum.comp_elim, speciesTermAt_inclusion, speciesTermAt_inclusion]
    exact (Set.inclusion_injective h).eq_iff.symm
  | rel R ts =>
    intro xs
    show (speciesTermAt D (ts ⟨0, _⟩) (Sum.elim v xs)).1 ∈
        (speciesTermAt D (ts ⟨1, _⟩) (Sum.elim v xs)).1 ↔
      (speciesTermAt D' (ts ⟨0, _⟩) (Sum.elim (Set.inclusion h ∘ v) (Set.inclusion h ∘ xs))).1 ∈
        (speciesTermAt D' (ts ⟨1, _⟩)
          (Sum.elim (Set.inclusion h ∘ v) (Set.inclusion h ∘ xs))).1
    rw [← Sum.comp_elim, speciesTermAt_inclusion, speciesTermAt_inclusion]
  | imp _ _ ih₁ ih₂ => intro xs; exact imp_congr (ih₁ xs) (ih₂ xs)
  | ball w _ ih =>
    intro xs
    rw [speciesBall_realize, speciesBall_realize]
    have hmem : ∀ y : ZFSet.{u},
        y ∈ (Sum.elim (Set.inclusion h ∘ v) (Set.inclusion h ∘ xs) w).1 ↔
          y ∈ (Sum.elim v xs w).1 := by
      intro y; rw [← Sum.comp_elim]; exact Iff.rfl
    constructor
    · intro H x' hx'
      have hx'D : x'.1 ∈ D := htr _ (Sum.elim v xs w).2 _ ((hmem _).1 hx')
      have hx : Set.inclusion h ⟨x'.1, hx'D⟩ = x' := Subtype.ext rfl
      have := (ih (Fin.snoc xs ⟨x'.1, hx'D⟩)).1 (H _ ((hmem _).1 hx'))
      rwa [Fin.comp_snoc, hx] at this
    · intro H x hx
      have := H (Set.inclusion h x) ((hmem _).2 hx)
      rw [← Fin.comp_snoc] at this
      exact (ih (Fin.snoc xs x)).2 this

/-! ## ZFC-models and the absoluteness proviso -/

/-- The ZFC-models used in this file: the ambient model `ZFSet.{u}` (domain `Set.univ`) and the
models determined by Grothendieck universes `V` (domain the elements of `V`), as on page 67.
This is narrower than "any ZFC-model" of the page; see the module docstring. -/
def IsSpeciesModel (D : Set ZFSet.{u}) : Prop :=
  D = Set.univ ∨ ∃ V : ZFSet.{u}, IsGrothendieckUniverse V ∧ D = {y | y ∈ V}

/-- The absoluteness proviso of page 68: for universes `V ∈ W` and sets of `V`, the formula
holds relative to the model determined by `V` exactly when it holds relative to the model
determined by `W`. -/
def SpeciesAbsolute {α : Type*} (φ : speciesLang.Formula α) : Prop :=
  ∀ V W : ZFSet.{u}, IsGrothendieckUniverse V → IsGrothendieckUniverse W → V ∈ W →
    ∀ x : α → ZFSet.{u}, (∀ a, x a ∈ V) →
      (speciesHolds {y | y ∈ V} φ x ↔ speciesHolds {y | y ∈ W} φ x)

theorem isSpeciesModel_univ : IsSpeciesModel (Set.univ : Set ZFSet.{u}) := Or.inl rfl

theorem isSpeciesModel_transitive {D : Set ZFSet.{u}} (hD : IsSpeciesModel D) :
    ∀ x ∈ D, ∀ y ∈ x, y ∈ D := by
  rcases hD with rfl | ⟨V, hV, rfl⟩
  · intro _ _ _ _; trivial
  · exact hV.transitive

theorem isSpeciesModel_empty_mem {D : Set ZFSet.{u}} (hD : IsSpeciesModel D) :
    (∅ : ZFSet.{u}) ∈ D := by
  rcases hD with rfl | ⟨V, hV, rfl⟩
  · trivial
  · exact hV.transitive _ hV.omega_mem _ ZFSet.omega_zero

theorem isSpeciesModel_powerset_empty_mem {D : Set ZFSet.{u}} (hD : IsSpeciesModel D) :
    ZFSet.powerset (∅ : ZFSet.{u}) ∈ D := by
  rcases hD with rfl | ⟨V, hV, rfl⟩
  · trivial
  · exact hV.powerset_mem _ (hV.transitive _ hV.omega_mem _ ZFSet.omega_zero)

/-- A formula with bounded quantifiers satisfies the absoluteness proviso of page 68. -/
theorem speciesAbsolute_of_delta0 {α : Type*} {φ : speciesLang.Formula α}
    (hφ : IsSpeciesDelta0 φ) : SpeciesAbsolute.{u} φ := by
  intro V W hV _ hVW x hx
  have hsub : {y | y ∈ V} ⊆ {y | y ∈ W} := fun y hy => ‹IsGrothendieckUniverse W›.transitive
    V hVW y hy
  have key := speciesDelta0_realize_iff hsub hV.transitive (fun a => ⟨x a, hx a⟩) hφ default
  constructor
  · rintro ⟨_, hφV⟩
    refine ⟨fun a => hsub (hx a), ?_⟩
    have := key.1 hφV
    rwa [Subsingleton.elim (Set.inclusion hsub ∘ default) default] at this
  · rintro ⟨_, hφW⟩
    refine ⟨hx, key.2 ?_⟩
    rwa [Subsingleton.elim (Set.inclusion hsub ∘ default) default]

/-! ## Coding of tuples -/

/-- The code of an ordered collection of `n` sets as one set: `∅` for `n = 0`, the entry itself
for `n = 1`, and iterated Kuratowski pairs `(E₀, (E₁, ...))` for `n ≥ 2`. -/
def speciesTupleCode : (n : ℕ) → (Fin n → ZFSet.{u}) → ZFSet.{u}
  | 0, _ => ∅
  | 1, E => E 0
  | n + 2, E => ZFSet.pair (E 0) (speciesTupleCode (n + 1) (Fin.tail E))

/-! ## Definition 3.1: species -/

/-- A 0-species (Definition 3.1 (i), page 68): a set-theoretic formula `Φ₀(E)` in an ordered
collection `E = (E₁, ..., E_{n₀})` of indeterminate sets. -/
structure ZeroSpeciesData where
  /-- The length `n₀` of a collection of species-data. -/
  zsArity : ℕ
  /-- The formula `Φ₀`. -/
  zsFormula : speciesLang.Formula (Fin zsArity)

/-- A 1-species acting on a 0-species `S₀` (Definition 3.1 (ii), pages 68 and 69): formulas
`Φ₁(E, E', F)` and `Φ₁∘₁(E, E', E'', F, F', F'')`. -/
structure OneSpeciesData (S₀ : ZeroSpeciesData) where
  /-- The length `n₁` of the collection `F`. -/
  osArity : ℕ
  /-- The formula `Φ₁(E, E', F)`. -/
  osFormula : speciesLang.Formula (Fin S₀.zsArity ⊕ Fin S₀.zsArity ⊕ Fin osArity)
  /-- The formula `Φ₁∘₁(E, E', E'', F, F', F'')`. -/
  osCompFormula : speciesLang.Formula
    ((Fin S₀.zsArity ⊕ Fin S₀.zsArity ⊕ Fin S₀.zsArity) ⊕ (Fin osArity ⊕ Fin osArity ⊕ Fin osArity))

/-- A species (Definition 3.1 (iii), page 69): a 0-species with a 1-species acting on it. -/
structure SpeciesData where
  /-- The 0-species `𝔖₀`. -/
  spZero : ZeroSpeciesData
  /-- The 1-species `𝔖₁` acting on `𝔖₀`. -/
  spOne : OneSpeciesData spZero

/-- The length `n₀` of species-objects. -/
abbrev SpeciesData.objArity (S : SpeciesData) : ℕ := S.spZero.zsArity

/-- The length `n₁` of species-morphisms. -/
abbrev SpeciesData.morArity (S : SpeciesData) : ℕ := S.spOne.osArity

section Specimens

variable (D : Set ZFSet.{u})

/-- A 0-specimen of `S₀` in the model `D`: an ordered collection of `n₀` sets of `D`
satisfying `Φ₀` (Definition 3.1 (i)). -/
def zeroSpecimen (S₀ : ZeroSpeciesData) (E : Fin S₀.zsArity → ZFSet.{u}) : Prop :=
  speciesHolds D S₀.zsFormula E

/-- A 1-specimen `F : E → E'` of `S` in the model `D`: `E`, `E'` are 0-specimens and
`Φ₁(E, E', F)` holds (Definition 3.1 (ii) (a)). -/
def oneSpecimen (S : SpeciesData) (E E' : Fin S.objArity → ZFSet.{u})
    (F : Fin S.morArity → ZFSet.{u}) : Prop :=
  zeroSpecimen D S.spZero E ∧ zeroSpecimen D S.spZero E' ∧
    speciesHolds D S.spOne.osFormula (Sum.elim E (Sum.elim E' F))

/-- `F'' : E → E''` is a composite of `F : E → E'` with `F' : E' → E''` in the model `D`: the
six conditions listed in Definition 3.1 (ii) (b) and `Φ₁∘₁(E, E', E'', F, F', F'')`. -/
def speciesComposite (S : SpeciesData) (E E' E'' : Fin S.objArity → ZFSet.{u})
    (F F' F'' : Fin S.morArity → ZFSet.{u}) : Prop :=
  oneSpecimen D S E E' F ∧ oneSpecimen D S E' E'' F' ∧ oneSpecimen D S E E'' F'' ∧
    speciesHolds D S.spOne.osCompFormula
      (Sum.elim (Sum.elim E (Sum.elim E' E'')) (Sum.elim F (Sum.elim F' F'')))

/-- Condition (c) of Definition 3.1 (ii) in the model `D`: any two 1-specimens
`F : E → E'`, `F' : E' → E''` have a unique composite. -/
def SpeciesCompExistsUniqueAt (S : SpeciesData) : Prop :=
  ∀ E E' E'' F F', oneSpecimen D S E E' F → oneSpecimen D S E' E'' F' →
    ∃! F'', speciesComposite D S E E' E'' F F' F''

/-- Condition (d) of Definition 3.1 (ii) in the model `D`: composition is associative. -/
def SpeciesCompAssocAt (S : SpeciesData) : Prop :=
  ∀ E₁ E₂ E₃ E₄ F₁ F₂ F₃ G H G' H',
    speciesComposite D S E₁ E₂ E₃ F₁ F₂ G → speciesComposite D S E₁ E₃ E₄ G F₃ H →
    speciesComposite D S E₂ E₃ E₄ F₂ F₃ G' → speciesComposite D S E₁ E₂ E₄ F₁ G' H' → H = H'

/-- `I : E → E` is an identity 1-specimen of `E` in the model `D` (Definition 3.1 (ii) (e)):
`I ∘ F' = F'` for every `F' : E' → E` and `F'' ∘ I = F''` for every `F'' : E → E''`. -/
def SpeciesIsIdentityAt (S : SpeciesData) (E : Fin S.objArity → ZFSet.{u})
    (I : Fin S.morArity → ZFSet.{u}) : Prop :=
  oneSpecimen D S E E I ∧
    (∀ E' F', oneSpecimen D S E' E F' → speciesComposite D S E' E E F' I F') ∧
    (∀ E'' F'', oneSpecimen D S E E'' F'' → speciesComposite D S E E E'' I F'' F'')

/-- Condition (e) of Definition 3.1 (ii) in the model `D`: every 0-specimen has an identity
1-specimen. -/
def SpeciesIdentityExistsAt (S : SpeciesData) : Prop :=
  ∀ E, zeroSpecimen D S.spZero E → ∃ I, SpeciesIsIdentityAt D S E I

/-- Conditions (c), (d), (e) of Definition 3.1 (ii) in the model `D`. -/
def SpeciesAxiomsAt (S : SpeciesData) : Prop :=
  SpeciesCompExistsUniqueAt D S ∧ SpeciesCompAssocAt D S ∧ SpeciesIdentityExistsAt D S

/-- A species-morphism `F : E → E'` is a species-isomorphism in the model `D`
(Definition 3.1 (iii)): there is `F' : E' → E` such that the composites `F ∘ F'` and `F' ∘ F`
are identity species-morphisms. -/
def SpeciesIsIsoAt (S : SpeciesData) (E E' : Fin S.objArity → ZFSet.{u})
    (F : Fin S.morArity → ZFSet.{u}) : Prop :=
  oneSpecimen D S E E' F ∧ ∃ F', oneSpecimen D S E' E F' ∧
    (∃ H, speciesComposite D S E E' E F F' H ∧ SpeciesIsIdentityAt D S E H) ∧
    (∃ H', speciesComposite D S E' E E' F' F H' ∧ SpeciesIsIdentityAt D S E' H')

/-- Species-objects `E`, `E'` are species-isomorphic in the model `D`. -/
def SpeciesIsomorphicAt (S : SpeciesData) (E E' : Fin S.objArity → ZFSet.{u}) : Prop :=
  ∃ F, SpeciesIsIsoAt D S E E' F

/-- A species-automorphism of `E` in the model `D`: a species-isomorphism `E → E`. -/
def SpeciesIsAutoAt (S : SpeciesData) (E : Fin S.objArity → ZFSet.{u})
    (F : Fin S.morArity → ZFSet.{u}) : Prop :=
  SpeciesIsIsoAt D S E E F

end Specimens

/-- Definition 3.1 (i): `S₀` is a 0-species: `n₀ ≥ 1` and `Φ₀` satisfies the proviso of
page 68. -/
def IsZeroSpecies (S₀ : ZeroSpeciesData) : Prop :=
  1 ≤ S₀.zsArity ∧ SpeciesAbsolute.{u} S₀.zsFormula

/-- Definition 3.1 (i): `S₀` is 0-small: in every model the 0-specimens form a set. -/
def IsZeroSmall (S₀ : ZeroSpeciesData) : Prop :=
  ∀ D : Set ZFSet.{u}, IsSpeciesModel D → ∃ s ∈ D, ∀ E : Fin S₀.zsArity → ZFSet.{u},
    (∀ i, E i ∈ D) → (zeroSpecimen D S₀ E ↔ speciesTupleCode _ E ∈ s)

/-- Definition 3.1 (ii): the 1-species of `S` acts on its 0-species: `n₁ ≥ 1`, the formulas
satisfy the proviso of page 68, and conditions (c), (d), (e) hold in every model. -/
def IsOneSpecies (S : SpeciesData) : Prop :=
  1 ≤ S.morArity ∧ SpeciesAbsolute.{u} S.spOne.osFormula ∧
    SpeciesAbsolute.{u} S.spOne.osCompFormula ∧
    ∀ D : Set ZFSet.{u}, IsSpeciesModel D → SpeciesAxiomsAt D S

/-- Definition 3.1 (ii): `S` is 1-small: in every model, for any two 0-specimens `E`, `E'` the
1-specimens `F : E → E'` form a set. -/
def IsOneSmall (S : SpeciesData) : Prop :=
  ∀ D : Set ZFSet.{u}, IsSpeciesModel D → ∀ E E', zeroSpecimen D S.spZero E →
    zeroSpecimen D S.spZero E' → ∃ s ∈ D, ∀ F : Fin S.morArity → ZFSet.{u},
      (∀ i, F i ∈ D) → (oneSpecimen D S E E' F ↔ speciesTupleCode _ F ∈ s)

/-- Definition 3.1 (iii): `S` is a species. -/
def IsSpecies (S : SpeciesData) : Prop :=
  IsZeroSpecies.{u} S.spZero ∧ IsOneSpecies.{u} S

/-- A formula `ψ` is a description of an `i`-specimen that is independent of the model
(Definition 3.1 (iii), page 69): for every pair of universes `V₁ ∈ V₂`, `ψ` determines a unique
assignment in the model of `V₁` and a unique assignment in the model of `V₂`, these are the same,
and it is a specimen (property `P`) in both models. -/
def SpeciesModelFreeDescription {α : Type*} (ψ : speciesLang.Formula α)
    (P : Set ZFSet.{u} → (α → ZFSet.{u}) → Prop) : Prop :=
  ∀ V₁ V₂ : ZFSet.{u}, IsGrothendieckUniverse V₁ → IsGrothendieckUniverse V₂ → V₁ ∈ V₂ →
    ∃ x, P {y | y ∈ V₁} x ∧ P {y | y ∈ V₂} x ∧
      (∀ x', speciesHolds {y | y ∈ V₁} ψ x' ↔ x' = x) ∧
      (∀ x', speciesHolds {y | y ∈ V₂} ψ x' ↔ x' = x)

/-- A model-free species-object: a description of a 0-specimen independent of the model. -/
def IsModelFreeZeroSpecimen (S : SpeciesData) (ψ : speciesLang.Formula (Fin S.objArity)) :
    Prop :=
  SpeciesModelFreeDescription.{u} ψ fun D E => zeroSpecimen D S.spZero E

/-- A model-free species-morphism: a description of a 1-specimen `(E, E', F)` independent of the
model. -/
def IsModelFreeOneSpecimen (S : SpeciesData)
    (ψ : speciesLang.Formula (Fin S.objArity ⊕ Fin S.objArity ⊕ Fin S.morArity)) : Prop :=
  SpeciesModelFreeDescription.{u} ψ fun D x =>
    oneSpecimen D S (x ∘ Sum.inl) (x ∘ Sum.inr ∘ Sum.inl) (x ∘ Sum.inr ∘ Sum.inr)

/-! ## Definition 3.1 (iv): the category determined by a species in a model -/

section Category

variable {D : Set ZFSet.{u}} {S : SpeciesData}

/-- The species-objects of `S` in the model `D`. -/
def SpeciesObjAt (D : Set ZFSet.{u}) (S : SpeciesData) : Type (u + 1) :=
  {E : Fin S.objArity → ZFSet.{u} // zeroSpecimen D S.spZero E}

/-- The species-morphisms `X → Y` of `S` in the model `D`. -/
def SpeciesHomAt (D : Set ZFSet.{u}) (S : SpeciesData) (X Y : SpeciesObjAt D S) : Type (u + 1) :=
  {F : Fin S.morArity → ZFSet.{u} // oneSpecimen D S X.1 Y.1 F}

/-- The identity 1-specimen is unique ("necessarily unique", Definition 3.1 (ii) (e)). -/
theorem speciesIdentity_unique (hc : SpeciesCompExistsUniqueAt D S)
    {E : Fin S.objArity → ZFSet.{u}} {I J : Fin S.morArity → ZFSet.{u}}
    (hI : SpeciesIsIdentityAt D S E I) (hJ : SpeciesIsIdentityAt D S E J) : I = J :=
  (hc _ _ _ _ _ hI.1 hJ.1).unique (hJ.2.1 E I hI.1) (hI.2.2 E J hJ.1)

/-- The identity species-morphism chosen by condition (e). -/
noncomputable def speciesIdAt (h : SpeciesAxiomsAt D S) (X : SpeciesObjAt D S) :
    Fin S.morArity → ZFSet.{u} :=
  Classical.choose (h.2.2 X.1 X.2)

theorem speciesIdAt_spec (h : SpeciesAxiomsAt D S) (X : SpeciesObjAt D S) :
    SpeciesIsIdentityAt D S X.1 (speciesIdAt h X) :=
  Classical.choose_spec (h.2.2 X.1 X.2)

/-- The composite species-morphism given by condition (c). -/
noncomputable def speciesCompAt (h : SpeciesAxiomsAt D S) {X Y Z : SpeciesObjAt D S}
    (f : SpeciesHomAt D S X Y) (g : SpeciesHomAt D S Y Z) : SpeciesHomAt D S X Z :=
  ⟨Classical.choose (h.1 _ _ _ _ _ f.2 g.2).exists,
    (Classical.choose_spec (h.1 _ _ _ _ _ f.2 g.2).exists).2.2.1⟩

theorem speciesCompAt_spec (h : SpeciesAxiomsAt D S) {X Y Z : SpeciesObjAt D S}
    (f : SpeciesHomAt D S X Y) (g : SpeciesHomAt D S Y Z) :
    speciesComposite D S X.1 Y.1 Z.1 f.1 g.1 (speciesCompAt h f g).1 :=
  Classical.choose_spec (h.1 _ _ _ _ _ f.2 g.2).exists

theorem speciesCompAt_eq (h : SpeciesAxiomsAt D S) {X Y Z : SpeciesObjAt D S}
    (f : SpeciesHomAt D S X Y) (g : SpeciesHomAt D S Y Z) {H : Fin S.morArity → ZFSet.{u}}
    (hH : speciesComposite D S X.1 Y.1 Z.1 f.1 g.1 H) : (speciesCompAt h f g).1 = H :=
  (h.1 _ _ _ _ _ f.2 g.2).unique (speciesCompAt_spec h f g) hH

/-- Definition 3.1 (iv): the category determined by `S` in the model `D`, whose objects are the
species-objects and whose arrows are the species-morphisms. Composition in Mathlib's
diagrammatic order: `f ≫ g` is the composite `g ∘ f` of the page. The category laws are proved
from conditions (c), (d), (e) ("one verifies immediately that this description does indeed
determine a category", page 70). -/
@[reducible] noncomputable def speciesCategoryAt (h : SpeciesAxiomsAt D S) :
    CategoryTheory.Category.{u + 1} (SpeciesObjAt D S) where
  Hom X Y := SpeciesHomAt D S X Y
  id X := ⟨speciesIdAt h X, (speciesIdAt_spec h X).1⟩
  comp f g := speciesCompAt h f g
  id_comp f := Subtype.ext (speciesCompAt_eq h _ _ ((speciesIdAt_spec h _).2.2 _ f.1 f.2))
  comp_id f := Subtype.ext (speciesCompAt_eq h _ _ ((speciesIdAt_spec h _).2.1 _ f.1 f.2))
  assoc f g k := Subtype.ext (h.2.1 _ _ _ _ _ _ _ _ _ _ _ (speciesCompAt_spec h f g)
    (speciesCompAt_spec h (speciesCompAt h f g) k) (speciesCompAt_spec h g k)
    (speciesCompAt_spec h f (speciesCompAt h g k)))

end Category

/-! ## Definition 3.3 (i): mutations -/

/-- A mutation `𝔐 : 𝔖 ⇝ 𝔖̲` (Definition 3.3 (i), pages 72 and 73): formulas `Ψ₀(E, E̲)` and
`Ψ₁(E, E', F, F̲)`. -/
structure MutationData (S T : SpeciesData) where
  /-- The formula `Ψ₀(E, E̲)`. -/
  mutObjFormula : speciesLang.Formula (Fin S.objArity ⊕ Fin T.objArity)
  /-- The formula `Ψ₁(E, E', F, F̲)`. -/
  mutMorFormula :
    speciesLang.Formula (Fin S.objArity ⊕ Fin S.objArity ⊕ Fin S.morArity ⊕ Fin T.morArity)

section Mutations

variable (D : Set ZFSet.{u}) {S T : SpeciesData}

/-- `A = 𝔐(E)` in the model `D`: `A` is a 0-specimen of `𝔖̲` and `Ψ₀(E, A)` holds. -/
def mutationObjRel (M : MutationData S T) (E : Fin S.objArity → ZFSet.{u})
    (A : Fin T.objArity → ZFSet.{u}) : Prop :=
  zeroSpecimen D T.spZero A ∧ speciesHolds D M.mutObjFormula (Sum.elim E A)

/-- `G : A → A'` is `𝔐(F)` for `F : E → E'` in the model `D`: `A = 𝔐(E)`, `A' = 𝔐(E')`, `G`
is a 1-specimen of `𝔖̲` and `Ψ₁(E, E', F, G)` holds. -/
def mutationMorRel (M : MutationData S T) (E E' : Fin S.objArity → ZFSet.{u})
    (F : Fin S.morArity → ZFSet.{u}) (A A' : Fin T.objArity → ZFSet.{u})
    (G : Fin T.morArity → ZFSet.{u}) : Prop :=
  mutationObjRel D M E A ∧ mutationObjRel D M E' A' ∧ oneSpecimen D T A A' G ∧
    speciesHolds D M.mutMorFormula (Sum.elim E (Sum.elim E' (Sum.elim F G)))

/-- Definition 3.3 (i) (a) in the model `D`: for every `E ∈ 𝔖₀` there is a unique
`E̲ ∈ 𝔖̲₀` with `Ψ₀(E, E̲)`. -/
def MutationObjUniqueAt (M : MutationData S T) : Prop :=
  ∀ E, zeroSpecimen D S.spZero E → ∃! A, mutationObjRel D M E A

/-- Definition 3.3 (i) (b), first requirement, in the model `D`: for every
`(F : E → E') ∈ 𝔖₁` there is a unique `(F̲ : 𝔐(E) → 𝔐(E')) ∈ 𝔖̲₁` with `Ψ₁(E, E', F, F̲)`. -/
def MutationMorUniqueAt (M : MutationData S T) : Prop :=
  ∀ E E' F A A', oneSpecimen D S E E' F → mutationObjRel D M E A → mutationObjRel D M E' A' →
    ∃! G, mutationMorRel D M E E' F A A' G

/-- Definition 3.3 (i) (b), compatibility with composites, in the model `D`. -/
def MutationCompatAt (M : MutationData S T) : Prop :=
  ∀ E E' E'' F F' F'' A A' A'' G G' G'',
    speciesComposite D S E E' E'' F F' F'' → mutationMorRel D M E E' F A A' G →
    mutationMorRel D M E' E'' F' A' A'' G' → mutationMorRel D M E E'' F'' A A'' G'' →
    speciesComposite D T A A' A'' G G' G''

/-- Definition 3.3 (i) (b), identity species-morphisms go to identity species-morphisms, in
the model `D`. -/
def MutationIdentityAt (M : MutationData S T) : Prop :=
  ∀ E I A J, SpeciesIsIdentityAt D S E I → mutationMorRel D M E E I A A J →
    SpeciesIsIdentityAt D T A J

/-- The conditions of Definition 3.3 (i) in the model `D`. -/
def MutationAxiomsAt (M : MutationData S T) : Prop :=
  MutationObjUniqueAt D M ∧ MutationMorUniqueAt D M ∧ MutationCompatAt D M ∧
    MutationIdentityAt D M

end Mutations

/-- Definition 3.3 (i): `M` is a mutation: its formulas satisfy the proviso of page 68 and the
conditions (a), (b) hold in every model. -/
def IsMutation {S T : SpeciesData} (M : MutationData S T) : Prop :=
  SpeciesAbsolute.{u} M.mutObjFormula ∧ SpeciesAbsolute.{u} M.mutMorFormula ∧
    ∀ D : Set ZFSet.{u}, IsSpeciesModel D → MutationAxiomsAt D M

section MutationFunctor

variable {D : Set ZFSet.{u}} {S T : SpeciesData} {M : MutationData S T}

/-- The species-object `𝔐(X)`. -/
noncomputable def mutationObjAt (hM : MutationAxiomsAt D M) (X : SpeciesObjAt D S) :
    Fin T.objArity → ZFSet.{u} :=
  Classical.choose (hM.1 X.1 X.2).exists

theorem mutationObjAt_spec (hM : MutationAxiomsAt D M) (X : SpeciesObjAt D S) :
    mutationObjRel D M X.1 (mutationObjAt hM X) :=
  Classical.choose_spec (hM.1 X.1 X.2).exists

/-- The species-morphism `𝔐(f)`. -/
noncomputable def mutationMorAt (hM : MutationAxiomsAt D M) {X Y : SpeciesObjAt D S}
    (f : SpeciesHomAt D S X Y) : Fin T.morArity → ZFSet.{u} :=
  Classical.choose
    (hM.2.1 X.1 Y.1 f.1 _ _ f.2 (mutationObjAt_spec hM X) (mutationObjAt_spec hM Y)).exists

theorem mutationMorAt_spec (hM : MutationAxiomsAt D M) {X Y : SpeciesObjAt D S}
    (f : SpeciesHomAt D S X Y) :
    mutationMorRel D M X.1 Y.1 f.1 (mutationObjAt hM X) (mutationObjAt hM Y)
      (mutationMorAt hM f) :=
  Classical.choose_spec
    (hM.2.1 X.1 Y.1 f.1 _ _ f.2 (mutationObjAt_spec hM X) (mutationObjAt_spec hM Y)).exists

/-- The species-object `𝔐(X)`, as an object of the category determined by `𝔖̲`. -/
noncomputable def mutationObjPt (hM : MutationAxiomsAt D M) (X : SpeciesObjAt D S) :
    SpeciesObjAt D T :=
  ⟨mutationObjAt hM X, (mutationObjAt_spec hM X).1⟩

/-- The species-morphism `𝔐(f)`, as an arrow of the category determined by `𝔖̲`. -/
noncomputable def mutationHomPt (hM : MutationAxiomsAt D M) {X Y : SpeciesObjAt D S}
    (f : SpeciesHomAt D S X Y) : SpeciesHomAt D T (mutationObjPt hM X) (mutationObjPt hM Y) :=
  ⟨mutationMorAt hM f, (mutationMorAt_spec hM f).2.2.1⟩

/-- Definition 3.3 (i), "In particular": in a fixed model a mutation determines a functor from
the category determined by `𝔖` to the category determined by `𝔖̲`. -/
noncomputable def mutationFunctorAt (hS : SpeciesAxiomsAt D S) (hT : SpeciesAxiomsAt D T)
    (hM : MutationAxiomsAt D M) :
    @CategoryTheory.Functor (SpeciesObjAt D S) (speciesCategoryAt hS) (SpeciesObjAt D T)
      (speciesCategoryAt hT) :=
  letI := speciesCategoryAt hS
  letI := speciesCategoryAt hT
  { obj := fun X => mutationObjPt hM X
    map := fun f => mutationHomPt hM f
    map_id := fun X => by
      apply Subtype.ext
      exact speciesIdentity_unique hT.1
        (hM.2.2.2 _ _ _ _ (speciesIdAt_spec hS X)
          (mutationMorAt_spec hM (CategoryTheory.CategoryStruct.id X)))
        (speciesIdAt_spec hT (mutationObjPt hM X))
    map_comp := fun f g => by
      apply Subtype.ext
      exact (speciesCompAt_eq hT (mutationHomPt hM f) (mutationHomPt hM g)
        (hM.2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ (speciesCompAt_spec hS f g) (mutationMorAt_spec hM f)
          (mutationMorAt_spec hM g)
          (mutationMorAt_spec hM (CategoryTheory.CategoryStruct.comp f g)))).symm }

end MutationFunctor

/-! ## Definition 3.3 (ii): morphisms of mutations -/

/-- A morphism of mutations `ℨ : 𝔐 → 𝔐'` between mutations `𝔖 ⇝ 𝔖̲` (Definition 3.3 (ii),
page 73): a formula `Ξ(E, F̲)`. -/
structure MutationMorphismData (S T : SpeciesData) where
  /-- The formula `Ξ(E, F̲)`. -/
  mmFormula : speciesLang.Formula (Fin S.objArity ⊕ Fin T.morArity)

section MutationMorphisms

variable (D : Set ZFSet.{u}) {S T : SpeciesData}

/-- `G = ℨ(E) : 𝔐(E) → 𝔐'(E)` in the model `D`. -/
def mutationMorphismRel (M M' : MutationData S T) (Z : MutationMorphismData S T)
    (E : Fin S.objArity → ZFSet.{u}) (A B : Fin T.objArity → ZFSet.{u})
    (G : Fin T.morArity → ZFSet.{u}) : Prop :=
  mutationObjRel D M E A ∧ mutationObjRel D M' E B ∧ oneSpecimen D T A B G ∧
    speciesHolds D Z.mmFormula (Sum.elim E G)

/-- Definition 3.3 (ii) (a) in the model `D`: for every `E ∈ 𝔖₀` there is a unique
`F̲ : 𝔐(E) → 𝔐'(E)` in `𝔖̲₁` with `Ξ(E, F̲)`. -/
def MutationMorphismUniqueAt (M M' : MutationData S T) (Z : MutationMorphismData S T) :
    Prop :=
  ∀ E A B, zeroSpecimen D S.spZero E → mutationObjRel D M E A → mutationObjRel D M' E B →
    ∃! G, mutationMorphismRel D M M' Z E A B G

/-- Definition 3.3 (ii) (b) in the model `D`: for every species-morphism `F : E₁ → E₂`,
`𝔐'(F) ∘ ℨ(E₁) = ℨ(E₂) ∘ 𝔐(F)`. -/
def MutationMorphismNaturalAt (M M' : MutationData S T) (Z : MutationMorphismData S T) :
    Prop :=
  ∀ E₁ E₂ F A₁ A₂ B₁ B₂ N N' G₁ G₂ H₁ H₂,
    oneSpecimen D S E₁ E₂ F → mutationMorRel D M E₁ E₂ F A₁ A₂ N →
    mutationMorRel D M' E₁ E₂ F B₁ B₂ N' → mutationMorphismRel D M M' Z E₁ A₁ B₁ G₁ →
    mutationMorphismRel D M M' Z E₂ A₂ B₂ G₂ →
    speciesComposite D T A₁ B₁ B₂ G₁ N' H₁ → speciesComposite D T A₁ A₂ B₂ N G₂ H₂ → H₁ = H₂

end MutationMorphisms

/-- Definition 3.3 (ii): `Z` is a morphism of mutations `M → M'`. -/
def IsMutationMorphism {S T : SpeciesData} (M M' : MutationData S T)
    (Z : MutationMorphismData S T) : Prop :=
  SpeciesAbsolute.{u} Z.mmFormula ∧ ∀ D : Set ZFSet.{u}, IsSpeciesModel D →
    MutationMorphismUniqueAt D M M' Z ∧ MutationMorphismNaturalAt D M M' Z

/-- Definition 3.3 (ii): `Z` is an isomorphism of mutations: a morphism of mutations with
`ℨ(E)` a species-isomorphism for every species-object `E`. -/
def IsMutationIso {S T : SpeciesData} (M M' : MutationData S T)
    (Z : MutationMorphismData S T) : Prop :=
  IsMutationMorphism.{u} M M' Z ∧ ∀ D : Set ZFSet.{u}, IsSpeciesModel D →
    ∀ E A B G, zeroSpecimen D S.spZero E → mutationMorphismRel D M M' Z E A B G →
      SpeciesIsIsoAt D T A B G

section MutationNatTrans

variable {D : Set ZFSet.{u}} {S T : SpeciesData} {M M' : MutationData S T}
  {Z : MutationMorphismData S T}

/-- The species-morphism `ℨ(X) : 𝔐(X) → 𝔐'(X)`. -/
noncomputable def mutationMorphismAt (hM : MutationAxiomsAt D M) (hM' : MutationAxiomsAt D M')
    (hZ : MutationMorphismUniqueAt D M M' Z) (X : SpeciesObjAt D S) :
    Fin T.morArity → ZFSet.{u} :=
  Classical.choose
    (hZ X.1 _ _ X.2 (mutationObjAt_spec hM X) (mutationObjAt_spec hM' X)).exists

theorem mutationMorphismAt_spec (hM : MutationAxiomsAt D M) (hM' : MutationAxiomsAt D M')
    (hZ : MutationMorphismUniqueAt D M M' Z) (X : SpeciesObjAt D S) :
    mutationMorphismRel D M M' Z X.1 (mutationObjAt hM X) (mutationObjAt hM' X)
      (mutationMorphismAt hM hM' hZ X) :=
  Classical.choose_spec
    (hZ X.1 _ _ X.2 (mutationObjAt_spec hM X) (mutationObjAt_spec hM' X)).exists

/-- The species-morphism `ℨ(X) : 𝔐(X) → 𝔐'(X)`, as an arrow of the category determined by
`𝔖̲`. -/
noncomputable def mutationMorphismPt (hM : MutationAxiomsAt D M) (hM' : MutationAxiomsAt D M')
    (hZ : MutationMorphismUniqueAt D M M' Z) (X : SpeciesObjAt D S) :
    SpeciesHomAt D T (mutationObjPt hM X) (mutationObjPt hM' X) :=
  ⟨mutationMorphismAt hM hM' hZ X, (mutationMorphismAt_spec hM hM' hZ X).2.2.1⟩

/-- Definition 3.3 (ii) (b), "In particular": in a fixed model a morphism of mutations
determines a natural transformation between the functors determined by `M` and `M'`. -/
noncomputable def mutationNatTransAt (hS : SpeciesAxiomsAt D S) (hT : SpeciesAxiomsAt D T)
    (hM : MutationAxiomsAt D M) (hM' : MutationAxiomsAt D M')
    (hZ : MutationMorphismUniqueAt D M M' Z) (hZn : MutationMorphismNaturalAt D M M' Z) :
    @CategoryTheory.NatTrans (SpeciesObjAt D S) (speciesCategoryAt hS) (SpeciesObjAt D T)
      (speciesCategoryAt hT) (mutationFunctorAt hS hT hM) (mutationFunctorAt hS hT hM') :=
  letI := speciesCategoryAt hS
  letI := speciesCategoryAt hT
  { app := fun X => mutationMorphismPt hM hM' hZ X
    naturality := fun X Y f => by
      apply Subtype.ext
      exact (hZn X.1 Y.1 f.1 _ _ _ _ _ _ _ _ _ _ f.2 (mutationMorAt_spec hM f)
        (mutationMorAt_spec hM' f) (mutationMorphismAt_spec hM hM' hZ X)
        (mutationMorphismAt_spec hM hM' hZ Y)
        (speciesCompAt_spec hT (mutationMorphismPt hM hM' hZ X) (mutationHomPt hM' f))
        (speciesCompAt_spec hT (mutationHomPt hM f) (mutationMorphismPt hM hM' hZ Y))).symm }

end MutationNatTrans

/-! ## Composition of mutations and identity mutations (the "evident notions" of page 73) -/

/-- The identity mutation of `S`: `Ψ₀(E, E̲)` is `E = E̲` and `Ψ₁(E, E', F, F̲)` is `F = F̲`,
coordinatewise. A choice made in this file. -/
noncomputable def mutationIdentity (S : SpeciesData) : MutationData S S where
  mutObjFormula := FirstOrder.Language.Formula.iInf fun i : Fin S.objArity =>
    FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inl i))
      (FirstOrder.Language.Term.var (Sum.inr i))
  mutMorFormula := FirstOrder.Language.Formula.iInf fun i : Fin S.morArity =>
    FirstOrder.Language.Term.equal
      (FirstOrder.Language.Term.var (Sum.inr (Sum.inr (Sum.inl i))))
      (FirstOrder.Language.Term.var (Sum.inr (Sum.inr (Sum.inr i))))

/-- The composite mutation `𝔑 ∘ 𝔐 : 𝔖 ⇝ 𝔘` of `𝔐 : 𝔖 ⇝ 𝔗` and `𝔑 : 𝔗 ⇝ 𝔘`:
`Ψ₀(E, C)` is `∃ B, Φ₀^𝔗(B) ∧ Ψ₀^𝔐(E, B) ∧ Ψ₀^𝔑(B, C)`, and `Ψ₁(E, E', F, H)` is
`∃ B B' G, Φ₀^𝔗(B) ∧ Φ₀^𝔗(B') ∧ Φ₁^𝔗(B, B', G) ∧ Ψ₀^𝔐(E, B) ∧ Ψ₀^𝔐(E', B') ∧
Ψ₁^𝔐(E, E', F, G) ∧ Ψ₁^𝔑(B, B', G, H)`. A choice made in this file. The object formula
does not require `Φ₀(E)`, and the morphism formula does not require `Φ₀(E)`, `Φ₀(E')`,
`Φ₁(E, E', F)`; the composite with these conditions is `saMutationComp` of
`IUT.PaperIV.SpeciesAbsoluteness`. -/
noncomputable def mutationAfter {S T U : SpeciesData} (N : MutationData T U)
    (M : MutationData S T) : MutationData S U where
  mutObjFormula := FirstOrder.Language.Formula.iExs (Fin T.objArity)
    (FirstOrder.Language.Formula.relabel Sum.inr T.spZero.zsFormula ⊓
      FirstOrder.Language.Formula.relabel (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr)
        M.mutObjFormula ⊓
      FirstOrder.Language.Formula.relabel (Sum.elim Sum.inr (Sum.inl ∘ Sum.inr))
        N.mutObjFormula)
  mutMorFormula :=
    let e₁ : Fin S.objArity → _ := fun i => Sum.inl (Sum.inl i)
    let e₂ : Fin S.objArity → _ := fun i => Sum.inl (Sum.inr (Sum.inl i))
    let f : Fin S.morArity → _ := fun i => Sum.inl (Sum.inr (Sum.inr (Sum.inl i)))
    let h : Fin U.morArity → _ := fun i => Sum.inl (Sum.inr (Sum.inr (Sum.inr i)))
    let b₁ : Fin T.objArity → _ := fun i => Sum.inr (Sum.inl i)
    let b₂ : Fin T.objArity → _ := fun i => Sum.inr (Sum.inr (Sum.inl i))
    let g : Fin T.morArity → _ := fun i => Sum.inr (Sum.inr (Sum.inr i))
    FirstOrder.Language.Formula.iExs (Fin T.objArity ⊕ Fin T.objArity ⊕ Fin T.morArity)
      (FirstOrder.Language.Formula.relabel b₁ T.spZero.zsFormula ⊓
        FirstOrder.Language.Formula.relabel b₂ T.spZero.zsFormula ⊓
        FirstOrder.Language.Formula.relabel (Sum.elim b₁ (Sum.elim b₂ g)) T.spOne.osFormula ⊓
        FirstOrder.Language.Formula.relabel (Sum.elim e₁ b₁) M.mutObjFormula ⊓
        FirstOrder.Language.Formula.relabel (Sum.elim e₂ b₂) M.mutObjFormula ⊓
        FirstOrder.Language.Formula.relabel (Sum.elim e₁ (Sum.elim e₂ (Sum.elim f g)))
          M.mutMorFormula ⊓
        FirstOrder.Language.Formula.relabel (Sum.elim b₁ (Sum.elim b₂ (Sum.elim g h)))
          N.mutMorFormula)

section FormulaLemmas

variable {D : Set ZFSet.{u}}

theorem speciesHolds_mem {α : Type*} {φ : speciesLang.Formula α} {x : α → ZFSet.{u}}
    (h : speciesHolds D φ x) : ∀ a, x a ∈ D :=
  h.1

theorem speciesHolds_relabel {α β : Type*} (g : α → β) (φ : speciesLang.Formula α)
    {x : β → ZFSet.{u}} (hx : ∀ b, x b ∈ D) :
    speciesHolds D (FirstOrder.Language.Formula.relabel g φ) x ↔ speciesHolds D φ (x ∘ g) := by
  let _ := speciesStructure D
  constructor
  · rintro ⟨_, h⟩
    rw [FirstOrder.Language.Formula.realize_relabel] at h
    exact ⟨fun a => hx (g a), h⟩
  · rintro ⟨_, h⟩
    exact ⟨hx, by rw [FirstOrder.Language.Formula.realize_relabel]; exact h⟩

theorem speciesHolds_inf {α : Type*} (φ ψ : speciesLang.Formula α) (x : α → ZFSet.{u}) :
    speciesHolds D (φ ⊓ ψ) x ↔ speciesHolds D φ x ∧ speciesHolds D ψ x := by
  let _ := speciesStructure D
  constructor
  · rintro ⟨hx, h⟩
    rw [FirstOrder.Language.Formula.realize_inf] at h
    exact ⟨⟨hx, h.1⟩, ⟨hx, h.2⟩⟩
  · rintro ⟨⟨hx, h₁⟩, ⟨_, h₂⟩⟩
    exact ⟨hx, by rw [FirstOrder.Language.Formula.realize_inf]; exact ⟨h₁, h₂⟩⟩

theorem speciesHolds_iExs {α β : Type*} [Finite β] (φ : speciesLang.Formula (α ⊕ β))
    {x : α → ZFSet.{u}} (hx : ∀ a, x a ∈ D) :
    speciesHolds D (FirstOrder.Language.Formula.iExs β φ) x ↔
      ∃ y : β → ZFSet.{u}, speciesHolds D φ (Sum.elim x y) := by
  let _ := speciesStructure D
  constructor
  · rintro ⟨_, h⟩
    rw [FirstOrder.Language.Formula.realize_iExs] at h
    obtain ⟨i, hi⟩ := h
    have hy : ∀ c, Sum.elim x (fun b => (i b).1) c ∈ D := by
      rintro (a | b)
      · exact hx a
      · exact (i b).2
    refine ⟨fun b => (i b).1, hy, ?_⟩
    have e : (fun c => (⟨Sum.elim x (fun b => (i b).1) c, hy c⟩ : D)) =
        Sum.elim (fun a => (⟨x a, hx a⟩ : D)) i := by
      funext c
      rcases c with a | b <;> rfl
    exact (congrArg (fun v : α ⊕ β → D => φ.Realize v) e).mpr hi
  · rintro ⟨y, hy, h⟩
    refine ⟨hx, ?_⟩
    rw [FirstOrder.Language.Formula.realize_iExs]
    refine ⟨fun b => ⟨y b, hy (Sum.inr b)⟩, ?_⟩
    have e : Sum.elim (fun a => (⟨x a, hx a⟩ : D)) (fun b => ⟨y b, hy (Sum.inr b)⟩) =
        fun c => (⟨Sum.elim x y c, hy c⟩ : D) := by
      funext c
      rcases c with a | b <;> rfl
    exact (congrArg (fun v : α ⊕ β → D => φ.Realize v) e).mpr h

/-- The object formula of a composite mutation means what its docstring says. -/
theorem mutationAfter_obj_holds {S T U : SpeciesData} (N : MutationData T U)
    (M : MutationData S T) (E : Fin S.objArity → ZFSet.{u}) (C : Fin U.objArity → ZFSet.{u})
    (hE : ∀ i, E i ∈ D) (hC : ∀ i, C i ∈ D) :
    speciesHolds D (mutationAfter N M).mutObjFormula (Sum.elim E C) ↔
      ∃ B, zeroSpecimen D T.spZero B ∧ speciesHolds D M.mutObjFormula (Sum.elim E B) ∧
        speciesHolds D N.mutObjFormula (Sum.elim B C) := by
  have hEC : ∀ a, Sum.elim E C a ∈ D := by
    rintro (a | a)
    · exact hE a
    · exact hC a
  have e₀ : ∀ B : Fin T.objArity → ZFSet.{u},
      Sum.elim (Sum.elim E C) B ∘ Sum.inr = B := fun B => rfl
  have e₁ : ∀ B : Fin T.objArity → ZFSet.{u},
      Sum.elim (Sum.elim E C) B ∘ Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr = Sum.elim E B := by
    intro B; funext c; rcases c with a | a <;> rfl
  have e₂ : ∀ B : Fin T.objArity → ZFSet.{u},
      Sum.elim (Sum.elim E C) B ∘ Sum.elim Sum.inr (Sum.inl ∘ Sum.inr) = Sum.elim B C := by
    intro B; funext c; rcases c with a | a <;> rfl
  change speciesHolds D (FirstOrder.Language.Formula.iExs (Fin T.objArity) _) _ ↔ _
  rw [speciesHolds_iExs _ hEC]
  constructor
  · rintro ⟨B, h⟩
    have hm := speciesHolds_mem h
    rw [speciesHolds_inf, speciesHolds_inf, speciesHolds_relabel _ _ hm,
      speciesHolds_relabel _ _ hm, speciesHolds_relabel _ _ hm, e₀, e₁, e₂] at h
    exact ⟨B, h.1.1, h.1.2, h.2⟩
  · rintro ⟨B, h₁, h₂, h₃⟩
    have hB := speciesHolds_mem h₁
    have hm : ∀ a, Sum.elim (Sum.elim E C) B a ∈ D := by
      rintro ((a | a) | a)
      · exact hE a
      · exact hC a
      · exact hB a
    refine ⟨B, ?_⟩
    rw [speciesHolds_inf, speciesHolds_inf, speciesHolds_relabel _ _ hm,
      speciesHolds_relabel _ _ hm, speciesHolds_relabel _ _ hm, e₀, e₁, e₂]
    exact ⟨⟨h₁, h₂⟩, h₃⟩

theorem mutationIdentity_obj_holds (S : SpeciesData)
    (x : Fin S.objArity ⊕ Fin S.objArity → ZFSet.{u}) :
    speciesHolds D (mutationIdentity S).mutObjFormula x ↔
      (∀ a, x a ∈ D) ∧ ∀ i, x (Sum.inl i) = x (Sum.inr i) := by
  let _ := speciesStructure D
  constructor
  · rintro ⟨hx, h⟩
    simp only [mutationIdentity, FirstOrder.Language.Formula.realize_iInf] at h
    refine ⟨hx, fun i => ?_⟩
    have := h i
    rw [FirstOrder.Language.Formula.realize_equal] at this
    exact congrArg Subtype.val this
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    simp only [mutationIdentity, FirstOrder.Language.Formula.realize_iInf]
    intro i
    rw [FirstOrder.Language.Formula.realize_equal]
    exact Subtype.ext (h i)

theorem mutationIdentity_mor_holds (S : SpeciesData)
    (x : Fin S.objArity ⊕ Fin S.objArity ⊕ Fin S.morArity ⊕ Fin S.morArity → ZFSet.{u}) :
    speciesHolds D (mutationIdentity S).mutMorFormula x ↔
      (∀ a, x a ∈ D) ∧
        ∀ i, x (Sum.inr (Sum.inr (Sum.inl i))) = x (Sum.inr (Sum.inr (Sum.inr i))) := by
  let _ := speciesStructure D
  constructor
  · rintro ⟨hx, h⟩
    simp only [mutationIdentity, FirstOrder.Language.Formula.realize_iInf] at h
    refine ⟨hx, fun i => ?_⟩
    have := h i
    rw [FirstOrder.Language.Formula.realize_equal] at this
    exact congrArg Subtype.val this
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    simp only [mutationIdentity, FirstOrder.Language.Formula.realize_iInf]
    intro i
    rw [FirstOrder.Language.Formula.realize_equal]
    exact Subtype.ext (h i)

end FormulaLemmas

section IdentityMutation

variable {D : Set ZFSet.{u}} {S : SpeciesData}

theorem mutationIdentity_objRel_iff (E A : Fin S.objArity → ZFSet.{u}) :
    mutationObjRel D (mutationIdentity S) E A ↔ zeroSpecimen D S.spZero A ∧ E = A ∧
      ∀ i, E i ∈ D := by
  unfold mutationObjRel
  rw [mutationIdentity_obj_holds]
  constructor
  · rintro ⟨hA, hx, h⟩
    exact ⟨hA, funext h, fun i => hx (Sum.inl i)⟩
  · rintro ⟨hA, rfl, hE⟩
    exact ⟨hA, by rintro (a | a) <;> exact hE a, fun _ => rfl⟩

theorem mutationIdentity_morRel_iff (E E' : Fin S.objArity → ZFSet.{u})
    (F : Fin S.morArity → ZFSet.{u}) (A A' : Fin S.objArity → ZFSet.{u})
    (G : Fin S.morArity → ZFSet.{u}) :
    mutationMorRel D (mutationIdentity S) E E' F A A' G ↔
      E = A ∧ E' = A' ∧ F = G ∧ oneSpecimen D S A A' G := by
  unfold mutationMorRel
  rw [mutationIdentity_objRel_iff, mutationIdentity_objRel_iff, mutationIdentity_mor_holds]
  constructor
  · rintro ⟨⟨_, rfl, _⟩, ⟨_, rfl, _⟩, hG, _, h⟩
    exact ⟨rfl, rfl, funext h, hG⟩
  · rintro ⟨rfl, rfl, rfl, hG⟩
    have hm := speciesHolds_mem hG.2.2
    refine ⟨⟨hG.1, rfl, fun i => hm (Sum.inl i)⟩, ⟨hG.2.1, rfl, fun i => hm (Sum.inr (Sum.inl i))⟩,
      hG, ?_, fun _ => rfl⟩
    rintro (a | a | a | a)
    exacts [hm (Sum.inl a), hm (Sum.inr (Sum.inl a)), hm (Sum.inr (Sum.inr a)),
      hm (Sum.inr (Sum.inr a))]

/-- The identity mutation of a species is a mutation (in every model of `IsSpeciesModel`, and its
formulas satisfy the proviso of page 68). -/
theorem isMutation_mutationIdentity : IsMutation.{u} (mutationIdentity S) := by
  refine ⟨?_, ?_, fun D _ => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro V W _ hW hVW x hx
    rw [mutationIdentity_obj_holds, mutationIdentity_obj_holds]
    exact ⟨fun h => ⟨fun a => hW.transitive V hVW _ (hx a), h.2⟩, fun h => ⟨hx, h.2⟩⟩
  · intro V W _ hW hVW x hx
    rw [mutationIdentity_mor_holds, mutationIdentity_mor_holds]
    exact ⟨fun h => ⟨fun a => hW.transitive V hVW _ (hx a), h.2⟩, fun h => ⟨hx, h.2⟩⟩
  · intro E hE
    refine ⟨E, (mutationIdentity_objRel_iff E E).2 ⟨hE, rfl, speciesHolds_mem hE⟩, ?_⟩
    intro A hA
    exact ((mutationIdentity_objRel_iff E A).1 hA).2.1.symm
  · intro E E' F A A' hF hA hA'
    obtain ⟨_, rfl, _⟩ := (mutationIdentity_objRel_iff E A).1 hA
    obtain ⟨_, rfl, _⟩ := (mutationIdentity_objRel_iff E' A').1 hA'
    refine ⟨F, (mutationIdentity_morRel_iff _ _ _ _ _ _).2 ⟨rfl, rfl, rfl, hF⟩, ?_⟩
    intro G hG
    exact ((mutationIdentity_morRel_iff _ _ _ _ _ _).1 hG).2.2.1.symm
  · intro E E' E'' F F' F'' A A' A'' G G' G'' hc h₁ h₂ h₃
    obtain ⟨rfl, rfl, rfl, _⟩ := (mutationIdentity_morRel_iff _ _ _ _ _ _).1 h₁
    obtain ⟨-, rfl, rfl, _⟩ := (mutationIdentity_morRel_iff _ _ _ _ _ _).1 h₂
    obtain ⟨-, -, rfl, _⟩ := (mutationIdentity_morRel_iff _ _ _ _ _ _).1 h₃
    exact hc
  · intro E I A J hI h
    obtain ⟨rfl, -, rfl, _⟩ := (mutationIdentity_morRel_iff _ _ _ _ _ _).1 h
    exact hI

end IdentityMutation

/-! ## Definition 3.3 (iii): mutation-equivalences -/

/-- Definition 3.3 (iii): `M : 𝔖 ⇝ 𝔖̲` is a mutation-equivalence: there is a mutation
`M' : 𝔖̲ ⇝ 𝔖` with isomorphisms of mutations from the composites `M' ∘ M` and `M ∘ M'` to the
identity mutations. -/
def IsMutationEquivalence {S T : SpeciesData} (M : MutationData S T) : Prop :=
  IsMutation.{u} M ∧ ∃ M' : MutationData T S, IsMutation.{u} M' ∧
    (∃ Z, IsMutationIso.{u} (mutationAfter M' M) (mutationIdentity S) Z) ∧
    (∃ Z', IsMutationIso.{u} (mutationAfter M M') (mutationIdentity T) Z')

/-- `M` and `M'` are mutation-quasi-inverses (Definition 3.3 (iii)). -/
def AreMutationQuasiInverses {S T : SpeciesData} (M : MutationData S T)
    (M' : MutationData T S) : Prop :=
  IsMutation.{u} M ∧ IsMutation.{u} M' ∧
    (∃ Z, IsMutationIso.{u} (mutationAfter M' M) (mutationIdentity S) Z) ∧
    (∃ Z', IsMutationIso.{u} (mutationAfter M M') (mutationIdentity T) Z')

/-! ## Definition 3.3 (iv): mutation-histories -/

section Histories

open IUT.Prerequisites

/-- In the oriented graph given by the semi-graph `G` and the choice `first e` of a first
branch of each edge, the edge `e` runs from `v₁` to `v₂`: its first branch abuts to `v₁` and
its other branch abuts to `v₂`. -/
def OrientedEdgeRunsFrom (G : SemiGraph.{w}) (first : G.Edge → G.Branch) (e : G.Edge)
    (v₁ v₂ : G.Vertex) : Prop :=
  G.edgeOf (first e) = e ∧ G.coincidence (first e) = some v₁ ∧
    ∃ b, G.edgeOf b = e ∧ b ≠ first e ∧ G.coincidence b = some v₂

/-- A mutation-history indexed by an oriented graph whose underlying graph is `G`
(Definition 3.3 (iv), page 74): the ordering of the branches of each edge (by the choice of a
first branch), a species `𝔖^v` for each vertex, and a mutation `𝔐^e : 𝔖^{v₁} ⇝ 𝔖^{v₂}` for each
edge running from `v₁` to `v₂`. -/
structure MutationHistoryData (G : SemiGraph.{w}) where
  /-- The first branch of each edge (the total ordering of its two branches). -/
  mhFirst : G.Edge → G.Branch
  /-- The species `𝔖^v` at each vertex. -/
  mhSpecies : G.Vertex → SpeciesData
  /-- The vertex an edge runs from. -/
  mhSource : G.Edge → G.Vertex
  /-- The vertex an edge runs to. -/
  mhTarget : G.Edge → G.Vertex
  /-- The mutation `𝔐^e` at each edge. -/
  mhMutation : (e : G.Edge) → MutationData (mhSpecies (mhSource e)) (mhSpecies (mhTarget e))

/-- `H` is a mutation-history: `G` is a graph, each edge runs from `mhSource e` to
`mhTarget e` for the chosen orientation, each `𝔖^v` is a species and each `𝔐^e` a mutation. -/
def IsMutationHistory {G : SemiGraph.{w}} (H : MutationHistoryData G) : Prop :=
  G.IsGraph ∧ (∀ e, OrientedEdgeRunsFrom G H.mhFirst e (H.mhSource e) (H.mhTarget e)) ∧
    (∀ v, IsSpecies.{u} (H.mhSpecies v)) ∧ ∀ e, IsMutation.{u} (H.mhMutation e)

/-- The underlying graph is simply connected: no edge is a loop and the incidence graph is a
tree (see the module docstring for this reading). -/
def IsSimplyConnectedGraph (G : SemiGraph.{w}) : Prop :=
  G.incidenceGraph.IsTree ∧
    ∀ b b', G.edgeOf b = G.edgeOf b' → b ≠ b' → G.coincidence b ≠ G.coincidence b'

/-! ## Definition 3.3 (v): observables and cores -/

/-- An `𝔖̲`-valued observable of the mutation-history `H` (Definition 3.3 (v), page 74): an
observation mutation `𝔙^v : 𝔖^v ⇝ 𝔖̲` at each vertex and a morphism of mutations `𝔙^e` at each
edge. -/
structure ObservableData {G : SemiGraph.{w}} (H : MutationHistoryData G) (T : SpeciesData) where
  /-- The observation mutation `𝔙^v`. -/
  obsMutation : (v : G.Vertex) → MutationData (H.mhSpecies v) T
  /-- The morphism of mutations `𝔙^e`. -/
  obsMorphism : (e : G.Edge) → MutationMorphismData (H.mhSpecies (H.mhSource e)) T

/-- A covariant observable: `𝔙^e : 𝔙^{v₁} → 𝔙^{v₂} ∘ 𝔐^e` for each edge from `v₁` to `v₂`. -/
def IsCovariantObservable {G : SemiGraph.{w}} {H : MutationHistoryData G} {T : SpeciesData}
    (O : ObservableData H T) : Prop :=
  IsSimplyConnectedGraph G ∧ IsMutationHistory.{u} H ∧ IsSpecies.{u} T ∧
    (∀ v, IsMutation.{u} (O.obsMutation v)) ∧
    ∀ e, IsMutationMorphism.{u} (O.obsMutation (H.mhSource e))
      (mutationAfter (O.obsMutation (H.mhTarget e)) (H.mhMutation e)) (O.obsMorphism e)

/-- A contravariant observable: `𝔙^e : 𝔙^{v₂} ∘ 𝔐^e → 𝔙^{v₁}` for each edge from `v₁` to `v₂`. -/
def IsContravariantObservable {G : SemiGraph.{w}} {H : MutationHistoryData G}
    {T : SpeciesData} (O : ObservableData H T) : Prop :=
  IsSimplyConnectedGraph G ∧ IsMutationHistory.{u} H ∧ IsSpecies.{u} T ∧
    (∀ v, IsMutation.{u} (O.obsMutation v)) ∧
    ∀ e, IsMutationMorphism.{u} (mutationAfter (O.obsMutation (H.mhTarget e)) (H.mhMutation e))
      (O.obsMutation (H.mhSource e)) (O.obsMorphism e)

/-- A core: a covariant observable all of whose `𝔙^e` are isomorphisms of mutations. -/
def IsCore {G : SemiGraph.{w}} {H : MutationHistoryData G} {T : SpeciesData}
    (O : ObservableData H T) : Prop :=
  IsCovariantObservable.{u} O ∧
    ∀ e, IsMutationIso.{u} (O.obsMutation (H.mhSource e))
      (mutationAfter (O.obsMutation (H.mhTarget e)) (H.mhMutation e)) (O.obsMorphism e)

end Histories

/-! ## Example: a species with one species-object (Remark 3.1.1) -/

/-- The species whose only species-object is `(∅)` and whose only species-morphism is `(∅)`:
`Φ₀(E) = (∀ x ∈ E₁, ⊥)`, `Φ₁(E, E', F) = (∀ x ∈ F₁, ⊥)`, `Φ₁∘₁ = ⊤`. -/
abbrev pointSpecies : SpeciesData where
  spZero := { zsArity := 1, zsFormula := speciesBall (Sum.inl 0) ⊥ }
  spOne :=
    { osArity := 1
      osFormula := speciesBall (Sum.inl (Sum.inr (Sum.inr 0))) ⊥
      osCompFormula := ⊤ }

section PointSpecies

variable {D : Set ZFSet.{u}}

theorem speciesHolds_ballEmpty {α : Type*} (htr : ∀ x ∈ D, ∀ y ∈ x, y ∈ D) (a : α)
    (x : α → ZFSet.{u}) :
    speciesHolds D (speciesBall (Sum.inl a) ⊥ : speciesLang.Formula α) x ↔
      (∀ b, x b ∈ D) ∧ x a = ∅ := by
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    have h' := (speciesBall_realize D (Sum.inl a) ⊥ (fun b => ⟨x b, hx b⟩) default).1 h
    apply ZFSet.ext
    intro z
    exact ⟨fun hz => False.elim (h' ⟨z, htr _ (hx a) _ hz⟩ hz),
      fun hz => absurd hz (ZFSet.notMem_empty z)⟩
  · rintro ⟨hx, h⟩
    refine ⟨hx, (speciesBall_realize D (Sum.inl a) ⊥ (fun b => ⟨x b, hx b⟩) default).2 ?_⟩
    intro y hy
    have hy' : y.1 ∈ x a := hy
    rw [h] at hy'
    exact absurd hy' (ZFSet.notMem_empty _)

theorem speciesHolds_top {α : Type*} (x : α → ZFSet.{u}) :
    speciesHolds D (⊤ : speciesLang.Formula α) x ↔ ∀ a, x a ∈ D := by
  let _ := speciesStructure D
  constructor
  · rintro ⟨hx, _⟩; exact hx
  · intro hx; exact ⟨hx, by rw [FirstOrder.Language.Formula.realize_top]; trivial⟩

theorem pointTuple_eq (x : Fin 1 → ZFSet.{u}) (h : x 0 = ∅) : x = fun _ => ∅ :=
  funext fun i => by rw [Subsingleton.elim i 0]; exact h

theorem pointSpecies_zeroFormula_holds (htr : ∀ x ∈ D, ∀ y ∈ x, y ∈ D)
    (E : Fin 1 → ZFSet.{u}) :
    speciesHolds D pointSpecies.spZero.zsFormula E ↔ (∀ b, E b ∈ D) ∧ E 0 = ∅ :=
  speciesHolds_ballEmpty htr 0 E

theorem pointSpecies_oneFormula_holds (htr : ∀ x ∈ D, ∀ y ∈ x, y ∈ D)
    (E E' F : Fin 1 → ZFSet.{u}) :
    speciesHolds D pointSpecies.spOne.osFormula (Sum.elim E (Sum.elim E' F)) ↔
      (∀ b, Sum.elim E (Sum.elim E' F) b ∈ D) ∧ F 0 = ∅ :=
  speciesHolds_ballEmpty htr (Sum.inr (Sum.inr 0)) (Sum.elim E (Sum.elim E' F))

theorem pointSpecies_compFormula_holds
    (x : (Fin 1 ⊕ Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1 ⊕ Fin 1) → ZFSet.{u}) :
    speciesHolds D pointSpecies.spOne.osCompFormula x ↔ ∀ a, x a ∈ D :=
  speciesHolds_top x

theorem pointSpecies_zeroSpecimen_iff (htr : ∀ x ∈ D, ∀ y ∈ x, y ∈ D)
    (E : Fin 1 → ZFSet.{u}) :
    zeroSpecimen D pointSpecies.spZero E ↔ (∅ : ZFSet.{u}) ∈ D ∧ E = fun _ => ∅ := by
  unfold zeroSpecimen
  rw [pointSpecies_zeroFormula_holds htr]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨h ▸ hx 0, pointTuple_eq E h⟩
  · rintro ⟨h0, rfl⟩
    exact ⟨fun _ => h0, rfl⟩

theorem pointSpecies_oneSpecimen_iff (htr : ∀ x ∈ D, ∀ y ∈ x, y ∈ D)
    (E E' F : Fin 1 → ZFSet.{u}) :
    oneSpecimen D pointSpecies E E' F ↔
      (∅ : ZFSet.{u}) ∈ D ∧ E = (fun _ => ∅) ∧ E' = (fun _ => ∅) ∧ F = fun _ => ∅ := by
  unfold oneSpecimen
  rw [pointSpecies_zeroSpecimen_iff htr, pointSpecies_zeroSpecimen_iff htr,
    pointSpecies_oneFormula_holds htr]
  constructor
  · rintro ⟨⟨h0, rfl⟩, ⟨-, rfl⟩, -, h⟩
    exact ⟨h0, rfl, rfl, pointTuple_eq F h⟩
  · rintro ⟨h0, rfl, rfl, rfl⟩
    refine ⟨⟨h0, rfl⟩, ⟨h0, rfl⟩, ?_, rfl⟩
    rintro (a | a | a) <;> exact h0

theorem pointSpecies_composite_iff (htr : ∀ x ∈ D, ∀ y ∈ x, y ∈ D)
    (E E' E'' F F' F'' : Fin 1 → ZFSet.{u}) :
    speciesComposite D pointSpecies E E' E'' F F' F'' ↔
      (∅ : ZFSet.{u}) ∈ D ∧ E = (fun _ => ∅) ∧ E' = (fun _ => ∅) ∧ E'' = (fun _ => ∅) ∧
        F = (fun _ => ∅) ∧ F' = (fun _ => ∅) ∧ F'' = fun _ => ∅ := by
  unfold speciesComposite
  rw [pointSpecies_oneSpecimen_iff htr, pointSpecies_oneSpecimen_iff htr,
    pointSpecies_oneSpecimen_iff htr, pointSpecies_compFormula_holds]
  constructor
  · rintro ⟨⟨h0, rfl, rfl, rfl⟩, ⟨-, -, rfl, rfl⟩, ⟨-, -, -, rfl⟩, -⟩
    exact ⟨h0, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨h0, rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨⟨h0, rfl, rfl, rfl⟩, ⟨h0, rfl, rfl, rfl⟩, ⟨h0, rfl, rfl, rfl⟩, ?_⟩
    rintro ((a | a | a) | (a | a | a)) <;> exact h0

/-- In a transitive model containing `∅`, the 1-specimen `(∅)` is the identity of `(∅)`. -/
theorem pointSpecies_isIdentityAt (htr : ∀ x ∈ D, ∀ y ∈ x, y ∈ D) (h0 : (∅ : ZFSet.{u}) ∈ D) :
    SpeciesIsIdentityAt D pointSpecies (fun _ => ∅) (fun _ => ∅) := by
  refine ⟨(pointSpecies_oneSpecimen_iff htr _ _ _).2 ⟨h0, rfl, rfl, rfl⟩, ?_, ?_⟩
  · intro E' F' hF'
    obtain ⟨-, rfl, -, rfl⟩ := (pointSpecies_oneSpecimen_iff htr _ _ _).1 hF'
    exact (pointSpecies_composite_iff htr _ _ _ _ _ _).2 ⟨h0, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro E'' F'' hF''
    obtain ⟨-, -, rfl, rfl⟩ := (pointSpecies_oneSpecimen_iff htr _ _ _).1 hF''
    exact (pointSpecies_composite_iff htr _ _ _ _ _ _).2 ⟨h0, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- In a transitive model, the species `pointSpecies` satisfies conditions (c), (d), (e) of
Definition 3.1 (ii). -/
theorem pointSpecies_axiomsAt (htr : ∀ x ∈ D, ∀ y ∈ x, y ∈ D) :
    SpeciesAxiomsAt D pointSpecies := by
  refine ⟨?_, ?_, ?_⟩
  · intro E E' E'' F F' hF hF'
    rw [pointSpecies_oneSpecimen_iff htr] at hF hF'
    obtain ⟨h0, rfl, rfl, rfl⟩ := hF
    obtain ⟨-, -, rfl, rfl⟩ := hF'
    refine ⟨fun _ => ∅, (pointSpecies_composite_iff htr _ _ _ _ _ _).2
      ⟨h0, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    intro G hG
    exact ((pointSpecies_composite_iff htr _ _ _ _ _ _).1 hG).2.2.2.2.2.2
  · intro E₁ E₂ E₃ E₄ F₁ F₂ F₃ G H G' H' _ h₂ _ h₄
    rw [((pointSpecies_composite_iff htr _ _ _ _ _ _).1 h₂).2.2.2.2.2.2,
      ((pointSpecies_composite_iff htr _ _ _ _ _ _).1 h₄).2.2.2.2.2.2]
  · intro E hE
    rw [pointSpecies_zeroSpecimen_iff htr] at hE
    obtain ⟨h0, rfl⟩ := hE
    exact ⟨fun _ => ∅, pointSpecies_isIdentityAt htr h0⟩

theorem pointSpecies_zeroFormula_delta0 : IsSpeciesDelta0 pointSpecies.spZero.zsFormula :=
  IsSpeciesDelta0.ball _ IsSpeciesDelta0.falsum

theorem pointSpecies_oneFormula_delta0 : IsSpeciesDelta0 pointSpecies.spOne.osFormula :=
  IsSpeciesDelta0.ball _ IsSpeciesDelta0.falsum

theorem pointSpecies_compFormula_delta0 : IsSpeciesDelta0 pointSpecies.spOne.osCompFormula :=
  IsSpeciesDelta0.imp IsSpeciesDelta0.falsum IsSpeciesDelta0.falsum

/-- `pointSpecies` is a species: its formulas satisfy the proviso of page 68 (they have bounded
quantifiers) and conditions (c), (d), (e) hold in every model of `IsSpeciesModel`. -/
theorem pointSpecies_isSpecies : IsSpecies.{u} pointSpecies :=
  ⟨⟨le_rfl, speciesAbsolute_of_delta0 pointSpecies_zeroFormula_delta0⟩,
    le_rfl, speciesAbsolute_of_delta0 pointSpecies_oneFormula_delta0,
    speciesAbsolute_of_delta0 pointSpecies_compFormula_delta0,
    fun _ hD => pointSpecies_axiomsAt (isSpeciesModel_transitive hD)⟩

theorem pointSpecies_isZeroSmall : IsZeroSmall.{u} pointSpecies.spZero := by
  intro D hD
  refine ⟨ZFSet.powerset ∅, isSpeciesModel_powerset_empty_mem hD, fun E _ => ?_⟩
  rw [pointSpecies_zeroSpecimen_iff (isSpeciesModel_transitive hD)]
  show _ ↔ E 0 ∈ ZFSet.powerset ∅
  rw [ZFSet.mem_powerset]
  constructor
  · rintro ⟨-, rfl⟩; exact fun _ hz => hz
  · intro hsub
    refine ⟨isSpeciesModel_empty_mem hD, pointTuple_eq E ?_⟩
    exact ZFSet.ext fun z => ⟨fun hz => hsub hz, fun hz => absurd hz (ZFSet.notMem_empty z)⟩

theorem pointSpecies_isOneSmall : IsOneSmall.{u} pointSpecies := by
  intro D hD E E' hE hE'
  have htr := isSpeciesModel_transitive hD
  refine ⟨ZFSet.powerset ∅, isSpeciesModel_powerset_empty_mem hD, fun F _ => ?_⟩
  rw [pointSpecies_oneSpecimen_iff htr]
  rw [pointSpecies_zeroSpecimen_iff htr] at hE hE'
  show _ ↔ F 0 ∈ ZFSet.powerset ∅
  rw [ZFSet.mem_powerset]
  constructor
  · rintro ⟨-, -, -, rfl⟩; exact fun _ hz => hz
  · intro hsub
    refine ⟨hE.1, hE.2, hE'.2, pointTuple_eq F ?_⟩
    exact ZFSet.ext fun z => ⟨fun hz => hsub hz, fun hz => absurd hz (ZFSet.notMem_empty z)⟩

/-- In every model of `IsSpeciesModel` (in particular in the ambient model `ZFSet.{u}`),
`pointSpecies` has exactly one species-object. -/
theorem pointSpecies_existsUnique_object (hD : IsSpeciesModel D) :
    ∃! E, zeroSpecimen D pointSpecies.spZero E := by
  have htr := isSpeciesModel_transitive hD
  refine ⟨fun _ => ∅, (pointSpecies_zeroSpecimen_iff htr _).2
    ⟨isSpeciesModel_empty_mem hD, rfl⟩, fun E hE => ?_⟩
  exact ((pointSpecies_zeroSpecimen_iff htr E).1 hE).2

/-- The defining formula `Φ₀` of `pointSpecies` is a model-free description of its
species-object (Definition 3.1 (iii) and Remark 3.1.1). -/
theorem pointSpecies_modelFree :
    IsModelFreeZeroSpecimen.{u} pointSpecies pointSpecies.spZero.zsFormula := by
  intro V₁ V₂ hV₁ hV₂ _
  have h₁ : IsSpeciesModel {y | y ∈ V₁} := Or.inr ⟨V₁, hV₁, rfl⟩
  have h₂ : IsSpeciesModel {y | y ∈ V₂} := Or.inr ⟨V₂, hV₂, rfl⟩
  refine ⟨fun _ => ∅, (pointSpecies_zeroSpecimen_iff (isSpeciesModel_transitive h₁) _).2
    ⟨isSpeciesModel_empty_mem h₁, rfl⟩, (pointSpecies_zeroSpecimen_iff
    (isSpeciesModel_transitive h₂) _).2 ⟨isSpeciesModel_empty_mem h₂, rfl⟩, fun x => ?_,
    fun x => ?_⟩
  · have := pointSpecies_zeroSpecimen_iff (isSpeciesModel_transitive h₁) x
    unfold zeroSpecimen at this
    rw [this]
    exact ⟨fun h => h.2, fun h => ⟨isSpeciesModel_empty_mem h₁, h⟩⟩
  · have := pointSpecies_zeroSpecimen_iff (isSpeciesModel_transitive h₂) x
    unfold zeroSpecimen at this
    rw [this]
    exact ⟨fun h => h.2, fun h => ⟨isSpeciesModel_empty_mem h₂, h⟩⟩

/-- The identity mutation of `pointSpecies` is a mutation. -/
theorem pointSpecies_isMutation_identity : IsMutation.{u} (mutationIdentity pointSpecies) :=
  isMutation_mutationIdentity

/-- The morphism of mutations into `pointSpecies` whose formula `Ξ` is `⊤`. -/
abbrev pointMorphism (S : SpeciesData) : MutationMorphismData S pointSpecies := ⟨⊤⟩

/-- For any formula collections `M`, `M'` from `S` to `pointSpecies`, `pointMorphism S` is an
isomorphism of mutations `M → M'` (Definition 3.3 (ii)). -/
theorem isMutationIso_toPoint {S : SpeciesData} (M M' : MutationData S pointSpecies) :
    IsMutationIso.{u} M M' (pointMorphism S) := by
  have habs : SpeciesAbsolute.{u} (pointMorphism S).mmFormula :=
    speciesAbsolute_of_delta0 (IsSpeciesDelta0.imp IsSpeciesDelta0.falsum IsSpeciesDelta0.falsum)
  have hrel : ∀ D : Set ZFSet.{u}, IsSpeciesModel D → ∀ E A B G,
      mutationMorphismRel D M M' (pointMorphism S) E A B G →
        (∅ : ZFSet.{u}) ∈ D ∧ A = (fun _ => ∅) ∧ B = (fun _ => ∅) ∧ G = fun _ => ∅ :=
    fun D hD _ A B G h => (pointSpecies_oneSpecimen_iff (isSpeciesModel_transitive hD) A B G).1
      h.2.2.1
  refine ⟨⟨habs, fun D hD => ⟨?_, ?_⟩⟩, fun D hD E A B G _ h => ?_⟩
  · intro E A B hE hA hB
    have htr := isSpeciesModel_transitive hD
    obtain ⟨h0, rfl⟩ := (pointSpecies_zeroSpecimen_iff htr A).1 hA.1
    obtain ⟨-, rfl⟩ := (pointSpecies_zeroSpecimen_iff htr B).1 hB.1
    refine ⟨fun _ => ∅, ⟨hA, hB, (pointSpecies_oneSpecimen_iff htr _ _ _).2
      ⟨h0, rfl, rfl, rfl⟩, (speciesHolds_top _).2 ?_⟩,
      fun G hG => (hrel D hD _ _ _ _ hG).2.2.2⟩
    rintro (a | a)
    · exact speciesHolds_mem hE a
    · exact h0
  · intro E₁ E₂ F A₁ A₂ B₁ B₂ N N' G₁ G₂ H₁ H₂ _ _ _ _ _ h₁ h₂
    have htr := isSpeciesModel_transitive hD
    rw [((pointSpecies_composite_iff htr _ _ _ _ _ _).1 h₁).2.2.2.2.2.2,
      ((pointSpecies_composite_iff htr _ _ _ _ _ _).1 h₂).2.2.2.2.2.2]
  · have htr := isSpeciesModel_transitive hD
    have hG := h.2.2.1
    obtain ⟨h0, rfl, rfl, rfl⟩ := hrel D hD E A B G h
    have hc := (pointSpecies_composite_iff htr (fun _ => ∅) (fun _ => ∅) (fun _ => ∅)
      (fun _ => ∅) (fun _ => ∅) (fun _ => ∅)).2 ⟨h0, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨hG, fun _ => ∅, hG, ⟨fun _ => ∅, hc, pointSpecies_isIdentityAt htr h0⟩,
      ⟨fun _ => ∅, hc, pointSpecies_isIdentityAt htr h0⟩⟩

/-- The identity mutation of `pointSpecies` is a mutation-equivalence (Definition 3.3 (iii)),
with itself as mutation-quasi-inverse. -/
theorem pointSpecies_isMutationEquivalence_identity :
    IsMutationEquivalence.{u} (mutationIdentity pointSpecies) :=
  ⟨isMutation_mutationIdentity, mutationIdentity pointSpecies, isMutation_mutationIdentity,
    ⟨pointMorphism _, isMutationIso_toPoint _ _⟩, ⟨pointMorphism _, isMutationIso_toPoint _ _⟩⟩

/-- The mutation-history on `G`, with the orientation `first` and edges running from `s e` to
`t e`, that has `pointSpecies` at every vertex and the identity mutation at every edge. -/
noncomputable abbrev pointHistory (G : IUT.Prerequisites.SemiGraph.{w}) (first : G.Edge → G.Branch)
    (s t : G.Edge → G.Vertex) : MutationHistoryData G where
  mhFirst := first
  mhSpecies := fun _ => pointSpecies
  mhSource := s
  mhTarget := t
  mhMutation := fun _ => mutationIdentity pointSpecies

/-- The `pointSpecies`-valued observable of `pointHistory` with identity observation mutations
and the morphisms `pointMorphism`. -/
noncomputable abbrev pointObservable (G : IUT.Prerequisites.SemiGraph.{w})
    (first : G.Edge → G.Branch) (s t : G.Edge → G.Vertex) :
    ObservableData (pointHistory G first s t) pointSpecies where
  obsMutation := fun _ => mutationIdentity pointSpecies
  obsMorphism := fun _ => pointMorphism pointSpecies

/-- On a simply connected graph with an orientation, `pointObservable` is a core
(Definition 3.3 (v)). -/
theorem pointObservable_isCore (G : IUT.Prerequisites.SemiGraph.{w}) (first : G.Edge → G.Branch)
    (s t : G.Edge → G.Vertex) (hsc : IsSimplyConnectedGraph G) (hG : G.IsGraph)
    (hor : ∀ e, OrientedEdgeRunsFrom G first e (s e) (t e)) :
    IsCore.{u} (pointObservable G first s t) :=
  ⟨⟨hsc, ⟨hG, hor, fun _ => pointSpecies_isSpecies, fun _ => isMutation_mutationIdentity⟩,
    pointSpecies_isSpecies, fun _ => isMutation_mutationIdentity,
    fun _ => (isMutationIso_toPoint _ _).1⟩, fun _ => isMutationIso_toPoint _ _⟩

/-- The semi-graph with one vertex and no edge. -/
abbrev pointGraph : IUT.Prerequisites.SemiGraph.{0} where
  Vertex := Unit
  Edge := Empty
  Branch := Empty
  edgeOf := Empty.elim
  card_branches_eq_two := fun e => e.elim
  coincidence := Empty.elim

theorem pointGraph_isSimplyConnected : IsSimplyConnectedGraph pointGraph := by
  have : Subsingleton pointGraph.SemiGraphComponent := ⟨fun x y => by
    rcases x with x | x <;> rcases y with y | y
    · rfl
    · exact Empty.elim y
    · exact Empty.elim x
    · exact Empty.elim x⟩
  refine ⟨⟨?_, SimpleGraph.IsAcyclic.of_subsingleton⟩, fun b => b.elim⟩
  refine IUT.Prerequisites.SemiGraph.connected_of_forall_reachable (.inl ()) ?_
  intro x
  obtain rfl := Subsingleton.elim x (.inl ())
  exact SimpleGraph.Reachable.refl _

/-- `pointObservable` on `pointGraph` is a core. -/
theorem pointGraph_isCore :
    IsCore.{u} (pointObservable pointGraph Empty.elim (fun _ => ()) fun _ => ()) :=
  pointObservable_isCore pointGraph _ _ _ pointGraph_isSimplyConnected (fun e => e.elim)
    fun e => e.elim

end PointSpecies

end IUT.PaperIV.Species
