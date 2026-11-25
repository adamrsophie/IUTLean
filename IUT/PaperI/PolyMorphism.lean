import Mathlib

/-!
# IUT I, Section 0: poly-morphisms and capsules

Source: Mochizuki, *Inter-universal Teichmüller Theory I*, Section 0 ("Notations and
Conventions"), subsection "Monoids and Categories", pages 33 and 34. Both pages were read as
rendered images for this file; every definition below was checked against those images.

These are the unnumbered definitions of poly-morphisms and capsules that the later sections of
IUT I to IV use throughout (for example, the radial data of IUT II, Example 1.8 (i), page 35,
read as a rendered image, include a full poly-isomorphism of topological groups `Π/Δ ⥲ G`). They are elementary and are stated here in full, for an arbitrary category
`C` of Mathlib.

## Definitions of page 33, stated in full

* A **poly-morphism** `A → B` is a collection of morphisms `A → B`, that is, a subset of the
  set of morphisms `A → B` (`PolyMorphism`). The page says "a subset"; the empty subset is
  allowed and no nonemptiness is imposed.
* It is a **poly-isomorphism** if all of its members are isomorphisms (`IsPolyIso`), and a
  **poly-automorphism** if moreover `A = B` (`IsPolyAut`).
* The **full poly-isomorphism** `A ⥲ B` is the poly-morphism consisting of all isomorphisms
  `A ⥲ B` (`fullPolyIso`).
* The **composite** of `{fᵢ : A → B}_{i ∈ I}` with `{g_j : B → C}_{j ∈ J}` is the set
  `{g_j ∘ fᵢ}_{(i,j) ∈ I × J}`, multiplicities ignored (`PolyMorphism.comp`). Mathlib writes
  composition in diagrammatic order, so `g_j ∘ fᵢ` is `fᵢ ≫ g_j`. Using sets realizes "the set
  [where multiplicities are ignored]".

## Definitions of pages 33 and 34

* A **capsule** of objects of `C` is a finite collection `{A_j}_{j ∈ J}` of objects indexed by a
  finite index set `J`; it is a `|J|`-capsule, and `π₀({A_j}) = J` (`Capsule`). The index set is
  a type with a `Fintype` instance.
* A **morphism of capsules** `{A_j}_{j ∈ J} → {A'_{j'}}_{j' ∈ J'}` is an injection
  `ι : J ↪ J'` together with a morphism `A_j → A'_{ι(j)}` for each `j` (`Capsule.Hom`).
  Composition and identities are given (`Capsule.Hom.comp`, `Capsule.Hom.id`).
  **Not done here:** the page states that capsules form a category `Capsule(C)`; the
  category laws are not proved in this file, so no `Category` instance is given.
* A **capsule-full poly-morphism** associated to a fixed injection `ι : J ↪ J'` is the set of
  capsule morphisms with that injection whose components are isomorphisms
  `A_j ⥲ A'_{ι(j)}` (`capsuleFullPolyMorphism`); it is a **capsule-full poly-isomorphism**
  when `ι` is a bijection. `IsCapsuleFullPolyIso` states only this bijectivity condition on
  `ι`, not the whole notion.

Nothing in this file is a theorem of the papers; the lemmas only record elementary properties
of the definitions.
-/

open CategoryTheory

namespace IUT.PaperI

universe v u

variable {C : Type u} [Category.{v} C]

/-! ### Poly-morphisms (page 33) -/

/-- IUT I, page 33: a **poly-morphism** `A → B` is a collection of morphisms `A → B`, that is,
a subset of the set of morphisms `A → B`. -/
abbrev PolyMorphism (A B : C) : Type v := Set (A ⟶ B)

/-- IUT I, page 33: a poly-morphism is a **poly-isomorphism** if all of the morphisms in the
collection are isomorphisms. -/
def IsPolyIso {A B : C} (S : PolyMorphism A B) : Prop :=
  ∀ f ∈ S, IsIso f

/-- IUT I, page 33: a poly-isomorphism `A ⥲ A` (with `A = B`) is a **poly-automorphism**. -/
def IsPolyAut {A : C} (S : PolyMorphism A A) : Prop :=
  IsPolyIso S

/-- IUT I, page 33: the **full poly-isomorphism** `A ⥲ B` is the poly-morphism given by the
collection of all isomorphisms `A ⥲ B`. -/
def fullPolyIso (A B : C) : PolyMorphism A B :=
  {f | IsIso f}

/-- IUT I, page 33: the composite of a poly-morphism `{fᵢ : A → B}` with a poly-morphism
`{g_j : B → C}` is the set `{g_j ∘ fᵢ}` (multiplicities ignored). In Mathlib's diagrammatic
notation `g_j ∘ fᵢ` is `fᵢ ≫ g_j`. -/
def PolyMorphism.comp {A B D : C} (S : PolyMorphism A B) (T : PolyMorphism B D) :
    PolyMorphism A D :=
  Set.image2 (fun f g => f ≫ g) S T

/-- The full poly-isomorphism is a poly-isomorphism. -/
theorem isPolyIso_fullPolyIso (A B : C) : IsPolyIso (fullPolyIso A B) :=
  fun _ hf => hf

/-- A poly-morphism is a poly-isomorphism if and only if it is contained in the full
poly-isomorphism. -/
theorem isPolyIso_iff_subset {A B : C} (S : PolyMorphism A B) :
    IsPolyIso S ↔ S ⊆ fullPolyIso A B :=
  Iff.rfl

/-- The composite of two poly-isomorphisms is a poly-isomorphism. -/
theorem IsPolyIso.comp {A B D : C} {S : PolyMorphism A B} {T : PolyMorphism B D}
    (hS : IsPolyIso S) (hT : IsPolyIso T) : IsPolyIso (S.comp T) := by
  rintro _ ⟨f, hf, g, hg, rfl⟩
  have := hS f hf
  have := hT g hg
  infer_instance

/-- Composition of poly-morphisms is associative. -/
theorem PolyMorphism.comp_assoc {A B D E : C} (S : PolyMorphism A B) (T : PolyMorphism B D)
    (U : PolyMorphism D E) : (S.comp T).comp U = S.comp (T.comp U) := by
  ext h
  simp only [PolyMorphism.comp, Set.mem_image2]
  constructor
  · rintro ⟨_, ⟨f, hf, g, hg, rfl⟩, k, hk, rfl⟩
    exact ⟨f, hf, g ≫ k, ⟨g, hg, k, hk, rfl⟩, (Category.assoc _ _ _).symm⟩
  · rintro ⟨f, hf, _, ⟨g, hg, k, hk, rfl⟩, rfl⟩
    exact ⟨f ≫ g, ⟨f, hf, g, hg, rfl⟩, k, hk, Category.assoc _ _ _⟩

/-! ### Capsules (pages 33 and 34) -/

variable (C) in
/-- IUT I, pages 33 and 34: a **capsule** of objects of `C` is a finite collection
`{A_j}_{j ∈ J}` of objects of `C` indexed by a finite index set `J`. -/
structure Capsule where
  /-- The index set `J = π₀({A_j}_{j ∈ J})`. -/
  index : Type
  /-- `J` is finite. -/
  [fintype : Fintype index]
  /-- The objects `A_j`. -/
  obj : index → C

attribute [instance] Capsule.fintype

namespace Capsule

/-- IUT I, page 34: `π₀({A_j}_{j ∈ J}) = J`. -/
abbrev π₀ (A : Capsule C) : Type := A.index

/-- IUT I, page 34: a capsule with index set `J` is a `|J|`-capsule. -/
def IsNCapsule (A : Capsule C) (n : ℕ) : Prop :=
  Fintype.card A.index = n

/-- IUT I, page 34: a **morphism of capsules** `{A_j}_{j ∈ J} → {A'_{j'}}_{j' ∈ J'}` consists
of an injection `ι : J ↪ J'` and, for each `j ∈ J`, a morphism `A_j → A'_{ι(j)}`. -/
structure Hom (A A' : Capsule C) where
  /-- The injection `ι : J ↪ J'`. -/
  ι : A.index ↪ A'.index
  /-- The morphisms `A_j → A'_{ι(j)}`. -/
  app : ∀ j, A.obj j ⟶ A'.obj (ι j)

/-- The identity morphism of a capsule. -/
def Hom.id (A : Capsule C) : Hom A A :=
  ⟨Function.Embedding.refl _, fun j => 𝟙 (A.obj j)⟩

/-- Composition of morphisms of capsules: compose the injections and the component
morphisms. -/
def Hom.comp {A A' A'' : Capsule C} (φ : Hom A A') (ψ : Hom A' A'') : Hom A A'' :=
  ⟨φ.ι.trans ψ.ι, fun j => φ.app j ≫ ψ.app (φ.ι j)⟩

/-- IUT I, page 34: the **capsule-full poly-morphism** `{A_j} → {A'_{j'}}` associated to a
fixed injection `ι : J ↪ J'` is the set of capsule morphisms with injection `ι` whose
components `A_j → A'_{ι(j)}` are isomorphisms. -/
def capsuleFullPolyMorphism (A A' : Capsule C) (ι : A.index ↪ A'.index) : Set (Hom A A') :=
  {φ | φ.ι = ι ∧ ∀ j, IsIso (φ.app j)}

/-- IUT I, page 34: a capsule-full poly-morphism is a **capsule-full poly-isomorphism** when
the associated injection between index sets is a bijection. -/
def IsCapsuleFullPolyIso {A A' : Capsule C} (ι : A.index ↪ A'.index) : Prop :=
  Function.Bijective ι

end Capsule

end IUT.PaperI
