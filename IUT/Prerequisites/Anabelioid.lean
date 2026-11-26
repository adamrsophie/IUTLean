import Mathlib
import IUT.Prerequisites.SemiGraph

/-!
# Connected anabelioids and semi-graphs of anabelioids

Sources:
* Mochizuki, *The Geometry of Anabelioids*, Section 1.1, PDF pages 9 and 10 (pages 9, 10 and 11
  read for this file and checked against rendered images): the category `B(G)` of finite sets
  with continuous `G`-action for a profinite group `G` (page 9), Definition 1.1.1 (connected
  anabelioid), Remark 1.1.1.1, Definition 1.1.2 (morphisms, isomorphisms, basepoints and
  fundamental groups of connected anabelioids), Remarks 1.1.2.1 to 1.1.2.3.
* Mochizuki, *Semi-graphs of Anabelioids*, Definition 2.1, PDF page 22 (pages 22 and 23 read
  for this file and checked against rendered images), and the definition of connected objects in
  Section 0, page 7 (read from the rendered image).
* *Comments on "Semi-graphs of Anabelioids"* (May 2020), read in full from the text layer;
  items (9) and (14) checked against rendered images (pages 3 and 7 of the comments). Item (9)
  says that the assertion in the second display of Remark 2.4.2 of *Semi-graphs of Anabelioids*
  is false as stated (Dehn twists give counterexamples), replaces it by a weaker assertion, and
  adds the hypothesis that every edge abuts to at least one vertex in the discussion that follows
  it; item (14) corrects
  "underlying graph" to "underlying semi-graph" in Definition 2.4 (iii). Neither Remark 2.4.2 nor
  Definition 2.4 is formalized here, so no corrected statement enters this file; Remark 2.4.2
  concerns morphisms of semi-graphs of anabelioids, which are not formalized (see below).

*Inter-universal Teichmüller Theory I*, Section 2 (pages 44 and 45, read from rendered images),
works with a semi-graph of anabelioids `𝒢` and the semi-graph of anabelioids attached to a
connected sub-semi-graph; Propositions 2.1 and 2.2 are stated in that notation. This file supplies
the definition. It proves no numbered result of the papers.

## What is formalized

* `FiniteGSets G`: the category `B(G)` of finite sets with continuous action of a profinite group
  `G`, built as Mathlib's `ContAction FintypeCat G` (finite sets with the discrete topology).
* `finiteGSets_galoisCategory`: `B(G)` is a Galois category in the sense of Mathlib
  (`CategoryTheory.GaloisCategory`), proved by Mathlib.
* `IsConnectedAnabelioid`: Definition 1.1.1, a category equivalent to some `B(G)`.
* `isConnectedAnabelioid_of_galoisCategory`: every Galois category in the sense of Mathlib is a
  connected anabelioid, which is one direction of Remark 1.1.1.1; it is proved from Mathlib's
  equivalence of a Galois category with the finite continuous `Aut F`-sets of a fiber functor.
* `AnabelioidMorphism`, `AnabelioidMorphism.IsIsomorphism`, `AnabelioidBasepoint`,
  `basepointFundamentalGroup`: Definition 1.1.2.
* `connectedObjectSubcategory`: the full subcategory of connected objects, with connectedness
  taken from Mathlib (`PreGaloisCategory.IsConnected`).
* `ConnectedAnabelioid` and `SemiGraphOfAnabelioids`: Definition 2.1 of *Semi-graphs of
  Anabelioids*, with a nonvacuity example `constantSemiGraphOfAnabelioids`.

## Interpretation choices, recorded

* Universes. The paper works in a fixed Grothendieck universe `V` with a `V`-small category of
  finite sets. Here `B(G)` for `G : ProfiniteGrp.{u}` uses `FintypeCat.{w}`, and the predicate
  `IsConnectedAnabelioid.{u, w}` fixes both universe levels; a category is a connected anabelioid
  at those levels.
* Exact functors. Page 9 defines an exact functor as one preserving finite limits and finite
  colimits; this is Mathlib's `ExactFunctor` (`C ⥤ₑ D`). A morphism `X → Y` of connected
  anabelioids is an exact functor `Y ⥤ₑ X` (Definition 1.1.2 (i)); `AnabelioidMorphism X Y` is
  that type for any two categories, and is used here only between connected anabelioids.
  The paper takes the 2-categorical point of view (Remark 1.1.2.1): morphisms are considered up to
  isomorphism of functors. No composition or 2-categorical structure is defined here.
* Connected objects. *Semi-graphs of Anabelioids*, page 7, calls a nonempty (non-initial) object
  connected when it is not isomorphic to a coproduct of two nonempty objects. Mathlib's
  `PreGaloisCategory.IsConnected` (Lenstra's definition) asks that the object be not initial and
  have no subobject other than itself and initial ones. That the two notions agree in a Galois
  category is not proved here.
* Definition 2.1 (c) asks for a morphism `b_* : 𝒢_e → 𝒢_v` for each branch `b` of `e` abutting
  to a vertex `v`; this is `branchMorphism b v h`, an exact functor `𝒢_v ⥤ₑ 𝒢_e`.

## Not formalized (open)

* The converse direction of Remark 1.1.1.1 (a connected anabelioid is a Galois category): Mathlib
  has no transport of `GaloisCategory` along an equivalence of categories.
* The recovery of `G` up to inner automorphism as `Aut(β*)` (page 9), the uniqueness of fundamental
  functors up to isomorphism (page 9), independence of `π₁` of the basepoint (Remark 1.1.2.2), and
  Proposition 1.1.4. These are reconstruction and uniqueness results and are not stated.
* Anabelioids that are not connected, Example 1.1.3, and the rest of *The Geometry of
  Anabelioids*.
* From *Semi-graphs of Anabelioids* Section 2: morphisms of semi-graphs of anabelioids (called
  "evident" on page 22), semi-graphs of anabelioids of injective type (`π₁`-monomorphisms),
  the category `B(𝒢)`, the groups `Π_𝔾`, `Π_v`, `Π_b`, Remark 2.4.2 and its corrected form, and
  everything after Definition 2.1.
-/

namespace IUT.Prerequisites

open CategoryTheory

/-- The category `B(G)` of finite sets with continuous action of a profinite group `G`
(*The Geometry of Anabelioids*, page 9), as Mathlib's category of finite sets with the discrete
topology and continuous `G`-action. The discrete topology on finite types is Mathlib's scoped
instance of the namespace `FintypeCatDiscrete`, named explicitly here instead of opening that
namespace. -/
abbrev FiniteGSets.{u, w} (G : ProfiniteGrp.{u}) : Type (max u (w + 1)) :=
  @ContAction FintypeCat.{w} _ _ _ _ _
    FintypeCatDiscrete.instHasForget₂FintypeCatFunObjFiniteTopCatContinuousMapCarrier G _ _

/-- `B(G)` is a Galois category in the sense of Mathlib (*The Geometry of Anabelioids*, page 9,
"a rather special kind of topos called a Galois category"). The proof is Mathlib's. -/
theorem finiteGSets_galoisCategory.{u, w} (G : ProfiniteGrp.{u}) :
    GaloisCategory (FiniteGSets.{u, w} G) :=
  inferInstance

/-- A connected anabelioid (*The Geometry of Anabelioids*, Definition 1.1.1): a category
equivalent to `B(G)` for some profinite group `G`. -/
def IsConnectedAnabelioid.{u, w, u₁, v₁} (X : Type u₁) [Category.{v₁} X] : Prop :=
  ∃ G : ProfiniteGrp.{u}, Nonempty (X ≌ FiniteGSets.{u, w} G)

/-- `B(G)` is a connected anabelioid. -/
theorem finiteGSets_isConnectedAnabelioid.{u, w} (G : ProfiniteGrp.{u}) :
    IsConnectedAnabelioid.{u, w} (FiniteGSets.{u, w} G) :=
  ⟨G, ⟨CategoryTheory.Equivalence.refl⟩⟩

/-- Every Galois category in the sense of Mathlib is a connected anabelioid: one direction of
Remark 1.1.1.1 of *The Geometry of Anabelioids*. The profinite group is the automorphism group of
a fiber functor, and the equivalence is Mathlib's `PreGaloisCategory.functorToContAction`. -/
theorem isConnectedAnabelioid_of_galoisCategory.{u₁, u₂} (C : Type u₁) [Category.{u₂} C]
    [GaloisCategory C] : IsConnectedAnabelioid.{max u₁ u₂, u₂} C :=
  ⟨ProfiniteGrp.of (Aut (GaloisCategory.getFiberFunctor C)),
    ⟨(PreGaloisCategory.functorToContAction (GaloisCategory.getFiberFunctor C)).asEquivalence⟩⟩

/-- A morphism `X → Y` of connected anabelioids (*The Geometry of Anabelioids*,
Definition 1.1.2 (i)): an exact functor `Y ⥤ X`, that is, one preserving finite limits and finite
colimits. -/
abbrev AnabelioidMorphism.{u₁, v₁, u₂, v₂} (X : Type u₁) [Category.{v₁} X] (Y : Type u₂)
    [Category.{v₂} Y] :=
  Y ⥤ₑ X

/-- An isomorphism of connected anabelioids (Definition 1.1.2 (i)): a morphism whose functor in
the opposite direction is an equivalence of categories. -/
def AnabelioidMorphism.IsIsomorphism.{u₁, v₁, u₂, v₂} {X : Type u₁} [Category.{v₁} X] {Y : Type u₂}
    [Category.{v₂} Y] (φ : AnabelioidMorphism X Y) : Prop :=
  φ.obj.IsEquivalence

/-- A basepoint of a connected anabelioid `X` (Definition 1.1.2 (ii)): a morphism from the
category of finite sets to `X`, that is, an exact functor `X ⥤ FintypeCat`. -/
abbrev AnabelioidBasepoint.{w, u₁, v₁} (X : Type u₁) [Category.{v₁} X] :=
  AnabelioidMorphism FintypeCat.{w} X

/-- The fundamental group `π₁(X, β) = Aut(β)` of a connected anabelioid with a basepoint
(Definition 1.1.2 (ii)): the automorphisms of the functor underlying `β`. -/
abbrev basepointFundamentalGroup.{w, u₁, v₁} {X : Type u₁} [Category.{v₁} X]
    (β : AnabelioidBasepoint.{w, u₁, v₁} X) : Type (max u₁ w) :=
  Aut β.obj

/-- The full subcategory of connected objects, with Mathlib's notion of a connected object of a
Galois category (`PreGaloisCategory.IsConnected`). -/
abbrev connectedObjectSubcategory.{u₁, v₁} (X : Type u₁) [Category.{v₁} X] : Type _ :=
  ObjectProperty.FullSubcategory fun A : X => PreGaloisCategory.IsConnected A

/-- A connected anabelioid, bundled: a category together with the fact that it is a connected
anabelioid. -/
structure ConnectedAnabelioid.{u, w, u₁, v₁} where
  /-- The underlying category. -/
  underlyingCat : Cat.{v₁, u₁}
  /-- It is equivalent to some `B(G)`. -/
  isConnectedAnabelioid : IsConnectedAnabelioid.{u, w} underlyingCat

/-- A semi-graph of (connected) anabelioids (*Semi-graphs of Anabelioids*, Definition 2.1): a
semi-graph `𝔾`, a connected anabelioid `𝒢_v` for each vertex `v`, a connected anabelioid `𝒢_e`
for each edge `e`, and for each branch `b` of `e` abutting to a vertex `v` a morphism of
anabelioids `b_* : 𝒢_e → 𝒢_v`, that is, an exact functor `𝒢_v ⥤ 𝒢_e`. -/
structure SemiGraphOfAnabelioids.{u, w, u₁, v₁, u₃} (𝔾 : SemiGraph.{u₃}) where
  /-- The constituent anabelioid at a vertex. -/
  vertexAnabelioid : 𝔾.Vertex → ConnectedAnabelioid.{u, w, u₁, v₁}
  /-- The constituent anabelioid at an edge. -/
  edgeAnabelioid : 𝔾.Edge → ConnectedAnabelioid.{u, w, u₁, v₁}
  /-- The morphism `b_* : 𝒢_e → 𝒢_v` for a branch `b` of `e` abutting to `v`. -/
  branchMorphism : ∀ (b : 𝔾.Branch) (v : 𝔾.Vertex), 𝔾.coincidence b = some v →
    AnabelioidMorphism (edgeAnabelioid (𝔾.edgeOf b)).underlyingCat
      (vertexAnabelioid v).underlyingCat

/-- `B(G)` as a bundled connected anabelioid. -/
def finiteGSetsConnectedAnabelioid.{u, w} (G : ProfiniteGrp.{u}) :
    ConnectedAnabelioid.{u, w, max u (w + 1), w} where
  underlyingCat := Cat.of (FiniteGSets.{u, w} G)
  isConnectedAnabelioid := finiteGSets_isConnectedAnabelioid G

/-- Nonvacuity of Definition 2.1: on any semi-graph, the constant semi-graph of anabelioids with
every constituent anabelioid `B(G)` and every branch morphism the identity functor. -/
def constantSemiGraphOfAnabelioids.{u, w, u₃} (𝔾 : SemiGraph.{u₃}) (G : ProfiniteGrp.{u}) :
    SemiGraphOfAnabelioids.{u, w, max u (w + 1), w, u₃} 𝔾 where
  vertexAnabelioid := fun _ => finiteGSetsConnectedAnabelioid.{u, w} G
  edgeAnabelioid := fun _ => finiteGSetsConnectedAnabelioid.{u, w} G
  branchMorphism := fun _ _ _ =>
    ⟨𝟭 _, (exactFunctor_iff _).2 ⟨Limits.PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _,
      Limits.PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _⟩⟩

end IUT.Prerequisites
