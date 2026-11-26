import Mathlib

/-!
# Semi-graphs

Source: Mochizuki, *Semi-graphs of Anabelioids*, Section 1, PDF pages 11 to 14 (pages 11 to 14
read for this file and checked against rendered images). The errata
*Comments on "Semi-graphs of Anabelioids"* (May 2020) were read in full from the text layer, with
pages 3 and 7 of the comments checked against rendered images; none of its items
concerns the combinatorial notions of Section 1 formalized here. Items (9) and (14) concern
Section 2 and are recorded in `IUT/Prerequisites/Anabelioid.lean`; item (6) uses Lemma 1.8,
which is not formalized.

This file formalizes the purely combinatorial notion of a semi-graph recalled on page 11, and
the elementary notions defined on pages 11 to 14. It is a prerequisite for the semi-graphs of
anabelioids of Section 2 of the same paper. *Inter-universal Teichmüller Theory I*, pages 44 and
45 (read from rendered images), states Propositions 2.1 and 2.2 in terms of a semi-graph of
anabelioids, a connected sub-semi-graph and the maximal subgraph. This file proves no numbered
result of either paper.

## The definition on page 11 and its encoding

Page 11 defines a semi-graph as a set `𝒱` of vertices, a set `ℰ` of edges, each edge being a set
of cardinality two with distinct edges disjoint, and for each edge `e` a coincidence map
`ζ_e : e → 𝒱 ∪ {𝒱}`. The elements of an edge are its branches. Here the branches of all edges
form one type `Branch` with a map `edgeOf : Branch → Edge` whose every fiber has cardinality two;
an edge of the page is the fiber of `edgeOf` over it, and disjointness of distinct edges is
automatic. The value `𝒱` of `ζ_e` (a branch abutting to no vertex) is `none`, and a value
`v ∈ 𝒱` is `some v`. This is a reencoding of the same data, not a change of definition.
The page says that an edge has exactly two branches; a semi-graph is therefore not a Mathlib
`SimpleGraph` (it may have loops, multiple edges and edges with fewer than two vertices).

## What is formalized

* `SemiGraph`: the semi-graph (page 11).
* verticial cardinality, graphs, finite and countable semi-graphs, components, the relations
  "joins" and "abuts to" (page 11);
* morphisms of semi-graphs (page 11) with identity and composition, and the fact that a morphism
  does not decrease verticial cardinality (the last sentence of the morphism paragraph, page 11);
* the sub-semi-graph with given sets of vertices and edges (page 12, conditions (a) to (c)), with
  its inclusion morphism;
* closed, open and isolated edges, coverticial edges (pages 12 and 13); locally finite and
  untangled semi-graphs, joints (page 13);
* the maximal subgraph, which is proved to be a graph (page 13);
* the compactification, which is proved to be a graph, together with the morphism from the
  semi-graph to its compactification, under which a branch abuts to an old vertex exactly when it
  did before (page 13: "`𝔾` forms a sub-semi-graph of its compactification");
* immersions, excisions, proper morphisms and graph-coverings (pages 13 and 14);
* four small examples: a vertex with an open edge, a loop, two vertices joined by a closed edge,
  and a joint, with their properties.

## Interpretation choices, recorded

* Connectedness. The page calls a semi-graph connected through its associated topological space
  (page 11 and 12: a point for each vertex, an interval for each edge, glued along the coincidence
  maps). That space is not constructed here. A semi-graph is called connected here when its
  incidence graph (the simple graph on vertices and edges in which an edge is adjacent to each
  vertex it abuts to) is connected in the sense of Mathlib (`SimpleGraph.Connected`, which requires
  nonemptiness). Since every edge interval is connected and meets exactly the vertex points it
  abuts to, this is the connectedness of the topological space; that equivalence is not proved.
* Sub-semi-graphs. Conditions (b) and (c) of page 12 determine the coincidence maps of a
  sub-semi-graph from its sets of vertices and edges; `SemiGraph.subSemiGraph` builds the
  sub-semi-graph from those two sets, and its branches are the branches of `𝔾` lying on the chosen
  edges.
* Morphisms. The page asks for a bijection `e ≅ e'` for each edge `e ↦ e'`, equivalently an
  injection. The field `onBranch_injective_on_edge` asks for injectivity on each edge;
  `SemiGraph.Hom.branchesOver_bijective` proves bijectivity.

## Not formalized

The topological space of a semi-graph, trees (contractible spaces), the semi-graphs
`𝔾[v]`, `𝔾[e]`, `𝔾[b]` of page 13, embeddings, the deformation retraction statement and the
unique extension of morphisms to compactifications (page 13), Galois graph-coverings and
pull-backs (page 14), Proposition 1.1, Theorem 1.2 and the rest of Section 1.
-/

namespace IUT.Prerequisites

universe u

/-- A semi-graph (Mochizuki, *Semi-graphs of Anabelioids*, page 11): vertices, edges, and
branches, each edge having exactly two branches, with a coincidence map sending a branch to the
vertex it abuts to (`some v`) or to nothing (`none`). -/
structure SemiGraph where
  /-- The vertices. -/
  Vertex : Type u
  /-- The edges. -/
  Edge : Type u
  /-- The branches of all edges. -/
  Branch : Type u
  /-- The edge of which a branch is a branch. -/
  edgeOf : Branch → Edge
  /-- Every edge has exactly two branches. -/
  card_branches_eq_two : ∀ e : Edge, Nat.card {b : Branch // edgeOf b = e} = 2
  /-- The coincidence maps: the vertex a branch abuts to, or `none`. -/
  coincidence : Branch → Option Vertex

namespace SemiGraph

variable (G : SemiGraph.{u})

/-- The edge `e` abuts to the vertex `v`: some branch of `e` abuts to `v` (page 11). -/
def EdgeAbutsTo (e : G.Edge) (v : G.Vertex) : Prop :=
  ∃ b, G.edgeOf b = e ∧ G.coincidence b = some v

/-- The verticial cardinality of an edge: the number of its branches that abut to a vertex
(page 11). -/
noncomputable def verticialCard (e : G.Edge) : ℕ :=
  Nat.card {b : G.Branch // G.edgeOf b = e ∧ (G.coincidence b).isSome}

/-- A graph: a semi-graph all of whose edges have verticial cardinality two (page 11). -/
def IsGraph : Prop := ∀ e : G.Edge, G.verticialCard e = 2

/-- A finite semi-graph: finitely many vertices and edges (page 11). -/
def IsFiniteSemiGraph : Prop := Finite G.Vertex ∧ Finite G.Edge

/-- A countable semi-graph: countably many vertices and edges (page 11). -/
def IsCountableSemiGraph : Prop := Countable G.Vertex ∧ Countable G.Edge

/-- A component of a semi-graph: a vertex or an edge (page 11). -/
abbrev SemiGraphComponent : Type u := G.Vertex ⊕ G.Edge

/-- The edge `e` of verticial cardinality two joins `v₁` to `v₂`: its two branches abut to `v₁`
and to `v₂` (page 11). -/
def Joins (e : G.Edge) (v₁ v₂ : G.Vertex) : Prop :=
  G.verticialCard e = 2 ∧ ∃ b₁ b₂, b₁ ≠ b₂ ∧ G.edgeOf b₁ = e ∧ G.edgeOf b₂ = e ∧
    G.coincidence b₁ = some v₁ ∧ G.coincidence b₂ = some v₂

/-- A closed edge: verticial cardinality two (page 12). -/
def IsClosedEdge (e : G.Edge) : Prop := G.verticialCard e = 2

/-- An open edge: verticial cardinality less than two (page 12). -/
def IsOpenEdge (e : G.Edge) : Prop := G.verticialCard e < 2

/-- An isolated edge: verticial cardinality zero (page 12). -/
def IsIsolatedEdge (e : G.Edge) : Prop := G.verticialCard e = 0

/-- Two closed edges are coverticial when they abut to the same vertices (pages 12 and 13). -/
def AreCoverticial (e e' : G.Edge) : Prop :=
  G.IsClosedEdge e ∧ G.IsClosedEdge e' ∧ ∀ v, G.EdgeAbutsTo e v ↔ G.EdgeAbutsTo e' v

/-- Locally finite: finitely many edges abut to each vertex (page 13). -/
def IsLocallyFinite : Prop := ∀ v : G.Vertex, {e : G.Edge | G.EdgeAbutsTo e v}.Finite

/-- Untangled: every closed edge abuts to two distinct vertices (page 13). -/
def IsUntangled : Prop :=
  ∀ e : G.Edge, G.IsClosedEdge e → ∃ v₁ v₂, v₁ ≠ v₂ ∧ G.EdgeAbutsTo e v₁ ∧ G.EdgeAbutsTo e v₂

/-- The incidence relation on components: an edge is related to each vertex it abuts to. -/
def incidenceRel : G.SemiGraphComponent → G.SemiGraphComponent → Prop
  | .inl v, .inr e => G.EdgeAbutsTo e v
  | _, _ => False

/-- The incidence graph: the simple graph on components in which an edge is adjacent to each
vertex it abuts to. -/
def incidenceGraph : SimpleGraph G.SemiGraphComponent := SimpleGraph.fromRel G.incidenceRel

/-- A connected semi-graph: the incidence graph is connected (in particular nonempty). This
stands for the connectedness of the associated topological space; see the module docstring. -/
def IsConnectedSemiGraph : Prop := G.incidenceGraph.Connected

/-- A joint: a connected semi-graph with exactly one vertex and exactly two edges, both open
(page 13). -/
def IsJoint : Prop :=
  G.IsConnectedSemiGraph ∧ Nat.card G.Vertex = 1 ∧ Nat.card G.Edge = 2 ∧
    ∀ e : G.Edge, G.IsOpenEdge e

/-- The branches of an edge form a finite type. -/
lemma finite_branchesOver (e : G.Edge) : Finite {b : G.Branch // G.edgeOf b = e} :=
  Nat.finite_of_card_ne_zero (by rw [G.card_branches_eq_two e]; norm_num)

/-- The verticial cardinality is at most two. -/
lemma verticialCard_le_two (e : G.Edge) : G.verticialCard e ≤ 2 := by
  have := G.finite_branchesOver e
  rw [← G.card_branches_eq_two e]
  exact Nat.card_le_card_of_injective
    (fun b : {b : G.Branch // G.edgeOf b = e ∧ (G.coincidence b).isSome} => ⟨b.1, b.2.1⟩)
    (fun x y h => Subtype.ext (congrArg Subtype.val h :))

/-- In a graph, every edge abuts to at least one vertex (page 11). -/
lemma IsGraph.exists_edgeAbutsTo {G : SemiGraph.{u}} (h : G.IsGraph) (e : G.Edge) :
    ∃ v, G.EdgeAbutsTo e v := by
  have hc : G.verticialCard e ≠ 0 := by rw [h e]; norm_num
  obtain ⟨⟨b, hb, hs⟩⟩ := (Nat.card_ne_zero.mp hc).1
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
  exact ⟨v, b, hb, hv⟩

/-! ### Morphisms -/

/-- A morphism of semi-graphs (page 11): maps on vertices and edges, and for each edge `e ↦ e'`
an injection (hence bijection) from the branches of `e` to those of `e'`, compatible with the
verticial restrictions of the coincidence maps. -/
structure Hom (G H : SemiGraph.{u}) where
  /-- The map on vertices. -/
  onVertex : G.Vertex → H.Vertex
  /-- The map on edges. -/
  onEdge : G.Edge → H.Edge
  /-- The map on branches. -/
  onBranch : G.Branch → H.Branch
  /-- A branch of `e` goes to a branch of the image of `e`. -/
  edgeOf_onBranch : ∀ b, H.edgeOf (onBranch b) = onEdge (G.edgeOf b)
  /-- The map on the branches of each edge is injective. -/
  onBranch_injective_on_edge :
    ∀ b₁ b₂, G.edgeOf b₁ = G.edgeOf b₂ → onBranch b₁ = onBranch b₂ → b₁ = b₂
  /-- Compatibility with the verticial restrictions of the coincidence maps. -/
  coincidence_onBranch :
    ∀ b v, G.coincidence b = some v → H.coincidence (onBranch b) = some (onVertex v)

/-- The identity morphism of a semi-graph. -/
def homIdentity : Hom G G where
  onVertex := fun v => v
  onEdge := fun e => e
  onBranch := fun b => b
  edgeOf_onBranch := fun _ => rfl
  onBranch_injective_on_edge := fun _ _ _ h => h
  coincidence_onBranch := fun _ _ h => h

/-- Composition of morphisms of semi-graphs. -/
def homComp {G H K : SemiGraph.{u}} (φ : Hom G H) (ψ : Hom H K) : Hom G K where
  onVertex := fun v => ψ.onVertex (φ.onVertex v)
  onEdge := fun e => ψ.onEdge (φ.onEdge e)
  onBranch := fun b => ψ.onBranch (φ.onBranch b)
  edgeOf_onBranch := fun b => by rw [ψ.edgeOf_onBranch, φ.edgeOf_onBranch]
  onBranch_injective_on_edge := fun b₁ b₂ he h =>
    φ.onBranch_injective_on_edge b₁ b₂ he
      (ψ.onBranch_injective_on_edge _ _ (by rw [φ.edgeOf_onBranch, φ.edgeOf_onBranch, he]) h)
  coincidence_onBranch := fun b v h =>
    ψ.coincidence_onBranch _ _ (φ.coincidence_onBranch b v h)

/-- The map induced by a morphism from the branches of `e` to the branches of its image. -/
def Hom.branchesOver {G H : SemiGraph.{u}} (φ : Hom G H) (e : G.Edge) :
    {b : G.Branch // G.edgeOf b = e} → {b' : H.Branch // H.edgeOf b' = φ.onEdge e} :=
  fun b => ⟨φ.onBranch b.1, by rw [φ.edgeOf_onBranch, b.2]⟩

/-- A morphism induces a bijection from the branches of each edge to the branches of its image,
as page 11 requires. -/
lemma Hom.branchesOver_bijective {G H : SemiGraph.{u}} (φ : Hom G H) (e : G.Edge) :
    Function.Bijective (φ.branchesOver e) := by
  have := H.finite_branchesOver (φ.onEdge e)
  have hinj : Function.Injective (φ.branchesOver e) := fun x y h =>
    Subtype.ext (φ.onBranch_injective_on_edge _ _ (by rw [x.2, y.2])
      (congrArg Subtype.val h :))
  refine ⟨hinj, ?_⟩
  have := G.finite_branchesOver e
  exact (Function.Injective.bijective_of_nat_card_le hinj
    (by rw [G.card_branches_eq_two, H.card_branches_eq_two])).2

/-- A morphism does not decrease verticial cardinality: an edge abutting to `k` vertices maps to an
edge abutting to at least `k` vertices (page 11, last sentence of the paragraph on morphisms). -/
lemma Hom.verticialCard_le {G H : SemiGraph.{u}} (φ : Hom G H) (e : G.Edge) :
    G.verticialCard e ≤ H.verticialCard (φ.onEdge e) := by
  have := H.finite_branchesOver (φ.onEdge e)
  have : Finite {b' : H.Branch // H.edgeOf b' = φ.onEdge e ∧ (H.coincidence b').isSome} :=
    Finite.of_injective
      (fun b' => (⟨b'.1, b'.2.1⟩ : {b' : H.Branch // H.edgeOf b' = φ.onEdge e}))
      (by intro x y h; simp only [Subtype.mk.injEq] at h; exact Subtype.ext h)
  refine Nat.card_le_card_of_injective
    (fun b => ⟨φ.onBranch b.1, by rw [φ.edgeOf_onBranch, b.2.1], ?_⟩) ?_
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp b.2.2
    rw [φ.coincidence_onBranch _ _ hv]
    rfl
  · intro x y h
    exact Subtype.ext (φ.onBranch_injective_on_edge _ _ (by rw [x.2.1, y.2.1])
      (congrArg Subtype.val h :))

/-- A proper morphism preserves verticial cardinalities of edges (page 14). -/
def Hom.IsProper {G H : SemiGraph.{u}} (φ : Hom G H) : Prop :=
  ∀ e, H.verticialCard (φ.onEdge e) = G.verticialCard e

/-- The map induced by a morphism from the branches abutting to `v` to the branches abutting to
the image of `v`. -/
def Hom.branchesAt {G H : SemiGraph.{u}} (φ : Hom G H) (v : G.Vertex) :
    {b : G.Branch // G.coincidence b = some v} →
      {b' : H.Branch // H.coincidence b' = some (φ.onVertex v)} :=
  fun b => ⟨φ.onBranch b.1, φ.coincidence_onBranch _ _ b.2⟩

/-- An immersion: injective on branches abutting to each vertex (pages 13 and 14). -/
def Hom.IsImmersion {G H : SemiGraph.{u}} (φ : Hom G H) : Prop :=
  ∀ v, Function.Injective (φ.branchesAt v)

/-- An excision: bijective on branches abutting to each vertex (pages 13 and 14). -/
def Hom.IsExcision {G H : SemiGraph.{u}} (φ : Hom G H) : Prop :=
  ∀ v, Function.Bijective (φ.branchesAt v)

/-- A graph-covering: a proper excision (page 14). -/
def Hom.IsGraphCovering {G H : SemiGraph.{u}} (φ : Hom G H) : Prop :=
  φ.IsProper ∧ φ.IsExcision

/-! ### Sub-semi-graphs -/

open Classical in
/-- The sub-semi-graph of `G` with vertex set `Vs` and edge set `Es` (page 12): its edges are the
edges in `Es` with the same branches; a branch abuts to a vertex `v` when it does so in `G` and
`v ∈ Vs`, and abuts to no vertex otherwise (conditions (b) and (c)). -/
noncomputable def subSemiGraph (Vs : Set G.Vertex) (Es : Set G.Edge) : SemiGraph.{u} where
  Vertex := Vs
  Edge := Es
  Branch := {b : G.Branch // G.edgeOf b ∈ Es}
  edgeOf := fun b => ⟨G.edgeOf b.1, b.2⟩
  card_branches_eq_two := fun e => by
    rw [← G.card_branches_eq_two e.1]
    exact Nat.card_congr
      { toFun := fun b => ⟨b.1.1, congrArg Subtype.val b.2⟩
        invFun := fun b => ⟨⟨b.1, by rw [b.2]; exact e.2⟩, Subtype.ext b.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  coincidence := fun b =>
    (G.coincidence b.1).bind fun v => if h : v ∈ Vs then some ⟨v, h⟩ else none

/-- Condition (b) of page 12: a branch abutting in `G` to a vertex of the sub-semi-graph abuts to
it in the sub-semi-graph. -/
lemma subSemiGraph_coincidence_of_mem (Vs : Set G.Vertex) (Es : Set G.Edge)
    (b : (G.subSemiGraph Vs Es).Branch) (v : G.Vertex) (hb : G.coincidence b.1 = some v)
    (hv : v ∈ Vs) : (G.subSemiGraph Vs Es).coincidence b = some ⟨v, hv⟩ := by
  simp [subSemiGraph, hb, hv]

/-- Condition (c) of page 12: a branch abutting in `G` to a vertex outside the sub-semi-graph, or
to no vertex, abuts to no vertex in the sub-semi-graph. -/
lemma subSemiGraph_coincidence_eq_none (Vs : Set G.Vertex) (Es : Set G.Edge)
    (b : (G.subSemiGraph Vs Es).Branch)
    (h : G.coincidence b.1 = none ∨ ∃ v, G.coincidence b.1 = some v ∧ v ∉ Vs) :
    (G.subSemiGraph Vs Es).coincidence b = none := by
  rcases h with h | ⟨v, hb, hv⟩
  · simp [subSemiGraph, h]
  · simp [subSemiGraph, hb, hv]

/-- The inclusion of a sub-semi-graph, as a morphism of semi-graphs. -/
noncomputable def subSemiGraphInclusion (Vs : Set G.Vertex) (Es : Set G.Edge) :
    Hom (G.subSemiGraph Vs Es) G where
  onVertex := Subtype.val
  onEdge := Subtype.val
  onBranch := Subtype.val
  edgeOf_onBranch := fun _ => rfl
  onBranch_injective_on_edge := fun _ _ _ h => Subtype.ext h
  coincidence_onBranch := fun b v h => by
    rcases hb : G.coincidence b.1 with _ | w
    · rw [subSemiGraph_coincidence_eq_none G Vs Es b (Or.inl hb)] at h
      exact absurd h (by simp)
    · by_cases hw : w ∈ Vs
      · rw [subSemiGraph_coincidence_of_mem G Vs Es b w hb hw] at h
        cases h
        rfl
      · rw [subSemiGraph_coincidence_eq_none G Vs Es b (Or.inr ⟨w, hb, hw⟩)] at h
        exact absurd h (by simp)

/-- The maximal subgraph: the sub-semi-graph obtained by omitting all open edges (page 13). -/
noncomputable def maximalSubgraph : SemiGraph.{u} :=
  G.subSemiGraph Set.univ {e | G.IsClosedEdge e}

/-- Keeping all vertices does not change verticial cardinalities. -/
lemma subSemiGraph_univ_verticialCard (Es : Set G.Edge) (e : Es) :
    (G.subSemiGraph Set.univ Es).verticialCard e = G.verticialCard e.1 := by
  have key : ∀ b : (G.subSemiGraph Set.univ Es).Branch,
      ((G.subSemiGraph Set.univ Es).coincidence b).isSome = (G.coincidence b.1).isSome := by
    intro b
    rcases hb : G.coincidence b.1 with _ | w
    · rw [subSemiGraph_coincidence_eq_none G _ _ b (Or.inl hb)]; rfl
    · rw [subSemiGraph_coincidence_of_mem G _ _ b w hb (Set.mem_univ w)]; rfl
  exact Nat.card_congr
    { toFun := fun b => ⟨b.1.1, congrArg Subtype.val b.2.1, (key b.1).symm.trans b.2.2⟩
      invFun := fun b => ⟨⟨b.1, by rw [b.2.1]; exact e.2⟩, Subtype.ext b.2.1,
        (key ⟨b.1, by rw [b.2.1]; exact e.2⟩).trans b.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The maximal subgraph is a graph (page 13). -/
theorem maximalSubgraph_isGraph : G.maximalSubgraph.IsGraph := fun e =>
  (G.subSemiGraph_univ_verticialCard _ e).trans e.2

/-! ### Compactification -/

/-- The coincidence map of the compactification: a branch abutting to no vertex abuts to the new
vertex attached to it. -/
def compactificationCoincidence (b : G.Branch) :
    Option (G.Vertex ⊕ {b : G.Branch // G.coincidence b = none}) :=
  match h : G.coincidence b with
  | some v => some (.inl v)
  | none => some (.inr ⟨b, h⟩)

/-- The compactification (page 13): for each branch abutting to no vertex, a new vertex is
appended to which that branch abuts. -/
def compactification : SemiGraph.{u} where
  Vertex := G.Vertex ⊕ {b : G.Branch // G.coincidence b = none}
  Edge := G.Edge
  Branch := G.Branch
  edgeOf := G.edgeOf
  card_branches_eq_two := G.card_branches_eq_two
  coincidence := G.compactificationCoincidence

/-- In the compactification every branch abuts to a vertex. -/
lemma compactificationCoincidence_isSome (b : G.Branch) :
    (G.compactificationCoincidence b).isSome := by
  unfold compactificationCoincidence
  split <;> rfl

/-- The compactification is a graph (page 13). -/
theorem compactification_isGraph : G.compactification.IsGraph := by
  intro e
  rw [← G.card_branches_eq_two e]
  exact Nat.card_congr
    { toFun := fun b => ⟨b.1, b.2.1⟩
      invFun := fun b => ⟨b.1, b.2, G.compactificationCoincidence_isSome b.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- In the compactification, a branch abuts to an old vertex `v` exactly when it abuts to `v`
in `G` (page 13: `G` forms a sub-semi-graph of its compactification). -/
lemma compactification_coincidence_inl_iff (b : G.Branch) (v : G.Vertex) :
    G.compactification.coincidence b = some (.inl v) ↔ G.coincidence b = some v := by
  change G.compactificationCoincidence b = _ ↔ _
  unfold compactificationCoincidence
  split
  next w hw =>
    rw [hw]
    exact ⟨fun h => by rw [Sum.inl_injective (Option.some_injective _ h)], fun h => by
      rw [Option.some_injective _ h]; exact rfl⟩
  next hw =>
    simp only [hw, reduceCtorEq, iff_false]
    intro h
    injection h with h
    cases h

/-- The morphism from a semi-graph to its compactification. -/
def toCompactification : Hom G G.compactification where
  onVertex := Sum.inl
  onEdge := fun e => e
  onBranch := fun b => b
  edgeOf_onBranch := fun _ => rfl
  onBranch_injective_on_edge := fun _ _ _ h => h
  coincidence_onBranch := fun b v h => (G.compactification_coincidence_inl_iff b v).2 h

/-! ### Examples -/

/-- A semi-graph is connected when every component is reachable from one component. -/
lemma connected_of_forall_reachable {G : SemiGraph.{u}} (x₀ : G.SemiGraphComponent)
    (h : ∀ x, G.incidenceGraph.Reachable x₀ x) : G.IsConnectedSemiGraph :=
  (SimpleGraph.connected_iff_exists_forall_reachable _).2 ⟨x₀, h⟩

/-- An edge is adjacent, in the incidence graph, to each vertex it abuts to. -/
lemma incidenceGraph_adj {G : SemiGraph.{u}} {e : G.Edge} {v : G.Vertex}
    (h : G.EdgeAbutsTo e v) : G.incidenceGraph.Adj (.inl v) (.inr e) := by
  rw [incidenceGraph, SimpleGraph.fromRel_adj]
  exact ⟨Sum.inl_ne_inr, Or.inl h⟩

/-- One vertex with one open edge: one branch abuts to the vertex and the other to nothing. -/
abbrev exampleOpenEdge : SemiGraph.{0} where
  Vertex := Unit
  Edge := Unit
  Branch := Bool
  edgeOf := fun _ => ()
  card_branches_eq_two := fun _ => by
    rw [Nat.card_eq_fintype_card]; rfl
  coincidence := fun b => if b then some () else none

/-- A loop: one vertex and one edge both of whose branches abut to that vertex. -/
abbrev exampleLoop : SemiGraph.{0} where
  Vertex := Unit
  Edge := Unit
  Branch := Bool
  edgeOf := fun _ => ()
  card_branches_eq_two := fun _ => by
    rw [Nat.card_eq_fintype_card]; rfl
  coincidence := fun _ => some ()

/-- Two vertices joined by one closed edge. -/
abbrev exampleSegment : SemiGraph.{0} where
  Vertex := Bool
  Edge := Unit
  Branch := Bool
  edgeOf := fun _ => ()
  card_branches_eq_two := fun _ => by
    rw [Nat.card_eq_fintype_card]; rfl
  coincidence := fun b => some b

/-- A joint: one vertex and two open edges, each with one branch abutting to the vertex. -/
abbrev exampleJoint : SemiGraph.{0} where
  Vertex := Unit
  Edge := Bool
  Branch := Bool × Bool
  edgeOf := Prod.fst
  card_branches_eq_two := fun e => by
    rw [Nat.card_eq_fintype_card]; cases e <;> rfl
  coincidence := fun b => if b.2 then some () else none

/-- The edge of `exampleOpenEdge` has verticial cardinality one. -/
lemma exampleOpenEdge_verticialCard : exampleOpenEdge.verticialCard () = 1 := by
  unfold SemiGraph.verticialCard; rw [Nat.card_eq_fintype_card]; rfl

/-- The edge of `exampleOpenEdge` is open and not isolated; the semi-graph is not a graph. -/
theorem exampleOpenEdge_properties :
    exampleOpenEdge.IsOpenEdge () ∧ ¬ exampleOpenEdge.IsIsolatedEdge () ∧
      ¬ exampleOpenEdge.IsGraph ∧ exampleOpenEdge.IsUntangled ∧
      exampleOpenEdge.IsConnectedSemiGraph := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [IsOpenEdge, exampleOpenEdge_verticialCard]
  · simp [IsIsolatedEdge, exampleOpenEdge_verticialCard]
  · intro h
    have := h ()
    rw [exampleOpenEdge_verticialCard] at this
    exact absurd this (by norm_num)
  · rintro ⟨⟩ he
    rw [IsClosedEdge, exampleOpenEdge_verticialCard] at he
    exact absurd he (by norm_num)
  · refine connected_of_forall_reachable (.inl ()) ?_
    rintro (⟨⟩ | ⟨⟩)
    · rfl
    · exact (incidenceGraph_adj (G := exampleOpenEdge) (e := ()) (v := ())
        ⟨true, rfl, rfl⟩).reachable

/-- The edge of `exampleLoop` has verticial cardinality two. -/
lemma exampleLoop_verticialCard : exampleLoop.verticialCard () = 2 := by
  unfold SemiGraph.verticialCard; rw [Nat.card_eq_fintype_card]; rfl

/-- The loop is a connected graph that is not untangled. -/
theorem exampleLoop_properties :
    exampleLoop.IsGraph ∧ exampleLoop.IsClosedEdge () ∧ ¬ exampleLoop.IsUntangled ∧
      exampleLoop.IsConnectedSemiGraph := by
  refine ⟨fun _ => exampleLoop_verticialCard, exampleLoop_verticialCard, ?_, ?_⟩
  · intro h
    obtain ⟨v₁, v₂, hne, -, -⟩ := h () exampleLoop_verticialCard
    exact hne rfl
  · refine connected_of_forall_reachable (.inl ()) ?_
    rintro (⟨⟩ | ⟨⟩)
    · rfl
    · exact (incidenceGraph_adj (G := exampleLoop) (e := ()) (v := ()) ⟨true, rfl, rfl⟩).reachable

/-- The edge of `exampleSegment` has verticial cardinality two. -/
lemma exampleSegment_verticialCard : exampleSegment.verticialCard () = 2 := by
  unfold SemiGraph.verticialCard; rw [Nat.card_eq_fintype_card]; rfl

/-- Two vertices joined by a closed edge: a connected, untangled, locally finite graph whose edge
joins the two vertices. -/
theorem exampleSegment_properties :
    exampleSegment.IsGraph ∧ exampleSegment.Joins () false true ∧ exampleSegment.IsUntangled ∧
      exampleSegment.IsLocallyFinite ∧ exampleSegment.IsConnectedSemiGraph := by
  refine ⟨fun _ => exampleSegment_verticialCard,
    ⟨exampleSegment_verticialCard, false, true, by decide, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · intro e _
    exact ⟨false, true, by decide, ⟨false, rfl, rfl⟩, ⟨true, rfl, rfl⟩⟩
  · intro v
    exact Set.toFinite _
  · refine connected_of_forall_reachable (.inr ()) ?_
    rintro (b | ⟨⟩)
    · exact (incidenceGraph_adj (G := exampleSegment) (e := ()) (v := b)
        ⟨b, rfl, rfl⟩).reachable.symm
    · rfl

/-- Each edge of `exampleJoint` has verticial cardinality one. -/
lemma exampleJoint_verticialCard (e : Bool) : exampleJoint.verticialCard e = 1 := by
  unfold SemiGraph.verticialCard; rw [Nat.card_eq_fintype_card]; cases e <;> rfl

/-- `exampleJoint` is a joint (page 13). -/
theorem exampleJoint_isJoint : exampleJoint.IsJoint := by
  refine ⟨?_, ?_, ?_, fun e => ?_⟩
  · refine connected_of_forall_reachable (.inl ()) ?_
    rintro (⟨⟩ | e)
    · rfl
    · exact (incidenceGraph_adj (G := exampleJoint) (e := e) (v := ())
        ⟨(e, true), rfl, rfl⟩).reachable
  · rw [Nat.card_eq_fintype_card]; rfl
  · rw [Nat.card_eq_fintype_card]; rfl
  · simp [IsOpenEdge, exampleJoint_verticialCard]

end SemiGraph

end IUT.Prerequisites
