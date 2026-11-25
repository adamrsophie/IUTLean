# Structures of IUT I: interface versus concrete implementation

Source: Mochizuki, *Inter-universal Teichmüller Theory I*, §§3 to 6. Pages are given per
construction; see `data/curated/iut1.json` for which pages were checked against rendered
images. Notation follows `docs/notation/IUT1.md`.

## The common pattern

Every structure of §§3 to 6 is introduced in two steps.

1. **Concrete model.** From fixed initial Θ-data (Definition 3.1) the paper builds one model
   object: model local data `F_v` (Examples 3.2 to 3.4), model global data `F^⊩_mod`
   (Example 3.5), model bridges `φ^NF`, `φ^Θ` (Examples 4.3, 4.4), `φ^{Θ±}`, `φ^{Θell}`
   (Examples 6.2, 6.3), and their Frobenioid lifts (Examples 5.1, 5.4).
2. **Interface.** The structure is then defined as *any* collection of data of the same shape
   that admits an isomorphism to the model, for instance "a category which admits an
   equivalence `†F_v ⥲ F_v`" (Definition 3.6 (a), page 87) or "such that there exist
   isomorphisms ... conjugation by which maps the model arrow to the given arrow"
   (Definition 4.6, pages 111 and 112).

So an object of each type is the model up to an *unspecified* isomorphism. What the theory
uses is (i) what can be reconstructed from the object alone, by "group-theoretic" or
"category-theoretic" algorithms, and (ii) the size of the set of isomorphisms between two
such objects (Propositions 4.8, 6.6; Corollaries 5.3, 5.6, 6.12). The model is used only
to certify nonemptiness of those isomorphism sets.

For a formalization this means: each interface type is a type of pairs (data, proof that the
data is isomorphic to the model), or equivalently the essential image of the model in a
groupoid of shapes. Defining the shape groupoid needs the morphisms of each component
(categories up to equivalence, Frobenioids, Aut-holomorphic orbispaces, poly-morphisms), and
the model needs initial Θ-data. Neither exists in Lean; no structure below is formalized.

Poly-morphism vocabulary (§0, pages 33 and 34): a poly-morphism `A → B` is a set of morphisms;
a full poly-isomorphism is the set of all isomorphisms; capsules are finite indexed families,
and a capsule-full poly-isomorphism is the set of all families of isomorphisms over a fixed
bijection of index sets. An "isomorphism `C → D`" of categories is an isomorphism class of
equivalences.

## Prime strips

### D-prime-strip (Definition 4.1, pages 95 to 98)

* Components: `{D_v}_{v ∈ V}`. At nonarchimedean `v`, a category equivalent to the model
  `D_v` (connected tempered coverings at bad `v`, connected finite étale coverings at good
  `v`). At archimedean `v`, an Aut-holomorphic orbispace isomorphic to the model.
* Carrier: the base categories only; no monoids, no Frobenioid structure.
* Retains: by [SemiAnbd] and [AbsTopIII], the arithmetic fundamental group `π_1(D_v)` up to
  inner automorphism, hence label classes of cusps `LabCusp(D_v)`, an `F_l^*`-torsor.
* Forgets: all monoid and value-group data; the identification with the specific `K_v`.
* Morphisms: collections of morphisms `D_v → D'_v` (in the §0 sense for temperoids).
* Choices: none in the definition; the model depends on all of the initial Θ-data.

### D^⊢-prime-strip (Definition 4.1, page 96)

* Components: `{D^⊢_v}`; at nonarchimedean `v` a category equivalent to `B(K_v)^0`, at
  archimedean `v` an object of `TM^⊢`.
* Mono-analyticization: a functor from D-prime-strips to D^⊢-prime-strips.
* Forgets: the curve; only the local field's Galois group (nonarchimedean) or a split
  topological monoid (archimedean) remains.

### F-prime-strip and F^⊢-prime-strip (Definition 5.2, pages 134 to 143)

* Components: at nonarchimedean `v` a Frobenioid equivalent to the model `F_v`; at archimedean
  `v` a triple `(C_v, D_v, κ_v)` with Kummer structure `κ_v`. F^⊢: split Frobenioids
  `(C^⊢_v, τ^⊢_v)` or the archimedean analogue.
* Carrier: the Frobenioids (monoids over the base categories) or, at archimedean `v`, the
  topological monoid with its Kummer structure.
* Morphisms: collections of isomorphisms.
* Choices: none in the definition; the model depends on the initial Θ-data through
  Examples 3.2 to 3.4.
* Retains versus forgets (Corollary 5.3, pages 143 to 145): isomorphisms of F-prime-strips
  correspond bijectively to isomorphisms of the associated D-prime-strips; for
  F^⊢-prime-strips the map to D^⊢ isomorphisms is only surjective. At bad `v`,
  `Aut(F_v) → Aut(D_v)` is bijective. So an F-prime-strip carries no more symmetry than its
  D-prime-strip, while an F^⊢-prime-strip carries extra automorphisms.

### F^⊩-prime-strip (Definition 5.2, pages 134 to 143)

* Components: `(C^⊩, Prime(C^⊩) ⥲ V, F^⊢, {ρ_v})`: a global realified Frobenioid, a bijection
  of its primes with `V`, an F^⊢-prime-strip, and isomorphisms of topological monoids `ρ_v`.
* Example: `F^⊩_mod` and `F^⊩_tht` of a Θ-Hodge theater (Example 3.5).
* Retains: the global realified degree data indexed by `V` and the local split monoids.
* Forgets: the global Frobenioid of the number field itself (only its realification and
  primes remain) and the local Galois data beyond F^⊢.
* Morphisms and choices: not stated separately on the pages read beyond Definition 5.2; the
  convention of Remark 3.5.2 (isomorphisms of collections of data) applies.

## Hodge theaters and bridges

### Θ-Hodge theater (Definition 3.6, pages 87 and 88)

* Components: `({F_v}_{v∈V}, F^⊩_mod)`, each isomorphic to the model of Examples 3.2 to 3.5.
* Derived data: `D_v`, `D^⊢_v`, `F^⊢_v`, `F^Θ_v` at each `v`; `F^⊩_tht`, `F^⊩_D` globally.
* Morphisms: Remark 3.6.2 states there is an evident notion of isomorphism and leaves the
  details to the reader. This is the first undefined notion a formalization must fix.
* Isomorphisms: biject with isomorphisms of the associated D-prime-strip (Corollary 5.6 (i)).

### Θ-link (Corollary 3.7, pages 88 and 89)

* Definition: for Θ-Hodge theaters `†HT^Θ`, `‡HT^Θ`, the full poly-isomorphism
  `†F^⊩_tht ⥲ ‡F^⊩_mod`. Nonempty because both are isomorphic to the same model shape.
* Retains: by (ii) and (iii) it induces full poly-isomorphisms `†D^⊢_v ⥲ ‡D^⊢_v` and of unit
  groups `O^×` at each `v`.
* Forgets: everything not visible in `F^⊩`; in particular the ring structure and the
  identification of Θ-pilot with q-pilot values. Remark 3.7.1: no isomorphism in the set is
  distinguished.
* Choice dependence: none beyond the two theaters; the link is the whole set.

### D-NF-bridge, D-Θ-bridge, D-ΘNF-Hodge theater (Definition 4.6, pages 111 and 112)

* D-NF-bridge: a poly-morphism `D_J → D^⊚` from a capsule of D-prime-strips indexed by a
  finite set `J` to a category equivalent to `D^⊚ = B(C_K)^0`, isomorphic to the model
  `φ^NF`. Morphisms: a capsule-full poly-isomorphism on `D_J` with an `Aut_ε`-orbit of
  isomorphisms on `D^⊚`.
* D-Θ-bridge: a poly-morphism `D_J → D_>` to a D-prime-strip, isomorphic to the model `φ^Θ`.
  Morphisms: a capsule-full poly-isomorphism with the full poly-isomorphism on `D_>`.
* D-ΘNF-Hodge theater: a D-NF-bridge and a D-Θ-bridge with the same capsule, jointly
  isomorphic to the model; morphisms are compatible pairs inducing the same bijection of
  index sets.
* Symmetries (Proposition 4.8, page 115): isomorphisms of D-NF-bridges form an
  `F_l^*`-torsor; of D-Θ-bridges and D-ΘNF-Hodge theaters, a single element; gluings form an
  `F_l^*`-torsor. Proposition 4.7 gives the labeling `χ : J ⥲ F_l^*` and `[ε]`.
* Choices: the model depends on `ε` (through `Aut_ε` and `[ε]`) and on `V`.

### NF-bridge, Θ-bridge, ΘNF-Hodge theater (Definition 5.5, pages 151 to 153)

* NF-bridge: `(F_J, F^⊚, F^⊛, restriction arrow, ψ^NF)`, where `ψ^NF` lifts a D-NF-bridge;
  the lift is unique by Corollary 5.3 (ii).
* Θ-bridge: `(F_J, F_>, HT^Θ, ψ^Θ)`, with `F_>` the F-prime-strip tautologically associated to
  the Θ-Hodge theater (pages 146 and 147) and `ψ^Θ` determined by a D-Θ-bridge.
* ΘNF-Hodge theater: an NF-bridge and a Θ-bridge with a common capsule, lifting a
  D-ΘNF-Hodge theater.
* Symmetries (Corollary 5.6, pages 153 and 154): isomorphism sets biject with those of the
  D-versions; gluings form an `F_l^*`-torsor.
* Concrete versus interface: the F-objects are determined by their D-shadows up to unique
  isomorphism, so the D-objects carry all the combinatorics.

### Θ^{±ell}-side (Definitions 6.1, 6.4, 6.11, pages 155 to 163 and 172 to 173)

* `F_l^{⋊±} = F_l ⋊ {±1}`; `T` is an `F_l^±`-group (Θ^±) or `F_l^±`-torsor (Θ^ell).
* D-Θ^±-bridge: a poly-morphism `D_T → D_≻` to a D-prime-strip, isomorphic to the model of
  Example 6.2; morphisms are capsule-+-full poly-isomorphisms over `F_l^±`-group isomorphisms.
  Derived capsules `D_{|T|}` (quotient by `±1`) and `D_{T^*}` (`|T|` minus `0`).
* D-Θ^ell-bridge: a poly-morphism `D_T → D^{⊚±}` with `D^{⊚±} = B(X_K)^0`, isomorphic to the
  model of Example 6.3; morphisms use `Aut_csp`-orbits.
* D-Θ^{±ell}-Hodge theater: both bridges on one capsule, isomorphic to the model.
* Θ^±-bridge: a poly-morphism of F-prime-strips lifting a D-Θ^±-bridge. Θ^ell-bridge: by
  Definition 6.11 (ii) it *is* a D-Θ^ell-bridge on the associated D-capsule; no Frobenioid
  data is attached at the target. Θ^{±ell}-Hodge theater: a Θ^±-bridge and a Θ^ell-bridge
  whose D-shadows form a D-Θ^{±ell}-Hodge theater.
* Symmetries (Proposition 6.6, Corollary 6.12): isomorphisms of D-Θ^±-bridges form a torsor
  over `{±1} × ∏_V {±1}`; of D-Θ^ell-bridges, an `F_l^{⋊±}`-torsor; of D-Θ^{±ell}-Hodge
  theaters, a `{±1}`-torsor; gluings form a torsor over `F_l^{⋊±} × ∏_V {±1}`.
* Choices: the isomorphism `Aut_±(D^{⊚±})/Aut_csp ⥲ F_l^{⋊±}` depends on `ε` (page 158).

### Θ^{±ell}NF-Hodge theater (Definition 6.13, page 182)

* Components: a Θ^{±ell}-Hodge theater, a ΘNF-Hodge theater, and the gluing isomorphism
  between them, stated to be necessarily unique (Remark 6.12.2, via Proposition 6.7: a
  D-Θ^±-bridge determines a D-Θ-bridge by passing to `D_{T^*}` and identifying `D_≻` with
  `D_0`).
* Retains: both the additive `F_l^{⋊±}` symmetry and the multiplicative `F_l^*` symmetry
  (Theorem A, pages 13 to 15).
* Forgets: nothing relative to its two constituents; the gluing adds no data because it is
  unique.
* Morphisms: Definition 6.13 is a triple; the morphisms of the triple were not found spelled
  out on the pages read (pages 182 to 184 in text), so they are presumably pairs of morphisms
  of the constituents compatible with the gluing.
* Choices: those of its constituents (`ε`, `V`).

## What a formalization would need, in order

1. Poly-morphisms and capsules over an arbitrary category: elementary, statable today.
2. Temperoids and their morphisms (§0, pages 34 and 35), tempered fundamental groups.
3. Frobenioids ([FrdI], [FrdII]) and their category-theoretic reconstruction results.
4. Aut-holomorphic orbispaces ([AbsTopIII]).
5. The models of Examples 3.2 to 3.5, 4.3, 4.4, 5.1, 5.4, 6.2, 6.3 from initial Θ-data.
6. The interface types as essential images, then the torsor statements.

Only step 1 is within reach of current Mathlib. It was not done here because, without
steps 2 to 5, a Lean structure named after a prime strip or Hodge theater would be a shell.
