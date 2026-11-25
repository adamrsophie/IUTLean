import Mathlib

/-!
# IUT I, Section 0: tempered groups and connected temperoids

Source: Mochizuki, *Inter-universal Teichmüller Theory I*, Section 0 ("Notations and
Conventions"), subsection "Monoids and Categories", pages 33 to 35, and Remark 2.5.3 (i), (T1),
page 52. Pages read for this file: 33, 34, 35 and 52, all as rendered images; every definition
below was checked against those images. Also read, as a rendered image: page 4 of Mochizuki's
*Comments on "Semi-graphs of Anabelioids"*, item (12), whose (T1) has the same wording as
IUT I, Remark 2.5.3 (i), (T1). Not read for this file: [SemiAnbd] itself (Definition 3.1 (i)
to (iii), Proposition 3.2) and [FrdI], §0.

## Galois-countability and the corrected theory

IUT I, Remark 2.5.3 (i), page 52 (and item (12) of the comments on [SemiAnbd]) notes that
pathologies occur in the theory of tempered fundamental groups without countability
hypotheses, and introduces in (T1): a tempered group is *Galois-countable* if its topology
admits a countable basis; a connected temperoid is Galois-countable if it arises from a
Galois-countable tempered group. The correction does not change the definitions of a tempered
group, of `B^temp(Π)` or of a connected temperoid: it adds Galois-countability as a hypothesis
to results (by (E7) of the comments, to [SemiAnbd] 3.2 to 3.9). IUT I, pages 34 and 35, keeps
the uncorrected definitions and puts "Galois-countable" only in the reconstruction of `Π` and
in the bijections of page 35, in agreement with the correction. This file therefore formalizes
the definitions as stated on page 34 (`IsTemperedGroup`, `TemperedSetCategory`,
`IsConnectedTemperoid`, with no countable basis condition) and states Galois-countability
separately (`IsGaloisCountableTemperedGroup`, `IsGaloisCountableConnectedTemperoid`); no
discrepancy between the two sources was found on the pages read.

## Definitions of pages 34 and 35, as stated here

The group written `Π` on the page is named `P` in the Lean code (`Π` is a reserved token).

* **Tempered topological group** (page 34): a topological group `Π` is tempered if it may be
  written as an inverse limit of an inverse system of surjections of countable discrete
  topological groups (`IsTemperedGroup`). The inverse system is spelled out: an index preorder
  `I`, groups `G i` that are countable and carry the discrete topology, surjective transition
  homomorphisms `G j →* G i` for `i ≤ j` satisfying the identity and composition laws, and an
  isomorphism of topological groups from `Π` onto the subgroup of compatible families of
  `∀ i, G i` with the subspace topology of the product topology (`compatibleFamilies`).
  **Interpretation:** the page states no condition on the index set. We take an arbitrary
  nonempty directed preorder (the usual meaning of "inverse system"), with no countability
  condition, in the universe of `Π`; the groups `G i` live in the same universe.
* **`B^temp(Π)`** (page 34): the category whose objects are countable discrete sets with a
  continuous `Π`-action and whose morphisms are morphisms of `Π`-sets (`TemperedSetCategory`).
  It is the full subcategory of Mathlib's category `Action (Type u) Π` of `Π`-sets and
  equivariant maps cut out by `IsCountableDiscreteContinuous`: the underlying set is countable
  and the action map `Π × X → X` is continuous for the discrete topology on `X`. "Countable"
  is Mathlib's `Countable` (cardinality at most that of `ℕ`), as on the page.
* **Connected temperoid** (page 34): a category equivalent to `B^temp(Π)` for a tempered
  topological group `Π` (`IsConnectedTemperoid`).
* **Galois-countable** (page 52, (T1)): a tempered group whose topology has a countable basis,
  Mathlib's `SecondCountableTopology` (`IsGaloisCountableTemperedGroup`); a connected temperoid
  equivalent to `B^temp(Π)` for such a `Π` (`IsGaloisCountableConnectedTemperoid`). "Arises
  from" is read as "is equivalent to `B^temp` of". The notions for temperoids,
  quasi-temperoids and semi-graphs of anabelioids in (T1) and (T2) are not stated.
* **Morphism of connected temperoids** (page 35): a morphism `C₁ → C₂` is an isomorphism class
  of functors `C₂ → C₁` that preserve finite limits and countable colimits
  (`TemperoidMorphismClass`). "Preserves countable colimits" is read as preserving colimits of
  every shape `J : Type` that is a `CountableCategory` (countably many objects and morphisms),
  in the same way as Mathlib's `PreservesFiniteLimits` quantifies over finite shapes in `Type`.
  The type is defined for arbitrary categories `C₁`, `C₂` with the same object and morphism
  universes; the page uses it for connected temperoids.

## Lemmas proved here (elementary properties, not results of the papers)

* Temperedness is invariant under isomorphism of topological groups
  (`isTemperedGroup_of_continuousMulEquiv`).
* A countable discrete group is tempered (`isTemperedGroup_of_countable_discrete`).
* A topological group isomorphic to an inverse limit of a surjective inverse system of finite
  discrete groups is tempered (`isTemperedGroup_of_finite_system`). This is close to the
  definition itself, since a finite group is countable; it records that such profinite groups
  are covered.
* A tempered group is totally disconnected (`totallyDisconnectedSpace_of_isTemperedGroup`), so
  the circle group is not tempered (`circle_not_isTemperedGroup`): the definition is not
  satisfied by every topological group.
* A set with the trivial action is an object of `B^temp(Π)` when countable
  (`trivialTemperedSet`), and `B^temp(Π)` is a connected temperoid when `Π` is tempered
  (`temperedSetCategory_isConnectedTemperoid`).
* A countable discrete group is a Galois-countable tempered group
  (`isGaloisCountableTemperedGroup_of_countable_discrete`), and a Galois-countable connected
  temperoid is a connected temperoid
  (`IsGaloisCountableConnectedTemperoid.isConnectedTemperoid`).

## Not covered

* `B(X)`, the category of finite étale coverings of a connected noetherian algebraic stack
  (page 34): algebraic stacks are not in Mathlib.
* The subcategory `C^0` of connected objects, the category `(C^0)^⊤`, the equivalence
  `C ≃ (C^0)^⊤` (page 34) and morphisms `C₁^0 → C₂^0` (page 35): the notions of connected
  object and of `(·)^⊤` are those of [FrdI], §0, which is not defined on the pages read.
* The reconstruction of `Π` up to inner
  automorphism from `B^temp(Π)` or `B^temp(Π)^0` and the groups `π₁(C)`, `π₁(C^0)` (page 34,
  citing Remark 2.5.3 (i), (T5)): open; not stated.
* The natural bijections of page 35 between continuous outer homomorphisms `Π₁ → Π₂`,
  morphisms `B^temp(Π₁) → B^temp(Π₂)` and morphisms `B^temp(Π₁)^0 → B^temp(Π₂)^0` for
  Galois-countable tempered `Π₁`, `Π₂` (citing Remark 2.5.3 (ii), (E7) and [SemiAnbd],
  Proposition 3.2): open; not stated.
* That `ℤ_[p]` (or any specific infinite profinite group) is tempered is not proved here.
-/

open CategoryTheory

namespace IUT.PaperI

universe u v w

/-! ### Tempered topological groups (page 34) -/

/-- The subgroup of `∀ i, G i` of families compatible with the transition maps `f`: those `x`
with `f h (x j) = x i` whenever `h : i ≤ j`. With the subspace topology of the product topology
it is the inverse limit of the system `f`. -/
def compatibleFamilies {I : Type u} [Preorder I] (G : I → Type u) [∀ i, Group (G i)]
    (f : ∀ {i j : I}, i ≤ j → G j →* G i) : Subgroup (∀ i, G i) where
  carrier := {x | ∀ (i j : I) (h : i ≤ j), f h (x j) = x i}
  mul_mem' {a b} ha hb i j h := by simp [ha i j h, hb i j h]
  one_mem' i j h := by simp
  inv_mem' {a} ha i j h := by simp [ha i j h]

/-- IUT I, page 34: a topological group `Π` is **tempered** if it may be written as an inverse
limit of an inverse system of surjections of countable discrete topological groups. The index
set is a nonempty directed preorder `I` with no countability condition (the page states none);
`I` and the groups `G i` are taken in the universe of `Π`. -/
def IsTemperedGroup (P : Type u) [Group P] [TopologicalSpace P] : Prop :=
  ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
    (G : I → Type u) (_ : ∀ i, Group (G i)) (_ : ∀ i, TopologicalSpace (G i))
    (f : ∀ {i j : I}, i ≤ j → G j →* G i),
    (∀ i, DiscreteTopology (G i)) ∧ (∀ i, Countable (G i)) ∧
    (∀ {i j : I} (h : i ≤ j), Function.Surjective (f h)) ∧
    (∀ (i : I) (x : G i), f (le_refl i) x = x) ∧
    (∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : G k),
      f hij (f hjk x) = f (hij.trans hjk) x) ∧
    Nonempty (P ≃ₜ* compatibleFamilies G f)

/-- Temperedness is invariant under isomorphism of topological groups. -/
theorem isTemperedGroup_of_continuousMulEquiv {P P' : Type u} [Group P] [TopologicalSpace P]
    [Group P'] [TopologicalSpace P'] (e : P' ≃ₜ* P) (h : IsTemperedGroup P) :
    IsTemperedGroup P' := by
  obtain ⟨I, _, _, _, G, _, _, f, hd, hc, hs, hid, hcomp, ⟨e'⟩⟩ := h
  exact ⟨I, _, ‹_›, ‹_›, G, _, _, f, hd, hc, hs, hid, hcomp, ⟨e.trans e'⟩⟩

/-- A countable group with the discrete topology is tempered: it is the inverse limit of the
inverse system with one index and the identity transition map. -/
theorem isTemperedGroup_of_countable_discrete (P : Type u) [Group P] [TopologicalSpace P]
    [DiscreteTopology P] [Countable P] : IsTemperedGroup P := by
  refine ⟨PUnit, inferInstance, inferInstance, inferInstance, fun _ => P, fun _ => inferInstance,
    fun _ => inferInstance, fun _ => MonoidHom.id P, fun _ => inferInstance,
    fun _ => inferInstance, fun _ => Function.surjective_id, fun _ _ => rfl,
    fun _ _ _ => rfl, ⟨?_⟩⟩
  let L := compatibleFamilies (fun _ : PUnit.{u + 1} => P) (fun _ => MonoidHom.id P)
  let toL : P →* L :=
    { toFun := fun g => ⟨fun _ => g, fun _ _ _ => rfl⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact
    { toMulEquiv :=
        { toFun := toL
          invFun := fun x => x.1 PUnit.unit
          left_inv := fun _ => rfl
          right_inv := fun x => Subtype.ext (funext fun _ => rfl)
          map_mul' := toL.map_mul }
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := (continuous_apply PUnit.unit).comp continuous_subtype_val }

/-- A topological group isomorphic to the inverse limit of a surjective inverse system of finite
discrete groups is tempered. This is close to the definition, since finite groups are
countable; it records that such profinite groups satisfy the definition. -/
theorem isTemperedGroup_of_finite_system (P : Type u) [Group P] [TopologicalSpace P]
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (G : I → Type u) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, DiscreteTopology (G i)] [∀ i, Finite (G i)]
    (f : ∀ {i j : I}, i ≤ j → G j →* G i)
    (hs : ∀ {i j : I} (h : i ≤ j), Function.Surjective (f h))
    (hid : ∀ (i : I) (x : G i), f (le_refl i) x = x)
    (hcomp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : G k),
      f hij (f hjk x) = f (hij.trans hjk) x)
    (e : P ≃ₜ* compatibleFamilies G f) : IsTemperedGroup P :=
  ⟨I, _, ‹_›, ‹_›, G, _, _, f, fun i => inferInstance, fun i => inferInstance, hs, hid, hcomp,
    ⟨e⟩⟩

/-- A tempered group is totally disconnected: it is homeomorphic to a subspace of a product of
discrete spaces. -/
theorem totallyDisconnectedSpace_of_isTemperedGroup (P : Type u) [Group P] [TopologicalSpace P]
    (h : IsTemperedGroup P) : TotallyDisconnectedSpace P := by
  obtain ⟨I, _, _, _, G, _, _, f, hd, -, -, -, -, ⟨e⟩⟩ := h
  exact Homeomorph.totallyDisconnectedSpace e.toHomeomorph.symm

/-- The circle group is not tempered: it is connected and nontrivial, while tempered groups are
totally disconnected. So `IsTemperedGroup` is not satisfied by every topological group. -/
theorem circle_not_isTemperedGroup : ¬ IsTemperedGroup Circle := by
  intro h
  have := totallyDisconnectedSpace_of_isTemperedGroup Circle h
  have hsub : (Set.univ : Set Circle).Subsingleton :=
    isTotallyDisconnected_of_totallyDisconnectedSpace _ Set.univ (Set.subset_univ _)
      isPreconnected_univ
  have hne : (Circle.exp Real.pi) ≠ 1 := by
    rw [Ne, Circle.exp_eq_one]
    rintro ⟨n, hn⟩
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have : (1 : ℝ) = n * 2 := by
      field_simp at hn
      linarith
    have h2 : (2 : ℤ) ∣ 1 := ⟨n, by exact_mod_cast (by linarith : (1 : ℝ) = 2 * n)⟩
    omega
  exact hne (hsub (Set.mem_univ _) (Set.mem_univ _))

/-! ### The category `B^temp(Π)` (page 34) -/

/-- A `Π`-set `X` (an object of Mathlib's `Action (Type u) Π`) is a countable discrete set with a
continuous `Π`-action: its underlying set is countable, and the action map `Π × X → X` is
continuous when `X` carries the discrete topology. -/
def IsCountableDiscreteContinuous {P : Type u} [Group P] [TopologicalSpace P] :
    ObjectProperty (Action (Type u) P) := fun X =>
  Countable X.V ∧
    letI : TopologicalSpace X.V := ⊥
    Continuous (fun p : P × X.V => X.ρ p.1 p.2)

/-- IUT I, page 34: the category `B^temp(Π)` whose objects are countable discrete sets with a
continuous `Π`-action and whose morphisms are morphisms of `Π`-sets. It is the full subcategory
of `Action (Type u) Π` (whose morphisms are the `Π`-equivariant maps) on the objects satisfying
`IsCountableDiscreteContinuous`; its category structure is Mathlib's full subcategory
structure. -/
abbrev TemperedSetCategory (P : Type u) [Group P] [TopologicalSpace P] : Type (u + 1) :=
  ObjectProperty.FullSubcategory (IsCountableDiscreteContinuous (P := P))

/-- A countable set with the trivial `Π`-action is an object of `B^temp(Π)`; in particular the
category is not empty. -/
def trivialTemperedSet (P : Type u) [Group P] [TopologicalSpace P] (S : Type u) [Countable S] :
    TemperedSetCategory P :=
  ⟨Action.trivial P S, ‹Countable S›, by
    let _ : TopologicalSpace S := ⊥
    exact continuous_snd⟩

/-! ### Connected temperoids (page 34) -/

/-- IUT I, page 34: a category `C` is a **connected temperoid** if it is equivalent to a
category `B^temp(Π)` for some tempered topological group `Π` (in the universe `u`). -/
def IsConnectedTemperoid (C : Type v) [Category.{w} C] : Prop :=
  ∃ (P : Type u) (_ : Group P) (_ : TopologicalSpace P) (_ : IsTopologicalGroup P),
    IsTemperedGroup P ∧ Nonempty (C ≌ TemperedSetCategory P)

/-- `B^temp(Π)` is a connected temperoid when `Π` is a tempered topological group. -/
theorem temperedSetCategory_isConnectedTemperoid (P : Type u) [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] (h : IsTemperedGroup P) :
    IsConnectedTemperoid.{u} (TemperedSetCategory P) :=
  ⟨P, _, _, ‹_›, h, ⟨CategoryTheory.Equivalence.refl⟩⟩

/-! ### Galois-countability (page 52, Remark 2.5.3 (i), (T1)) -/

/-- IUT I, page 52, Remark 2.5.3 (i), (T1): a tempered group is **Galois-countable** if its
topology admits a countable basis. Stated as the conjunction of `IsTemperedGroup` with Mathlib's
`SecondCountableTopology` (existence of a countable basis of the topology). -/
def IsGaloisCountableTemperedGroup (P : Type u) [Group P] [TopologicalSpace P] : Prop :=
  IsTemperedGroup P ∧ SecondCountableTopology P

/-- IUT I, page 52, Remark 2.5.3 (i), (T1): a connected temperoid is **Galois-countable** if it
arises from a Galois-countable tempered group; "arises from" is read as "is equivalent to
`B^temp(Π)` for". -/
def IsGaloisCountableConnectedTemperoid (C : Type v) [Category.{w} C] : Prop :=
  ∃ (P : Type u) (_ : Group P) (_ : TopologicalSpace P) (_ : IsTopologicalGroup P),
    IsGaloisCountableTemperedGroup P ∧ Nonempty (C ≌ TemperedSetCategory P)

/-- A countable discrete group is a Galois-countable tempered group. -/
theorem isGaloisCountableTemperedGroup_of_countable_discrete (P : Type u) [Group P]
    [TopologicalSpace P] [DiscreteTopology P] [Countable P] :
    IsGaloisCountableTemperedGroup P :=
  ⟨isTemperedGroup_of_countable_discrete P, inferInstance⟩

/-- A Galois-countable connected temperoid is a connected temperoid. -/
theorem IsGaloisCountableConnectedTemperoid.isConnectedTemperoid {C : Type v} [Category.{w} C]
    (h : IsGaloisCountableConnectedTemperoid.{u} C) : IsConnectedTemperoid.{u} C := by
  obtain ⟨P, _, _, hP, ⟨ht, -⟩, he⟩ := h
  exact ⟨P, _, _, hP, ht, he⟩

/-! ### Morphisms of connected temperoids (page 35) -/

/-- The functors `C₂ ⥤ C₁` that preserve finite limits and countable colimits; "countable
colimits" is read as colimits of every shape `J : Type` that is a `CountableCategory`. -/
def ExactCountableFunctor (C₁ : Type v) [Category.{w} C₁] (C₂ : Type v) [Category.{w} C₂] :
    Type (max v w) :=
  {F : C₂ ⥤ C₁ // Limits.PreservesFiniteLimits F ∧
    ∀ (J : Type) [SmallCategory J] [CountableCategory J], Limits.PreservesColimitsOfShape J F}

/-- IUT I, page 35: a **morphism** `C₁ → C₂` of connected temperoids is an isomorphism class of
functors `C₂ → C₁` that preserve finite limits and countable colimits. Defined here for any two
categories `C₁`, `C₂` in the same universes; the page applies it to connected temperoids. -/
def TemperoidMorphismClass (C₁ : Type v) [Category.{w} C₁] (C₂ : Type v) [Category.{w} C₂] :
    Type (max v w) :=
  Quot (fun F G : ExactCountableFunctor C₁ C₂ => Nonempty (F.1 ≅ G.1))

end IUT.PaperI
