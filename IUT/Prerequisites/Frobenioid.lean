import Mathlib

/-!
# Frobenioids: monoids, elementary Frobenioids, Definitions 1.1 to 1.3 (partial)

Source: Shinichi Mochizuki, *The Geometry of Frobenioids I: The General Theory*, Section 0
("Notations and Conventions", pages 10 to 16) and Section 1 (Definitions 1.1, 1.2, 1.3,
Remarks 1.1.1 and 1.2.1, pages 19 to 25, and Proposition 1.5, page 27), with the author's *Comments on "The Geometry of
Frobenioids I"* (January 2024). Pages read for this file: 10 to 25 and 27 of the paper and pages 1
to 6 of the comments (text); pages checked against rendered images: 10, 11, 12, 14, 15, 16, 19
to 25 and 27 of the paper and pages 1 and 6 of the comments. Every definition below was compared with the
rendered page it cites.

Errata applied (numbering of the comments): item 30 (in Definition 1.1 (i) "of characteristic
type" is automatic) is proved as `isCharacteristicTypeMonoid_of_isIntegralMonoid`; the
definition `IsPreDivisorialMonoid` keeps all three conditions of the page, and
`isPreDivisorialMonoid_iff` shows the third redundant. Item 3 (quotation marks around `Φ^pf` in
Definition 1.1 (ii)) is typographical. Items 4, 13 (monoprime monoids, ordering of `{ℤ, ℚ, ℝ}`)
and 28 (FSMFF-type) concern notions not formalized here. No other item touches pages 10 to 25.

This file is a prerequisite for the Frobenioid-theoretic data of IUT I (Examples 3.2 to 3.5,
Definitions 3.6 and 4.1); it does not formalize any statement of IUT I.

## Formalized

* Section 0, page 11 and 12: sharp, integral, saturated, torsion-free, perfect monoids; the
  characteristic `M^char = M / M^±` (`characteristicCon`, `MonoidCharacteristic`); characteristic
  type; characteristically injective morphisms; the relations `≤`, `≼`; irreducible and primary
  elements. The groupification `M^gp` is Mathlib's Grothendieck group, whose construction is the
  one of page 11.
* Section 0, pages 14 and 15: fiberwise-surjective arrows, FSM-morphisms, totally epimorphic
  categories. "Connected" (page 16) is read as Mathlib's `IsConnected` (nonempty and connected
  by zigzags).
* Definition 1.1 (i): pre-divisorial, group-like, divisorial monoids, non-dilating
  endomorphisms. Group-like, divisorial and non-dilating are defined on the page only under the
  pre-divisorial hypothesis, which is therefore part of each definition.
* Definition 1.1 (ii): monoids on a category (`IsMonoidOn`, with "isomorphism of monoids" read
  as a bijective morphism) and divisorial monoids on a category.
* Definition 1.1 (iii): the elementary Frobenioid `𝔽_Φ` of a functor `Φ : Dᵒᵖ ⥤ AddCommMonCat`:
  objects, morphisms `(φ_D, Z_φ, n_φ)`, the composition `(ψ_D ∘ φ_D, φ_D^*(Z_ψ) + n_ψ · Z_φ,
  n_ψ · n_φ)`, identities, and the three category laws as theorems
  (`elemFrobCompose_identity_left`, `elemFrobCompose_identity_right`, `elemFrobCompose_assoc`);
  the category structure `elemFrobCategory` and the projection functor to `D`. The construction
  does not use conditions (a), (b) of a monoid on `D`, so it is stated for every functor.
  The elementary Frobenioid `𝔽_M` of a monoid (`elemFrobMonoid`) and the noncommutativity of the
  standard Frobenioid `𝔽 = 𝔽_{ℤ≥0}`.
* Definition 1.1 (iv) and Remark 1.1.1: functors `C → 𝔽_Φ`, the pre-Frobenioid hypotheses, and
  `Base`, `Div`, `deg_Fr` with their behavior under composition, proved from functoriality.
* Definition 1.2 (i) to (iii) completely, and from (iv) the Frobenius-ample, Frobenius-trivial
  and isotropic objects and isotropic hulls. Remark 1.2.1, third implication.
* Definition 1.3: clauses (i) (a), (i) (b), (ii), (iii) (a) to (c), (iv), (v), (vi), (vii), one
  definition each, and their conjunction with the pre-Frobenioid hypotheses,
  `PartialFrobenioidConditions`.
* An inhabitant of `PartialFrobenioidConditions`: the elementary Frobenioid `𝔽_ℕ` over the
  one-object, one-morphism category `Discrete PUnit`, with its identity functor
  (`natPoint_partialFrobenioidConditions`), each clause proved separately. Proposition 1.5 (i)
  (page 27) asserts that `𝔽_Φ`, with the natural functor `𝔽_Φ → 𝔽_{Φ^char}`, is a Frobenioid
  whenever `Φ` is a pre-divisorial monoid on a connected, totally epimorphic category `D`. The
  example meets these hypotheses: the constant monoid `ℕ` is divisorial, and `Discrete PUnit`
  is connected and totally epimorphic. Since `ℕ` is sharp, `Φ^char = Φ`, so the natural functor
  is the identity functor used here.

## Not formalized

* Definition 1.3 (i) (c) (the functor `(C^pl-bk)_A → D_{A_D}` is an equivalence) and (iii) (d)
  (the functors from the categories of co-angular pre-steps under and over `A` to
  `Order(Φ(A))` and its opposite are equivalences). They need category structures on slices of
  non-full subcategories, which would have to be built as new categories. Hence
  `PartialFrobenioidConditions` is not the definition of a Frobenioid, and no declaration here is
  called a Frobenioid.
* The perfection `M^pf` (only the predicate "perfect" is defined), primes `Prime(M)`, bounded
  subsets and suprema, and the objects of Definition 1.2 (iv) other than those listed above;
  Definition 1.2 (v) (types of pre-Frobenioids).
* That the example satisfies the omitted clauses (i) (c) and (iii) (d), which Proposition 1.5
  asserts, is not proved, since those clauses are not stated.

## Conventions

* Monoids are written additively, as on page 11, and `ℕ≥1` is `ℕ+`.
* Mathlib writes composition in diagrammatic order: the paper's `ψ ∘ φ` is `φ ≫ ψ`.
* The library registers no instances, so the category structure of `𝔽_Φ` is the plain
  definition `elemFrobCategory`, passed explicitly where it is needed; functors `C → 𝔽_Φ` are
  `FrobFunctor C Φ`.
* "Isomorphism class of a Frobenius-trivial object maps to every isomorphism class" in
  Definition 1.3 (i) (a) is stated as: for every object `X` of `D` there is a Frobenius-trivial
  `A` with `Base(A) ≅ X`. The pull-back condition of Definition 1.2 (ii) is stated objectwise
  (an isomorphism of presheaves of sets is an objectwise bijection).
-/

namespace IUT.Prerequisites.Frobenioid

open CategoryTheory Opposite

universe u v w u' v'

/-! ## Section 0: classes of commutative monoids (page 11) -/

section Monoids

variable (M : Type*) [AddCommMonoid M]

/-- The natural homomorphism `M → M^gp` to the groupification, realized by Mathlib's
Grothendieck group (the localization of `M` at all of `M`; its elements are classes of pairs
`(a, b)` with `(a₁, b₁) ∼ (a₂, b₂)` when `a₁ + b₂ + c = b₁ + a₂ + c` for some `c`, as on
page 11). -/
noncomputable abbrev toGroupification : M →+ Algebra.GrothendieckAddGroup M :=
  Algebra.GrothendieckAddGroup.of

/-- `M` is *sharp* (page 11): its group of invertible elements `M^±` is zero. -/
def IsSharpMonoid : Prop := ∀ u : AddUnits M, u = 0

/-- `M` is *integral* (page 11): the natural map `M → M^gp` is injective. -/
def IsIntegralMonoid : Prop := Function.Injective (toGroupification M)

/-- `M` is *saturated* (page 11): every `a ∈ M^gp` such that `n · a` lies in the image of `M`
for some `n ∈ ℕ≥1` lies in the image of `M`. -/
def IsSaturatedMonoid : Prop :=
  ∀ a : Algebra.GrothendieckAddGroup M,
    (∃ n : ℕ+, (n : ℕ) • a ∈ Set.range (toGroupification M)) →
      a ∈ Set.range (toGroupification M)

/-- `M` is *torsion-free* (page 11): `M` has no torsion elements. Reading: a torsion element is
a nonzero `a` with `n · a = 0` for some `n ∈ ℕ≥1`. -/
def IsTorsionFreeMonoid : Prop := ∀ (a : M) (n : ℕ+), (n : ℕ) • a = 0 → a = 0

/-- `M` is *perfect* (page 11): multiplication by every element of `ℕ≥1` is bijective on `M`. -/
def IsPerfectMonoid : Prop := ∀ n : ℕ+, Function.Bijective fun a : M => (n : ℕ) • a

/-- The congruence on `M` whose quotient is the characteristic `M^char = M / M^±` (page 11):
`a ∼ b` when `a + u = b` for some invertible `u`. -/
def characteristicCon : AddCon M where
  r a b := ∃ u : AddUnits M, a + (u : M) = b
  iseqv :=
    ⟨fun a => ⟨0, by simp⟩,
     fun {a b} ⟨u, h⟩ => ⟨-u, by rw [← h, add_assoc, AddUnits.add_neg, add_zero]⟩,
     fun {a b c} ⟨u, h⟩ ⟨w, k⟩ => ⟨u + w, by rw [← k, ← h, AddUnits.val_add, add_assoc]⟩⟩
  add' := by
    rintro a b c d ⟨u, h⟩ ⟨w, k⟩
    refine ⟨u + w, ?_⟩
    rw [← h, ← k, AddUnits.val_add]
    abel

/-- The characteristic `M^char = M / M^±` of `M` (page 11), as the quotient monoid of
`characteristicCon`. -/
abbrev MonoidCharacteristic : Type _ := (characteristicCon M).Quotient

/-- `M` is *of characteristic type* (page 11): the fibers of `M ↠ M^char` are torsors over `M^±`.
Reading: `M^±` acts on each fiber by addition; the action is transitive by the definition of
the quotient, and the torsor condition asks that it be free, so for `a, b` in one fiber there is
exactly one invertible `u` with `a + u = b`. -/
def IsCharacteristicTypeMonoid : Prop :=
  ∀ a b : M, characteristicCon M a b → ∃! u : AddUnits M, a + (u : M) = b

/-- Erratum 30 of the comments on the paper: "of characteristic type" is automatic in
Definition 1.1 (i). Here: an integral monoid is of characteristic type. -/
theorem isCharacteristicTypeMonoid_of_isIntegralMonoid {M : Type*} [AddCommMonoid M]
    (h : IsIntegralMonoid M) : IsCharacteristicTypeMonoid M := by
  rintro a b ⟨u, hu⟩
  refine ⟨u, hu, fun w hw => ?_⟩
  apply AddUnits.ext
  apply h
  have : toGroupification M a + toGroupification M (w : M) =
      toGroupification M a + toGroupification M (u : M) := by
    rw [← map_add, ← map_add, hw, hu]
  exact add_left_cancel this

/-- Definition 1.1 (i), page 19: `M` is *pre-divisorial* if it is integral, saturated and of
characteristic type. All three conditions of the page are kept; by
`isCharacteristicTypeMonoid_of_isIntegralMonoid` the third is redundant (erratum 30). -/
def IsPreDivisorialMonoid : Prop :=
  IsIntegralMonoid M ∧ IsSaturatedMonoid M ∧ IsCharacteristicTypeMonoid M

/-- Pre-divisorial is equivalent to integral and saturated (erratum 30). -/
theorem isPreDivisorialMonoid_iff :
    IsPreDivisorialMonoid M ↔ IsIntegralMonoid M ∧ IsSaturatedMonoid M :=
  ⟨fun h => ⟨h.1, h.2.1⟩,
   fun h => ⟨h.1, h.2, isCharacteristicTypeMonoid_of_isIntegralMonoid h.1⟩⟩

/-- Definition 1.1 (i), page 19: a pre-divisorial `M` is *group-like* if `M^char` is zero. The
page defines the term only for pre-divisorial `M`, so that hypothesis is part of the
definition. -/
def IsGroupLikeMonoid : Prop :=
  IsPreDivisorialMonoid M ∧ ∀ x : MonoidCharacteristic M, x = 0

/-- Definition 1.1 (i), page 19: a pre-divisorial `M` is *divisorial* if it is sharp. The
pre-divisorial hypothesis of the page is part of the definition. -/
def IsDivisorialMonoid : Prop := IsPreDivisorialMonoid M ∧ IsSharpMonoid M

variable {M}

/-- The relation `a ≤ b` of page 12: `a + c = b` for some `c ∈ M`. The page introduces it for
sharp, integral, saturated `M`; it is defined here for every commutative monoid. -/
def MonoidDivides (a b : M) : Prop := ∃ c : M, a + c = b

/-- The relation `a ≼ b` of page 12: `a ≤ n · b` for some `n ∈ ℕ≥1`. -/
def MonoidPrecedes (a b : M) : Prop := ∃ n : ℕ+, MonoidDivides a ((n : ℕ) • b)

/-- An *irreducible* element (page 12): `a ≠ 0`, and `a = b + c` implies `b = 0` or `c = 0`. -/
def IsIrreducibleElem (a : M) : Prop := a ≠ 0 ∧ ∀ b c : M, a = b + c → b = 0 ∨ c = 0

/-- A *primary* element (page 12): `a ≠ 0`, and for every `b ≠ 0` with `b ≼ a`, `a ≼ b`. -/
def IsPrimaryElem (a : M) : Prop :=
  a ≠ 0 ∧ ∀ b : M, MonoidPrecedes b a → b ≠ 0 → MonoidPrecedes a b

variable {N : Type*} [AddCommMonoid N]

/-- The morphism `M^char → N^char` induced by a morphism `f : M → N` of commutative monoids. -/
def characteristicMap (f : M →+ N) : MonoidCharacteristic M →+ MonoidCharacteristic N :=
  (characteristicCon M).lift ((characteristicCon N).mk'.comp f) <| by
    rintro a b ⟨u, rfl⟩
    rw [AddCon.ker_rel, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, map_add]
    exact (AddCon.eq _).2 ⟨AddUnits.map f u, rfl⟩

/-- The induced map on characteristics sends the class of `a` to the class of `f(a)`. -/
theorem characteristicMap_mk (f : M →+ N) (a : M) :
    characteristicMap f ((characteristicCon M).mk' a) = (characteristicCon N).mk' (f a) :=
  rfl

/-- A morphism `f : M → N` is *characteristically injective* (page 11) if `f` is injective and
the induced morphism `M^char → N^char` is injective. -/
def IsCharInjective (f : M →+ N) : Prop :=
  Function.Injective f ∧ Function.Injective (characteristicMap f)

/-- Definition 1.1 (i), page 19: an endomorphism `α` of a pre-divisorial `M` is *non-dilating*
if `α^char` is the identity of `M^char` whenever `α^char(a) ≼ a` for every primary `a ∈ M^char`.
The pre-divisorial hypothesis of the page is part of the definition. -/
def IsNonDilating (α : M →+ M) : Prop :=
  IsPreDivisorialMonoid M ∧
    ((∀ a : MonoidCharacteristic M, IsPrimaryElem a → MonoidPrecedes (characteristicMap α a) a) →
      characteristicMap α = AddMonoidHom.id _)

end Monoids

/-! ## Examples showing the monoid conditions are nonvacuous -/

section MonoidExamples

/-- A cancellative commutative monoid is integral (via `Algebra.GrothendieckAddGroup.of_injective`). -/
theorem isIntegralMonoid_of_isCancelAdd (M : Type*) [AddCommMonoid M] [IsCancelAdd M] :
    IsIntegralMonoid M :=
  Algebra.GrothendieckAddGroup.of_injective

/-- Every element of `M^gp` is a difference of two elements of the image of `M`. -/
theorem exists_eq_sub_toGroupification {M : Type*} [AddCommMonoid M]
    (x : Algebra.GrothendieckAddGroup M) :
    ∃ p q : M, x = toGroupification M p - toGroupification M q := by
  induction x using AddLocalization.induction_on with
  | H y =>
    obtain ⟨p, q, hq⟩ := y
    refine ⟨p, q, ?_⟩
    have e : ∀ m : M, toGroupification M m = AddLocalization.mk m 0 := fun m => rfl
    rw [e, e, Algebra.GrothendieckAddGroup.mk_sub_mk]
    congr 1
    · simp
    · ext; simp

/-- A commutative group is saturated: `M → M^gp` is onto. -/
theorem isSaturatedMonoid_of_addCommGroup (M : Type*) [AddCommGroup M] :
    IsSaturatedMonoid M := by
  intro x _
  obtain ⟨p, q, rfl⟩ := exists_eq_sub_toGroupification x
  exact ⟨p - q, by rw [map_sub]⟩

/-- A sharp-type criterion: a canonically ordered commutative monoid is sharp. -/
theorem isSharpMonoid_of_canonicallyOrderedAdd (M : Type*) [AddCommMonoid M] [PartialOrder M]
    [CanonicallyOrderedAdd M] : IsSharpMonoid M := by
  intro u
  apply AddUnits.ext
  have h : (u : M) ≤ 0 := by
    calc (u : M) ≤ (u : M) + ((-u : AddUnits M) : M) := le_self_add
      _ = 0 := AddUnits.add_neg u
  exact le_antisymm h zero_le

/-- A linearly and canonically ordered cancellative commutative monoid is saturated. This covers
`ℕ`, `ℚ≥0` and `ℝ≥0`. -/
theorem isSaturatedMonoid_of_linearOrder (M : Type*) [AddCommMonoid M] [LinearOrder M]
    [IsOrderedCancelAddMonoid M] [CanonicallyOrderedAdd M] : IsSaturatedMonoid M := by
  rintro x ⟨n, m, hm⟩
  obtain ⟨p, q, rfl⟩ := exists_eq_sub_toGroupification x
  have hinj := isIntegralMonoid_of_isCancelAdd M
  have key : (n : ℕ) • p = m + (n : ℕ) • q := by
    apply hinj
    rw [map_nsmul, map_add, map_nsmul, hm, smul_sub, sub_add_cancel]
  have hle : q ≤ p := by
    have : (n : ℕ) • q ≤ (n : ℕ) • p := by rw [key]; exact le_add_self
    exact le_of_nsmul_le_nsmul_right (PNat.ne_zero n) this
  obtain ⟨d, rfl⟩ := exists_add_of_le hle
  exact ⟨d, by rw [map_add, add_sub_cancel_left]⟩

/-- A cancellative, linearly and canonically ordered commutative monoid is divisorial. -/
theorem isDivisorialMonoid_of_linearOrder (M : Type*) [AddCommMonoid M] [LinearOrder M]
    [IsOrderedCancelAddMonoid M] [CanonicallyOrderedAdd M] : IsDivisorialMonoid M :=
  ⟨(isPreDivisorialMonoid_iff M).2
      ⟨isIntegralMonoid_of_isCancelAdd M, isSaturatedMonoid_of_linearOrder M⟩,
    isSharpMonoid_of_canonicallyOrderedAdd M⟩

/-- `ℕ = ℤ≥0` under addition is divisorial. -/
theorem nat_isDivisorialMonoid : IsDivisorialMonoid ℕ := isDivisorialMonoid_of_linearOrder ℕ

/-- `ℚ≥0` under addition is divisorial. -/
theorem nnrat_isDivisorialMonoid : IsDivisorialMonoid ℚ≥0 :=
  isDivisorialMonoid_of_linearOrder ℚ≥0

/-- `ℝ≥0` under addition is divisorial. -/
theorem nnreal_isDivisorialMonoid : IsDivisorialMonoid NNReal :=
  isDivisorialMonoid_of_linearOrder NNReal

/-- `ℕ` is not perfect: `2 · a = 1` has no solution. -/
theorem nat_not_isPerfectMonoid : ¬ IsPerfectMonoid ℕ := by
  intro h
  obtain ⟨a, ha⟩ := (h 2).2 1
  simp only [PNat.val_ofNat, smul_eq_mul] at ha
  omega

/-- `ℚ≥0` is perfect. -/
theorem nnrat_isPerfectMonoid : IsPerfectMonoid ℚ≥0 := by
  intro n
  have hn : ((n : ℕ) : ℚ≥0) ≠ 0 := by exact_mod_cast PNat.ne_zero n
  refine ⟨fun a b hab => ?_, fun b => ⟨b / (n : ℕ), ?_⟩⟩
  · simp only [nsmul_eq_mul] at hab
    exact mul_left_cancel₀ hn hab
  · simp only [nsmul_eq_mul]
    exact mul_div_cancel₀ b hn

/-- `ℝ≥0` is perfect. -/
theorem nnreal_isPerfectMonoid : IsPerfectMonoid NNReal := by
  intro n
  have hn : ((n : ℕ) : NNReal) ≠ 0 := by exact_mod_cast PNat.ne_zero n
  refine ⟨fun a b hab => ?_, fun b => ⟨b / (n : ℕ), ?_⟩⟩
  · simp only [nsmul_eq_mul] at hab
    exact mul_left_cancel₀ hn hab
  · simp only [nsmul_eq_mul]
    exact mul_div_cancel₀ b hn

/-- `ℕ` is torsion-free. -/
theorem nat_isTorsionFreeMonoid : IsTorsionFreeMonoid ℕ := by
  intro a n h
  simp only [smul_eq_mul, mul_eq_zero] at h
  exact h.resolve_left (PNat.ne_zero n)

/-- `ZMod 2` is not torsion-free. -/
theorem zmod2_not_isTorsionFreeMonoid : ¬ IsTorsionFreeMonoid (ZMod 2) := by
  intro h
  exact absurd (h 1 2 (by decide)) (by decide)

/-- `ℤ` is pre-divisorial and group-like: its characteristic is zero. -/
theorem int_isGroupLikeMonoid : IsGroupLikeMonoid ℤ := by
  refine ⟨(isPreDivisorialMonoid_iff ℤ).2
    ⟨isIntegralMonoid_of_isCancelAdd ℤ, isSaturatedMonoid_of_addCommGroup ℤ⟩, ?_⟩
  intro x
  induction x using AddCon.induction_on with
  | H a =>
    rw [← (characteristicCon ℤ).coe_zero, AddCon.eq]
    exact ⟨AddUnits.mk (-a) a (by simp) (by simp), by simp⟩

/-- `ℤ` is not sharp, hence not divisorial. -/
theorem int_not_isSharpMonoid : ¬ IsSharpMonoid ℤ := by
  intro h
  have := congrArg AddUnits.val (h (AddUnits.mk 1 (-1) (by simp) (by simp)))
  simp at this

/-- `WithTop ℕ` is not integral: `0 + ⊤ = 1 + ⊤` and `M^gp` is a group. -/
theorem withTopNat_not_isIntegralMonoid : ¬ IsIntegralMonoid (WithTop ℕ) := by
  intro h
  have h01 : toGroupification (WithTop ℕ) 0 = toGroupification (WithTop ℕ) 1 := by
    have : toGroupification (WithTop ℕ) 0 + toGroupification (WithTop ℕ) ⊤ =
        toGroupification (WithTop ℕ) 1 + toGroupification (WithTop ℕ) ⊤ := by
      rw [← map_add, ← map_add, zero_add, WithTop.add_top]
    exact add_right_cancel this
  exact absurd (h h01) (by decide)

/-- `WithTop ℤ` is not of characteristic type: the units `0` and `1` act equally on `⊤`. -/
theorem withTopInt_not_isCharacteristicTypeMonoid :
    ¬ IsCharacteristicTypeMonoid (WithTop ℤ) := by
  intro h
  let one : AddUnits (WithTop ℤ) :=
    AddUnits.mk ((1 : ℤ) : WithTop ℤ) ((-1 : ℤ) : WithTop ℤ)
      (by rw [← WithTop.coe_add]; simp) (by rw [← WithTop.coe_add]; simp)
  obtain ⟨u, -, hu⟩ := h ⊤ ⊤ ⟨0, by simp⟩
  have h0 := hu 0 (by simp)
  have h1 := hu one (WithTop.top_add _)
  have := congrArg AddUnits.val (h1.trans h0.symm)
  simp [one] at this

end MonoidExamples

/-! ## Section 0: notions for categories used by Definitions 1.1 and 1.2 (pages 14 to 16) -/

section CategoryNotions

variable {C : Type u} [Category.{v} C]

/-- An arrow `β : B → A` is *fiberwise-surjective* (page 14) if for every arrow `γ : E → A` there
are arrows `δ_B : F → B`, `δ_E : F → E` with `β ∘ δ_B = γ ∘ δ_E`. -/
def IsFiberwiseSurjective {B A : C} (β : B ⟶ A) : Prop :=
  ∀ (E : C) (γ : E ⟶ A), ∃ (F : C) (δB : F ⟶ B) (δE : F ⟶ E), δB ≫ β = δE ≫ γ

/-- An *FSM-morphism* (page 14): a fiberwise-surjective monomorphism. -/
def IsFSMMorphism {B A : C} (β : B ⟶ A) : Prop := IsFiberwiseSurjective β ∧ Mono β

/-- A *totally epimorphic* category (page 15): every morphism is an epimorphism. -/
def IsTotallyEpimorphicCat (C : Type u) [Category.{v} C] : Prop :=
  ∀ (X Y : C) (f : X ⟶ Y), Epi f

end CategoryNotions

/-! ## Definition 1.1 (ii): monoids on a category (page 19) -/

section MonoidOn

variable {D : Type u} [Category.{v} D]

/-- Definition 1.1 (ii), page 19: a contravariant functor `Φ : D → Mon` (here `Dᵒᵖ ⥤
AddCommMonCat`) is a *monoid on `D`* if (a) every induced `α^* : Φ(A) → Φ(B)`, for
`α : B → A`, is characteristically injective, and (b) `α^*` is an isomorphism of monoids
(here: bijective) whenever `α` is an FSM-morphism. -/
def IsMonoidOn (Φ : Dᵒᵖ ⥤ AddCommMonCat.{w}) : Prop :=
  (∀ {B A : D} (α : B ⟶ A), IsCharInjective (Φ.map α.op).hom) ∧
    ∀ {B A : D} (α : B ⟶ A), IsFSMMorphism α → Function.Bijective (Φ.map α.op).hom

/-- Definition 1.1 (ii): `Φ` is *divisorial* if every `Φ(A)` is divisorial. -/
def IsDivisorialMonoidOn (Φ : Dᵒᵖ ⥤ AddCommMonCat.{w}) : Prop :=
  IsMonoidOn Φ ∧ ∀ A : D, IsDivisorialMonoid (Φ.obj (op A))

/-- Characteristic map of the identity. -/
theorem characteristicMap_id {M : Type*} [AddCommMonoid M] :
    characteristicMap (AddMonoidHom.id M) = AddMonoidHom.id _ := by
  ext x
  rfl

/-- The constant functor with value `ℕ` on a category in which every morphism is an identity
(here `Discrete PUnit`) is a divisorial monoid on that category: Definition 1.1 (ii) is
nonvacuous. -/
theorem constNat_isDivisorialMonoidOn :
    IsDivisorialMonoidOn
      ((Functor.const (Discrete PUnit.{1})ᵒᵖ).obj (AddCommMonCat.of ℕ)) := by
  refine ⟨⟨fun α => ?_, fun α _ => ?_⟩, fun _ => nat_isDivisorialMonoid⟩
  · refine ⟨fun a b h => h, ?_⟩
    change Function.Injective (characteristicMap (AddMonoidHom.id ℕ))
    rw [characteristicMap_id]
    exact fun a b h => h
  · exact Function.bijective_id

end MonoidOn

/-! ## Definition 1.1 (iii): the elementary Frobenioid `𝔽_Φ` (page 20) -/

section Elementary

variable {D : Type u} [Category.{v} D] (Φ : Dᵒᵖ ⥤ AddCommMonCat.{w})

/-- The objects of `𝔽_Φ`: the objects of `D`. -/
def ElemFrobObj (_Φ : Dᵒᵖ ⥤ AddCommMonCat.{w}) : Type u := D

/-- A morphism `A → B` of `𝔽_Φ`: a triple `(φ_D, Z_φ, n_φ)` with `φ_D : A_D → B_D` in `D`,
`Z_φ ∈ Φ(A_D)` and `n_φ ∈ ℕ≥1`. -/
abbrev ElemFrobHom (A B : D) : Type (max v w) := (A ⟶ B) × Φ.obj (op A) × ℕ+

variable {Φ}

/-- The projection `Base(φ) = φ_D`. -/
def elemBase {A B : D} (φ : ElemFrobHom Φ A B) : A ⟶ B := φ.1

/-- The zero divisor `Div(φ) = Z_φ ∈ Φ(A_D)`. -/
def elemDiv {A B : D} (φ : ElemFrobHom Φ A B) : Φ.obj (op A) := φ.2.1

/-- The Frobenius degree `deg_Fr(φ) = n_φ ∈ ℕ≥1`. -/
def elemDeg {A B : D} (φ : ElemFrobHom Φ A B) : ℕ+ := φ.2.2

variable (Φ)

/-- The identity of `A` in `𝔽_Φ`: `(id, 0, 1)`. -/
def elemFrobIdentity (A : D) : ElemFrobHom Φ A A := (𝟙 A, 0, 1)

variable {Φ}

/-- Composition in `𝔽_Φ` (page 20). For `φ = (φ_D, Z_φ, n_φ) : A → B` and
`ψ = (ψ_D, Z_ψ, n_ψ) : B → C`, the composite `ψ ∘ φ` (written `elemFrobCompose φ ψ`, in
diagrammatic order) is `(ψ_D ∘ φ_D, φ_D^*(Z_ψ) + n_ψ · Z_φ, n_ψ · n_φ)`. -/
def elemFrobCompose {A B C : D} (φ : ElemFrobHom Φ A B) (ψ : ElemFrobHom Φ B C) :
    ElemFrobHom Φ A C :=
  (φ.1 ≫ ψ.1, (Φ.map φ.1.op).hom ψ.2.1 + (ψ.2.2 : ℕ) • φ.2.1, ψ.2.2 * φ.2.2)

/-- Left identity law of `𝔽_Φ`: `φ ∘ id = φ`. -/
theorem elemFrobCompose_identity_left {A B : D} (φ : ElemFrobHom Φ A B) :
    elemFrobCompose (elemFrobIdentity Φ A) φ = φ := by
  obtain ⟨f, z, n⟩ := φ
  simp [elemFrobCompose, elemFrobIdentity]

/-- Right identity law of `𝔽_Φ`: `id ∘ φ = φ`. -/
theorem elemFrobCompose_identity_right {A B : D} (φ : ElemFrobHom Φ A B) :
    elemFrobCompose φ (elemFrobIdentity Φ B) = φ := by
  obtain ⟨f, z, n⟩ := φ
  simp [elemFrobCompose, elemFrobIdentity]

/-- Associativity of the composition of `𝔽_Φ`. -/
theorem elemFrobCompose_assoc {A B C E : D} (φ : ElemFrobHom Φ A B) (ψ : ElemFrobHom Φ B C)
    (χ : ElemFrobHom Φ C E) :
    elemFrobCompose (elemFrobCompose φ ψ) χ = elemFrobCompose φ (elemFrobCompose ψ χ) := by
  obtain ⟨f, z, n⟩ := φ
  obtain ⟨g, y, m⟩ := ψ
  obtain ⟨h, x, k⟩ := χ
  simp only [elemFrobCompose, op_comp, Functor.map_comp, AddCommMonCat.hom_comp,
    AddMonoidHom.comp_apply, map_add, map_nsmul, PNat.mul_coe, mul_nsmul, smul_add,
    Category.assoc, add_assoc, mul_assoc]
  rw [smul_comm (m : ℕ) (k : ℕ) z]

/-- In `𝔽_Φ`: `Base(ψ ∘ φ) = Base(ψ) ∘ Base(φ)`. -/
theorem elemBase_compose {A B C : D} (φ : ElemFrobHom Φ A B) (ψ : ElemFrobHom Φ B C) :
    elemBase (elemFrobCompose φ ψ) = elemBase φ ≫ elemBase ψ := rfl

/-- In `𝔽_Φ`: `Div(ψ ∘ φ) = Base(φ)^*(Div(ψ)) + deg_Fr(ψ) · Div(φ)`. -/
theorem elemDiv_compose {A B C : D} (φ : ElemFrobHom Φ A B) (ψ : ElemFrobHom Φ B C) :
    elemDiv (elemFrobCompose φ ψ) =
      (Φ.map (elemBase φ).op).hom (elemDiv ψ) + (elemDeg ψ : ℕ) • elemDiv φ := rfl

/-- In `𝔽_Φ` the Frobenius degree is multiplicative: `deg_Fr(ψ ∘ φ) = deg_Fr(ψ) · deg_Fr(φ)`. -/
theorem elemDeg_compose {A B C : D} (φ : ElemFrobHom Φ A B) (ψ : ElemFrobHom Φ B C) :
    elemDeg (elemFrobCompose φ ψ) = elemDeg ψ * elemDeg φ := rfl

variable (Φ)

/-- The category structure of the elementary Frobenioid `𝔽_Φ` (Definition 1.1 (iii)). It is a
plain definition, not a registered instance, because the library declares no instances; the
three laws are the theorems `elemFrobCompose_identity_left`, `elemFrobCompose_identity_right`
and `elemFrobCompose_assoc` about the concrete composition. -/
@[reducible] def elemFrobCategory : Category.{max v w} (ElemFrobObj Φ) where
  Hom A B := ElemFrobHom Φ A B
  id A := elemFrobIdentity Φ A
  comp φ ψ := elemFrobCompose φ ψ
  id_comp := elemFrobCompose_identity_left
  comp_id := elemFrobCompose_identity_right
  assoc := elemFrobCompose_assoc

/-- The natural projection functor `𝔽_Φ → D`. -/
def elemFrobProjection : @Functor (ElemFrobObj Φ) (elemFrobCategory Φ) D _ :=
  letI := elemFrobCategory Φ
  { obj := fun A => (A : D)
    map := fun φ => elemBase φ
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl }

end Elementary

/-! ## The elementary Frobenioid `𝔽_M` of a monoid and the standard Frobenioid (page 20) -/

section ElementaryMonoid

variable (M : Type*) [AddCommMonoid M]

/-- The underlying set `M × ℕ≥1` of the elementary Frobenioid `𝔽_M` associated to `M`. -/
abbrev ElemFrobMonoidCarrier : Type _ := M × ℕ+

variable {M}

/-- The product of `𝔽_M` (page 20): `(a₁, n₁) · (a₂, n₂) = (a₁ + n₁ · a₂, n₁ · n₂)`. It agrees
with the composition of `𝔽_Φ` for the one-object case, `(a₁, n₁) · (a₂, n₂)` being the composite
`ψ ∘ φ` with `ψ = (a₁, n₁)`, `φ = (a₂, n₂)` and `φ_D^*` the identity. -/
def elemFrobMul (x y : ElemFrobMonoidCarrier M) : ElemFrobMonoidCarrier M :=
  (x.1 + (x.2 : ℕ) • y.1, x.2 * y.2)

/-- Associativity of the product of `𝔽_M`. -/
theorem elemFrobMul_assoc (x y z : ElemFrobMonoidCarrier M) :
    elemFrobMul (elemFrobMul x y) z = elemFrobMul x (elemFrobMul y z) := by
  obtain ⟨a, n⟩ := x
  obtain ⟨b, m⟩ := y
  obtain ⟨c, k⟩ := z
  simp only [elemFrobMul, PNat.mul_coe, mul_nsmul, smul_add, add_assoc, mul_assoc]
  rw [smul_comm (m : ℕ) (n : ℕ) c]

/-- `(0, 1)` is a left unit of `𝔽_M`. -/
theorem elemFrobMul_unit_left (x : ElemFrobMonoidCarrier M) :
    elemFrobMul ((0, 1) : ElemFrobMonoidCarrier M) x = x := by
  obtain ⟨a, n⟩ := x
  simp [elemFrobMul]

/-- `(0, 1)` is a right unit of `𝔽_M`. -/
theorem elemFrobMul_unit_right (x : ElemFrobMonoidCarrier M) :
    elemFrobMul x ((0, 1) : ElemFrobMonoidCarrier M) = x := by
  obtain ⟨a, n⟩ := x
  simp [elemFrobMul]

variable (M)

/-- The monoid `𝔽_M` (page 20), as a plain definition (no instance is registered). -/
@[reducible] def elemFrobMonoid : Monoid (ElemFrobMonoidCarrier M) where
  mul := elemFrobMul
  one := ((0 : M), (1 : ℕ+))
  mul_assoc := elemFrobMul_assoc
  one_mul := elemFrobMul_unit_left
  mul_one := elemFrobMul_unit_right

/-- The standard Frobenioid `𝔽 = 𝔽_{ℤ≥0}` (page 20) is not commutative:
`(1, 1) · (0, 2) = (1, 2)` while `(0, 2) · (1, 1) = (2, 2)`. -/
theorem standardFrobenioid_mul_not_comm :
    elemFrobMul ((1, 1) : ElemFrobMonoidCarrier ℕ) (0, 2) = (1, 2) ∧
      elemFrobMul ((0, 2) : ElemFrobMonoidCarrier ℕ) (1, 1) = (2, 2) := by
  constructor <;> rfl

end ElementaryMonoid

/-! ## Definition 1.1 (iv) and Remark 1.1.1: functors to `𝔽_Φ` (pages 20 and 21) -/

section PreFrobenioid

variable {D : Type u} [Category.{v} D] {Φ : Dᵒᵖ ⥤ AddCommMonCat.{w}}

/-- A functor `C → 𝔽_Φ`, with the category structure `elemFrobCategory Φ` on the target. -/
abbrev FrobFunctor (C : Type u') [Category.{v'} C] (Φ : Dᵒᵖ ⥤ AddCommMonCat.{w}) :=
  @Functor C _ (ElemFrobObj Φ) (elemFrobCategory Φ)

variable {C : Type u'} [Category.{v'} C]

/-- Definition 1.1 (iv), page 20: a functor `C → 𝔽_Φ` is a *pre-Frobenioid structure* on `C`
when `Φ` is a divisorial monoid on `D` and `C`, `D` are connected, totally epimorphic
categories. Reading of "connected" (page 16: the graph of the category is connected): Mathlib's
`IsConnected`, which also asks the category to be nonempty. -/
def IsPreFrobenioidStructure (_P : FrobFunctor C Φ) : Prop :=
  IsDivisorialMonoidOn Φ ∧ IsConnected C ∧ IsConnected D ∧ IsTotallyEpimorphicCat C ∧
    IsTotallyEpimorphicCat D

variable (P : FrobFunctor C Φ)

/-- `Base(X) ∈ Ob(D)` for an object `X` of `C`. -/
def frobObj (X : C) : D := @Functor.obj C _ (ElemFrobObj Φ) (elemFrobCategory Φ) P X

/-- The morphism `P(f)` of `𝔽_Φ`, as a triple. -/
def frobImage {X Y : C} (f : X ⟶ Y) : ElemFrobHom Φ (frobObj P X) (frobObj P Y) :=
  letI := elemFrobCategory Φ
  P.map f

/-- Functoriality: the image of a composite is the composite in `𝔽_Φ`. -/
theorem frobImage_compose {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    frobImage P (f ≫ g) = elemFrobCompose (frobImage P f) (frobImage P g) := by
  let := elemFrobCategory Φ
  exact P.map_comp f g

/-- Functoriality: the image of an identity is the identity of `𝔽_Φ`. -/
theorem frobImage_identity (X : C) : frobImage P (𝟙 X) = elemFrobIdentity Φ (frobObj P X) := by
  let := elemFrobCategory Φ
  exact P.map_id X

/-- `Base(f)`, the projection of `f` to `D`. -/
def frobBase {X Y : C} (f : X ⟶ Y) : frobObj P X ⟶ frobObj P Y := elemBase (frobImage P f)

/-- `Div(f) ∈ Φ(Base(X))`, the zero divisor of `f : X → Y`. -/
def frobDiv {X Y : C} (f : X ⟶ Y) : Φ.obj (op (frobObj P X)) := elemDiv (frobImage P f)

/-- `deg_Fr(f) ∈ ℕ≥1`, the Frobenius degree of `f`. -/
def frobDeg {X Y : C} (f : X ⟶ Y) : ℕ+ := elemDeg (frobImage P f)

/-- Remark 1.1.1, page 21: `Base(φ ∘ ψ) = Base(φ) ∘ Base(ψ)` (here `ψ ≫ φ`). -/
theorem frobBase_compose {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    frobBase P (f ≫ g) = frobBase P f ≫ frobBase P g := by
  unfold frobBase
  rw [frobImage_compose]
  rfl

/-- Remark 1.1.1, page 21: `Div(φ ∘ ψ) = Base(ψ)^*(Div(φ)) + deg_Fr(φ) · Div(ψ)`, with
`ψ = f`, `φ = g`. -/
theorem frobDiv_compose {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    frobDiv P (f ≫ g) =
      (Φ.map (frobBase P f).op).hom (frobDiv P g) + ((frobDeg P g : ℕ)) • frobDiv P f := by
  unfold frobDiv frobBase frobDeg
  rw [frobImage_compose]
  rfl

/-- Remark 1.1.1, page 21: `deg_Fr(φ ∘ ψ) = deg_Fr(φ) · deg_Fr(ψ)`. -/
theorem frobDeg_compose {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    frobDeg P (f ≫ g) = frobDeg P g * frobDeg P f := by
  unfold frobDeg
  rw [frobImage_compose]
  rfl

/-- An identity has Frobenius degree `1`. -/
theorem frobDeg_identity (X : C) : frobDeg P (𝟙 X) = 1 := by
  unfold frobDeg
  rw [frobImage_identity]
  rfl

/-- An identity has zero divisor `0`. -/
theorem frobDiv_identity (X : C) : frobDiv P (𝟙 X) = 0 := by
  unfold frobDiv
  rw [frobImage_identity]
  rfl

/-- The base of an identity is an identity. -/
theorem frobBase_identity (X : C) : frobBase P (𝟙 X) = 𝟙 (frobObj P X) := by
  unfold frobBase
  rw [frobImage_identity]
  rfl

/-- `𝔽_Φ` itself, through its identity functor, as a functor to `𝔽_Φ`; the notions of
Definitions 1.2 and 1.3 thus apply to morphisms of `𝔽_Φ`. -/
def elemFrobIdentityFunctor (Φ : Dᵒᵖ ⥤ AddCommMonCat.{w}) :
    @FrobFunctor D _ (ElemFrobObj Φ) (elemFrobCategory Φ) Φ :=
  @Functor.id (ElemFrobObj Φ) (elemFrobCategory Φ)

/-- For `𝔽_Φ` through its identity functor, `deg_Fr` is the third component of the triple. -/
theorem frobDeg_elemFrobIdentityFunctor {A B : D} (φ : ElemFrobHom Φ A B) :
    @frobDeg D _ Φ (ElemFrobObj Φ) (elemFrobCategory Φ) (elemFrobIdentityFunctor Φ) A B φ =
      elemDeg φ := rfl

/-- For `𝔽_Φ` through its identity functor, `Div` is the second component of the triple. -/
theorem frobDiv_elemFrobIdentityFunctor {A B : D} (φ : ElemFrobHom Φ A B) :
    @frobDiv D _ Φ (ElemFrobObj Φ) (elemFrobCategory Φ) (elemFrobIdentityFunctor Φ) A B φ =
      elemDiv φ := rfl

/-- For `𝔽_Φ` through its identity functor, `Base` is the first component of the triple. -/
theorem frobBase_elemFrobIdentityFunctor {A B : D} (φ : ElemFrobHom Φ A B) :
    @frobBase D _ Φ (ElemFrobObj Φ) (elemFrobCategory Φ) (elemFrobIdentityFunctor Φ) A B φ =
      elemBase φ := rfl

end PreFrobenioid

/-! ## Definition 1.2: types of morphisms and objects (pages 21 to 23) -/

section Definition12

variable {D : Type u} [Category.{v} D] {Φ : Dᵒᵖ ⥤ AddCommMonCat.{w}}
variable {C : Type u'} [Category.{v'} C] (P : FrobFunctor C Φ)

/-- Definition 1.2 (i): `f` is *linear* if `deg_Fr(f) = 1`. -/
def IsLinearMor {X Y : C} (f : X ⟶ Y) : Prop := frobDeg P f = 1

/-- Definition 1.2 (i): `f` is *isometric* (an isometry) if `Div(f) = 0`. -/
def IsIsometricMor {X Y : C} (f : X ⟶ Y) : Prop := frobDiv P f = 0

/-- Definition 1.2 (i): co-objective `f, g` are *metrically equivalent* if `Div(f) = Div(g)`. -/
def AreMetricallyEquivalent {X Y : C} (f g : X ⟶ Y) : Prop := frobDiv P f = frobDiv P g

/-- Definition 1.2 (ii): `f` is a *base-isomorphism* if `Base(f)` is an isomorphism of `D`. -/
def IsBaseIsoMor {X Y : C} (f : X ⟶ Y) : Prop := IsIso (frobBase P f)

/-- Definition 1.2 (ii): `f` is a *base-FSM-morphism* if `Base(f)` is an FSM-morphism of `D`. -/
def IsBaseFSMMor {X Y : C} (f : X ⟶ Y) : Prop := IsFSMMorphism (frobBase P f)

/-- Definition 1.2 (ii): two objects are *base-isomorphic* if their images in `D` are
isomorphic. -/
def AreBaseIsomorphic (X Y : C) : Prop := Nonempty (frobObj P X ≅ frobObj P Y)

/-- Definition 1.2 (ii): `f : A → B` is a *pull-back morphism* if the natural transformation
`Hom_C(-, A) → Hom_C(-, B) ×_{Hom_D(-, B_D)|_C} Hom_D(-, A_D)|_C` induced by `f` is an
isomorphism. Stated pointwise: for every object `T` of `C`, the map sending `g : T → A` to the
pair `(f ∘ g, Base(g))` is a bijection onto the pairs `(h, k)` with `Base(h) = Base(f) ∘ k`. -/
def IsPullBackMor {A B : C} (f : A ⟶ B) : Prop :=
  ∀ T : C, Function.Bijective fun g : T ⟶ A =>
    (⟨(g ≫ f, frobBase P g), by simp only [frobBase_compose]⟩ :
      {p : (T ⟶ B) × (frobObj P T ⟶ frobObj P A) // frobBase P p.1 = p.2 ≫ frobBase P f})

/-- Definition 1.2 (ii): co-objective `f, g` are *base-equivalent* if `Base(f) = Base(g)`. -/
def AreBaseEquivalent {X Y : C} (f g : X ⟶ Y) : Prop := frobBase P f = frobBase P g

/-- Definition 1.2 (ii): co-objective `f, g` are *Div-equivalent* if `Φ(f) = Φ(g)`, read as
equality of the induced morphisms `Φ(Base(f)), Φ(Base(g)) : Φ(Y_D) → Φ(X_D)`. -/
def AreDivEquivalent {X Y : C} (f g : X ⟶ Y) : Prop :=
  Φ.map (frobBase P f).op = Φ.map (frobBase P g).op

/-- Definition 1.2 (ii): a *base-identity* endomorphism. -/
def IsBaseIdentityEndo {X : C} (f : X ⟶ X) : Prop := AreBaseEquivalent P f (𝟙 X)

/-- Definition 1.2 (ii): a *Div-identity* endomorphism. -/
def IsDivIdentityEndo {X : C} (f : X ⟶ X) : Prop := AreDivEquivalent P f (𝟙 X)

/-- Definition 1.2 (ii): `O^▷(X) ⊆ End_C(X)`, the base-identity linear endomorphisms. -/
def unitTriangleEndos (X : C) : Set (X ⟶ X) :=
  {f | IsBaseIdentityEndo P f ∧ IsLinearMor P f}

/-- Definition 1.2 (ii): `O^×(X) ⊆ Aut_C(X)`, the base-identity linear automorphisms (as the
endomorphisms in `O^▷(X)` that are isomorphisms). -/
def unitTimesAutos (X : C) : Set (X ⟶ X) :=
  {f | f ∈ unitTriangleEndos P X ∧ IsIso f}

/-- Definition 1.2 (iii): a *pre-step* is a linear base-isomorphism. -/
def IsPreStep {X Y : C} (f : X ⟶ Y) : Prop := IsLinearMor P f ∧ IsBaseIsoMor P f

/-- Definition 1.2 (iii): a *step* is a pre-step that is not an isomorphism. -/
def IsStepMor {X Y : C} (f : X ⟶ Y) : Prop := IsPreStep P f ∧ ¬ IsIso f

/-- Definition 1.2 (iii): a *primary* pre-step: a pre-step whose zero divisor is a primary
element of `Φ(X)`. -/
def IsPrimaryPreStep {X Y : C} (f : X ⟶ Y) : Prop :=
  IsPreStep P f ∧ IsPrimaryElem (frobDiv P f)

/-- Definition 1.2 (iii): `φ` is *co-angular* if for every factorization `φ = α ∘ β ∘ γ` with
`α` linear, `β` an isometric pre-step, and `α` or `γ` a base-isomorphism, `β` is an
isomorphism. -/
def IsCoAngular {A B : C} (φ : A ⟶ B) : Prop :=
  ∀ (X Y : C) (γ : A ⟶ X) (β : X ⟶ Y) (α : Y ⟶ B), γ ≫ β ≫ α = φ →
    IsLinearMor P α → IsIsometricMor P β → IsPreStep P β →
      (IsBaseIsoMor P α ∨ IsBaseIsoMor P γ) → IsIso β

/-- Definition 1.2 (iii): *LB-invertible*: co-angular and isometric. -/
def IsLBInvertible {X Y : C} (f : X ⟶ Y) : Prop := IsCoAngular P f ∧ IsIsometricMor P f

/-- Definition 1.2 (iii): a *morphism of Frobenius type*: an LB-invertible base-isomorphism. -/
def IsFrobeniusTypeMor {X Y : C} (f : X ⟶ Y) : Prop := IsLBInvertible P f ∧ IsBaseIsoMor P f

/-- Definition 1.2 (iii): a *prime-Frobenius morphism*: of Frobenius type with prime Frobenius
degree. -/
def IsPrimeFrobeniusMor {X Y : C} (f : X ⟶ Y) : Prop :=
  IsFrobeniusTypeMor P f ∧ (frobDeg P f : ℕ).Prime

/-- Definition 1.2 (iv): a *Frobenius-ample* object admits an endomorphism of every Frobenius
degree `n ∈ ℕ≥1`. -/
def IsFrobeniusAmpleObj (X : C) : Prop := ∀ n : ℕ+, ∃ f : X ⟶ X, frobDeg P f = n

/-- Definition 1.2 (iv): a *Frobenius-trivial* object `X` admits a monoid homomorphism
`ζ : ℕ≥1 → End_C(X)` with (a) `deg_Fr ∘ ζ = id` and (b) every `ζ(n)` a base-identity
endomorphism of Frobenius type. (`ℕ≥1` is commutative, so the composition convention of
`End X` does not matter.) -/
def IsFrobeniusTrivialObj (X : C) : Prop :=
  ∃ ζ : ℕ+ →* End X, (∀ n, frobDeg P ((ζ n).asHom) = n) ∧
    ∀ n, IsBaseIdentityEndo P ((ζ n).asHom) ∧
      IsFrobeniusTypeMor P ((ζ n).asHom)

/-- Definition 1.2 (iv): an *isotropic* object: every isometric pre-step out of it is an
isomorphism. -/
def IsIsotropicObj (X : C) : Prop :=
  ∀ (Y : C) (f : X ⟶ Y), IsIsometricMor P f → IsPreStep P f → IsIso f

/-- Definition 1.2 (iv): `φ : A → B` is an *isotropic hull* of `A` if `φ` is an isometric
pre-step, `B` is isotropic, and every `γ : A → E` with `E` isotropic factors uniquely as
`γ = β ∘ φ`. -/
def IsIsotropicHull {A B : C} (φ : A ⟶ B) : Prop :=
  IsIsometricMor P φ ∧ IsPreStep P φ ∧ IsIsotropicObj P B ∧
    ∀ (E : C) (γ : A ⟶ E), IsIsotropicObj P E → ∃! β : B ⟶ E, φ ≫ β = γ

/-- Linear morphisms are closed under composition (from Remark 1.1.1). -/
theorem IsLinearMor.compose {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsLinearMor P f)
    (hg : IsLinearMor P g) : IsLinearMor P (f ≫ g) := by
  unfold IsLinearMor at *
  rw [frobDeg_compose, hf, hg, mul_one]

/-- Pre-steps are closed under composition. -/
theorem IsPreStep.compose {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsPreStep P f)
    (hg : IsPreStep P g) : IsPreStep P (f ≫ g) := by
  refine ⟨hf.1.compose P hg.1, ?_⟩
  unfold IsBaseIsoMor
  rw [frobBase_compose]
  have : IsIso (frobBase P f) := hf.2
  have : IsIso (frobBase P g) := hg.2
  infer_instance

/-- Identities are pre-steps and isometric. -/
theorem isPreStep_identity (X : C) : IsPreStep P (𝟙 X) ∧ IsIsometricMor P (𝟙 X) := by
  refine ⟨⟨frobDeg_identity P X, ?_⟩, frobDiv_identity P X⟩
  unfold IsBaseIsoMor
  rw [frobBase_identity]
  infer_instance

/-- The Frobenius degree of the `n`-fold composite of an endomorphism `f` is `deg_Fr(f)^n`. -/
theorem frobDeg_pow {X : C} (f : End X) (n : ℕ) :
    frobDeg P (f ^ n).asHom = frobDeg P f.asHom ^ n := by
  induction n with
  | zero => exact frobDeg_identity P X
  | succ n ih =>
    rw [pow_succ, pow_succ, End.mul_asHom, frobDeg_compose, ih, mul_comm]

end Definition12

/-! ## Definition 1.3: the clauses stated here (pages 24 and 25) -/

section Definition13

variable {D : Type u} [Category.{v} D] {Φ : Dᵒᵖ ⥤ AddCommMonCat.{w}}
variable {C : Type u'} [Category.{v'} C] (P : FrobFunctor C Φ)

/-- Remark 1.2.1, page 24: a base-identity endomorphism is a Div-identity endomorphism. -/
theorem IsBaseIdentityEndo.isDivIdentityEndo {X : C} {f : X ⟶ X}
    (h : IsBaseIdentityEndo P f) : IsDivIdentityEndo P f := by
  unfold IsDivIdentityEndo AreDivEquivalent
  rw [show frobBase P f = frobBase P (𝟙 X) from h]

/-- Definition 1.3 (i) (a): every isomorphism class of `D` is the image of the isomorphism class
of a Frobenius-trivial object of `C`. -/
def FrobCondIA : Prop :=
  ∀ X : D, ∃ A : C, IsFrobeniusTrivialObj P A ∧ Nonempty (frobObj P A ≅ X)

/-- Definition 1.3 (i) (b): for every isomorphism `α : A_D ≅ B_D` there are pre-steps
`φ : E → A`, `ψ : E → B` with `α = Base(ψ) ∘ Base(φ)⁻¹`, stated without the inverse as
`α ∘ Base(φ) = Base(ψ)`. -/
def FrobCondIB : Prop :=
  ∀ (A B : C) (α : frobObj P A ≅ frobObj P B), ∃ (E : C) (φ : E ⟶ A) (ψ : E ⟶ B),
    IsPreStep P φ ∧ IsPreStep P ψ ∧ frobBase P φ ≫ α.hom = frobBase P ψ

/-- Definition 1.3 (ii): for every `A` and `n ∈ ℕ≥1` there is a morphism of Frobenius type
`φ : A → B` of degree `n`, and every other `ψ : A → E` of Frobenius type and degree `n` is
`β ∘ φ` for an isomorphism `β : B ≅ E`. -/
def FrobCondII : Prop :=
  ∀ (A : C) (n : ℕ+), ∃ (B : C) (φ : A ⟶ B), IsFrobeniusTypeMor P φ ∧ frobDeg P φ = n ∧
    ∀ (E : C) (ψ : A ⟶ E), IsFrobeniusTypeMor P ψ → frobDeg P ψ = n →
      ∃ β : B ≅ E, φ ≫ β.hom = ψ

/-- Definition 1.3 (iii) (a): co-angular morphisms are closed under composition. -/
def FrobCondIIIA : Prop :=
  ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), IsCoAngular P f → IsCoAngular P g →
    IsCoAngular P (f ≫ g)

/-- Definition 1.3 (iii) (b): if `A' → A` is a co-angular pre-step, then every morphism
`A' → A` is co-angular. -/
def FrobCondIIIB : Prop :=
  ∀ {A' A : C} (f : A' ⟶ A), IsCoAngular P f → IsPreStep P f → ∀ g : A' ⟶ A, IsCoAngular P g

/-- A bijection `e : O^▷(A) ≅ O^▷(B)` is *induced* by `φ : A → B` (Definition 1.3 (iii) (c)) if
it is multiplicative and `e(α) ∘ φ = φ ∘ α` for every `α ∈ O^▷(A)`. -/
def IsInducedUnitBijection {A B : C} (φ : A ⟶ B)
    (e : unitTriangleEndos P A ≃ unitTriangleEndos P B) : Prop :=
  (∀ α : unitTriangleEndos P A, φ ≫ (e α).1 = α.1 ≫ φ) ∧
    ∀ α α' α'' : unitTriangleEndos P A, α.1 ≫ α'.1 = α''.1 →
      (e α).1 ≫ (e α').1 = (e α'').1

/-- Definition 1.3 (iii) (c): every co-angular pre-step `φ : A → B` induces a bijection of
monoids `O^▷(A) ≅ O^▷(B)`, and the induced bijection depends only on `Base(φ)`. The bracketed
uniqueness of the page is included (take `φ' = φ`); it holds automatically when `C` is totally
epimorphic. -/
def FrobCondIIIC : Prop :=
  ∀ {A B : C} (φ : A ⟶ B), IsCoAngular P φ → IsPreStep P φ →
    (∃ e, IsInducedUnitBijection P φ e) ∧
      ∀ (φ' : A ⟶ B), IsCoAngular P φ' → IsPreStep P φ' → AreBaseEquivalent P φ φ' →
        ∀ e e', IsInducedUnitBijection P φ e → IsInducedUnitBijection P φ' e' → e = e'

/-- Definition 1.3 (iv) (a): every `φ : A → B` factors as `φ = α ∘ β ∘ γ` with `α` a pull-back
morphism, `β` a pre-step and `γ` of Frobenius type, uniquely up to replacing `(α, β, γ)` by
`(α ∘ δ, δ⁻¹ ∘ β ∘ ε, ε⁻¹ ∘ γ)` for isomorphisms `δ`, `ε`. -/
def FrobCondIVA : Prop :=
  ∀ {A B : C} (φ : A ⟶ B),
    (∃ (X Y : C) (γ : A ⟶ X) (β : X ⟶ Y) (α : Y ⟶ B), γ ≫ β ≫ α = φ ∧
      IsPullBackMor P α ∧ IsPreStep P β ∧ IsFrobeniusTypeMor P γ) ∧
    ∀ (X Y X' Y' : C) (γ : A ⟶ X) (β : X ⟶ Y) (α : Y ⟶ B) (γ' : A ⟶ X') (β' : X' ⟶ Y')
      (α' : Y' ⟶ B),
      γ ≫ β ≫ α = φ → IsPullBackMor P α → IsPreStep P β → IsFrobeniusTypeMor P γ →
      γ' ≫ β' ≫ α' = φ → IsPullBackMor P α' → IsPreStep P β' → IsFrobeniusTypeMor P γ' →
      ∃ (δ : Y' ≅ Y) (ε : X' ≅ X), α' = δ.hom ≫ α ∧ β' = ε.hom ≫ β ≫ δ.inv ∧
        γ' = γ ≫ ε.inv

/-- Definition 1.3 (iv) (b): every pull-back morphism is LB-invertible and linear. -/
def FrobCondIVB : Prop :=
  ∀ {A B : C} (f : A ⟶ B), IsPullBackMor P f → IsLBInvertible P f ∧ IsLinearMor P f

/-- Definition 1.3 (v) (a): every pre-step is a monomorphism. -/
def FrobCondVA : Prop := ∀ {A B : C} (f : A ⟶ B), IsPreStep P f → Mono f

/-- The factorization pattern of Definition 1.3 (v) (b) and (c): `φ = α ∘ β` with `α` in the
class `Sα` and `β` in the class `Sβ`, unique up to replacing `(α, β)` by `(α ∘ γ, γ⁻¹ ∘ β)` for an
isomorphism `γ`. -/
def HasUniqueTwoFactorization {A B : C} (φ : A ⟶ B) (Sα Sβ : ∀ {X Y : C}, (X ⟶ Y) → Prop) :
    Prop :=
  (∃ (X : C) (β : A ⟶ X) (α : X ⟶ B), β ≫ α = φ ∧ Sα α ∧ Sβ β) ∧
    ∀ (X X' : C) (β : A ⟶ X) (α : X ⟶ B) (β' : A ⟶ X') (α' : X' ⟶ B),
      β ≫ α = φ → Sα α → Sβ β → β' ≫ α' = φ → Sα α' → Sβ β' →
        ∃ γ : X' ≅ X, α' = γ.hom ≫ α ∧ β' = β ≫ γ.inv

/-- Definition 1.3 (v) (b): every pre-step factors as an isometric pre-step after a co-angular
pre-step, uniquely up to isomorphism. -/
def FrobCondVB : Prop :=
  ∀ {A B : C} (φ : A ⟶ B), IsPreStep P φ →
    HasUniqueTwoFactorization φ (fun f => IsIsometricMor P f ∧ IsPreStep P f)
      (fun f => IsCoAngular P f ∧ IsPreStep P f)

/-- Definition 1.3 (v) (c): every pre-step factors as a co-angular pre-step after an isometric
pre-step, uniquely up to isomorphism. -/
def FrobCondVC : Prop :=
  ∀ {A B : C} (φ : A ⟶ B), IsPreStep P φ →
    HasUniqueTwoFactorization φ (fun f => IsCoAngular P f ∧ IsPreStep P f)
      (fun f => IsIsometricMor P f ∧ IsPreStep P f)

/-- Definition 1.3 (vi): base-equivalent, metrically equivalent co-angular pre-steps
`φ, ψ : A → B` satisfy `φ = α ∘ ψ` for some `α ∈ O^×(B)`. -/
def FrobCondVI : Prop :=
  ∀ {A B : C} (φ ψ : A ⟶ B), AreBaseEquivalent P φ ψ → AreMetricallyEquivalent P φ ψ →
    IsCoAngular P φ → IsPreStep P φ → IsCoAngular P ψ → IsPreStep P ψ →
      ∃ α ∈ unitTimesAutos P B, φ = ψ ≫ α

/-- Definition 1.3 (vii) (a): every object has an isotropic hull. -/
def FrobCondVIIA : Prop := ∀ A : C, ∃ (B : C) (φ : A ⟶ B), IsIsotropicHull P φ

/-- Definition 1.3 (vii) (b): the codomain of a morphism out of an isotropic object is
isotropic. -/
def FrobCondVIIB : Prop :=
  ∀ {A E : C} (_f : A ⟶ E), IsIsotropicObj P A → IsIsotropicObj P E

/-- The conditions of Definition 1.3 (pages 24 and 25) that are stated in this file, together
with the pre-Frobenioid hypotheses of Definition 1.1 (iv). This is not the definition of a
Frobenioid: clauses (i) (c) and (iii) (d) are omitted (see the module docstring). Every clause
that is included has a verified example: all fifteen conjuncts hold for the elementary
Frobenioid `𝔽_ℕ` over `Discrete PUnit` (`natPoint_partialFrobenioidConditions`). -/
def PartialFrobenioidConditions : Prop :=
  IsPreFrobenioidStructure P ∧ FrobCondIA P ∧ FrobCondIB P ∧ FrobCondII P ∧
    FrobCondIIIA P ∧ FrobCondIIIB P ∧ FrobCondIIIC P ∧ FrobCondIVA P ∧ FrobCondIVB P ∧
    FrobCondVA P ∧ FrobCondVB P ∧ FrobCondVC P ∧ FrobCondVI P ∧ FrobCondVIIA P ∧
    FrobCondVIIB P

end Definition13
/-! ## An example: `𝔽_ℕ` over a one-object, one-morphism base (Proposition 1.5, page 27) -/

section NatPointExample

/-- The constant monoid `ℕ` on the one-object, one-morphism category `Discrete PUnit`. -/
def natPointMonoid : (Discrete PUnit.{1})ᵒᵖ ⥤ AddCommMonCat.{0} :=
  (Functor.const _).obj (AddCommMonCat.of ℕ)

/-- `𝔽_ℕ` over `Discrete PUnit`, through its identity functor, as a functor to `𝔽_ℕ`. -/
def natPointFrobFunctor :
    @FrobFunctor (Discrete PUnit.{1}) _ (ElemFrobObj natPointMonoid)
      (elemFrobCategory natPointMonoid) natPointMonoid :=
  elemFrobIdentityFunctor natPointMonoid

/-- The morphism of the example with zero divisor `z` and Frobenius degree `n`. -/
def natPointHom (A B : ElemFrobObj natPointMonoid) (z : ℕ) (n : ℕ+) :
    ElemFrobHom natPointMonoid A B :=
  (eqToHom (Subsingleton.elim (α := Discrete PUnit.{1}) A B), z, n)

/-- The zero divisor of a morphism of the example, as a natural number. -/
def natPointDiv {A B : ElemFrobObj natPointMonoid} (f : ElemFrobHom natPointMonoid A B) : ℕ :=
  f.2.1

/-- The Frobenius degree of a morphism of the example, as a natural number. -/
def natPointDeg {A B : ElemFrobObj natPointMonoid} (f : ElemFrobHom natPointMonoid A B) : ℕ :=
  (f.2.2 : ℕ)

/-- A morphism of the example is determined by its zero divisor and Frobenius degree. -/
theorem natPoint_eq_iff :
    letI := elemFrobCategory natPointMonoid
    ∀ {A B : ElemFrobObj natPointMonoid} (f g : A ⟶ B),
      f = g ↔ natPointDiv f = natPointDiv g ∧ natPointDeg f = natPointDeg g := by
  intro A B f g
  refine ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h1, h2⟩ => ?_⟩
  have hs : Subsingleton (@Quiver.Hom (Discrete PUnit.{1}) _ (@id (Discrete PUnit.{1}) A)
      (@id (Discrete PUnit.{1}) B)) := inferInstance
  exact Prod.ext (@Subsingleton.elim _ hs _ _) (Prod.ext h1 (PNat.coe_injective h2))

/-- In the example, `Div(g ∘ f) = Div(g) + deg(g) · Div(f)`. -/
theorem natPointDiv_comp :
    letI := elemFrobCategory natPointMonoid
    ∀ {A B E : ElemFrobObj natPointMonoid} (f : A ⟶ B) (g : B ⟶ E),
      natPointDiv (f ≫ g) = natPointDiv g + natPointDeg g * natPointDiv f :=
  fun _ _ => rfl

/-- In the example, `deg(g ∘ f) = deg(g) · deg(f)`. -/
theorem natPointDeg_comp :
    letI := elemFrobCategory natPointMonoid
    ∀ {A B E : ElemFrobObj natPointMonoid} (f : A ⟶ B) (g : B ⟶ E),
      natPointDeg (f ≫ g) = natPointDeg g * natPointDeg f :=
  fun _ _ => PNat.mul_coe _ _

/-- The zero divisor of `natPointHom A B z n` is `z`. -/
theorem natPointDiv_hom (A B : ElemFrobObj natPointMonoid) (z : ℕ) (n : ℕ+) :
    natPointDiv (natPointHom A B z n) = z := rfl

/-- The Frobenius degree of `natPointHom A B z n` is `n`. -/
theorem natPointDeg_hom (A B : ElemFrobObj natPointMonoid) (z : ℕ) (n : ℕ+) :
    natPointDeg (natPointHom A B z n) = n := rfl

/-- Identities of the example have zero divisor `0` and degree `1`. -/
theorem natPoint_identity :
    letI := elemFrobCategory natPointMonoid
    ∀ A : ElemFrobObj natPointMonoid, natPointDiv (𝟙 A) = 0 ∧ natPointDeg (𝟙 A) = 1 :=
  fun _ => ⟨rfl, rfl⟩

/-- Frobenius degrees of the example are positive. -/
theorem natPointDeg_pos {A B : ElemFrobObj natPointMonoid} (f : ElemFrobHom natPointMonoid A B) :
    0 < natPointDeg f := PNat.pos _

/-- The isomorphism between any two objects of the example with zero divisor `0` and degree
`1`. -/
def natPointIso :
    letI := elemFrobCategory natPointMonoid
    ∀ A B : ElemFrobObj natPointMonoid, A ≅ B := by
  letI := elemFrobCategory natPointMonoid
  intro A B
  refine ⟨natPointHom A B 0 1, natPointHom B A 0 1, ?_, ?_⟩ <;>
  · refine (natPoint_eq_iff _ _).2 ⟨?_, ?_⟩
    · rw [natPointDiv_comp, natPointDiv_hom, natPointDiv_hom, (natPoint_identity _).1]
      simp
    · rw [natPointDeg_comp, natPointDeg_hom, natPointDeg_hom, (natPoint_identity _).2]
      simp

/-- The forward morphism of `natPointIso`. -/
theorem natPointIso_hom :
    letI := elemFrobCategory natPointMonoid
    ∀ A B : ElemFrobObj natPointMonoid, (natPointIso A B).hom = natPointHom A B 0 1 :=
  fun _ _ => rfl

/-- The inverse morphism of `natPointIso`. -/
theorem natPointIso_inv :
    letI := elemFrobCategory natPointMonoid
    ∀ A B : ElemFrobObj natPointMonoid, (natPointIso A B).inv = natPointHom B A 0 1 :=
  fun _ _ => rfl

/-- In the example, a morphism is an isomorphism if and only if its zero divisor is `0` and its
degree is `1`. -/
theorem natPoint_isIso_iff :
    letI := elemFrobCategory natPointMonoid
    ∀ {A B : ElemFrobObj natPointMonoid} (f : A ⟶ B),
      IsIso f ↔ natPointDiv f = 0 ∧ natPointDeg f = 1 := by
  let := elemFrobCategory natPointMonoid
  intro A B f
  constructor
  · intro hf
    have h := (natPoint_eq_iff _ _).1 (IsIso.hom_inv_id f)
    rw [natPointDiv_comp, natPointDeg_comp, (natPoint_identity _).1,
      (natPoint_identity _).2] at h
    have hpos := natPointDeg_pos (inv f)
    refine ⟨?_, Nat.eq_one_of_mul_eq_one_left h.2⟩
    have h0 : natPointDeg (inv f) * natPointDiv f = 0 := by omega
    rcases Nat.mul_eq_zero.1 h0 with h' | h'
    · omega
    · exact h'
  · rintro ⟨h1, h2⟩
    have e : f = (natPointIso A B).hom := by
      rw [natPointIso_hom]
      exact (natPoint_eq_iff _ _).2 ⟨h1, h2⟩
    rw [e]
    infer_instance

/-- In the example, every morphism is a base-isomorphism. -/
theorem natPoint_isBaseIsoMor :
    letI := elemFrobCategory natPointMonoid
    ∀ {A B : ElemFrobObj natPointMonoid} (f : A ⟶ B), IsBaseIsoMor natPointFrobFunctor f := by
  intro A B f
  exact ⟨⟨eqToHom (Subsingleton.elim _ _), Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩

/-- In the example, a morphism is a pre-step if and only if its degree is `1`. -/
theorem natPoint_isPreStep :
    letI := elemFrobCategory natPointMonoid
    ∀ {A B : ElemFrobObj natPointMonoid} (f : A ⟶ B),
      IsPreStep natPointFrobFunctor f ↔ natPointDeg f = 1 := by
  let := elemFrobCategory natPointMonoid
  intro A B f
  exact ⟨fun h => congrArg PNat.val h.1,
    fun h => ⟨PNat.coe_injective h, natPoint_isBaseIsoMor f⟩⟩

/-- In the example, every morphism is co-angular: an isometric pre-step has zero divisor `0`
and degree `1`, hence is an isomorphism. -/
theorem natPoint_isCoAngular :
    letI := elemFrobCategory natPointMonoid
    ∀ {A B : ElemFrobObj natPointMonoid} (f : A ⟶ B), IsCoAngular natPointFrobFunctor f := by
  let := elemFrobCategory natPointMonoid
  intro A B f X Y γ β α _ _ hβ hpre _
  exact (natPoint_isIso_iff β).2 ⟨hβ, (natPoint_isPreStep β).1 hpre⟩

/-- In the example, a morphism is of Frobenius type if and only if its zero divisor is `0`. -/
theorem natPoint_isFrobeniusTypeMor :
    letI := elemFrobCategory natPointMonoid
    ∀ {A B : ElemFrobObj natPointMonoid} (f : A ⟶ B),
      IsFrobeniusTypeMor natPointFrobFunctor f ↔ natPointDiv f = 0 := by
  let := elemFrobCategory natPointMonoid
  intro A B f
  exact ⟨fun h => h.1.2, fun h => ⟨⟨natPoint_isCoAngular f, h⟩, natPoint_isBaseIsoMor f⟩⟩

/-- In the example, every object is isotropic. -/
theorem natPoint_isIsotropicObj :
    letI := elemFrobCategory natPointMonoid
    ∀ X : ElemFrobObj natPointMonoid, IsIsotropicObj natPointFrobFunctor X := by
  let := elemFrobCategory natPointMonoid
  intro X Y f h hpre
  exact (natPoint_isIso_iff f).2 ⟨h, (natPoint_isPreStep f).1 hpre⟩

/-- In the example, a pull-back morphism has zero divisor `0` and degree `1`. -/
theorem natPoint_of_isPullBackMor :
    letI := elemFrobCategory natPointMonoid
    ∀ {A B : ElemFrobObj natPointMonoid} (f : A ⟶ B), IsPullBackMor natPointFrobFunctor f →
      natPointDiv f = 0 ∧ natPointDeg f = 1 := by
  let := elemFrobCategory natPointMonoid
  intro A B f hf
  obtain ⟨g, hg⟩ := (hf A).2 ⟨(natPointHom A B 0 1, 𝟙 _), Subsingleton.elim _ _⟩
  have h := (natPoint_eq_iff (g ≫ f) (natPointHom A B 0 1)).1 (congrArg (fun p => p.1.1) hg)
  rw [natPointDiv_comp, natPointDeg_comp, natPointDiv_hom, natPointDeg_hom] at h
  exact ⟨by simp at h; omega, Nat.eq_one_of_mul_eq_one_right h.2⟩

/-- In the example, a morphism with zero divisor `0` and degree `1` is a pull-back morphism. -/
theorem natPoint_isPullBackMor :
    letI := elemFrobCategory natPointMonoid
    ∀ {A B : ElemFrobObj natPointMonoid} (f : A ⟶ B), natPointDiv f = 0 → natPointDeg f = 1 →
      IsPullBackMor natPointFrobFunctor f := by
  let := elemFrobCategory natPointMonoid
  intro A B f h1 h2 T
  have key : ∀ g : T ⟶ A, natPointDiv (g ≫ f) = natPointDiv g ∧
      natPointDeg (g ≫ f) = natPointDeg g := by
    intro g
    rw [natPointDiv_comp, natPointDeg_comp, h1, h2]
    simp
  refine ⟨fun g g' hgg => ?_, fun ⟨⟨h, k⟩, hk⟩ => ?_⟩
  · have e := (natPoint_eq_iff _ _).1 (congrArg (fun p => p.1.1) hgg)
    simp only at e
    rw [(key g).1, (key g).2, (key g').1, (key g').2] at e
    exact (natPoint_eq_iff _ _).2 e
  · refine ⟨natPointHom T A (natPointDiv h) h.2.2,
      Subtype.ext (Prod.ext ?_ (Subsingleton.elim _ _))⟩
    change natPointHom T A (natPointDiv h) h.2.2 ≫ f = h
    refine (natPoint_eq_iff _ _).2 ⟨?_, ?_⟩
    · rw [(key _).1, natPointDiv_hom]
    · rw [(key _).2, natPointDeg_hom]
      rfl

/-- In the example, every morphism is a monomorphism. -/
theorem natPoint_mono :
    letI := elemFrobCategory natPointMonoid
    ∀ {A B : ElemFrobObj natPointMonoid} (f : A ⟶ B), Mono f := by
  let := elemFrobCategory natPointMonoid
  intro A B f
  refine ⟨fun {Z} g h e => ?_⟩
  have e' := (natPoint_eq_iff _ _).1 e
  rw [natPointDiv_comp, natPointDeg_comp, natPointDiv_comp, natPointDeg_comp] at e'
  have hp := natPointDeg_pos f
  exact (natPoint_eq_iff _ _).2
    ⟨Nat.eq_of_mul_eq_mul_left hp (by omega), Nat.eq_of_mul_eq_mul_left hp e'.2⟩

/-- In the example, every morphism is an epimorphism. -/
theorem natPoint_epi :
    letI := elemFrobCategory natPointMonoid
    ∀ {A B : ElemFrobObj natPointMonoid} (f : A ⟶ B), Epi f := by
  let := elemFrobCategory natPointMonoid
  intro A B f
  refine ⟨fun {Z} g h e => ?_⟩
  have e' := (natPoint_eq_iff _ _).1 e
  rw [natPointDiv_comp, natPointDeg_comp, natPointDiv_comp, natPointDeg_comp] at e'
  have hdeg : natPointDeg g = natPointDeg h :=
    Nat.eq_of_mul_eq_mul_right (natPointDeg_pos f) e'.2
  rw [hdeg] at e'
  exact (natPoint_eq_iff _ _).2 ⟨by omega, hdeg⟩

/-- The pre-Frobenioid hypotheses hold for the example: `ℕ` is divisorial, and both
`Discrete PUnit` and `𝔽_ℕ` are connected and totally epimorphic. -/
theorem natPoint_isPreFrobenioidStructure :
    @IsPreFrobenioidStructure (Discrete PUnit.{1}) _ natPointMonoid (ElemFrobObj natPointMonoid)
      (elemFrobCategory natPointMonoid) natPointFrobFunctor := by
  let := elemFrobCategory natPointMonoid
  have : Nonempty (ElemFrobObj natPointMonoid) := ⟨(⟨⟨⟩⟩ : Discrete PUnit.{1})⟩
  have : Subsingleton (ElemFrobObj natPointMonoid) :=
    inferInstanceAs (Subsingleton (Discrete PUnit.{1}))
  exact ⟨constNat_isDivisorialMonoidOn, isConnected_of_nonempty_and_subsingleton,
    inferInstance, fun _ _ f => natPoint_epi f,
    fun _ _ _ => ⟨fun g h _ => Subsingleton.elim g h⟩⟩

/-- Every object of the example is Frobenius-trivial, via `ζ(n) = (0, n)`. -/
theorem natPoint_isFrobeniusTrivialObj :
    letI := elemFrobCategory natPointMonoid
    ∀ X : ElemFrobObj natPointMonoid, IsFrobeniusTrivialObj natPointFrobFunctor X := by
  let := elemFrobCategory natPointMonoid
  intro X
  have hmul : ∀ m n : ℕ+, (show X ⟶ X from natPointHom X X 0 (m * n)) =
      natPointHom X X 0 n ≫ natPointHom X X 0 m := by
    intro m n
    refine (natPoint_eq_iff _ _).2 ⟨?_, ?_⟩
    · rw [natPointDiv_comp, natPointDiv_hom, natPointDiv_hom, natPointDiv_hom]
      simp
    · rw [natPointDeg_comp, natPointDeg_hom, natPointDeg_hom, natPointDeg_hom]
      exact PNat.mul_coe _ _
  let ζ : ℕ+ →* End X :=
    { toFun := fun n => End.of (natPointHom X X 0 n)
      map_one' := End.ext ((natPoint_eq_iff _ _).2 ⟨rfl, rfl⟩)
      map_mul' := fun m n => End.ext (hmul m n) }
  exact ⟨ζ, fun n => rfl, fun n => ⟨Subsingleton.elim _ _,
    (natPoint_isFrobeniusTypeMor (ζ n).asHom).2 rfl⟩⟩

/-- Definition 1.3 (i) (a) holds for the example. -/
theorem natPoint_frobCondIA :
    @FrobCondIA (Discrete PUnit.{1}) _ natPointMonoid (ElemFrobObj natPointMonoid)
      (elemFrobCategory natPointMonoid) natPointFrobFunctor := by
  let := elemFrobCategory natPointMonoid
  intro X
  exact ⟨X, natPoint_isFrobeniusTrivialObj X, ⟨Iso.refl X⟩⟩

/-- Definition 1.3 (i) (b) holds for the example. -/
theorem natPoint_frobCondIB :
    @FrobCondIB (Discrete PUnit.{1}) _ natPointMonoid (ElemFrobObj natPointMonoid)
      (elemFrobCategory natPointMonoid) natPointFrobFunctor := by
  let := elemFrobCategory natPointMonoid
  intro A B _
  exact ⟨A, natPointHom A A 0 1, natPointHom A B 0 1, (natPoint_isPreStep _).2 rfl,
    (natPoint_isPreStep _).2 rfl, Subsingleton.elim _ _⟩

/-- Definition 1.3 (ii) holds for the example, with `φ = (0, n)`. -/
theorem natPoint_frobCondII :
    @FrobCondII (Discrete PUnit.{1}) _ natPointMonoid (ElemFrobObj natPointMonoid)
      (elemFrobCategory natPointMonoid) natPointFrobFunctor := by
  let := elemFrobCategory natPointMonoid
  intro A n
  refine ⟨A, natPointHom A A 0 n, (natPoint_isFrobeniusTypeMor _).2 rfl, rfl, ?_⟩
  intro E ψ hψ hdeg
  have h1 : natPointDiv ψ = 0 := (natPoint_isFrobeniusTypeMor ψ).1 hψ
  have h2 : natPointDeg ψ = n := congrArg PNat.val hdeg
  refine ⟨natPointIso A E, (natPoint_eq_iff _ _).2 ⟨?_, ?_⟩⟩
  · rw [natPointDiv_comp, natPointIso_hom, natPointDiv_hom, natPointDiv_hom, h1]
    simp
  · rw [natPointDeg_comp, natPointIso_hom, natPointDeg_hom, natPointDeg_hom, h2]
    simp

/-- Definition 1.3 (iii) (a) holds for the example (every morphism is co-angular). -/
theorem natPoint_frobCondIIIA :
    @FrobCondIIIA (Discrete PUnit.{1}) _ natPointMonoid (ElemFrobObj natPointMonoid)
      (elemFrobCategory natPointMonoid) natPointFrobFunctor := by
  let := elemFrobCategory natPointMonoid
  intro X Y Z f g _ _
  exact natPoint_isCoAngular _

/-- Definition 1.3 (iii) (b) holds for the example (every morphism is co-angular). -/
theorem natPoint_frobCondIIIB :
    @FrobCondIIIB (Discrete PUnit.{1}) _ natPointMonoid (ElemFrobObj natPointMonoid)
      (elemFrobCategory natPointMonoid) natPointFrobFunctor := by
  let := elemFrobCategory natPointMonoid
  intro A' A f _ _ g
  exact natPoint_isCoAngular g

/-- Definition 1.3 (iii) (c) holds for the example: the induced bijection `O^▷(A) ≅ O^▷(B)`
keeps the zero divisor. -/
theorem natPoint_frobCondIIIC :
    @FrobCondIIIC (Discrete PUnit.{1}) _ natPointMonoid (ElemFrobObj natPointMonoid)
      (elemFrobCategory natPointMonoid) natPointFrobFunctor := by
  let := elemFrobCategory natPointMonoid
  have mem : ∀ {X : ElemFrobObj natPointMonoid} (z : ℕ),
      natPointHom X X z 1 ∈ unitTriangleEndos natPointFrobFunctor X :=
    fun z => ⟨Subsingleton.elim _ _, rfl⟩
  have deg1 : ∀ {X : ElemFrobObj natPointMonoid} (α : unitTriangleEndos natPointFrobFunctor X),
      natPointDeg α.1 = 1 := fun α => congrArg PNat.val α.2.2
  have forced : ∀ {A B : ElemFrobObj natPointMonoid} (φ : A ⟶ B), natPointDeg φ = 1 →
      ∀ (α : unitTriangleEndos natPointFrobFunctor A)
        (β : unitTriangleEndos natPointFrobFunctor B), φ ≫ β.1 = α.1 ≫ φ →
        natPointDiv β.1 = natPointDiv α.1 := by
    intro A B φ hφ α β h
    have e := ((natPoint_eq_iff _ _).1 h).1
    rw [natPointDiv_comp, natPointDiv_comp, deg1 β, hφ] at e
    omega
  intro A B φ _ hφ
  have hφ1 := (natPoint_isPreStep φ).1 hφ
  let e : unitTriangleEndos natPointFrobFunctor A ≃ unitTriangleEndos natPointFrobFunctor B :=
    { toFun := fun α => ⟨natPointHom B B (natPointDiv α.1) 1, mem _⟩
      invFun := fun β => ⟨natPointHom A A (natPointDiv β.1) 1, mem _⟩
      left_inv := fun α => Subtype.ext ((natPoint_eq_iff _ _).2 ⟨rfl, (deg1 α).symm⟩)
      right_inv := fun β => Subtype.ext ((natPoint_eq_iff _ _).2 ⟨rfl, (deg1 β).symm⟩) }
  refine ⟨⟨e, fun α => ?_, fun α α' α'' h => ?_⟩, ?_⟩
  · change φ ≫ natPointHom B B (natPointDiv α.1) 1 = α.1 ≫ φ
    refine (natPoint_eq_iff _ _).2 ⟨?_, ?_⟩
    · rw [natPointDiv_comp, natPointDiv_comp, natPointDiv_hom, natPointDeg_hom, hφ1]
      simp [Nat.add_comm]
    · rw [natPointDeg_comp, natPointDeg_comp, natPointDeg_hom, hφ1, deg1 α]
      simp
  · have hz := ((natPoint_eq_iff _ _).1 h).1
    rw [natPointDiv_comp, deg1 α'] at hz
    change (natPointHom B B (natPointDiv α.1) 1 : B ⟶ B) ≫ natPointHom B B (natPointDiv α'.1) 1 =
      (show B ⟶ B from natPointHom B B (natPointDiv α''.1) 1)
    refine (natPoint_eq_iff _ _).2 ⟨?_, ?_⟩
    · rw [natPointDiv_comp, natPointDiv_hom, natPointDiv_hom, natPointDiv_hom, natPointDeg_hom]
      simp only [PNat.one_coe]
      omega
    · rw [natPointDeg_comp, natPointDeg_hom, natPointDeg_hom, natPointDeg_hom]
      simp
  · intro φ' _ hφ' _ e₁ e₂ h₁ h₂
    have hφ'1 := (natPoint_isPreStep φ').1 hφ'
    refine Equiv.ext fun α => Subtype.ext ((natPoint_eq_iff _ _).2 ⟨?_, by rw [deg1, deg1]⟩)
    rw [forced φ hφ1 α (e₁ α) (h₁.1 α), forced φ' hφ'1 α (e₂ α) (h₂.1 α)]

/-- Definition 1.3 (iv) (a) holds for the example: `(z, n) = (0, 1) ∘ (z, 1) ∘ (0, n)`. -/
theorem natPoint_frobCondIVA :
    @FrobCondIVA (Discrete PUnit.{1}) _ natPointMonoid (ElemFrobObj natPointMonoid)
      (elemFrobCategory natPointMonoid) natPointFrobFunctor := by
  let := elemFrobCategory natPointMonoid
  have comps : ∀ {A B X Y : ElemFrobObj natPointMonoid} (φ : A ⟶ B) (γ : A ⟶ X) (β : X ⟶ Y)
      (α : Y ⟶ B), γ ≫ β ≫ α = φ → IsPullBackMor natPointFrobFunctor α →
      IsPreStep natPointFrobFunctor β → IsFrobeniusTypeMor natPointFrobFunctor γ →
      natPointDiv α = 0 ∧ natPointDeg α = 1 ∧ natPointDiv β = natPointDiv φ ∧
        natPointDeg β = 1 ∧ natPointDiv γ = 0 ∧ natPointDeg γ = natPointDeg φ := by
    intro A B X Y φ γ β α h hα hβ hγ
    obtain ⟨a1, a2⟩ := natPoint_of_isPullBackMor α hα
    have b2 := (natPoint_isPreStep β).1 hβ
    have c1 := (natPoint_isFrobeniusTypeMor γ).1 hγ
    have e := (natPoint_eq_iff _ _).1 h
    simp only [natPointDiv_comp, natPointDeg_comp, a1, a2, b2, c1] at e
    exact ⟨a1, a2, by simpa using e.1, b2, c1, by simpa using e.2⟩
  intro A B φ
  refine ⟨⟨A, A, natPointHom A A 0 φ.2.2, natPointHom A A (natPointDiv φ) 1,
    natPointHom A B 0 1, ?_, natPoint_isPullBackMor _ rfl rfl, (natPoint_isPreStep _).2 rfl,
    (natPoint_isFrobeniusTypeMor _).2 rfl⟩, ?_⟩
  · refine (natPoint_eq_iff _ _).2 ⟨?_, ?_⟩
    · rw [natPointDiv_comp, natPointDiv_comp, natPointDeg_comp, natPointDiv_hom,
        natPointDiv_hom, natPointDiv_hom, natPointDeg_hom, natPointDeg_hom]
      simp
    · rw [natPointDeg_comp, natPointDeg_comp, natPointDeg_hom, natPointDeg_hom, natPointDeg_hom]
      simp [natPointDeg]
  · intro X Y X' Y' γ β α γ' β' α' h hα hβ hγ h' hα' hβ' hγ'
    obtain ⟨a1, a2, b1, b2, c1, c2⟩ := comps φ γ β α h hα hβ hγ
    obtain ⟨a1', a2', b1', b2', c1', c2'⟩ := comps φ γ' β' α' h' hα' hβ' hγ'
    refine ⟨natPointIso Y' Y, natPointIso X' X, ?_, ?_, ?_⟩
    · refine (natPoint_eq_iff _ _).2 ⟨?_, ?_⟩
      · rw [natPointDiv_comp, natPointIso_hom, natPointDiv_hom, a1, a1']
        simp
      · rw [natPointDeg_comp, natPointIso_hom, natPointDeg_hom, a2, a2']
        simp
    · refine (natPoint_eq_iff _ _).2 ⟨?_, ?_⟩
      · rw [natPointDiv_comp, natPointDiv_comp, natPointDeg_comp, natPointIso_hom,
          natPointIso_inv, natPointDiv_hom, natPointDiv_hom, natPointDeg_hom, b1, b1', b2]
        simp
      · rw [natPointDeg_comp, natPointDeg_comp, natPointIso_hom, natPointIso_inv,
          natPointDeg_hom, natPointDeg_hom, b2, b2']
        simp
    · refine (natPoint_eq_iff _ _).2 ⟨?_, ?_⟩
      · rw [natPointDiv_comp, natPointIso_inv, natPointDiv_hom, natPointDeg_hom, c1, c1']
        simp
      · rw [natPointDeg_comp, natPointIso_inv, natPointDeg_hom, c2, c2']
        simp

/-- Definition 1.3 (iv) (b) holds for the example. -/
theorem natPoint_frobCondIVB :
    @FrobCondIVB (Discrete PUnit.{1}) _ natPointMonoid (ElemFrobObj natPointMonoid)
      (elemFrobCategory natPointMonoid) natPointFrobFunctor := by
  let := elemFrobCategory natPointMonoid
  intro A B f hf
  obtain ⟨h1, h2⟩ := natPoint_of_isPullBackMor f hf
  exact ⟨⟨natPoint_isCoAngular f, h1⟩, PNat.coe_injective h2⟩

/-- Definition 1.3 (v) (a) holds for the example (every morphism is a monomorphism). -/
theorem natPoint_frobCondVA :
    @FrobCondVA (Discrete PUnit.{1}) _ natPointMonoid (ElemFrobObj natPointMonoid)
      (elemFrobCategory natPointMonoid) natPointFrobFunctor := by
  let := elemFrobCategory natPointMonoid
  intro A B f _
  exact natPoint_mono f

/-- In the example, factorizations `φ = α ∘ β` of a morphism by two classes of degree `1`
morphisms, one of which consists of isometries, are unique up to isomorphism, provided one
exists. -/
theorem natPoint_twoFactorization :
    letI := elemFrobCategory natPointMonoid
    ∀ {A B : ElemFrobObj natPointMonoid} (φ : A ⟶ B)
      (Sα Sβ : ∀ {X Y : ElemFrobObj natPointMonoid}, (X ⟶ Y) → Prop),
      (∃ (X : ElemFrobObj natPointMonoid) (β : A ⟶ X) (α : X ⟶ B), β ≫ α = φ ∧ Sα α ∧ Sβ β) →
      (∀ {X Y} (f : X ⟶ Y), Sα f → natPointDeg f = 1) →
      (∀ {X Y} (f : X ⟶ Y), Sβ f → natPointDeg f = 1) →
      ((∀ {X Y} (f : X ⟶ Y), Sα f → natPointDiv f = 0) ∨
        (∀ {X Y} (f : X ⟶ Y), Sβ f → natPointDiv f = 0)) →
      HasUniqueTwoFactorization φ Sα Sβ := by
  let := elemFrobCategory natPointMonoid
  intro A B φ Sα Sβ hex hα1 hβ1 hzero
  refine ⟨hex, ?_⟩
  intro X X' β α β' α' h hα hβ h' hα' hβ'
  have e := ((natPoint_eq_iff _ _).1 h).1
  have e' := ((natPoint_eq_iff _ _).1 h').1
  rw [natPointDiv_comp, hα1 α hα] at e
  rw [natPointDiv_comp, hα1 α' hα'] at e'
  have hdiv : natPointDiv α' = natPointDiv α ∧ natPointDiv β' = natPointDiv β := by
    rcases hzero with hz | hz
    · have := hz α hα
      have := hz α' hα'
      omega
    · have := hz β hβ
      have := hz β' hβ'
      omega
  refine ⟨natPointIso X' X, (natPoint_eq_iff _ _).2 ⟨?_, ?_⟩, (natPoint_eq_iff _ _).2 ⟨?_, ?_⟩⟩
  · rw [natPointDiv_comp, natPointIso_hom, natPointDiv_hom, hα1 α hα, hdiv.1]
    simp
  · rw [natPointDeg_comp, natPointIso_hom, natPointDeg_hom, hα1 α hα, hα1 α' hα']
    simp
  · rw [natPointDiv_comp, natPointIso_inv, natPointDiv_hom, natPointDeg_hom, hdiv.2]
    simp
  · rw [natPointDeg_comp, natPointIso_inv, natPointDeg_hom, hβ1 β hβ, hβ1 β' hβ']
    simp

/-- Definition 1.3 (v) (b) holds for the example: `(z, 1) = (0, 1) ∘ (z, 1)`. -/
theorem natPoint_frobCondVB :
    @FrobCondVB (Discrete PUnit.{1}) _ natPointMonoid (ElemFrobObj natPointMonoid)
      (elemFrobCategory natPointMonoid) natPointFrobFunctor := by
  let := elemFrobCategory natPointMonoid
  intro A B φ hφ
  have hφ1 := (natPoint_isPreStep φ).1 hφ
  refine natPoint_twoFactorization φ _ _ ⟨A, natPointHom A A (natPointDiv φ) 1,
    natPointHom A B 0 1, ?_, ⟨rfl, (natPoint_isPreStep _).2 rfl⟩,
    ⟨natPoint_isCoAngular _, (natPoint_isPreStep _).2 rfl⟩⟩
    (fun f hf => (natPoint_isPreStep f).1 hf.2) (fun f hf => (natPoint_isPreStep f).1 hf.2)
    (Or.inl fun f hf => hf.1)
  refine (natPoint_eq_iff _ _).2 ⟨?_, ?_⟩
  · rw [natPointDiv_comp, natPointDiv_hom, natPointDiv_hom, natPointDeg_hom]
    simp
  · rw [natPointDeg_comp, natPointDeg_hom, natPointDeg_hom, hφ1]
    simp

/-- Definition 1.3 (v) (c) holds for the example: `(z, 1) = (z, 1) ∘ (0, 1)`. -/
theorem natPoint_frobCondVC :
    @FrobCondVC (Discrete PUnit.{1}) _ natPointMonoid (ElemFrobObj natPointMonoid)
      (elemFrobCategory natPointMonoid) natPointFrobFunctor := by
  let := elemFrobCategory natPointMonoid
  intro A B φ hφ
  have hφ1 := (natPoint_isPreStep φ).1 hφ
  refine natPoint_twoFactorization φ _ _ ⟨A, natPointHom A A 0 1,
    natPointHom A B (natPointDiv φ) 1, ?_, ⟨natPoint_isCoAngular _, (natPoint_isPreStep _).2 rfl⟩,
    ⟨rfl, (natPoint_isPreStep _).2 rfl⟩⟩
    (fun f hf => (natPoint_isPreStep f).1 hf.2) (fun f hf => (natPoint_isPreStep f).1 hf.2)
    (Or.inr fun f hf => hf.1)
  refine (natPoint_eq_iff _ _).2 ⟨?_, ?_⟩
  · rw [natPointDiv_comp, natPointDiv_hom, natPointDiv_hom, natPointDeg_hom]
    simp
  · rw [natPointDeg_comp, natPointDeg_hom, natPointDeg_hom, hφ1]
    simp

/-- Definition 1.3 (vi) holds for the example: metrically equivalent pre-steps are equal. -/
theorem natPoint_frobCondVI :
    @FrobCondVI (Discrete PUnit.{1}) _ natPointMonoid (ElemFrobObj natPointMonoid)
      (elemFrobCategory natPointMonoid) natPointFrobFunctor := by
  let := elemFrobCategory natPointMonoid
  intro A B φ ψ _ hm _ hφ _ hψ
  refine ⟨𝟙 B, ⟨⟨rfl, rfl⟩, inferInstance⟩, ?_⟩
  rw [Category.comp_id]
  exact (natPoint_eq_iff _ _).2
    ⟨hm, by rw [(natPoint_isPreStep φ).1 hφ, (natPoint_isPreStep ψ).1 hψ]⟩

/-- Definition 1.3 (vii) (a) holds for the example: identities are isotropic hulls. -/
theorem natPoint_frobCondVIIA :
    @FrobCondVIIA (Discrete PUnit.{1}) _ natPointMonoid (ElemFrobObj natPointMonoid)
      (elemFrobCategory natPointMonoid) natPointFrobFunctor := by
  let := elemFrobCategory natPointMonoid
  intro A
  refine ⟨A, 𝟙 A, rfl, (natPoint_isPreStep _).2 rfl, natPoint_isIsotropicObj A,
    fun E γ _ => ⟨γ, Category.id_comp γ, fun β h => ?_⟩⟩
  rw [← h, Category.id_comp]

/-- Definition 1.3 (vii) (b) holds for the example (every object is isotropic). -/
theorem natPoint_frobCondVIIB :
    @FrobCondVIIB (Discrete PUnit.{1}) _ natPointMonoid (ElemFrobObj natPointMonoid)
      (elemFrobCategory natPointMonoid) natPointFrobFunctor := by
  let := elemFrobCategory natPointMonoid
  intro A E _ _
  exact natPoint_isIsotropicObj E

/-- `PartialFrobenioidConditions` holds for the elementary Frobenioid `𝔽_ℕ` over
`Discrete PUnit` with its identity functor, so the stated clauses are jointly satisfiable.
Proposition 1.5 (i) (page 27) asserts that `𝔽_Φ`, with the natural functor `𝔽_Φ → 𝔽_{Φ^char}`,
is a Frobenioid for a pre-divisorial monoid `Φ` on a connected, totally epimorphic category;
here `Φ` is divisorial (sharp), so `Φ^char = Φ` and the natural functor is the identity. -/
theorem natPoint_partialFrobenioidConditions :
    @PartialFrobenioidConditions (Discrete PUnit.{1}) _ natPointMonoid
      (ElemFrobObj natPointMonoid) (elemFrobCategory natPointMonoid) natPointFrobFunctor :=
  ⟨natPoint_isPreFrobenioidStructure, natPoint_frobCondIA, natPoint_frobCondIB,
    natPoint_frobCondII, natPoint_frobCondIIIA, natPoint_frobCondIIIB, natPoint_frobCondIIIC,
    natPoint_frobCondIVA, natPoint_frobCondIVB, natPoint_frobCondVA, natPoint_frobCondVB,
    natPoint_frobCondVC, natPoint_frobCondVI, natPoint_frobCondVIIA, natPoint_frobCondVIIB⟩

end NatPointExample

end IUT.Prerequisites.Frobenioid
