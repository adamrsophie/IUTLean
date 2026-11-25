import Mathlib

/-!
# IUT I, Definition 3.1: the conditions on initial Θ-data that Mathlib can state today

Source: Mochizuki, *Inter-universal Teichmüller Theory I*, Definition 3.1, pages 61 to 63,
with Remarks 3.1.1 to 3.1.7 (pages 63 to 69, text only) for context. Pages 61, 62, 63 were read as
rendered images; every condition transcribed below was checked against those images.

This file is **not** a formalization of Definition 3.1. Initial Θ-data is a tuple
`(F̄/F, X_F, l, C_K, V, V^bad_mod, ε)` subject to conditions (a) to (f). Most of the objects
involved (hyperbolic orbicurves of type `(1, l-tors)±`, `K`-cores, étale fundamental groups of
orbicurves, the field of moduli of `X_F` in the sense of [AbsTopIII], Definition 5.1, (ii),
the `q`-parameters of a Tate curve, cusps arising from the quotient `Q` of [EtTh], Definition
2.1) have no counterpart in Mathlib. This file states, as separate named predicates on an
actual number field `F` and an actual Weierstrass curve `W` over `F`, exactly those clauses
whose every term exists in Mathlib with its intended meaning, and proves a few small facts.

## What is stated here

* `SqrtNegOneMem F`: the clause `√−1 ∈ F` of condition (a).
* `IsAuxiliaryPrime l`: the clause "`l` is a prime number `≥ 5`" of condition (c).
* `TorsionRational W n`: every `n`-torsion point of `E_F` over an algebraic closure is
  `F`-rational. With `n = 6` this is the clause "the `2 · 3`-torsion points of `E_F` are
  rational over `F`" of condition (b).
* `SemistableAtFinitePlaces W`: the clause "`X_F` admits stable reduction over all
  `v ∈ 𝕍(F)^non`" of condition (b), read as described below.
* Relative to a number field `k` with `F` an algebra over `k`, standing in for `F_mod`:
  `BadSetOddNonempty`, `MultiplicativeOverBadSet`, `GaloisOfDegreePrimeTo`,
  `PrimeToBadResidueChars`. These state the clauses of (b) and (c) that mention `F_mod`
  and `𝕍^bad_mod`, for an arbitrary such `k`; the requirement that `k` be the field of moduli
  of `X_F` is **not** stated, because the field of moduli is not defined here.
* `PartialInitialThetaConditions`: the conjunction of the predicates above. It is a partial
  collection, not Definition 3.1; its docstring lists what is missing.

## Interpretation choices, recorded

* `F̄` is taken to be Mathlib's `AlgebraicClosure F`. The rationality of torsion points does
  not depend on the choice of algebraic closure; that independence is not proved here.
* `E_F` is represented by a Weierstrass curve `W` with `W.IsElliptic`. Points of `E_F` over a
  field `L` are `(W⁄L).toAffine.Point` (the point at infinity together with the affine
  nonsingular points), with Mathlib's group law.
* Stable reduction of the once-punctured elliptic curve `X_F` at a finite place is read as:
  a minimal Weierstrass model of `E_F` over the valuation ring of `F` at that place has good
  or multiplicative reduction. This identification of "stable reduction of `X_F`" with
  "semistable reduction of `E_F`" is the standard one but is not argued on the pages read;
  it is a reading of page 61, not a transcription. Mathlib's `WeierstrassCurve.minimal`
  is a chosen minimal model; the reduction type does not depend on the choice, but that is
  not proved here.
* "Bad (i.e., multiplicative) reduction" at the places over `𝕍^bad_mod` is page 61's own
  gloss and is stated with `HasMultiplicativeReduction`.
* "Odd residue characteristic" at a prime `w` of `𝓞 k` is stated as `(2 : 𝓞 k) ∉ w`, and
  "`l` prime to the residue characteristic of `w`" as `(l : 𝓞 k) ∉ w`.
* A place of `F` lies over a place `w` of `k` when the prime ideals satisfy
  `v ∩ 𝓞 k = w`.

## Not statable today (see `docs/INITIAL_THETA_DATA.md`)

The field of moduli `F_mod` of `X_F`; the image of `G_F → GL₂(𝔽_l)` containing `SL₂(𝔽_l)`
and the field `K` it cuts out (Mathlib has the group law on `E(F̄)` and the Galois action can
be written with `WeierstrassCurve.Affine.Point.map`, but the structure theorem
`E[l](F̄) ≅ (ℤ/lℤ)²` that gives the representation its meaning is not in Mathlib); the orders
of the `q`-parameters at the places of `𝕍(F)^bad`; the orbicurves `C_F`, `C_K`, `X_K` and
their types; `K`-cores; the étale and tempered fundamental groups `Π`, `Δ`; the section
`V ⊆ 𝕍(K)` (statable once `K` is constructed, omitted here); the cusp `ε` and the condition
at `v ∈ V^bad` that `C_v` be of type `(1, ℤ/lℤ)±`.

No claim of the form `l ≠ 5` is made: it would need the mod `l` Galois representation.
-/

open NumberField IsDedekindDomain WeierstrassCurve

namespace IUT.PaperI

/-! ### Condition (a) -/

/-- Definition 3.1 (a), first clause, page 61: the number field `F` contains a square root
of `−1`. -/
def SqrtNegOneMem (F : Type*) [Field F] : Prop :=
  ∃ x : F, x ^ 2 = -1

/-- The clause of condition (a) is not automatic: it fails for `ℚ`. -/
theorem not_sqrtNegOneMem_rat : ¬ SqrtNegOneMem ℚ := by
  rintro ⟨x, hx⟩
  nlinarith [sq_nonneg x]

/-! ### Condition (c), first clause -/

/-- Definition 3.1 (c), first clause, page 62: `l` is a prime number with `l ≥ 5`. -/
def IsAuxiliaryPrime (l : ℕ) : Prop :=
  l.Prime ∧ 5 ≤ l

/-- The clause of condition (c) is satisfiable: `5` is a prime `≥ 5`. -/
theorem isAuxiliaryPrime_five : IsAuxiliaryPrime 5 :=
  ⟨by norm_num, le_rfl⟩

/-- A prime `l ≥ 5` is prime to `6`, as the hypotheses of §1 (page 37) require of `l`. -/
theorem IsAuxiliaryPrime.coprime_six {l : ℕ} (h : IsAuxiliaryPrime l) : Nat.Coprime l 6 := by
  have h5 := h.2
  have h2 : Nat.Coprime l 2 := (Nat.coprime_primes h.1 Nat.prime_two).mpr (by omega)
  have h3 : Nat.Coprime l 3 := (Nat.coprime_primes h.1 Nat.prime_three).mpr (by omega)
  exact Nat.Coprime.mul_right h2 h3

/-! ### Condition (b): torsion and reduction of `E_F` -/

section Curve

variable {F : Type*} [Field F] [NumberField F] (W : WeierstrassCurve F) [W.IsElliptic]

open scoped Classical in
/-- Every `n`-torsion point of `E_F` over `F̄` (here `AlgebraicClosure F`) is `F`-rational,
that is, lies in the image of the base change map `E(F) → E(F̄)`. With `n = 6` this is the
clause of Definition 3.1 (b), page 62: "the `2 · 3`-torsion points of `E_F` are rational over
`F`". -/
def TorsionRational (n : ℕ) : Prop :=
  ∀ P : (W⁄(AlgebraicClosure F)).toAffine.Point, n • P = 0 →
    P ∈ (Affine.Point.baseChange (W' := W) F (AlgebraicClosure F)).range

omit [NumberField F] [W.IsElliptic] in
open scoped Classical in
variable {W} in
/-- Rationality of the `n`-torsion implies rationality of the `m`-torsion for `m ∣ n`. -/
theorem TorsionRational.of_dvd {m n : ℕ} (hmn : m ∣ n) (h : TorsionRational W n) :
    TorsionRational W m := by
  intro P hP
  apply h
  obtain ⟨k, rfl⟩ := hmn
  rw [mul_nsmul, hP, nsmul_zero]

omit [NumberField F] [W.IsElliptic] in
variable {W} in
/-- The `2`-torsion part, used on page 63 (Definition 3.1 (e)) and page 71 (Example 3.2 (iv)):
rationality of the `6`-torsion gives rationality of the `2`-torsion. -/
theorem TorsionRational.two_of_six (h : TorsionRational W 6) : TorsionRational W 2 :=
  h.of_dvd (by norm_num)

/-- Definition 3.1 (b), page 61: `X_F` admits stable reduction at every nonarchimedean
valuation of `F`, read as: at every nonzero prime `v` of `𝓞 F`, a minimal model of `E_F` over
the valuation ring of `v` has good or multiplicative reduction. See the module docstring for
this interpretation. -/
def SemistableAtFinitePlaces : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F),
    (W.minimal (v.valuation F).valuationSubring).HasGoodReduction
        (v.valuation F).valuationSubring ∨
      (W.minimal (v.valuation F).valuationSubring).HasMultiplicativeReduction
        (v.valuation F).valuationSubring

end Curve

/-! ### Clauses of (b) and (c) that mention `F_mod`, stated relative to a given field `k` -/

section RelativeToFmod

variable {k : Type*} [Field k] [NumberField k] {F : Type*} [Field F] [NumberField F]
  [Algebra k F]

/-- Definition 3.1 (b), page 61, relative to a number field `k` standing in for `F_mod`:
`S` (standing in for `𝕍^bad_mod`) is a nonempty set of nonarchimedean valuations of `k` of odd
residue characteristic. -/
def BadSetOddNonempty (S : Set (HeightOneSpectrum (𝓞 k))) : Prop :=
  S.Nonempty ∧ ∀ w ∈ S, (2 : 𝓞 k) ∉ w.asIdeal

/-- Definition 3.1 (b), page 61, relative to `k`: `E_F` has bad, that is multiplicative,
reduction at every nonarchimedean valuation of `F` lying over an element of `S`. -/
def MultiplicativeOverBadSet (W : WeierstrassCurve F) (S : Set (HeightOneSpectrum (𝓞 k))) :
    Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), ∀ w ∈ S,
    v.asIdeal.comap (algebraMap (𝓞 k) (𝓞 F)) = w.asIdeal →
      (W.minimal (v.valuation F).valuationSubring).HasMultiplicativeReduction
        (v.valuation F).valuationSubring

variable (k F) in
/-- Definition 3.1 (b), pages 61 and 62, relative to `k`: the extension `F/k` is Galois of
degree prime to `l`. -/
def GaloisOfDegreePrimeTo (l : ℕ) : Prop :=
  IsGalois k F ∧ Nat.Coprime (Module.finrank k F) l

/-- Definition 3.1 (c), page 62, relative to `k`: `l` is prime to the residue characteristics
of the elements of `S`. -/
def PrimeToBadResidueChars (l : ℕ) (S : Set (HeightOneSpectrum (𝓞 k))) : Prop :=
  ∀ w ∈ S, (l : 𝓞 k) ∉ w.asIdeal

/-- A **partial** collection of the conditions of Definition 3.1 (pages 61 to 63): the
clauses that are statable with Mathlib today, for a number field `F`, an elliptic curve `W`
standing for `E_F`, a natural number `l`, a number field `k` with `F` a `k`-algebra standing
in for `F_mod`, and a set `S` standing in for `𝕍^bad_mod`.

This is not initial Θ-data. Missing, relative to Definition 3.1:
* (a) nothing beyond the choice `F̄ = AlgebraicClosure F`;
* (b) that `X_F` is the once-punctured curve `E_F \ {0}` (implicit in using `W`), the
  orbicurve `C_F`, the requirement that `k` be the field of moduli `F_mod` of `X_F`, the field
  `F_sol`, and the fundamental groups `Π_{X_F} ⊆ Π_{C_F}`, `Δ_X ⊆ Δ_C`;
* (c) that the image of `G_F → GL₂(𝔽_l)` contain `SL₂(𝔽_l)`, the field `K`, and that `l` be
  prime to the orders of the `q`-parameters of `E_F` at the places of `𝕍(F)^bad`;
* (d) the orbicurve `C_K` of type `(1, l-tors)±` with `K`-core `C_F ×_F K`, and `X_K`;
* (e) the section `V ⊆ 𝕍(K)` of `𝕍(K) → 𝕍_mod` and the type `(1, ℤ/lℤ)±` condition at
  `v ∈ V^bad`;
* (f) the cusp `ε` and its normalization at `v ∈ V^bad`. -/
structure PartialInitialThetaConditions (W : WeierstrassCurve F) [W.IsElliptic] (l : ℕ)
    (S : Set (HeightOneSpectrum (𝓞 k))) : Prop where
  /-- (a): `√−1 ∈ F`. -/
  sqrtNegOne : SqrtNegOneMem F
  /-- (b): the `2 · 3`-torsion points of `E_F` are rational over `F`. -/
  torsionSix : TorsionRational W 6
  /-- (b): stable reduction at all nonarchimedean places, read as semistable reduction. -/
  semistable : SemistableAtFinitePlaces W
  /-- (b): `S` is nonempty and of odd residue characteristic. -/
  badSet : BadSetOddNonempty S
  /-- (b): multiplicative reduction at the places of `F` over `S`. -/
  multiplicative : MultiplicativeOverBadSet W S
  /-- (b): `F/k` is Galois of degree prime to `l`. -/
  galois : GaloisOfDegreePrimeTo k F l
  /-- (c): `l` is a prime `≥ 5`. -/
  prime : IsAuxiliaryPrime l
  /-- (c): `l` is prime to the residue characteristics of the elements of `S`. -/
  primeToBad : PrimeToBadResidueChars l S

end RelativeToFmod

end IUT.PaperI
