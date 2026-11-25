# Initial Θ-data (IUT I, Definition 3.1)

Source: Mochizuki, *Inter-universal Teichmüller Theory I*, Definition 3.1, pages 61 to 63
(read as rendered images), Remarks 3.1.1 to 3.1.7, pages 63 to 69 (text). Existence:
*Inter-universal Teichmüller Theory IV*, Corollary 2.2, pages 41 and 42 (rendered images),
proof pages 43 to 46 (text, skimmed).

Lean: `IUT/PaperI/InitialThetaData.lean`, namespace `IUT.PaperI`. Curated records:
`data/curated/iut1.json`, ids `IUT1.Def3_1` and `IUT1.Def3_1.a` to `IUT1.Def3_1.f`.

## The tuple

Initial Θ-data is a tuple `(F̄/F, X_F, l, C_K, V, V^bad_mod, ε)`. Several further objects are
derived from it inside the definition: `G_F`, `E_F`, `C_F`, `F_mod`, `F_sol`, `V_mod`,
`V^good_mod`, `K`, `X_K`, `V^bad`, `V^good`, `Π_v`, and the arrow-decorated curves. The
definition is stated condition by condition below. "Mathlib" means Lean 4 Mathlib at tag
v4.36.0; paths are relative to `Mathlib/`.

## Condition by condition

### (a) page 61

Content: `F` a number field containing `√−1`; `F̄` an algebraic closure; `G_F = Gal(F̄/F)`.

| Object | Mathlib | Path |
|---|---|---|
| number field | `NumberField` | `NumberTheory/NumberField/Basic.lean` |
| algebraic closure | `AlgebraicClosure` | `FieldTheory/IsAlgClosed/AlgebraicClosure.lean` |
| absolute Galois group | `Field.absoluteGaloisGroup` | `FieldTheory/AbsoluteGaloisGroup.lean` |

Lean: `SqrtNegOneMem F := ∃ x : F, x ^ 2 = -1`. Fully statable. Shown not automatic:
`not_sqrtNegOneMem_rat`.

### (b) pages 61 and 62

Content, split into clauses:

1. `X_F` is a once-punctured elliptic curve over `F` with stable reduction at every
   `v ∈ 𝕍(F)^non`; `E_F` is the elliptic curve it determines.
2. `C_F` is the stack quotient of `X_F` by the natural action of `±1`; `F_mod` is the field
   of moduli of `X_F` ([AbsTopIII] Definition 5.1 (ii)); `F_sol` is the maximal solvable
   extension of `F_mod` in `F̄`; `V_mod = 𝕍(F_mod)`.
3. `V^bad_mod ⊆ V^non_mod` is a nonempty set of valuations of odd residue characteristic
   such that `X_F` has bad (that is, multiplicative) reduction at the places over
   `V^bad_mod`; `V^good_mod` is the complement.
4. Fundamental groups `Π_{X_F} ⊆ Π_{C_F}` and geometric parts `Δ_X ⊆ Δ_C`.
5. `F/F_mod` is Galois of degree prime to `l`, and the `2 · 3`-torsion points of `E_F` are
   defined over `F`.

| Object | Mathlib | Path |
|---|---|---|
| elliptic curve | `WeierstrassCurve`, `WeierstrassCurve.IsElliptic` | `AlgebraicGeometry/EllipticCurve/Weierstrass.lean` |
| points and group law | `WeierstrassCurve.Affine.Point` (`AddCommGroup`) | `AlgebraicGeometry/EllipticCurve/Affine/Point.lean` |
| base change of points | `WeierstrassCurve.Affine.Point.baseChange` | same directory |
| minimal model, reduction types | `WeierstrassCurve.minimal`, `HasGoodReduction`, `HasMultiplicativeReduction` | `AlgebraicGeometry/EllipticCurve/Reduction.lean` |
| finite places | `IsDedekindDomain.HeightOneSpectrum (𝓞 F)` | `RingTheory/DedekindDomain/Ideal/Lemmas.lean` and related |
| valuation ring at a place (a DVR) | `(v.valuation F).valuationSubring` | `IsDiscreteValuationRing` found by instance search in a check file; the instance stated in `NumberTheory/NumberField/Completion/FinitePlace.lean` is for `(v.valuation F).integer` |
| Galois extension, degree | `IsGalois`, `Module.finrank` | `FieldTheory/Galois/Basic.lean` |
| once-punctured curve as a hyperbolic curve | absent | |
| stack quotient `C_F` | absent (no algebraic stacks) | |
| field of moduli | absent | |
| étale fundamental group of a curve | absent (Galois categories exist in `CategoryTheory/Galois/`, with no instance for finite étale covers of schemes) | |

Lean:

* clause 5, torsion: `TorsionRational W 6`, with `TorsionRational.of_dvd` and
  `TorsionRational.two_of_six`;
* clause 1, reduction: `SemistableAtFinitePlaces W`, read as good or multiplicative reduction
  of `W.minimal` at every finite place (interpretation recorded in the module docstring);
* clause 3: `BadSetOddNonempty S` and `MultiplicativeOverBadSet W S`, relative to a number
  field `k` with `[Algebra k F]` standing in for `F_mod`;
* clause 5, Galois: `GaloisOfDegreePrimeTo k F l`.

What a full Lean statement would need: the field of moduli (so that `k` is pinned to
`F_mod`), algebraic stacks or orbicurves for `C_F`, and étale fundamental groups. Without the
field of moduli the clauses that mention `F_mod` are weaker than the paper's: they hold for
an unspecified `k`.

### (c) page 62

Content: `l ≥ 5` is prime; the image of the outer action `G_F → GL_2(F_l)` on the `l`-torsion
of `E_F` contains `SL_2(F_l)`; `K` is the finite Galois extension of `F` cut out by the kernel;
`l` is prime to the residue characteristics of the elements of `V^bad_mod` and to the orders
of the `q`-parameters of `E_F` at the elements of `𝕍(F)^bad` ([GenEll] Definition 3.3).

| Object | Mathlib | Path |
|---|---|---|
| primes | `Nat.Prime` | `Data/Nat/Prime/Defs.lean` |
| `SL_2(F_l)`, `GL_2` | `Matrix.SpecialLinearGroup`, `Matrix.GeneralLinearGroup` | `LinearAlgebra/Matrix/SpecialLinearGroup.lean`, `LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean` |
| Galois action on points | `WeierstrassCurve.Affine.Point.map` | `AlgebraicGeometry/EllipticCurve/Affine/Point.lean` |
| `E[l](F̄) ≅ (Z/lZ)^2` | absent | |
| Tate curve, `q`-parameter | absent | |

Lean: `IsAuxiliaryPrime l := l.Prime ∧ 5 ≤ l`, with `coprime_six`; `PrimeToBadResidueChars`.
Not stated: the `SL_2` condition (needs the structure of `E[l]` to fix a basis and give the
representation its meaning), `K`, and the `q`-parameter condition. Expressing the order of
the `q`-parameter through the valuation of the minimal discriminant or of `j` would be an
interpretation and was not made.

### (d) page 62

Content: `C_K` is a hyperbolic orbicurve of type `(1, l-tors)_±` ([EtTh] Definition 2.1)
over `K` whose `K`-core ([CanLift] Remark 2.1.1) is `C_F ×_F K`; this determines `X_K` and
cartesian diagrams, and inclusions of geometric fundamental groups ([EtTh] Proposition 2.2,
Definition 2.3).

Mathlib: nothing beyond schemes. Not statable.

### (e) pages 62 and 63

Content: `V ⊆ 𝕍(K)` is a section of the natural surjection `𝕍(K) → V_mod`; `V^bad`, `V^good`
are its parts over `V^bad_mod`, `V^good_mod`. For `v ∈ V^bad` the base change of `C_K` to
`K_v` is of type `(1, Z/lZ)_±` ([EtTh] Definition 2.5 (i)), with associated curves `X_v`, `C_v`
(double underline) and `Π_v` the tempered fundamental group.

Mathlib: places of `K` exist (`HeightOneSpectrum`, `NumberField.InfinitePlace`), so the
section is statable once `K` is constructed; `K` is not constructed here. Types
`(1, Z/lZ)_±` and tempered groups are absent.

### (f) page 63

Content: `ε` is a cusp of `C_K` arising from a nonzero element of the quotient `Q` of
[EtTh] Definition 2.1; at `v ∈ V^bad` the induced cusp arises from the generator `±1` of `Ẑ`
in the Tate uniformization. `ε` determines the arrow-decorated curves and the groups `Π_v`
at good `v`.

Mathlib: absent. Not statable.

## Summary of what is in Lean

`PartialInitialThetaConditions W l S` (relative to `k`) bundles: (a); the torsion, reduction,
bad-set, multiplicative and Galois clauses of (b); the prime and residue characteristic
clauses of (c). Its docstring lists every missing clause. It is not initial Θ-data.

Statements of the paper that would sharpen the Lean: none was formalized. In particular the
claim `l ≠ 5` or any lower bound on `l` beyond `5` is not stated; it is not part of
Definition 3.1.

## Existence: IUT IV, Corollary 2.2

Pages 41 and 42 (rendered). Setting: `X = P^1_Q`, the λ-line, with divisor `D = {0, 1, ∞}`; a compactly
bounded subset `K_V` whose support contains the prime `2` and satisfies the condition
`(∗_{j-inv})`. Assertion (ii) gives constants `H_unif`, `C_K`, `H_K`, sets
`δ = 2^12 · 3^3 · 5 · d`, a finite exceptional set `Exc_d`, and for an elliptic curve `E` over
a number field with `x_E ∈ K_V \ Exc_d` it sets `F_tpd = F_mod(E[2])` and
`F = F_mod(√−1, E_{F_mod}[2 · 3 · 5])`. The conclusion is that `E_F` and `F_mod` arise from
initial Θ-data as in IUT IV Theorem 1.10, satisfying conditions (C1) and (C2) there.

Proof outline as read on pages 43 to 46: a prime `l` is chosen with the prime number theorem
(IUT IV Proposition 2.1) satisfying conditions (P1) to (P5); (P6), the `SL_2` image, follows
from (P2), (P4), (P5) and [GenEll] Lemma 3.1 (iii); (P7) states that conditions (a) to (f)
follow formally; the existence of `V` and `ε` uses (P6).

Points a reader of the proof should check:

* the condition that `[F : F_mod]` be prime to `l` (Definition 3.1 (b)) was not found argued
  separately on the pages read; it is covered only by the general statement (P7);
* the `F`-rationality of the `2 · 3`-torsion follows from `F ⊇ F_mod(E[2 · 3 · 5])` as soon
  as `E_F` is the base change of a model of `E` over `F_mod` (an inference, not a quotation);
* which of (P1) to (P5) give the residue characteristic and `q`-parameter conditions of (c)
  was not traced in detail.

### What a formal nonvacuity proof would require

1. Definitions of every object in (a) to (f): field of moduli, orbicurves and stacks,
   `K`-cores, étale and tempered fundamental groups, the Tate uniformization and
   `q`-parameters, cusps and the quotient `Q` of [EtTh].
2. The structure theorem `E[n](F̄) ≅ (Z/nZ)^2` and the mod `l` Galois representation.
3. An open image result giving `SL_2(F_l) ⊆` image for some prime `l` in the required range,
   which is the role of [GenEll] Lemma 3.1 (iii) and IUT IV Proposition 2.1.
4. The prime number theorem in the form used by IUT IV Proposition 2.1. Mathlib contains a
   weak form (`NumberTheory/LSeries/WeakPNT.lean`); whether it suffices was not checked.
5. The existence of an elliptic curve with the required bad reduction, for example from the
   λ-line setting of IUT IV.

A weaker, Lean-checkable target is nonvacuity of `PartialInitialThetaConditions` on a
concrete curve over a concrete field, for example `Q(i)` and a curve with full rational
`6`-torsion. That needs explicit computation of minimal models and reduction types, and was
not attempted.
