# Mathlib gap analysis for the IUT prerequisites

This document lists, for every prerequisite area that the four papers draw on, what the installed Mathlib (tag v4.36.0, Lean 4.36.0) provides, what is missing, and how each part is classified. The same content is in `data/prerequisites.json`.

Method. Every Mathlib declaration named below was checked by `#check` against the installed library, and the file given is the module in which Lean reports it is declared. File paths are relative to `.lake/packages/mathlib/Mathlib/`. Absence claims come from text searches of the Mathlib sources and are stated with the search used; a failed search is not a proof of absence. Material in other Lean libraries is reported from their README files or file names only; it was not built.

Classes: (1) exists in Mathlib; (2) derivable from Mathlib; (3) needs substantial new formalization; (4) exists in another verifiable Lean library; (5) needs additional literature; (6) unresolved or disputed claim.

"Needed first by" uses statement ids of `data/statements.json`. The mechanical index is not a reading of the papers.

## Most cited outside references

| Key | Citations | By paper | First citing statements (mechanical) |
|:--|:--|:--|:--|
| [AbsTopIII] | 406 | IUT1: 198, IUT2: 91, IUT3: 99, IUT4: 18 | IUT1.Cor1_2, IUT2.Prop1_2, IUT3.Def1_1, IUT4.Prop1_4 |
| [EtTh] | 380 | IUT1: 151, IUT2: 167, IUT3: 48, IUT4: 14 | IUT1.Cor1_2, IUT2.Def1_1, IUT3.Rem2_1_1, IUT4.Rem1_10_6 |
| [FrdI] | 144 | IUT1: 97, IUT2: 20, IUT3: 22, IUT4: 5 | IUT1.Rem3_1_5, IUT2.Prop1_2, IUT3.Rem2_1_1, IUT4.Rem2_3_3 |
| [SemiAnbd] | 100 | IUT1: 88, IUT2: 9, IUT3: 1, IUT4: 2 | IUT1.ThmB, IUT2.Rem1_4_1, IUT3.Rem2_1_2, IUT4.Rem2_3_3 |
| [GenEll] | 69 | IUT1: 5, IUT4: 64 | IUT1.Def3_1, IUT4.ThmA |
| [FrdII] | 58 | IUT1: 40, IUT2: 13, IUT3: 5 | IUT1.Rem2_5_3, IUT2.Prop1_2, IUT3.Rem2_4_2 |
| [HASurI] | 36 | IUT1: 10, IUT2: 14, IUT4: 12 | IUT1.Rem4_3_1, IUT2.Rem1_12_5, IUT4.Rem1_10_1 |
| [AbsTopI] | 34 | IUT1: 28, IUT2: 4, IUT4: 2 | IUT1.Cor1_2, IUT2.Rem1_6_1, IUT4.Rem2_3_5 |
| [pOrd] | 32 | IUT1: 14, IUT2: 1, IUT3: 4, IUT4: 13 | IUT1.Rem4_3_3, IUT2.Rem3_6_5, IUT3.Rem3_12_3, IUT4.Rem1_10_2 |
| [AbsTopII] | 27 | IUT1: 17, IUT2: 7, IUT4: 3 | IUT1.Cor1_2, IUT2.Rem1_5_2, IUT4.Rem2_3_5 |
| [pTeich] | 27 | IUT1: 14, IUT2: 4, IUT3: 3, IUT4: 6 | IUT1.Rem4_3_3, IUT2.Rem1_11_6, IUT3.Rem3_12_3, IUT4.Rem1_10_2 |
| [AbsAnab] | 25 | IUT1: 13, IUT2: 11, IUT3: 1 | IUT1.Rem1_2_2, IUT2.Prop1_6, IUT3.Cor3_12 |

## Summary table

| Area | Classes |
|:--|:--|
| Algebraic number fields and their completions | 1, 2 |
| Local and global class field theory | 3, 4 |
| Algebraic closures and Galois theory (finite and infinite) | 1 |
| Profinite groups and continuous cohomology | 1, 3 |
| Etale fundamental groups | 3, 4 |
| Tempered fundamental groups | 3, 4, 5 |
| Algebraic and arithmetic geometry: schemes, stacks, orbicurves | 1, 3, 4 |
| Hyperbolic curves | 3, 4 |
| Grothendieck's anabelian geometry, absolute and mono-anabelian reconstruction, category-theoretic reconstruction | 3, 5 |
| Frobenioids | 3, 5 |
| Kummer theory | 2, 3, 4 |
| Tate curves and Tate uniformization | 3, 4 |
| Elliptic curves with level structures | 1, 3, 4 |
| Etale theta functions | 3, 5 |
| Hodge-Arakelov theory | 5 |
| Valuations and normalized absolute values | 1, 2 |
| Nonarchimedean analysis | 1, 3 |
| p-adic logarithms and exponentials | 2, 3, 4 |
| Arithmetic divisors | 2 |
| Arakelov degrees | 2, 3 |
| Heights and discriminants | 1, 2, 3, 4, 5 |
| Ramification theory and the different | 1, 2, 3, 4 |
| Haar measures and log-volumes | 1, 2, 3 |
| Tensor products of local fields | 2, 3 |
| Diophantine geometry | 3, 4, 5 |
| Szpiro-type and Vojta-type inequalities | 6 |
| Set-theoretic foundations and universe management | 1, 2, 3, 5 |

## Areas

### Algebraic number fields and their completions

Classes: (1) EXISTS_IN_MATHLIB, (2) DERIVABLE_FROM_MATHLIB.

In Mathlib:

* `NumberTheory/NumberField/Basic.lean`: `NumberField`, `NumberField.RingOfIntegers`
* `NumberTheory/NumberField/InfinitePlace/Basic.lean`: `NumberField.InfinitePlace`, `NumberField.InfinitePlace.mult`
* `NumberTheory/NumberField/Completion/InfinitePlace.lean`: `NumberField.InfinitePlace.Completion`
* `NumberTheory/NumberField/Completion/FinitePlace.lean`: `NumberField.FinitePlace`, `NumberField.FinitePlace.mk`, `NumberField.FinitePlace.equivHeightOneSpectrum`
* `RingTheory/DedekindDomain/AdicValuation/Completion.lean`: `IsDedekindDomain.HeightOneSpectrum.adicCompletion`, `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers`
* `RingTheory/DedekindDomain/FiniteAdeleRing.lean`: `IsDedekindDomain.FiniteAdeleRing`, `IsDedekindDomain.FiniteAdeleRing.isUnit_iff`
* `NumberTheory/NumberField/AdeleRing.lean`: `NumberField.AdeleRing`
* `NumberTheory/NumberField/InfiniteAdeleRing.lean`: `NumberField.InfiniteAdeleRing`
* `NumberTheory/Padics/PadicNumbers.lean`: `Padic`
* `NumberTheory/Padics/PadicIntegers.lean`: `PadicInt`
* `NumberTheory/Padics/Complex.lean`: `PadicComplex`
* `NumberTheory/LocalField/Basic.lean`: `IsNonarchimedeanLocalField`
* `NumberTheory/NumberField/Discriminant/Defs.lean`: `NumberField.discr`
* `NumberTheory/NumberField/Units/DirichletTheorem.lean`: `NumberField.Units.rank`, `NumberField.Units.fundSystem`

In this project:

* `IUT/PaperIV/ArithmeticDivisor.lean`: `IUT.PaperIV.Valuations`
* `IUT/Prerequisites/PositiveRationalsZhatUnits.lean`: `IUT.Prerequisites.Zhat`, `IUT.Prerequisites.Zhat.toFiniteAdeles`

Missing:

* A uniform interface identifying the completion of a number field at a finite place with a finite extension of Q_p as an instance of IsNonarchimedeanLocalField (not searched exhaustively). Classes 2.
* The ring Zhat as a named object; modeled in this project as the product of the adicCompletionIntegers over the primes of Z. Classes 2.

Needed first by: IUT1.Def3_1, IUT4.Def1_9.

Read: IUT I Definition 3.1 (a), pages 61 and 62 (a number field containing a square root of -1, an algebraic closure, valuation sets); IUT IV Definition 1.9, pages 21 and 22.

### Local and global class field theory

Classes: (3) NEEDS_SUBSTANTIAL_FORMALIZATION, (4) EXISTS_IN_OTHER_LEAN_LIBRARY.

In Mathlib:

* `NumberTheory/LegendreSymbol/QuadraticReciprocity.lean`: quadratic reciprocity only
* `RepresentationTheory/Homological/TateCohomology/Basic.lean`: Tate cohomology of finite groups, an ingredient of cohomological class field theory

Missing:

* Local reciprocity map and existence theorem for p-adic fields. Classes 3, 4.
* Global class field theory (idelic Artin map, reciprocity, existence). Classes 3.

Other Lean libraries:

* `lana-agents/local-class-field-theory (dependency pinned by lana-agents/iut)`: local reciprocity, the Artin map for p-adic fields and the existence theorem, per its README. Lean 4.32, not built here, cannot be imported.

Bibliography keys: [NSW].

A plain text search of the Mathlib sources for "ClassField", "reciprocity" and "Artin" found no class field theory; the two "ClassField" hits are references, in module docstrings of TateCohomology/Basic.lean and RingTheory/Valuation/Discrete/Basic.lean, to external class field theory projects. Which IUT statements need class field theory was not determined from the pages read; the mechanical index shows [NSW] only in remarks and one example.

### Algebraic closures and Galois theory (finite and infinite)

Classes: (1) EXISTS_IN_MATHLIB.

In Mathlib:

* `FieldTheory/Galois/Basic.lean`: `IsGalois`, `IsGalois.intermediateFieldEquivSubgroup`
* `FieldTheory/IsAlgClosed/AlgebraicClosure.lean`: `AlgebraicClosure`
* `FieldTheory/IsAlgClosed/Basic.lean`: `IsAlgClosure`
* `FieldTheory/AbsoluteGaloisGroup.lean`: `Field.absoluteGaloisGroup`, `Field.absoluteGaloisGroupAbelianization`
* `FieldTheory/KrullTopology.lean`: `krullTopology`
* `FieldTheory/Galois/Infinite.lean`: `InfiniteGalois.IntermediateFieldEquivClosedSubgroup`
* `NumberTheory/Cyclotomic/Basic.lean`: `IsCyclotomicExtension`
* `RingTheory/RootsOfUnity/Basic.lean`: `rootsOfUnity`
* `RingTheory/RootsOfUnity/PrimitiveRoots.lean`: `IsPrimitiveRoot`

Missing:

* Decomposition and inertia subgroups of absolute Galois groups of number fields at places, in the form used for prime-strips (not searched exhaustively). Classes 2, 3.

Needed first by: IUT1.Def3_1.

Infinite Galois theory with the Krull topology and the fundamental theorem for closed subgroups exists. IUT I Definition 3.1 (a), (c), pages 61 and 62 (read), uses the absolute Galois group of a number field and the image of its action on l-torsion points in GL_2(F_l).

### Profinite groups and continuous cohomology

Classes: (1) EXISTS_IN_MATHLIB, (3) NEEDS_SUBSTANTIAL_FORMALIZATION.

In Mathlib:

* `Topology/Algebra/Category/ProfiniteGrp/Basic.lean`: `ProfiniteGrp`
* `Topology/Algebra/Category/ProfiniteGrp/Completion.lean`: `ProfiniteGrp.ProfiniteCompletion.completion`
* `RepresentationTheory/Homological/ContCohomology/Basic.lean`: `continuousCohomology`
* `RepresentationTheory/Homological/GroupCohomology/Basic.lean`: `groupCohomology`
* `RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean`: `groupCohomology.H1ofAutOnUnitsUnique`

Missing:

* Cyclotomes Hom(Q/Z, M) and cyclotomic rigidity isomorphisms, as in IUT I, Example 5.1 (v), page 127 (read). Classes 3.

Bibliography keys: [AbsTopIII].

Needed first by: IUT1.Def3_1, IUT1.Ex5_1.

IUT I Definition 3.1 (b), page 61 (read), uses profinite etale fundamental groups and the exact sequences of profinite groups 1 to Delta to Pi to G_F to 1.

### Etale fundamental groups

Classes: (3) NEEDS_SUBSTANTIAL_FORMALIZATION, (4) EXISTS_IN_OTHER_LEAN_LIBRARY.

In Mathlib:

* `CategoryTheory/Galois/Basic.lean`: `CategoryTheory.PreGaloisCategory`, `CategoryTheory.GaloisCategory`, `CategoryTheory.PreGaloisCategory.FiberFunctor`
* `CategoryTheory/Galois/IsFundamentalgroup.lean`: `CategoryTheory.PreGaloisCategory.IsFundamentalGroup`
* `AlgebraicGeometry/Morphisms/Etale.lean`: `AlgebraicGeometry.Etale`
* `AlgebraicGeometry/Sites/Etale.lean`: `AlgebraicGeometry.Scheme.etaleTopology`

Missing:

* The etale fundamental group of a connected scheme (finite etale covers form a Galois category). Classes 3, 4.
* Arithmetic fundamental groups of hyperbolic orbicurves over number fields and local fields, with the outer Galois action. Classes 3.

Other Lean libraries:

* `lana-agents/pi1 (dependency pinned by lana-agents/iut)`: etale fundamental group of a connected scheme via Galois categories, per its README. Lean 4.32, not built here, cannot be imported.

Bibliography keys: [AbsTopI], [AbsTopII], [AbsTopIII].

Needed first by: IUT1.Def3_1.

Mathlib has the abstract Galois category framework but no etale fundamental group of a scheme was found by name search. IUT I Definition 3.1 (b), page 61 (read), uses the etale fundamental groups of the curve, of the orbicurve, and of their geometric base changes.

### Tempered fundamental groups

Classes: (3) NEEDS_SUBSTANTIAL_FORMALIZATION, (4) EXISTS_IN_OTHER_LEAN_LIBRARY, (5) NEEDS_ADDITIONAL_LITERATURE.

In Mathlib: nothing found.

Missing:

* Andre's tempered fundamental group of a p-adic hyperbolic curve and its relation to semi-graphs of anabelioids. Classes 3, 4, 5.

Other Lean libraries:

* `lana-agents/tempered-fundamental-groups (dependency pinned by lana-agents/iut)`: tempered fundamental groups over integral models, per its README (algebraic models instead of rigid or Berkovich geometry). Lean 4.32, not built here, cannot be imported; agreement with the definition used in [SemiAnbd] and [EtTh] not checked.

Bibliography keys: [SemiAnbd], [EtTh].

Needed first by: IUT1.ThmB, IUT2.Rem1_4_1.

A search for "tempered" in the Mathlib sources finds only tempered distributions. The needed_by entries are from the mechanical index.

### Algebraic and arithmetic geometry: schemes, stacks, orbicurves

Classes: (1) EXISTS_IN_MATHLIB, (3) NEEDS_SUBSTANTIAL_FORMALIZATION, (4) EXISTS_IN_OTHER_LEAN_LIBRARY.

In Mathlib:

* `AlgebraicGeometry/Scheme.lean`: `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom`
* `AlgebraicGeometry/Morphisms/Smooth.lean`: `AlgebraicGeometry.SmoothOfRelativeDimension`
* `CategoryTheory/Sites/Descent/DescentData.lean`: `CategoryTheory.Pseudofunctor.IsStackFor`

Missing:

* Algebraic stacks, Deligne-Mumford stacks, and one-dimensional orbifolds (orbicurves) over a field; stack-theoretic quotients by finite group actions. Classes 3.
* Moduli stack of elliptic curves and its coarse space. Classes 3.

Other Lean libraries:

* `lana-agents/orbicurve-cores (dependency pinned by lana-agents/iut)`: cores of once-punctured elliptic curves, [CanLift] Proposition 2.7, per its README. Lean 4.32, not built here, cannot be imported.
* `lana-agents/curves-jacobian (dependency pinned by lana-agents/iut)`: smooth proper curves as schemes, Jacobians, per its README. Lean 4.32, not built here, cannot be imported.

Bibliography keys: [CanLift], [AbsTopIII], [EtTh].

Needed first by: IUT1.Def3_1.

Mathlib has schemes and a categorical notion of stack for a pseudofunctor; no algebraic stacks or orbicurves were found. IUT I Definition 3.1 (b), (d), pages 61 and 62 (read), forms a hyperbolic orbicurve as a stack-theoretic quotient by the involution -1, and uses hyperbolic orbicurves of type (1, l-tors) with a K-core ([EtTh] Definition 2.1, [CanLift] Remark 2.1.1).

### Hyperbolic curves

Classes: (3) NEEDS_SUBSTANTIAL_FORMALIZATION, (4) EXISTS_IN_OTHER_LEAN_LIBRARY.

In Mathlib: nothing found.

Missing:

* Smooth proper curves, genus, hyperbolicity 2g-2+r>0, stable reduction, and their arithmetic fundamental groups. Classes 3, 4.

Other Lean libraries:

* `lana-agents/curves-jacobian (dependency pinned by lana-agents/iut)`: smooth proper curves, per its README. Lean 4.32, not built here, cannot be imported.
* `lana-agents/belyi (dependency pinned by lana-agents/iut)`: Belyi's theorem, per its README. Lean 4.32, not built here, cannot be imported.

Bibliography keys: [AbsAnab], [AbsTopIII].

Needed first by: IUT1.Def3_1.

A plain text search for "hyperbolic curve" and declaration name searches for "genus" and "IsCurve" in Mathlib found nothing relevant. IUT I Definition 3.1 (b), page 61 (read), takes a once-punctured elliptic curve, a hyperbolic curve of type (1,1), with stable reduction at all nonarchimedean valuations.

### Grothendieck's anabelian geometry, absolute and mono-anabelian reconstruction, category-theoretic reconstruction

Classes: (3) NEEDS_SUBSTANTIAL_FORMALIZATION, (5) NEEDS_ADDITIONAL_LITERATURE.

In Mathlib: nothing found.

Missing:

* Anabelian reconstruction theorems of [AbsTopI], [AbsTopII], [AbsTopIII], [AbsAnab], [CombGC], [SemiAnbd]. Classes 3, 5.
* Mono-anabelian reconstruction algorithms (for example [AbsTopIII], Theorem 1.9, cited on IUT I page 127, read). Classes 3, 5.

Other Lean libraries:

* `lana-agents/iut (Iut/Anabelian, Iut/Reconstruction)`: anabelian objects and reconstruction material, per its README. Lean 4.32, not built here, cannot be imported.

Bibliography keys: [AbsTopIII], [AbsTopI], [AbsTopII], [AbsAnab], [CombGC], [SemiAnbd].

Needed first by: IUT1.Cor1_2, IUT2.Prop1_2, IUT3.Def1_1, IUT4.Prop1_4.

[AbsTopIII] is the most cited outside reference (406 citations counting all four papers). The needed_by entries are from the mechanical index.

### Frobenioids

Classes: (3) NEEDS_SUBSTANTIAL_FORMALIZATION, (5) NEEDS_ADDITIONAL_LITERATURE.

In Mathlib: nothing found.

Missing:

* The general theory of Frobenioids [FrdI] and poly-Frobenioids [FrdII]. Classes 3, 5.

Other Lean libraries:

* `lana-agents/iut (Iut/Frobenioid)`: Frobenioid material, per its README. Lean 4.32, not built here, cannot be imported.

Bibliography keys: [FrdI], [FrdII].

Needed first by: IUT1.Rem3_1_5, IUT2.Prop1_2, IUT3.Rem2_1_1, IUT4.Rem2_3_3.

No declaration named Frobenioid exists in Mathlib. IUT I page 61 (read) states that Theta-Hodge theaters are formulated via the theory of Frobenioids. The needed_by entries are from the mechanical index.

### Kummer theory

Classes: (2) DERIVABLE_FROM_MATHLIB, (3) NEEDS_SUBSTANTIAL_FORMALIZATION, (4) EXISTS_IN_OTHER_LEAN_LIBRARY.

In Mathlib:

* `FieldTheory/KummerExtension.lean`: `autAdjoinRootXPowSubC`
* `RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean`: `groupCohomology.H1ofAutOnUnitsUnique`

Missing:

* The Kummer map from the multiplicative group into H^1(G, mu_n) and its profinite limit (Kummer classes), as in IUT I page 127 (read). Classes 2, 3, 4.

Other Lean libraries:

* `lana-agents/continuous-kummer-theory (dependency pinned by lana-agents/iut)`: continuous Kummer theory for local fields, per its README. Lean 4.32, not built here, cannot be imported.

Bibliography keys: [AbsTopIII].

Needed first by: IUT1.Ex5_1.

Mathlib has cyclic Kummer extensions and Hilbert 90; no declaration with "Kummer" in its name was found for the Kummer map.

### Tate curves and Tate uniformization

Classes: (3) NEEDS_SUBSTANTIAL_FORMALIZATION, (4) EXISTS_IN_OTHER_LEAN_LIBRARY.

In Mathlib:

* `NumberTheory/ModularForms/JacobiTheta/OneVariable.lean`: `jacobiTheta`
* `NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean`: `jacobiTheta₂`

Missing:

* The Tate curve over a complete nonarchimedean field and q-uniformization. Classes 3, 4.

Other Lean libraries:

* `lana-agents/tate-curves-theta (dependency pinned by lana-agents/iut)`: q-uniformization and the formal algebraic theta function, per its README. Lean 4.32, not built here, cannot be imported; the README claims it is sorry-free at its tip, not checked here.

Bibliography keys: [EtTh].

Needed first by: IUT1.Cor1_2, IUT2.Def1_1.

Only complex analytic Jacobi theta functions exist in Mathlib; a plain text search for "TateCurve" and "Tate curve" found nothing. The needed_by entries are from the mechanical index.

### Elliptic curves with level structures

Classes: (1) EXISTS_IN_MATHLIB, (3) NEEDS_SUBSTANTIAL_FORMALIZATION, (4) EXISTS_IN_OTHER_LEAN_LIBRARY.

In Mathlib:

* `AlgebraicGeometry/EllipticCurve/Weierstrass.lean`: `WeierstrassCurve`, `WeierstrassCurve.j`, `WeierstrassCurve.IsElliptic`
* `AlgebraicGeometry/EllipticCurve/Affine/Point.lean`: `WeierstrassCurve.Affine.Point`
* `AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`: `WeierstrassCurve.Ψ`
* `AlgebraicGeometry/EllipticCurve/Reduction.lean`: `WeierstrassCurve.IsIntegral`

Missing:

* Level structures, the l-torsion as a Galois module, and the fields of definition of torsion points, as in IUT I Definition 3.1 (b), (c) and IUT IV Theorem 1.10. Classes 3, 4.
* Semistable reduction and Neron models, cited in the proof of IUT IV Proposition 1.8 ([NerMod], [Silv]). Classes 3, 5.

Other Lean libraries:

* `lana-agents/elliptic-curves (dependency pinned by lana-agents/iut)`: reduction theory of elliptic curves following Silverman, per its README. Lean 4.32, not built here, cannot be imported; a plain text search finds the word sorry in several files, status not checked.

Bibliography keys: [GenEll], [Silv], [NerMod].

Needed first by: IUT1.Def3_1, IUT4.Prop1_8, IUT4.Thm1_10.

Read: IUT I Definition 3.1 (b), (c), pages 61 and 62 (rational 2 and 3 torsion points, l at least 5, image of G_F in GL_2(F_l) containing SL_2(F_l), q-parameters at bad places); IUT IV page 21 (end of the proof of Proposition 1.8, citing [Silv] and [NerMod]) and page 22 (Theorem 1.10: torsion points of order 2, 3 and 5, Legendre form).

### Etale theta functions

Classes: (3) NEEDS_SUBSTANTIAL_FORMALIZATION, (5) NEEDS_ADDITIONAL_LITERATURE.

In Mathlib: nothing found.

Missing:

* The etale theta function and mono-theta environments of [EtTh]. Classes 3, 5.

Other Lean libraries:

* `lana-agents/iut (Iut/EtaleTheta)`: etale theta material, per its README. Lean 4.32, not built here, cannot be imported.

Bibliography keys: [EtTh].

Needed first by: IUT1.Cor1_2, IUT2.Def1_1, IUT3.Rem2_1_1, IUT4.Rem1_10_6.

[EtTh] is cited 380 times across the four papers (bibliography index). The needed_by entries are from the mechanical index.

### Hodge-Arakelov theory

Classes: (5) NEEDS_ADDITIONAL_LITERATURE.

In Mathlib: nothing found.

Missing:

* Hodge-Arakelov theory of elliptic curves ([HASurI], [HASurII]). Classes 5.

Bibliography keys: [HASurI], [HASurII].

Needed first by: IUT1.Rem4_3_1, IUT2.Rem1_12_5, IUT4.Rem1_10_1.

By the mechanical index every statement whose page span cites [HASurI] or [HASurII] is a Remark, which suggests, without having been checked by reading, that this theory serves as motivation rather than as a logical input.

### Valuations and normalized absolute values

Classes: (1) EXISTS_IN_MATHLIB, (2) DERIVABLE_FROM_MATHLIB.

In Mathlib:

* `RingTheory/Valuation/Basic.lean`: `Valuation`
* `Topology/Algebra/Valued/ValuationTopology.lean`: `Valued`
* `Algebra/Order/AbsoluteValue/Basic.lean`: `AbsoluteValue`
* `Algebra/Order/Ring/Basic.lean`: `IsNonarchimedean`
* `NumberTheory/Padics/PadicNorm.lean`: `padicNorm`
* `NumberTheory/Padics/PadicVal/Basic.lean`: `padicValRat`
* `NumberTheory/Ostrowski.lean`: `Rat.AbsoluteValue.equiv_padic_of_bounded`
* `RingTheory/DedekindDomain/AdicValuation/Valuation.lean`: `IsDedekindDomain.HeightOneSpectrum.valuation`, `IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one`
* `NumberTheory/NumberField/ProductFormula.lean`: `NumberField.prod_abs_eq_one`, `NumberField.FinitePlace.prod_eq_inv_abs_norm`

In this project:

* `IUT/Prerequisites/ProductFormula.lean`: `IUT.Prerequisites.normAbs`, `IUT.Prerequisites.prod_normAbs_eq_one`, `IUT.Prerequisites.sum_log_normAbs_eq_zero`
* `IUT/Prerequisites/PositiveRationalsZhatUnits.lean`: `IUT.Prerequisites.eq_one_of_forall_valuation_eq_one`

Needed first by: IUT4.Def1_9, IUT3.Rem3_12_1.

The product formula exists in Mathlib; this project restates it over the valuation set of IUT IV Definition 1.9. IUT III Remark 3.12.1 (iii), pages 186 and 187 (read), refers to the product formula.

### Nonarchimedean analysis

Classes: (1) EXISTS_IN_MATHLIB, (3) NEEDS_SUBSTANTIAL_FORMALIZATION.

In Mathlib:

* `Topology/MetricSpace/Ultra/Basic.lean`: `IsUltrametricDist`
* `NumberTheory/Padics/Hensel.lean`: `hensels_lemma`
* `NumberTheory/Padics/Complex.lean`: `PadicComplex`

Missing:

* Rigid analytic or Berkovich geometry, used in the literature for the tempered fundamental group and the Tate curve. Classes 3, 5.

Bibliography keys: [EtTh], [SemiAnbd].

Basic ultrametric analysis exists; analytic spaces over nonarchimedean fields were not found.

### p-adic logarithms and exponentials

Classes: (2) DERIVABLE_FROM_MATHLIB, (3) NEEDS_SUBSTANTIAL_FORMALIZATION, (4) EXISTS_IN_OTHER_LEAN_LIBRARY.

In Mathlib:

* `Analysis/Normed/Algebra/Logarithm.lean`: `NormedSpace.log`, `NormedSpace.logSeries`
* `Analysis/Normed/Algebra/Exponential.lean`: `NormedSpace.exp`

Missing:

* Convergence of NormedSpace.log on the disc of radius 1 over a complete ultrametric field, the homomorphism property, its extension to all units of a p-adic local field, and its image; these are listed as TODO items in the Mathlib file. Outside the region of convergence NormedSpace.log takes a junk value, so it is not yet the p-adic logarithm of the papers. The p-adic radius of convergence of NormedSpace.exp was not found either. Classes 2, 3, 4.
* Log-shells: IUT III Definition 1.1 (page 24, rendered and read) defines the log-shell as (p_v*)^{-1} times the pre-log-shell, the image under the p_v-adic logarithm of the Galois invariant units, with p_v* = p_v for p_v odd and p_v* = p_v^2 for p_v = 2, citing [AbsTopIII], Definition 5.4 (iii). Classes 3.

Other Lean libraries:

* `lana-agents/padic-log-volume (dependency pinned by lana-agents/iut)`: the p-adic logarithm of a complete discretely valued field of characteristic 0 and normalized Haar log-volume, per its README. Lean 4.32, not built here, cannot be imported.
* `lana-agents/iut (Iut/Concrete/LocalConstruct/LocalLogShell.lean)`: a log-shell defined as (2p)^{-1} log of the principal units. Lean 4.32, not built here, cannot be imported. By an elementary argument not formalized here this is the same set as on IUT III page 24: log of the units equals log of the principal units, which is a Z_p-module, and 2p differs from p* by a unit when p is odd and equals p* = 4 when p = 2.

Bibliography keys: [AbsTopIII].

Needed first by: IUT3.Def1_1, IUT3.Prop3_9, IUT4.Prop1_2.

Mathlib v4.36.0 defines NormedSpace.log for any topological Q-algebra, hence for Q_p, with only its algebraic properties at 1. The convergence on the open unit disc, the homomorphism property and the extension to the units are proved in this library for Q_p (IUT/Prerequisites/PadicLog.lean), where the log-shell of IUT III Definition 1.1 is defined for Q_p; finite extensions are not treated there. IUT3.Prop3_9 and IUT4.Prop1_2 are the statements that use it (Log-volume for Packets and Processions; Differents and Logarithms).

### Arithmetic divisors

Classes: (2) DERIVABLE_FROM_MATHLIB.

In Mathlib:

* `NumberTheory/RamificationInertia/Basic.lean`: `Ideal.sum_ramification_inertia`

In this project:

* `IUT/PaperIV/ArithmeticDivisor.lean`: `IUT.PaperIV.ADiv`, `IUT.PaperIV.degF`, `IUT.PaperIV.normalizedDeg`

Missing:

* Pull-back of arithmetic divisors to a finite extension and the identity deg(a|_K) = deg(a) of IUT IV Definition 1.9 (i), which the paper defines "in the evident fashion"; the natural proof uses the fundamental identity, which Mathlib has as Ideal.sum_ramification_inertia. Classes 2.
* Normalized E-degree of Definition 1.9 (ii). Classes 2.
* The arithmetic divisors of the different ideal, of the q-parameters and of the conductor used in IUT IV Theorem 1.10 (pages 22 and 23, read). Classes 2, 3.

Other Lean libraries:

* `lana-agents/iut (Iut4Sec1/Global/Pullback.lean, Iut4Sec1/Global/ArithmeticDivisor.lean)`: pull-back of arithmetic divisors (coefficient times ramification index at finite places, times local degree at infinite places) and invariance of the normalized degree, per its module docstring. Lean 4.32, not built here, cannot be imported; this is one choice of the pull-back that the paper leaves to the reader.

Bibliography keys: [GenEll].

Needed first by: IUT4.Def1_9, IUT4.Thm1_10.

Read: IUT IV pages 21 to 23.

### Arakelov degrees

Classes: (2) DERIVABLE_FROM_MATHLIB, (3) NEEDS_SUBSTANTIAL_FORMALIZATION.

In Mathlib: nothing found.

In this project:

* `IUT/PaperIV/ArithmeticDivisor.lean`: `IUT.PaperIV.degF`

Missing:

* Arithmetic line bundles on the spectrum of the ring of integers of a number field and their Arakelov degree. Which statements use them was not determined by reading in this pass. Classes 2, 3.

Other Lean libraries:

* `lana-agents/iut (Iut/Arakelov: FractionalIdeal.lean, LineBundle.lean, Container.lean, ArchScaling.lean, QPilot.lean)`: Arakelov line bundle material, per its file names and README. Lean 4.32, not built here, cannot be imported.

Bibliography keys: [Arak].

Needed first by: IUT4.Rem1_10_4.

A plain text search for "Arakelov" in the Mathlib sources finds nothing. The needed_by entry is from the mechanical index.

### Heights and discriminants

Classes: (1) EXISTS_IN_MATHLIB, (2) DERIVABLE_FROM_MATHLIB, (3) NEEDS_SUBSTANTIAL_FORMALIZATION, (4) EXISTS_IN_OTHER_LEAN_LIBRARY, (5) NEEDS_ADDITIONAL_LITERATURE.

In Mathlib:

* `NumberTheory/Height/Basic.lean`: `Height.AdmissibleAbsValues`, `Height.mulHeight₁`, `Height.logHeight₁`
* `NumberTheory/Height/NumberField.lean`: `NumberField.absLogHeight₁`
* `NumberTheory/Height/EllipticCurve.lean`: `WeierstrassCurve.Affine.Point.naiveHeight`
* `NumberTheory/NumberField/Discriminant/Defs.lean`: `NumberField.discr`
* `NumberTheory/NumberField/Discriminant/Different.lean`: `NumberField.absNorm_differentIdeal`

Missing:

* The normalized degrees log(d), log(q), log(f) of the different, q-parameter and conductor divisors, as in the statement of IUT IV Theorem 1.10, pages 22 and 23 (read); the q-parameters are the local heights of [GenEll], Definition 3.3, per IUT I page 62 (read). Classes 2, 3.
* Heights of elliptic curves and of points of hyperbolic curves in the sense of [GenEll] (not read). Classes 3, 4, 5.

Other Lean libraries:

* `lana-agents/heights (dependency pinned by lana-agents/iut)`: Weil heights, the height machine on curves, and conductor and different bounds of [GenEll], per its README. Lean 4.32, not built here, cannot be imported.
* `lana-agents/genl (dependency pinned by lana-agents/iut)`: [GenEll] Theorem 2.1 project, per its README. Lean 4.32, not built here, cannot be imported; its README and a text search show a sorry in Challenge.lean.

Bibliography keys: [GenEll].

Needed first by: IUT1.Def3_1, IUT4.Thm1_10.


### Ramification theory and the different

Classes: (1) EXISTS_IN_MATHLIB, (2) DERIVABLE_FROM_MATHLIB, (3) NEEDS_SUBSTANTIAL_FORMALIZATION, (4) EXISTS_IN_OTHER_LEAN_LIBRARY.

In Mathlib:

* `RingTheory/RamificationInertia/Ramification.lean`: `Ideal.ramificationIdx`
* `RingTheory/RamificationInertia/Inertia.lean`: `Ideal.inertiaDeg`
* `NumberTheory/RamificationInertia/Basic.lean`: `Ideal.sum_ramification_inertia`
* `RingTheory/DedekindDomain/Different.lean`: `differentIdeal`
* `NumberTheory/NumberField/Discriminant/Different.lean`: `NumberField.absNorm_differentIdeal`
* `RingTheory/Valuation/RamificationGroup.lean`: `ValuationSubring.inertiaSubgroup`

Missing:

* Higher ramification groups (no declaration with "RamificationGroup" or "lowerNumbering" found). Classes 3.
* Estimates of the different of local fields and of tensor products of local fields, IUT IV Propositions 1.1 to 1.3 (Multiple Tensor Products and Differents; Differents and Logarithms; Estimates of Differents; pages 9 to 13; the inequality of Proposition 1.3 (i) for finite extensions of Q_p is proved in IUT/PaperIV/LocalFields/, the rest is open). Classes 2, 3.

Other Lean libraries:

* `lana-agents/padic-log-volume (dependency pinned by lana-agents/iut)`: trace duality in finite Q_p algebras and their tensor products, ingredients of IUT IV Proposition 1.1, per its README. Lean 4.32, not built here, cannot be imported.
* `lana-agents/iut (Iut/Tower: Different.lean, DifferentBound.lean, Inertia.lean, RamIdx.lean, WildBound.lean)`: different and ramification bounds in towers, per file names. Lean 4.32, not built here, cannot be imported.

Bibliography keys: [Kobl].

Needed first by: IUT4.Prop1_1, IUT4.Prop1_2, IUT4.Prop1_3, IUT4.Thm1_10.

IUT IV Theorem 1.10, pages 22 and 23 (read), uses the arithmetic divisor of the different ideal of a number field over Q.

### Haar measures and log-volumes

Classes: (1) EXISTS_IN_MATHLIB, (2) DERIVABLE_FROM_MATHLIB, (3) NEEDS_SUBSTANTIAL_FORMALIZATION.

In Mathlib:

* `MeasureTheory/Measure/Haar/Basic.lean`: `MeasureTheory.Measure.haarMeasure`, `MeasureTheory.Measure.haar`
* `MeasureTheory/Group/Measure.lean`: `MeasureTheory.Measure.IsAddHaarMeasure`
* `MeasureTheory/Measure/Haar/Unique.lean`: `MeasureTheory.Measure.haarScalarFactor`

Missing:

* Normalized Haar measure on a p-adic local field (ring of integers of volume 1) and the scaling rule vol(aS) = |a| vol(S). Classes 2.
* Log-volumes of packets and processions and of tensor packets of log-shells, IUT III Proposition 3.9 and IUT IV Proposition 1.4 (titles only, not read). Classes 3.

Other Lean libraries:

* `lana-agents/padic-log-volume (dependency pinned by lana-agents/iut)`: normalized Haar log-volume, per its README. Lean 4.32, not built here, cannot be imported.
* `lana-agents/iut (Iut/Concrete/LocalConstruct/Haar.lean, Volume.lean)`: Haar log-volume constructions, per file names. Lean 4.32, not built here, cannot be imported.

Bibliography keys: [AbsTopIII].

Needed first by: IUT3.Prop3_9, IUT4.Prop1_4.


### Tensor products of local fields

Classes: (2) DERIVABLE_FROM_MATHLIB, (3) NEEDS_SUBSTANTIAL_FORMALIZATION.

In Mathlib:

* `LinearAlgebra/TensorProduct/Defs.lean`: `TensorProduct`
* `RingTheory/TensorProduct/Basic.lean`: `Algebra.TensorProduct.includeLeft`

Missing:

* Decomposition of a tensor product of finite extensions of Q_p into a product of fields, integral structures, and differents (IUT IV Proposition 1.1; IUT III Propositions 3.1 and 3.2 on tensor packets; titles only, not read). Classes 2, 3.

Other Lean libraries:

* `lana-agents/padic-log-volume (dependency pinned by lana-agents/iut)`: trace duality for tensor products of finite Q_p algebras, per its README. Lean 4.32, not built here, cannot be imported.
* `lana-agents/iut (Iut/Concrete/LocalConstruct/TensorIntegral.lean, PacketDifferent.lean, LocalDifferent.lean)`: integral structures and differents of tensor packets, per file names. Lean 4.32, not built here, cannot be imported.

Needed first by: IUT3.Prop3_1, IUT3.Prop3_2, IUT4.Prop1_1.


### Diophantine geometry

Classes: (3) NEEDS_SUBSTANTIAL_FORMALIZATION, (4) EXISTS_IN_OTHER_LEAN_LIBRARY, (5) NEEDS_ADDITIONAL_LITERATURE.

In Mathlib:

* `NumberTheory/FLT/MasonStothers.lean`: `Polynomial.abc`
* `NumberTheory/SiegelsLemma.lean`: `Int.Matrix.exists_ne_zero_int_vec_norm_le`

In this project:

* `IUT/Applications/ABC.lean`

Missing:

* The equivalence of [GenEll] Theorem 2.1 between bounded-degree Vojta or abc type statements for hyperbolic curves and a restricted abc statement for the tripod, as described in the README of the genl library; its use in IUT IV Corollaries 2.2 and 2.3 was not read. Classes 3, 4, 5.
* Faltings' theorem and related results cited in remarks ([Falt]). Classes 5.

Other Lean libraries:

* `lana-agents/genl (dependency pinned by lana-agents/iut)`: [GenEll] project, per its README. Lean 4.32, not built here, cannot be imported.

Bibliography keys: [GenEll], [Falt], [vFr].

Needed first by: IUT4.Cor2_2, IUT4.Cor2_3.

The function field abc (Mason-Stothers) and Siegel lemma exist in Mathlib. IUT4.Cor2_2 and IUT4.Cor2_3 are cited from their titles (Construction of Suitable Initial Theta-Data; Diophantine Inequalities).

### Szpiro-type and Vojta-type inequalities

Classes: (6) UNRESOLVED_OR_DISPUTED.

In Mathlib: nothing found.

Missing:

* Szpiro and Vojta type inequalities over number fields: open conjectures in general. IUT IV Corollary 2.3 (title: Diophantine Inequalities; not read in this pass) is where the papers state Diophantine inequalities as consequences of the theory. Whether that derivation is valid is the disputed point; nothing here takes a position. Classes 6.
* Function field (geometric) Szpiro inequality via Bogomolov ([BogIUT]), cited in remarks. Classes 5.

Bibliography keys: [GenEll], [BogIUT].

Needed first by: IUT4.Cor2_3.

These are targets of the papers, not prerequisites; they must never enter the library as assumptions of unconditional results.

### Set-theoretic foundations and universe management

Classes: (1) EXISTS_IN_MATHLIB, (2) DERIVABLE_FROM_MATHLIB, (3) NEEDS_SUBSTANTIAL_FORMALIZATION, (5) NEEDS_ADDITIONAL_LITERATURE.

In Mathlib:

* `SetTheory/ZFC/Basic.lean`: `ZFSet`, `ZFSet.omega`, `ZFSet.powerset`, `ZFSet.sUnion`, `ZFSet.IsFunc`, `ZFSet.mem_wf`, `ZFSet.range`
* `SetTheory/ZFC/VonNeumann.lean`: `ZFSet.vonNeumann`
* `SetTheory/Cardinal/Regular.lean`: `Cardinal.IsInaccessible`
* `Logic/Small/Defs.lean`: `Small`
* `Basic/UnivLE.lean`: `UnivLE`

In this project:

* `IUT/Foundations/GrothendieckUniverse.lean`: `IUT.Foundations.IsGrothendieckUniverse`, `IUT.Foundations.ExistenceAxiom`, `IUT.Foundations.exists_universe_forall_mem`, `IUT.Foundations.exists_ascending_chain`, `IUT.Foundations.not_exists_descending_mem_chain`

Missing:

* The existence axiom (dagger G): every set lies in a Grothendieck universe. Not a theorem of ZFC; the paper assumes it (IUT IV page 67) and leaves the existence of ZFCG-models aside, citing Feferman (page 68). In Lean, `ExistenceAxiom` is independent of what can be proved about `ZFSet.{u}` (see the module docstring of `IUT/Foundations/GrothendieckUniverse.lean`). Classes 5.
* No Grothendieck universe on ZFSet is exhibited (for example the image of ZFSet.{u} inside ZFSet.{u+1}); Mathlib has the embedding only at the PSet level (PSet.embed). Classes 2.
* Species, set-theoretic formulas, and absoluteness of formulas between universes (IUT IV Definition 3.1 and page 68); needs a formal syntax for set-theoretic formulas. Classes 3, 5.

Bibliography keys: [McLn], [Drk], [Ffmn].

Needed first by: IUT4.Def3_1.

Read: IUT IV pages 67 and 68. A search for "GrothendieckUniverse" in Mathlib declaration names found nothing.

## Rough dependency order

A coarse planning order: most items in a layer use items of earlier layers. It is not a proved dependency graph; for example the universe material is independent of the arithmetic layers.

1. Valuations and normalized absolute values; Algebraic number fields and their completions; Algebraic closures and Galois theory (finite and infinite); Profinite groups and continuous cohomology.
2. p-adic logarithms and exponentials; Haar measures and log-volumes; Tensor products of local fields; Ramification theory and the different; Arithmetic divisors; Arakelov degrees; Kummer theory; Local and global class field theory.
3. Algebraic and arithmetic geometry: schemes, stacks, orbicurves; Hyperbolic curves; Elliptic curves with level structures; Tate curves and Tate uniformization; Etale fundamental groups; Nonarchimedean analysis.
4. Tempered fundamental groups; Grothendieck's anabelian geometry, absolute and mono-anabelian reconstruction, category-theoretic reconstruction; Frobenioids; Etale theta functions; Heights and discriminants.
5. Diophantine geometry; Set-theoretic foundations and universe management; Hodge-Arakelov theory.
6. Szpiro-type and Vojta-type inequalities.

## Verified prerequisites

* `IUT.Prerequisites.posRat_inter_zhatUnits` in `IUT/Prerequisites/PositiveRationalsZhatUnits.lean`: `{q : ℚ | 0 < q ∧ ∃ u : Zhatˣ, Zhat.toFiniteAdeles ↑u = (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) q} = {1}`. Source: IUT I, Example 5.1 (v), page 127 (rendered); IUT III, Remark 3.12.1 (iii), pages 186 and 187 (rendered).
* `IUT.Prerequisites.eq_one_of_forall_valuation_eq_one` in `IUT/Prerequisites/PositiveRationalsZhatUnits.lean`: `∀ {q : ℚ}, 0 < q → (∀ (v : HeightOneSpectrum ℤ), (valuation ℚ v) q = 1) → q = 1`. Source: as above.
* `IUT.Prerequisites.prod_normAbs_eq_one` in `IUT/Prerequisites/ProductFormula.lean`: `∀ {F : Type*} [Field F] [NumberField F] {x : F}, x ≠ 0 → ∏ᶠ (v : Valuations F), normAbs v x = 1`. Source: IUT IV, Definition 1.9, pages 21 and 22 (rendered); Mathlib NumberField.prod_abs_eq_one.
* `IUT.Prerequisites.sum_log_normAbs_eq_zero` in `IUT/Prerequisites/ProductFormula.lean`: `∀ {F : Type*} [Field F] [NumberField F] {x : F}, x ≠ 0 → ∑ᶠ (v : Valuations F), Real.log (normAbs v x) = 0`. Source: as above.
* `IUT.Foundations.exists_universe_forall_mem` in `IUT/Foundations/GrothendieckUniverse.lean`: `ExistenceAxiom → ∀ {I : Type*} [Small.{u} I] (V : I → ZFSet.{u}), ∃ W, IsGrothendieckUniverse W ∧ ∀ (i : I), V i ∈ W`. Source: IUT IV, page 67 (rendered).
* `IUT.Foundations.exists_ascending_chain` in `IUT/Foundations/GrothendieckUniverse.lean`: `ExistenceAxiom → ∃ V : ℕ → ZFSet.{u}, (∀ n, IsGrothendieckUniverse (V n)) ∧ (∀ n, V n ∈ V (n + 1)) ∧ ∃ W, IsGrothendieckUniverse W ∧ ∀ n, V n ∈ W`. Source: IUT IV, page 67 (rendered).
* `IUT.Foundations.not_exists_descending_mem_chain` in `IUT/Foundations/GrothendieckUniverse.lean`: `¬∃ V : ℕ → ZFSet.{u}, ∀ (n : ℕ), V (n + 1) ∈ V n`. Source: IUT IV, page 68 (rendered).

The universe results use the existence axiom only as an explicit hypothesis `ExistenceAxiom`; it is not proved. `ExistenceAxiom` is a statement about Lean's model `ZFSet.{u}`, not the paper's axiom in the paper's set theory, and it is not expected to be provable or refutable in Lean: in the standard semantics where `Type u` is `V_κ` for an inaccessible `κ`, it fails when `κ` is the least inaccessible (then `ZFSet.{u}` contains no Grothendieck universe) and holds when `κ` is an inaccessible limit of inaccessibles. This argument is about models and is not formalized. In models where it fails, the two conditional theorems `exists_universe_forall_mem` and `exists_ascending_chain` are vacuous. All seven results depend only on the axioms `propext`, `Classical.choice`, `Quot.sound`.

## Candidates not formalized, and why

* Log-shell of Q_p: Mathlib v4.36.0 defines NormedSpace.log, but without convergence on the disc, the homomorphism property, or the extension to all units (open TODO items in Analysis/Normed/Algebra/Logarithm.lean). These are proved in this library for Q_p (IUT/Prerequisites/PadicLog.lean), where the log-shell of IUT III Definition 1.1 (page 24) is defined as the image of the units under the logarithm divided by p*, and its equality with Z_p is a theorem. Finite extensions of Q_p remain open.
* Pull-back invariance deg(a|_K) = deg(a) of IUT IV Definition 1.9 (i): The paper defines the pull-back only "in the evident fashion"; choosing the pull-back so that the identity holds would make it nearly definitional. Deferred until the convention is fixed from [GenEll], section 1, which was not read.
* Degree zero of principal arithmetic divisors: Not defined on the pages read (IUT IV pages 21 to 23); with the archimedean weight 1 of Definition 1.9 (i) the coefficient convention at complex places would have to be chosen. Only the product formula itself was formalized.
* Existence of a Grothendieck universe in ZFSet.{u+1}: Mathlib has the embedding only at the PSet level (PSet.embed); building it for ZFSet and checking axioms (i) to (v) is a separate task.

## External repository `lana-agents/iut`

Read only. Its README states a proof of an implication from a variant of IUT III Corollary 3.12 to the abc conjecture, with the variant itself not proved. It depends on fifteen further Lean libraries, pinned dependencies of the lana-agents organization at the revisions in data/external_projects.json. None of this can be imported here because of the toolchain difference; statements and definitions would have to be ported and rechecked. Toolchain: leanprover/lean4:v4.32.0 with Mathlib v4.32.0.
