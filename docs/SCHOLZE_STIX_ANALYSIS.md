# The Scholze and Stix manuscript: claims, propositions, hypotheses

This document lists, item by item, what P. Scholze and J. Stix assert in *Why abc is still a conjecture*, states each assertion as a precise proposition where one can be stated, names the hypotheses it rests on, and points to the corresponding passage of the four IUT papers. Mochizuki's responses are in `docs/MOCHIZUKI_RESPONSES.md`; the mapping between the two is in `data/dispute_map.json` and in the table at the end.

Three layers are kept apart throughout. **SS** marks what Scholze and Stix say. **M** marks what Mochizuki says. **Assessment** marks the view of this project. Neither party's standing is treated as evidence. This document does not declare either side right.

## Sources and versions

| Document | File | Pages | Read | Version notes |
|---|---|---|---|---|
| Scholze and Stix, *Why abc is still a conjecture* | PDF from <https://www.math.uni-bonn.de/people/scholze/WhyABCisStillaConjecture.pdf> (SHA-256 in `data/dispute_map.json`) | 10 | all 10 | Dated July 16, 2018 (Bonn web page). Mochizuki's comment file of September 2018 calls the version it answers "SS2018-08"; its quotations (footnotes 10 and 12, "convince" in Section 2.1 (3)) match this file, so this file is treated as that version. The May 2018 version "SS2018-05" was not available. Passages of it are known here only through Mochizuki's quotations in Cmt2018-05; such quotations are attributed to Cmt2018-05, not to the manuscript. Its footnote and remark numbers differ from this file (Cmt2018-05's "Remark 8" corresponds to Remark 9 here, its "Footnote 7" to footnote 10 here). |
| Mochizuki, *Report on Discussions … March 15 to 20, 2018* | `Rpt2018.pdf`, from <https://www.kurims.kyoto-u.ac.jp/~motizuki/> | 45 | all 45 | Title page dated **February 2019**. The comment files cite versions of July and September 2018. Only this version was read. |
| Mochizuki, *Comments on the manuscript by Scholze–Stix* | `Cmt2018-05.pdf` | 8 | all 8 | Dated July 2018; answers SS2018-05. |
| Mochizuki, *Comments on the manuscript (2018-08 version)* | `Cmt2018-08.pdf` | 5 | all 5 | Dated September 2018. |
| IUT III (May 2020 manuscript) | author's manuscript, SHA-256 in `data/source_manifest.json` | 199 | pages 173, 174, 180 to 195 | Statement of Corollary 3.12 (pages 173, 174), Step (xi) (pages 181 to 186), Remarks 3.12.1 to 3.12.3 (pages 186 to 195). |

Full hashes are in `data/dispute_map.json`. No further document was downloaded.

**Version caveat (assessment).** Scholze and Stix quote Step (xi) of the proof of Corollary 3.12 as "If one interprets the above discussion in terms of the notation introduced in the statement of Corollary 3.12, then one concludes [...] that −|log(q)| ≤ −|log(Θ)| ∈ ℝ" (page 9). That sentence does not occur in the May 2020 manuscript used by this project, whose Step (xi) is divided into substeps (xi-a) to (xi-h) (pages 181 to 185). Scholze and Stix therefore read an earlier version. Whether the substeps and Remark 3.12.2 (ii) (the toy models) were added after March 2018 cannot be decided from the files available here; the report of February 2019 already cites the toy models of Remark 3.12.2 (ii).

Formulas used below were checked against rendered pages: SS pages 2, 3, 4, 8, 9, 10; report pages 2, 17, 18, 24, 25; IUT III pages 173, 174, 184, 190, 191.

## Part 1. The reduction to Claim 6 and Vojta's inequality (Section 1)

**SS-1 (page 2, Conjecture 3).** The uniform Vojta inequality for hyperbolic curves: for `ε > 0`, `d ≥ 1`, all `P ∈ X(k̄)` with `[κ(P) : ℚ] ≤ d` satisfy `h_{ω(D)}(P) < (1 + ε)(d(P) + n¹_D(P)) + O_{ε,d,X}(1)` (1.1). Proposition: a standard conjecture, quoted. IUT counterpart: IUT IV, Corollary 2.2 and 2.3 (not read for this document).

**SS-2 (page 2, Section 1.2).** Reduction via Belyi maps and [GenEll] to elliptic curves `E/k` with (1) bounded local data at 2 and ∞, (2) split semistable reduction, so that `h(P) = (1/6) deg(q_E) + O(h(P)^{1/2} + 1)` (1.2), (3) a prime `ℓ = ℓ(P)` with `h(P)^{1/2} ≤ ℓ ≤ h(P)^{1/2}(c₁ + c₂ log h(P))` (1.3), such that the image of the mod `ℓ` Galois representation `ρ : Gal_k → GL(E[ℓ](k̄)) ≅ GL₂(F_ℓ)` contains `SL₂(F_ℓ)` (not necessarily all of `GL₂(F_ℓ)`), and such that at places of bad reduction the extension `0 → μ_ℓ → E[ℓ] → ℤ/ℓℤ → 0` from the Tate parametrization does not split (`q_v` not an `ℓ`-th power). Hypotheses: the cited results of [GenEll] and [Belyi]; an exceptional sparse set is "omitted". IUT counterpart: IUT IV, Theorem 1.10 and its proof (not read for this document). Not disputed by either side.

**SS-3 (page 3, Remark 5).** For fixed `d ≥ 1` and `b > 0` there are only finitely many `E/k` corresponding to `P ∈ M_ell(k)` **as above** (that is, subject to the restrictions (1) to (3) of Section 1.2, over the varying number fields `k`) with `[k : ℚ] ≤ d` and `h(P) ≤ b`. Proof offered: Faltings' theorem (Shafarevich conjecture) for the Weil restriction `A = R_{k/ℚ}(E)`, of dimension bounded by `d` with good reduction outside a finite set of primes depending on `b`, and finiteness of the fibers of `E/k ↦ A/ℚ`. M (Cmt2018-08 (C1), pages 1 and 2) says the finiteness follows from the `j`-invariant and finiteness of algebraic numbers of bounded degree and bounded height, and that the Faltings route needs a bound on the discriminant of `k/ℚ`.
Assessment: two statements must be kept apart. (a) Finiteness of the moduli values: the points `P`, equivalently the `j`-invariants `j(E)`, of degree at most `d` and height at most `b` form a finite set; this is Northcott's theorem and is the content of M's argument. (b) Finiteness of the curves `E/k` themselves: this does not follow from (a), since infinitely many curves share one `j`-invariant (for example the quadratic twists `y² = x³ − D²x` over `ℚ`, all with `j = 1728`). Any claim about curves, or about the fibers of the Weil restriction, needs its own argument using the restrictions "as above"; this project neither proves nor refutes (b). The reduction SS-5 needs neither (a) nor (b).

**SS-4 (page 3, Claim 6).** Their summary of IUT IV, Theorem 1.10: functions `α_d(ℓ) → 0`, `β_d(ℓ) = O_d(1)` with `(1/6) deg(q_E) ≤ (1 + α_d(ℓ))(d(P) + n¹_∞(P)) + β_d(ℓ) ℓ`.

**SS-5 (page 3, two displays after Claim 6).** Proposition (real analysis, formalized): if `h > 0`, `h ≤ Q + c(h^{1/2} + 1)` with `Q = (1/6) deg(q_E)`, Claim 6 holds, and (1.3) holds, then `h (1 − (c(1 + h^{−1/2}) + β(c₁ + c₂ log h))/h^{1/2}) ≤ (1 + α) N` with `N = d(P) + n¹_∞(P)`; and if moreover `0 < 1 + α < (1 − …)(1 + ε)` and `N ≥ 0`, then `h ≤ (1 + ε) N`. Uniformly over all `P`, this gives `h(P) ≤ (1 + ε) N(P) + C_ε`.
Lean: `IUT.Audit.ScholzeStix.display_after_claim6`, `display_after_claim6_abs`, `vojta_pointwise`, `vojta_of_claim6` in `IUT/Audit/ScholzeStix/Reduction.lean`.
Hypotheses, exactly: `h > 0`; `N ≥ 0` (not displayed; true for the intended quantities and needed); `β ≥ 0` for the first display (not displayed; removable by passing to `|β|`); `α(ℓ) → 0`; `β` bounded for large `ℓ`; `c, c₁, c₂` constants.
Assessment: the arithmetic is correct with these two implicit hypotheses made explicit. The final `O(1)` does not need Remark 5: for `h(P) < H` one has `h(P) < H ≤ (1 + ε) N(P) + H` because `N ≥ 0`. The only property of the different plus conductor term `N` that the reduction uses is this lower bound. So the objection to Remark 5 (Cmt2018-08 (C1)) does not affect this reduction.

**SS-6 (pages 3 and 4, display (1.4)).** Claim 6 is deduced in IUT IV, Theorem 1.10 from `−|log(q)| ≤ −|log(Θ)|` (1.4), "the main claim of" IUT III, Corollary 3.12. IUT counterpart: IUT III, Corollary 3.12, pages 173 and 174, which states `−|log(Θ)| ∈ ℝ` and `−|log(Θ)| ≥ −|log(q)|`, with `−|log(Θ)|` the procession-normalized mono-analytic log-volume of the holomorphic hull of the union of possible images of a Θ-pilot object, subject to (Ind1), (Ind2), (Ind3). The orientation agrees. Lean: `IUT.PaperIII.Corollary312` (existing) formalizes the numerical shape.

**SS-7 (page 4).** `−|log(q)| = −deg(q̲_E) = −(1/(2ℓ)) deg(q_E)`.

**SS-8 (page 4, display (1.5)).** "In essential approximation", `−|log(Θ)| ≈ (1/ℓ*) Σ_v Σ_{j=1}^{ℓ*} (j d(P)_v − j² v(q_v) log N(v)/(2ℓ[k:ℚ])) = ((ℓ* + 1)/2)(d(P) − (1/6) deg(q_E))`, with `ℓ* = (ℓ − 1)/2`; substituting into (1.4) gives `(1/6) deg(q_E) ≲ (1 − 12/(ℓ(ℓ + 1)))^{−1} d(P)`.
Lean (existing): `display_1_5`, `consequence_with_squares` in `IUT/Audit/ScholzeStix/Section1_3.lean`.
Hypotheses: the "essential approximation" itself, which is SS's reading of IUT IV, Theorem 1.10; it is not derived.
Assessment: the inverted form needs `1 − 12/(ℓ(ℓ + 1)) > 0`, that is `ℓ ≥ 5`; at `ℓ = 3` the factor vanishes. The existing Lean statement uses the multiplied form, which is valid for all `ℓ`.

**SS-9 (page 4, display (1.6)).** SS claim that the reasoning of Corollary 3.12 "rather describes" the same average with the factor `j²` missing, `((ℓ* + 1)/2) d(P) − deg(q_E)/(2ℓ)`, from which (1.4) gives only `0 ≲ d(P)`, "essentially free of content".
Lean (existing): `display_1_6`, `consequence_without_squares`. New: `withSquares_eq_withoutSquares_scaled` and `avgSq_eq` in `Blurring.lean`: (1.5) and (1.6) differ exactly by the factor `avg_j j² = ℓ(ℓ + 1)/12` on the `q` term, for `ℓ* ≥ 1` and `ℓ = 2ℓ* + 1`.
This is the central claim; its justification is Section 2.2.

## Part 2. The simplifications of Section 2.1 (what is replaced by what)

SS (pages 4 and 5) give four "excuses" for their simplifications: (1) Mochizuki agreed some are acceptable, for example for `F^{⊩▶×μ}`-prime strips; (2) the Kyoto discussions were only slightly more sophisticated; (3) the drastic ones (a Hodge theater replaced by a curve abstractly isomorphic to `X`; identical objects identified along the identity) are "inessential to the point we are making"; (4) "even with all subtleties restored, the issue we are pointing out will prevail". M contests (2), (3), (4) (Cmt2018-05 (C2) to (C4)).

| Id | Page | Replaced | Replaced by | Hypothesis it introduces | IUT passage |
|---|---|---|---|---|---|
| SS-S1 | 5 | Initial Θ-data | `E/k`, prime `ℓ`, `X = E \ {0}`; coverings omitted | Coverings irrelevant to the issue | IUT I, Definition 3.1 |
| SS-S2 | 5 to 6 | Étale-like data `D` | `π₁(X)` up to inner automorphism; by [Anab3, Theorem 1.9] equivalent to curves (SS Theorem 7, Remark 9) | Anabelian full faithfulness makes group theory and geometry equivalent here | IUT I, Section 3 |
| SS-S3 | 5 to 6 | Frobenius-like data | `π₁(X)` acting on a monoid such as `k̄^×` or `o^▷`; Kummer theory makes the forgetful functor an equivalence on the essential image (except for `o^×`, "non-rigidity of the unit group portion") | Kummer rigidity | IUT I, Corollary 5.3, 6.12 |
| SS-S4 | 6 | A Θ^{±ell}NF-Hodge theater | A once-punctured elliptic curve abstractly isomorphic to `X`; claimed equivalence of categories (IUT I, Corollary 6.12 (i), Proposition 6.6 (iii), Corollary 5.6 (ii), Proposition 4.8 (ii), Definition 6.13) | This equivalence; M (Cmt2018-08 (C3)) says it is false as stated because it ignores the choices of `ℓ` and `V` | IUT I, Section 6 |
| SS-S5 | 6 to 7 | log-link | An endofunctor on topological fields isomorphic to `k̄_v`, naturally equivalent to the identity via `log : log(K) ≅ K` | Domain and codomain may be identified (M: (C6) of Cmt2018-05 says this is false) | IUT III, Definition 1.1 |
| SS-S6 | 7, footnote 8 | Full poly-isomorphisms | One chosen isomorphism; "obvious" isomorphisms `Π₁ = π₁(X) = Π₂`, `K₁ = k̄ = K₂` | Indeterminacy can be removed without loss (this is M's (SSInd)) | IUT III, Theorem 3.11 (i), (Ind1), (Ind2) |
| SS-S7 | 7 | Global realified Frobenioid | Ordered one-dimensional real vector space `ℝ_⊙ = (⊕_v ℝ_v)/D₀` with `γ_can` | None beyond [IUT I, Example 3.5] | IUT I, Example 3.5 |
| SS-S8 | 7 to 8 | `F^{⊩▶×μ}`-prime strip | `G_v ⟲ o^{×μ} × ℕ` at finite places plus a trivialized global realified Frobenioid; ×μ-Kummer structure ignored (footnote 9) | Kummer structure irrelevant | IUT II, Definition 4.9 |
| SS-S9 | 8 | Θ-pilot object, q-pilot object | "Abstract" pilot element `γ_pilot ∈ ℝ_⊙` versus "concrete" pilot objects `q̲_v`, `q̲_v^{j²}` in `o^▷_{k̄_v}`; the distinction is "ours" (footnote 10) | That IUT does not properly distinguish them (M: (C16), (C12) say it does) | IUT III, Definition 3.8 |
| SS-S10 | 9 | Θ-link | The full poly-isomorphism `F^{⊩▶×μ}_{Θ,1} ≅ F^{⊩▶×μ}_{q,2}`; "a canonical choice" exists since both are `G_v ⟲ o^{×μ} × ℕ` | The identity is admissible (this is M's (SSId); M: (SSIdFs)) | IUT III, Definition 3.8, Corollary 3.7 |
| SS-S11 | 9, footnote 12 | Theorem 3.11 | With identical copies identified along the identity, "does not become false, but trivial" | Same as SS-S6, SS-S10 | IUT III, Theorem 3.11 |

**SS-10 (page 8, Section 2.1.6).** Proposition: under the trivialization `γ_can ↦ 1`, the abstract pilot element maps to `(1/(2ℓ)) deg(q_E)`. Hypotheses: SS-S7, SS-S8. M (C11) agrees for q-pilots, says it does not coincide with arithmetic degree for Θ-pilots.

**SS-11 (pages 8 and 9, Section 2.1.8).** Proposition: the `j`-th concrete Θ-pilot divisor has degree `j²` times that of the q-pilot; the abstract Θ-pilot element encodes that degree "only when the identification `ℝ_{⊙,Θ} ≅ ℝ` is scaled by `j²`". M (C13), (C14) of Cmt2018-05 (which answer the May version, as quoted there) agree, reading `j²` as its average over `j`. M (C10) of Cmt2018-08 objects to "j-th concrete Θ-pilot object" as a term.

## Part 3. The central argument of Section 2.2

**SS-12 (page 9).** The rough outline of Step (xi): the Θ-link maps the abstract Θ-pilot of `HT₁` to the abstract q-pilot of `HT₂`; it "is argued" that Theorem 3.11 turns this, up to (Ind1, 2, 3), into an identification of concrete Θ- and q-pilot objects, "and then the inequality follows directly". IUT counterpart: Step (xi-a) to (xi-f), pages 181 to 184; Fig. 3.8, page 185.

**SS-13 (pages 9 and 10). The six copies of ℝ and the diagram.** The ordered one-dimensional real vector spaces are `ℝ_{⊙,Θ}`, `ℝ_{⊙,q}` (abstract pilot elements), `(ℝ_{⊙c,Θ_j})_{j=1..ℓ*}` and `ℝ_{⊙c,q}` (concrete pilot elements; the `Θ` vertex is really `ℓ*` spaces), and two copies `ℝ_Θ`, `ℝ_q` of the standard reals. Edges: `ℝ_{⊙,Θ} → ℝ_{⊙,q}` (Θ-link), `ℝ_{⊙,Θ} → ℝ_{⊙c,Θ_j} → ℝ_Θ`, `ℝ_{⊙,q} → ℝ_{⊙c,q} → ℝ_q`, and `ℝ_Θ = ℝ_q`. "In order for a meaningful inequality to be concluded, one must consistently identify all of these."
Proposition (formalized under (Lin)): if every edge is multiplication by a positive scalar, the diagram commutes if and only if the product of scalars around the cycle is `1`. Lean (existing): `Consistent`, `consistent_canonical` in `Diagram.lean`.
Hypotheses: (Lin), named so by M in Cmt2018-08 (C14), page 4, who accepts linear relations between the copies of `ℝ` arising via the Θ-link from the prime strips and denies them only for log-volumes of regions subject to indeterminacies (so the prime-strip level and the level of log-volumes under (Ind1, 2, 3) are distinct questions); and the claim that the proof of Corollary 3.12 requires such a cycle to commute (denied by M, Cmt2018-05 (C17) (N4)).

**SS-14 (page 10). The scalar `j²`.** With the canonical isomorphisms the diagram commutes but the abstract Θ-pilot does not encode the Θ-divisor's degree; inserting `j²` on the left gives monodromy `j²` (or its average). Proposition: under (Lin), one edge with scalar `s` and the rest canonical is consistent iff `s = 1`; for `s = j²`, `j ≥ 2`, inconsistent. Lean (existing): `scalar_eq_one_of_consistent`, `not_consistent_square`. New: with the averaged scalar, `avgSq ℓ* = ℓ(ℓ + 1)/12` for `ℓ* ≥ 1` and `ℓ = 2ℓ* + 1` (`avgSq_eq`).

**SS-15 (page 10). Conclusion.** "With consistent identifications of copies of real numbers, one must in (1.5) omit the scalars `j²` … which leads to an empty inequality." This combines SS-13, SS-14, SS-9. The step from "consistent identifications" to "(1.6) is what Corollary 3.12 gives" is not stated as a proposition in the manuscript; it is the disputed inference.

**SS-16 (page 10). The "blurring" remark.** M claimed on the last day that the diagram commutes up to the blurring of certain indeterminacies; SS: "this statement means that the blurring must be by a factor of at least `O(ℓ²)` rendering the inequality thus obtained useless". Three claims are kept apart. (i) Arithmetic, proved on the domain `ℓ* ≥ 1`, `ℓ = 2ℓ* + 1` and with no other hypothesis: the average of `j²` over `j = 1, …, ℓ*` is `ℓ(ℓ + 1)/12` (`avgSq_eq`), and, for `ℓ* ≥ 1`, (1.5) and (1.6) differ exactly by that factor on the `q` term (`withSquares_eq_withoutSquares_scaled`). The domain is needed: at `ℓ* = 0`, `ℓ = 1` the average is `0` (empty sum, Lean's convention `1/0 = 0`) while `ℓ(ℓ + 1)/12 = 1/6`. (ii) Under the assumed hypothesis (Lin) and the tolerance model of this project `ConsistentUpTo B` (product of scalars around the cycle in `[1/B, B]`), a cycle with the averaged scalar on one edge closes up to `B` exactly when `1/B ≤ ℓ(ℓ + 1)/12 ≤ B` (`consistentUpTo_avgSq_iff`, from `blur_bound`); the bound on `B` is the tolerance hypothesis evaluated, not a consequence of other premises. (iii) M, Cmt2018-08 (C14), page 4, accepts linear relations between the copies of `ℝ` arising via the Θ-link from the prime strips, but denies linearity for log-volumes of regions subject to indeterminacies; (LVEx) is a nonlinear example in the plane, not a construction of the comparison in Corollary 3.12. Assessment: the "useless" part is a quantitative inference about how such a blurring would enter (1.4); SS do not write that computation out, and this project does not supply it (obligation OB-BLUR-QUANT in `data/dispute_map.json`).

## Table: objection, response, obligation

Columns: **Def** = do the two sides use equivalent definitions; **Kind** = disagreement about a mathematical statement (Stmt) or its interpretation (Interp); **Resolving hypothesis**; **Established?** in IUT I to IV; **Obligation** for a formalization of IUT III, Corollary 3.12. All entries in the last four columns are this project's assessment. Details in `data/dispute_map.json`.

| Objection | Response | Def | Kind | Resolving hypothesis | Established? | Obligation |
|---|---|---|---|---|---|---|
| SS-5, SS-3 (Remark 5) | Cmt-08 (C1) | partly: M's argument concerns `j`-invariants (moduli values), SS's statement concerns curves `E/k` as above | method disputed; the statements differ in what is counted | none needed (`N ≥ 0` suffices) | not needed | OB-RED (done here, real analysis only) |
| SS-S4 (Hodge theater ≃ curve) | Cmt-08 (C3), Cmt-05 (C3), (T3) | no: SS ignore `ℓ`, `V` | Stmt | The equivalence with `ℓ`, `V` included | not checked for this document | OB-HT |
| SS-S5 (log-link as endofunctor) | Cmt-05 (C6), (LbLp), (Lblog) | no | Stmt (invariance of Θ-link under identifying log-link ends) | Invariance (Q3) or its negation | asserted by M (Rpt §14 to §15), not proved in a checked form | OB-LOG |
| SS-S6, footnote 8 (poly-isomorphisms) | (SSInd), (PMQut), (PMEss), Cmt-05 (C7) | no | Stmt | Theorem 3.11 with (Ind1), (Ind2) removed is false or trivial | IUT III Theorem 3.11 (i) introduces them; necessity asserted, not proved as a statement | OB-IND |
| SS-S9, footnote 10 (abstract vs concrete) | Cmt-05 (C16), Cmt-08 (C12), (LbLV) | no: M identifies "concrete realizations" with hol. structures | Interp | A precise definition of the "relevant Kummer isomorphisms" and of `−|log(Θ)|` as a function of initial Θ-data | defined in IUT III Corollary 3.12 statement, page 173 to 174, in terms not yet formalized | OB-DEF |
| SS-S10, footnote 12 (canonical Θ-link, id-version) | (SSId), (SSIdFs), (†ΘCR), (SSIdEx), (ModEll), Cmt-05 (C15), Cmt-08 (C13) | no | Stmt: is Theorem 3.11 applicable to the id-version? | (ΘCR): Theorem 3.11 needs value and unit group portions from one ring structure | asserted in Rpt §9 to §10; the hypotheses of Theorem 3.11 would decide it | OB-311-HYP |
| SS-13 (consistent identification of copies of ℝ) | Cmt-05 (C17) (N1) to (N5), (C18) | no | Interp of Step (xi) | Step (xi) compares regions inside one container with one log-volume; no cycle | asserted (Cmt-05 (C17)); Step (xi-d) page 183 describes one container `1,◦U^Q` | OB-XI-CONTAINER |
| SS-14 (monodromy `j²`) | (AD), (IUAD), (LbEx1), (Smm) | partly: both accept (AD) | Interp: is the loop formed? | Distinct labels for hol. structures (Γ_seg vs Γ_loop) | (IUAD) says no dispute about (AD) | OB-XI-CONTAINER |
| SS-15 ((1.6), not (1.5)) | (SSAD)/(SSADFs), Cmt-08 (C14) (Lin), (MlLV) | no | Stmt | Whether log-volume of the hull relates non-linearly to the Θ-pilot's | (Ind3) inequality: IUT III Theorem 3.11 (ii), Proposition 3.9; not checked here | OB-XI-F |
| SS-16 (blurring `O(ℓ²)`) | (MlLV), (LVEx), (DsInd), Cmt-08 (C14) | no | Stmt about size and form of the effect of indeterminacies | Quantitative bound on the effect of (Ind1, 2, 3) on log-volume, and a computation of how a blurring of that size enters (1.4) | IUT IV Proposition 1.2 and Theorem 1.10 (not read for this document) | OB-IND-SIZE, OB-BLUR-QUANT |
| SS excuses (2) to (4) | Cmt-05 (C2) to (C4), (T7), (T8) | n/a | about the discussion, not mathematics | none | n/a | none |

## What the Lean files in `IUT/Audit/ScholzeStix/` prove

* `Section1_3.lean`: displays (1.5), (1.6) and their consequences.
* `Diagram.lean`: consistency of a cycle of positive scalars under (Lin), the `j²` case.
* `Reduction.lean`: SS-5.
* `Blurring.lean`: SS-14 averaged, SS-16 under (Lin) and a chosen tolerance model, and the exact relation between (1.5) and (1.6).

None of these settles the dispute: every disputed step enters as a hypothesis or lies outside the files.

`IUT/Audit/LANA/EtaGoal.lean` is a related model outside `IUT/Audit/ScholzeStix/`: a third
party's isolation of the step from Theorem 3.11 to Corollary 3.12 (the LANA interim report), in
a simplified setting and not a statement of the papers. It types the report's main goal as a
schema with the action as data (`lanaEtaGoalFor`), and its model of issue 2 of the report's
repository is the non-commutativity of the hexagon of Scholze and Stix in that setting
(`lana_issue2_model`).
