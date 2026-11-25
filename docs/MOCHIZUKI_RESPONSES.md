# Mochizuki's responses to Scholze and Stix: items, propositions, hypotheses

This document lists Mochizuki's responses as numbered items with source and page, and states each as a precise proposition where one can be stated. The objections they answer are in `docs/SCHOLZE_STIX_ANALYSIS.md`; the mapping is in `data/dispute_map.json` and in the table at the end.

Layers: **M** is what Mochizuki says; **SS** is what Scholze and Stix say; **Assessment** is the view of this project. Neither party's standing is evidence. No winner is declared.

## Sources

* **Rpt** = *Report on Discussions, Held During the Period March 15 to 20, 2018, Concerning Inter-universal Teichmüller Theory (IUTch)*, `Rpt2018.pdf` from <https://www.kurims.kyoto-u.ac.jp/~motizuki/> (SHA-256 in `data/dispute_map.json`), 45 pages, title page dated February 2019. Read in full. Pages 2, 17, 18, 24, 25 checked against renders.
* **Cmt-05** = *Comments on the Manuscript by Scholze–Stix Concerning IUTch*, July 2018, `Cmt2018-05.pdf`, 8 pages, read in full. It answers the May 2018 version of the manuscript, which is not available here; text of that version is known only through Cmt-05's quotations, which this document attributes to Cmt-05, not to the manuscript. Its references to footnotes and remarks use that version's numbering.
* **Cmt-08** = *Comments on the Manuscript (2018-08 Version) by Scholze–Stix*, September 2018, `Cmt2018-08.pdf`, 5 pages, read in full. Its references match the July 16, 2018 file used here.
* IUT III, May 2020 manuscript, pages 173, 174, 180 to 195.

## Part 1. Comments on the May 2018 version (Cmt-05)

The May 2018 version of the manuscript is not among the available sources. Phrases of it quoted in this part are quoted as Cmt-05 gives them; they are attributed to Cmt-05, not to the manuscript.

| Item | Page | Target in SS | Content (paraphrase) | Proposition, where one can be stated |
|---|---|---|---|---|
| (C1) | 1 | title, Section 1 | SS give no proofs of negative claims; key IUT notions (multiradial, log-shell, tensor packet, procession, (Ind1, 2, 3)) are absent; the main assertion is at the end of Section 1 (top of page 4). | None (procedural). |
| (C2) | 1 to 2 | 2.1 (2) | Whether a simplification obscures depends on the aspect; M did not agree that SS understood the substantial content. | None (about the discussion). |
| (C3) | 2 | 2.1 (3) | "Inessential to the point we are making" is "completely false"; see Rpt. | Points to (SSId), (SSIdFs). |
| (C4) | 2 | 2.1 (4) | "The issue will prevail" is false and not a proof. | None. |
| (C5) | 2 to 3 | Remark 8 (now 9) | Étale-like structures matter through their symmetry within the log-theta-lattice. (Q1): the log-theta-lattice has no automorphism permuting the 0- and 1-columns. (Q2): its étale-like portion does. | P-Q1: no automorphism of the portion Γ_main of the log-theta-lattice swaps the 0- and 1-columns. P-Q2: the étale-like portion admits such a swap. Both are (LbMn), (EtMn). |
| (C6) | 3 to 4 | 2.1.3 | Identifying domain and codomain of the log-link forces identifying the Θ-links from both ends, incompatible with the definition of the Θ-link, which fixes multiplicative structures. (Q3): can SS prove invariance of the Θ-link under that identification? | P-Q3 (M asserts its negation): the Θ-link is not invariant under identifying the Θ-links emanating from the domain and codomain of a log-link. |
| (C7) | 4 | footnote 5 (now 8) | Rigidifying the Π's in a column depends on Frobenius-like data that has no 0/1 switching symmetry; as abstract groups they admit it. | Same as P-Q1, P-Q2. |
| (C8) | 4 | 2.1.4 | `γ_v`, `γ_can` exist but are canonical only when the Frobenioid comes from an `F^{×μ}`-prime strip. Addressed in SS2018-08 per Cmt-08 (C5). | Agreement after revision. |
| (C9) | 4 to 5 | 2.1.5 | Two minor errors (generator from `o^▷`, `Ẑ` for `Z`). Addressed per Cmt-08 (C6). | Agreement after revision. |
| (C10) | 5 | 2.1.6 | `v(q̲_v)` should be `v(q̲_v)·γ_v`; only bad places. Addressed per Cmt-08 (C8). | Agreement after revision. |
| (C11) | 5 | 2.1.6 | The isomorphism `ℝ_⊙ ≅ ℝ`, `γ_can ↦ 1`, equals arithmetic degree for q-pilots, not for Θ-pilots. | Agrees with SS-10, SS-11. |
| (C12) | 5 | 2.1.7 | For q-pilots that isomorphism is the usual arithmetic degree. | Agreement. |
| (C13) | 5 | 2.1.8 | "`j²`" should be read as the average of the `j²`. | Agreement up to averaging. |
| (C14) | 5 | 2.1.8 | For Θ-pilots, that isomorphism scaled by the average of `j²` is the arithmetic degree. | Agreement with SS-11. |
| (C15) | 5 | 2.1.9 | The "canonical choice" of Θ-link is the id-version (SSId); Theorem 3.11 cannot be applied to it (SSIdFs). | See (SSIdFs). |
| (C16) | 5 to 6 | footnote 7 (now 10) | Distinguishing abstract pilot objects from their concrete multiradial representations on tensor packets of log-shells is central to IUT (Theorem 3.11, Corollary 3.12); SS confuse them. | None as a proposition; a claim about the papers. |
| (C17) | 6 | 2.2 | Section 2.2 misrepresents Step (xi). None of (N1) "careful identifications of copies of reals", (N2) "consistently identifying", (N3) identifying `ℝ_Θ` and `ℝ_q`, (N4) a loop required to commute, (N5) "introducing scalars `j²`" occurs in Step (xi). The loop is the erroneous identification of labels or ring structures. IUT keeps the ring structures distinct and computes their relation by embedding objects into a common container with one log-volume function, so no loop needs to commute. | P-N4: the proof of Corollary 3.12 compares log-volumes of subsets of one container, so no commutativity of a cycle of identifications is used. |
| (C18) | 7 | 2.2 | The argument of 2.2 is a "superficial internal contradiction" of a modified version obtained by identifying ring structures on both sides of the Θ-link; such contradictions differ in kind from a gap. | (GLR1), (GLR2). |

## Part 2. Comments on the 2018-08 version (Cmt-08)

| Item | Page | Target | Content | Proposition |
|---|---|---|---|---|
| (C1) | 1 to 2 | Remark 5 | The finiteness follows from elementary height theory: the `j`-invariant (times a suitable integer depending on `d`, `b`) satisfies a monic integer polynomial of degree `d` with bounded coefficients; not Faltings. Also the discriminant of `k/ℚ` must be bounded for the Faltings route. | Two propositions, to be kept apart. P-R5j (moduli values): for fixed `d`, `b`, the `j`-invariants of degree at most `d` and height at most `b` form a finite set; this is Northcott's theorem, and it is what M's argument establishes. P-R5E (curves, SS's Remark 5): for fixed `d`, `b`, finitely many `E/k` corresponding to `P ∈ M_ell(k)` **as above** (the restrictions (1) to (3) of SS Section 1.2) with `[k:ℚ] ≤ d`, `h(P) ≤ b`. P-R5j does not imply P-R5E without further argument, since infinitely many quadratic twists over `ℚ` share one `j`-invariant; P-R5E, and finiteness of the fibers of the Weil restriction, need their own argument from the restrictions "as above", not checked here. Assessment: the reduction SS-5 needs neither; it uses only `N ≥ 0` (`Reduction.lean`). |
| (C2) | 2 | 2.1 (3) | "explain" replaced by "convince"; refers to (T3), §10, (SSId), (SSIdFs), (SSIdEx), (ModEll). | See those. |
| (C3) | 2 | 2.1.2 | The claimed equivalence of categories (Hodge theaters ≃ the one-object category of `X`) is false as stated: the choices of `ℓ` and `V` are ignored. "Not such a central issue." | P-HT: the stated functor is not an equivalence without fixing `ℓ`, `V`. Not checked here. |
| (C4) | 2 | footnote 7 | The image of the `p`-adic logarithm is not in the maximal ideal already for sufficiently ramified finite extensions. Minor. | Standard fact; not disputed. |
| (C5), (C6), (C8) | 2 | 2.1.4 to 2.1.6 | Earlier comments addressed; misprint `k_V` for `k_v`. | Agreement. |
| (C7) | 2 | footnote 8 | "convincingly in our opinion" added; see Cmt-05 (C7). | As (C7). |
| (C9) | 2 to 3 | 2.1.8 | The revised passage (global `π₁(X)`, "tempered coverings of `X`") is less accurate; theta values are local at bad primes; tempered coverings are only local. | P-T: tempered coverings are defined only locally. Terminology. |
| (C10) | 3 | 2.1.8 | There is one concrete Θ-pilot object with `j`-th components, not a "`j`-th Θ-pilot object". | Terminology. |
| (C11) | 3 | 2.2 | Multiradial algorithm and tensor packets are now mentioned but still misunderstood. | None. |
| (C12) | 3 | footnote 10 | The q- and Θ-"concrete realizations" are exactly the q- and Θ-arithmetic holomorphic structures (the intertwining of value and unit group portions); the failure to distinguish arises because SS do not distinguish the holomorphic structures. See (LbLV). | Interpretive identification. |
| (C13) | 3 to 4 | footnote 12 | The simplifications are the id-version; then Theorem 3.11 cannot be applied (SSIdFs); see (SSIdEx), (ModEll), (HstMod). | See (SSIdFs). |
| (C14) | 4 | 2.2 | SS's argument rests on **(Lin)**: every relationship between two of the copies of `ℝ` is multiplication by a positive scalar. (Lin) is false as a statement about all the copies: such linear relations do exist between copies of `ℝ` arising (via the Θ-link) from `F^{×μ}`-prime strips, but where indeterminacies are involved, as for the multiradial representation of the Θ-pilot, the relation between log-volumes of regions with and without indeterminacies is "highly non-linear" and depends on the region. See (MlLV), (LVEx), (DsInd). | P-Lin-neg: the map from the log-volume of the Θ-pilot in its own holomorphic structure to the log-volume of the holomorphic hull of its multiradial representation is not of the form `x ↦ c x`. Two levels are distinguished: linearity of the link at the level of prime strips (accepted by M) and linearity of log-volume under the indeterminacies (denied by M). |

## Part 3. Labeled assertions of the report (Rpt)

Every labeled item was read. Items are grouped; page numbers refer to the February 2019 version.

### 3.1 Summary and general logic (pages 1 to 4)

* **(Smm)** (page 2). Positive reals `A`, `B` with `−2B = −A` (the Θ-link) and a theorem `−2B ≤ −2A + 1` (the multiradial representation) give `A ≤ 1` (Corollary 3.12). Assuming `A = B` forces `A = B = 0`, contradicting positivity; M says this is SS's error. Proposition and proof: `IUT.Audit.MochizukiResponses.ToyModels.smm_bound`, `smm_identify`, `smm_contradiction`. Assessment: the "theorem" is a hypothesis of the model.
* **(GLR1), (GLR2)** (page 3). Identifying objects that must be distinct yields contradictions that show the objects are distinct, not that the original argument is flawed. A general logical remark; true as stated, and its application to IUT is what is disputed.
* **(T1) to (T9)** (pages 5 to 6). Themes: histories, species, the id-version, poly-morphisms, labels, refusal to consider distinct holomorphic structures, simplification, misinterpreted statements, exposition of Theorem 3.11. (T9): SS did not dispute the validity of the algorithms of Theorem 3.11, but their non-triviality.

### 3.2 Histories, re-initialization, symmetry (pages 6 to 11)

* **(H1), (H2)** (page 6 to 7). Conventional single history versus histories with re-initialization requiring labels.
* **(HEx1), (HEx2-1), (HEx2-2)** (pages 7 to 8). In the log-link the Π's are known only as abstract topological groups; in the Θ-link the G's as abstract groups and the `O^{×μ}`'s as abstract monoids with submodules; the full poly-isomorphism gives (Ind1, 2).
* **(HC1), (HC2)** (pages 8 to 9). Classical analogues: Teichmüller theory, anabelian geometry.
* **(SSInd)** (page 9). M's statement of SS's position: the essential content (for example multiradial algorithms) is unaffected if (Ind1, 2) are eliminated. Proposition (attributed to SS): Theorem 3.11 remains valid and nontrivial with (Ind1), (Ind2) removed. M asserts it is false.
* **(SW), (Sym)** (page 9). Multiradiality is invariance up to indeterminacy under switching data in domain and codomain of the Θ-link; forgetting structure enables symmetry.
* **(SWC1), (SWC2)** (page 10). Elementary examples: forgetting the order on `{0,1}` gives `S₂` symmetry; forgetting atlases.
* **(SWE1), (SWE2)** (pages 11). Ring structures around the log-link and the Θ-link obstruct switching symmetry; forgetting them gives (Ind1, 2).

### 3.3 The Θ-link and ring structures (pages 11 to 15)

* **(ΘNR), (ΘNR1 to 3)** (page 12). The Θ-link `{q^{j²}}^ℕ · O^{×μ} ≅ q^ℕ · O^{×μ}` (with `G`) is not compatible with the ring structures (additive, multiplicative, Galois) on either side. Proposition: there is no ring isomorphism compatible with the Θ-link gluing. Both sides agree (compare SS-S10 and (IUAD)).
* **(GIUT)** (page 12). The goal is to compute the Θ-holomorphic structure in terms of the q-holomorphic structure.
* **(ΘCR), (ΘCR1), (ΘCR2)** (page 12). The Θ-link is compatible with the largest possible portion of the ring structures: the monoid subquotients and `G` acting on them. These ring structures are needed to define the log-links used in Theorem 3.11.
* **(VUSQ)** (page 13). The splitting into value group and unit group portions is a property of the monoids; the whole monoid is a subquotient of one multiplicative monoid `k^×`.
* **(VUC1)** (page 13). With the identity isomorphism `⁰O^{×μ} ≅ ¹O^{×μ}` and `{⁰q^{j²}} ↦ ¹q`, the induced identity `⁰k ≅ ¹k` does not map `⁰q^{j²}` to `¹q` for `j ≥ 2`. Proposition: under the identity of fields, `q^{j²} ≠ q` for `j ≥ 2` (elementary).
* **(VUC2)** (page 13 to 14). Removing the incompatibility by placing the value group portions in other, unrelated copies of `k`; not IUT's approach.
* **(VUC3)** (page 14). IUT's approach: the full poly-isomorphism of the single subquotients.
* **(RLFU)** (pages 14 to 15). A construction of a `p`-adic field `†K` functorial in `(†W, α : †W ≅ W_K)`, from `U_K = 1 + p²O_K`. Proposition: the construction recovers `K` from `W_K` with a given isomorphism. Assessment: as stated, with the isomorphism `α` given, it is a transport of structure; not formalized.

### 3.4 The id-version (pages 15 to 20)

* **(SSId)** (page 15). M's statement of SS's assertion on the last day: Theorem 3.11 can relate the Θ- and q-holomorphic structures in the id-version, where the identity on `G ⟲ O^{×μ}` is used and the value-group monoids come from ring structures `†Θ`, `†q` declared unrelated.
* **(SSId1), (SSId2)** (page 16). SS introduced the separation to secure (SW); motivated by the belief that value and unit group portions are treated independently.
* **(†ΘCR)** (page 16). Theorem 3.11 may only relate the value group portion of `†Θ` to another structure through data containing the `G ⟲ O^{×μ}` of `†Θ` itself; it cannot be applied with the rigidified portion of (SSId).
* **(SSIdFs)** (page 16). Hence (SSId) is false. Proposition: Theorem 3.11 is not applicable to the id-version. Assessment: this is a statement about the hypotheses of Theorem 3.11 and would be decided by a precise statement of those hypotheses.
* **(SSIdEx)** (pages 17 to 19). Two complex structures on `ℝ²` (`U`: `i e₁ = e₂`; `W`: `i e₁ = t e₂`, `0 < t < 1`); (≇) the data with `ι_U`, `ι_W` are not isomorphic; (Dilat) replacing `φ = id` by `(φ₁)_ℂ` loses the nonzero dilatation. Formalized in `IUT/Audit/MochizukiResponses/SSIdEx.lean`: `not_iso_of_ne_one`, `iso_of_eq_one`, `φcoord_eq`, `beltrami` (μ = (t − 1)/(t + 1)), `dilatation` (K = 1/t). Assessment: the example is correct. Its relevance rests on the asserted correspondence (V₁ ↔ unit group portion, V₂ ↔ value group portion, U ↔ q-hol. str., W ↔ Θ-hol. str.), which is not a mathematical statement that the example proves.
* **(ModEll), (HolMod), (TchMod)** (pages 19 to 20). The same example as holomorphic moduli (`ℂ/(ℤ + ℤτ)`, `τ = t⁻¹ i`) versus Teichmüller moduli (fixed lattice, varying structure); (HolMod) ↔ [Φ] ↔ id-version, (TchMod) ↔ Φ ↔ Θ-link. Proposition: the structure `i(1,0) = (0,t)` corresponds to `τ = t⁻¹ i`. Consistent with `ζW` in `SSIdEx.lean` (`e₂ ↦ i/t`).
* **(HstMod)** (page 20). Historical remark.

### 3.5 Global nature (pages 20 to 22)

* **(ΘFrd)** (page 21). The Θ-link contains global realified Frobenioids; Theorem 3.11 and the inequalities are global.
* **(ΘInd)** (page 21). The compatibility with `{q^{j²}} ↦ q` cannot come from automorphisms in (Ind1, 2) permuting `exp(q^{j²})` and `exp(q)`; such automorphisms do not exist in general. Assessment: this is a point of agreement with SS on what local indeterminacies cannot do.
* **(UnEx1), (UnEx2), (UnEx3)** (pages 21 to 22). Non-isomorphic structures with isomorphic underlying objects: Riemann surfaces, groups of order four, `p`-adic fields with isomorphic absolute Galois groups ([Ymgt]). All standard.

### 3.6 Arithmetic degrees and labels (pages 22 to 26)

* **(AD)** (page 22). Within one holomorphic structure, `{q^{j²}} ↦ q` is incompatible with arithmetic degrees unless degrees are taken up to factors `j²`, which makes them meaningless. Proposition (both agree): in one ring structure, `deg(q^{j²}) = j² deg(q) ≠ deg(q)` for `j ≥ 2`.
* **(IUAD)** (page 22). "There is absolutely no dispute" about (AD); it is the starting point of IUT, which is why the two holomorphic structures are kept distinct.
* **(ADItw)** (page 23). Degree computations depend on the intertwining of value and unit group portions, which comes from the ring structures; the Θ-link is not compatible with them.
* **(SSAD)** (page 23). M's statement of an SS assertion: the contradiction of (AD) occurs even without (SSId), using Theorem 3.11 as stated.
* **(SSADFs)** (page 23). (SSAD) is false: the contradiction only occurs when the holomorphic structures on the two sides are identified. This is the core disagreement about Step (xi).
* **(SSDLFs)** (page 23). Deleting labels identifies the holomorphic structures, which is stronger than (SSInd), (SSId).
* **(LbLV)** (pages 23 to 24). Labels are markers saying whether the pilot value-group generator is identified with the log-volume of `q` (q-hol. str.) or of `{q^{j²}}` (Θ-hol. str.). Refers to the toy models of IUT III Remark 3.12.2 (ii).
* **(MlLV)** (page 24). The Θ-link gives a linear relation between copies of `ℝ`; the computation via Theorem 3.11 of the log-volume of the Θ-pilot in the q-hol. str. involves indeterminacies giving a highly non-linear relation between the Θ-pilot's log-volume and that of its multiradial representation.
* **(LVEx)** (pages 24 to 26). `R_{a,b}`, `S_{a,b} = R ∪ σR` in `ℝ²`; `μ^log(S) = log(4a + 4b) > μ^log(R) = log(4a + 2b)`; the ratio varies with `(a, b)`; with `μ^log(S) > 0 > λ > μ^log(R)`, `ρ = μ^log(R)/λ > 1`, gluing `x ↦ x/ρ`, and `μ^log(S) > λ`. Correspondence: `R` ↔ Θ-pilot in Θ-hol. str., `S` ↔ holomorphic hull of the multiradial representation, `R_λ` ↔ q-pilot, the gluing ↔ Θ-link. Formalized: areas from Lebesgue measure (`LVExMeasure.lean`: `volume_R`, `volume_S`, `σ_S`, `σ_R_ne`, `admissible_exists`, `gluing`), non-linearity (`LVEx.lean`: `not_linear`, `not_affine_shift`). The log-volume `μlog` is meaningful on sets of finite positive measure (both regions, for `a, b > 0`); elsewhere it is `0` by totalization. Assessment: the inequality `μ^log(S) > λ` follows from the hypotheses `μ^log(S) > 0 > λ` alone (`logVolS_gt_lambda`), so the third conjunct of `gluing` adds no evidence about the gluing; the example illustrates consistency rather than deriving it. It refutes (Lin) for the pair (rigid region, symmetrized hull). Whether the pair of log-volumes in Step (xi) behaves this way is not decided by the example.
* **(PMInd), (PMEx1), (PMEx2), (PMTrv), (PMQut), (PMEss)** (pages 26 to 27). Poly-morphisms are common (homotopy classes, derived categories); IUT's are not single maps between quotient sets; they produce the symmetries underlying multiradiality.
* **(LbRl), (LbEx1) to (LbEx6), (DfLb)** (pages 28 to 32). Labels distinguish copies. (LbEx1): segment versus loop graph, monodromy; the incompatibility (AD) is monodromy around the loop obtained by identifying the two ends of the Θ-link. (LbEx2): localization `A_f` as a colimit needs a base label. (LbEx3): colimit of `F_p[t]` under Frobenius without labels. (LbEx4): `ℚ(∛2)` and `ℚ(ω∛2)`. (LbEx5): manifolds. (LbEx6): the id-version itself uses labels; identifying them yields the (VUC1) contradiction unless exponents of `q` are taken up to `j²`. (DfLb): "remembering" without explicit labeling risks non-equivalent structures. Assessment: (LbEx3) is correct as stated: the colimit of the one-object diagram `A` with endomorphism `φ` is the coequalizer of `id` and `φ`, namely `F_p[t]/(t^p − t) ≅ F_p^p` by the Chinese remainder theorem, whereas the ℤ-indexed system gives the perfection. Not formalized.
* **(LbHT)** (page 32). Labels for evaluation points inside one Hodge theater.

### 3.7 Symmetries of the log-theta-lattice (pages 33 to 36)

* **(LbLp)** (pages 33 to 34). Γ_ℤ, Γ₀, Γ_loop: forgetting vertical labels replaces the simply connected Γ₀ by a loop.
* **(LbΘ)** (page 34). No Θ-link admits a symmetry swapping domain and codomain: there are no field automorphisms `α, β` with `α(q^{j²}) = q`, `β(q) = q^{j²}` up to roots of unity. Proposition: elementary via valuations (`v(α(x)) = v(x)` for continuous automorphisms) for `j ≥ 2`. Not formalized.
* **(Lblog)** (page 35). No log-link admits such a symmetry.
* **(LbMn)** (page 35). Γ_main has no symmetry swapping the 0- and 1-columns.
* **(EtFr), (EtFrEx)** (page 35 to 36). Étale-like objects on opposite sides are related by isomorphisms; Frobenius on `F_p(t)` induces `Aut(F) ≅ Aut(F)`.
* **(EtΘ), (Etlog), (EtMn)** (page 36). The G's and Π's as abstract groups can be permuted; the diagram `Π ↠ G ↞ Π` admits the swap.

### 3.8 Classical analogies (pages 37 to 41)

* **(DsGl)** (page 37). Discomfort with `{q^{j²}}^ℕ ≅ q^ℕ`.
* **(GlMt), (DFL), (DiIsm), (MAT1) to (MAT4)** (pages 37 to 38). Isogeny invariance of heights: `q ↦ q^l` is a dilation of degrees and an isometry of `dlog q`.
* **(MlCr1), (MlCr2), (MlCrH1), (MlCrH2)** (pages 38 to 39). Crystals and thickenings.
* **(SLZR)** (page 39). `[[1, m], [0, 1]]` are conjugate in `SL₂(ℝ)` but not in `SL₂(ℤ)` for distinct positive `m`. Standard and elementary.
* **(BgCp), (Chrn), (LkDt), (Bg1), (Bg2), (BgIUT1), (BgIUT2)** (pages 39 to 41). Bogomolov's proof of geometric Szpiro as an analogue.
* **(DsInd)** (page 41). Bogomolov's displacement estimates as a further example of sizing a region subject to indeterminacies that approximates a rigid region from above.

### 3.9 Conclusions (pages 41 to 44)

* **(FM1), (FM2), (FM3)** (pages 41 to 42). The misunderstandings: re-initialization and poly-morphisms; labels; (FM3) value and unit group portions in the domain of the Θ-link must come from one ring structure to apply Theorem 3.11.
* **(MVEx)** (page 42). Modified versions as exercises.
* **(Vrf1), (Vrf2), (CMA), (DfMth), (PCM1) to (PCM3)** (pages 42 to 44). Statements about verification by others, about how conspicuous the alleged flaws are, and about causes of misunderstanding. Not mathematical; not used as evidence.

## Part 4. IUT III passages cited by the responses

* **Corollary 3.12, Step (xi)** (pages 181 to 185). (xi-a): the Θ-link as a gluing of holomorphic structures sending the Θ-pilot at (0,0) to the q-pilot at (1,0). (xi-b), (xi-c): Theorem 3.11 yields possibilities of output data in `1,◦U` related by (IPL) to the q-pilot and expressible in the 1-column holomorphic structure (SHE). (xi-d): holomorphic hulls and log-volumes give `ℝ_{≤ −|log(Θ)|}` and `−|log(q)|`. (xi-e), (xi-f): the construction of `ℝ_{≤ −|log(Θ)|}` is a construction (up to approximation) of the input pilot log-volume, so `−|log(q)| ∈ ℝ_{≤ −|log(Θ)|}` and the inequality "follows formally". Formal last step: `ToyModels.stepXIf_formal`.
* **Remark 3.12.2 (ii), (a^itw) to (f^itw), (a^toy) to (f^toy)** (pages 187 to 191). The q- and Θ-intertwinings hold simultaneously because the holomorphic structures are distinguished; the toy model with `∗ ↦ −h`, `∗ ↦ −2h`, `∗ ↦ ℝ_{≤ −2h + ε}` and the conclusion `h ≤ ε`. Formalized in `ToyModels.lean`. Assessment: the step that carries content in the toy model is the supposition (e^toy) that `λ^Ind_Θ` can be constructed from the structure of `λ_q` even after identifying the copies of `ℝ`. In Step (xi) its analogue is (xi-e), (xi-f). This is precisely where SS locate the problem (SS-15), so the toy model restates the disputed step in a simpler setting rather than settling it.
* **Fig. 3.9** (page 193). Multiradiality holds for Θ-pilots, not q-pilots; in the 1-column log-volumes give equalities, in the 0-column (Ind3) gives upper bounds.

## Table: response to objection to obligation

All entries in the last four columns are this project's assessment.

| Response | Objection answered | Same definitions? | Statement or interpretation | Hypothesis that would resolve it | In IUT I to IV? | Obligation |
|---|---|---|---|---|---|---|
| Cmt-08 (C1) | SS Remark 5 | partly: `j`-invariants versus curves | method, and what is counted | none for the reduction | n/a | OB-RED |
| Cmt-08 (C3) | SS-S4 | no | statement | equivalence with `ℓ`, `V` fixed | not checked | OB-HT |
| Cmt-05 (C6), (LbLp), (Lblog) | SS-S5 | no | statement (Q3) | non-invariance of the Θ-link | asserted, Rpt §15 | OB-LOG |
| (SSInd), (PMEss), Cmt-05 (C7) | SS-S6 | no | statement | Theorem 3.11 fails or trivializes without (Ind1, 2) | asserted | OB-IND |
| Cmt-05 (C16), Cmt-08 (C12), (LbLV) | SS-S9 | no | interpretation | formal definition of `−|log(Θ)|` from initial Θ-data | defined in prose, IUT III pages 173 to 174 | OB-DEF |
| (SSId), (SSIdFs), (†ΘCR), (SSIdEx), (ModEll), Cmt-05 (C15), Cmt-08 (C13) | SS-S10, SS-S11 | no | statement | (ΘCR) as a stated hypothesis of Theorem 3.11 | asserted in Rpt §9, §10 | OB-311-HYP |
| Cmt-05 (C17) (N1) to (N5), (C18) | SS-13 | no | interpretation of Step (xi) | single container with one log-volume | Step (xi-d), page 183, asserts it | OB-XI-CONTAINER |
| (AD), (IUAD), (LbEx1), (Smm) | SS-14 | partly | interpretation | distinct labels for the two holomorphic structures | IUT III Step (xi-a), Remark 3.12.2 (c^itw) | OB-XI-CONTAINER |
| (SSADFs), Cmt-08 (C14), (MlLV) | SS-15 | no | statement | non-linear (non-(Lin)) relation via (Ind1, 2, 3) between the two log-volumes | Theorem 3.11 (ii), Proposition 3.9; not verified here | OB-XI-F |
| (LVEx), (DsInd) | SS-16 | no | statement | quantitative size of the indeterminacies on log-volumes, and how a blurring of that size enters (1.4) | IUT IV, Proposition 1.2, Theorem 1.10 (not read here) | OB-IND-SIZE, OB-BLUR-QUANT |
| Remark 3.12.2 toy models | SS-12, SS-15 | n/a | restates the disputed step | (e^toy) for the real objects | asserted as (xi-e), (xi-f) | OB-XI-F |

## Lean modules for this document

* `IUT/Audit/MochizukiResponses/LVEx.lean`: non-linearity from the stated areas.
* `IUT/Audit/MochizukiResponses/LVExMeasure.lean`: the areas from Lebesgue measure; the `λ`, `ρ` assertions.
* `IUT/Audit/MochizukiResponses/SSIdEx.lean`: the two complex structures, (≇), (Dilat).
* `IUT/Audit/MochizukiResponses/ToyModels.lean`: (Smm) and the toy model of Remark 3.12.2 (ii).

None settles the dispute: the disputed propositions (OB-311-HYP, OB-XI-CONTAINER, OB-XI-F, OB-IND-SIZE) are not formalized, because the objects they mention are not yet defined in Lean.
