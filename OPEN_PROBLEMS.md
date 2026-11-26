# Open problems

Every unresolved obligation of the project, grouped by kind. Each item gives an id, a precise
statement, the source page (manuscript pages, see `docs/SOURCE_MANIFEST.md`), a category, and
what would close it. The per-statement records in `data/curated/` carry the same obligations
in their `obligations` fields; counts are in [docs/DASHBOARD.md](docs/DASHBOARD.md).
Published claims bearing on these problems, with their stated status, are tabulated in docs/LITERATURE.md, Section 3.

The status `BLOCKED_BY_MISSING_JUSTIFICATION` used in `data/curated/` means: the text gives an assertion where a formalization needs a derivation; this is not a claim that the result is false.

The seven categories are kept apart:

1. failure of proof search;
2. missing library theorem;
3. gap in the formalization;
4. insufficient hypotheses;
5. counterexample to a simplified abstraction;
6. counterexample to a faithfully formalized statement;
7. demonstrated contradiction.

No item below is in category 6 or 7. The countermodels of `IUT/Countermodels/` are in
category 5: each refutes a simplified model of a step, not a statement of the papers
(`docs/COUNTERMODELS.md`). Category 4 means that the hypotheses written on the page do not by
themselves yield the step in a formalization. It does not mean that the step is false, and an
unstated hypothesis that holds is not an error in the paper.

## 0. Next stage: typed objects of the final comparison

Started: T-CMP has an abstract interface, `IUT.PaperIII.Corollary312.Comparison`. Its objects are inputs (an abstract region log-volume, required only to be monotone, a hull map with (P1) to (P3), a q-pilot region, a family of possible images), not the papers' objects. The logarithm of a measure is one instance of such a log-volume, but not the general case: the weighted packet log-volume of pages 95 to 97 and 115 to 117 is in general not the logarithm of a measure on the original product, and the weights of Rem 3.1.1 (ii), page 94, already divide by the local degree. The interface omits the construction of every region from initial Θ-data, the generation of the possible images by (Ind1), (Ind2), (Ind3) (they are an arbitrary indexed family), the tensor packets and the procession structure (only an equal-weight average over labels), the sum over places, the normalization of the integral structure (it enters only as the sign of the q-pilot log-volume), and the identification of the two sides through the link (both regions are placed in one space with one log-volume by the typing). It states the comparison directly against the hull of the union of the possible images, as a log-volume inequality (`LogVolumeComparison`) and as a region containment (`Containment`). Step (xi-f), page 184, asserts a numerical inclusion, which is the inequality form; containment of regions is a sufficient condition studied in the interface, not what the page asserts. It proves that containment together with a finiteness hypothesis gives the numerical conclusion (`conclusion_of_containment`), and gives examples on `ℝ` where the comparison holds, fails, and needs the hull of the union. T-HULL is started only on products of `p`-adic fields (see its row). T-PKT is started only on one finite-dimensional `ℚ_p`-vector space, on tensor packets of two factors, and on tensor packets over `ℚ_p` of finitely many factors (see its row). T-IMG is started only for (Ind3): `IUT.PaperIII.Corollary312.UpperSemiCompatibility` types (Ind3) in one reading of its nonarchimedean part, with abstract regions (`VerticalRegionFamily`, `UpperSemiCompatible`). T-ABC is started at the level of statements (`IUT/Applications/ABCSpecialization.lean`, `IUT/Applications/VojtaNumberField.lean`); the gap between it and IUT IV is T-GENELL.

The obligations of the next stage (`docs/ROADMAP.md`, stage 1a). Each is a typed statement to
be written in Lean, with the source it depends on and the smallest check that would show
progress. None is stated in Lean on the papers' objects yet.

| Id | Typed obligation | Source dependencies | Category | Smallest next check |
|---|---|---|---|---|
| T-PKT | A local tensor packet `log(^A F_{v_ℚ})` for one `v_ℚ` and a label set `A`, its integral structures and the maps between them as described on page 93, and the packet-normalized log-volume. | IUT III Prop 3.1, pages 92 to 99; Prop 3.9 (i), page 115; P-LOG | 2, 3 | Done in a model: on a finite-dimensional `ℚ_p`-vector space with the normalized log-volume of `IUT/Prerequisites/PadicVolume.lean`, the normalizing set has log-volume `0` (`padicMuLog_self`) and multiplication by `p` adds `−log p` (`padicMuLog_p_zpow_smul`); for one finite extension of `ℚ_p`, for tensor packets of two factors, and over `ℚ_p` for any finite number of factors (`Packets.lean`), the normalization of IUT IV Prop 1.4 (i) is proved (`volBridge_muLog_integralClosure`, `volBridge_packet_muLog_normalization`, `packet_muLog_normalization_tensor`). Open: the packets of page 93 with their integral structures, and the identification over `ℤ_p` beyond two factors. |
| T-IMG | The set of admissible images of a region under the group generated by (Ind1) and (Ind2), with the (Ind3) containments, defined by a formula. | IUT III Thm 3.11 (i), (ii), pages 154 to 156; A3 to A7 | 3, 4 | (Ind3) alone is typed in one reading (`UpperSemiCompatibility.lean`; see C3). State C2 (invariance of the normalized log-volume under the generated group) on T-PKT and T-IMG, then prove it or classify it. |
| T-HULL | The holomorphic hull of the union of admissible images on the packet. | IUT III Rem 3.9.5, page 127; Cor 3.12, pages 173 to 174 | 3 | Started on finite products of finite extensions of `ℚ_p` (`IUT/PaperIII/Corollary312/PacketHull.lean`: existence as the smallest `λ·O`, and (P1) to (P3) on a chosen domain). Open: tensor packets, `I^ℚ(−)`, the archimedean case and the union of admissible images. |
| T-CMP (started, interface only) | The comparison `−|log(q)| ≤ μ̄(hull of the union of admissible images of the Θ-pilot region)`, with finiteness of `−|log(Θ)|` as a separate conjunct, stated on T-PKT, T-IMG, T-HULL. | IUT III Cor 3.12, pages 173 to 174; Steps (xi-a) to (xi-f), pages 181 to 184 | 3, 4 | A kernel-checked proof that T-CMP implies the numerical statement of `Numerical.lean`; T-CMP itself stays open. |
| T-ABC (started, statements only) | IUT IV Theorem A specialized to an abc triple: the point `x = a/c` of `ℙ¹ \ {0, 1, ∞}`, its height, log-different and log-conductor in terms of `a`, `b`, `c`, and the implication from Theorem A (a named hypothesis) to `Challenge.ABCLog`. | IUT IV Thm A and Cor 2.3, pages 41 to 55; P-HT | 2, 3 | The smallest check is done: for a coprime triple the height (Mathlib's `Height.logHeight₁`) and conductor of `x = a/c` are `log c` and `rad(abc)` (`logHeight₁_of_triple`, `ratConductor_of_triple`), and the rational-point statement `VojtaLineMinusThreePointsRational` is proved equivalent to `Challenge.ABC` (`vojta_iff_ABC`). Over number fields, `IUT/Applications/VojtaNumberField.lean` states the bounded degree statement `VojtaLineMinusThreePointsBoundedDegree` (open), with the height, log-different and log-conductor of [GenEll] Definition 1.5 defined from Mathlib objects; its degree one piece is proved equivalent to `Challenge.ABC` (`degreeAtMostOne_iff_ABC`), so it implies `Challenge.ABC` (`abc_of_boundedDegree`). Open: the identification of the height of [GenEll] attached to `ω_X(D) = 𝒪(1)` with Mathlib's logarithmic height up to a bounded function (not formalized), and T-GENELL (the compactly bounded form is stated, OP-KV). The explicit comparison `|h(j(y)) − 6 h(y)| ≤ log 41 + 8 log 2` over number fields is a model test (`htCmp_abs_heightNF_legendreJ_sub_le`). |
| T-GENELL | The direction (ii) ⟹ (i) of [GenEll] Theorem 2.1. IUT IV, Corollary 2.3, derives (ii): the inequality on `ℙ¹_ℚ \ {0, 1, ∞}` for every `d` on compactly bounded subsets `K_V`. The rational-point statement of T-ABC is an instance of (i), which has no `K_V`. The proof of (ii) ⟹ (i) passes to a finite étale covering, which raises the degree bound to `d · deg(Y/X)`, and uses points of bounded degree over number fields and a noncritical Belyi map ([Mzk1] Theorem 2.5). On the reading of page 12 recorded in `IUT/Applications/ABCSpecialization.lean` (not a sentence of the paper), this route needs (ii) at degrees `d' > 1` even for `d = 1`. | [GenEll] Thm 2.1 and its proof, pages 11 to 13; IUT IV Cor 2.3 and its proof, pages 54 to 55; P-HT | 2, 3 | Form (i) for `ℙ¹ \ {0, 1, ∞}` at points of every bounded degree is stated (`VojtaLineMinusThreePointsBoundedDegree`, open). Form (ii) is stated (`genEllTheorem2_1iiStatement`) and (i) ⟹ (ii) is proved in the instance of the λ-line (`genEllTheorem2_1ii_of_boundedDegree`). Next: (ii) ⟹ (i). |

## 1. Toward IUT III, Corollary 3.12

Corollary 3.12 (IUT III, pages 173 to 174) asserts `−|log(Θ)| ∈ ℝ` and
`−|log(Θ)| ≥ −|log(q)|`. The analysis, with the notation `μ̄`, `Q`, `Ū`, `G`, `τ`, `⊑` used
below, is in [docs/COR312_ANALYSIS.md](docs/COR312_ANALYSIS.md). Its numerical layer is in
`IUT/PaperIII/Corollary312/Numerical.lean`.

### Candidate conditions

These are propositions that a formalization would have to prove, or adopt as named
hypotheses, to pass from Theorem 3.11 to the inequality. None is stated in Lean, because the
objects they mention are not defined. The verdicts are assessments of
`docs/COR312_ANALYSIS.md`.

| Id | Statement | Source | Category | Relation to the conclusion | What would close it |
|---|---|---|---|---|---|
| C1 | The permutation-symmetry identification `τ` of the `0,◦` and `1,◦` region spaces preserves procession-normalized log-volume: `μ̄(τX) = μ̄(X)`. | Step (x), pages 180 to 181 | 3 | weaker, independent | Definitions of processions, tensor packets and `μ̄`, then a proof. |
| C2 | `μ̄(gX) = μ̄(X)` for every `g` in the group generated by (Ind1) and (Ind2), acting jointly. | Thm 3.11 (i), page 154; Step (x), page 181 | 3, 4 | weaker | A Lean definition of (Ind1), (Ind2) and their joint action, then a proof. |
| C3 | (Ind3) is monotone and `G`-stable: `X ⊑ Y ⇒ X ⊆ Y` and `X ⊑ Y ⇒ gX ⊑ gY`. | Thm 3.11 (ii), page 156 | 3, 4 | weaker | A definition of the set of maps (Ind3) ranges over. In the reading of `UpperSemiCompatibility.lean` (regions along the vertical line, each contained in a container, the possible image the hull of their union) the containment is proved for the iterates of the logarithm on units in one local field; stability of the container under (Ind1) and (Ind2) is a hypothesis there (`ContainerStable`; see OP-IND1), and the archimedean surjections of Prop 3.5 (ii) (b) are not modeled. |
| C4 | One averaged log-volume measures both sides, with one averaging rule, and `−|log(q)| = μ̄(Q)`. The determinant raised to a positive tensor power, `det_{⊗M}`, enters only through the normalized construction of Rem 3.9.5 (vii), (Ob3-1) to (Ob3), pages 132 to 133: weighted tensor powers of the determinants of the direct summands (weights of Rem 3.1.1 (iv)), tensored with the inverse determinant of the structure sheaf; `det_{⊗M}` sends an arithmetic line bundle to its `M`-th tensor power, and the degree of the output is read as the log-volume of the original bundle only "by working with suitable normalization factors" (page 133). No scaling law for arbitrary regions is stated; the same normalization must be applied to both sides. | Step (xi-d), page 183; Rem 3.9.5 (vii), pages 132 to 133; Prop 3.9 (iii), page 117 | 4 | weaker; needed for the conclusion to be well posed | Fixing `J` (see A1) and the normalization of Prop 3.9 (iii) (see A2). |
| C5 | Some admissible possible image has hull containing the q-pilot region: `∃ g ∈ G, ∃ Y, g·R_Θ ⊑ Y ∧ Q ⊆ hull(Y)`. | Steps (xi-c) to (xi-f), pages 182 to 184 | 4 | strictly stronger | A proof from IPL and SHE once these are formal properties of an algorithm. |
| C5' | `∃ g ∈ G, ∃ Y, g·R_Θ ⊑ Y ∧ μ̄(Q) ≤ μ̄(hull(Y))`. | as C5 | 4 | stronger in general; equivalent when `μ̄(Ū)` is attained by one hull | As C5, or a proof of the attainment. |
| C6 | `−|log(q)| ∈ R_{≤−|log(Θ)|}`. | Step (xi-f), page 184 | none | **a restatement of the inequality conjunct only** (`stepXIf_inclusion_iff_inequality`, by `Iff.rfl`). The finiteness conjunct `−|log(Θ)| ∈ ℝ` of page 174 is separate: when `−|log(Θ)| = +∞`, every real `−|log(q)|` satisfies C6 while finiteness fails. | Not a usable condition. Assuming it would assume the inequality conjunct; finiteness would still be open (C7). |
| C7 | (a) The union of possible images is relatively compact in each `U^ℚ_{j,v_ℚ}`, so that each local hull has finite log-volume; and (b) the local log-volumes of the hulls are zero for all but finitely many `v_ℚ`, the finite-support condition under which Prop 3.9 (iii), page 117, defines the global log-volume. | opening reduction, page 175; Prop 3.9 (iii), page 117 | 3, 4 | independent of the inequality; (a) and (b) together give the first conjunct `−|log(Θ)| ∈ ℝ`. Placewise compactness (a) alone does not, since `V_ℚ` is infinite. | Compactness of Ism-orbits and boundedness of the (Ind3) containments for (a); an argument for the finite support (b), which page 175 does not address. |
| C8 | Restricting the input to `I_q = {inputs with μ̄(pilot) = −|log(q)|}` leaves the possible outputs unchanged, and C5 holds for some input in `I_q`. | Step (xi-e), page 183; Rem 3.12.2, page 190 | 4 | contains C5 | A formal notion of the input class of the algorithm and a proof of both clauses. |

The central interpretive question is whether the condition of Step (xi-f) is meant as C6,
as C5', or as C5 together with C8 (`docs/COR312_ANALYSIS.md`).

### Gaps by step of the proof

| Id | Step and pages | Gap | Category | What would close it |
|---|---|---|---|---|
| G-RED1 | opening reduction, pages 174 to 175 | Finiteness of `−|log(Θ)|` from "[easily verified] compactness" is asserted; the finite-support condition of Prop 3.9 (iii), page 117, is not addressed. The numerical reduction is verified (`inequality_of_nonneg`). | 3, 4 | C7. |
| G-RED2 | opening reduction, pages 174 to 175 | Restricting possible images to those interpretable as an `F^{⊩▶}`-prime-strip shrinks the union; the effect on the hull is not discussed. | 4 | A proof that the hull is unchanged, or that the restriction only helps the inequality. |
| G-I | Steps (i), (iii), (iv), (v), pages 175 to 177 | Arguments by definition and by reference to Thm 1.5 and Thm 3.11. | 3 | Formal statements of Thm 1.5 and Thm 3.11. |
| G-II | Steps (ii), (vi) to (ix), pages 175 to 180 | Rest on [EtTh], IUT I and IUT II; Step (vi) asserts that three approaches to cyclotomic rigidity are compatible ("one verifies immediately"). | 3 | Formalization of the cited results, or a written argument for Step (vi). |
| G-X | Step (x), pages 180 to 181 | Invariance under (Ind1), (Ind2) asserted; (Ind3) gives an inequality. | 3, 4 | C2 and C3. |
| G-XIabc | Steps (xi-a) to (xi-c), pages 181 to 182 | IPL and SHE are cited from Rem 3.11.1 and Thm 3.11. | 3 | Formal statements of IPL and SHE. |
| G-XId | Step (xi-d), page 183 | Index set `|F_l|` versus `F*_l`, and the determinant power. | 4 | C4. |
| G-XIef | Steps (xi-e), (xi-f), pages 183 to 184 | The inclusion is asserted; the proposition that yields it is not named. The final passage is formal and checked in Lean. | 4 | C5, C5' or C8. |
| G-XIg | Step (xi-g), pages 184 to 185 | "Two tautologically equivalent ways to compute" give a region bound and a number; "equivalent" needs a precise meaning. | 4 | A precise statement of the equivalence. |
| G-XIh | Step (xi-h), page 185 | The step that uses `N = 1` is not located. | 4 | Identifying the step and the [EtTh] result it uses. |
| G-XII | Step (xii), pages 185 to 186 | An argument for using global Frobenioids. | 3 | Formalization of global Frobenioids. |
| G-311 | Thm 3.11, pages 153 to 159; Rem 3.8.2, pages 114 to 115 | Theorem 3.11 is not stated in Lean; its proof on page 159 is a single sentence, and the LGP generalization of Thm 1.5 that it uses is asserted in Rem 3.8.2. | 3 | Definitions of the log-theta-lattice, packets and indeterminacies; see `docs/THEOREM_3_11.md`. |

## 2. The dispute map

`data/dispute_map.json` maps each objection of Scholze and Stix to Mochizuki's response and to
a formal obligation. No winner is declared. Analyses: `docs/SCHOLZE_STIX_ANALYSIS.md`,
`docs/MOCHIZUKI_RESPONSES.md`.

| Id | Obligation | Source | Category | What would close it |
|---|---|---|---|---|
| OB-RED | Real analysis from Claim 6 and (1.2), (1.3) to Vojta's inequality with `O(1)`. | SS pages 2 to 3 | closed | Done: `vojta_of_claim6`. It needs only the lower bound `N ≥ 0` on the different plus conductor term, and no finiteness statement: neither finiteness of `j`-invariants of bounded degree and height (Northcott; Mochizuki's (C1)) nor finiteness of the curves `E/k` as above (Scholze and Stix, Remark 5, page 3), which would need its own argument. |
| OB-HT | The category of Θ^{±ell}NF-Hodge theaters with `l` and `V` fixed, and its relation to the curve `X` (objection D2). | SS page 6; IUT I, Definition 6.13, pages 182 to 184 | 3 | A Lean definition of the category and a proof or refutation of the equivalence. |
| OB-LOG | The log-link with distinguished domain and codomain, and whether the Θ-link is invariant under identifying them (Mochizuki's question (Q3); D3). | SS pages 6 to 7; IUT III Def 1.1, pages 24 to 27 | 2, 3 | The log-shell (P-LOG below), then the definition and a proof. |
| OB-IND | Lean definitions of (Ind1), (Ind2), (Ind3) and of full poly-isomorphisms ((Ind3) is typed in one reading of its nonarchimedean part, with abstract regions, in `UpperSemiCompatibility.lean`), and a proof or refutation that Theorem 3.11 needs them (D4). | SS page 7; IUT III page 154 | 3 | Definitions; then Theorem 3.11 with the indeterminacies removed, proved false or trivial. |
| OB-DEF | Lean definitions of `−|log(Θ)|` and `−|log(q)|` from initial Θ-data (D5). | IUT III pages 173 to 174 | 3 | The constructions listed in section 1. |
| OB-311-HYP | The exact hypotheses of Theorem 3.11, in particular whether the value group and unit group portions of the Θ-link domain must come from one ring structure ((ThetaCR)); decides whether the identity version (SSId) is admissible (D6). | SS page 9; IUT III pages 153 to 159 | 4 | A faithful statement of Theorem 3.11. |
| OB-XI-CONTAINER | The output possibilities and the q-pilot representation lie in one container `1,◦U^ℚ` with one log-volume, so that no cycle of identifications of copies of `ℝ` must commute (D7, D8). | IUT III Steps (xi-b) to (xi-d), pages 182 to 183 | 4 | C4 and the definition of the container. |
| OB-XI-F | `−|log(q)|` lies in `R_{≤−|log(Θ)|}`, that is, the multiradial construction is a construction of the input pilot log-volume up to indeterminacies (D9). The formal last step is `IUT.Audit.MochizukiResponses.ToyModels.stepXIf_formal`. | IUT III Steps (xi-e), (xi-f), pages 183 to 184 | 4 | C5 with C8, or C5'. |
| OB-BLUR-QUANT | The quantitative objection: a blurring that makes the diagram commute must be by a factor of at least `O(l²)`, and a blurring of that size makes the inequality from (1.4) useless. Needs OB-IND-SIZE and a computation of how the blurring enters (1.4). Under (Lin) and the tolerance model `ConsistentUpTo` (an interval `[1/B, B]` for the product of scalars around a cycle; a modeling choice of this project, not a statement of either side), `IUT.Audit.ScholzeStix.consistentUpTo_avgSq_iff` only evaluates the tolerance condition. Whether (Lin) holds for log-volumes under the indeterminacies is disputed (Mochizuki's (C14) accepts it only at the level of prime strips) (D10). | SS page 10; Cmt-08 (C14), page 4 | 4 | OB-IND-SIZE, then the computation. |
| OB-IND-SIZE | The quantitative effect of (Ind1), (Ind2), (Ind3) on log-volumes, to compare with the factor `l(l+1)/12` of `IUT.Audit.ScholzeStix.avgSq_eq` (D10). | SS page 10; IUT IV Prop 1.2 and Thm 1.10, pages 10 to 31 | 3 | Relating the local bounds of `IUT/PaperIV/` to the indeterminacies of Theorem 3.11. |

## 3. Prerequisite gaps

From [docs/MATHLIB_GAP_ANALYSIS.md](docs/MATHLIB_GAP_ANALYSIS.md), which classifies each area
as (1) in Mathlib, (2) derivable, (3) substantial new formalization, (4) in another Lean
library, (5) needs further literature, (6) unresolved or disputed.

| Id | Statement | Source | Category | What would close it |
|---|---|---|---|---|
| P-LOG | The log-shell `I_{†F_v}` needs the `p`-adic logarithm with convergence on the disc, the homomorphism property and the extension to all units; Mathlib's `NormedSpace.log` lacks these (TODO items in `Analysis/Normed/Algebra/Logarithm.lean`). For the base field `ℚ_p` the library proves them (`IUT/Prerequisites/PadicLog.lean`): convergence on the open unit disc, the homomorphism property, the extension to `ℤ_p^×` whose image is the closed ball of radius `1/p*` (`p* = p` for odd `p`, `p* = 4` for `p = 2`), and the log-shell of page 24, proved compact and equal to `ℤ_p`; the identification of the Galois-invariant units with `ℤ_p^×` is not formalized. For a finite extension `L` of `ℚ_p` the library defines the logarithm on the units and the log-shell `(p*)⁻¹ log(R^×)` in a normed-field model (`IUT/PaperIV/LocalFields/Logarithm.lean`), and proves for `R = integralClosure ℤ_p L` with the spectral norm that the closed unit ball is `R`, that the ramification index satisfies the hypothesis of the model (`padicBridge_hval`), and the bounds of IUT IV Prop 1.2 (i) (`padicBridge_extLogUnit_image_bounds`, `padicBridge_extLogShell_bounds`). Open: compactness of the log-shell beyond `ℚ_p`, tensor products of more than two rings of integers, and the setting of IUT III. | IUT III Def 1.1, page 24; IUT III Prop 1.2 (v), pages 31 to 32; IUT IV Prop 1.2, pages 10 to 11 | 2 | These results for finite extensions of `ℚ_p`, in Mathlib or in the library. Defining the log-shell as `ℤ_p` would be a shell; for `ℚ_p` the equality is a theorem. |
| P-PULL | Pull-back `𝔞|_K` of arithmetic divisors and `deg(𝔞|_K) = deg(𝔞)`. Defined "in the evident fashion". | IUT IV Def 1.9 (i), pages 21 to 22 | 3 | Done in one reading: `degPb_normalizedDeg_pullback` (`IUT/PaperIV/DegreePullback.lean`). |
| P-DEG0 | Degree zero of principal arithmetic divisors with the archimedean weight 1 of Def 1.9 (i). | IUT IV pages 21 to 23 | 3 | Done with the convention of [GenEll] page 4 (`degPb_degF_principal`). |
| P-UNIV | Existence of a Grothendieck universe in `ZFSet.{u+1}`. Mathlib has the embedding only for `PSet`. | IUT IV pages 67 to 68 | 2 | A construction and a check of axioms (i) to (v). The library uses the existence axiom `(†^G)` only as the explicit hypothesis `ExistenceAxiom`. `ExistenceAxiom` is a statement about Lean's model `ZFSet.{u}`, not the paper's axiom in the paper's set theory, and it is not expected to be provable or refutable in Lean: in the standard semantics where `Type u` is `V_κ` for an inaccessible `κ`, it fails when `κ` is the least inaccessible (then `ZFSet.{u}` contains no Grothendieck universe) and holds when `κ` is an inaccessible limit of inaccessibles. This argument is about models and is not formalized. In models where it fails, the two conditional theorems `exists_universe_forall_mem` and `exists_ascending_chain` are vacuous. |
| P-ANAB | Tempered fundamental groups, anabelian reconstruction, Frobenioids, étale theta functions. | IUT I §§1 to 6; IUT II | 2, 3 | Formalization of [SemiAnbd], [AbsTopIII], [FrdI], [EtTh]; classes 3 and 5. |
| P-HA | Hodge-Arakelov theory. | IUT II | 2 | Class 5: the literature itself must be read first. |
| P-HT | Heights, log-differents and log-conductors on curves over number fields; needed for Theorem A of IUT IV and its passage to `Challenge.ABCLog`. | IUT IV, Theorem A and Cor 2.3, pages 41 to 55 | 2, 3 | Definitions in Mathlib or in the library, then the specialization of `docs/PAPER_IV_DERIVATION.md`. |
| P-VOJ | Szpiro-type and Vojta-type inequalities. | IUT IV | none | Class 6: these are the disputed conclusions, not prerequisites to be imported. |

## 4. Ambiguities in the papers

Places where the text admits more than one reading, or uses a notion it does not define.
Extraction artifacts of the PDF text layer are not ambiguities of the papers; they are listed
in `docs/VERIFICATION_REPORT.md`.

| Id | Source | Description |
|---|---|---|
| A1 | IUT III pages 153, 173, 174, 181, 183 | Pages 173 and 181 say that the average is taken over `j ∈ F*_l`. Pages 153 and 174 index the modules, integral structures and regions by `j ∈ |F_l|` (and `v_ℚ ∈ V_ℚ`) and state no average. Page 183 speaks of the log-volume "suitably normalized, with respect to `j ∈ |F_l|`". How the component of label 0 enters an average over `F*_l` is not stated. |
| A2 | IUT III page 117 | "relative to a suitable normalization" in Prop 3.9 (iii) is not specified; Thm 3.11 (i)(c), page 154, inherits it. |
| A3 | IUT III pages 154, 181 | (Ind1) is defined as automorphisms of the procession, then described as permutation symmetries of the étale picture. |
| A4 | IUT III page 154 | Whether (Ind1) includes automorphisms of each D^⊢-prime-strip or only permutations of labels is not stated. |
| A5 | IUT III page 156 | (Ind3) is called an indeterminacy but defined as a semi-compatibility property; the maps it ranges over are not specified. |
| A6 | IUT III pages 157 to 159 | "compatible up to (Ind1), (Ind2), (Ind3)" does not say whether the indeterminacies act jointly or separately, or whether compatibility means equal orbits or containment. |
| A7 | IUT III pages 173 to 174 | "possible images" and "subject to the indeterminacies" are not given as a set by a formula; whether (Ind3) enlarges each image or acts separately is not stated. |
| A8 | IUT III page 183 | Why every real below `−|log(Θ)|` is a possible log-volume, rather than only the log-volumes of actual images, is not argued. |
| A9 | IUT III page 184 | "perhaps only up to some sort of approximation" leaves the sense of the condition in Step (xi-f) open. |
| A10 | IUT III pages 184 to 185 | "tautologically equivalent": the two computations give a region bound and a number. |
| A11 | IUT III pages 185 to 187 | Rem 3.12.1 (ii) applies the argument to `q^λ`; Step (xi-h) excludes `N`-th powers on the theta side. Which steps differ is not shown. |
| A12 | IUT III pages 181 to 182 | The "somewhat more complicated" relation for the `F^{⊢×μ}` portion in Step (xi-b) is not specified. |
| A13 | IUT III pages 124, 145 to 147, 173 | Value sets `ℝ ∪ {+∞}` (Cor 3.12) and `ℝ ∪ {−∞}` (Rem 3.9.4, Rem 3.9.7) are not reconciled. |
| A14 | IUT III page 127 | Rem 3.9.5 (ii) gives closure under intersections as the reason for the intersection formula; the formula follows from (P1) to (P3) alone (checked in `HullOperator.lean`), and closure gives existence. At archimedean places the "smallest `λ·O`" exists by compactness; the text does not separate the cases. |
| A15 | IUT III pages 35 to 39 | Rem 1.2.2: "commutative with respect to log-volumes" is not defined as a formal property. |
| A16 | IUT III pages 48 to 50 | Thm 1.5 (iii): "regarded up to a certain class of isomorphisms" is not described. |
| A17 | IUT III page 112 | Def 3.8 (i): "determined by any collection" asserts independence of the choice without argument. |
| A18 | IUT III pages 115 to 116 | Prop 3.9 (i): the weighting under which multiplication by `p_v` acts on a packet with several components is stated by reference. |
| A19 | IUT III pages 119 to 120 | Rem 3.9.3: which quantity must be preserved under inclusions is not specified, and the conclusion depends on it. |
| A20 | IUT III pages 131 to 139 | Rem 3.9.5 (vii), (Ob4): the effect of the `M`-th tensor power on normalized log-volume is not written as a formula. |
| A21 | IUT III pages 159 to 167 | Rem 3.11.1: IPL and SHE are stated informally. |
| A22 | IUT III pages 187 to 195 | Rem 3.12.2 (e^toy): the property that does the work is introduced by "suppose that one verifies". |
| A23 | IUT I page 88 | Rem 3.6.2 leaves isomorphisms of Θ-Hodge theaters to the reader; morphisms of Θ-bridges (Def 5.5, pages 151 to 153) depend on them. |
| A24 | IUT I page 87 | Rem 3.5.2: later definitions of morphisms rely on this unstated convention. |
| A25 | IUT I pages 111 to 112 | Def 4.6: composition of morphisms is described as evident. |
| A26 | IUT I pages 39 to 40 | Cor 1.2: "algorithm" is informal; no model of computation is specified. The same holds for "algorithm" and "functorial" in Thm 3.11 (i), IUT III pages 153 to 155. |
| A27 | IUT I pages 61 to 62 | Def 3.1 (b): "stable reduction" of `X_F` is identified with semistable reduction of `E_F`, and "bad" is glossed as multiplicative; page 61 does not spell this out. |
| A28 | IUT I page 148 | Ex 5.4: `F^⊚|_δ` is defined only up to isomorphism. |
| A29 | IUT II pages 79 to 80 | Rem 2.6.3: read literally, item (d) says `‖Γ′‖` is strictly increasing in `|Γ′|` on `{1, …, l*}` (proved in `IUT/PaperII/Labels.lean`), which conflicts with "not strictly increasing". See `docs/PAPER_II_STRUCTURES.md`. |
| A30 | IUT IV pages 21 to 22 | Def 1.9 (ii): the numerator is the unnormalized `deg_F` (not underlined in the render); only this reading makes the stated invariance hold. The Lean definition uses it. |

## 5. Unstated hypotheses

Steps that need a hypothesis the page does not write. Each one holds for the intended
quantities; none is an error in the paper. Where Lean is listed, the hypothesis is carried
explicitly there.

| Id | Statement | Source | Category | Status |
|---|---|---|---|---|
| H2 | `D ≥ 0` to pass from `(4/l)·D` to `(4·d_mod/l)·D`. | IUT IV Thm 1.10 Step (iii), page 26 | 4 | Holds by definition; carried in `step_iii_final`. |
| H3 | `log 𝔡^K_{v_ℚ}`, `log 𝔰^ℚ_{v_ℚ}`, `l*_mod·log 𝔰^≤_{v_ℚ} ≥ 0`, and `l ≥ 5`. | IUT IV Thm 1.10 Step (v), page 29 | 4 | Hold by definition; carried in `step_v_final`. |
| H4 | `l ≥ 7`, while (P1) writes `5 ≤ l`. | IUT IV Cor 2.2, page 45; Thm 1.10, page 22 | 4 | Follows from `l ≠ 5`, which page 22 derives from two premises together: the assumption of Thm 1.10 that the `(3·5)`-torsion points of `E_F` are defined over `F` (so the 5-torsion is rational), and IUT I Def 3.1 (c) (the image of Galois in `GL_2(F_l)` contains `SL_2(F_l)`). Independently from `5 ≤ h^{1/2} < l` (`P1_l_ge_seven`). |
| H5 | Cor 2.2 (iii) is stated for `ε ≤ 1`; Cor 2.3 uses all `ε > 0`. | IUT IV Cor 2.3, pages 54 to 55 | 4 | Monotonicity in `ε`, since `log-diff + log-cond ≥ 0` (`BDle_mono_eps`). |
| H6 | `[F : F_mod]` prime to `l` is not argued separately in the proof of Cor 2.2. | IUT IV pages 42 to 48 | 4 | Open: a check against IUT I Def 3.1; see `docs/INITIAL_THETA_DATA.md`. |
| H7 | `N ≥ 0` in the reduction of Scholze and Stix; `β ≥ 0` in the first display. | SS page 3 | 4 | `N ≥ 0` holds for the intended quantities and is carried in `vojta_of_claim6`; `β ≥ 0` is removable by passing to `|β|`. |
| H8 | The inverted form of display (1.5) needs `1 − 12/(l(l+1)) > 0`, that is `l ≥ 5`. | SS page 4 | 4 | The Lean statement `consequence_with_squares` uses the multiplied form, valid for all `l`. |
| H9 | The LGP generalization of Thm 1.5 used by Theorem 3.11 is asserted in Rem 3.8.2, not proved as a numbered statement. | IUT III pages 114 to 115 | 3 | A statement and proof of the generalization. |

## 6. Open items of the local, prerequisite and Diophantine modules

Each item is a statement that the modules named do not formalize; the modules say so in their
docstrings. Pages are manuscript pages of IUT I to IV unless another paper is named.

| Id | Statement | Source | Category | What would close it |
|---|---|---|---|---|
| OP-P13-BASE | IUT IV Prop 1.3 over a general base `k_0 ⊆ k_i` containing `ℚ_p`: (i) `𝔡_i ≥ 𝔡_0 + (e_{i/0} − 1)/e_i`, with equality when `k_i` is tamely ramified over `k_0`, and (ii) `𝔡_i ≤ 𝔡_0 + n_i + 1/e_0`. Over a general base, the transitivity of the different, (i) as an inequality and its equality in the tame case are proved, and (ii) when `k_i` is tame over `k_0` and when `n_i = 0` (`IUT/PaperIV/LocalFields/Tower.lean`); (ii) in the wild Galois case is open. | IUT IV Prop 1.3, pages 11 to 12 | 2, 3 | The induction of page 12 through Kummer extensions of degree `p`. |
| OP-P11 | IUT IV Prop 1.1: `p^(𝔡_{I*}) · (R_I)^∼ ⊆ R_I ⊆ (R_I)^∼`. The second inclusion is proved for two factors, with `(R_E)^∼` the integral closure of `ℤ_p` in `K_1 ⊗ K_2` (`IUT/PaperIV/LocalFields/VolumeBridge.lean`); the first is proved for two factors, with `p^(𝔡_{I*})` an element of order `𝔡_2`, a generator of the different or any element of it (`IUT/PaperIV/LocalFields/TensorDifferent.lean`). More than two factors, and that this integral closure is the normalization of the paper, are not proved. | IUT IV Prop 1.1 and its proof, pages 9 to 10 | 2, 3 | An induction on the number of factors for the first inclusion. |
| OP-P12 | IUT IV Prop 1.2 (ii) to (iv): the inclusions for the tensor products `R_I`. (i) is proved for one finite extension of `ℚ_p`; of (ii), the first display of its proof is proved for two factors in a stronger form (`tensorDiff_mul_mem_logUnit_span`). | IUT IV Prop 1.2, pages 10 to 11 | 2, 3 | OP-P11 and the logarithm on `R_I^×`. |
| OP-TENSOR | Tensor packets of more than two factors: the first inclusion of Prop 1.1 and the additivity of `μ^log` over factors used on page 14. The decomposition of `⊗_{i ∈ E} K_i` into finite extensions of `ℚ_p` and the normalization of IUT IV Prop 1.4 (i) on `(R_E)^∼` are done for any finite number of factors over `ℚ_p` (`IUT/PaperIV/LocalFields/Packets.lean`); the identification of the tensor product over `ℤ_p` with that over `ℚ_p` is a model test there. | IUT IV Prop 1.1 and 1.4, pages 9 and 13 to 14 | 3 | An induction on the number of factors with the decomposition at each step. |
| OP-IND1 | Stability of the log-shell of a tensor packet under (Ind1) and (Ind2), the hypothesis `ContainerStable` of `UpperSemiCompatibility.lean`. For (Ind2) on one factor, Prop 1.2 (vi), page 32, asserts the compatibility, not proved here; for (Ind1), no page read for that module asserts it. | IUT III Prop 1.2 (vi), page 32; Thm 3.11 (i), page 154 | 3, 4 | A definition of (Ind1) on packets, then a proof, or a page that asserts it. |
| OP-KV | The compactly bounded form, [GenEll] Theorem 2.1 (ii): the inequality on `K_V ∩ U_P(ℚ̄)^{≤d}` for compactly bounded `K_V` whose support contains a fixed finite set of primes, the form that IUT IV Cor 2.3 derives (with `Σ = {2}` and `(*_{j-inv})`). Stated as an open proposition (`genEllTheorem2_1iiStatement`, `IUT/Applications/CompactlyBounded.lean`), with compactly bounded subsets defined through `PadicAlgCl p`; the reduced form of page 55 is stated (`iutIVCor2_3ReducedFormStatement`). | [GenEll] Thm 2.1 (ii), page 11, Example 1.3 (ii), pages 5 to 6; IUT IV pages 41 and 55 | 2, 3 | T-GENELL. |
| OP-ANAB | The converse of Remark 1.1.1.1 of *The Geometry of Anabelioids*: a connected anabelioid is a Galois category. One direction is proved (`IUT/Prerequisites/Anabelioid.lean`). | *The Geometry of Anabelioids*, pages 9 to 10 | 2 | Transport of `GaloisCategory` along an equivalence of categories, which Mathlib lacks. |
| OP-FRD | Clauses (i) (c) and (iii) (d) of Definition 1.3 of *The Geometry of Frobenioids I*; without them `PartialFrobenioidConditions` is not the definition of a Frobenioid (`IUT/Prerequisites/Frobenioid.lean`), and that its example satisfies them (Proposition 1.5) is not proved. | *The Geometry of Frobenioids I*, Definition 1.3, pages 24 and 25; Proposition 1.5, page 27 | 2, 3 | Category structures on slices of non-full subcategories, then the two equivalences. |

**The triple `1 + 8 = 9` and the exceptional set.** For the coprime triple `1 + 8 = 9` the point
`λ = 1/9` of the `λ`-line has `j`-invariant `2²·73³·3⁻⁴`: this is `legendreJ_one_ninth`, a
computation of the rational function `legendreJ` at `1/9`. `legendreJ_eq_73_iff` proves that,
for `t ≠ 0, 1` in a field of characteristic zero, `legendreJ t = 2²·73³·3⁻⁴` exactly when `t` is
one of `9, −8, 9/8, −1/8, 8/9, 1/9`. The value `2²·73³·3⁻⁴` is one of the four `j`-values listed
in *Explicit estimates in inter-universal Teichmüller theory*, Proposition 2.1, page 21, and the
proof of IUT IV Cor 2.2 (ii), page 43, excludes points with one of "four possibilities for the
`j`-invariant". That these are the `j`-invariants of curves without an F-core, and that such
points lie in the exceptional set `Exc_d`, are statements of the papers that are not proved
here. Nothing about the triple follows from these two lemmas beyond its `j`-value.

## 7. Not attempted yet

Recorded so that nobody reads their absence as a result: the nonvacuity of
`PartialInitialThetaConditions` (an explicit curve satisfying it), conditions (d) to (f) of
IUT I Definition 3.1, power maps on `ℤ_p^×`, free and surface groups for IUT I §§1 to 2, and
prime strips and Hodge theaters. See `docs/FAILED_APPROACHES.md`.
