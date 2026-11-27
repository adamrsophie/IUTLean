# Literature survey

This page summarizes a survey of the arXiv literature around inter-universal Teichmüller
theory (IUT), the abc conjecture, and the formalization methods this project uses. The
machine-readable record is [`data/literature.json`](../data/literature.json), with one entry
per paper read and per paper kept at screening. Each entry gives authors, title, year, arXiv
categories, a theme, a relevance score, how the paper was read, a neutral description, the
statements of interest with their numbers (for the papers scored 2 or 3), and links to
statements, open problems and files of this project.

The project is neutral in the dispute over IUT III, Corollary 3.12. This page reports what
papers state and what readings for this project found. It does not say whether any paper
proves or refutes abc, Szpiro's conjecture, Vojta's conjecture or Corollary 3.12.

## 1. Method and counts

* **Search.** 96 queries to the arXiv API, retrieved on 2026-11-25, returned 1,412 distinct
  records (title, authors, abstract, categories, dates).
* **Screening.** Each record was screened on its title and abstract: 201 were included, 12
  were marked maybe, and 1,199 were excluded.
* **Reading.** 98 papers (86 of the included ones and all 12 maybes) were selected for
  reading in full text. Of these, 32 were read in full from the TeX source, 30 in full from
  the PDF text, 35 in part (the sections read are listed in each record), and 1 could not be
  read because the arXiv page states that it is withdrawn. The other 115 included papers were
  not read beyond the abstract. One further working paper, not on arXiv, was supplied to the
  project and read in part.
* **Records.** `data/literature.json` therefore holds 214 records: 98 read from arXiv, 115
  abstract only, and the supplied working paper.
* **Scores.** Each paper read was given a relevance score from 0 (no use for the project) to
  3 (directly usable): 7 papers scored 3, 24 scored 2, 43 scored 1 and 25 scored 0. Papers
  known only from the abstract have no score.
* **Second readings.** For the papers that bear most on the comparison with Corollary 3.12,
  a second, independent reading checked selected statements. An internal inconsistency of a
  paper is reported on this page only when both readings report the same thing at the same
  location.

Where a paper's TeX title uses a double hyphen, it is written with a single hyphen in the
records; a spaced hyphen used as a separator in a title is written as a colon; TeX markup in
titles is reduced to plain text.

## 2. Themes

| Theme | Records | Read (full or partial) |
|:-|:-|:-|
| IUT core expositions and reformulations | 2 | 2 |
| Joshi series | 14 | 14 |
| Explicit consequences | 5 | 5 |
| Critiques and the dispute | 2 | 2 |
| Anabelian and local-field prerequisites | 44 | 32 |
| abc and Vojta | 122 | 24 |
| Formalization methodology | 25 | 20 |

**IUT core.** T. Dupuy and A. Hilado, "The Statement of Mochizuki's Corollary 3.12: Initial
Theta Data" (arXiv:2004.13228), restate the hypotheses of Corollary 3.12 (pre theta data,
Definition 2.4.1; initial theta data, Definition 2.8.1) in standard terms and work the
example of curve 11a1 with l = 13. Their Remark 2.4.2 records that IUT I, Definition 3.1 asks
for 6-torsion while the authors impose 30-torsion because IUT IV uses it. A. Sarkisyan
(arXiv:2306.02448) claims another proof of Corollary 3.12; see Section 3.

**Joshi series.** K. Joshi's papers build "arithmetic Teichmüller spaces" from untilts of
perfectoid fields and Fargues and Fontaine curves (arXiv:2010.05748, 2106.11452, 2210.11635),
anabelomorphy (arXiv:2003.01890, 2008.01228) and arithmeticoids (arXiv:2305.10398). Three
papers carry the main claims: a local prototype (arXiv:2303.01662), a version of Corollary
3.12 for theta sets the author constructs (arXiv:2401.13508), and abc (arXiv:2403.10430). A
report (arXiv:2505.10568) states the author's position without proofs. Section 1.4 of
arXiv:2403.10430 gives the author's correspondence with IUT IV: Corollary 2.2 with Theorem
5.7.1, Corollary 3.12 with Corollary 9.11.1.1 of arXiv:2401.13508, Theorem 1.10 with Theorem
6.1.1, and Corollary 2.3 with Theorem 7.1.1.

**Explicit consequences.** These papers derive explicit inequalities from Corollary 3.12 or
from IUT IV, and state them as conditional:

* T. Dupuy and A. Hilado, "Probabilistic Szpiro, Baby Szpiro, and Explicit Szpiro from
  Mochizuki's Corollary 3.12" (arXiv:2004.13108);
* V. Dimitrov, "Effectivity in Mochizuki's work on the abc-conjecture" (arXiv:1601.03572),
  an outline of an effective form of [GenEll], Theorem 2.1;
* Z.-P. Zhou, "The inter-universal Teichmüller theory and new Diophantine results over the
  rational numbers. I" and "II" (arXiv:2503.14510, 2510.05448), which take as input the
  μ₆ version of Corollary 3.12 from S. Mochizuki, I. Fesenko, Y. Hoshi, A. Minamide and
  W. Porowski, "Explicit Estimates in Inter-universal Teichmüller Theory" (not returned by
  the search, so outside this survey);
* P. Mihăilescu and M. T. Rassias (arXiv:2108.08580), a Fermat bound announced as input for
  an explicit abc inequality based on IUT IV, Theorem A.

**Critiques and the dispute.** Two papers in the corpus discuss the dispute. A. Aberdein,
"Deep Disagreement in Mathematics" (arXiv:2210.16488), states (page 19) that formalization
cannot arbitrate a dispute that has to be settled before formalization begins. Y. Lu
(arXiv:2603.21074) gives a heuristic argument doubting the main inequality of Corollary 3.12,
and the author states that it is not fully justified.
C. Zeng, "An Integral-Structure Inflation in the Hull Operation of IUT Corollary 3.12"
(hexagon 2610.00646, version 1, 29 October 2026; not on arXiv, so outside this survey and its
counts), computes for a Galois extension `K` of `ℚ_p` the index of the image of the `n`-fold
tensor power of its ring of integers in the maximal order (Theorem 5.1), and from it draws a
conclusion about the passage from Theorem 3.11 to Corollary 3.12 (sections 8 to 10 and 16); the
author states that the paper is "not a verdict on IUT". `IUT/Audit/TensorOrderIndex.lean`
checks the case of two factors; see [`COR312_ANALYSIS.md`](COR312_ANALYSIS.md). The search did not return the
manuscript of P. Scholze and J. Stix; the project's account of the
dispute is in [`data/dispute_map.json`](../data/dispute_map.json).

**Anabelian and local-field prerequisites.** These include:

* tempered fundamental groups: E. Lepage (arXiv:1004.2150, 0811.3169) and related papers;
* m-step solvable reconstruction of number fields and local fields: M. Saidi and
  A. Tamagawa (arXiv:1909.08829), S.-H. Hyeon (arXiv:2405.16950), Y. Mao and M. Saidi
  (arXiv:2511.05192);
* two results on outer automorphisms of absolute Galois groups of p-adic fields: K. Kondo
  (arXiv:2512.09231) for p odd and Y. Nishio (arXiv:2512.05095) for p = 2. Both show that
  Aut(k) is not normal in Out(G_k) in the cases they treat;
* the image of a Lubin and Tate logarithm: G. Harbor-Collins (arXiv:2604.27111);
* canonical models of the four arithmetic (1; ∞) curves: J. Sijsling (arXiv:1707.01158). The
  author states that IUT I, Definition 3.1 (d) excludes these curves.

**abc and Vojta.** This theme holds:

* P. Vojta's formulation of the conjecture for algebraic points with truncated counting
  functions (arXiv:math/9806171);
* M. van Frankenhuijsen's proofs of two restricted abc reductions, including Mochizuki's
  general position reduction (arXiv:2010.09493, Theorem 7.6);
* elementary coordinates for abc triples, R. Laniewski and K. Müller (arXiv:2610.03212);
* unconditional bounds weaker than abc (Section 3);
* many papers that use abc as a hypothesis. These were screened but not read.

**Formalization methodology.** This theme covers:

* Lean libraries the project can build on: Mason and Stothers (arXiv:2408.15180), Weierstrass
  curves (arXiv:2302.10640), local fields (arXiv:2310.01998), q-series and the Jacobi triple
  product (arXiv:2607.01544);
* three papers on whether formal statements are faithful to their sources: Formal
  Conjectures (arXiv:2605.13171), MechAlign (arXiv:2610.35269) and LeanFlow
  (arXiv:2607.20503).

## 3. Claims of a proof or partial proof

The status column reports what the paper states and, where marked, what a reading for this
project found. It is not this project's verdict on the claim.

| Paper | Claim | Status as described |
|:-|:-|:-|
| K. Joshi, arXiv:2403.10430 | abc and Szpiro over Q (Theorem 7.2.1), via Vojta's inequality on the line minus three points (Theorem 7.1.1) | Preprint that the author marks as a preliminary version for comments. It takes the Corollary 3.12 step from arXiv:2401.13508. Section 1.6, item 6 (page 21) states that the expected relation between the two theta sets of Part III "is not presently established". Locations confirmed by two readings are in Section 4. |
| K. Joshi, arXiv:2401.13508 | Corollary 3.12 for the author's theta sets (Theorem 9.11.1, Corollary 9.11.1.1) | Preprint. The text records disagreement both with Scholze and Stix and with Mochizuki. Locations confirmed by two readings are in Section 4. |
| K. Joshi, arXiv:2303.01662 | A one-prime inequality for the author's theta locus (Theorem 9.2.1) | The author states that the locus is not the set of IUT III and that the inequality is not exactly Corollary 3.12. |
| K. Joshi, arXiv:2111.04890 | A local analog of Corollary 3.12 | The author states that it is not a proof of Corollary 3.12 and claims no Diophantine consequence. |
| K. Joshi, arXiv:2505.10568 | abc is established by the author's series combined with IUT | A position report with no proofs. |
| A. Sarkisyan, arXiv:2306.02448 | Another proof of Corollary 3.12, based on the Erdős and Kac theorem | Listed in math.GM. The arXiv page seen when the PDF was obtained was titled as withdrawn. |
| Z.-P. Zhou, arXiv:2503.14510 | Explicit abc over Q (Theorem 3.2: log abc ≤ 3 log rad(abc) + 8 (log abc · log log abc)^(1/2) when log abc ≥ 700), an ε form (Corollary 3.3), and Fermat-type results | Stated as conditional on the μ₆ version of Corollary 3.12 (Proposition 1.9). Some ranges rely on computer calculations that the author does not publish. |
| Z.-P. Zhou, arXiv:2510.05448 | The method of Part I for 2-torsion initial theta data, and generalized Fermat results (Theorem 5.1) | Conditional as above. Remark 1.1.1 claims that IUT I to IV hold in the 2-torsion setting. The author states (Remark 1.13.1 (ii)) that an analytic step is omitted, and describes this version as older. |
| T. Dupuy and A. Hilado, arXiv:2004.13108 | Probabilistic, baby and explicit Szpiro inequalities (Theorems 1.0.3, 7.12.1, 8.2.1) | Stated as conditional on Corollary 3.12 and on Claim 5.0.1, an archimedean radius used as an assumption. |
| V. Dimitrov, arXiv:1601.03572 | An effective reduction from abc on compactly bounded sets to full abc (Theorem 1.1) | The author presents it as an outline. An effective abc would follow if IUT IV, Theorem 1.10 holds. |
| P. Mihăilescu and M. T. Rassias, arXiv:2108.08580 | An explicit abc inequality based on IUT IV, Theorem A | Announced. The paper proves only a lower bound for solutions of the second case of Fermat's Last Theorem. |
| C. Soulé, arXiv:2611.05217 | Theorem B: c ≤ A(ε) rad(abc)^(24 + ε) for coprime positive a + b = c | Unrefereed preprint of November 2026. The exponent is fixed, so the statement does not imply the abc conjecture. The body calls its height inequality for genus two curves (Theorem A) a weak form of Vojta's conjecture. |
| H. Pasten, arXiv:1705.09251, 2205.07841, 2312.03566; H. Pasten and R. Sepúlveda-Manzo, arXiv:2406.05083; A. Surroca, arXiv:math/0408168 (Theorem 4) | Unconditional bounds of polynomial, subexponential or exponential shape | Weaker than abc, as the authors state. arXiv:2205.07841 also gives a 1 + ε truncated Vojta inequality conditional on the Lang and Waldschmidt conjecture. |
| H. Pasten, arXiv:2609.17390, 2308.07114; J. Cuevas Barrientos and H. Pasten, arXiv:2504.15971 | Unconditional Szpiro-type bounds for all curves over Q, for small j-denominators, and in families | Far weaker than Szpiro's conjecture, as the papers state. |
| Y. Yasufuku, arXiv:1601.03825 | Vojta's conjecture for certain blowups of the plane | Proved for those surfaces. The paper states that these cases imply only an S-unit case of abc. |
| C. Bright, arXiv:2301.11056; C. Bernert, T. Browning, J. D. Lichtman and J. Teräväinen, arXiv:2410.12234 | A lower bound for infinitely many triples; counts of triples | They bound how sharp abc can be, or count triples. Neither bounds individual triples by abc. |
| abstract only: arXiv:1802.02770, math/0301050, 1708.00620, 2407.18406, 1809.03328, 1206.3715, 2111.07791, 2208.14354, 2608.16764 | abc or Szpiro for special sets or families, or improved weaker bounds | Known from the abstract only; not read. |
| abstract only: arXiv:math/0606221, 1407.7289, math/0503401 | Heuristic or conditional arguments against abc | Known from the abstract only; not read. |
| H. Lu, arXiv:1211.0451 | Uniform bounds for base change conductors, with a link to a generalized Szpiro conjecture | The arXiv page states that it is withdrawn. Not read. |

## 4. Locations confirmed by two readings

Each item below was reported independently by two readings for this project at the same
location. The items describe the text as printed. They are not rulings on the main claims,
and the readings differ on what some of them mean for the argument.

* **arXiv:2401.13508 (v4), Corollary 9.11.1.1, page 128.** The corollary prints
  `-(1/l*)|LogVol| ≥ -Σ log|q_w^{1/2l}|`. As printed, the left side is at most 0 and the
  right side is positive. arXiv:2403.10430 (v2), Theorem 6.10.1, quotes the corollary in the
  form `-|log q_l| ≤ -(1/l*)|log Vol|`.
* **arXiv:2401.13508, Theorem 4.2.2.1 (4), pages 32 to 33.** The theorem gives the exponent j².
  The proof of Theorem 9.9.1, display (9.9.4) on page 121, cites it with j²/l*².
* **arXiv:2401.13508, Corollary 7.4.2, page 57.** The lower bound `Π|q_w^{1/2l}|` lacks the
  exponent l* of Theorem 7.3.1, page 55.
* **arXiv:2403.10430, Theorem 5.7.1, page 53.** The window for the auxiliary prime uses
  `log(2δ log Q)`. Lemma 5.8.7 (page 56) and the proof of Theorem 7.1.1 (page 73) use
  `log(2δQ)`.
* **arXiv:2403.10430, proof of Theorem 7.1.1, page 73.** The proof uses `e*_mod ≤ d_mod`.
  The definitions give e*_mod = 2^12·3^3·5·e_mod, and the inequality does not follow from them.

Two further passages of arXiv:2403.10430 are statements of the paper itself, recorded in its
entry in `data/literature.json`:

* Theorem 6.10.1 (pages 66 to 67) joins its lower and upper bounds through an equality of
  hull log-volumes. The proof calls this equality a tautology resting on "the same global
  normalization".
* Section 1.6, item 6 (page 21) says that the expected relation between the two theta sets
  "is not presently established".

## 5. What the literature offers the project, and what it does not

**What it offers:**

* **Elementary statements ready for Lean.** Examples are the inequality (1/12)(1 + 1/l*) <
  (1/4)(1 − 1/l) for odd l ≥ 5 used in arXiv:2303.01662, the inequalities
  2 log c < log(abc) < 3 log c and the abc and Szpiro implications for Frey curves in
  arXiv:2610.03212, the height and radical bounds of arXiv:2010.09493 (Lemmas 2.3 and 2.4),
  and the Frey curve discriminant and conductor relations recalled in arXiv:1705.09251
  (Section 3).
* **Infrastructure.** Mathlib already holds `Polynomial.abc` (arXiv:2408.15180), and Lean
  developments exist for the Weierstrass group law, discrete valuation rings and local fields,
  and the Jacobi triple product (arXiv:2302.10640, 2310.01998, 2607.01544).
* **Comparison points for the hypotheses of Corollary 3.12.** These are initial theta data in
  standard terms (arXiv:2004.13228), the 6-torsion, 30-torsion and 2-torsion variants
  (arXiv:2004.13228, 2510.05448), and the four (1; ∞) curves excluded by IUT I, Definition 3.1
  (arXiv:1707.01158).
* **Precise statements of what anabelian algorithms can and cannot recover.** These include
  m-step solvable reconstruction (arXiv:1909.08829, 2405.16950, 2511.05192) and the
  non-normality of Aut(k) in Out(G_k) (arXiv:2512.09231, 2512.05095). They bear on the
  indeterminacy entries of [`OPEN_PROBLEMS.md`](../OPEN_PROBLEMS.md).
* **Checks on faithfulness.** Formal Conjectures (arXiv:2605.13171) restricts accepted proofs
  to the standard axioms and checks them with a comparator; it reports 14 unfaithful
  statements among 100 reviewed after release. MechAlign (arXiv:2610.35269) reviews the
  closure of statements a theorem depends on, without proof bodies, and checks that quoted
  evidence occurs verbatim. LeanFlow (arXiv:2607.20503) freezes statements once they pass a
  faithfulness check.
* **Weaker abc statements.** These give `Challenge.ABC` intermediate comparison targets: a
  fixed exponent (arXiv:2611.05217, Theorem B), explicit constants conditional on IUT
  (arXiv:2503.14510), and unconditional subexponential bounds.

**What it does not offer:**

* Among the papers read, the readings for this project found none that constructs the objects
  of Corollary 3.12 completely enough to state the corollary in Lean with every term defined.
* Each of the explicit papers states its results as conditional on Corollary 3.12 or on
  IUT IV.
* No arXiv paper in the corpus is a line-by-line response to the manuscript of Scholze and
  Stix, apart from Joshi's own tables (arXiv:2505.10568, Table 2).
* No formalization of any part of IUT was found on arXiv.

## 6. Limits of this survey

* Only arXiv was searched, apart from one supplied working paper. Journal-only papers,
  manuscripts on personal pages, and papers the search did not return (including the
  manuscript of Scholze and Stix and the explicit estimates paper cited above) are outside the
  corpus, except where a paper in the
  corpus quotes them.
* The search was retrieved on 2026-11-25. Later versions and later papers are not included.
* Screening used titles and abstracts only, so 115 included papers are described here only
  from their abstracts.
* 35 arXiv papers and the supplied working paper were read in part. Each record lists the
  sections read, and statements outside them were not checked.
* Readings used the TeX source or the PDF text. Rendered pages were consulted only for some
  of the second readings. Internal inconsistencies that only one reading reported are not
  published here.
* Relevance scores measure usefulness to this project, not the quality of a paper.
