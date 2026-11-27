# External formalization projects

This file records existing formal work related to the four IUT papers and to the abc conjecture,
what it claims, what it actually states in Lean, and what it trusts. Machine-readable data:
`data/external_projects.json`. Everything here was obtained on 2026-11-25 by reading the code at
the commits listed and by grepping. No external project was built: their toolchains (Lean
`v4.32.0`, `v4.33.1`) differ from ours (`v4.36.0`), and building them would require their own
Mathlib. Axiom claims of the external projects are therefore their own claims, not re-checked by
our kernel; our trust inventory is textual.

Primary source pages read for the comparison: IUT III, pages 153 to 159 (Theorem 3.11 and its
proof) and pages 173 to 174 (statement of Corollary 3.12 and the start of its proof). The
displays of pages 153, 154, 156, 173 and 174 were checked against rendered page images.

## 1. Summary

| Project | Commit | Date | License | Lean / Mathlib | Lean files | Claim inspected in source or reported by the project |
|---|---|---|---|---|---|---|
| `lana-agents/iut` | `b4a9966f` | 2026-11-22 | Apache-2.0 | `v4.32.0` / `v4.32.0` | 768 | a variant of IUT III Cor. 3.12 (assumed) implies classical abc |
| `LANA-Project/genl` | `6e9a6543` | 2026-07-19 | none in repository | `v4.32.0` / `v4.32.0` | 16 | [GenEll] Thm 2.1 (ii) implies (i), relative to abstract height data |
| `LANA-Project/iut4-sec1` | `a7551d2f` | 2026-07-20 | Apache-2.0 | `v4.32.0` / `v4.32.0` | 26 | elementary lemmas of IUT IV, Section 1 |
| `google-deepmind/formal-conjectures` | `9097e2f9` | 2026-11-24 | Apache-2.0 | `v4.33.1` / `v4.33.1` | 2199 | statements only (abc is stated, with `sorry`) |
| Mochizuki, "On the formalization of IUT" (slides) | file of 2026-04-07 | April 2026 | not stated | no code published | 0 | none (describes unpublished skeletal code) |

Full commits and Mathlib revisions are in the JSON file. The last column records what the source, read at the listed commit, states, or what the project reports; none of it was replayed by our kernel, since no external project was built. Independent replay of each project, and equivalence of its statements with the statements of the manuscripts (for example of the LANA variant of Corollary 3.12 with the paper's multiradial images and extended-real formulation), remain open.

## 2. `lana-agents/iut`

URL: <https://github.com/lana-agents/iut>. Commit `b4a9966ffe09b5019b57e05b2497972b22799e4a`
(2026-11-22). Apache-2.0. Lean `v4.32.0`, Mathlib tag `v4.32.0` (revision `81a5d257`). 768 Lean
files (752 in `Iut/`, 6 in `Iut4Sec1/`, comparator and script files), about 234,000 lines, plus 15
pinned dependencies of the `lana-agents` organization (about 4,400 Lean files, 1.26 million lines;
section 2.6). Its `formalization.yaml` records that the code was produced with automated
(machine-generated) assistance, that its review status is "agent-reviewed", and that it "has not
been reviewed by a human".

### 2.1 What it claims

The README (all 1102 lines read) and `formalization.yaml` (read in full) say plainly that the
repository does not verify IUT and does not prove abc. The main theorem is a conditional
implication:

```lean
def Iut.Cor312VariantHolds : Prop :=
  ∀ D : InitialThetaData.{0}, Corollary312Variant (concreteVariantData D)
theorem Iut.classicalABC_of_variant (h312 : Cor312VariantHolds) : ClassicalABC
```

(`Iut/Concrete/ThetaRegion.lean:375`, `Iut/MainTheorem.lean:36`), with claimed axioms `propext`,
`Classical.choice`, `Quot.sound`. The variant is called "project-owner-specified", is "deliberately
not identified with the published Corollary 3.12", and is never proved or assumed as an axiom.
A comparator challenge (`Comparator/Challenge.lean`) states `Cor312VariantHolds → ABC` with the
Formal Conjectures statement `ABC.abc` copied from their commit `1646ca16` (the file at that commit
is byte-identical to the one at `9097e2f9` that we use).

Other claims: Theorem 1.10 of IUT IV from the variant (`Iut.Theorem110Invariants.theorem110`), IUT
IV Corollaries 2.2 and 2.3, [GenEll] Theorem 2.1 (ii) implies (i) for the tripod, the identification
of the tempered group at the bad places with André's tempered group, Theorem B for the Tate curves
of the Θ-data, and a large body of supporting number theory (Serre's different bound, torsion of
Legendre curves, stable reduction, Chebyshev bounds). Recorded deviations: Proposition 1.6 of IUT
IV is used with factor `3/2` in place of the printed `4/3`; reduction predicates up to change of
variables; the cyclic subgroup bound of [GenEll] Lemma 3.5 weakened at the prime 2; two local
statements restricted to packets over `p`.

### 2.2 How Corollary 3.12 is stated

The chain of definitions, unfolded until Mathlib objects are reached:

* `Iut.Corollary312Variant X := X.qPilot.lhs ≤ X.rhsData.rhs`
  (`Iut/Cor312/Statement.lean:89`), for a bundle `Corollary312VariantData` of
  `D : InitialThetaData`, `QPilotData D`, `RHSData D` (`Statement.lean:68`).
* Left side (`Iut/Cor312/LeftHandSide.lean:81` to `93`): `lhs = −absLogQ`,
  `absLogQ = logQ / (2ℓ)`, `logQ = Σ_{w ∈ V(F)^bad} weight w · ord_w(q_w) · log p_w`.
  In the concrete instance (`ThetaRegion.lean:348`) `weight w = f_w / [F : ℚ]` and `q_w` is the
  Tate parameter of `E` at `w` (defined from `j(E)` in `tate-curves-theta`). This is a real number
  computed from the curve; the factor `1/2ℓ` is taken from the proof of IUT IV, Theorem 1.10.
* Right side (`Iut/Cor312/RightHandSide.lean:99`, `107`): `rhs = processionVol (hull (thetaPilot))`,
  the unweighted average over the `ℓ* = (ℓ − 1)/2` capsules (`Iut/Cor312/LogVolume.lean:207`) of
  global log-volumes of the holomorphic hull of a region in the container of tensor packets
  `⊗_j K_{v_j}` (Mathlib `PiTensorProduct` of completions, with normalized Haar measure).
* The region (`ThetaRegion.lean:170` to `183`, `273`): at a prime `p` and tuple `c` of places of
  `V ≅ V_mod`, `⋃_{φ ∈ indAut} φ(q_{v_j}^{j²} · ⊗_l 𝓘_{v_l})`, where `q_v` is a `2ℓ`-th root of
  the Tate parameter, `𝓘_v` the log-shell `(2p)⁻¹ log(𝒪_v^×)` (from `padic-log-volume`), and
  `indAut = tensorAut` (`Iut/Concrete/LocalConstruct/IndAut.lean:219`, `299`) is the set of
  tensor products `⊗ g_j` of arbitrary `ℚ_p`-linear automorphisms `g_j` of `K_{v_j}` that preserve
  the lattice `𝓘_{v_j}`. At the archimedean place: the unit ball of a tensor product Hermitian
  metric with sign and conjugation automorphisms. The label is `{j}` (`ivLabels`, line 237);
  a "literal" version over all labels, `Cor312LiteralHolds` (line 383), is implied by the variant
  (`Iut/Concrete/Literal.lean:115`).
* `InitialThetaData` (`Iut/Cor312/ThetaData/Basic.lean:81`) is a structure of genuine data:
  a number field `F`, an algebraic closure, a `WeierstrassCurve` with `IsElliptic`, a set of bad
  places of `F_mod`, and fields stating the conditions of IUT I, Definition 3.1, about Mathlib
  objects and about objects of the dependencies (`pi1`, `tempered-fundamental-groups`,
  `orbicurve-cores`).

So every term of `Cor312VariantHolds` is defined. It is not a statement about abstract
parameters: it is one concrete real inequality per initial Θ-datum.

### 2.3 Comparison with the original Corollary 3.12

IUT III, Corollary 3.12 (pages 173 to 174), in our reading: in the situation of Theorem 3.11
(initial Θ-data and a collection of distinct Θ^{±ell}NF-Hodge theaters arising from an
LGP-Gaussian log-theta-lattice), let `−|log(Θ)| ∈ ℝ ∪ {+∞}` be the procession-normalized
mono-analytic log-volume of the holomorphic hull of the union of the possible images of a Θ-pilot
object, relative to the Kummer isomorphisms of Theorem 3.11 (ii), in the multiradial representation
of Theorem 3.11 (i), subject to (Ind1), (Ind2), (Ind3); let `−|log(q)| ∈ ℝ` be the corresponding
log-volume of the image of a q-pilot object, not subject to the indeterminacies, with `|log(q)| > 0`.
Then `−|log(Θ)| ∈ ℝ` and `−|log(Θ)| ≥ −|log(q)|`.

Differences, each read off the code:

1. **Variant, not the original.** The inequality direction is the same (`−|log q| ≤ −|log Θ|`), but
   `−|log Θ|` is not defined as in the paper. In the paper it is the log-volume of a hull of
   possible images of the Θ-pilot under Kummer isomorphisms in the multiradial representation of
   Theorem 3.11; in `lana-agents/iut` it is the log-volume of a region written down directly from
   `D` (theta values `q^{j²}` acting on log-shells, closed under a chosen automorphism group). No
   Hodge theater, Θ-link, Kummer isomorphism, or multiradial algorithm enters the definition of
   `concreteVariantData`. The repository says the relation of this region to the paper's region "is
   documented per-module but not itself a theorem" (`Iut/Cor312/Statement.lean`, docstring).
2. **(Ind2)** is enlarged from independent copies of `Ism` (IUT III, Proposition 1.2 (vi)) to all
   lattice automorphisms of each factor log-shell; documented as making the region larger.
3. **(Ind1)** is read as in IUT IV, proof of Theorem 1.10, Steps (iv) to (v) (label `j` only), not
   as the union over the label permutations; the literal reading is a separate, weaker hypothesis.
4. **(Ind3)** is modeled by letting the theta value act on the log-shells rather than on the
   integral structure. The paper's (Ind3) is the upper semi-compatibility of the log-Kummer
   correspondence along the log-links (page 156).
5. The finiteness assertion `−|log(Θ)| ∈ ℝ` of the corollary is built into the type (the value is
   real by construction).
6. `|log(q)|` uses the normalization `(1/2ℓ) log(q)` from IUT IV; IUT III only says it "is easily
   computed in terms of the q-parameters".

**Hypotheses of the top-level theorems.** `Iut.classicalABC_of_variant` has exactly one hypothesis,
`h312 : Cor312VariantHolds`. All other inputs (tower arithmetic, curve facts, Chebyshev bounds,
existence of Θ-data for the Legendre curves) are discharged by closed terms in
`Iut/Tripod/Main.lean:120` to `132`. `h312` is not a restatement of abc: it is an inequality between
log-volumes of local objects, and the passage to abc goes through IUT IV Theorem 1.10, Corollaries
2.2, 2.3 and [GenEll] Theorem 2.1. It carries, however, all of the content that IUT III is supposed
to supply; the repository's own analysis (`Iut/WallEquiv/README.md`, `Iut/WallEquiv/NonDerivable.lean:548`,
`556`) proves that in its model of Theorem 3.11 the remaining step (Step (xi) of the proof of
Corollary 3.12) is equivalent to an inequality it names after Scholze and Stix, that this step is
not derivable from the fields of its Theorem 3.11 package, and that the step for all Θ-data implies
`ClassicalABC`. Whether `Cor312VariantHolds` is true is not known; if it were false the main
theorem would hold vacuously. Not checked by us: whether `InitialThetaData.{0}` is inhabited by a
term that the definitions intend (the repository constructs Θ-data for Legendre curves in
`Iut/Concrete/Existence.lean`).

### 2.4 How Theorem 3.11 is stated

`Iut.LogLink.Thm311 L K : Prop` (`Iut/LogLink/Thm311.lean:141`) is a structure with fields
`ind12`, `multiradial`, `upperSemi`, `logShell`, `volCompat`, `thetaCompat`, about a
`LogThetaLattice D` and "unit-induced" Kummer data `LatticeKummer L` of the repository's
multi-container model, and `thm311_model` (line 190) proves it for every lattice and every such
Kummer data. The Kummer identifications are scalings of the container (`model_transport`, line
170); the output of the multiradial algorithm is defined as `lgp D S` (`model_out`, line 167). This is
a model in which the paper's Frobenioids, Hodge theaters and Kummer theory are replaced by local
fields and a log-volume calculus; the repository says so. It is not IUT III, Theorem 3.11 as stated
on pages 153 to 158, whose objects (D-prime-strips, Θ^{±ell}NF-Hodge theaters, the splitting
monoids `Ψ^⊥_LGP`, global Frobenioids, the Kummer isomorphisms of [IUTchII] Corollaries 4.6 and
4.8) are not formalized there in the paper's sense. `XiPrinciple` (line 203) is Step (xi) as an
explicit hypothesis; `variant_of_thm311` (line 214) and `xi_iff_ss` (line 219) relate it to the
variant and to `SSIneq` (`Iut/Wall/MultiContainer.lean:88`).

### 2.5 Trust inventory of `lana-agents/iut`

Grep over all `.lean` files at `b4a9966f`:

| Keyword | Hits | Where |
|---|---|---|
| `axiom` declaration | 0 | |
| `sorry` | 1 | `Comparator/Challenge.lean:76`, the comparator placeholder (not in a library) |
| `admit`, `unsafe`, `native_decide`, `implemented_by`, `extern`, `partial def` | 0 | |
| `opaque` declaration | 0 | 7 occurrences of the word, all in comments |
| `run_cmd`, `#eval` | 5 | `scripts/Audit*.lean`, `scripts/ShellLint.lean` (check scripts, not library) |
| custom syntax | 1 | tactic macro `circ_ring` in `Iut/Frobenioid/Angular/Category.lean:50` |

Structures and predicates that carry mathematical claims: 18 `Prop`-valued structures and about 24
named hypotheses (`*Hyp`, `*Holds`, `XiPrinciple`, `SSIneq`). For the main theorem all except
`Cor312VariantHolds` are discharged by theorems (for example `Iut.Tripod.towerLocalHyp`,
`cyclicBoundOdd`, `primeCountingHyp_holds`, `northcottHyp`). `Iut.Tripod.CyclicGraphBoundHyp`
(`Iut/Tripod/CyclicBound.lean:239`) is an unused, unproved `Prop`. Statements named after theorems
of the papers that are proved only in a model or as variants: `Corollary312Variant`, `Thm311`,
`Thm311LGP`, `Thm311iii`, `Iut.Theorem110Invariants.theorem110` (conditional on the variant and
with the factor `3/2`).

### 2.6 Dependencies (transitive)

Pinned in `lake-manifest.json`; downloaded at the pinned revisions to a local, untracked
directory and grepped. All carry a LICENSE file.

| Package | Revision | Files | Lines | Findings |
|---|---|---|---|---|
| tempered-fundamental-groups | `c8e4b854` | 1049 | 297,454 | no axiom, no sorry (1 hit in a comment) |
| oka | `7f2a6241` | 831 | 250,299 | no axiom declaration (12 hits in prose); 1 `#eval` in a docstring; tactic macros |
| formal-schemes | `e58ecf04` | 652 | 182,967 | clean; `run_cmd` only in `scripts/` |
| curves-jacobian | `cb06131f` | 592 | 174,901 | clean |
| elliptic-curves | `e70086a9` | 483 | 161,481 | clean (axiom, sorry, opaque hits are prose) |
| belyi | `7206d783` | 157 | 30,978 | clean |
| orbicurve-cores | `d08559e6` | 135 | 30,900 | clean |
| local-class-field-theory | `a6655a87` | 122 | 32,347 | clean; tactic macro |
| pi1 | `ed24c6c7` | 115 | 30,054 | clean; tactic macro |
| tate-curves-theta | `d1fba948` | 79 | 22,657 | clean (sorry hits are prose) |
| heights | `f4379dbc` | 68 | 19,095 | 6 `sorry` in `Comparator/Challenge.lean` only |
| weil-curves | `1cadab4e` | 50 | 11,716 | clean |
| continuous-kummer-theory | `1d5194fc` | 39 | 8,969 | clean |
| genl (lana-agents fork) | `179e26f6` | 12 | 2,143 | 1 `sorry` in `Challenge.lean` only |
| padic-log-volume | `9a190da2` | 3 | 808 | clean |

Note: the README's pin table names older revisions (for example `tempered-fundamental-groups`
`a2415c1`) than `lakefile.toml` and `lake-manifest.json`; the manifest is authoritative.

### 2.7 Reusable parts

Candidates to reuse after porting to Lean `v4.36.0` and checking statements: the number theory
in `Iut/Tower/` (Serre's different bound `Iut.Serre.not_pow_dvd_differentIdeal`, ramification in
towers), `Iut/Torsion/` (division polynomials, `E[n] ≅ (ℤ/n)²` over algebraically closed fields of
characteristic 0), `Iut/Implication/ChebyshevExplicit.lean`, `Iut/NumberTheory/` (rational six
exponentials theorem, linear independence of logarithms of primes), the formal-conjectures
equivalences in `Iut/Abc/FormalConjectures.lean`, the tensor-packet log-volume construction in
`Iut/Concrete/LocalConstruct/`, and the Θ-data record as one reading of IUT I, Definition 3.1 (to be
compared with our own extraction). The Corollary 3.12 strand and the model of Theorem 3.11 are not
reusable as statements of the papers; they can serve as a documented alternative interpretation.

## 3. `LANA-Project/genl`

URL: <https://github.com/LANA-Project/genl>. Commit `6e9a6543b46a2a02fd7fe7ec8ab203d878f32859`
(2026-07-19). No LICENSE file in the repository; the organization listing reports no license.
Lean `v4.32.0`, Mathlib `v4.32.0` (`81a5d257`). 16 Lean files, 1335 lines (plus a blueprint).

Claim: [GenEll] Theorem 2.1, (ii) implies (i), relative to an abstract `Genl.HeightTheory`
(`Genl/GeneralPosition/HeightTheory.lean:57`: a structure whose fields are a type of curves, types of
points, real-valued `htCan`, `logDiff`, `logCond`, and so on, with no connection to Mathlib curves)
and a `ProofPackage` (`Genl/GeneralPosition/ProofPackage.lean:158`) whose fields `covering` and
`belyi` are the arithmetic-geometric inputs of the proof (ramified coverings and noncritical Belyi
maps with height estimates). These are hypotheses carrying mathematical claims, bundled in
structures; the theorem is about abstract parameters. Trust grep: one `sorry` in `Challenge.lean:27`
(comparator placeholder); nothing else. The `lana-agents/genl` fork used by `lana-agents/iut`
(`179e26f6`) adds a concrete height theory of curves (`Genl.Curves`) consumed for the tripod.

## 4. `LANA-Project/iut4-sec1`

URL: <https://github.com/LANA-Project/iut4-sec1>. Commit
`a7551d2f575b7e462cf9e82c587d9c6308e7b15c` (2026-07-20). Apache-2.0. Lean `v4.32.0`, Mathlib
`v4.32.0`. 26 Lean files, 2526 lines. Merged into `lana-agents/iut` as `Iut4Sec1/` (one file,
`Real/LogError.lean`, differs). Claims: the real-arithmetic error bound used in IUT IV Proposition
1.4 (iii), the weighted-average identity of Proposition 1.7, the range identities (E1), (E2), and
arithmetic-divisor foundations of Definition 1.9 (i); it states it does not claim Definition 1.9
(ii). Trust grep: 10 `sorry`, all in `Comparator/Challenge.lean` (comparator placeholders); no
axioms. Overlaps our `IUT/PaperIV/ArithmeticDivisor.lean` and `IUT/PaperIV/Theorem1_10/Arithmetic.lean`.
The organization `LANA-Project` has a third public repository, `.github` (profile only).

## 5. `google-deepmind/formal-conjectures`

URL: <https://github.com/google-deepmind/formal-conjectures>. Commit
`9097e2f90e66d2f6244209cb1c07f7120d17ec53` (2026-11-24). Apache-2.0. Lean `v4.33.1`, Mathlib
`v4.33.1` (`0df444a3`). 2199 Lean files. A statement repository: 5510 `sorry`, 107
`native_decide`, one `axiom` (`FormalConjecturesTest/Util/Linters/StubLinter.lean:39`, a linter
test). `FormalConjecturesForMathlib/` has no `sorry`.

`FormalConjectures/Wikipedia/ABC.lean` (read in full) defines `ABC.radical n = n.primeFactors.prod
id`, `ABC.quality a b c = log c / log (radical (a*b*c))`, and three open theorems: `ABC.abc`
(finiteness, pairwise coprimality of `{a, b, c}`), `ABC.abc.variants.lt_constant_mul` (`∃ K`, no
sign condition, strict `<`), `ABC.abc.variants.quality` (finiteness of quality `> 1 + ε`).

Comparison with `Challenge.ABC`: `IUT/Applications/ABCFormalConjectures.lean` restates the three as
`Prop` definitions and proves `abc_iff_ABC`, `ltConstantMul_iff_ABC`, `qualityVariant_iff_ABC`
(standard axioms only). All three are exactly equivalent to `Challenge.ABC`. Details: positivity of
`K` is forced by the triple `1 + 1 = 2`; strict and non-strict constant forms are equivalent by
replacing `K` with `K + 1`; in the quality form the radical of `abc` is at least 2 on every triple
with `a, b > 0` and `a + b = c` (the radical is 1 only when `abc = 1`, i.e. `a = b = c = 1`, which
violates `a + b = c`), so the division by `log 1 = 0` never occurs and the quality set equals the
finiteness set for each `ε`.

## 6. Mochizuki's 2026 work on formalizing IUT

Pages and queries tried (2026-11-25):

* <https://www.kurims.kyoto-u.ac.jp/~motizuki/papers-english.html> (last modified 2025-03-16): no
  formalization item; newest papers entry dated 2025-03-16.
* `top-english.html`, `news-english.html` (last modified 2026-04-07), `research-english.html`,
  `thoughts-english.html`, and the Japanese counterparts. The news page has the entry
  "2026-04-08: Posted the slides for my talk at a workshop 'Workshop on AI and Theorem Provers in
  Mathematics'", and "2025-10-26: Posted a report concerning the current situation surrounding
  inter-universal Teichmuller theory". The research page links both.
* Web searches: "Mochizuki 2026 Lean formalization IUT Corollary 3.12"; "Formalization of IUT
  Mochizuki preliminary progress report Hoshi Yamashita Lean".

Found and opened:

1. **S. Mochizuki, "On the formalization of IUT: a preliminary progress report [joint work in
   progress with Y. Hoshi, G. Yamashita, Y. Yang, ...]"**, slides, April 2026, 14 pages,
   <https://www.kurims.kyoto-u.ac.jp/~motizuki/Formalization%20of%20IUT%20(2026-04).pdf>
   (server date 2026-04-07; SHA-256 `9a32b248...72ee9c`; talk at the online Workshop on AI and
   Theorem Provers in Mathematics, 8 to 10 April 2026, <https://aitpm.github.io/>). Read in full.
   Contents: Lean formalization viewed mainly as a communication tool; a five-stage plan (Stage 1:
   IUT III Theorem 3.11 implies Corollary 3.12; Stage 2: Theorem 3.11 modulo IUT I and II; Stages 3
   to 5: earlier anabelian work and the numerics of IUT IV), stating that the project is "in the
   early skeletal portion of Stage 1"; a discussion of species and mutations and of formalizing ZFC
   as a first-order theory (judged not necessary for Stages 1 and 2); a review of IUT through a toy
   gluing of two copies of an integral domain along the `N`-th power map; and in §4 a description
   (a diagram, no code) of "skeletal Lean code for 3.11.5 ⇒ 3.12". There "3.11.5" is a
   reorganization "(= 3.11 + Rmk. 3.9.5)" that, as the slides say, never appears in IUT I to IV; the
   implication 3.11 ⇒ 3.12 is decomposed into four commuting triangles (a multiradial algorithm
   with input a basic prime-strip "BPS", a descent arrow (dsc), a "hull+det" step, and a
   "simultaneous holomorphic expressibility" arrow (SHE) for the q-pilot), with properties called
   input prime-strip link (IPL) and algorithmic parallel transport (APT). The skeletal code concerns
   the fourth triangle ("3.11.5 ⇒ 3.12"); code for the second and third is in progress. The slides
   state that the code is not yet suitable for release to the public. **No Lean code is published**;
   we found no repository.
2. **S. Mochizuki, "Report on the current situation surrounding inter-universal Teichmüller theory
   (IUT)"**, October 2025, 30 pages, <https://www.kurims.kyoto-u.ac.jp/~motizuki/IUT-report-2025-10.pdf>.
   Read: contents and §3.2 (pages 26 to 30). §3.2 describes Lean formalization activity at RIMS,
   states that efforts "have only just begun" and will take "at least several more years", and
   proposes reorganizing IUT into blackboxes plus purely formal arguments ((MthFm), (BBxFm)). No
   Lean code.

Read from its TeX source: **Project LANA (F. Kato, J. Commelin, Y. Hoshi, K. Kedlaya, A. Topaz),
"Project LANA Interim Report on IUT Theory"**, July 2026, GitHub repository
`katobungen/LANA_report_202607` at commit `293bdd8` (the repository has no license file); a PDF
is at <https://ncatlab.org/nlab/files/LANAProject-Report-July2026.pdf>. Read: sections 1.2, 1.3,
5 and 9 to 11, and the further sections listed in the records of the model module. No Lean code is
published with the report. Its main goal (section 10.2) is to show that there exists a suitable
`S` with `η^q = η^anab_S`. Both are isomorphisms of pointed real lines from `ℝ^val`, the line of
the value-group portion of a basic prime strip, to `ℝ^ss`, the classes of adelic measurable
subsets of a volume container up to equal volume. The first comes from the q-pilot; the second
from an action of `ℕ` on the volume container, obtained by anabelian steps after an isomorphism
to the Θ-pilot strip of a Hodge theater is fixed, together with a subset `S` taken as the
integral structure. The report describes those anabelian steps in outline only. In section 11
the report agrees with Scholze and Stix that their hexagon does not commute, states that its own
analysis does not give rise to that diagram, and states: "we, the LANA project, do not have a
proof of [the main goal] at this time." The report's simplified objects are modeled in
`IUT/Audit/LANA/EtaGoal.lean`, with the main goal as a schema whose action is data. This is the
report cited as "[LANA]" in `lana-agents/iut/Iut/WallEquiv/README.md`.

Downloaded copies are kept in a local, untracked directory; the URLs above are the sources.

## 7. Mathlib

Our project uses Mathlib `v4.36.0`; the LANA projects use `v4.32.0`. Mathlib provides the radical
(`UniqueFactorizationMonoid.radical`, `Nat.radical_eq_prod_primeFactors`, used in
`IUT/Applications/ABC.lean`), number fields and their places, adic completions, `PiTensorProduct`,
Haar measure, and Weierstrass curves. It has no anabelian geometry, Frobenioids, Hodge theaters,
or tempered fundamental groups.
