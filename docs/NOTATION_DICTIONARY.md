# Notation dictionary

This file merges the four per-paper dictionaries by topic. Each symbol is listed with the paper
and the page where it is defined or first fixed. Page numbers are those of the author
manuscripts listed in `docs/SOURCE_MANIFEST.md` (IUT I May 2020, IUT II December 2020, IUT III
May 2020, IUT IV April 2020), not the journal pages.

The per-paper files remain the reference: they record which entries were checked against a
rendered page and which were read from the extracted text only.

* [IUT I](notation/IUT1.md)
* [IUT II](notation/IUT2.md)
* [IUT III](notation/IUT3.md)
* [IUT IV](notation/IUT4.md)

When an entry here and a per-paper file differ, the per-paper file is the one that was checked.

## Symbols used differently across papers

| Symbol | Uses | Where |
|---|---|---|
| `l*`, `l^⋇` | The same number `(l − 1)/2`, written with an asterisk in IUT I and IUT IV and with a six-pointed star in IUT II. IUT III uses it as the largest label of `F*_l`. | IUT I 95; IUT II 3; IUT III 173; IUT IV 27 |
| `p_v` at archimedean `v` | IUT I: a positive real with `log p_v = 1`. IUT II: `p_v = e`. These agree; the two descriptions are worded differently. | IUT I 36; IUT II 129 to 131 |
| `V` | IUT I to III: the chosen set of places of `K` from the initial Θ-data. IUT IV Proposition 1.5: a finite set of archimedean data. IUT IV §3: a Grothendieck universe. | IUT I 62 to 63; IUT IV 15, 67 |
| `C_K` | IUT I: the orbicurve of type `(1, l-tors)_±`. IUT IV §2: a constant depending on `K_V`. | IUT I 62; IUT IV 42 to 47 |
| `φ` | IUT III Remark 3.9.5: the hull map `ℙ → ℍ`. IUT IV Proposition 1.2: an automorphism of `R_I ⊗ ℚ_p`. | IUT III 127; IUT IV 10 |
| `ε` | IUT I: the cusp of `C_K` in the initial Θ-data. IUT IV §2: the exponent of Theorem A and Corollary 2.2. | IUT I 63; IUT IV 42 |
| `A` | IUT III: a set of labels of a tensor packet. IUT IV Proposition 2.1 and Corollary 2.2: a finite set of primes. | IUT III 92 to 93; IUT IV 40, 44 |
| `E` | IUT I: the elliptic curve `E_F`. IUT IV Proposition 1.7: a finite set with weights. | IUT I 61; IUT IV 16 to 17 |
| `I` | IUT III: log-shells `I_{†F_v}`. IUT IV §1: a finite index set of local fields. | IUT III 24; IUT IV 9 |
| `ξ` | IUT II: a value profile. IUT IV: the threshold `ξ_prm` of Proposition 2.1. | IUT II 94; IUT IV 40 |
| Value sets | IUT III Corollary 3.12 uses `ℝ ∪ {+∞}` for `−|log(Θ)|`; Remark 3.9.4 uses `ℝ ∪ {−∞}` for log-volumes of `Rss`, and Remark 3.9.7 allows `−∞` for volumes defined by infima. The quantities differ; the papers do not reconcile the conventions. | IUT III 124, 145 to 147, 173 to 174 |
| `log(q)` | IUT III: `ord_v(q_v)·log(p_v)` at one place. IUT IV: `log(𝔮)`, the normalized log of the arithmetic divisor of `q`-parameters. | IUT III 124; IUT IV 23 |

## Conventions and decorations

The extracted text of the PDFs loses decorations. The per-paper files restore them from renders.

| Symbol | Meaning | Paper and page |
|---|---|---|
| underline under `v` | element of the chosen set `V ⊆ 𝕍(K)` | IUT I (conventions table) |
| double underline on `q`, `Θ`, `F_v`, `X_v` | objects at a bad place (tempered covering, Frobenioid, `q`-parameter) | IUT I 69 to 71 |
| left superscript `†`, `‡`, `∗` | label of a copy | IUT I, Remark 3.6.1 |
| `^⊢`, `^⊩` | mono-analytic version; realified global version | IUT I (conventions table) |
| `^⊛`, `^⊚` | global objects | IUT I, Definition 4.1 and Example 5.1 |
| `⌈x⌉`, `⌊x⌋` | ceiling and floor, dropped in the extracted text | IUT IV 10, 13, 27 |
| `∉`, `≠` | dropped or misread in the extracted text | IUT IV 22, 25, 40, 46; IUT III 174 |
| underlined `deg` | normalized degree | IUT IV 21 |

## The Tate parameter, its root, the q-pilot, and the indices

The papers use one letter for several related objects; a formalization must keep them apart.
Checked against the rendered IUT I page 71, IUT II page 72 and IUT IV page 23; the Scholze and
Stix manuscript, page 3, uses the same normalization.

| Object | Definition | Relation | Where |
|---|---|---|---|
| Tate parameter `q_v` (single underline under `v`) | the `q`-parameter of `E_v` over `K_v`, an element of `O^▷` | `q_v = qq_v^{2l}` | IUT I 71 |
| chosen root `qq_v` (`q_v` with a double underline) | `q_v^{1/2l}`; exists by Definition 3.1 (b), (c); determined only up to a `μ_{2l}`-multiple; it is the value of `Θ_v` (double underline; the reciprocal of an `l`-th root of the theta function, IUT I 70) at `√(−q_v)` | `qq_v^{2l} = q_v` | IUT I 71 |
| theta value at label `j` | the `μ_{2l}`-orbit of `qq_v^{j²}`, for `j ∈ {0, 1, …, l*}` determined by `j ∈ \|F_l\|` | `qq_v^{j²} = q_v^{j²/2l}` (Tate parameter `q_v`) | IUT II 72 |
| q-pilot | built from `qq_v`, not from the Tate parameter `q_v` | its absolute log-volume is `\|log(q)\| = (1/2l)·log(𝔮)` | IUT IV 23 |
| `log(𝔮)` | normalized degree of the effective arithmetic divisor of the Tate parameters at the bad places | no `1/2l` factor | IUT IV 23 |
| `deg(q_E)`, `deg(q̲_E)` | Scholze and Stix: the arithmetic divisor of the Tate parameters, and of the chosen roots | `deg(q̲_E) = deg(q_E)/(2ℓ)` | SS 2 to 4 |

So a quantity written with `q` must say whether it is the Tate parameter or the chosen root: the
two differ by the exponent `2l` (by `1/2l` on log-volumes), and the theta values carry the
exponent `j²` on the root, not on the Tate parameter. The symbol `qq_v` for the double-underlined
`q` is the one used in `docs/notation/IUT2.md`.

**Packet and procession indices.** The labels are `|F_l| = {0} ⊔ F*_l`, identified with
`{0, 1, …, l*}` (IUT II 3; IUT III 153 to 154). The procession at label `j` uses the capsule
index set `S^±_{j+1} = {0, …, j}` of `j + 1` elements (IUT III 120, 153; IUT IV 27), and the
tensor packet over a label set `A` is `log(^A F_{v_ℚ})` (IUT III 92 to 99). The averaging
index of the procession-normalized log-volume is written `F*_l` on IUT III pages 173 and 181 and
`|F_l|` on pages 153, 174 and 183 (ambiguity A1 of `OPEN_PROBLEMS.md`); the two differ by the
label `0`. The theta exponent `j²` uses the representative `j ∈ {0, …, l*}`.

## Category-theoretic vocabulary (IUT I §0)

| Symbol | Meaning | Paper and page |
|---|---|---|
| poly-morphism, poly-isomorphism | a set of morphisms; a set of isomorphisms | IUT I 33 |
| full poly-isomorphism `A ⥲ B` | the set of all isomorphisms `A ⥲ B` | IUT I 33 |
| capsule `{A_j}_{j∈J}`, `Capsule(C)` | finite family of objects and its category | IUT I 33 to 34 |
| capsule-full poly-morphism | all morphisms of capsules over a fixed injection | IUT I 34 |
| `B(X)`, `B(X)^0`, `B^temp(Π)` | finite étale coverings, connected objects, tempered `Π`-sets | IUT I 34 |
| connected temperoid, `π_1(C)` | [SemiAnbd] Definition 3.1; reconstructed group | IUT I 34 to 35 |
| NF, MLF, CAF | number field; mixed characteristic local field; complex archimedean field | IUT I 35 |

## Labels and arithmetic of `l`

| Symbol | Meaning | Paper and page |
|---|---|---|
| `l` | prime `≥ 5` fixed in the initial Θ-data; `l ≠ 5` by Definition 3.1 (c) | IUT I 3, 61 |
| `l* = (l − 1)/2`, `l^± = (l + 1)/2` | label counts | IUT I 95, 162; IUT II 3 |
| `F*_l = F_l^×/{±1}`, `F_l^{⋊±} = F_l ⋊ {±1}` | label groups | IUT I 95, 155; IUT II 3 |
| `\|F_l\| = F_l/{±1} = {0} ⊔ F*_l` | labels `0, …, l*` | IUT II 3; IUT III 153 to 154 |
| `LabCusp(D_v)`, `LabCusp^±` | label classes of cusps | IUT I 97, 158 to 159; IUT II 67 to 68 |
| `\|Γ′\|`, `‖Γ′‖` | classes hit by a subgraph; normalized sum of minimal squares | IUT II 79 |
| `S^±_{j+1} = {0, …, j}` | capsule index set at label `j` | IUT III 120, 153; IUT IV 27 |
| `△` | identification of the labels `0` and `⟨F*_l⟩` | IUT III 174 (citing IUT II Corollary 4.10 (i)) |

## Places and fields

| Symbol | Meaning | Paper and page |
|---|---|---|
| `𝕍(F) = 𝕍(F)^arc ⊔ 𝕍(F)^non` | places of a number field | IUT I 35 |
| `F_v`, `L_v`, `p_v` | completion; completion of a Galois extension; residue characteristic | IUT I 35 to 36 |
| `(F̄/F, X_F, l, C_K, V, V^bad_mod, ε)` | initial Θ-data | IUT I 61 |
| `F_mod`, `F_sol`, `V_mod` | field of moduli, maximal solvable extension, its places | IUT I 61 |
| `K` | field cut out by the kernel of `G_F → GL_2(F_l)` | IUT I 62 |
| `V`, `V^bad`, `V^good` | section of `𝕍(K) → V_mod` and its parts | IUT I 62 to 63 |
| `V_ℚ`, `v_ℚ`, `v \| v_ℚ` | places of `ℚ` | IUT III 89 |
| `F_mod ⊆ F_tpd ⊆ F ⊆ K` | field of moduli, tripodal field, `F_tpd(√−1, E[15])`, `F(E[l])` | IUT IV 22 |
| `d_mod`, `e_mod`, `d*_mod`, `e*_mod` | degree and ramification of `F_mod`, times `2¹²·3³·5` | IUT IV 22 |
| `𝕍_ℚ^dst`, `ι_{v_ℚ}`, `l*_mod` | distinguished places, indicator, `log(e*_mod·l)` | IUT IV 25 to 28 |

## Groups, cyclotomes and Kummer theory

| Symbol | Meaning | Paper and page |
|---|---|---|
| `G_F`, `Π_{X_F}`, `Δ_X` | Galois group; arithmetic and geometric fundamental groups | IUT I 61 to 62 |
| `Π_v`, `Π^±_v`, `Π^cor_v` | tempered groups at bad `v` | IUT I 63; IUT II 67 to 68 |
| `(l·Δ_Θ)(Π)`, `Π_μ(M^Θ_*)` | interior cyclotome; cyclotome of the mono-theta environment | IUT II 46 to 47 |
| `μ_Ẑ(G)`, `Ism(G)` | cyclotome of `G`; compact group of isometries of `O^{×μ}(G)` | IUT II 39, 49; IUT III 32 |
| `(∗^{mono-Θ}_Π)`, `(∗bs-Gal)` | mono-theta and base-field cyclotomic rigidity | IUT II 47, 49 |
| `×`-, `×μ`-Kummer structure | orbits of isomorphisms of unit monoids | IUT II 153 to 154 |
| `κ_v` | Kummer structure at archimedean `v` | IUT I 80 to 81 |

## Frobenioids, monoids and theta objects

| Symbol | Meaning | Paper and page |
|---|---|---|
| `F_v`, `C^⊢_v`, `C^Θ_v`, `τ^⊢_v`, `F^⊢_v` | tempered Frobenioid; split Frobenioids and splittings | IUT I 69 to 73, 78, 81 |
| `Θ_v` (double underline) | reciprocal of the theta function | IUT I 70 to 71 |
| `q_v` (single underline under `v`), `qq_v` (`q_v` with a double underline) | the Tate parameter; its chosen `2l`-th root `q_v^{1/2l}`, determined up to a `μ_{2l}`-multiple (see the reconciliation below) | IUT I 71; IUT III 112 |
| `C^⊩_mod`, `ρ_v` | global realified Frobenioid; normalization of `log(p_v)` | IUT I 84 to 85 |
| `O^×(G)`, `O^μ(G)`, `O^{×μ}(G)`, `O^▷(G)` | monoids attached to `G` | IUT II 36 to 38, 153 |
| `θ(Π)`, `θ^{\|t\|}`, `θ^{\|t\|}_env` | étale theta classes and evaluated orbits | IUT II 55 to 58, 71, 81 to 83 |
| `qq_v^{j²}` | theta value at label `j`: the `j²`-th power of the chosen root `qq_v`, that is `q_v^{j²/2l}` with `q_v` the Tate parameter | IUT II 72; IUT III 173 |
| `Ψ_cns`, `Ψ_ξ`, `Ψ_gau`, `Ψ_env` | constant, Gaussian and theta monoids | IUT II 93 to 95, 120 to 122 |
| `Ψ_{F_LGP}`, `Ψ^⊥_{F_LGP}`, `Ψ^⊥_{F_lgp}` | LGP-monoids and splitting monoids | IUT III 101 to 105, 112 |
| `F_MOD`, `F_mod`, `F^R_MOD`, `C^⊩_LGP`, `C^⊩_△` | global Frobenioids | IUT III 106 to 112 |
| `log(p_v)`, `log(Θ)` | distinguished element; formal symbol | IUT II 121 to 122 |

## Prime-strips, Hodge theaters and links

| Symbol | Meaning | Paper and page |
|---|---|---|
| `HT^Θ`, Θ-link | Θ-Hodge theater; full poly-isomorphism `†F^⊩_tht ⥲ ‡F^⊩_mod` | IUT I 87 to 88 |
| `F^⊩_mod`, `F^⊩_tht` | q-pilot and Θ-pilot data | IUT I 85 to 86 |
| D-, D^⊢-, F-, F^⊢-, F^⊩-prime-strip | collections of local data indexed by `V` | IUT I 95 to 96, 134 to 143 |
| `F^{⊢□}`, `F^{⊩▶×μ}`-prime-strip, pilot object | Kummer-theoretic prime-strips | IUT II 158 |
| NF-bridge, Θ-bridge, ΘNF-Hodge theater | IUT I Definition 5.5 | IUT I 151 to 153 |
| Θ^±-bridge, Θ^ell-bridge, Θ^{±ell}NF-Hodge theater | IUT I Definitions 6.11 and 6.13 | IUT I 172 to 173, 182 |
| `Prc(n,◦D^⊢_T)` | procession of D^⊢-prime-strips | IUT III 153 (citing IUT I Proposition 6.9 (ii)) |
| `Θ^{×μ}`, `Θ^{×μ}_gau` | horizontal links | IUT II 160; IUT III 45 |
| `Θ^{×μ}_LGP`, `Θ^{×μ}_lgp` | links relative to a log-link | IUT III 113 |
| log-link `†F →^{log} ‡F` | tautological log-link post-composed with a poly-isomorphism | IUT III 24, 27 |
| `n,m HT^{Θ±ellNF}`, `(n,m)` | Hodge theater at a lattice position | IUT III 45 |
| `n,◦` | vertically coric object of column `n` | IUT III 48, 153 |

## Log-shells, log-volumes and hulls (IUT III, IUT IV)

| Symbol | Meaning | Paper and page |
|---|---|---|
| `p*_v`, `I_{†F_v}` | `p_v` or `p_v²`; log-shell | IUT III 24 to 25 |
| `log(^A F_{v_ℚ})`, `I^ℚ(−)` | tensor packet; ℚ-span of its integral structure | IUT III 92 to 99, 117 |
| `I(S^±_{j+1}; n,◦D^⊢_{v_ℚ})` | mono-analytic integral structures | IUT III 153; IUT IV 27 |
| `M(−)` | compact open subsets (closures at archimedean places) | IUT III 115 to 116 |
| `μ^log`, procession-normalization | packet-normalized log-volume; average over capsules | IUT III 115 to 117; IUT IV 13 |
| `Sub`, `Fn`, `Rss` | pre-ample subsets, functions, quotient | IUT III 120 |
| holomorphic hull, `ℙ`, `ℍ`, `φ` | smallest `λ·O` containing a region; hull map with (P1) to (P3) | IUT III 127 |
| `n,◦U`, `n,◦U^ℚ`, `n,◦Ū` | unions of possible images, ambient packets, hulls | IUT III 174 |
| `−\|log(Θ)\| ∈ ℝ ∪ {+∞}`, `−\|log(q)\| ∈ ℝ` | the two log-volumes of Corollary 3.12 | IUT III 173 to 174 |
| `C_Θ` | a real with `−\|log(Θ)\| ≤ C_Θ·\|log(q)\|` | IUT III 174; IUT IV 23 |
| `R_{≤−\|log(Θ)\|}` | reals at most `−\|log(Θ)\|` | IUT III 183 |
| (Ind1), (Ind2), (Ind3) | indeterminacies of Theorem 3.11 | IUT III 154, 156 |
| IPL, SHE, APT, HIS | properties named in Remark 3.11.1 | IUT III 160 to 162 |

## Local and global estimates (IUT IV)

| Symbol | Meaning | Paper and page |
|---|---|---|
| `k_i`, `R_i`, `e_i`, `𝔡_i`, `R_I`, `(R_I)^∼` | local fields, integers, ramification, different, tensor product, normalization | IUT IV 9 |
| `a_i`, `b_i`, `λ`, `I*`, `m_i` | exponents of Propositions 1.2 to 1.4 | IUT IV 10 to 13 |
| `p_n`, `π(η)`, `η_prm` | primes, prime counting, threshold of Proposition 1.6 | IUT IV 16 |
| `λ_e`, `β_e`, `β_avg` | weights and averages of Proposition 1.7 | IUT IV 16 to 17 |
| `ADiv_ℝ(F)`, `deg_F`, `deg_E` | arithmetic divisors and degrees | IUT IV 21 to 22 |
| `log(𝔡^{F□})`, `log(𝔣^{F□})`, `log(𝔮)` | normalized log-different, log-conductor, log of `q` | IUT IV 22 to 23 |
| `θ(x)`, `θ_A`, `ξ_prm` | Chebyshev function and threshold of Proposition 2.1 | IUT IV 40 |
| `ht`, `log-diff_X`, `log-cond_D`, `≲` | heights and bounded discrepancy | IUT IV 41, 55 |
| `K_V`, `Exc_d`, `ε_E`, `H_unif` | compactly bounded set, exceptional sets, error term, constant | IUT IV 41 to 47 |

## Set theory (IUT IV §3)

| Symbol | Meaning | Paper and page |
|---|---|---|
| Grothendieck universe, `(†^G)` | transitive set closed under the listed operations; every set lies in one | IUT IV 67 to 68 |
| species, specimen, mutation | formulas for objects and morphisms, and maps between them | IUT IV 68 to 74 |
| core, coricity | observable whose edge morphisms are isomorphisms | IUT IV 74 |

The Lean counterparts of the universe axioms are in `IUT/Foundations/GrothendieckUniverse.lean`
(`IsGrothendieckUniverse`, `ExistenceAxiom`). Species and mutations are not formalized.
