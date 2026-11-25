# Notation of IUT IV

Source: Mochizuki, *Inter-universal Teichmüller Theory IV* (April 2020 manuscript). Each entry
gives the PDF page where the notation is introduced. Rendered pages checked: 3, 10 to 17, 21 to
31, 40 to 48, 54, 55, 67, 68. Other pages were read in the extracted text only.

## Decorations lost in the extracted text

| Written here | In the paper | Meaning |
|---|---|---|
| `⌈x⌉`, `⌊x⌋` | ceiling, floor | dropped in the text of pages 10, 13, 27; restored from the renders |
| `∉` | not-in | read as `∈` in the text of pages 25 and 40; the renders show `∉` |
| `≠` | not-equal | lost in the text: page 22 reads `l = 5` and page 46 reads `V^bad_mod = ∅`; the renders show `l ≠ 5` and `≠ ∅` |
| `deg` with underline | underlined `deg` | normalized degree (page 21); the numerator of `deg_E` (page 22) is not underlined |
| `v` with underline | underlined `v` | element of `𝕍 ≅ 𝕍_mod` (IUT I) |
| `q` with double underline | double underline | `q`-parameter at a bad valuation (IUT I Example 3.2 (iv)) |
| `^∼` | tilde | normalization of a ring (Proposition 1.1) |
| `l*`, `e*_mod`, `d*_mod`, `ε*_d` | star | written `*` here |

## Section 1: local estimates (pages 9 to 40)

| Notation | Page | Meaning |
|---|---|---|
| `k_i`, `R_i = 𝒪_{k_i}`, `e_i`, `f_i`, `𝔪_i` | 9 | finite extensions of `ℚ_p`, their rings of integers, ramification index, residue degree, maximal ideal |
| `𝔡_i` | 9 | order of the different of `k_i` over `ℚ_p`, in `(1/e_i)ℤ` |
| `I`, `R_I = ⊗_{i∈I} R_i`, `𝔡_I = ∑ 𝔡_i` | 9 | finite index set; tensor product over `ℤ_p`; total different |
| `(R_I)^∼` | 9 | normalization of `R_I` in `R_I ⊗ ℚ_p` |
| `a_i`, `b_i`, `a_I = ∑ a_i`, `b_I = ∑ b_i` | 10 | exponents bounding `log_p(R_i^×)` (Prop 1.2) |
| `log_p` | 10 | `p`-adic logarithm |
| `φ` | 10 | automorphism of `R_I ⊗ ℚ_p` preserving `log_p(R_I^×)` |
| `k_0`, `e_0`, `e_{i/0}`, `n_i` | 11 | base field, its ramification index, relative index, number of Kummer steps (Prop 1.3) |
| `μ^log` | 13 | log-volume ([AbsTopIII] §5), normalized so `μ^log(R_i) = 0`, `μ^log(p·R_i) = −log p`, and on tensor products `μ^log((R_E)^∼) = 0` (Prop 1.4 (i)) |
| `I* ⊆ I` | 13 | indices with `e_i > p − 2` |
| `λ` | 13 | integer exponent in `φ(p^λ (R_I)^∼)` |
| `m_i` | 13 | `log_p` torsion term in Prop 1.4 (ii) |
| `V`, `M_I`, `B_I` | 15 | finite set of archimedean data; tensor product of copies of `ℂ`; unit ball (Prop 1.5) |
| `p_n`, `π(η)`, `n_0`, `η_prm` | 16 | `n`-th prime; prime counting function; thresholds (Prop 1.6) |
| `E`, `λ_e`, `β_e`, `β_avg`, `E^n` | 16 to 17 | finite set, weights, values, weighted average, tuples (Prop 1.7) |
| `E_k`, `E[n]`, Legendre form | 18 to 21 | elliptic curve over a field, `n`-torsion, `y² = x(x−1)(x−λ)` (Prop 1.8) |
| `ADiv_ℝ(F)`, `deg_F`, `deg` | 21 | arithmetic `ℝ`-divisors, degree with weights `log q_v` and 1, normalized degree `deg_F/[F:ℚ]` (Def 1.9 (i)) |
| `𝔞_E`, `deg_E` | 22 | part supported on `E`, normalized `E`-degree (Def 1.9 (ii)) |
| `d_mod = [F_mod : ℚ]`, `e_mod` | 22 | degree and maximal ramification index of `F_mod` |
| `d*_mod`, `e*_mod` | 22 | `2¹²·3³·5·d_mod`, `2¹²·3³·5·e_mod` |
| `F_mod ⊆ F_tpd ⊆ F ⊆ K` | 22 | field of moduli, tripodal field `F_mod(E[2])`, `F = F_tpd(√−1, E[3·5])`, `K = F(E[l])` |
| `𝔡^{F□}_{ADiv}`, `𝔡^{F□}`, `log(𝔡^{F□})` | 22 to 23 | different as arithmetic divisor; normalized log-different |
| `𝔣^{F□}_{ADiv}`, `log(𝔣^{F□})` | 23 | conductor of `E_F` as arithmetic divisor; normalized log-conductor |
| `𝔮_{ADiv}`, `log(𝔮)` | 23 | `q`-parameters at `𝕍^bad_mod`; normalized log of `q` |
| `C_Θ` | 23 | constant of IUT III Corollary 3.12 |
| `𝕍_ℚ^dst` | 25 | distinguished valuations of `ℚ` (conditions (D0) to (D7)) |
| `ι_{v_ℚ}` | 25 to 28 | 1 if `p_{v_ℚ} ≤ e*_mod·l`, else 0 |
| `𝔰^ℚ`, `𝔰^≤`, `log(𝔰^ℚ)`, `log(𝔰^≤)` | 26 | divisors supported at distinguished primes (resp. primes `≤ e*_mod·l`) |
| `l* = (l−1)/2`, `𝕊^±_{j+1} = {0, …, j}` | 27 | labels; IUT I Prop 6.9 |
| `l*_mod` | 28 | `log(e*_mod·l)` |
| `ℐ^ℚ(𝕊^±_{j+1};n,◦𝒟^⊢_{v_ℚ})` | 27 | tensor packet of log-shells (IUT III Thm 3.11) |

## Section 2: global estimates (pages 40 to 67)

| Notation | Page | Meaning |
|---|---|---|
| `θ(x)`, `θ_A`, `ξ_prm` | 40 | Chebyshev function, `∑_{p∈A} log p`, threshold (Prop 2.1) |
| `X = ℙ¹`, `D = {0, 1, ∞}`, `U_X` | 41 | `λ`-line and its boundary |
| `ℳ_ell`, `ht_∞` | 41 | moduli stack of elliptic curves, height at infinity |
| `ht_{ω_X(D)}`, `log-diff_X`, `log-cond_D` | 41 | height, log-different, log-conductor ([GenEll] Def 1.5) |
| `≲`, `≈` | 41, 55 | bounded discrepancy relations ([GenEll] Def 1.2 (ii) corrected by Rem 2.3.1 (ii)): `α ≲ β` iff `α − β` is bounded above |
| `K_V` | 41 | compactly bounded subset of `U_X(ℚ̄)` with support `V` containing 2 |
| `(*_{j-inv})` | 41 | `j`-invariant condition on `K_V` |
| `log(𝔮^∀)`, `log(𝔮^{∤2})` | 41 | normalized `q`-logs over all bad valuations (resp. those prime to 2) |
| `d`, `δ = 2¹²·3³·5·d` | 42 | degree bound; scaled degree |
| `h = log(𝔮^∀)` | 42 | shorthand used in the proof |
| `ε_d`, `ε*_d = ε_d/16` | 42, 47 | exponent parameters |
| `Exc_d`, `Exc_{ε,d}` | 42 | exceptional finite sets |
| `H_unif`, `H_K`, `C_K`, `B_K`, `T_K` | 42 to 47 | uniform and `K_V`-dependent constants |
| `ε_E = (60δ)²·h^{−1/2}·log(2δh)` | 42 | error term of (C2) |
| `x_E` | 42 | point of `K_V` attached to an elliptic curve |
| `A` | 44 | finite set of primes avoided by `l` in (P1) |
| `U_X(ℚ̄)^{≤d}` | 54 | points of degree at most `d` |

## Section 3: species and mutations (pages 67 to 87)

### Universe and set-theory conventions (pages 67 to 68)

* **ZFC-model.** A model of the ZFC axioms ("sets" and `∈`).
* **Grothendieck universe `V`.** A set with: (i) transitive; (ii) `ℕ ∈ V`; (iii) closed under
  power set; (iv) closed under union of members; (v) closed under surjective images of members.
  A `V`-set is an element of `V`.
* **Existence axiom `(†^G)`.** Every set lies in some universe. A ZFC-model satisfying it is a
  **ZFCG-model**. Consequences: any set-indexed family of universes lies in a larger universe;
  infinite ascending chains `V_0 ∈ V_1 ∈ …` exist; infinite descending chains do not (foundation).
* **Absoluteness proviso.** Every set-theoretic formula used is absolute: its truth for sets in
  `V` relative to `V` is equivalent to its truth relative to any universe `W` with `V ∈ W`.
* The paper does not settle whether ZFCG-models exist; it points to Feferman ([Ffmn]).

### Definitions

| Notation | Page | Meaning |
|---|---|---|
| 0-species `𝔖_0`, `Φ_0(𝔈)`, species-data `𝔈 = (𝔈_1, …, 𝔈_{n_0})` | 68 | set-theoretic formula in `n_0 ≥ 1` indeterminate sets (Def 3.1 (i)) |
| 0-specimen `E ∈ 𝔖_0`, 0-small | 68 | sets in a specific ZFC-model satisfying `Φ_0`; specimens form a set in every model |
| 1-species `𝔖_1`, `Φ_1(𝔈, 𝔈', 𝔉)`, `Φ_{1∘1}` | 68 to 69 | formulas for morphisms `𝔉 : 𝔈 → 𝔈'` and composition, with unique composites, associativity, identities (Def 3.1 (ii) (a) to (e)) |
| 1-specimen `F : E → E'`, 1-small | 69 | morphism in a ZFC-model; hom-sets are sets |
| species `𝔖 = (𝔖_0, 𝔖_1)` | 69 | pair (Def 3.1 (iii)) |
| species-object, species-morphism, species-isomorphism, species-automorphism | 69 | 0-specimen, 1-specimen, invertible 1-specimen, invertible endo-1-specimen |
| model-free specimen | 69 | specimen given by a formula determining the same specimen in nested universes `V_1 ∈ V_2` |
| category determined by `𝔖` | 70 | objects and arrows the specimens in a fixed ZFC-model (Def 3.1 (iv)) |
| mutation `𝔐 : 𝔖 ⇝ 𝔖'`, `Ψ_0`, `Ψ_1` | 72 to 73 | formulas sending species-objects and species-morphisms of `𝔖` to those of `𝔖'`, functorially (Def 3.3 (i)) |
| morphism of mutations `Z : 𝔐 → 𝔐'`, `Ξ(𝔈, 𝔉)` | 73 | formula giving `Z(E) : 𝔐(E) → 𝔐'(E)` natural in `E`; isomorphism of mutations (Def 3.3 (ii)) |
| mutation-equivalence, mutation-quasi-inverse | 73 to 74 | invertible up to isomorphism of mutations (Def 3.3 (iii)) |
| mutation-history `ℋ = (Γ, 𝔖_∗, 𝔐_∗)` | 74 | oriented graph with species at vertices and mutations along edges (Def 3.3 (iv)) |
| covariant / contravariant observable `𝒱`, observation mutation `𝒱_v` | 74 | mutations `𝔖_v ⇝ 𝔖` and morphisms of mutations along edges (Def 3.3 (v)); `Γ` simply connected |
| core, coricity | 74 | covariant observable whose edge morphisms are isomorphisms |

None of the Section 3 notions is formalized. In Lean 4 with Mathlib the closest analogues are
`CategoryTheory.Category` in a universe `Type u` and functors between such categories; Lean's
universe hierarchy `Type 0 : Type 1 : …` plays the role of the chain of universes, and
`ULift` the role of passing to a larger universe. This is a comparison, not a formalization.
