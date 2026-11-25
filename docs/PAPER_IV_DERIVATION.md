# IUT IV: the derivation from IUT III Corollary 3.12 to the abc inequality

This document follows the chain of results in *Inter-universal Teichmüller Theory IV* (April 2020
manuscript) that leads from IUT III, Corollary 3.12 to Theorem A and from there to the abc
inequality. For each step it records what is used, which external results are cited, which Lean
declarations check it, and which obligations remain open. Page numbers are PDF pages of IUT IV.

Pages read: the whole paper (pages 1 to 87) from the extracted text; Sections 1 and 2 line by
line; rendered pages 3, 9 to 17, 21 to 31, 40 to 48, 54 to 56, 67, 68, and IUT III page 174.

Nothing in this chain is formalized end to end. The Lean files check the real arithmetic of each
step relative to hypotheses that encode the arithmetic geometry; those hypotheses are named in
each theorem.

In `data/curated/iut4.json` every Lean lemma that checks one step is its own fragment record
(`<parent>.frag.<name>`); the records for the statements and proof steps themselves carry no Lean
declaration and the status `EXTRACTED`, except Propositions 1.6, 1.7 and 2.1, whose Lean theorems
(`proposition1_6`, `weighted_averages`, `proposition2_1`) state the whole proposition.

## The chain

```
IUT III Cor 3.12  (C_Θ ≥ −1 for every real C_Θ with −|log(Θ)| ≤ C_Θ·|log(q)|)
   │
   ▼
IUT IV Thm 1.10   (explicit value of C_Θ; final inequality for (1/6)·log(𝔮))
   │
   ▼
IUT IV Cor 2.2    (initial Θ-data from points of a compactly bounded K_V; (C1), (C2))
   │
   ▼
IUT IV Cor 2.3    (ht ≲ (1 + ε)(log-diff + log-cond) on U_X(ℚ̄)^{≤d}; uses [GenEll] Thm 2.1)
   │
   ▼
IUT IV Theorem A  (same statement as Cor 2.3)
   │
   ▼
abc               (specialization X = ℙ¹, D = {0, 1, ∞}, d = 1)
```

Dependency grades used in `data/curated/iut4.json` (field `cor3_12_dependency`):

* **independent**: does not use IUT III Theorem 3.11 or Corollary 3.12 (Propositions 1.1 to 1.8,
  Definition 1.9, Steps (i) to (iii) of the proof of Theorem 1.10, Proposition 2.1, Corollary
  2.2 (i) and (C1), proof steps (P1) to (P7) of Corollary 2.2).
* **setup_only**: uses the multiradial representation of IUT III Theorem 3.11 and the notion of an
  admissible bound `C_Θ` from the statement of Corollary 3.12, but not the inequality `C_Θ ≥ −1`
  (Steps (iv) to (viii) of Theorem 1.10, which show that the displayed value is admissible).
  Corollary 3.12 quantifies over all admissible real `C_Θ` (IUT III page 174); Theorem 1.10
  supplies one. Theorem 3.11 does not construct `C_Θ`.
* **conditional**: uses `C_Θ ≥ −1` (the final inequality of Theorem 1.10, Corollary 2.2 as a whole,
  its (C2) and (iii), the application of Theorem 1.10 and the assembly in its proof, Corollary
  2.3, Theorem A). Corollary 2.2 (iii) is graded conditional because it controls the exceptional
  sets of (ii); its arithmetic step alone is independent.

## Step 1: IUT III Corollary 3.12 → Theorem 1.10

**Statement (pages 22 to 23).** Hypotheses: a collection of initial Θ-data in the situation of
IUT III Corollary 3.12; `E_F` has good reduction at every valuation in
`𝕍(F)^good ∩ 𝕍(F)^non` not dividing `2l`; `d_mod = [F_mod : ℚ]`, `e_mod` the maximal
ramification index of `F_mod` over `ℚ`, `d*_mod = 2¹²·3³·5·d_mod`, `e*_mod = 2¹²·3³·5·e_mod`;
the tripodal field `F_tpd = F_mod(E_{F_mod}[2])`; the `3·5`-torsion of `E_F` is defined over
`F`; `F = F_tpd(√−1, E_{F_tpd}[3·5])`. Then the real number

`(l+1)/(4·|log(q)|)·{(1 + 12·d_mod/l)·(log(𝔡^{F_tpd}) + log(𝔣^{F_tpd})) + 10·(e*_mod·l + η_prm)
 − (1/6)·(1 − 12/l²)·log(𝔮)} − 1`,

is an admissible `C_Θ` for IUT III Corollary 3.12. Here `|log(q)| = log(𝔮)/(2l)` (page 23). In
Lean, `Theorem1_10.constant l d D E Q q` keeps `q` (for `|log(q)|`) and `Q` (for `log(𝔮)`) as
separate variables; the relation `q = Q/(2l)` is a hypothesis of `constant_bound_of_raw` and
`step_viii_constant`. Then, by `C_Θ ≥ −1`, `(1/6)·log(𝔮) ≤ (1 + 20·d_mod/l)·(log(𝔡^{F_tpd}) + log(𝔣^{F_tpd})) +
20·(e*_mod·l + η_prm)`. The statement does not list a bound on `l`: `l` is a prime `≥ 5` by IUT I
Definition 3.1, and page 22 notes `l ≠ 5` (the 5-torsion is rational over `F`), so `l ≥ 7`, which
the final estimate uses.

**Uses.** Propositions 1.3, 1.4, 1.5, 1.6, 1.7, 1.8; Definition 1.9; IUT III Theorem 3.11 and
Corollary 3.12; IUT I Definition 3.1.

**External.** [IUTchIII] Theorem 3.11, Corollary 3.12, Proposition 3.9; [AbsTopIII] Propositions
5.7, 5.8 (log-volumes); [DmMn] §3.10 (prime number theorem, through Proposition 1.6); [Silv],
[NerMod] (through Proposition 1.8).

**Lean (module `IUT.PaperIV.Theorem1_10.*`).**

| Step | Content | Declarations | Status |
|---|---|---|---|
| (i) | (E1) to (E6) | `E1`, `E2`, `card_GL2`, `E4`, `E4_product`, `E6` | fragments kernel checked; (E5) open, so the step is open |
| (ii) | constants 21 and 46 | `step_ii_F`, `step_ii_K`, `step_ii_final` | conditional on the Prop 1.3 inputs |
| (iii) | (R4); constant 52 | `R4`, `step_iii_p_eq_l`, `step_iii_sQ`, `step_iii_final` | conditional on (R1) to (R3) and the bound on `log(𝔰^ℚ)` |
| (iv) | reduction to local log-volumes | none | blocked by IUT III Thm 3.11 |
| (v) | weighted and procession-normalized bounds | `sum_Istar_le`, `weighted_average_normalized`, `betaAvg_affine`, `step_v_weighted`, `procession_sum`, `procession_average`, `procession_average_l`, `step_v_final` | conditional on the local bounds of Prop 1.4 (iii) |
| (vi) | bound 0 | none | open: the content is that the container `(R_I)^∼` has log-volume 0 and contains the possible images, by Prop 1.4 (iv) (page 29); not formalized |
| (vii) | archimedean bound | `step_vii_average`, `step_vii_archimedean` (existing) | conditional on Prop 1.5 |
| (viii) | summation, prime count, value of `C_Θ` | `step_viii_sum`, `step_viii_raw`, `step_viii_prime_count`, `step_viii_prime_count_prm`, `step_viii_constant`, and the existing `step_viii_estimate`, `step_viii_absorb`, `step_viii_substitute`, `constant_bound_of_raw` | conditional on the summed local bounds and `log(𝔰^≤) ≤ π(e*_mod·l)` |
| final | final inequality | `final_estimate_one`, `final_estimate_two`, `final_inequality`, `final_inequality_F` (existing) | conditional on `−1 ≤ constant` (IUT III Cor 3.12) |

Supporting modules: `IUT.PaperIV.Proposition1_2`, `Proposition1_3`, `Proposition1_4`,
`Proposition1_5` (elementary parts), `Proposition1_6` and `Proposition1_7` (whole statements),
`IUT.PaperIV.Definition1_9` (the definitions of (i) and (ii); `deg_E` is defined only for nonempty
sets of valuations over one place of `ℚ`; pull-back to extensions and the two invariance
statements are not formalized).

**Open obligations.** The local inputs: Propositions 1.1, 1.2 (inclusions), 1.3 (differents), 1.4
(log-volumes), 1.5 (metrics), 1.8 (torsion of elliptic curves), (E5); IUT III Theorem 3.11 and
Corollary 3.12; the identification of the global quantities with sums of local ones (Definition
1.9 (ii) invariance).

## Step 2: Theorem 1.10 → Corollary 2.2

**Statement (pages 41 to 43).** For `X = ℙ¹`, `D = {0, 1, ∞}` (the `λ`-line) and a compactly
bounded `K_V ⊆ U_X(ℚ̄)` containing the prime 2 in its support and satisfying `(*_{j-inv})`:
(i) `(1/6)·log(𝔮^{∤2}) ≈ (1/6)·log(𝔮^∀) ≈ (1/6)·ht_∞ ≈ ht_{ω_X(D)}` on `K_V`; (ii) outside a
finite set `Exc_{ε_d}`, an elliptic curve with a point `x_E ∈ K_V` arises from initial Θ-data with
(C1) `h^{1/2} ≤ l ≤ 10δ·h^{1/2}·log(2δh)` and (C2)
`(1/6)·log(𝔮^∀) ≤ (1 + ε_E)·(log-diff_X(x_E) + log-cond_D(x_E)) + C_K`, where
`δ = 2¹²·3³·5·d`, `h = log(𝔮^∀)`, `ε_E = (60δ)²·h^{−1/2}·log(2δh)`, and
`log(𝔮^∀) ≤ H_unif·ε_d^{−3}·d^{4+ε_d} + H_K` on `Exc_{ε_d}` (page 42); (iii) the exceptional sets can be
chosen with `log(𝔮^∀) ≤ H_unif·ε^{−3}·ε_d^{−3}·d^{4+ε_d} + H_K` and `ε_E ≤ ε` outside them.

**Uses.** Proposition 2.1; Theorem 1.10 (final inequality) with Remark 1.10.7 (i); Proposition 1.8.

**External.** [GenEll] Definition 1.2, Example 1.3, Proposition 1.4, Lemma 3.1, Definition 3.3,
Proposition 3.4, Lemma 3.5, Lemma 3.7; [CanLift] Proposition 2.7; [IUTchI] Definition 3.1.

**Lean (module `IUT.PaperIV.Corollary2_2.Arithmetic`, namespace `IUT.PaperIV.Corollary2_2`).**
`thetaA_chain`, `S1_bound`, `P1_upper`, `P1_lower`, `P1_l_ge_seven`, `P1_bound` ((C1));
`P4_bound`; `sqrt_mul_log_l`, `sqrt_mul_log_l_steps`, `P5_bound`; `apply_theorem_1_10`,
`q_not2_step`, `fifteen_delta_step`, `assembly`, `epsE_ge`, `final_step`, `C2_of_final` ((C2));
`eps_star_estimates`, `h_lt_of_eps_lt_epsE`, `h_bound_Hunif` ((iii)). Proposition 2.1 is
`IUT.PaperIV.Proposition2_1` (whole statement `proposition2_1`, from Mathlib's prime number
theorem).

(P3) (pages 44 to 45): if `l = p_v` for some nonarchimedean `v`, then `h_v < h^{1/2}`. This holds
because `l ∉ A` and, by (S3), `A` contains `p_v` for every `v` with `h_v ≥ h^{1/2}`. No Lean
lemma states (P3); `q_not2_step` takes its consequence on page 47 as a hypothesis.

(P7) (page 46) follows formally from (P1), (P2), (P5) and (P6). There `F̄ = ℚ̄` and `F` is the
number field of the discussion; `F_mod` stays the minimal field of definition of the moduli
point, of degree `d_mod ≤ d`, not `ℚ`.

**Open obligations.** (i) (heights on the moduli of elliptic curves); the local height
computations behind the bound on `θ_A`; (P2) to (P7) (Galois images, cyclic subgroups, the
existence of the data `V`, `ε` of IUT I Definition 3.1); finiteness of `j`-invariants of bounded
height.

## Step 3: Corollary 2.2 → Corollary 2.3 = Theorem A

**Statement (page 54).** For `X` smooth, proper, geometrically connected over a number field,
`D` reduced with `U_X` hyperbolic, `d ≥ 1`, `ε > 0`:
`ht_{ω_X(D)} ≲ (1 + ε)·(log-diff_X + log-cond_D)` on `U_X(ℚ̄)^{≤d}`.

**Proof (pages 54 and 55).** The statement is [GenEll] Theorem 2.1 (i). By the equivalence of
[GenEll] Theorem 2.1 it suffices to prove [GenEll] Theorem 2.1 (ii), i.e. the inequality on
`K_V ∩ U_X(ℚ̄)^{≤d}` for the `λ`-line, which follows from Corollary 2.2 (i), (ii) (C2), (iii)
using `d_mod ≤ d`.

**External.** [GenEll] Theorem 2.1 (Belyi maps, noncritical Belyi maps), with the corrections of
Remark 2.3.1 (ii) and (v).

**Lean (module `IUT.PaperIV.Corollary2_3`).** `BDle`, `BDeq` (the relations of [GenEll]
Definition 1.2 (ii) as corrected by Remark 2.3.1 (ii)), `BDle_of_finite_exceptions`,
`cor2_3_on_KV` (an abstract lemma about real functions on an arbitrary set `S`, true for every
`S` including the empty set; it mirrors the logical form of the step on `K_V`, with Corollary 2.2
(i), (C2), (iii) and `Λ ≥ 0` as hypotheses; Corollary 2.3 itself is not stated in Lean), `BDle_mono_eps` (passage from `ε ≤ 1` to all `ε`).

**Open obligations.** [GenEll] Theorem 2.1; Corollary 2.2 itself.

Theorem A (page 3) is the statement of Corollary 2.3.

## Step 4: Theorem A → abc

The paper does not write out this specialization. The standard one is:

* **Curve and divisor.** `X = ℙ¹_ℚ`, `D = {0, 1, ∞}`, `U_X = ℙ¹ \ {0, 1, ∞}`. Then
  `deg ω_X(D) = −2 + 3 = 1 > 0`, so `U_X` is hyperbolic.
* **Degree bound.** `d = 1`: points over `ℚ`.
* **Point.** For positive integers `a + b = c` with `gcd(a, b) = 1`, take `x = a/c = [a : c]`.
  Since `a, b > 0`, `x ≠ 0, 1, ∞`, so `x ∈ U_X(ℚ)`.
* **Height.** `ω_X(D) ≅ 𝒪(1)`, and `ht_{𝒪(1)}([a : c]) = log max(|a|, |c|) = log c` for coprime
  `a, c` with the standard metric; heights are defined only up to bounded discrepancy, so
  `ht_{ω_X(D)}(x) ≈ log c`.
* **Log-different.** The minimal field of definition is `ℚ`, whose different is trivial, so
  `log-diff_X(x) = deg_ℚ(δ_x) = 0` ([GenEll] Definition 1.5 (iii)).
* **Log-conductor.** The morphism `Spec ℤ → ℙ¹_ℤ` given by `[a : c]` meets `0` at the primes
  dividing `a`, `1` at the primes dividing `c − a = b`, and `∞` at the primes dividing `c`. The
  reduced pullback `(D_x)_red` is `∑_{p | abc} p`, so `log-cond_D(x) = ∑_{p | abc} log p =
  log rad(abc)` ([GenEll] Definition 1.5 (iv)). Over `ℚ` normalized and unnormalized degrees
  agree.
* **Conclusion.** Theorem A gives, for each `ε > 0`, a constant `C_ε` with
  `log c ≤ (1 + ε)·log rad(abc) + C_ε` for all such triples.

**Relation to `Challenge.ABCLog`.** `Challenge/Defs.lean` defines `Challenge.ABCLog` as: for every
`ε > 0` there is `C` such that for all positive `a, b, c` with `Nat.Coprime a b` and `a + b = c`,
`Real.log c ≤ (1 + ε)·Real.log (rad (a*b*c)) + C`. This is exactly the conclusion above, and
`IUT/Applications/ABC.lean` proves `ABC ↔ ABCLog` (`abc_iff_abcLog`).

**The reduction Theorem A → `Challenge.ABCLog` is not formalized.** Mathlib has no heights,
log-differents or log-conductors on curves over number fields, and Theorem A itself is not
formalized. The specialization above is a paper-level argument.

## Summary of places where the arithmetic needs an extra hypothesis or a reading

| Page | Place | Finding |
|---|---|---|
| 16 | Proposition 1.6 | `η_prm` is said to be positive, and that suffices: Step (viii) (page 31) divides by `log(η_prm)` only in the case `1 < e*_mod·l < η_prm`, where `log(η_prm) > 0`. The Lean witness satisfies `η_prm ≥ 2`, which is stronger than needed. |
| 22 | Definition 1.9 (ii) | In the render the line under `deg(𝔞_E)` is the fraction bar, so the numerator is the unnormalized `deg` of (i), i.e. `deg_F`; only this reading makes the stated invariance under extensions hold. `deg_E` is defined for nonempty `E` over one valuation of `ℚ`. |
| 26 | Step (iii), final display | Replacing `(4/l)·D` by `(4·d_mod/l)·D` needs `D ≥ 0` (true, not stated). |
| 29 | Step (v), final display | Needs `log(𝔡^K_{v_ℚ})`, `log(𝔰^ℚ_{v_ℚ})`, `l*_mod·log(𝔰^≤_{v_ℚ}) ≥ 0` (true, not stated). |
| 40 | Proposition 2.1 (ii) | The text extraction reads `p ∈ A`; the render shows `p ∉ A`. |
| 55 | Corollary 2.3 | Corollary 2.2 (iii) is stated for `ε ≤ 1`; larger `ε` follow by monotonicity since `log-diff + log-cond ≥ 0`. |

Not a gap, but worth recording: (P1) on page 45 writes `5 ≤ l`, while the final estimate of
Theorem 1.10 needs `l ≥ 7`. Page 22 notes `l ≠ 5` from [IUTchI] Definition 3.1 (c); also, `5 ≤ h^{1/2}` puts 5 in the avoided set `A` while `l ∉ A`,
so the prime `l` is at least 7 (`P1_l_ge_seven`).

No error was found in `IUT/PaperIV/Theorem1_10/Arithmetic.lean` or
`IUT/PaperIV/ArithmeticDivisor.lean`.
