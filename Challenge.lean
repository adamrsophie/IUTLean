import Challenge.Defs

/-!
# Challenge: the headline statements

The challenge file of `lake comparator` (see `comparator.json`). It states the headline
theorems of the project with `sorry` on purpose; `Solution.lean` states the same theorems,
byte for byte and under the same names, and proves them from the library. The comparator
checks that each solution theorem has the statement given here, with the definitions of
`Challenge.Defs` underneath, uses no axiom outside `propext`, `Classical.choice` and
`Quot.sound`, and is accepted by the kernel.

This file imports only `Challenge.Defs`, so every statement below is written with Mathlib terms
and the reviewed definitions `Challenge.rad`, `Challenge.ABC`, `Challenge.ABCFinite` and
`Challenge.ABCLog`. Definitions of the library that a statement needs are written out in
place. No statement here asserts the abc conjecture or its negation; the first two are
equivalences between formulations.

This file is not part of any default build target, and nothing imports it. The `sorry`
placeholders are allowed here and nowhere else outside `IUT/Experimental/`.

No PDF page was read for this file: the statements are taken from the library modules named
below, whose docstrings record the pages read. Sources of the statements:

* the equivalences and the radical: `IUT/Applications/ABC.lean`;
* the final inequality of IUT IV, Theorem 1.10, as real arithmetic:
  `IUT/PaperIV/Theorem1_10/Arithmetic.lean`, theorem `final_inequality`, with the definition
  `constant` (the constant `C_Θ` of the statement) written out;
* the two consequences of Scholze and Stix, Section 1.3, displays (1.4) to (1.6):
  `IUT/Audit/ScholzeStix/Section1_3.lean`, with the definitions `thetaWithSquares` and
  `thetaWithoutSquares` written out.
-/

namespace Solution

open Challenge

/-- The constant form and the finiteness form of the abc conjecture are equivalent. -/
theorem abc_iff_abcFinite : ABC ↔ ABCFinite := sorry

/-- The constant form and the logarithmic form of the abc conjecture are equivalent. -/
theorem abc_iff_abcLog : ABC ↔ ABCLog := sorry

/-- The radical of `Challenge.Defs` is Mathlib's radical on `ℕ`. -/
theorem rad_eq_radical (n : ℕ) : rad n = UniqueFactorizationMonoid.radical n := sorry

/-- For positive `a`, `b` with `a + b = c`, coprimality of `a` and `b` is pairwise coprimality
of `a`, `b`, `c`. -/
theorem coprime_iff_pairwise {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a + b = c) :
    a.Coprime b ↔ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime := sorry

/-- IUT IV, Theorem 1.10, final portion, as real arithmetic: if the constant `C_Θ` of the
statement is at least `−1`, then
`(1/6)·log(𝔮) ≤ (1 + 20·d_mod/l)·(log 𝔡 + log 𝔣) + 20·(e*_mod·l + η_prm)`. -/
theorem theorem1_10_final_inequality {l d D E Q q : ℝ} (hl : 7 ≤ l) (hd : 1 ≤ d)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hq : 0 < q)
    (hC : -1 ≤ (l + 1) / (4 * q) * ((1 + 12 * d / l) * D + 10 * E
      - 1 / 6 * (1 - 12 / l ^ 2) * Q) - 1) :
    1 / 6 * Q ≤ (1 + 20 * d / l) * D + 20 * E := sorry

/-- Scholze and Stix, Section 1.3: substituting the average (1.5), with the factor `j²`, into
(1.4) gives `(1/6)·qE·(1 − 12/(ℓ(ℓ+1))) ≤ d`. -/
theorem scholzeStix_with_squares {lh : ℕ} (hlh : 1 ≤ lh) {l : ℝ} (hl : l = 2 * lh + 1)
    {d qE : ℝ} (h14 : -(qE / (2 * l)) ≤
      (1 / (lh : ℝ)) * ∑ j ∈ Finset.Icc 1 lh, ((j : ℝ) * d - (j : ℝ) ^ 2 * (qE / (2 * l)))) :
    1 / 6 * qE * (1 - 12 / (l * (l + 1))) ≤ d := sorry

/-- Scholze and Stix, Section 1.3: substituting the average (1.6), without the factor `j²`,
into (1.4) gives an inequality equivalent to `0 ≤ d`. -/
theorem scholzeStix_without_squares {lh : ℕ} (hlh : 1 ≤ lh) (l d qE : ℝ) :
    -(qE / (2 * l)) ≤ (1 / (lh : ℝ)) * ∑ j ∈ Finset.Icc 1 lh, ((j : ℝ) * d - qE / (2 * l))
      ↔ 0 ≤ d := sorry

end Solution
