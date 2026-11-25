import Challenge.Defs
import IUT.Applications.ABC
import IUT.PaperIV.Theorem1_10.Arithmetic
import IUT.Audit.ScholzeStix.Section1_3

/-!
# Solution: the headline statements, proved from the library

The solution file of `lake comparator` (see `comparator.json`). Every theorem below has, byte
for byte and under the same name, the statement of `Challenge.lean`, and is proved by reference
to the library theorem named in `Challenge.lean`. This module is a default build target, and
the axiom gate `AxiomGate.lean` checks its constants like those of the library.
-/

namespace Solution

open Challenge

/-- The constant form and the finiteness form of the abc conjecture are equivalent. -/
theorem abc_iff_abcFinite : ABC ↔ ABCFinite := IUT.ABC.abc_iff_abcFinite

/-- The constant form and the logarithmic form of the abc conjecture are equivalent. -/
theorem abc_iff_abcLog : ABC ↔ ABCLog := IUT.ABC.abc_iff_abcLog

/-- The radical of `Challenge.Defs` is Mathlib's radical on `ℕ`. -/
theorem rad_eq_radical (n : ℕ) : rad n = UniqueFactorizationMonoid.radical n :=
  IUT.ABC.rad_eq_radical n

/-- For positive `a`, `b` with `a + b = c`, coprimality of `a` and `b` is pairwise coprimality
of `a`, `b`, `c`. -/
theorem coprime_iff_pairwise {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a + b = c) :
    a.Coprime b ↔ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime := IUT.ABC.coprime_iff_pairwise ha hb h

/-- IUT IV, Theorem 1.10, final portion, as real arithmetic: if the constant `C_Θ` of the
statement is at least `−1`, then
`(1/6)·log(𝔮) ≤ (1 + 20·d_mod/l)·(log 𝔡 + log 𝔣) + 20·(e*_mod·l + η_prm)`. -/
theorem theorem1_10_final_inequality {l d D E Q q : ℝ} (hl : 7 ≤ l) (hd : 1 ≤ d)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hq : 0 < q)
    (hC : -1 ≤ (l + 1) / (4 * q) * ((1 + 12 * d / l) * D + 10 * E
      - 1 / 6 * (1 - 12 / l ^ 2) * Q) - 1) :
    1 / 6 * Q ≤ (1 + 20 * d / l) * D + 20 * E :=
  IUT.PaperIV.Theorem1_10.final_inequality hl hd hD hE hq hC

/-- Scholze and Stix, Section 1.3: substituting the average (1.5), with the factor `j²`, into
(1.4) gives `(1/6)·qE·(1 − 12/(ℓ(ℓ+1))) ≤ d`. -/
theorem scholzeStix_with_squares {lh : ℕ} (hlh : 1 ≤ lh) {l : ℝ} (hl : l = 2 * lh + 1)
    {d qE : ℝ} (h14 : -(qE / (2 * l)) ≤
      (1 / (lh : ℝ)) * ∑ j ∈ Finset.Icc 1 lh, ((j : ℝ) * d - (j : ℝ) ^ 2 * (qE / (2 * l)))) :
    1 / 6 * qE * (1 - 12 / (l * (l + 1))) ≤ d :=
  IUT.Audit.ScholzeStix.consequence_with_squares hlh hl h14

/-- Scholze and Stix, Section 1.3: substituting the average (1.6), without the factor `j²`,
into (1.4) gives an inequality equivalent to `0 ≤ d`. -/
theorem scholzeStix_without_squares {lh : ℕ} (hlh : 1 ≤ lh) (l d qE : ℝ) :
    -(qE / (2 * l)) ≤ (1 / (lh : ℝ)) * ∑ j ∈ Finset.Icc 1 lh, ((j : ℝ) * d - qE / (2 * l))
      ↔ 0 ≤ d :=
  IUT.Audit.ScholzeStix.consequence_without_squares hlh l d qE

end Solution
