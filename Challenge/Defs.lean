import Mathlib

/-!
# Trusted definitions

This file is the reviewed, protected vocabulary of the project. It depends on Mathlib only.
Every definition here is meant to be read by a human and compared with its source. The file
`data/challenge_fingerprints.json` records a fingerprint of each declaration, and the trust
checks fail when a fingerprint changes without the record being updated on purpose.

Sources: the classical statement of the abc conjecture (Masser, Oesterlé), and
Mochizuki, *Inter-universal Teichmüller Theory IV*, Theorem A and Corollary 2.3, for the
role the statement plays in the four papers.
-/

namespace Challenge

/-- The radical of a natural number: the product of its distinct prime divisors.
`rad 0 = 1` and `rad 1 = 1`, because `Nat.primeFactors` is empty in both cases. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

/-- **The abc conjecture**, constant form.

For every real `ε > 0` there is a real constant `K > 0`, depending on `ε` only, such that
every triple of positive integers `a`, `b`, `c` with `a` and `b` coprime and `a + b = c`
satisfies `c ≤ K * rad (a * b * c) ^ (1 + ε)`.

Because `a + b = c`, coprimality of `a` and `b` is the same as pairwise coprimality of the
three numbers; see `Solution.coprime_iff_pairwise`. The exponent is a real power. -/
def ABC : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
    Nat.Coprime a b → a + b = c → (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε)

/-- The abc conjecture, finiteness form: for every `ε > 0` only finitely many coprime triples
`a + b = c` have `c > rad (a * b * c) ^ (1 + ε)`. This is the primary form in the Formal
Conjectures project (`FormalConjectures/Wikipedia/ABC.lean`, theorem `ABC.abc`), with the
pairwise coprimality written there replaced by the equivalent coprimality of `a` and `b`. -/
def ABCFinite : Prop :=
  ∀ ε : ℝ, 0 < ε → {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧
    Nat.Coprime t.1 t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧
    ((rad (t.1 * t.2.1 * t.2.2) : ℝ) ^ (1 + ε) < t.2.2)}.Finite

/-- The abc conjecture, logarithmic form: `log c ≤ (1 + ε) * log (rad (a b c)) + C`. This is
the shape in which the statement appears as a height inequality (compare the inequality
`ht ≲ (1 + ε)(log-diff + log-cond)` of IUT IV, Theorem A, for the projective line minus
three points and rational points). -/
def ABCLog : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
    Nat.Coprime a b → a + b = c →
      Real.log c ≤ (1 + ε) * Real.log (rad (a * b * c)) + C

end Challenge
