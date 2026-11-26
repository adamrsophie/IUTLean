import IUT.ABC.Variants

/-!
# Elementary results around the abc conjecture from the literature

This file collects elementary statements, each proved, taken from recent papers on the abc
conjecture, together with four named statements that are not proved here (a claim of an
unrefereed preprint, an open finiteness statement, a theorem of a paper, and a classical divisor
bound used as an explicit hypothesis). Nothing here says whether the abc conjecture holds. No page of the IUT papers is
used.

Sources (formulas taken from the TeX sources; pages read for this file are the sections named;
no page was checked against a rendered image):

* C. Soulé, *On the abc conjecture*, arXiv 2611.05217 (November 2026, unrefereed preprint),
  Introduction, statements of Theorems A and B.
* J. Cuevas Barrientos and H. Pasten, *On the greatest prime factor of polynomial values and
  subexponential Szpiro in families*, arXiv 2504.15971, Section 4 (Lemma 4.2) and Section 5
  (the unnumbered display `4^P(M) ≥ ∏_{p ≤ P(M)} p ≥ rad(M)`).
* K. Joshi, *Construction of Arithmetic Teichmuller spaces II: Proof of a local prototype of
  Mochizuki's Corollary 3.12*, arXiv 2303.01662, Section 9, Theorem 9.2.1 and its proof.
* R. Laniewski and K. Müller, *The quality plane of abc-triples and the decomposition into
  gains*, arXiv 2610.03212 (preprint), Sections 2 to 5: Definition 2.1, Lemma 2.2, Lemma 3.3,
  Proposition 3.4, Definition 4.1, Proposition 4.2.
* M. van Frankenhuijsen, *Two Restricted ABC Conjectures*, arXiv 2010.09493, Sections 2 and 4:
  Lemmas 2.3, 2.4, 4.1, 4.2, 4.3.
* P. Vojta, *A more general abc conjecture*, arXiv math/9806171, Proposition 2.6.
* H. Pasten, *Shimura curves and the abc conjecture*, arXiv 1705.09251, Theorem 1.11 and
  Theorem 16.7.

## Named statements that are not proved here

* `SouleTheoremBClaim`: Theorem B of Soulé, `c ≤ A(ε)·rad(abc)^(24 + ε)`. A claim of an
  unrefereed preprint. Proved: `Challenge.ABC → SouleTheoremBClaim`
  (`souleTheoremBClaim_of_ABC`) and `SouleTheoremBClaim → ABCWithExponent κ` for every `κ > 24`
  (`abcWithExponent_of_souleTheoremBClaim`).
* `LaniewskiMullerMassBound`: for every `ε > 0` only finitely many triples have logarithmic
  mass `Y = log(abc)/log rad(abc) > 3 + ε`. Implied by `Challenge.ABC`
  (`laniewskiMullerMassBound_of_ABC`); it implies that only finitely many triples have quality
  `> 3/2 + ε` (`finite_quality_gt_of_laniewskiMullerMassBound`). Laniewski and Müller,
  Lemma 3.3, state that it is equivalent to Szpiro's conjecture for Frey curves; that
  equivalence needs the minimal discriminant and the conductor of the Frey curve and is not
  formalized.
* `PastenDivisorBound`: Pasten's `d(abc) < K_ε·rad(abc)^(8/3 + ε)`, a theorem of that paper
  (proved there with modularity and Shimura curves) that is not proved in this library. It is
  implied by `Challenge.ABC` (`pastenDivisorBound_of_ABC`), by an elementary argument
  (`d(n) ≤ 2√n`) that is not taken from the paper.
* `DivisorCountPowerBound`: the classical divisor bound `d(n) ≤ C_δ·n^δ` for every `δ > 0`. It
  is not in Mathlib and is used only as an explicit hypothesis of
  `divisorCount_le_rad_rpow_of_ABC`.

## Items not formalized

* van Frankenhuijsen, Lemma 2.4 (`r_K(a : 1-a : 1) ≤ 3[K:ℚ] + 3h_K(a : 1-a : 1)`): the
  radical `r_K` of a number field point is not in Mathlib. Over `ℚ`, for a point with coprime
  integer coordinates it reduces to `1 + log rad(abc) ≤ 3 + 3 log max`, which follows from
  `IUT.ABC.Variants.rad_le_mul_mul` and `IUT.ABC.Variants.mul_mul_lt_cube`.
* Laniewski and Müller, Lemma 3.3 (the passage to Szpiro's conjecture): see above.
-/

open Finset

namespace IUT.ABC.Elementary

open Challenge IUT.ABC IUT.ABC.Variants

/-! ## Soulé's Theorem B -/

/-- **Theorem B of C. Soulé, *On the abc conjecture*, arXiv 2611.05217**, as stated there: for
every `ε > 0` there is `A(ε) > 0` such that all positive integers `a`, `b`, `c` with no common
divisor and `a + b = c` satisfy `c ≤ A(ε)·N^(24 + ε)`, `N` the product of the primes dividing
`abc`. "No common divisor" is read as `Nat.Coprime a b`, which is equivalent since `a + b = c`;
the constant and the non-strict inequality are those of `ABCWithExponent`.

This is **a claim** of an unrefereed preprint of November 2026: the paper claims Theorem A (an
effective Mordell bound for genus 2 curves) and states that Theorem B follows from it by work of
Moret-Bailly. It is not proved or assumed anywhere in this library. It is strictly weaker than
the abc conjecture as a statement: the conjecture implies it (`souleTheoremBClaim_of_ABC`),
while it gives no bound with an exponent `24` or smaller, so it does not give the conjecture by
any argument in this library. -/
def SouleTheoremBClaim : Prop := ∀ ε : ℝ, 0 < ε → ABCWithExponent (24 + ε)

/-- The abc conjecture implies Soulé's Theorem B. -/
theorem souleTheoremBClaim_of_ABC (h : ABC) : SouleTheoremBClaim :=
  fun _ hε => abcWithExponent_of_ABC h (by linarith)

/-- Soulé's Theorem B gives the fixed exponent bound for every exponent `κ > 24`. -/
theorem abcWithExponent_of_souleTheoremBClaim (h : SouleTheoremBClaim) {κ : ℝ} (hκ : 24 < κ) :
    ABCWithExponent κ := by
  have := h (κ - 24) (by linarith)
  rwa [show 24 + (κ - 24) = κ by ring] at this

/-- Soulé's Theorem B is the fixed exponent bound for every exponent `κ > 24`. -/
theorem souleTheoremBClaim_iff :
    SouleTheoremBClaim ↔ ∀ κ : ℝ, 24 < κ → ABCWithExponent κ :=
  ⟨fun h _ hκ => abcWithExponent_of_souleTheoremBClaim h hκ,
    fun h ε hε => h (24 + ε) (by linarith)⟩

/-! ## The radical and the largest prime factor -/

/-- The largest prime factor `P(M)` of `M`, with the convention `P(M) = 0` for `M ≤ 1` (the
supremum of the empty set of prime factors). -/
def largestPrimeFactorOf (M : ℕ) : ℕ := M.primeFactors.sup id

/-- **`rad M ≤ 4^P(M)`**, the display `4^P(M) ≥ ∏_{p ≤ P(M)} p ≥ rad(M)` of Section 5 of
J. Cuevas Barrientos and H. Pasten, *On the greatest prime factor of polynomial values and
subexponential Szpiro in families*, arXiv 2504.15971 (unnumbered; stated there for `M > 1`).
The radical divides the primorial of `P(M)`, which is at most `4^P(M)` by Mathlib's
`primorial_le_four_pow`. With `P(M) = 0` for `M ≤ 1` it holds for every `M`. -/
theorem rad_le_four_pow_largestPrimeFactorOf (M : ℕ) : rad M ≤ 4 ^ largestPrimeFactorOf M := by
  classical
  have hsub : M.primeFactors ⊆ (range (largestPrimeFactorOf M + 1)).filter Nat.Prime := by
    intro p hp
    refine mem_filter.2 ⟨mem_range.2 (Nat.lt_succ_of_le ?_), Nat.prime_of_mem_primeFactors hp⟩
    exact Finset.le_sup (f := id) hp
  have hdvd : rad M ∣ primorial (largestPrimeFactorOf M) := by
    unfold rad primorial
    exact Finset.prod_dvd_prod_of_subset _ _ (fun p => p) hsub
  exact (Nat.le_of_dvd (primorial_pos _) hdvd).trans (primorial_le_four_pow _)

/-- The logarithmic form: `log rad M ≤ P(M)·log 4`. So a lower bound for `log rad M` is a lower
bound for the largest prime factor, as used in Section 5 of Cuevas Barrientos and Pasten. -/
theorem log_rad_le_largestPrimeFactorOf_mul_log_four (M : ℕ) :
    Real.log (rad M : ℝ) ≤ largestPrimeFactorOf M * Real.log 4 := by
  have h : (rad M : ℝ) ≤ (4 : ℝ) ^ largestPrimeFactorOf M := by
    exact_mod_cast rad_le_four_pow_largestPrimeFactorOf M
  calc Real.log (rad M : ℝ) ≤ Real.log ((4 : ℝ) ^ largestPrimeFactorOf M) :=
        Real.log_le_log (by exact_mod_cast rad_pos M) h
    _ = largestPrimeFactorOf M * Real.log 4 := Real.log_pow _ _

/-! ## Joshi's coefficient comparison -/

/-- `∑_{j=1}^{n} j² = n(n + 1)(2n + 1)/6`. -/
theorem sum_Icc_sq_eq (n : ℕ) :
    ∑ j ∈ Icc 1 n, ((j : ℝ) ^ 2) = n * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; push_cast; ring

/-- **The coefficient identity of the proof of Theorem 9.2.1** of K. Joshi, *Construction of
Arithmetic Teichmuller spaces II: Proof of a local prototype of Mochizuki's Corollary 3.12*,
arXiv 2303.01662. With `l = 2l* + 1` and `n = l* ≥ 1`:
`(∑_{j=1}^{l*} j²/l*²)·(1/(2l)) = (1/12)(1 + 1/l*)`. -/
theorem joshi_coefficient_eq (n : ℕ) (hn : 1 ≤ n) :
    (∑ j ∈ Icc 1 n, ((j : ℝ) ^ 2 / (n : ℝ) ^ 2)) * (1 / (2 * (2 * n + 1)))
      = 1 / 12 * (1 + 1 / (n : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                               linarith
  rw [← Finset.sum_div, sum_Icc_sq_eq]
  field_simp
  ring

/-- The right side of the comparison in the proof of Joshi's Theorem 9.2.1:
`(1/4)(1 - 1/l) = l*/(2l)` for `l = 2l* + 1`. -/
theorem joshi_quarter_eq (n : ℕ) :
    1 / 4 * (1 - 1 / (2 * (n : ℝ) + 1)) = n / (2 * (2 * n + 1)) := by
  have : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- **The comparison of the proof of Joshi's Theorem 9.2.1**, with the threshold made exact:
for `l = 2l* + 1` with `l* ≥ 1`, `(1/12)(1 + 1/l*) < (1/4)(1 - 1/l)` holds if and only if
`l* ≥ 2`, that is `l ≥ 5`. The paper says "if `ℓ` is sufficiently large"; the difference of the
two sides is `(4l* + 1)(l* - 1)/(12·l*·l)`. -/
theorem joshi_coefficient_lt_iff (n : ℕ) (hn : 1 ≤ n) :
    1 / 12 * (1 + 1 / (n : ℝ)) < 1 / 4 * (1 - 1 / (2 * (n : ℝ) + 1)) ↔ 2 ≤ n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have key : 1 / 4 * (1 - 1 / (2 * (n : ℝ) + 1)) - 1 / 12 * (1 + 1 / (n : ℝ))
      = (4 * n + 1) * (n - 1) / (12 * n * (2 * n + 1)) := by
    field_simp
    ring
  have hden : (0 : ℝ) < 12 * n * (2 * n + 1) := by positivity
  rw [← sub_pos, key, div_pos_iff_of_pos_right hden]
  constructor
  · intro h
    have h1 : (0 : ℝ) < n - 1 := by
      by_contra hc
      push Not at hc
      nlinarith
    have : (1 : ℝ) < n := by linarith
    exact_mod_cast this
  · intro h
    have : (2 : ℝ) ≤ n := by exact_mod_cast h
    nlinarith

/-- At `l = 3` (`l* = 1`) the two sides of Joshi's comparison are equal (both `1/6`), so the
strict inequality needs `l ≥ 5`. -/
theorem joshi_coefficient_eq_at_three :
    1 / 12 * (1 + 1 / ((1 : ℕ) : ℝ)) = 1 / 4 * (1 - 1 / (2 * ((1 : ℕ) : ℝ) + 1)) := by
  norm_num

/-- **Relation to IUT IV, Theorem 1.10.** The coefficient `(l + 1)/24` of `log 𝔮` in the
procession-normalized bound of IUT IV, proof of Theorem 1.10, Step (v) (page 29; in this
library `IUT.PaperIV.Theorem1_10.procession_average_l`) is the average
`(1/l*)·∑_{j=1}^{l*} j²/(2l)`. Joshi's coefficient averages `j²/l*²` instead, a different
normalization: `(1/12)(1 + 1/l*) = (1/l*)·(l + 1)/24`. -/
theorem joshi_coefficient_eq_div_iut4 (n : ℕ) (hn : 1 ≤ n) :
    1 / 12 * (1 + 1 / (n : ℝ)) = 1 / (n : ℝ) * (((2 * n + 1 : ℝ) + 1) / 24) := by
  have hn0 : (n : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                               linarith
  field_simp
  ring

/-! ## Laniewski and Müller: quality, mass and gains -/

/-- The **logarithmic mass** (weak quality) `Y = log(abc)/log rad(abc)` of R. Laniewski and
K. Müller, *The quality plane of abc-triples and the decomposition into gains*,
arXiv 2610.03212, Definition 2.1. The quality `X = log c/log rad(abc)` of the same definition is
`IUT.ABC.FormalConjectures.quality`. -/
noncomputable def lmMass (a b c : ℕ) : ℝ :=
  Real.log ((a * b * c : ℕ) : ℝ) / Real.log (rad (a * b * c) : ℝ)

/-- **The mass bound** of Laniewski and Müller, Lemma 3.3 and Proposition 3.4, arXiv
2610.03212: for every `ε > 0` only finitely many triples have `Y > 3 + ε`. Their triples are
coprime positive integers `a + b = c` with `a < b`.

Laniewski and Müller, Lemma 3.3, state that this is equivalent to Szpiro's conjecture for Frey
curves (finitely many triples with Szpiro ratio `> 6 + ε`); that equivalence uses the minimal
discriminant and the conductor of the Frey curve and is not formalized. This is an open
statement, implied by the abc conjecture (`laniewskiMullerMassBound_of_ABC`). -/
def LaniewskiMullerMassBound : Prop :=
  ∀ ε : ℝ, 0 < ε → {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ t.1 < t.2.1 ∧ Nat.Coprime t.1 t.2.1 ∧
    t.1 + t.2.1 = t.2.2 ∧ 3 + ε < lmMass t.1 t.2.1 t.2.2}.Finite

/-- For positive `a + b = c`, `0 < log rad(abc)`. -/
theorem log_rad_pos_of_triple {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a + b = c) :
    0 < Real.log (rad (a * b * c) : ℝ) :=
  Real.log_pos (by exact_mod_cast (two_le_rad_of_triple ha hb h))

/-- **Laniewski and Müller, Proposition 3.4 (i), elementary part.** The abc conjecture implies
the mass bound. Their proof: `Y = λX < 3X` (Lemma 2.2). Combined with their Lemma 3.3 (not
formalized) this is "abc implies Szpiro for Frey curves". -/
theorem laniewskiMullerMassBound_of_ABC (h : ABC) : LaniewskiMullerMassBound := by
  intro ε hε
  refine (abcFinite_of_abc h (ε / 3) (by positivity)).subset ?_
  rintro ⟨a, b, c⟩ ⟨ha, hab, hcop, hsum, hY⟩
  dsimp only at ha hab hcop hsum hY ⊢
  have hb : 0 < b := by omega
  refine ⟨ha, hb, show 0 < c by omega, hcop, hsum, ?_⟩
  have hL := log_rad_pos_of_triple ha hb hsum
  have hY' : (3 + ε) * Real.log (rad (a * b * c) : ℝ) < Real.log ((a * b * c : ℕ) : ℝ) := by
    have := hY; unfold lmMass at this; rwa [lt_div_iff₀ hL] at this
  have h3 := log_mul_mul_lt_three_mul_log ha hb hsum
  have hc : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  have hrad : (0 : ℝ) < rad (a * b * c) := by exact_mod_cast rad_pos _
  show (rad (a * b * c) : ℝ) ^ (1 + ε / 3) < c
  rw [Real.rpow_def_of_pos hrad, ← Real.exp_log hc]
  apply Real.exp_lt_exp.2
  nlinarith

/-- For positive `a + b = c`: `c² ≤ 2abc`, since `a + b ≤ 2ab`. -/
theorem sq_le_two_mul_mul_mul {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a + b = c) :
    c ^ 2 ≤ 2 * (a * b * c) := by
  have h1 : a + b ≤ 2 * (a * b) := by nlinarith
  calc c ^ 2 = (a + b) * c := by rw [h]; ring
    _ ≤ 2 * (a * b) * c := Nat.mul_le_mul_right c h1
    _ = 2 * (a * b * c) := by ring

/-- **Laniewski and Müller, Proposition 3.4 (ii), elementary part.** The mass bound implies that
for every `ε > 0` only finitely many triples have quality `X > 3/2 + ε`.

The paper argues with `X = Y/λ` and `liminf λ ≥ 2` as `rad(abc) → ∞`, which uses the finiteness
of triples with a given radical (Mahler). The proof here avoids it: from `abc ≥ c²/2` one gets
`2 log c ≤ log 2 + log(abc)`, so a triple with `Y ≤ 3 + ε` and `X > 3/2 + ε` has
`ε·log c < (3/2 + ε)·log 2`, hence `c` is bounded. -/
theorem finite_quality_gt_of_laniewskiMullerMassBound (h : LaniewskiMullerMassBound) {ε : ℝ}
    (hε : 0 < ε) :
    {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ t.1 < t.2.1 ∧ Nat.Coprime t.1 t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧
      3 / 2 + ε < FormalConjectures.quality t.1 t.2.1 t.2.2}.Finite := by
  set B : ℕ := ⌈Real.exp ((3 / 2 + ε) * Real.log 2 / ε)⌉₊ with hB
  have hfin : ((range (B + 1) ×ˢ range (B + 1) ×ˢ range (B + 1) : Finset (ℕ × ℕ × ℕ)) :
      Set (ℕ × ℕ × ℕ)).Finite := Finset.finite_toSet _
  refine ((h ε hε).union hfin).subset ?_
  rintro ⟨a, b, c⟩ ⟨ha, hab, hcop, hsum, hX⟩
  dsimp only at ha hab hcop hsum hX
  by_cases hY : 3 + ε < lmMass a b c
  · exact Or.inl ⟨ha, hab, hcop, hsum, hY⟩
  right
  push Not at hY
  have hb : 0 < b := by omega
  have hL := log_rad_pos_of_triple ha hb hsum
  have hc : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  have habc : (0 : ℝ) < ((a * b * c : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos ha hb) (show 0 < c by omega)
  have hY' : Real.log ((a * b * c : ℕ) : ℝ) ≤ (3 + ε) * Real.log (rad (a * b * c) : ℝ) := by
    unfold lmMass at hY; rwa [div_le_iff₀ hL] at hY
  have hX' : (3 / 2 + ε) * Real.log (rad (a * b * c) : ℝ) < Real.log c := by
    unfold FormalConjectures.quality at hX
    rw [FormalConjectures.radical_eq_rad, lt_div_iff₀ hL] at hX
    exact hX
  have hlow : 2 * Real.log c ≤ Real.log 2 + Real.log ((a * b * c : ℕ) : ℝ) := by
    have hle : ((c ^ 2 : ℕ) : ℝ) ≤ ((2 * (a * b * c) : ℕ) : ℝ) := by
      exact_mod_cast sq_le_two_mul_mul_mul ha hb hsum
    have := Real.log_le_log (by exact_mod_cast pow_pos (show 0 < c by omega) 2) hle
    push_cast at this
    rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity)] at this
    push_cast at this ⊢
    linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have e1 : (3 / 2 + ε) * (2 * Real.log c - Real.log 2)
      ≤ (3 / 2 + ε) * ((3 + ε) * Real.log (rad (a * b * c) : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have e2 : (3 + ε) * ((3 / 2 + ε) * Real.log (rad (a * b * c) : ℝ)) < (3 + ε) * Real.log c :=
    mul_lt_mul_of_pos_left hX' (by linarith)
  have hlc : Real.log c < (3 / 2 + ε) * Real.log 2 / ε := by
    rw [lt_div_iff₀ hε]; nlinarith
  have hcB : (c : ℝ) ≤ B := by
    calc (c : ℝ) = Real.exp (Real.log c) := (Real.exp_log hc).symm
      _ ≤ Real.exp ((3 / 2 + ε) * Real.log 2 / ε) := Real.exp_le_exp.2 hlc.le
      _ ≤ B := Nat.le_ceil _
  have hcB' : c ≤ B := by exact_mod_cast hcB
  simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
  omega

/-- A **presentation** of a triple in the sense of Laniewski and Müller, Definition 4.1: a
positive integer `P` with `P ∣ abc` and `rad P = rad(abc)` (positivity follows from `P ∣ abc`
when `abc > 0`). -/
def IsLMPresentation (a b c P : ℕ) : Prop := P ∣ a * b * c ∧ rad P = rad (a * b * c)

/-- The exponent factor `f = log(abc)/log P` of Laniewski and Müller, Definition 4.1. -/
noncomputable def lmExponentFactor (a b c P : ℕ) : ℝ :=
  Real.log ((a * b * c : ℕ) : ℝ) / Real.log (P : ℝ)

/-- The approximation gain `G_a = log c/log P` of Laniewski and Müller, Definition 4.1. -/
noncomputable def lmApproximationGain (c P : ℕ) : ℝ := Real.log (c : ℝ) / Real.log (P : ℝ)

/-- The power gain `G_p = log P/log rad(abc)` of Laniewski and Müller, Definition 4.1. -/
noncomputable def lmPowerGain (a b c P : ℕ) : ℝ :=
  Real.log (P : ℝ) / Real.log (rad (a * b * c) : ℝ)

/-- The balance `λ = log(abc)/log c` of Laniewski and Müller, Definition 2.1. -/
noncomputable def lmBalance (a b c : ℕ) : ℝ := Real.log ((a * b * c : ℕ) : ℝ) / Real.log (c : ℝ)

/-- For a presentation `P` of a positive triple: `rad(abc) ≤ P ≤ abc`. -/
theorem rad_le_and_le_of_isLMPresentation {a b c P : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : a + b = c) (hP : IsLMPresentation a b c P) :
    rad (a * b * c) ≤ P ∧ P ≤ a * b * c := by
  have hpos : 0 < a * b * c := Nat.mul_pos (Nat.mul_pos ha hb) (by omega)
  have hP0 : 0 < P := Nat.pos_of_dvd_of_pos hP.1 hpos
  exact ⟨hP.2 ▸ rad_le hP0, Nat.le_of_dvd hpos hP.1⟩

/-- The logarithms of a presentation: `0 < log rad(abc) ≤ log P ≤ log(abc)` and `0 < log c`. -/
theorem log_bounds_of_isLMPresentation {a b c P : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : a + b = c) (hP : IsLMPresentation a b c P) :
    0 < Real.log (rad (a * b * c) : ℝ) ∧ Real.log (rad (a * b * c) : ℝ) ≤ Real.log (P : ℝ) ∧
      Real.log (P : ℝ) ≤ Real.log ((a * b * c : ℕ) : ℝ) ∧ 0 < Real.log (c : ℝ) := by
  obtain ⟨h1, h2⟩ := rad_le_and_le_of_isLMPresentation ha hb h hP
  have hr : (0 : ℝ) < rad (a * b * c) := by exact_mod_cast rad_pos _
  refine ⟨log_rad_pos_of_triple ha hb h, Real.log_le_log hr (by exact_mod_cast h1),
    Real.log_le_log (by linarith [(show ((rad (a * b * c) : ℕ) : ℝ) ≤ P by exact_mod_cast h1)])
      (by exact_mod_cast h2), Real.log_pos (by exact_mod_cast (show 1 < c by omega))⟩

/-- **Laniewski and Müller, Proposition 4.2, the identities**: for a presentation `P` of a
positive triple, `G_a·G_p = X`, `f·G_p = Y` and `λ·G_a = f`. Neither coprimality nor `a < b`
is needed. -/
theorem lm_dictionary_identities {a b c P : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a + b = c)
    (hP : IsLMPresentation a b c P) :
    lmApproximationGain c P * lmPowerGain a b c P = FormalConjectures.quality a b c ∧
      lmExponentFactor a b c P * lmPowerGain a b c P = lmMass a b c ∧
      lmBalance a b c * lmApproximationGain c P = lmExponentFactor a b c P := by
  obtain ⟨hn, hnp, -, hc⟩ := log_bounds_of_isLMPresentation ha hb h hP
  have hp : Real.log (P : ℝ) ≠ 0 := (lt_of_lt_of_le hn hnp).ne'
  unfold lmApproximationGain lmPowerGain lmExponentFactor lmMass lmBalance
    FormalConjectures.quality
  rw [FormalConjectures.radical_eq_rad]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp

/-- **Laniewski and Müller, Proposition 4.2, the bounds**: for a presentation `P` of a positive
triple, `1 ≤ f ≤ Y`, `1 ≤ G_p ≤ Y` and `1/λ ≤ G_a ≤ X`. -/
theorem lm_dictionary_bounds {a b c P : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a + b = c)
    (hP : IsLMPresentation a b c P) :
    1 ≤ lmExponentFactor a b c P ∧ lmExponentFactor a b c P ≤ lmMass a b c ∧
      1 ≤ lmPowerGain a b c P ∧ lmPowerGain a b c P ≤ lmMass a b c ∧
      1 / lmBalance a b c ≤ lmApproximationGain c P ∧
      lmApproximationGain c P ≤ FormalConjectures.quality a b c := by
  obtain ⟨hn, hnp, hpm, hc⟩ := log_bounds_of_isLMPresentation ha hb h hP
  have hp : 0 < Real.log (P : ℝ) := lt_of_lt_of_le hn hnp
  have hm : 0 < Real.log ((a * b * c : ℕ) : ℝ) := lt_of_lt_of_le hp hpm
  unfold lmApproximationGain lmPowerGain lmExponentFactor lmMass lmBalance
    FormalConjectures.quality
  rw [FormalConjectures.radical_eq_rad, one_div_div]
  refine ⟨(one_le_div hp).2 hpm, div_le_div_of_nonneg_left hm.le hn hnp,
    (one_le_div hn).2 hnp, div_le_div_of_nonneg_right hpm hn.le,
    div_le_div_of_nonneg_left hc.le hp hpm, div_le_div_of_nonneg_left hc.le hn hnp⟩

/-! ## van Frankenhuijsen: Lemmas 2.3, 4.1, 4.2 and 4.3 -/

/-- A triple of integers whose first and last entries are coprime has `gcd = 1`, in the
normalized form `Finset.univ.gcd x = 1` used by Mathlib's height of a tuple. -/
theorem finset_gcd_eq_one_of_isCoprime {x : Fin 3 → ℤ} (h : IsCoprime (x 0) (x 2)) :
    Finset.univ.gcd x = 1 := by
  have hu : IsUnit (Finset.univ.gcd x) :=
    h.isUnit_of_dvd' (Finset.gcd_dvd (mem_univ 0)) (Finset.gcd_dvd (mem_univ 2))
  rw [← Finset.normalize_gcd]
  exact normalize_eq_one.2 hu

/-- **Lemma 2.3 of M. van Frankenhuijsen, *Two Restricted ABC Conjectures*, arXiv 2010.09493,
for `K = ℚ`.** For `a = p/q` with coprime integers `p`, `q`, the point `(a : 1 - a : 1)` has the
primitive integer representative `(p : q - p : q)`, and `(aⁿ : 1 - aⁿ : 1)` has
`(pⁿ : qⁿ - pⁿ : qⁿ)`. With Mathlib's logarithmic height `Height.logHeight` of a tuple over `ℚ`:
`h(aⁿ : 1 - aⁿ : 1) ≤ n·h(a : 1 - a : 1) + log 2` and
`h(aⁿ : 1 - aⁿ : 1) ≥ n·h(a : 1 - a : 1) - n·log 2`. The heights are computed by Mathlib's
`Rat.logHeight_eq_max_abs_of_gcd_eq_one`; the general number field case is not formalized. -/
theorem vanFrankenhuijsen_lemma23_rat {p q : ℤ} (hpq : IsCoprime p q) (n : ℕ) :
    Height.logHeight (((↑) : ℤ → ℚ) ∘ ![p ^ n, q ^ n - p ^ n, q ^ n])
        ≤ n * Height.logHeight (((↑) : ℤ → ℚ) ∘ ![p, q - p, q]) + Real.log 2 ∧
      n * Height.logHeight (((↑) : ℤ → ℚ) ∘ ![p, q - p, q]) - n * Real.log 2
        ≤ Height.logHeight (((↑) : ℤ → ℚ) ∘ ![p ^ n, q ^ n - p ^ n, q ^ n]) := by
  set x : Fin 3 → ℤ := ![p, q - p, q] with hx
  set y : Fin 3 → ℤ := ![p ^ n, q ^ n - p ^ n, q ^ n] with hy
  have hgx : Finset.univ.gcd x = 1 := finset_gcd_eq_one_of_isCoprime (by simpa [hx] using hpq)
  have hgy : Finset.univ.gcd y = 1 :=
    finset_gcd_eq_one_of_isCoprime (by simpa [hy] using hpq.pow (m := n) (n := n))
  rw [Rat.logHeight_eq_max_abs_of_gcd_eq_one hgx, Rat.logHeight_eq_max_abs_of_gcd_eq_one hgy]
  set M1 := ⨆ i, |x i| with hM1
  set M2 := ⨆ i, |y i| with hM2
  have hbx : BddAbove (Set.range fun i => |x i|) := (Set.finite_range _).bddAbove
  have hby : BddAbove (Set.range fun i => |y i|) := (Set.finite_range _).bddAbove
  have hx0 : |p| ≤ M1 := by simpa [hx] using le_ciSup hbx 0
  have hx2 : |q| ≤ M1 := by simpa [hx] using le_ciSup hbx 2
  have hy0 : |p| ^ n ≤ M2 := by simpa [hy, abs_pow] using le_ciSup hby 0
  have hy2 : |q| ^ n ≤ M2 := by simpa [hy, abs_pow] using le_ciSup hby 2
  -- `max(|p|, |q|) ≥ 1`
  have hm1 : 1 ≤ max |p| |q| := by
    by_contra hc
    push Not at hc
    have hp0 : p = 0 := abs_nonpos_iff.1 (by omega)
    have hq0 : q = 0 := abs_nonpos_iff.1 (by omega)
    rw [hp0, hq0, isCoprime_zero_left] at hpq
    exact not_isUnit_zero hpq
  have hM1pos : 1 ≤ M1 := hm1.trans (max_le hx0 hx2)
  have hmn : max |p| |q| ^ n ≤ M2 := by
    rcases le_total |p| |q| with hle | hle
    · rw [max_eq_right hle]; exact hy2
    · rw [max_eq_left hle]; exact hy0
  have hM2pos : 1 ≤ M2 := (one_le_pow₀ hm1).trans hmn
  -- upper bound `M2 ≤ 2·M1^n`
  have hup : M2 ≤ 2 * M1 ^ n := by
    have hp' : |p| ^ n ≤ M1 ^ n := pow_le_pow_left₀ (abs_nonneg _) hx0 n
    have hq' : |q| ^ n ≤ M1 ^ n := pow_le_pow_left₀ (abs_nonneg _) hx2 n
    have hM1n : 0 ≤ M1 ^ n := pow_nonneg (by omega) n
    apply ciSup_le
    intro i
    fin_cases i <;> simp [hy, abs_pow]
    · linarith
    · calc |q ^ n - p ^ n| ≤ |q ^ n| + |p ^ n| := abs_sub _ _
        _ ≤ 2 * M1 ^ n := by rw [abs_pow, abs_pow]; linarith
    · linarith
  -- lower bound `M1^n ≤ 2^n·M2`
  have hlow : M1 ^ n ≤ 2 ^ n * M2 := by
    have hM1le : M1 ≤ 2 * max |p| |q| := by
      apply ciSup_le
      intro i
      have h1 := le_max_left |p| |q|
      have h2 := le_max_right |p| |q|
      fin_cases i <;> simp [hx]
      · linarith
      · calc |q - p| ≤ |q| + |p| := abs_sub _ _
          _ ≤ 2 * max |p| |q| := by linarith
      · linarith
    calc M1 ^ n ≤ (2 * max |p| |q|) ^ n := pow_le_pow_left₀ (by omega) hM1le n
      _ = 2 ^ n * max |p| |q| ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * M2 := mul_le_mul_of_nonneg_left hmn (by positivity)
  have hM1r : (0 : ℝ) < (M1 : ℝ) := by exact_mod_cast (show (0 : ℤ) < M1 by omega)
  have hM2r : (0 : ℝ) < (M2 : ℝ) := by exact_mod_cast (show (0 : ℤ) < M2 by omega)
  constructor
  · have hc : (M2 : ℝ) ≤ 2 * (M1 : ℝ) ^ n := by exact_mod_cast hup
    have := Real.log_le_log hM2r hc
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at this
    linarith
  · have hc : (M1 : ℝ) ^ n ≤ 2 ^ n * (M2 : ℝ) := by exact_mod_cast hlow
    have := Real.log_le_log (by positivity) hc
    rw [Real.log_mul (by positivity) hM2r.ne', Real.log_pow, Real.log_pow] at this
    linarith

/-- **Lemma 4.1 of van Frankenhuijsen, arXiv 2010.09493, for `K = ℚ` and integers.** If
`p^k ∣ a - 1` with `k ≥ 1` (for `p` prime: `v_p(a - 1) ≥ k ≥ 1`), then `p^(k + 1) ∣ a^p - 1`.
The paper states it for `a` in a completion `K_v` with `p` the residue characteristic; this is
the case `K = ℚ`, `a ∈ ℤ`. The argument does not use that `p` is prime, so the hypothesis is
dropped. The proof
is the paper's: `a^p - 1 = (a - 1)·∑_{m < p} a^m` and the sum is `≡ p ≡ 0 (mod p)`. -/
theorem vanFrankenhuijsen_lemma41_int {p : ℕ} {a : ℤ} {k : ℕ} (hk : 1 ≤ k)
    (h : (p : ℤ) ^ k ∣ a - 1) : (p : ℤ) ^ (k + 1) ∣ a ^ p - 1 := by
  have hp1 : (p : ℤ) ∣ a - 1 := (dvd_pow_self (p : ℤ) (by omega)).trans h
  have ha1 : ((a : ℤ) : ZMod p) = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (a - 1) p).2 hp1
    push_cast at this
    exact sub_eq_zero.1 this
  have hsum : (p : ℤ) ∣ ∑ i ∈ range p, a ^ i := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1
    push_cast
    simp [ha1]
  rw [← geom_sum_mul, pow_succ, mul_comm (∑ i ∈ range p, a ^ i)]
  exact mul_dvd_mul h hsum

/-- **Lemma 4.2 of van Frankenhuijsen, arXiv 2010.09493.** For a complex number `α` with
`|α| = 1` and a real `d > 0` there is an exponent `1 ≤ m ≤ 8π·e^d` with `|α^m - 1| < e^(-d)/4`.
The proof uses Dirichlet's approximation theorem (Mathlib's
`Real.exists_int_int_abs_mul_sub_le`) instead of the paper's ordering of the points `α^j`. -/
theorem vanFrankenhuijsen_lemma42 {α : ℂ} (hα : ‖α‖ = 1) {d : ℝ} (hd : 0 < d) :
    ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ 8 * Real.pi * Real.exp d ∧
      ‖α ^ m - 1‖ < Real.exp (-d) / 4 := by
  set B := 8 * Real.pi * Real.exp d with hB
  have hB1 : 1 ≤ B := by
    have h1 := Real.pi_gt_three
    have h2 : 1 ≤ Real.exp d := Real.one_le_exp hd.le
    rw [hB]; nlinarith
  set n := ⌊B⌋₊ with hn
  have hn0 : 0 < n := Nat.floor_pos.2 hB1
  obtain ⟨j, k, hk0, hkn, hjk⟩ :=
    Real.exists_int_int_abs_mul_sub_le (Complex.arg α / (2 * Real.pi)) hn0
  have hkk : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk0.le
  refine ⟨k.toNat, by omega, ?_, ?_⟩
  · have : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast hkk
    rw [this]
    calc (k : ℝ) ≤ n := by exact_mod_cast hkn
      _ ≤ B := Nat.floor_le (by linarith)
  · have hαe : α = Complex.exp (Complex.arg α * Complex.I) := by
      have := Complex.norm_mul_exp_arg_mul_I α
      rw [hα] at this
      simpa using this.symm
    set t : ℝ := k * Complex.arg α - 2 * Real.pi * j with ht
    have hpow : α ^ k.toNat = Complex.exp (Complex.I * t) := by
      rw [hαe, ← Complex.exp_nat_mul]
      have h1 : Complex.exp (Complex.I * t)
          = Complex.exp ((k.toNat : ℂ) * (Complex.arg α * Complex.I))
            * Complex.exp (((-j : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) := by
        rw [← Complex.exp_add]
        congr 1
        have hkc : ((k.toNat : ℕ) : ℂ) = (k : ℂ) := by exact_mod_cast hkk
        rw [ht, hkc]
        push_cast
        ring
      rw [h1, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hpow]
    have hn1 : B < n + 1 := Nat.lt_floor_add_one B
    have hpi : 0 < Real.pi := Real.pi_pos
    have htle : |t| ≤ 2 * Real.pi / (n + 1) := by
      have e : t = 2 * Real.pi * (k * (Complex.arg α / (2 * Real.pi)) - j) := by
        rw [ht]; field_simp
      rw [e, abs_mul, abs_of_pos (by positivity), div_eq_mul_one_div (2 * Real.pi)]
      exact mul_le_mul_of_nonneg_left hjk (by positivity)
    calc ‖Complex.exp (Complex.I * t) - 1‖ ≤ ‖t‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
      _ = |t| := Real.norm_eq_abs t
      _ ≤ 2 * Real.pi / (n + 1) := htle
      _ < 2 * Real.pi / B := div_lt_div_of_pos_left (by positivity) (by linarith) hn1
      _ = Real.exp (-d) / 4 := by
        rw [hB, Real.exp_neg]
        field_simp
        ring

/-- **Lemma 4.3 of van Frankenhuijsen, arXiv 2010.09493.** For a complex number `a ≠ 0` and a
real `d > 0` with `|log|a|| < e^(-2d)/(32π)` there is an exponent `1 ≤ m ≤ 8π·e^d` with
`|a^m - 1| < e^(-d)`. The hypothesis `a ≠ 0` is implicit in the paper (`log|a|` must be
defined); it is needed here because Mathlib sets `Real.log 0 = 0`. The estimate of `|a|^m - 1`
uses `|e^y - 1| ≤ 2|y|` for `|y| ≤ 1` in place of the paper's `1/(1 - e^(-d)/4)`. -/
theorem vanFrankenhuijsen_lemma43 {a : ℂ} (ha : a ≠ 0) {d : ℝ} (hd : 0 < d)
    (hlog : |Real.log ‖a‖| < Real.exp (-2 * d) / (32 * Real.pi)) :
    ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ 8 * Real.pi * Real.exp d ∧ ‖a ^ m - 1‖ < Real.exp (-d) := by
  have hr : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hrc : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  set α : ℂ := a / (‖a‖ : ℂ) with hαdef
  have hα : ‖α‖ = 1 := by
    rw [hαdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne']
  obtain ⟨m, hm1, hmB, hm⟩ := vanFrankenhuijsen_lemma42 hα hd
  refine ⟨m, hm1, hmB, ?_⟩
  have hpi : 0 < Real.pi := Real.pi_pos
  set y : ℝ := (m : ℝ) * Real.log ‖a‖ with hy
  have hed : Real.exp (-d) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hed0 : 0 < Real.exp (-d) := Real.exp_pos _
  have hyb : |y| < Real.exp (-d) / 4 := by
    rw [hy, abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    calc (m : ℝ) * |Real.log ‖a‖| < m * (Real.exp (-2 * d) / (32 * Real.pi)) :=
          mul_lt_mul_of_pos_left hlog hm0
      _ ≤ 8 * Real.pi * Real.exp d * (Real.exp (-2 * d) / (32 * Real.pi)) :=
          mul_le_mul_of_nonneg_right hmB (by positivity)
      _ = Real.exp (-d) / 4 := by
          rw [show -2 * d = -d + -d by ring, Real.exp_add, Real.exp_neg]
          field_simp
          ring
  have hy1 : |y| ≤ 1 := by linarith
  have hexp : ‖a‖ ^ m = Real.exp y := by
    rw [hy, Real.exp_nat_mul, Real.exp_log hr]
  have h1 : |Real.exp y - 1| ≤ 2 * |y| := Real.abs_exp_sub_one_le hy1
  have h2 : Real.exp y ≤ 2 := by
    have := (abs_le.1 h1).2
    linarith
  have key : a ^ m - 1 = ((‖a‖ ^ m : ℝ) : ℂ) * (α ^ m - 1) + (((‖a‖ ^ m - 1 : ℝ)) : ℂ) := by
    have ha' : a = (‖a‖ : ℂ) * α := by rw [hαdef]; field_simp
    conv_lhs => rw [ha']
    push_cast
    ring
  have hpos : 0 < ‖a‖ ^ m := pow_pos hr m
  rw [key]
  calc ‖((‖a‖ ^ m : ℝ) : ℂ) * (α ^ m - 1) + (((‖a‖ ^ m - 1 : ℝ)) : ℂ)‖
      ≤ ‖((‖a‖ ^ m : ℝ) : ℂ) * (α ^ m - 1)‖ + ‖(((‖a‖ ^ m - 1 : ℝ)) : ℂ)‖ := norm_add_le _ _
    _ = ‖a‖ ^ m * ‖α ^ m - 1‖ + |‖a‖ ^ m - 1| := by
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos hpos]
    _ < 2 * (Real.exp (-d) / 4) + 2 * (Real.exp (-d) / 4) := by
        rw [hexp]
        have e1 : Real.exp y * ‖α ^ m - 1‖ < 2 * (Real.exp (-d) / 4) := by
          calc Real.exp y * ‖α ^ m - 1‖ < Real.exp y * (Real.exp (-d) / 4) :=
                mul_lt_mul_of_pos_left hm (Real.exp_pos y)
            _ ≤ 2 * (Real.exp (-d) / 4) := mul_le_mul_of_nonneg_right h2 (by positivity)
        linarith
    _ = Real.exp (-d) := by ring

/-! ## Vojta: triples with small radical -/

/-- **Restatement of `IUT.ABC.Variants.exists_coprime_triple_gt_mul_rad`** as an existence
statement with `<`, in the shape of P. Vojta, *A more general abc conjecture*, arXiv
math/9806171, Proposition 2.6 for `n = 3`: for every `ε > 0` there is a coprime triple of
positive integers `a + b = c` with `rad(abc) < ε·c`. The paper's form (`≤` on a Zariski-dense
set) is `infinite_coprime_triples_rad_le_mul`. -/
theorem exists_coprime_triple_rad_lt_mul {ε : ℝ} (hε : 0 < ε) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a.Coprime b ∧ a + b = c ∧
      (rad (a * b * c) : ℝ) < ε * c := by
  obtain ⟨a, b, c, ha, hb, hc, hab, habc, hlt⟩ := exists_coprime_triple_gt_mul_rad (1 / ε)
  refine ⟨a, b, c, ha, hb, hc, hab, habc, ?_⟩
  rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ hε] at hlt
  linarith

/-- **Vojta, Proposition 2.6, the case `n = 3`** (arXiv math/9806171; the paper says "for
`n = 3` this is already well known" and gives no proof). For every `ε > 0` the set of coprime
triples of positive integers `a + b = c` with `rad(abc) ≤ ε·c` is infinite. Vojta's statement is
a Zariski-dense set of points `[x_0 : x_1 : x_2]` with pairwise coprime coordinates on the line
`x_0 + x_1 + x_2 = 0`; on that line a set is Zariski dense if and only if it is infinite, and the
points `[a : b : -c]` from distinct positive triples are distinct. The triples used are
`1 + (3^(2^k) - 1) = 3^(2^k)` (`IUT.ABC.Variants.two_pow_mul_rad_family_lt`). -/
theorem infinite_coprime_triples_rad_le_mul {ε : ℝ} (hε : 0 < ε) :
    {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ Nat.Coprime t.1 t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧
      (rad (t.1 * t.2.1 * t.2.2) : ℝ) ≤ ε * t.2.2}.Infinite := by
  obtain ⟨k₀, hk₀⟩ := pow_unbounded_of_one_lt (3 / ε) (by norm_num : (1 : ℝ) < 2)
  set f : ℕ → ℕ × ℕ × ℕ := fun k => (1, 3 ^ 2 ^ (k + k₀) - 1, 3 ^ 2 ^ (k + k₀)) with hf
  have hinj : Function.Injective f := by
    intro k l hkl
    have h3 : 3 ^ 2 ^ (k + k₀) = 3 ^ 2 ^ (l + k₀) := congrArg (fun t => t.2.2) hkl
    have h2 := Nat.pow_right_injective (le_refl 2)
      (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h3)
    simpa using h2
  refine Set.infinite_of_injective_forall_mem hinj fun k => ?_
  set K := k + k₀ with hK
  have hc1 : 1 ≤ 3 ^ 2 ^ K := Nat.one_le_pow _ _ (by norm_num)
  have hc2 : 2 ≤ 3 ^ 2 ^ K := by
    calc 2 ≤ 3 ^ 1 := by norm_num
      _ ≤ 3 ^ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_two_pow)
  refine ⟨one_pos, show 0 < 3 ^ 2 ^ K - 1 by omega, Nat.coprime_one_left _,
    Nat.add_sub_of_le hc1, ?_⟩
  simp only [hf]
  have key := two_pow_mul_rad_family_lt K
  have hr : (2 : ℝ) ^ K * (rad (1 * (3 ^ 2 ^ K - 1) * 3 ^ 2 ^ K) : ℝ) <
      3 * ((3 ^ 2 ^ K : ℕ) : ℝ) := by exact_mod_cast key
  have h2K : 3 / ε < (2 : ℝ) ^ K :=
    hk₀.trans_le (pow_le_pow_right₀ (by norm_num) (by omega))
  have h3 : 3 < ε * (2 : ℝ) ^ K := by rwa [div_lt_iff₀ hε, mul_comm] at h2K
  have hcpos : (0 : ℝ) < ((3 ^ 2 ^ K : ℕ) : ℝ) := by positivity
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
  have hlt : (2 : ℝ) ^ K * (rad (1 * (3 ^ 2 ^ K - 1) * 3 ^ 2 ^ K) : ℝ)
      < (2 : ℝ) ^ K * (ε * ((3 ^ 2 ^ K : ℕ) : ℝ)) := by nlinarith
  exact (lt_of_mul_lt_mul_left hlt h2pos.le).le

/-! ## A polynomial corollary of Mathlib's Fermat–Catalan theorem -/

/-- **Lemma 4.2 of J. Cuevas Barrientos and H. Pasten, arXiv 2504.15971**, over any field of
characteristic zero (the paper works over `ℂ`): for coprime polynomials `f`, `g`, not both
constant, `f² + g³` is not constant. The paper's proof uses the Riemann–Hurwitz formula for a
map to the elliptic curve `y² = x³ + 1`; here it follows from Mathlib's
`Polynomial.flt_catalan` with exponents `(2, 3, 6)`, for which `3·6 + 6·2 + 2·3 = 2·3·6`. -/
theorem cuevasPasten_lemma42 {k : Type*} [Field k] [CharZero k] {f g : Polynomial k}
    (hfg : IsCoprime f g) (hnc : 0 < f.natDegree ∨ 0 < g.natDegree) :
    0 < (f ^ 2 + g ^ 3).natDegree := by
  by_contra hcon
  have h0 : (f ^ 2 + g ^ 3).natDegree = 0 := by omega
  set w := (f ^ 2 + g ^ 3).coeff 0 with hw
  have heq : f ^ 2 + g ^ 3 = Polynomial.C w := Polynomial.eq_C_of_natDegree_eq_zero h0
  by_cases hf : f = 0
  · rw [hf] at h0 hnc
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add,
      Polynomial.natDegree_pow] at h0
    simp at hnc
    omega
  by_cases hg : g = 0
  · rw [hg] at h0 hnc
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
      Polynomial.natDegree_pow] at h0
    simp at hnc
    omega
  by_cases hw0 : w = 0
  · rw [hw0, map_zero] at heq
    have hgu : IsUnit g := by
      refine hfg.symm.pow_right (n := 2) |>.isUnit_of_dvd' dvd_rfl ?_
      exact ⟨-(g ^ 2), by linear_combination heq⟩
    have hg0 : g.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hgu
    have hf2 : f ^ 2 = -(g ^ 3) := by linear_combination heq
    have hdeg := congrArg Polynomial.natDegree hf2
    rw [Polynomial.natDegree_neg, Polynomial.natDegree_pow, Polynomial.natDegree_pow, hg0] at hdeg
    omega
  have heq' : Polynomial.C 1 * f ^ 2 + Polynomial.C 1 * g ^ 3 + Polynomial.C (-w) * 1 ^ 6 = 0 := by
    rw [map_neg, map_one, one_mul, one_mul, one_pow, mul_one, heq]
    ring
  obtain ⟨hf0, hg0, -⟩ := Polynomial.flt_catalan (p := 2) (q := 3) (r := 6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Nat.cast_ne_zero.2 (by norm_num)) (Nat.cast_ne_zero.2 (by norm_num))
    (Nat.cast_ne_zero.2 (by norm_num)) hf hg one_ne_zero hfg one_ne_zero one_ne_zero
    (neg_ne_zero.2 hw0) heq'
  omega

/-! ## Pasten's `d(abc)` theorem -/

/-- **Theorem 16.7 (Theorem 1.11 in the introduction) of H. Pasten, *Shimura curves and the abc
conjecture*, arXiv 1705.09251**, the "`d(abc)`-Theorem": for every `ε > 0` there is `K_ε > 0`
such that all coprime positive integers `a + b = c` satisfy `d(abc) < K_ε·rad(abc)^(8/3 + ε)`,
where `d(n)` is the number of divisors of `n`. The inequality is strict as in the paper.

This is a theorem of that paper, proved there with modularity, Shimura curves and linear forms
in logarithms; it is **not proved in this library**.
The abc conjecture implies it (`pastenDivisorBound_of_ABC`). -/
def PastenDivisorBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → Nat.Coprime a b →
    a + b = c → ((a * b * c).divisors.card : ℝ) < K * (rad (a * b * c) : ℝ) ^ (8 / 3 + ε)

/-- `d(n) ≤ 2√n`: a divisor `d` with `d² > n` is `n/e` for the divisor `e = n/d` with
`e² < n`, and the divisors `e` with `e² ≤ n` are at most `⌊√n⌋` in number. -/
theorem card_divisors_le_two_mul_real_sqrt (n : ℕ) :
    (n.divisors.card : ℝ) ≤ 2 * Real.sqrt n := by
  classical
  set A := Finset.Icc 1 (Nat.sqrt n) with hA
  have hsub : n.divisors ⊆ A ∪ A.image (fun e => n / e) := by
    intro d hd
    have hn0 : n ≠ 0 := (Nat.mem_divisors.1 hd).2
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    obtain ⟨e, he⟩ := Nat.dvd_of_mem_divisors hd
    rcases le_or_gt (d * d) n with h | h
    · exact mem_union_left _ (mem_Icc.2 ⟨hd0, Nat.le_sqrt.2 h⟩)
    · apply mem_union_right
      have he0 : 0 < e := by
        rcases Nat.eq_zero_or_pos e with h0 | h0
        · rw [h0, mul_zero] at he; exact absurd he hn0
        · exact h0
      have hed : e < d := by
        by_contra hc
        push Not at hc
        have : d * d ≤ d * e := Nat.mul_le_mul_left d hc
        omega
      refine mem_image.2 ⟨e, mem_Icc.2 ⟨he0, Nat.le_sqrt.2 ?_⟩, ?_⟩
      · calc e * e ≤ d * e := Nat.mul_le_mul_right e hed.le
          _ = n := he.symm
      · rw [he, Nat.mul_div_cancel _ he0]
  have hcard : n.divisors.card ≤ A.card + A.card :=
    (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left card_image_le _))
  have hAc : A.card = Nat.sqrt n := by simp [hA]
  have h1 : (n.divisors.card : ℝ) ≤ 2 * (Nat.sqrt n : ℝ) := by
    have : n.divisors.card ≤ 2 * Nat.sqrt n := by omega
    exact_mod_cast this
  linarith [Real.nat_sqrt_le_real_sqrt (a := n)]

/-- **The abc conjecture implies Pasten's `d(abc)` bound.** From `d(n) ≤ 2√n` and `abc < c³`,
`d(abc) < 2c^(3/2)`; the abc conjecture with `ε = 1/2` gives `c ≤ K·rad(abc)^(3/2)`, hence
`d(abc) < 2K^(3/2)·rad(abc)^(9/4)`, and `9/4 < 8/3`. This elementary implication is not taken
from Pasten's paper. -/
theorem pastenDivisorBound_of_ABC (h : ABC) : PastenDivisorBound := by
  intro ε hε
  obtain ⟨K, hK, hb⟩ := h (1 / 2) (by norm_num)
  refine ⟨2 * K ^ (3 / 2 : ℝ), by positivity, fun a b c ha hb' hc hab habc => ?_⟩
  have hcK := hb a b c ha hb' hc hab habc
  rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num] at hcK
  set r : ℝ := (rad (a * b * c) : ℝ) with hr
  have hr1 : 1 ≤ r := one_le_rad_cast _
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  -- `d(abc) < 2·c^(3/2)`
  have hcube : ((a * b * c : ℕ) : ℝ) < (c : ℝ) ^ 3 := by
    exact_mod_cast mul_mul_lt_cube ha hb' habc
  have hd1 : ((a * b * c).divisors.card : ℝ) < 2 * (c : ℝ) ^ (3 / 2 : ℝ) := by
    have h1 := card_divisors_le_two_mul_real_sqrt (a * b * c)
    have h2 : Real.sqrt ((a * b * c : ℕ) : ℝ) < Real.sqrt ((c : ℝ) ^ 3) :=
      Real.sqrt_lt_sqrt (Nat.cast_nonneg _) hcube
    have h3 : Real.sqrt ((c : ℝ) ^ 3) = (c : ℝ) ^ (3 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hc0]
      norm_num
    rw [h3] at h2
    linarith
  -- `c^(3/2) ≤ K^(3/2)·r^(9/4)`
  have hd2 : (c : ℝ) ^ (3 / 2 : ℝ) ≤ K ^ (3 / 2 : ℝ) * r ^ (9 / 4 : ℝ) := by
    calc (c : ℝ) ^ (3 / 2 : ℝ) ≤ (K * r ^ (3 / 2 : ℝ)) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow hc0 hcK (by norm_num)
      _ = K ^ (3 / 2 : ℝ) * r ^ (9 / 4 : ℝ) := by
          rw [Real.mul_rpow hK.le (by positivity), ← Real.rpow_mul (by linarith)]
          norm_num
  have hd3 : r ^ (9 / 4 : ℝ) ≤ r ^ (8 / 3 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
  have hK32 : 0 < K ^ (3 / 2 : ℝ) := by positivity
  calc ((a * b * c).divisors.card : ℝ) < 2 * (c : ℝ) ^ (3 / 2 : ℝ) := hd1
    _ ≤ 2 * (K ^ (3 / 2 : ℝ) * r ^ (9 / 4 : ℝ)) := by linarith
    _ ≤ 2 * (K ^ (3 / 2 : ℝ) * r ^ (8 / 3 + ε)) := by
        have := mul_le_mul_of_nonneg_left hd3 hK32.le
        linarith
    _ = 2 * K ^ (3 / 2 : ℝ) * r ^ (8 / 3 + ε) := by ring

/-- The classical divisor bound `d(n) ≤ C_δ·n^δ` for every `δ > 0`. It is a classical theorem
that is not in Mathlib; it is not proved here and is used only as an explicit hypothesis of
`divisorCount_le_rad_rpow_of_ABC`. -/
def DivisorCountPowerBound : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ δ

/-- **Conditional on the divisor bound, the abc conjecture gives `d(abc) ≤ K_η·rad(abc)^η` for
every `η > 0`**, a better exponent than Pasten's `8/3 + ε`. From `abc < c³`, the abc conjecture
with `ε = 1` (`c ≤ K·rad(abc)²`) and `d(n) ≤ C·n^(η/6)`. -/
theorem divisorCount_le_rad_rpow_of_ABC (hdiv : DivisorCountPowerBound) (h : ABC) {η : ℝ}
    (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → Nat.Coprime a b → a + b = c →
      ((a * b * c).divisors.card : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ η := by
  obtain ⟨C, hC, hCb⟩ := hdiv (η / 6) (by positivity)
  obtain ⟨K, hK, hb⟩ := h 1 one_pos
  refine ⟨C * K ^ (η / 2), by positivity, fun a b c ha hb' hc hab habc => ?_⟩
  have hcK := hb a b c ha hb' hc hab habc
  rw [show (1 : ℝ) + 1 = 2 by norm_num] at hcK
  set r : ℝ := (rad (a * b * c) : ℝ) with hr
  have hr0 : 0 ≤ r := by positivity
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hn := hCb (a * b * c) (Nat.mul_pos (Nat.mul_pos ha hb') hc)
  have hcube : ((a * b * c : ℕ) : ℝ) ≤ (c : ℝ) ^ 3 := by
    exact_mod_cast (mul_mul_lt_cube ha hb' habc).le
  have h1 : ((a * b * c : ℕ) : ℝ) ^ (η / 6) ≤ (c : ℝ) ^ (η / 2) := by
    calc ((a * b * c : ℕ) : ℝ) ^ (η / 6) ≤ ((c : ℝ) ^ 3) ^ (η / 6) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hcube (by positivity)
      _ = (c : ℝ) ^ (η / 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hc0]
          congr 1
          push_cast
          ring
  have h2 : (c : ℝ) ^ (η / 2) ≤ K ^ (η / 2) * r ^ η := by
    calc (c : ℝ) ^ (η / 2) ≤ (K * r ^ (2 : ℝ)) ^ (η / 2) :=
          Real.rpow_le_rpow hc0 hcK (by positivity)
      _ = K ^ (η / 2) * r ^ η := by
          rw [Real.mul_rpow hK.le (by positivity), ← Real.rpow_mul hr0]
          congr 2
          ring
  calc ((a * b * c).divisors.card : ℝ) ≤ C * ((a * b * c : ℕ) : ℝ) ^ (η / 6) := hn
    _ ≤ C * (K ^ (η / 2) * r ^ η) := mul_le_mul_of_nonneg_left (h1.trans h2) hC.le
    _ = C * K ^ (η / 2) * r ^ η := by ring

end IUT.ABC.Elementary
