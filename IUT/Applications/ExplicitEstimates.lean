import Mathlib
import IUT.Applications.ABC
import IUT.ABC.Variants

/-!
# Explicit estimates in IUT: the explicit abc-type inequalities and their arithmetic

Source: S. Mochizuki, I. Fesenko, Y. Hoshi, A. Minamide, W. Porowski, *Explicit Estimates in
Inter-universal Teichmüller Theory* (58 pages). In that paper the PDF page number equals the
printed page number. Pages read for this file: 1 to 8, 21 to 23, 26 to 28, 32 to 57. Pages
checked against rendered images: 3 to 8, 21, 22, 23, 26, 27, 28, 32 to 57 (every display used
below was read from a render).

The paper states numerically explicit versions of the inequalities of IUT IV, Corollary 2.2,
conditional on IUT I to III in a slightly modified form (the "μ₆-version", its Sections 3
and 4). This file is not a formalization of that theory. It does three things.

1. It states, as propositions that are **not proved here and not assumed anywhere in this
   library**, two explicit inequalities of the paper for integer triples:
   * `Thm5_4Claim`: Theorem 5.4 (= Theorem B of the introduction), page 46 and 47;
   * `Thm5_3iiRationalClaim`: the case `L = ℚ` of Theorem 5.3 (ii), page 43, restricted to
     coprime integer triples;
   and the paper's elementary Lemma 5.7 (page 50) as `Lemma5_7Claim`, which the paper proves
   on pages 50 to 52 and which is not proved here. The conclusion of Corollary 5.8 (page 53)
   is `Cor5_8Statement`.
2. It proves implications with these propositions as explicit hypotheses: Corollary 5.8 from
   `Thm5_3iiRationalClaim` and `Lemma5_7Claim` (following the proof on pages 53 and 54,
   including the reduction to coprime triples), and the passage from either explicit
   inequality to the abc bound with exponent `3/2 + ε` or `3 + ε`.
3. It checks elementary numerical steps of the proofs of Theorem 5.1, Corollary 5.2,
   Theorem 5.3 and Theorem 5.4 (pages 34, 35, 40, 42, 43, 45, 48).

Why nothing here implies `Challenge.ABC`: the abc conjecture has exponent `1 + ε` on the
radical. Theorem 5.4 bounds `|abc|` by a constant times `rad(abc)^(3(1+ε))`, which bounds the
largest of the three numbers by `rad^(3+3ε)`; Theorem 5.3 (ii) for `ℚ` bounds the largest by
`rad^(3(1+ε)/2)`. Exponents `3/2 + ε` and `3 + ε` are weaker than `1 + ε`, and no argument
from them to exponent `1 + ε` is known. The conclusions below are therefore stated with the
library's fixed exponent bound `IUT.ABC.Variants.ABCWithExponent κ` for `κ = 3/2 + ε` and
`κ = 3 + ε`, never for `κ = 1 + ε`.

Interpretation recorded for `Thm5_3iiRationalClaim` (page 43): for `L = ℚ` one has
`d = 1`, `Δ_ℚ = 1`, and for nonzero integers `a`, `b`, `c` with `gcd(a, b) = 1` and
`a + b + c = 0` the height `H_ℚ(a, b, c)` (product over all places of
`max{|a|_v, |b|_v, |c|_v}`) equals `max{|a|, |b|, |c|}` (every nonarchimedean factor is `1`),
and `rad_ℚ(a, b, c)` (product of `p` over primes at which the three absolute values are not
all equal) equals `rad(|abc|)`. These identifications use the usual normalized absolute
values on `ℚ`; the paper's general conventions of its Section 0 were not read for this file.

Coprimality: the paper says "nonzero coprime integers" (Theorem 5.4) and "coprime positive
integers" (Lemma 5.7). Under `a + b + c = 0` (respectively `x^p + y^p = z^p`), coprimality of
the first two numbers is equivalent to coprimality of all three and to pairwise coprimality;
the statements below use `gcd` of the first two.
-/

namespace IUT.ExplicitEstimates

open Challenge Real IUT.ABC.Variants

/-! ## The paper's statements, as propositions -/

/-- The constant `h_1(ε) = 3.4 · 10^30 · ε^(−166/81)` of Theorem 5.3 and Corollary 5.2
(pages 36 and 43), case `d = 1`. -/
noncomputable def hOne (ε : ℝ) : ℝ := 3.4 * 10 ^ 30 * ε ^ (-(166 : ℝ) / 81)

/-- **Theorem 5.4 (Theorem B) of the paper, as a proposition; not proved here and not assumed
anywhere.** Pages 46 and 47 (statement also on page 4). For nonzero integers `a`, `b`, `c`
with `gcd(a, b) = 1` and `a + b + c = 0`, and every real `0 < ε ≤ 1`,
`|abc| ≤ 2^4 · max{exp(1.7 · 10^30 · ε^(−166/81)), rad(abc)^(3(1+ε))}`.
The paper derives it from Theorem 5.3, hence from its modified version of IUT I to III. -/
def Thm5_4Claim : Prop :=
  ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 → Int.gcd a b = 1 → a + b + c = 0 →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      |((a * b * c : ℤ) : ℝ)| ≤ 2 ^ 4 * max (exp (1.7 * 10 ^ 30 * ε ^ (-(166 : ℝ) / 81)))
        ((rad (a * b * c).natAbs : ℝ) ^ (3 * (1 + ε)))

/-- **Theorem 5.3 (ii) of the paper for `L = ℚ` and coprime integer triples, as a proposition;
not proved here and not assumed anywhere.** Page 43. With `d = 1` and `Δ_ℚ = 1`:
`max{|a|, |b|, |c|} ≤ 2^(5/2) · max{exp(h_1(ε)/4), rad(abc)^(3(1+ε)/2)}`.
The identification of `H_ℚ` and `rad_ℚ` for coprime integers is the interpretation recorded
in the module docstring. The paper's Theorem 5.3 is stated for all mono-complex fields and
all nonzero `a`, `b`, `c`; this is only the specialization used in Corollary 5.8. -/
def Thm5_3iiRationalClaim : Prop :=
  ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 → Int.gcd a b = 1 → a + b + c = 0 →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      max (max |(a : ℝ)| |(b : ℝ)|) |(c : ℝ)| ≤ (2 : ℝ) ^ ((5 : ℝ) / 2) *
        max (exp (1 / 4 * hOne ε)) ((rad (a * b * c).natAbs : ℝ) ^ (3 * (1 + ε) / 2))

/-- **Lemma 5.7 of the paper, as a proposition; not proved here.** Page 50: for a prime
`p ≥ 3` and coprime positive integers `x`, `y`, `z` with `x^p + y^p = z^p`, one has
`z > (p+1)^p / 2`, written here as `(p+1)^p < 2z`. The paper proves it by elementary means on
pages 48 to 52 (Lemmas 5.5 and 5.6); it does not depend on IUT. -/
def Lemma5_7Claim : Prop :=
  ∀ p : ℕ, p.Prime → 3 ≤ p → ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → Nat.Coprime x y →
    x ^ p + y ^ p = z ^ p → (p + 1) ^ p < 2 * z

/-- The conclusion of Corollary 5.8 of the paper (page 53; Corollary C on page 5): for every
prime `p > 1.615 · 10^14` there are no positive integers `x`, `y`, `z` with
`x^p + y^p = z^p`. -/
def Cor5_8Statement : Prop :=
  ∀ p : ℕ, p.Prime → (1.615 * 10 ^ 14 : ℝ) < p → ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z →
    x ^ p + y ^ p ≠ z ^ p

/-- The exponent `5/2` is a real exponent: `2^(5/2) = 4√2`, not `2^2`. -/
theorem two_rpow_five_halves : (2 : ℝ) ^ ((5 : ℝ) / 2) = 4 * √2 := by
  rw [show (5 : ℝ) / 2 = 2 + 1 / 2 by norm_num, rpow_add (by norm_num), sqrt_eq_rpow]
  norm_num

/-- `h_1(1) = 3.4 · 10^30`, the value used in Corollary 5.8 (page 53). -/
theorem hOne_one : hOne 1 = 3.4 * 10 ^ 30 := by simp [hOne]

/-! ## Elementary facts -/

/-- The second line of the displays of Theorems 5.3 (ii) and 5.4 (pages 43 and 47): when both
entries are at least `1`, the maximum is at most the product. -/
theorem max_le_mul_of_one_le_both {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) : max x y ≤ x * y :=
  max_le (le_mul_of_one_le_right (by linarith) hy) (le_mul_of_one_le_left (by linarith) hx)

/-- For nonzero integers, the radical of `|(x^p)(y^p)(z^p)|` is the radical of `xyz`. -/
theorem rad_natAbs_pow_triple (x y z p : ℕ) (hp : p ≠ 0) :
    rad ((x : ℤ) ^ p * (y : ℤ) ^ p * (-((z : ℤ) ^ p))).natAbs = rad (x * y * z) := by
  have : ((x : ℤ) ^ p * (y : ℤ) ^ p * (-((z : ℤ) ^ p))).natAbs = (x * y * z) ^ p := by
    simp [Int.natAbs_mul, Int.natAbs_pow, mul_pow]
  rw [this]
  unfold rad
  rw [Nat.primeFactors_pow _ hp]

/-! ## From the explicit inequalities to abc-type bounds -/

/-- **Theorem 5.4, specialized to positive triples `a + b = c`.** Applying the statement to
`(a, b, -c)` and using `c ≤ abc`:
`c ≤ 2^4 · max{exp(1.7 · 10^30 · ε^(−166/81)), rad(abc)^(3(1+ε))}`. -/
theorem c_le_of_thm5_4Claim (h : Thm5_4Claim) {a b c : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) (habc : a + b = c) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (c : ℝ) ≤ 2 ^ 4 * max (exp (1.7 * 10 ^ 30 * ε ^ (-(166 : ℝ) / 81)))
      ((rad (a * b * c) : ℝ) ^ (3 * (1 + ε))) := by
  have hc : 0 < c := by omega
  have key := h a b (-c) (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne')
    (by simp; omega) (by simpa [Int.gcd_natCast_natCast] using hab)
    (by rw [← habc]; push_cast; ring) ε hε0 hε1
  have hn : ((a : ℤ) * b * -(c : ℤ)).natAbs = a * b * c := by
    simp [Int.natAbs_mul]
  rw [hn] at key
  have habs : |(((a : ℤ) * b * -(c : ℤ) : ℤ) : ℝ)| = (a : ℝ) * b * c := by
    push_cast
    rw [show (a : ℝ) * b * -c = -(a * b * c) by ring, abs_neg, abs_of_nonneg (by positivity)]
  rw [habs] at key
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hc0 : (0 : ℝ) ≤ c := by positivity
  have : (c : ℝ) ≤ a * b * c := by
    have : (1 : ℝ) ≤ a * b := one_le_mul_of_one_le_of_one_le ha1 hb1
    nlinarith
  linarith

/-- **Theorem 5.3 (ii) for `ℚ`, specialized to positive triples `a + b = c`.** Applying the
statement to `(a, b, -c)`:
`c ≤ 2^(5/2) · max{exp(h_1(ε)/4), rad(abc)^(3(1+ε)/2)}`. -/
theorem c_le_of_thm5_3iiRationalClaim (h : Thm5_3iiRationalClaim) {a b c : ℕ} (ha : 0 < a)
    (hb : 0 < b) (hab : Nat.Coprime a b) (habc : a + b = c) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) :
    (c : ℝ) ≤ (2 : ℝ) ^ ((5 : ℝ) / 2) *
      max (exp (1 / 4 * hOne ε)) ((rad (a * b * c) : ℝ) ^ (3 * (1 + ε) / 2)) := by
  have key := h a b (-c) (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne')
    (by simp; omega) (by simpa [Int.gcd_natCast_natCast] using hab)
    (by rw [← habc]; push_cast; ring) ε hε0 hε1
  have hn : ((a : ℤ) * b * -(c : ℤ)).natAbs = a * b * c := by
    simp [Int.natAbs_mul]
  rw [hn] at key
  have hc : |(((-(c : ℤ)) : ℤ) : ℝ)| = c := by push_cast; rw [abs_neg, abs_of_nonneg (by positivity)]
  rw [hc] at key
  exact (le_max_right _ _).trans key

/-- **Theorem 5.4 implies the abc bound with exponent `3 + ε` for every `ε > 0`.** Given
`ε > 0`, apply `c_le_of_thm5_4Claim` with `ε' = min(ε/3, 1)` and bound the maximum by the
product. The exponent `3 + ε` is weaker than the `1 + ε` of `Challenge.ABC`. -/
theorem abcWithExponent_three_add_of_thm5_4Claim (h : Thm5_4Claim) :
    ∀ ε : ℝ, 0 < ε → ABCWithExponent (3 + ε) := by
  intro ε hε
  unfold ABCWithExponent
  set ε' := min (ε / 3) 1 with hε'
  have hε'0 : 0 < ε' := lt_min (by linarith) one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hε'3 : 3 * ε' ≤ ε := by have := min_le_left (ε / 3) 1; linarith
  set E := exp (1.7 * 10 ^ 30 * ε' ^ (-(166 : ℝ) / 81))
  refine ⟨2 ^ 4 * E, by positivity, ?_⟩
  intro a b c ha hb hc hab habc
  have key := c_le_of_thm5_4Claim h ha hb hab habc hε'0 hε'1
  have hR := IUT.ABC.one_le_rad_cast (a * b * c)
  have hE : 1 ≤ E := one_le_exp (by positivity)
  have hRp : (1 : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (3 * (1 + ε')) :=
    one_le_rpow hR (by positivity)
  have hmono : (rad (a * b * c) : ℝ) ^ (3 * (1 + ε')) ≤ (rad (a * b * c) : ℝ) ^ (3 + ε) :=
    rpow_le_rpow_of_exponent_le hR (by linarith)
  have hmax := max_le_mul_of_one_le_both hE hRp
  have h0 : (0 : ℝ) ≤ E := by positivity
  calc (c : ℝ) ≤ 2 ^ 4 * max E ((rad (a * b * c) : ℝ) ^ (3 * (1 + ε'))) := key
    _ ≤ 2 ^ 4 * (E * (rad (a * b * c) : ℝ) ^ (3 * (1 + ε'))) := by gcongr
    _ ≤ 2 ^ 4 * (E * (rad (a * b * c) : ℝ) ^ (3 + ε)) := by gcongr
    _ = 2 ^ 4 * E * (rad (a * b * c) : ℝ) ^ (3 + ε) := by ring

/-- **Theorem 5.3 (ii) for `ℚ` implies the abc bound with exponent `3/2 + ε` for every
`ε > 0`.** Given `ε > 0`, apply `c_le_of_thm5_3iiRationalClaim` with `ε' = min(2ε/3, 1)`, so
`3(1+ε')/2 ≤ 3/2 + ε`. The exponent `3/2 + ε` is weaker than the `1 + ε` of `Challenge.ABC`. -/
theorem abcWithExponent_three_halves_add_of_thm5_3iiRationalClaim (h : Thm5_3iiRationalClaim) :
    ∀ ε : ℝ, 0 < ε → ABCWithExponent (3 / 2 + ε) := by
  intro ε hε
  unfold ABCWithExponent
  set ε' := min (2 * ε / 3) 1 with hε'
  have hε'0 : 0 < ε' := lt_min (by linarith) one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hε'3 : 3 * ε' ≤ 2 * ε := by have := min_le_left (2 * ε / 3) 1; linarith
  set E := exp (1 / 4 * hOne ε')
  refine ⟨(2 : ℝ) ^ ((5 : ℝ) / 2) * E, by positivity, ?_⟩
  intro a b c ha hb hc hab habc
  have key := c_le_of_thm5_3iiRationalClaim h ha hb hab habc hε'0 hε'1
  have hR := IUT.ABC.one_le_rad_cast (a * b * c)
  have hE : 1 ≤ E := one_le_exp (by unfold hOne; positivity)
  have hRp : (1 : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (3 * (1 + ε') / 2) :=
    one_le_rpow hR (by positivity)
  have hmono : (rad (a * b * c) : ℝ) ^ (3 * (1 + ε') / 2) ≤ (rad (a * b * c) : ℝ) ^ (3 / 2 + ε) :=
    rpow_le_rpow_of_exponent_le hR (by linarith)
  have hmax := max_le_mul_of_one_le_both hE hRp
  have h0 : (0 : ℝ) ≤ E := by positivity
  calc (c : ℝ) ≤ (2 : ℝ) ^ ((5 : ℝ) / 2) * max E ((rad (a * b * c) : ℝ) ^ (3 * (1 + ε') / 2)) :=
        key
    _ ≤ (2 : ℝ) ^ ((5 : ℝ) / 2) * (E * (rad (a * b * c) : ℝ) ^ (3 * (1 + ε') / 2)) := by
        gcongr
    _ ≤ (2 : ℝ) ^ ((5 : ℝ) / 2) * (E * (rad (a * b * c) : ℝ) ^ (3 / 2 + ε)) := by gcongr
    _ = (2 : ℝ) ^ ((5 : ℝ) / 2) * E * (rad (a * b * c) : ℝ) ^ (3 / 2 + ε) := by ring

/-! ## Corollary 5.8: the numerical part (page 54) -/

/-- Page 54: `1/log(2) > 1.44`. -/
theorem one_div_log_two_gt_one_point_four_four : (1.44 : ℝ) < 1 / log 2 := by
  have h := log_two_lt_d9
  have h0 : 0 < log 2 := by positivity
  rw [lt_div_iff₀ h0]
  nlinarith

/-- Page 54: `5/2 + log₂(e) · (1/4) · h_1(1) < 1.227 · 10^30`, with `log₂(e) = 1/log(2)` and
`h_1(1) = 3.4 · 10^30`. -/
theorem cor5_8_right_bound :
    5 / 2 + 1 / log 2 * (1 / 4 * (3.4 * 10 ^ 30)) < (1.227 * 10 ^ 30 : ℝ) := by
  have h := log_two_gt_d9
  have h0 : 0 < log 2 := by positivity
  have e : 1 / log 2 * (1 / 4 * (3.4 * 10 ^ 30)) = (8.5 * 10 ^ 29) / log 2 := by ring
  rw [e]
  have : (8.5 * 10 ^ 29) / log 2 < 1.2269 * 10 ^ 30 := by
    rw [div_lt_iff₀ h0]
    nlinarith
  linarith

/-- `log x ≥ 32.7` for `x ≥ 1.615 · 10^14`, from `log 2 > 0.6931471803`, the factorization
`1.615 · 10^14 = 2^47 · (1.615 · 10^14 / 2^47)` and `log y ≥ 1 − 1/y`. -/
theorem log_ge_of_ge_threshold {x : ℝ} (hx : 1.615 * 10 ^ 14 ≤ x) : 32.7 ≤ log x := by
  have h2 := log_two_gt_d9
  have hpos : (0 : ℝ) < 1.615 * 10 ^ 14 := by norm_num
  have e : (1.615 * 10 ^ 14 : ℝ) = 2 ^ 47 * (1.615 * 10 ^ 14 / 2 ^ 47) := by ring
  have h1 : log (1.615 * 10 ^ 14 : ℝ) = 47 * log 2 + log (1.615 * 10 ^ 14 / 2 ^ 47) := by
    rw [e, log_mul (by norm_num) (by norm_num), log_pow]
    norm_num
  have h3 := one_sub_inv_le_log_of_pos (x := (1.615 * 10 ^ 14 / 2 ^ 47 : ℝ)) (by norm_num)
  have h4 : log (1.615 * 10 ^ 14 : ℝ) ≤ log x := log_le_log hpos hx
  norm_num at h3 h1
  norm_num
  linarith

/-- Page 54: for `x > 1.615 · 10^14`, `(x − 9)(−1 + 1.44 · x · log(x + 1)) > 1.227 · 10^30`.
The paper argues by monotonicity of this function on `x ≥ 9`; here the two factors are
bounded below separately. -/
theorem cor5_8_left_bound {x : ℝ} (hx : 1.615 * 10 ^ 14 < x) :
    (1.227 * 10 ^ 30 : ℝ) < (x - 9) * (-1 + 1.44 * x * log (x + 1)) := by
  have hl := log_ge_of_ge_threshold (x := x + 1) (by linarith)
  have h1 : (1.615 * 10 ^ 14 - 9 : ℝ) ≤ x - 9 := by linarith
  have h2 : (1.44 * (1.615 * 10 ^ 14) * 32.7 - 1 : ℝ) ≤ -1 + 1.44 * x * log (x + 1) := by
    have := mul_le_mul hx.le hl (by norm_num) (by linarith)
    nlinarith
  have h3 : (1.227 * 10 ^ 30 : ℝ) <
      (1.615 * 10 ^ 14 - 9) * (1.44 * (1.615 * 10 ^ 14) * 32.7 - 1) := by
    norm_num
  calc (1.227 * 10 ^ 30 : ℝ) < _ := h3
    _ ≤ _ := mul_le_mul h1 h2 (by norm_num) (by linarith)

/-- **The contradiction of pages 53 and 54, for a real `z`.** If `p > 1.615 · 10^14`,
`z > (p+1)^p / 2` and `z^p ≤ 2^(5/2) · exp(h_1(1)/4) · z^9`, then contradiction. The proof
follows the paper: `z^(p−9) ≤ 2^(5/2) · exp(h_1(1)/4)`, take `log₂`, and compare
`(p − 9)(−1 + p · log₂(p+1))` with `1.227 · 10^30` from both sides. -/
theorem cor5_8_contradiction {p : ℕ} {z : ℝ} (hp : (1.615 * 10 ^ 14 : ℝ) < p)
    (hz : ((p : ℝ) + 1) ^ p < 2 * z)
    (hbound : z ^ p ≤ (2 : ℝ) ^ ((5 : ℝ) / 2) * exp (1 / 4 * (3.4 * 10 ^ 30)) * z ^ 9) :
    False := by
  have hp9 : 9 ≤ p := by
    have : (9 : ℝ) < p := by linarith
    exact_mod_cast this.le
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  -- `z ≥ 1`, since `(p+1)^p ≥ p + 1 ≥ 2`
  have hpow : (p : ℝ) + 1 ≤ ((p : ℝ) + 1) ^ p :=
    le_self_pow₀ (by linarith) (by omega)
  have hz1 : 1 ≤ z := by linarith
  have hz0 : 0 < z := by linarith
  -- `z^(p−9) ≤ C`
  set C : ℝ := (2 : ℝ) ^ ((5 : ℝ) / 2) * exp (1 / 4 * (3.4 * 10 ^ 30)) with hC
  have hCpos : 0 < C := by positivity
  have hsplit : z ^ p = z ^ (p - 9) * z ^ 9 := by rw [← pow_add, Nat.sub_add_cancel hp9]
  have h9 : 0 < z ^ 9 := by positivity
  have hzp : z ^ (p - 9) ≤ C := by
    rw [hsplit] at hbound
    exact le_of_mul_le_mul_right hbound h9
  -- take logarithms
  have hlogC : log C = 5 / 2 * log 2 + 1 / 4 * (3.4 * 10 ^ 30) := by
    rw [hC, log_mul (by positivity) (by positivity), log_rpow (by norm_num), log_exp]
  have hA : ((p - 9 : ℕ) : ℝ) * log z ≤ log C := by
    rw [← log_pow]
    exact log_le_log (by positivity) hzp
  have hB : (p : ℝ) * log ((p : ℝ) + 1) < log 2 + log z := by
    rw [← log_pow, ← log_mul (by norm_num) hz0.ne']
    exact log_lt_log (by positivity) hz
  have hcast : ((p - 9 : ℕ) : ℝ) = (p : ℝ) - 9 := by
    rw [Nat.cast_sub hp9]
    norm_num
  rw [hcast, hlogC] at hA
  have hpm9 : 0 < (p : ℝ) - 9 := by linarith
  -- `(p − 9)(p · log(p+1) − log 2) < (5/2) · log 2 + h_1(1)/4`
  have hmain : ((p : ℝ) - 9) * ((p : ℝ) * log ((p : ℝ) + 1) - log 2)
      < 5 / 2 * log 2 + 1 / 4 * (3.4 * 10 ^ 30) := by
    have := mul_lt_mul_of_pos_left (by linarith : (p : ℝ) * log ((p : ℝ) + 1) - log 2 < log z)
      hpm9
    linarith
  -- divide by `log 2`, that is, pass to `log₂`
  have hL := log_two_gt_d9
  have hL0 : 0 < log 2 := by positivity
  set u : ℝ := 1 / log 2 with hu
  have hu0 : 0 < u := by positivity
  have huL : u * log 2 = 1 := by rw [hu]; field_simp
  have hlog2 : ((p : ℝ) - 9) * (-1 + (p : ℝ) * log ((p : ℝ) + 1) * u)
      < 5 / 2 + u * (1 / 4 * (3.4 * 10 ^ 30)) := by
    have := mul_lt_mul_of_pos_left hmain hu0
    have e1 : u * (((p : ℝ) - 9) * ((p : ℝ) * log ((p : ℝ) + 1) - log 2))
        = ((p : ℝ) - 9) * (-1 + (p : ℝ) * log ((p : ℝ) + 1) * u) := by
      linear_combination (-((p : ℝ) - 9)) * huL
    have e2 : u * (5 / 2 * log 2 + 1 / 4 * (3.4 * 10 ^ 30))
        = 5 / 2 + u * (1 / 4 * (3.4 * 10 ^ 30)) := by
      linear_combination (5 / 2) * huL
    linarith
  have hright := cor5_8_right_bound
  have hleft := cor5_8_left_bound hp
  have h144 := one_div_log_two_gt_one_point_four_four
  have hplog : 0 ≤ (p : ℝ) * log ((p : ℝ) + 1) :=
    mul_nonneg (by linarith) (log_nonneg (by linarith))
  have hcmp : ((p : ℝ) - 9) * (-1 + 1.44 * (p : ℝ) * log ((p : ℝ) + 1))
      ≤ ((p : ℝ) - 9) * (-1 + (p : ℝ) * log ((p : ℝ) + 1) * u) := by
    apply mul_le_mul_of_nonneg_left _ hpm9.le
    have := mul_le_mul_of_nonneg_left h144.le hplog
    nlinarith
  linarith

/-! ## Corollary 5.8 from the two hypotheses -/

/-- Corollary 5.8 for coprime triples: the core of the proof on pages 53 and 54. -/
theorem cor5_8_coprime (h53 : Thm5_3iiRationalClaim) (h57 : Lemma5_7Claim) {p : ℕ}
    (hp : p.Prime) (hpN : (1.615 * 10 ^ 14 : ℝ) < p) {x y z : ℕ} (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (hxy : Nat.Coprime x y) (heq : x ^ p + y ^ p = z ^ p) : False := by
  have hp3 : 3 ≤ p := by
    have : (3 : ℝ) < p := by linarith
    exact_mod_cast this.le
  have hp0 : p ≠ 0 := by omega
  -- Lemma 5.7
  have hL := h57 p hp hp3 x y z hx hy hz hxy heq
  -- Theorem 5.3 (ii) with `L = ℚ`, `(a, b, c) = (x^p, y^p, −z^p)`, `ε = 1`
  have key := h53 ((x : ℤ) ^ p) ((y : ℤ) ^ p) (-((z : ℤ) ^ p)) (by positivity)
    (by positivity) (by simp; omega)
    (by rw [show ((x : ℤ) ^ p) = ((x ^ p : ℕ) : ℤ) by push_cast; rfl,
      show ((y : ℤ) ^ p) = ((y ^ p : ℕ) : ℤ) by push_cast; rfl, Int.gcd_natCast_natCast]
        exact Nat.Coprime.pow p p hxy)
    (by
      have : ((x ^ p + y ^ p : ℕ) : ℤ) = ((z ^ p : ℕ) : ℤ) := by rw [heq]
      push_cast at this
      linarith) 1 one_pos le_rfl
  rw [rad_natAbs_pow_triple x y z p hp0] at key
  have hz' : |(((-((z : ℤ) ^ p)) : ℤ) : ℝ)| = (z : ℝ) ^ p := by
    push_cast
    rw [abs_neg, abs_of_nonneg (by positivity)]
  rw [hz'] at key
  have hzp := (le_max_right _ _).trans key
  -- simplify `ε = 1`
  have e1 : hOne 1 = 3.4 * 10 ^ 30 := hOne_one
  have e2 : (3 * (1 + 1) / 2 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
  rw [e1, e2, rpow_natCast] at hzp
  -- `rad(xyz) ≤ xyz ≤ z^3`
  have hxz : x ≤ z := by
    have : x ^ p ≤ z ^ p := by omega
    exact (Nat.pow_le_pow_iff_left hp0).mp this
  have hyz : y ≤ z := by
    have : y ^ p ≤ z ^ p := by omega
    exact (Nat.pow_le_pow_iff_left hp0).mp this
  have hrad : rad (x * y * z) ≤ z ^ 3 := by
    have h1 := IUT.ABC.rad_le (n := x * y * z) (by positivity)
    have h2 : x * y * z ≤ z * z * z := Nat.mul_le_mul (Nat.mul_le_mul hxz hyz) le_rfl
    calc rad (x * y * z) ≤ x * y * z := h1
      _ ≤ z * z * z := h2
      _ = z ^ 3 := by ring
  have hradR : (rad (x * y * z) : ℝ) ^ 3 ≤ ((z : ℝ) ^ 3) ^ 3 := by
    have : (rad (x * y * z) : ℝ) ≤ (z : ℝ) ^ 3 := by exact_mod_cast hrad
    exact pow_le_pow_left₀ (by positivity) this 3
  -- `max ≤ E · z^9`
  set E : ℝ := exp (1 / 4 * (3.4 * 10 ^ 30))
  have hE : 1 ≤ E := one_le_exp (by norm_num)
  have hz1 : (1 : ℝ) ≤ z := by exact_mod_cast hz
  have hz9 : (1 : ℝ) ≤ (z : ℝ) ^ 9 := one_le_pow₀ hz1
  have hmax : max E ((rad (x * y * z) : ℝ) ^ 3) ≤ E * (z : ℝ) ^ 9 := by
    apply max_le
    · exact le_mul_of_one_le_right (by linarith) hz9
    · calc (rad (x * y * z) : ℝ) ^ 3 ≤ ((z : ℝ) ^ 3) ^ 3 := hradR
        _ = (z : ℝ) ^ 9 := by ring
        _ ≤ E * (z : ℝ) ^ 9 := le_mul_of_one_le_left (by positivity) hE
  have hbound : (z : ℝ) ^ p ≤ (2 : ℝ) ^ ((5 : ℝ) / 2) * E * (z : ℝ) ^ 9 := by
    calc (z : ℝ) ^ p ≤ (2 : ℝ) ^ ((5 : ℝ) / 2) * max E ((rad (x * y * z) : ℝ) ^ 3) := hzp
      _ ≤ (2 : ℝ) ^ ((5 : ℝ) / 2) * (E * (z : ℝ) ^ 9) := by gcongr
      _ = _ := by ring
  have hz2 : ((p : ℝ) + 1) ^ p < 2 * (z : ℝ) := by exact_mod_cast hL
  exact cor5_8_contradiction hpN hz2 hbound

/-- **Corollary 5.8 of the paper, conditional on two named hypotheses.** If the case `L = ℚ`
of Theorem 5.3 (ii) (`Thm5_3iiRationalClaim`) and Lemma 5.7 (`Lemma5_7Claim`) hold, then for
every prime `p > 1.615 · 10^14` the equation `x^p + y^p = z^p` has no solution in positive
integers. Pages 53 and 54. The reduction to coprime `x`, `y`, `z`, which the paper takes
"without loss of generality", is proved here by dividing by `gcd(x, y)`. -/
theorem cor5_8_of_thm5_3iiRationalClaim_of_lemma5_7Claim (h53 : Thm5_3iiRationalClaim)
    (h57 : Lemma5_7Claim) : Cor5_8Statement := by
  intro p hp hpN x y z hx hy hz heq
  have hp0 : p ≠ 0 := hp.ne_zero
  set g := Nat.gcd x y with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left y hx
  obtain ⟨x', hx'⟩ := Nat.gcd_dvd_left x y
  obtain ⟨y', hy'⟩ := Nat.gcd_dvd_right x y
  rw [← hg] at hx' hy'
  -- `g ∣ z`
  have hgz : g ∣ z := by
    rw [← Nat.pow_dvd_pow_iff hp0, ← heq, hx', hy', mul_pow, mul_pow]
    exact Nat.dvd_add (Nat.dvd_mul_right _ _) (Nat.dvd_mul_right _ _)
  obtain ⟨z', hz'⟩ := hgz
  have hx'0 : 0 < x' := by
    rcases Nat.eq_zero_or_pos x' with h | h
    · rw [h] at hx'; omega
    · exact h
  have hy'0 : 0 < y' := by
    rcases Nat.eq_zero_or_pos y' with h | h
    · rw [h] at hy'; omega
    · exact h
  have hz'0 : 0 < z' := by
    rcases Nat.eq_zero_or_pos z' with h | h
    · rw [h] at hz'; omega
    · exact h
  have heq' : x' ^ p + y' ^ p = z' ^ p := by
    rw [hx', hy', hz', mul_pow, mul_pow, mul_pow, ← mul_add] at heq
    exact Nat.eq_of_mul_eq_mul_left (by positivity) heq
  have hcop : Nat.Coprime x' y' := by
    have := Nat.coprime_div_gcd_div_gcd (m := x) (n := y) hg0
    rw [← hg] at this
    have ex : x / g = x' := by rw [hx', Nat.mul_div_cancel_left _ hg0]
    have ey : y / g = y' := by rw [hy', Nat.mul_div_cancel_left _ hg0]
    rwa [ex, ey] at this
  exact cor5_8_coprime h53 h57 hp hpN hx'0 hy'0 hz'0 hcop heq'

/-! ## Elementary steps of the proofs of Theorems 5.3 and 5.4 -/

/-- **Page 45, end of the proof of Theorem 5.3 (ii), as real arithmetic.** Write `X` for
`(1/6) · h_non(j(E_{a,b,c}))`, `A` for `(1 + ε) · log(Δ_L · rad_L(a, b, c))`, `h` for
`h_d(ε)` and `logH` for `log(H_L(a, b, c))`. From Claim 5.3C
(`(2/(3d)) · logH − (5/3) · log 2 ≤ X`) and Theorem 5.3 (i) (`X ≤ max{A/d, h/6}`) follows
`logH ≤ max{(d/4) · h, (3/2) · A} + (5d/2) · log 2`. -/
theorem thm5_3_ii_log_step {d h A X logH : ℝ} (hd : 0 < d)
    (hC : 2 / (3 * d) * logH - 5 / 3 * log 2 ≤ X) (hi : X ≤ max (1 / d * A) (1 / 6 * h)) :
    logH ≤ max (d / 4 * h) (3 / 2 * A) + 5 * d / 2 * log 2 := by
  have h1 : logH ≤ 3 * d / 2 * (X + 5 / 3 * log 2) := by
    have e : 3 * d / 2 * (2 / (3 * d) * logH) = logH := by field_simp
    have := mul_le_mul_of_nonneg_left (by linarith : 2 / (3 * d) * logH ≤ X + 5 / 3 * log 2)
      (by positivity : (0 : ℝ) ≤ 3 * d / 2)
    linarith
  have h2 : 3 * d / 2 * X ≤ max (d / 4 * h) (3 / 2 * A) := by
    have := mul_le_mul_of_nonneg_left hi (by positivity : (0 : ℝ) ≤ 3 * d / 2)
    rw [mul_max_of_nonneg _ _ (by positivity)] at this
    have e1 : 3 * d / 2 * (1 / d * A) = 3 / 2 * A := by field_simp
    have e2 : 3 * d / 2 * (1 / 6 * h) = d / 4 * h := by ring
    rw [e1, e2, max_comm] at this
    exact this
  nlinarith

/-- **Page 43, end of the proof of Corollary 5.2:** for `x, y > 0` with `2x + y ≤ ε ≤ 1`,
`(1 − x)⁻¹ · (1 + y) ≤ 1 + ε`. -/
theorem inv_one_sub_mul_one_add_le {x y ε : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : 2 * x + y ≤ ε) (hε : ε ≤ 1) : (1 - x)⁻¹ * (1 + y) ≤ 1 + ε := by
  have hx1 : 0 < 1 - x := by linarith
  rw [inv_mul_le_iff₀ hx1]
  nlinarith

/-- **Page 48, end of the proof of Theorem 5.4, as real arithmetic.** With `C = ‖c‖`,
`P = ‖ab‖` (so `‖abc^(−2)‖ = P/C²`) and `M` the maximum in Claim 5.4A for `L = ℚ`: if
`C ≤ 2^(4/3) · M · (P/C²)^(−1/3)` then, raising to the third power, `P · C ≤ 2^4 · M^3`. -/
theorem thm5_4_cube_step {P C M : ℝ} (hP : 0 < P) (hC : 0 < C)
    (h : C ≤ (2 : ℝ) ^ ((4 : ℝ) / 3) * M * (P / C ^ 2) ^ (-(1 : ℝ) / 3)) :
    P * C ≤ 2 ^ 4 * M ^ 3 := by
  have hQ : 0 < P / C ^ 2 := by positivity
  have h3 := pow_le_pow_left₀ hC.le h 3
  have e1 : ((2 : ℝ) ^ ((4 : ℝ) / 3)) ^ 3 = 2 ^ 4 := by
    rw [← rpow_mul_natCast (by norm_num)]
    norm_num
  have e2 : ((P / C ^ 2) ^ (-(1 : ℝ) / 3)) ^ 3 = C ^ 2 / P := by
    rw [← rpow_mul_natCast hQ.le]
    norm_num
    rw [rpow_neg_one, inv_div]
  rw [mul_pow, mul_pow, e1, e2] at h3
  have hP' : C ^ 3 * P ≤ 2 ^ 4 * M ^ 3 * C ^ 2 := by
    have := mul_le_mul_of_nonneg_right h3 hP.le
    rw [show 2 ^ 4 * M ^ 3 * (C ^ 2 / P) * P = 2 ^ 4 * M ^ 3 * C ^ 2 by field_simp] at this
    exact this
  have hC2 : 0 < C ^ 2 := by positivity
  have : C ^ 2 * (P * C) ≤ C ^ 2 * (2 ^ 4 * M ^ 3) := by nlinarith
  exact le_of_mul_le_mul_left this hC2

/-- **Page 48: the cube of the maximum in Claim 5.4A for `L = ℚ`.**
`max{exp(x/6), R^(1+ε)}^3 = max{exp(x/2), R^(3(1+ε))}` for `R ≥ 0`; with
`x = 3.4 · 10^30 · ε^(−166/81)` this turns `(1/6) · 3.4 · 10^30` into `1.7 · 10^30`. -/
theorem thm5_4_max_cube {x R ε : ℝ} (hR : 0 ≤ R) :
    (max (exp (1 / 6 * x)) (R ^ (1 + ε))) ^ 3 = max (exp (1 / 2 * x)) (R ^ (3 * (1 + ε))) := by
  have hmono : Monotone (fun t : ℝ => t ^ 3) := (Odd.strictMono_pow (by decide)).monotone
  rw [hmono.map_max]
  congr 1
  · rw [← exp_nat_mul]
    norm_num
    ring_nf
  · rw [← rpow_mul_natCast hR]
    ring_nf

/-- Page 47 to 48: the constant `1.7 · 10^30` of Theorem 5.4 is `3 · (1/6) · 3.4 · 10^30`. -/
theorem thm5_4_constant : (3 : ℝ) * (1 / 6 * (3.4 * 10 ^ 30)) = 1.7 * 10 ^ 30 := by norm_num

/-! ## Elementary steps of the proof of Theorem 5.1 (pages 34 and 35) -/

/-- Page 34, replacement in Step (v): `4(l+5)/(l+1) = 4 + 16/(l+1) ≤ 4 + 100/l ≤ 4 + 10^(−13)`
for `l ≥ 10^15` (IUT IV used `4(l+5)/(l+1) ≤ 20/3`). -/
theorem four_mul_add_five_div_le {l : ℝ} (hl : 10 ^ 15 ≤ l) :
    4 * (l + 5) / (l + 1) ≤ 4 + 1 / 10 ^ 13 := by
  have hl0 : 0 < l := by linarith
  rw [div_le_iff₀ (by linarith)]
  have : 16 * 10 ^ 13 ≤ l := by linarith
  nlinarith

/-- Page 34: `e*_mod · l ≥ 2^12 · 3^3 · 5 · 10^15 ≥ η_prm = 5 · 10^20`, where
`e*_mod = 2^12 · 3^3 · 5 · e_mod` and `e_mod ≥ 1`, `l ≥ 10^15`. -/
theorem eStar_mul_l_ge_eta_prm {l e : ℝ} (hl : 10 ^ 15 ≤ l) (he : 1 ≤ e) :
    (5 * 10 ^ 20 : ℝ) ≤ (2 ^ 12 * 3 ^ 3 * 5 * e) * l := by
  have : (2 ^ 12 * 3 ^ 3 * 5 * 1 : ℝ) * 10 ^ 15 ≤ (2 ^ 12 * 3 ^ 3 * 5 * e) * l :=
    mul_le_mul (by linarith) hl (by norm_num) (by linarith)
  nlinarith

/-- Pages 34 and 35, replacement in Step (viii):
`10^(−5) · 1.022 · e*_mod · l ≥ (10^(−5) · 2^12 · 3^2 · 5) · 3l ≥ 3l ≥ 2 · log(l) + 56`
for `l ≥ 10^15` and `e_mod ≥ 1`. -/
theorem step_viii_absorb_mu6 {l e : ℝ} (hl : 10 ^ 15 ≤ l) (he : 1 ≤ e) :
    2 * log l + 56 ≤ 1 / 10 ^ 5 * 1.022 * (2 ^ 12 * 3 ^ 3 * 5 * e) * l := by
  have hl0 : 0 < l := by linarith
  have hlog : log l ≤ l := (log_le_sub_one_of_pos hl0).trans (by linarith)
  have h1 : (1 : ℝ) * l ≤ e * l := mul_le_mul_of_nonneg_right he hl0.le
  nlinarith

/-- Page 35: `(4 + 10^(−13) + 10^(−5)) · 1.022 ≤ (4 + 2 · 10^(−5)) · 1.022 ≤ 4.08803`. -/
theorem constant_4_08803 :
    (4 + 1 / 10 ^ 13 + 1 / 10 ^ 5 : ℝ) * 1.022 ≤ (4 + 2 / 10 ^ 5) * 1.022 ∧
      (4 + 2 / 10 ^ 5 : ℝ) * 1.022 ≤ 4.08803 := by
  norm_num

/-- Page 35, replacement in Step (viii): `(1 − 12/l²)⁻¹ = 1 + 12/(l² − 12) ≤ 1 + 100/l ≤
1 + 10^(−13)` for `l ≥ 10^15` (IUT IV used `(1 − 12/l²)⁻¹ ≤ 2`). -/
theorem inv_one_sub_twelve_div_sq_le {l : ℝ} (hl : 10 ^ 15 ≤ l) :
    (1 - 12 / l ^ 2)⁻¹ ≤ 1 + 1 / 10 ^ 13 := by
  have hl0 : 0 < l := by linarith
  have hl2 : 12 * 10 ^ 13 + 12 ≤ l ^ 2 := by nlinarith
  have e : 1 - 12 / l ^ 2 = (l ^ 2 - 12) / l ^ 2 := by field_simp
  rw [e, inv_div, div_le_iff₀ (by linarith)]
  nlinarith

/-- Page 35: `4.08803 · (1 + 10^(−13)) ≤ 4.0881`. -/
theorem constant_4_0881 : (4.08803 : ℝ) * (1 + 1 / 10 ^ 13) ≤ 4.0881 := by norm_num

/-- Page 35: `δ = 2^12 · 3^3 · 5 · d = 552960 · d`. -/
theorem delta_coefficient : (2 ^ 12 * 3 ^ 3 * 5 : ℝ) = 552960 := by norm_num

/-- Numerical estimates cited in the proof of Corollary 5.2 (pages 39, 40 and 42):
`1.00072 · (1.4621 + 0.0001) ≤ 1.464`; `1.464 · 1.45 ≤ 4`; `2^13 · 3^3 · 5 ≤ 10^15`;
`4.0881 · 1.464 ≤ 5.985`; `71.82 · (2^12 · 3^3 · 5)^2 ≥ 4 · 10^12`;
`(10^(−12) + 1 + 10^(−8)) · (1 − 10^(−7)) ≤ 1`. -/
theorem cor5_2_numerics :
    (1.00072 : ℝ) * (1.4621 + 0.0001) ≤ 1.464 ∧ (1.464 : ℝ) * 1.45 ≤ 4 ∧
      (2 ^ 13 * 3 ^ 3 * 5 : ℝ) ≤ 10 ^ 15 ∧ (4.0881 : ℝ) * 1.464 ≤ 5.985 ∧
      (4 * 10 ^ 12 : ℝ) ≤ 71.82 * (2 ^ 12 * 3 ^ 3 * 5) ^ 2 ∧
      (1 / 10 ^ 12 + 1 + 1 / 10 ^ 8 : ℝ) * (1 - 1 / 10 ^ 7) ≤ 1 := by
  norm_num

/-- Proposition 2.1 (page 21): the displayed factorizations of the four `j`-invariants.
`488095744/125 = 2^14 · 31^3 · 5^(−3)`, `1556068/81 = 2^2 · 73^3 · 3^(−4)`,
`1728 = 2^6 · 3^3`. -/
theorem prop2_1_factorizations :
    (488095744 / 125 : ℚ) = 2 ^ 14 * 31 ^ 3 / 5 ^ 3 ∧
      (1556068 / 81 : ℚ) = 2 ^ 2 * 73 ^ 3 / 3 ^ 4 ∧ (1728 : ℚ) = 2 ^ 6 * 3 ^ 3 := by
  norm_num

/-- Proof of Proposition 2.2 (i) (page 22), the algebraic part: if `log x ≥ 47.66` then
`1.17 / log x ≤ 0.0246`, and `x / (log x − 1.0246) ≤ 1.022 · x / log x` for `x > 0`. The
estimate `log(η_prm) ≥ 47.66` itself and the cited bound of Axler are not checked here. -/
theorem prop2_2_i_algebra {x L : ℝ} (hx : 0 < x) (hL : 47.66 ≤ L) :
    1.17 / L ≤ 0.0246 ∧ x / (L - 1.0246) ≤ 1.022 * x / L := by
  have hL0 : 0 < L := by linarith
  have hL1 : 0 < L - 1.0246 := by linarith
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ hL0]; linarith
  · rw [div_le_div_iff₀ hL1 hL0]
    nlinarith

end IUT.ExplicitEstimates
