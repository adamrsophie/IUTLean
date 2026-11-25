import IUT.Applications.ABC

/-!
# Rational points of the line minus three points and the abc conjecture

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Theorem A (page 3), the notation
recalled before Corollary 2.2 (page 40), Corollary 2.2 (pages 41 to 43, read for the setting
`X = ℙ¹_ℚ`, `D = {0, 1, ∞}`), and Corollary 2.3 with its proof and Remark 2.3.1 (pages 54 to 56).
Second source: Mochizuki, *Arithmetic Elliptic Curves in General Position* ([GenEll]), §1
(Definitions 1.1, 1.2, Example 1.3, Proposition 1.4, Remark 1.4.1, Definition 1.5,
Remark 1.5.1, Propositions 1.6 and 1.7; pages 3 to 10) and §2 (Theorem 2.1 and its proof;
pages 11 to 13), with its list of corrections, *Comments on "Arithmetic Elliptic Curves in
General Position"* (July 2016, pages 1 and 2), whose items (1), (2), (5) are repeated in
IUT IV, Remark 2.3.1.
Pages read for this file: IUT IV pages 3, 40 to 43, 54 to 56; [GenEll] pages 3 to 13; the
corrections, pages 1 and 2. Pages checked against rendered images: all of these.

**What this file proves.** It proves that a statement about rational points of the projective
line minus the three points `0`, `1`, `∞` (`VojtaLineMinusThreePointsRational`) is equivalent to
the abc conjecture `Challenge.ABC` (`vojta_iff_ABC`). It does not prove that statement. In the
papers that statement is a special case of IUT IV, Corollary 2.3 (equivalently Theorem A), whose
proof depends on IUT I to III and is not formalized here. Nothing here bears on whether that
proof is correct.

**The statement of the papers and what is dropped.** Corollary 2.3 (page 54) concerns a smooth,
proper, geometrically connected curve `X` over a number field, a reduced divisor `D` with
`U_X = X \ D` hyperbolic, a positive integer `d` and `ε > 0`, and asserts the inequality of
bounded discrepancy classes `ht_{ω_X(D)} ≲ (1 + ε)(log-diff_X + log-cond_D)` of functions on
`U_X(ℚ̄)^{≤d}`, the points defined over number fields of degree at most `d`. Here `α ≲ β` means
that `α - β` is bounded above by a constant (Remark 2.3.1 (ii), page 55). The proof (page 55)
reduces, through [GenEll] Theorem 2.1, to `X = ℙ¹_ℚ`, `D = {0, 1, ∞}`, and points in a compactly
bounded subset `K_V` of `U_X(ℚ̄)`. The proposition of this file keeps one curve
(`X = ℙ¹_ℚ`, `D = {0, 1, ∞}`) and one field (`d = 1`, points over `ℚ`), and drops: number fields
of bounded degree `d > 1`, the compactly bounded subsets `K_V` of the proof, and general
hyperbolic curves over number fields.

**Normalizations, checked against [GenEll].** Page 40 of IUT IV says: `ht_{ω_X(D)}` is the
normalized height on `U_X(ℚ̄)` attached to `ω_X(D)`, well defined up to a bounded discrepancy
([GenEll] Proposition 1.4 (iii)); `log-diff_X` is the normalized log-different ([GenEll]
Definition 1.5 (iii)); `log-cond_D` is the normalized log-conductor ([GenEll] Definition 1.5
(iv)). In [GenEll] these are defined on a normal, proper, flat model `X` over `ℤ`, and at a point
`x ∈ X(F)` are computed with the normalized degree `(1 / [F : ℚ]) · deg_F` of arithmetic
divisors on `Spec 𝒪_F`, which gives a finite prime `v` the weight `log q_v` (page 4). For a
rational point (`F = ℚ`) the normalization is division by `1`.

* Height (page 4, page 6, page 8). `ht_𝓜(x)` is the normalized degree of the pullback of an
  arithmetic line bundle `𝓜` (a line bundle on the model with a hermitian metric) along
  `Spec 𝒪_F → X`. By Proposition 1.4 (iii) its bounded discrepancy class depends only on the
  isomorphism class of the line bundle on the generic fiber, and by Remark 1.4.1 only on `X_ℚ`.
  For `X = ℙ¹_ℚ` and `D = {0, 1, ∞}`, `ω_X(D)` has degree `-2 + 3 = 1`, so it is `𝒪(1)`.
  What [GenEll] does not contain, and this file does not formalize, is the computation that
  `ht_{𝒪(1)}` at `x = a / c` in lowest terms equals `log max(|a|, |c|)` up to a bounded function
  (for `𝒪_ℙ(1)` on `ℙ¹_ℤ` with the Fubini-Study metric used on page 7 the value is
  `(1/2) log (a² + c²)`, within `(1/2) log 2` of `log max(|a|, |c|)`); that step is a standard
  computation recorded here as an unformalized link. This file uses Mathlib's
  `Height.logHeight₁` on `ℚ`, which Mathlib proves equal to `log max(|num x|, den x)`
  (`Rat.logHeight₁_eq_log_max`). Since `≲` absorbs bounded functions, any function at bounded
  distance from it gives an equivalent statement (`vojta_iff_rationalPointBoundFor`).
* Log-different (page 8, Definition 1.5 (iii)). It is the normalized degree of the arithmetic
  divisor of the different ideal of the minimal field of definition of `x`. For a rational point
  that field is `ℚ`, whose different is the unit ideal, so the log-different is exactly `0`.
* Log-conductor (page 8, Definition 1.5 (iv), with correction (12) of the comments: "conductor
  of `x` with respect to `D`"). Pull `D` back along `Spec 𝒪_F → X` to an effective divisor
  `D_x`; the conductor is `(D_x)_red`, an arithmetic divisor supported at the finite primes; the
  log-conductor is its normalized degree. So the archimedean place contributes nothing, each
  prime counts once whatever its multiplicity, and no prime (in particular not `2`) is treated
  differently. For the model `ℙ¹_ℤ` with `D` the closure of the three sections `0`, `1`, `∞`, a
  rational point `x = n / d` in lowest terms is the section `(n : d)`, and `D_x` is cut out by
  `n`, `n - d` and `d`. Hence the log-conductor is the sum of `log p` over the primes dividing
  `n`, `n - d` (the numerator of `x - 1`) or `d`, which is `log (ratConductor x)` exactly. This
  pullback computation is made here, not quoted from [GenEll]. Another model changes the value,
  but by Remark 1.5.1 (pages 8 and 9) only at finitely many primes, hence by a bounded function.

The relation `α ≲ β` means `α - β ≤ C` for a constant `C`: this is [GenEll] Definition 1.2 (ii)
(page 5) after correction (2) of the comments, which reverses the printed direction, repeated
as IUT IV Remark 2.3.1 (ii) (page 55). So the inequality `ht ≤ (1 + ε)(log-diff + log-cond) + C`
on rational points is the `d = 1` case of the inequality of Corollary 2.3, up to the
unformalized identification of the height named above.

**[GenEll] Theorem 2.1 and what remains between this file and the papers.** Theorem 2.1
(page 11) fixes a finite set `Σ` of prime numbers and asserts that two statements are
equivalent.
(i) For every smooth, proper, geometrically connected curve `X` over a number field, reduced
divisor `D` with `U_X = X \ D` hyperbolic (`deg ω_X(D) > 0`), positive integer `d` and `ε > 0`,
`ht_{ω_X(D)} ≲ (1 + ε)(log-diff_X + log-cond_D)` on `U_X(ℚ̄)^{≤d}`.
(ii) For `P = ℙ¹_ℚ`, `C = {0, 1, ∞}`, every positive integer `d`, every `ε > 0` and every
compactly bounded subset `K_V ⊆ U_P(ℚ̄)` (Example 1.3 (ii), pages 5 and 6, with correction (8): its
bounding domains lie in `U_P`) whose support contains `Σ`,
`ht_{ω_P(C)} ≲ (1 + ε)(log-diff_P + log-cond_C)` on `K_V ∩ U_P(ℚ̄)^{≤d}`.
The direction (i) ⟹ (ii) is immediate. The proof of (ii) ⟹ (i) (pages 11 to 13) passes to a
finite étale Galois covering `Y` of `U_X`, which raises the degree bound to
`d' = d · deg(Y/X)`, reduces to `D = ∅`, uses compactness at the places of a finite set `V` and
a noncritical Belyi map `X → P` (from an earlier paper of Mochizuki, cited as [Mzk1]
Theorem 2.5), and Propositions 1.4, 1.6 and 1.7; correction (5) replaces the last `≈` of the
final display by `ht_E ≲ 2 · (deg E / deg ω_X) · ht_{ω_X}` and adjusts the choice of `ε'`.

In IUT IV the chain is as follows. Corollary 2.2 (pages 41 to 43) constructs initial Θ-data to
which Theorem 1.10 is applied (Theorem 1.10 itself and the proof of Corollary 2.2 beyond its
first paragraph, page 43, are not among the pages read for this file). For `X = ℙ¹_ℚ`,
`D = {0, 1, ∞}` and a compactly bounded `K_V` whose support contains the prime `2` and which
satisfies a condition `(*_{j-inv})` at `2`, it identifies `(1/6) log 𝔮^∀` with `ht_{ω_X(D)}` up
to bounded discrepancy on `K_V` (part (i)); bounds `(1/6) log 𝔮^∀` by
`(1 + ε_E)(log-diff_X + log-cond_D) + C_K` for the points of `K_V` of degree at most `d` outside
a finite set (part (ii), condition (C2); this summary omits the conditions of part (ii) on the
field `F` and on the prime `l`, condition (C1)); and makes `ε_E ≤ ε` outside a finite set
(part (iii)). The proof of Corollary 2.3 (pages 54
and 55) says that Corollary 2.3 coincides with [GenEll] Theorem 2.1 (i), so by the equivalence
it suffices to prove (ii) with `Σ = {2}`; it adds the condition `(*_{j-inv})`, which the paper
says is vacuous for fixed `d`, and derives (ii) from Corollary 2.2 (i), (ii), (iii). The
proposition of this file is an instance of (i), not of (ii): it has no `K_V`. So reaching it
from IUT IV uses the direction (ii) ⟹ (i) of [GenEll] Theorem 2.1. On our reading of page 12
(not a sentence of the paper), that proof uses (ii) at the degree `d' > 1` of the covering even
for `d = 1` and `X = ℙ¹`, so a version of Corollary 2.2 for rational points alone would not
suffice through this route. None of Theorem 1.10,
Corollary 2.2, Theorem 2.1 of [GenEll], the Belyi map theorem, or the height computation above
is formalized here.

**Main results.**

* `logHeight₁_of_triple`, `ratConductor_of_triple`: for positive coprime `a`, `b` with
  `a + b = c`, the point `x = a / c` has height `log c` and conductor `rad (a b c)`.
* `exists_triple_of_ne`: every rational `x ∉ {0, 1}` gives such a triple, after clearing
  denominators and choosing signs, with height at most `log c` and conductor `rad (a b c)`.
* `vojta_iff_ABC`: the proposition is equivalent to `Challenge.ABC`.
* `ratConductor_one_sub`, `ratConductor_inv`: the conductor is invariant under the maps
  `x ↦ 1 - x` and `x ↦ 1 / x`, which generate the six permutations of `{0, 1, ∞}`;
  `abs_logHeight₁_one_sub_sub_le`: the height changes by at most `log 2` under `x ↦ 1 - x` (and
  not at all under `x ↦ 1 / x`, Mathlib's `Height.logHeight₁_inv`).
* `vojta_iff_unitInterval`: the proposition is equivalent to its restriction to `0 < x < 1`.
* `exists_rat_ne_zero_ne_one` and the values at `1/2` and `8/9`: the statement quantifies over a
  nonempty set and the definitions give the expected numbers.
-/

namespace IUT.ABCSpecialization

open Challenge

/-! ## Definitions -/

/-- The conductor of a rational number `x` relative to the divisor `{0, 1, ∞}` of `ℙ¹`: the
product of the primes `p` that divide the numerator of `x` (where `x` reduces to `0`), the
numerator of `x - 1` (where `x` reduces to `1`), or the denominator of `x` (where `x` reduces to
`∞`). Its logarithm is the log-conductor of the rational point `x` in the sense of [GenEll]
Definition 1.5 (iv) (page 8) for the model `ℙ¹_ℤ` with the sections `0`, `1`, `∞`; another model
changes it by a bounded function (module docstring). -/
def ratConductor (x : ℚ) : ℕ :=
  ∏ p ∈ x.num.natAbs.primeFactors ∪ (x - 1).num.natAbs.primeFactors ∪ x.den.primeFactors, p

/-- **A special case of the conclusion of IUT IV, Corollary 2.3, not the corollary itself.**
For every `ε > 0` there is a constant `C` such that every rational number `x ≠ 0, 1` satisfies
`ht(x) ≤ (1 + ε) * log (ratConductor x) + C`, where `ht` is Mathlib's logarithmic height on `ℚ`.

This is the inequality `ht_{ω_X(D)} ≲ (1 + ε)(log-diff_X + log-cond_D)` of Corollary 2.3
(page 54) specialized to one curve, `X = ℙ¹_ℚ` with `D = {0, 1, ∞}`, and to its rational points
(`d = 1`), where the log-different vanishes. It drops the points over number fields of degree
`d > 1`, the compactly bounded subsets of the proof, and all other hyperbolic curves over number
fields. It is an open statement: this file proves only that it is equivalent to the abc
conjecture (`vojta_iff_ABC`). -/
def VojtaLineMinusThreePointsRational : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℚ, x ≠ 0 → x ≠ 1 →
    Height.logHeight₁ x ≤ (1 + ε) * Real.log (ratConductor x) + C

/-- The same inequality with an arbitrary function `ht` on `ℚ` in place of the height. Used only
to show that changing the height by a bounded function does not change the statement. -/
def RationalPointBoundFor (ht : ℚ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℚ, x ≠ 0 → x ≠ 1 →
    ht x ≤ (1 + ε) * Real.log (ratConductor x) + C

/-! ## Independence of the height up to bounded functions -/

/-- If `ht` and `ht'` differ by at most `B` on `ℚ \ {0, 1}`, the two inequalities are
equivalent: the constant `C` absorbs `B`. -/
theorem rationalPointBoundFor_iff_of_bounded {ht ht' : ℚ → ℝ} (B : ℝ)
    (hB : ∀ x : ℚ, x ≠ 0 → x ≠ 1 → |ht x - ht' x| ≤ B) :
    RationalPointBoundFor ht ↔ RationalPointBoundFor ht' := by
  have key : ∀ {f g : ℚ → ℝ}, (∀ x : ℚ, x ≠ 0 → x ≠ 1 → |f x - g x| ≤ B) →
      RationalPointBoundFor f → RationalPointBoundFor g := by
    intro f g hfg hf ε hε
    obtain ⟨C, hC⟩ := hf ε hε
    refine ⟨C + B, fun x h0 h1 => ?_⟩
    have := hC x h0 h1
    have := neg_abs_le (f x - g x)
    have := hfg x h0 h1
    linarith
  exact ⟨key hB, key fun x h0 h1 => by rw [abs_sub_comm]; exact hB x h0 h1⟩

/-- The proposition of this file is the bound for Mathlib's height, and any height at bounded
distance from it on `ℚ \ {0, 1}` gives an equivalent statement. -/
theorem vojta_iff_rationalPointBoundFor {ht : ℚ → ℝ} (B : ℝ)
    (hB : ∀ x : ℚ, x ≠ 0 → x ≠ 1 → |ht x - Height.logHeight₁ x| ≤ B) :
    VojtaLineMinusThreePointsRational ↔ RationalPointBoundFor ht :=
  (rationalPointBoundFor_iff_of_bounded B hB).symm

/-! ## Numerators, denominators and radicals -/

/-- The numerator of `x - 1` is the numerator of `x` minus the denominator of `x`: the fraction
`(num x - den x) / den x` is already in lowest terms. -/
theorem num_sub_one_eq_num_sub_den (x : ℚ) : (x - 1).num = x.num - x.den := by
  have hd : (0 : ℤ) < x.den := by exact_mod_cast x.den_pos
  have hcop : (x.num - x.den).natAbs.Coprime (x.den : ℤ).natAbs := by
    rw [← Int.isCoprime_iff_nat_coprime]
    have h : IsCoprime x.num (x.den : ℤ) :=
      Int.isCoprime_iff_nat_coprime.mpr (by simpa using x.reduced)
    simpa using (IsCoprime.sub_mul_right_left_iff (z := 1)).mpr h
  have hx : x - 1 = ((x.num - x.den : ℤ) : ℚ) / ((x.den : ℤ) : ℚ) := by
    have hd' : ((x.den : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [Int.cast_sub, sub_div, div_self hd', Int.cast_natCast, Rat.num_div_den]
  rw [hx, Rat.num_div_eq_of_coprime hd hcop]

/-- The radical of a product of three nonzero numbers is the product over the union of their
sets of prime factors. -/
theorem rad_mul_mul_eq_prod_union {a b c : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    rad (a * b * c) = ∏ p ∈ a.primeFactors ∪ b.primeFactors ∪ c.primeFactors, p := by
  unfold rad
  rw [Nat.primeFactors_mul (Nat.mul_ne_zero ha hb) hc, Nat.primeFactors_mul ha hb]

/-! ## From a triple to a rational point -/

/-- For positive coprime `a`, `b` with `a + b = c`, the fraction `a / c` is in lowest terms:
its numerator is `a` and its denominator is `c`. -/
theorem num_den_of_triple {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : a + b = c) : ((a : ℚ) / c).num = a ∧ ((a : ℚ) / c).den = c := by
  have hac : a.Coprime c := by
    subst h; exact Nat.coprime_self_add_right.mpr hab
  have hc : (0 : ℤ) < c := by exact_mod_cast (show 0 < c by omega)
  have hcop : (a : ℤ).natAbs.Coprime (c : ℤ).natAbs := by simpa using hac
  have h1 := Rat.num_div_eq_of_coprime hc hcop
  have h2 := Rat.den_div_eq_of_coprime hc hcop
  push_cast at h1 h2
  exact ⟨h1, by exact_mod_cast h2⟩

/-- **Height of the point of a triple.** For positive coprime `a`, `b` with `a + b = c`, the
height of `a / c` is `log c`. -/
theorem logHeight₁_of_triple {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : a + b = c) : Height.logHeight₁ ((a : ℚ) / c) = Real.log c := by
  obtain ⟨hn, hd⟩ := num_den_of_triple ha hb hab h
  rw [Rat.logHeight₁_eq_log_max, hn, hd, Int.natAbs_natCast, max_eq_right (by omega)]

/-- **Conductor of the point of a triple.** For positive coprime `a`, `b` with `a + b = c`, the
conductor of `x = a / c` is `rad (a b c)`: the numerator of `x` is `a`, the numerator of
`x - 1 = -b / c` is `-b`, and the denominator of `x` is `c`. -/
theorem ratConductor_of_triple {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : a + b = c) : ratConductor ((a : ℚ) / c) = rad (a * b * c) := by
  obtain ⟨hn, hd⟩ := num_den_of_triple ha hb hab h
  have hm : (((a : ℚ) / c) - 1).num.natAbs = b := by
    rw [num_sub_one_eq_num_sub_den, hn, hd]; omega
  unfold ratConductor
  rw [hm, hn, hd, Int.natAbs_natCast, rad_mul_mul_eq_prod_union (by omega) (by omega) (by omega)]

/-! ## From a rational point to a triple -/

/-- **Every rational point of the line minus three points gives a triple.** Write `n`, `d` for
the numerator and denominator of `x ∉ {0, 1}`, so that `n - d` is the numerator of `x - 1`. The
three numbers `|n|`, `|n - d|`, `d` are positive, and one of them is the sum of the other two:
`|n| + d = |n - d|` if `x < 0`, `|n| + |n - d| = d` if `0 < x < 1`, and `|n - d| + d = |n|` if
`1 < x`. This gives positive coprime `a`, `b` with `a + b = c`, the height of `x` is at most
`log c` (with equality unless `x < 0`), and the conductor of `x` is `rad (a b c)`. -/
theorem exists_triple_of_ne (x : ℚ) (h0 : x ≠ 0) (h1 : x ≠ 1) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a.Coprime b ∧ a + b = c ∧
      Height.logHeight₁ x ≤ Real.log c ∧ ratConductor x = rad (a * b * c) := by
  have hred : x.num.natAbs.Coprime x.den := x.reduced
  have hd : 0 < x.den := x.den_pos
  have hn0 : x.num ≠ 0 := Rat.num_ne_zero.mpr h0
  have hnd : x.num ≠ x.den := by
    intro h; apply h1
    rw [← Rat.num_div_den x, h, Int.cast_natCast, div_self (by exact_mod_cast hd.ne')]
  have hH : Height.logHeight₁ x = Real.log (max x.num.natAbs x.den : ℕ) :=
    Rat.logHeight₁_eq_log_max x
  have hcond : ratConductor x = ∏ p ∈ x.num.natAbs.primeFactors ∪
      (x.num - x.den).natAbs.primeFactors ∪ x.den.primeFactors, p := by
    unfold ratConductor; rw [num_sub_one_eq_num_sub_den]
  set N := x.num.natAbs with hN
  set M := (x.num - x.den).natAbs with hM
  set D := x.den with hD
  have hlog : ∀ c : ℕ, max N D ≤ c → Height.logHeight₁ x ≤ Real.log c := fun c hc => by
    rw [hH]
    exact Real.log_le_log (by exact_mod_cast (show 0 < max N D by omega)) (by exact_mod_cast hc)
  rcases lt_or_gt_of_ne hn0 with hneg | hpos
  · -- `x < 0`: `N + D = M`
    have hs : N + D = M := by omega
    refine ⟨N, D, M, by omega, hd, by omega, hred, hs, hlog M (by omega), ?_⟩
    rw [hcond, rad_mul_mul_eq_prod_union (by omega) (by omega) (by omega)]
    congr 1; ext p; simp only [Finset.mem_union]; tauto
  rcases lt_or_gt_of_ne hnd with hlt | hgt
  · -- `0 < x < 1`: `N + M = D`
    have hs : N + M = D := by omega
    refine ⟨N, M, D, by omega, by omega, hd, ?_, hs, hlog D (by omega), ?_⟩
    · rw [← hs] at hred; exact Nat.coprime_self_add_right.mp hred
    · rw [hcond, rad_mul_mul_eq_prod_union (by omega) (by omega) (by omega)]
  · -- `1 < x`: `M + D = N`
    have hs : M + D = N := by omega
    refine ⟨M, D, N, by omega, hd, by omega, ?_, hs, hlog N (by omega), ?_⟩
    · rw [← hs] at hred; exact Nat.coprime_add_self_left.mp hred
    · rw [hcond, rad_mul_mul_eq_prod_union (by omega) (by omega) (by omega)]
      congr 1; ext p; simp only [Finset.mem_union]; tauto

/-! ## Equivalence with the abc conjecture -/

/-- The bound on rational points implies the logarithmic form of abc, applied to `x = a / c`. -/
theorem abcLog_of_vojta (h : VojtaLineMinusThreePointsRational) : ABCLog := by
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨C, fun a b c ha hb hc hab habc => ?_⟩
  have hx0 : (a : ℚ) / c ≠ 0 :=
    div_ne_zero (by exact_mod_cast ha.ne') (by exact_mod_cast hc.ne')
  have hx1 : (a : ℚ) / c ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq (by exact_mod_cast hc.ne')]
    exact_mod_cast (show a ≠ c by omega)
  have := hC _ hx0 hx1
  rwa [logHeight₁_of_triple ha hb hab habc, ratConductor_of_triple ha hb hab habc] at this

/-- The logarithmic form of abc implies the bound on rational points, through
`exists_triple_of_ne`, with the same constant. -/
theorem vojta_of_abcLog (h : ABCLog) : VojtaLineMinusThreePointsRational := by
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨C, fun x hx0 hx1 => ?_⟩
  obtain ⟨a, b, c, ha, hb, hc, hab, habc, hle, hcond⟩ := exists_triple_of_ne x hx0 hx1
  rw [hcond]
  exact hle.trans (hC a b c ha hb hc hab habc)

/-- **The bound on rational points of `ℙ¹ \ {0, 1, ∞}` is equivalent to the abc conjecture.**
Neither side is proved here. -/
theorem vojta_iff_ABC : VojtaLineMinusThreePointsRational ↔ ABC :=
  ⟨fun h => IUT.ABC.abc_of_abcLog (abcLog_of_vojta h),
    fun h => vojta_of_abcLog (IUT.ABC.abcLog_of_abc h)⟩

/-! ## Symmetries of `{0, 1, ∞}` and the points of `(0, 1)` -/

/-- The numerator of `1 - x` is the denominator of `x` minus the numerator of `x`. -/
theorem num_one_sub_eq_den_sub_num (x : ℚ) : (1 - x).num = x.den - x.num := by
  rw [show (1 : ℚ) - x = -(x - 1) by ring, Rat.num_neg_eq_neg_num, num_sub_one_eq_num_sub_den]
  ring

/-- The denominator of `1 - x` is the denominator of `x`. -/
theorem den_one_sub_eq_den (x : ℚ) : (1 - x).den = x.den := by
  simp

/-- **The conductor is invariant under `x ↦ 1 - x`**, which exchanges `0` and `1` and fixes `∞`:
the numerators of `1 - x` and `(1 - x) - 1 = -x` are, up to sign, those of `x - 1` and `x`, and
the denominator is unchanged. -/
theorem ratConductor_one_sub (x : ℚ) : ratConductor (1 - x) = ratConductor x := by
  have h1 : (1 - x - 1).num.natAbs = x.num.natAbs := by
    rw [show (1 : ℚ) - x - 1 = -x by ring, Rat.num_neg_eq_neg_num, Int.natAbs_neg]
  have h2 : (1 - x).num.natAbs = (x - 1).num.natAbs := by
    rw [num_one_sub_eq_den_sub_num, num_sub_one_eq_num_sub_den]; omega
  unfold ratConductor
  rw [h1, h2, den_one_sub_eq_den]
  congr 1; ext p; simp only [Finset.mem_union]; tauto

/-- **The conductor is invariant under `x ↦ 1 / x`**, which exchanges `0` and `∞` and fixes `1`:
for `x ≠ 0` the numerator and denominator of `1 / x` are, up to sign, the denominator and
numerator of `x`, and the numerator of `1 / x - 1` is, up to sign, that of `x - 1`. At `x = 0`
both sides are the conductor of `0`, since `0⁻¹ = 0` in `ℚ`. -/
theorem ratConductor_inv (x : ℚ) : ratConductor x⁻¹ = ratConductor x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hn : x.num ≠ 0 := Rat.num_ne_zero.mpr hx
  have hnum : x⁻¹.num.natAbs = x.den := by
    rw [Rat.num_inv]; rcases lt_or_gt_of_ne hn with h | h
    · rw [Int.sign_eq_neg_one_of_neg h]; omega
    · rw [Int.sign_eq_one_of_pos h]; omega
  have hden : x⁻¹.den = x.num.natAbs := Rat.den_inv_of_ne_zero hx
  have hsub : (x⁻¹ - 1).num.natAbs = (x - 1).num.natAbs := by
    rw [num_sub_one_eq_num_sub_den, num_sub_one_eq_num_sub_den, Rat.num_inv, hden]
    rcases lt_or_gt_of_ne hn with h | h
    · rw [Int.sign_eq_neg_one_of_neg h]; omega
    · rw [Int.sign_eq_one_of_pos h]; omega
  unfold ratConductor
  rw [hnum, hden, hsub]
  congr 1; ext p; simp only [Finset.mem_union]; tauto

/-- **The height changes by at most `log 2` under `x ↦ 1 - x`.** With `x = n / d` in lowest
terms, `1 - x = (d - n) / d` in lowest terms, and each of `max(|d - n|, d)` and `max(|n|, d)` is
at most twice the other. (Under `x ↦ 1 / x` the height is unchanged: Mathlib's
`Height.logHeight₁_inv`.) -/
theorem abs_logHeight₁_one_sub_sub_le (x : ℚ) :
    |Height.logHeight₁ (1 - x) - Height.logHeight₁ x| ≤ Real.log 2 := by
  rw [Rat.logHeight₁_eq_log_max, Rat.logHeight₁_eq_log_max, num_one_sub_eq_den_sub_num,
    den_one_sub_eq_den]
  have hd := x.den_pos
  have key : ∀ a b : ℕ, 0 < a → a ≤ 2 * b → Real.log a ≤ Real.log 2 + Real.log b := by
    intro a b ha hab
    have hb : 0 < b := by omega
    rw [← Real.log_mul (by norm_num) (by exact_mod_cast hb.ne')]
    exact Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast hab)
  rw [abs_sub_le_iff]
  constructor
  · have := key (max ((x.den : ℤ) - x.num).natAbs x.den) (max x.num.natAbs x.den)
      (by omega) (by omega)
    linarith
  · have := key (max x.num.natAbs x.den) (max ((x.den : ℤ) - x.num).natAbs x.den)
      (by omega) (by omega)
    linarith

/-- The inequality of `VojtaLineMinusThreePointsRational` asked only for rational `x` with
`0 < x < 1`. -/
def VojtaLineMinusThreePointsUnitInterval : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℚ, 0 < x → x < 1 →
    Height.logHeight₁ x ≤ (1 + ε) * Real.log (ratConductor x) + C

/-- **It suffices to bound the points of `(0, 1)`, with the same constant.** One direction is a
restriction. For the other, `exists_triple_of_ne` sends `x ∉ {0, 1}` to a triple `a + b = c`;
the point `y = a / c` lies in `(0, 1)`, has height `log c ≥ ht(x)` and the same conductor
`rad (a b c)` as `x`. (The point `y` is the image of `x` under one of the six maps generated by
`x ↦ 1 - x` and `x ↦ 1 / x`, compare `ratConductor_one_sub`, `ratConductor_inv` and
`abs_logHeight₁_one_sub_sub_le`, but the proof does not use those lemmas.) -/
theorem vojta_iff_unitInterval :
    VojtaLineMinusThreePointsRational ↔ VojtaLineMinusThreePointsUnitInterval := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC⟩ := h ε hε
    exact ⟨C, fun x h0 h1 => hC x h0.ne' h1.ne⟩
  · intro h ε hε
    obtain ⟨C, hC⟩ := h ε hε
    refine ⟨C, fun x hx0 hx1 => ?_⟩
    obtain ⟨a, b, c, ha, hb, hc, hab, habc, hle, hcond⟩ := exists_triple_of_ne x hx0 hx1
    have hc' : (0 : ℚ) < c := by exact_mod_cast hc
    have hy0 : (0 : ℚ) < a / c := div_pos (by exact_mod_cast ha) hc'
    have hy1 : (a : ℚ) / c < 1 := by
      rw [div_lt_one hc']; exact_mod_cast (show a < c by omega)
    have := hC _ hy0 hy1
    rw [logHeight₁_of_triple ha hb hab habc, ratConductor_of_triple ha hb hab habc] at this
    rw [hcond]
    exact hle.trans this

/-! ## Nonvacuity and examples -/

/-- The set of rational points quantified over is not empty. -/
theorem exists_rat_ne_zero_ne_one : ∃ x : ℚ, x ≠ 0 ∧ x ≠ 1 :=
  ⟨1 / 2, by norm_num, by norm_num⟩

/-- The height of `1/2` is `log 2` (triple `1 + 1 = 2`). -/
theorem logHeight₁_one_half : Height.logHeight₁ (1 / 2 : ℚ) = Real.log 2 := by
  have := logHeight₁_of_triple (a := 1) (b := 1) (c := 2) (by decide) (by decide) (by decide) rfl
  simpa using this

/-- The conductor of `1/2` is `2`: the numerator of `1/2` is `1`, the numerator of `-1/2` is
`-1`, and the denominator is `2`. -/
theorem ratConductor_one_half : ratConductor (1 / 2 : ℚ) = 2 := by
  have := ratConductor_of_triple (a := 1) (b := 1) (c := 2) (by decide) (by decide) (by decide)
    rfl
  simp only [Nat.cast_one, Nat.cast_ofNat, mul_one, one_mul] at this
  rw [this]
  simpa using IUT.ABC.rad_prime_pow (k := 1) Nat.prime_two one_ne_zero

/-- The height of `8/9` is `log 9` (triple `8 + 1 = 9`). -/
theorem logHeight₁_eight_ninths : Height.logHeight₁ (8 / 9 : ℚ) = Real.log 9 := by
  have := logHeight₁_of_triple (a := 8) (b := 1) (c := 9) (by decide) (by decide) (by decide) rfl
  simpa using this

/-- The conductor of `8/9` is `6 = rad (8 * 1 * 9)`: the primes are `2` (numerator `8`) and `3`
(denominator `9`); the numerator of `8/9 - 1 = -1/9` contributes none. -/
theorem ratConductor_eight_ninths : ratConductor (8 / 9 : ℚ) = 6 := by
  have := ratConductor_of_triple (a := 8) (b := 1) (c := 9) (by decide) (by decide) (by decide)
    rfl
  simp only [Nat.cast_ofNat] at this
  rw [this, show (8 * 1 * 9 : ℕ) = 2 ^ 3 * 3 ^ 2 by norm_num,
    IUT.ABC.rad_mul_of_coprime (by decide), IUT.ABC.rad_prime_pow Nat.prime_two (by decide),
    IUT.ABC.rad_prime_pow Nat.prime_three (by decide)]

end IUT.ABCSpecialization
