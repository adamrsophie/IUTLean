import Mathlib

/-!
# The classical theta series on a Tate curve and its values at the points `±√−1 · q_X^{j/2}`

Sources. Pages read for this file; every formula used was checked against a rendered image:

* Mochizuki, *The Étale Theta Function and its Frobenioid-theoretic Manifestations*, Section 1,
  pages 18 to 21: the coordinates `U` and `Ü` (pages 19 and 20), Proposition 1.4 with its proof
  (pages 20 and 21).
* Mochizuki, *Comments on "The Étale Theta Function and its Frobenioid-theoretic
  Manifestations"* (March 2022): all items read; pages 3, 4 and 6, which hold the items on
  Section 1, checked against rendered images. None corrects the series or the functional
  equations of Proposition 1.4. Item (xvii) replaces "∈" by "⊆" for the sets of classes in
  Proposition 1.4 (iii), and item (xxx) adds references for the classical theory of theta
  functions on Tate curves; neither concerns a statement formalized here.
* *Inter-universal Teichmüller Theory II*, Remark 2.5.1, pages 72 and 73, and page 24 (part
  (iv) of Remark 1.1.1, which runs over pages 21 to 25; only page 24 was read), all rendered.

## The series

Proposition 1.4 (page 20) defines
`Θ̈(Ü) = q_X^{−1/8} · ∑_{n ∈ ℤ} (−1)^n · q_X^{(1/2)(n + 1/2)²} · Ü^{2n+1}`.
Since `(1/2)(n + 1/2)² − 1/8 = n(n + 1)/2` is an integer, no fractional power of `q_X` occurs:
`Θ̈(Ü) = ∑_{n ∈ ℤ} (−1)^n · q_X^{n(n+1)/2} · Ü^{2n+1}`. The file fixes an element `r` with
`r² = q_X` (the `q_X^{1/2}` of the quasi-periodicity) and defines
`thetaSeries r u = ∑_{n ∈ ℤ} (−1)^n · r^{n(n+1)} · u^{2n+1}`; `zpow_mul_succ_eq_sq_zpow` records
`r^{n(n+1)} = (r²)^{n(n+1)/2}`, so `thetaSeries r u` is exactly `Θ̈(u)` for `q_X = r²`, evaluated
at a point `u` of the field `K` rather than regarded as a function on the formal scheme.

Setting: `K` a complete normed field and `0 < ‖r‖ < 1`. Summability (`summable_thetaTerm`, for
every `u ≠ 0`) uses the ratio test and does not need the ultrametric inequality; only the
nonvanishing of `Θ(√−1)` uses `IsUltrametricDist K`. The functional equations are identities of
`tsum` that hold for all arguments; they carry content where the series converges.

## What is proved

1. Proposition 1.4 (ii): `Θ(u) = −Θ(u⁻¹)` (`thetaSeries_inv`), `Θ(−u) = −Θ(u)`
   (`thetaSeries_neg`), and `Θ(r^a u) = (−1)^a · r^{−a²} · u^{−2a} · Θ(u)` for `a ∈ ℤ`, `u ≠ 0`
   (`thetaSeries_zpow_mul`), i.e. `Θ̈(q_X^{a/2} Ü) = (−1)^a q_X^{−a²/2} Ü^{−2a} Θ̈(Ü)`.
2. The zeros `Θ(±1) = 0` (stated in the proof, page 20) in every characteristic, and hence
   `Θ(±r^a) = 0` for all `a ∈ ℤ` (`thetaSeries_zpow`). That these are all the zeros, that they
   are simple, and the divisor of poles (Proposition 1.4 (i)) are not formalized.
3. The values used in IUT II, Remark 2.5.1 (ii), page 73: at `c` with `c² = −1`,
   `Θ(r^j · c) = r^{−j²} · Θ(c)` (`thetaSeries_zpow_mul_of_sq_eq_neg_one`), i.e.
   `Θ̈(±√−1 · q_X^{j/2}) = q_X^{−j²/2} · Θ̈(±√−1)`; the sign `(−1)^j` cancels against
   `c^{−2j} = (−1)^j`. In a complete ultrametric field, `Θ(c) = 2c · ∑_{n ≥ 0} r^{n(n+1)}` and
   `‖Θ(c)‖ = ‖2‖`, so `Θ(c) ≠ 0` when `2 ≠ 0` in `K`, and the ratio `Θ(r^j c)/Θ(c)` equals
   `r^{−j²}` (`thetaSeries_div_of_sq_eq_neg_one`). Normalizing by `Θ(c)` is a choice of this
   file: the pages read state no normalization of `Θ̈` at `√−1`.
4. Relation to `IUT.PaperII.Labels`. That module attaches to `j ∈ {0, 1, …, l^⋇}` the exponent
   `j²` of `qq_v`, a chosen `2l`-th root of the Tate parameter (as recorded in that module, from
IUT I, Example 3.2 (iv); that page was not read for this file). With
   `qq` an element such that `qq^l = r` (so `qq^{2l} = q_X`), `(qq^{j²})^l · Θ(r^j c) = Θ(c)`
   (`pow_mul_thetaSeries_zpow_mul`): the theta value at `±√−1 · q_X^{j/2}`, relative to `Θ(c)`, is
   the reciprocal of the `l`-th power of `qq^{j²}`, as Remark 2.5.1 (ii) says. Moreover, for `x`
   in `K`, `x^{2l} · R_j² = 1` with `R_j = Θ(r^j c)/Θ(c)` if and only if `x` lies in the
   `μ_{2l}(K)`-orbit of `qq^{j²}` (`pow_mul_thetaRatio_sq_eq_one_iff`). Interpretation: the
   identification of `q_X` with the Tate parameter `q_v` is read off from Remark 2.5.1 (ii) and is
   not proved. On page 24 of IUT II (Remark 1.1.1 (iv)), the running text speaks of a Kummer
   class of a product of integral powers of `(Ü)²` and `q_X^{l/2}` (exponent `l/2` as printed,
   rendered at 300 dpi), citing Proposition 1.4 (ii); that passage plays no role here.

## What is not formalized

The étale theta function itself (the Kummer classes of Propositions 1.3 and 1.4 (iii)), the
tempered coverings `Ÿ` and their cusps, the evaluation points on the tempered covering, the
group-theoretic evaluation of IUT II, Corollary 2.5, the cyclotomic rigidity and Kummer map of
Remark 2.5.1 (i), and hence the statement that `θ^j(Π_v)` is the `μ_{2l}`-orbit of `qq_v^{j²}`:
only the classical identity behind it is proved. The property in Remark 2.5.1 (ii) that
`Θ̈(c)/Θ̈(c′)` is a root of unity when `c′` arises from `c` by an automorphism of `Π_v` with
`c′/c` a unit, and Remark 2.5.1 (iii), are not treated. The orbit criterion of item 4 is a
reformulation made in this file, not a statement of the paper.

## Instance

Over `ℚ_[p]` with `r = p` (`p` is not a square in `ℚ_[p]`, so `q_X = p²`): summability, the
zeros `Θ(±p^a) = 0`, and `‖Θ(p^j c)/Θ(c)‖ = p^{j²}` for `p` odd and `c² = −1`; such a `c` exists
in `ℚ_[5]` (Hensel's lemma, `exists_sq_eq_neg_one_padic_five`).
-/

namespace IUT.Prerequisites.ThetaFunction

open Filter Topology

section Series

variable {K : Type*} [NormedField K]

/-- The `n`-th term `(−1)^n · r^{n(n+1)} · u^{2n+1}` of the theta series, with `r` in the role
of `q_X^{1/2}`. -/
def thetaTerm (r u : K) (n : ℤ) : K := (-1) ^ n * r ^ (n * (n + 1)) * u ^ (2 * n + 1)

/-- The theta series `Θ(u) = ∑_{n ∈ ℤ} (−1)^n · r^{n(n+1)} · u^{2n+1}`. With `r² = q_X` and
`u = Ü` this is the series `Θ̈(Ü)` of Proposition 1.4 of the paper on the étale theta function
(see the module docstring for the computation of the exponents). -/
noncomputable def thetaSeries (r u : K) : K := ∑' n : ℤ, thetaTerm r u n

/-- The exponent of `r` is even, so each term depends on `r` only through `q_X = r²`:
`r^{n(n+1)} = (r²)^{n(n+1)/2}`. -/
theorem zpow_mul_succ_eq_sq_zpow (r : K) (n : ℤ) :
    r ^ (n * (n + 1)) = (r ^ 2) ^ (n * (n + 1) / 2) := by
  have h2 : (2 : ℤ) ∣ n * (n + 1) := (Int.even_mul_succ_self n).two_dvd
  rw [← zpow_natCast, ← zpow_mul, Nat.cast_ofNat, Int.mul_ediv_cancel' h2]

/-- `(−1)^{−(n+1)} = −(−1)^n`. -/
private lemma neg_one_zpow_neg_succ (n : ℤ) : (-1 : K) ^ (-(n + 1)) = -(-1) ^ n := by
  rw [zpow_neg, zpow_add_one₀ (by norm_num), mul_neg_one, inv_neg, ← inv_zpow, inv_neg, inv_one]

/-- Reflection of the index `n ↦ −(n + 1)` relates the terms at `u` and at `u⁻¹`. -/
theorem thetaTerm_neg_succ (r u : K) (n : ℤ) :
    thetaTerm r u (-(n + 1)) = -thetaTerm r u⁻¹ n := by
  unfold thetaTerm
  rw [neg_one_zpow_neg_succ, show -(n + 1) * (-(n + 1) + 1) = n * (n + 1) by ring,
    show 2 * -(n + 1) + 1 = -(2 * n + 1) by ring, zpow_neg (u), inv_zpow]
  ring

/-- The involution `n ↦ −(n + 1)` of `ℤ`. -/
def negSuccEquiv : ℤ ≃ ℤ where
  toFun n := -(n + 1)
  invFun n := -(n + 1)
  left_inv n := by simp only; omega
  right_inv n := by simp only; omega

/-- Proposition 1.4 (ii), first formula: `Θ(u) = −Θ(u⁻¹)`. -/
theorem thetaSeries_inv (r u : K) : thetaSeries r u = -thetaSeries r u⁻¹ := by
  unfold thetaSeries
  rw [← negSuccEquiv.tsum_eq, ← tsum_neg]
  exact tsum_congr fun n => thetaTerm_neg_succ r u n

/-- Proposition 1.4 (ii), second formula: `Θ(−u) = −Θ(u)`. -/
theorem thetaSeries_neg (r u : K) : thetaSeries r (-u) = -thetaSeries r u := by
  unfold thetaSeries
  rw [← tsum_neg]
  refine tsum_congr fun n => ?_
  unfold thetaTerm
  rw [Odd.neg_zpow (n := 2 * n + 1) ⟨n, by ring⟩ u]
  ring

/-- The term identity behind the quasi-periodicity:
`term(r^a u, n) = (−1)^a · r^{−a²} · u^{−2a} · term(u, n + a)`. -/
theorem thetaTerm_zpow_mul {r u : K} (hr : r ≠ 0) (hu : u ≠ 0) (a n : ℤ) :
    thetaTerm r (r ^ a * u) n =
      (-1) ^ a * r ^ (-a ^ 2) * u ^ (-2 * a) * thetaTerm r u (n + a) := by
  unfold thetaTerm
  have h1 : ((-1 : K) ^ a * (-1) ^ (n + a)) = (-1) ^ n := by
    rw [← zpow_add₀ (by norm_num), show a + (n + a) = n + 2 * a by ring,
      zpow_add₀ (by norm_num), zpow_mul, show ((-1 : K) ^ (2 : ℤ)) = 1 by norm_num, one_zpow,
      mul_one]
  have h2 : r ^ (-a ^ 2) * r ^ ((n + a) * (n + a + 1)) = r ^ (n * (n + 1)) * r ^ (a * (2 * n + 1)) := by
    rw [← zpow_add₀ hr, ← zpow_add₀ hr]
    congr 1
    ring
  have h3 : u ^ (-2 * a) * u ^ (2 * (n + a) + 1) = u ^ (2 * n + 1) := by
    rw [← zpow_add₀ hu]
    congr 1
    ring
  rw [mul_zpow, ← zpow_mul]
  calc (-1) ^ n * r ^ (n * (n + 1)) * (r ^ (a * (2 * n + 1)) * u ^ (2 * n + 1))
      = ((-1) ^ a * (-1) ^ (n + a)) * (r ^ (-a ^ 2) * r ^ ((n + a) * (n + a + 1))) *
          (u ^ (-2 * a) * u ^ (2 * (n + a) + 1)) := by rw [h1, h2, h3]; ring
    _ = _ := by ring

/-- Proposition 1.4 (ii), third formula: for `a ∈ ℤ`,
`Θ(r^a · u) = (−1)^a · r^{−a²} · u^{−2a} · Θ(u)`, i.e.
`Θ̈(q_X^{a/2} Ü) = (−1)^a · q_X^{−a²/2} · Ü^{−2a} · Θ̈(Ü)` with `r = q_X^{1/2}`. -/
theorem thetaSeries_zpow_mul {r u : K} (hr : r ≠ 0) (hu : u ≠ 0) (a : ℤ) :
    thetaSeries r (r ^ a * u) = (-1) ^ a * r ^ (-a ^ 2) * u ^ (-2 * a) * thetaSeries r u := by
  unfold thetaSeries
  simp_rw [thetaTerm_zpow_mul hr hu a]
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.addRight a).tsum_eq (thetaTerm r u)

end Series

section Summability

variable {K : Type*} [NormedField K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- `‖term(n)‖ = ‖r‖^{n(n+1)} · ‖u‖^{2n+1}`. -/
theorem norm_thetaTerm (r u : K) (n : ℤ) :
    ‖thetaTerm r u n‖ = ‖r‖ ^ (n * (n + 1)) * ‖u‖ ^ (2 * n + 1) := by
  simp [thetaTerm, norm_zpow]

/-- The terms with index `n ≥ 0` are summable when `0 < ‖r‖ < 1` and `u ≠ 0` (ratio test). -/
theorem summable_thetaTerm_nat {r u : K} (hr0 : r ≠ 0) (hr : ‖r‖ < 1) (hu : u ≠ 0) :
    Summable fun n : ℕ => thetaTerm r u n := by
  have hrn : 0 < ‖r‖ := norm_pos_iff.mpr hr0
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu
  refine summable_of_ratio_test_tendsto_lt_one zero_lt_one
    (Eventually.of_forall fun n => ?_) ?_
  · rw [← norm_ne_zero_iff, norm_thetaTerm]; positivity
  · have key : ∀ n : ℕ, ‖thetaTerm r u ((n + 1 : ℕ) : ℤ)‖ / ‖thetaTerm r u (n : ℤ)‖ =
        (‖r‖ ^ 2) ^ (n + 1) * ‖u‖ ^ 2 := by
      intro n
      rw [norm_thetaTerm, norm_thetaTerm, div_eq_iff (by positivity)]
      have e1 : (‖r‖ ^ 2) ^ (n + 1) = ‖r‖ ^ ((2 * (n + 1) : ℕ) : ℤ) := by rw [zpow_natCast, pow_mul]
      have e2 : ‖u‖ ^ 2 = ‖u‖ ^ ((2 : ℕ) : ℤ) := by rw [zpow_natCast]
      rw [e1, e2, show ∀ a b c d : ℝ, a * b * (c * d) = (a * c) * (b * d) from
        fun _ _ _ _ => by ring, ← zpow_add₀ hrn.ne', ← zpow_add₀ hun.ne']
      congr 2 <;> push_cast <;> ring
    simp_rw [key]
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : (0 : ℝ) ≤ ‖r‖ ^ 2)
      (by nlinarith)).comp (tendsto_add_atTop_nat 1)).mul_const (‖u‖ ^ 2)
    simpa using h

/-- Summability of the theta series on `ℤ` for every `u ≠ 0` when `0 < ‖r‖ < 1`. -/
theorem summable_thetaTerm {r u : K} (hr0 : r ≠ 0) (hr : ‖r‖ < 1) (hu : u ≠ 0) :
    Summable (thetaTerm r u) := by
  refine Summable.of_nat_of_neg_add_one (summable_thetaTerm_nat hr0 hr hu) ?_
  simp_rw [thetaTerm_neg_succ]
  exact (summable_thetaTerm_nat hr0 hr (inv_ne_zero hu)).neg

/-- `Θ(1) = 0` (stated in the proof of Proposition 1.4), in every characteristic: the terms of
index `n` and `−(n + 1)` cancel. -/
theorem thetaSeries_one {r : K} (hr0 : r ≠ 0) (hr : ‖r‖ < 1) : thetaSeries r 1 = 0 := by
  have h1 := summable_thetaTerm_nat hr0 hr one_ne_zero
  have h2 : Summable fun n : ℕ => thetaTerm r 1 (-(n + 1)) := by
    simp_rw [thetaTerm_neg_succ, inv_one]; exact h1.neg
  unfold thetaSeries
  rw [tsum_of_nat_of_neg_add_one h1 h2]
  simp_rw [thetaTerm_neg_succ, inv_one, tsum_neg, add_neg_cancel]

/-- `Θ(−1) = 0`. -/
theorem thetaSeries_neg_one {r : K} (hr0 : r ≠ 0) (hr : ‖r‖ < 1) : thetaSeries r (-1) = 0 := by
  rw [thetaSeries_neg, thetaSeries_one hr0 hr, neg_zero]

/-- The zeros `Θ(±r^a) = 0`, `a ∈ ℤ`, i.e. `Θ̈(±q_X^{a/2}) = 0`: obtained from `Θ(±1) = 0` and
the quasi-periodicity. -/
theorem thetaSeries_zpow {r : K} (hr0 : r ≠ 0) (hr : ‖r‖ < 1) (a : ℤ) :
    thetaSeries r (r ^ a) = 0 ∧ thetaSeries r (-r ^ a) = 0 := by
  have h : thetaSeries r (r ^ a) = 0 := by
    have := thetaSeries_zpow_mul hr0 one_ne_zero a
    rw [mul_one] at this
    rw [this, thetaSeries_one hr0 hr, mul_zero]
  exact ⟨h, by rw [thetaSeries_neg, h, neg_zero]⟩

end Summability

section Values

variable {K : Type*} [NormedField K]

/-- At a point `c` with `c² = −1` the signs cancel: `term(c, n) = c · r^{n(n+1)}`. -/
theorem thetaTerm_of_sq_eq_neg_one {r c : K} (hc : c ^ 2 = -1) (n : ℤ) :
    thetaTerm r c n = c * r ^ (n * (n + 1)) := by
  have hc0 : c ≠ 0 := by rintro rfl; norm_num at hc
  unfold thetaTerm
  rw [zpow_add_one₀ hc0, zpow_mul c 2 n, show c ^ (2 : ℤ) = -1 by rw [zpow_two, ← pow_two, hc]]
  have h1 : ((-1 : K) ^ n) * (-1) ^ n = 1 := by
    rw [← mul_zpow, show (-1 : K) * -1 = 1 by norm_num, one_zpow]
  linear_combination (c * r ^ (n * (n + 1))) * h1

/-- The theta values at the points `r^j · c`, `c² = −1`, separated by periods from `c`:
`Θ(r^j · c) = r^{−j²} · Θ(c)`, i.e. `Θ̈(±√−1 · q_X^{j/2}) = q_X^{−j²/2} · Θ̈(±√−1)`. The sign
`(−1)^j` and the factor `c^{−2j} = (−1)^j` of the quasi-periodicity cancel. -/
theorem thetaSeries_zpow_mul_of_sq_eq_neg_one {r c : K} (hr : r ≠ 0) (hc : c ^ 2 = -1)
    (j : ℤ) : thetaSeries r (r ^ j * c) = r ^ (-j ^ 2) * thetaSeries r c := by
  have hc0 : c ≠ 0 := by rintro rfl; norm_num at hc
  rw [thetaSeries_zpow_mul hr hc0 j]
  have h : (-1 : K) ^ j * c ^ (-2 * j) = 1 := by
    rw [show (-2 : ℤ) * j = 2 * (-j) by ring, zpow_mul c 2 (-j),
      show c ^ (2 : ℤ) = -1 by rw [zpow_two, ← pow_two, hc], ← zpow_add₀ (by norm_num),
      add_neg_cancel, zpow_zero]
  linear_combination (r ^ (-j ^ 2) * thetaSeries r c) * h

/-- The same identity in terms of a chosen `l`-th root `qq` of `r`, so that `qq^{2l} = r² = q_X`
(the root written as `q` with a double underline in IUT): `(qq^{j²})^l · Θ(r^j · c) = Θ(c)`. That
is, `Θ(r^j · c)` is `Θ(c)` times the reciprocal of the `l`-th power of `qq^{j²}`. -/
theorem pow_mul_thetaSeries_zpow_mul {r c qq : K} (hr : r ≠ 0) (hc : c ^ 2 = -1) {l : ℕ}
    (hqq : qq ^ l = r) (j : ℤ) :
    (qq ^ (j ^ 2)) ^ l * thetaSeries r (r ^ j * c) = thetaSeries r c := by
  rw [thetaSeries_zpow_mul_of_sq_eq_neg_one hr hc j, ← mul_assoc, ← zpow_natCast, ← zpow_mul,
    mul_comm (j ^ 2), zpow_mul, zpow_natCast, hqq, ← zpow_add₀ hr, add_neg_cancel, zpow_zero,
    one_mul]

end Values

section Ultrametric

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- At `c` with `c² = −1`, pairing the indices `n` and `−(n + 1)`:
`Θ(c) = 2c · ∑_{n ≥ 0} r^{n(n+1)}`. -/
theorem thetaSeries_of_sq_eq_neg_one {r c : K} (hr0 : r ≠ 0) (hr : ‖r‖ < 1) (hc : c ^ 2 = -1) :
    thetaSeries r c = 2 * c * ∑' n : ℕ, r ^ (n * (n + 1)) := by
  have hc0 : c ≠ 0 := by rintro rfl; norm_num at hc
  have h1 := summable_thetaTerm_nat hr0 hr hc0
  have e1 : ∀ n : ℕ, thetaTerm r c n = c * r ^ (n * (n + 1)) := by
    intro n
    rw [thetaTerm_of_sq_eq_neg_one hc, show ((n : ℤ) * (n + 1)) = ((n * (n + 1) : ℕ) : ℤ) by
      push_cast; ring, zpow_natCast]
  have e2 : ∀ n : ℕ, thetaTerm r c (-(n + 1)) = c * r ^ (n * (n + 1)) := by
    intro n
    rw [thetaTerm_of_sq_eq_neg_one hc, show (-((n : ℤ) + 1) * (-(n + 1) + 1)) =
      ((n * (n + 1) : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have h2 : Summable fun n : ℕ => thetaTerm r c (-(n + 1)) := by
    simp_rw [e2]; simp_rw [e1] at h1; exact h1
  unfold thetaSeries
  rw [tsum_of_nat_of_neg_add_one h1 h2]
  simp_rw [e1, e2, tsum_mul_left]
  ring

/-- `‖Θ(c)‖ = ‖2‖` for `c² = −1`, in a complete ultrametric field with `0 < ‖r‖ < 1`. -/
theorem norm_thetaSeries_of_sq_eq_neg_one {r c : K} (hr0 : r ≠ 0) (hr : ‖r‖ < 1)
    (hc : c ^ 2 = -1) : ‖thetaSeries r c‖ = ‖(2 : K)‖ := by
  have hc0 : c ≠ 0 := by rintro rfl; norm_num at hc
  have hcn : ‖c‖ = 1 := by
    have h : ‖c‖ ^ 2 = 1 := by rw [← norm_pow, hc, norm_neg, norm_one]
    nlinarith [norm_nonneg c, sq_nonneg (‖c‖ - 1)]
  have hs : Summable fun n : ℕ => r ^ (n * (n + 1)) := by
    have h1 := (summable_thetaTerm_nat hr0 hr hc0).mul_left c⁻¹
    refine h1.congr fun n => ?_
    rw [thetaTerm_of_sq_eq_neg_one hc, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul,
      show ((n : ℤ) * (n + 1)) = ((n * (n + 1) : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have htail : ‖∑' n : ℕ, r ^ ((n + 1) * (n + 1 + 1))‖ ≤ ‖r‖ ^ 2 :=
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun n => by
      rw [norm_pow]
      exact pow_le_pow_of_le_one (norm_nonneg r) hr.le (by nlinarith)
  have hT : ‖∑' n : ℕ, r ^ (n * (n + 1))‖ = 1 := by
    rw [hs.tsum_eq_zero_add, zero_mul, pow_zero,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, norm_one]
    · exact max_eq_left (htail.trans (by nlinarith [norm_nonneg r]))
    · rw [norm_one]; exact (htail.trans_lt (by nlinarith [norm_nonneg r])).ne'
  rw [thetaSeries_of_sq_eq_neg_one hr0 hr hc, norm_mul, norm_mul, hcn, hT, mul_one, mul_one]

/-- `Θ(c) ≠ 0` for `c² = −1` when moreover `2 ≠ 0` in `K`. -/
theorem thetaSeries_ne_zero_of_sq_eq_neg_one {r c : K} (hr0 : r ≠ 0) (hr : ‖r‖ < 1)
    (hc : c ^ 2 = -1) (h2 : (2 : K) ≠ 0) : thetaSeries r c ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_thetaSeries_of_sq_eq_neg_one hr0 hr hc]
  exact norm_ne_zero_iff.mpr h2

/-- The ratio form: `Θ(r^j · c)/Θ(c) = r^{−j²}`, with the denominator nonzero. -/
theorem thetaSeries_div_of_sq_eq_neg_one {r c : K} (hr0 : r ≠ 0) (hr : ‖r‖ < 1)
    (hc : c ^ 2 = -1) (h2 : (2 : K) ≠ 0) (j : ℤ) :
    thetaSeries r (r ^ j * c) / thetaSeries r c = r ^ (-j ^ 2) := by
  rw [thetaSeries_zpow_mul_of_sq_eq_neg_one hr0 hc j,
    mul_div_cancel_right₀ _ (thetaSeries_ne_zero_of_sq_eq_neg_one hr0 hr hc h2)]

/-- Recovering the `μ_{2l}`-orbit of `qq^{j²}` from the ratio `R_j = Θ(r^j · c)/Θ(c)`: for `x`
in `K`, `x^{2l} · R_j² = 1` (that is, `x^{−l} = ±R_j` for `x ≠ 0`) holds if and only if
`x = ζ · qq^{j²}` for some `ζ ∈ K` with `ζ^{2l} = 1`. Here `qq^l = r`, so `qq^{2l} = q_X`. -/
theorem pow_mul_thetaRatio_sq_eq_one_iff {r c qq : K} (hr0 : r ≠ 0) (hr : ‖r‖ < 1)
    (hc : c ^ 2 = -1) (h2 : (2 : K) ≠ 0) {l : ℕ} (hqq : qq ^ l = r) (j : ℤ) (x : K) :
    x ^ (2 * l) * (thetaSeries r (r ^ j * c) / thetaSeries r c) ^ 2 = 1 ↔
      ∃ ζ : K, ζ ^ (2 * l) = 1 ∧ x = ζ * qq ^ (j ^ 2) := by
  have hqq0 : qq ≠ 0 := by
    rintro rfl
    rcases l with _ | l
    · simp only [pow_zero] at hqq; rw [← hqq, norm_one] at hr; exact lt_irrefl _ hr
    · simp at hqq; exact hr0 hqq.symm
  set Q := qq ^ (j ^ 2) with hQ
  have hQ0 : Q ≠ 0 := zpow_ne_zero _ hqq0
  have hR : thetaSeries r (r ^ j * c) / thetaSeries r c = (Q ^ l)⁻¹ := by
    rw [thetaSeries_div_of_sq_eq_neg_one hr0 hr hc h2, hQ, ← zpow_natCast, ← zpow_mul,
      mul_comm (j ^ 2), zpow_mul, zpow_natCast, hqq, zpow_neg]
  rw [hR, inv_pow, ← pow_mul, mul_comm l 2, mul_inv_eq_one₀ (pow_ne_zero _ hQ0)]
  constructor
  · intro h
    refine ⟨x / Q, ?_, by rw [div_mul_cancel₀ _ hQ0]⟩
    rw [div_pow, h, div_self (pow_ne_zero _ hQ0)]
  · rintro ⟨ζ, hζ, rfl⟩
    rw [mul_pow, hζ, one_mul]

end Ultrametric

section Padic

/-! ## Instance: `K = ℚ_[p]`, `r = p` (so `q_X = p²`)

Since `p` is not a square in `ℚ_[p]`, the parameter is taken to be `r = p`, that is `q_X = p²`. -/

variable {p : ℕ} [Fact p.Prime]

/-- The theta series over `ℚ_[p]` with `r = p` converges at every `u ≠ 0`. -/
theorem padic_summable_thetaTerm {u : ℚ_[p]} (hu : u ≠ 0) :
    Summable (thetaTerm (p : ℚ_[p]) u) :=
  summable_thetaTerm (by exact_mod_cast (Fact.out : p.Prime).ne_zero) Padic.norm_p_lt_one hu

/-- The zeros `Θ(±p^a) = 0` over `ℚ_[p]`. -/
theorem padic_thetaSeries_zpow (a : ℤ) :
    thetaSeries (p : ℚ_[p]) ((p : ℚ_[p]) ^ a) = 0 ∧ thetaSeries (p : ℚ_[p]) (-(p : ℚ_[p]) ^ a) = 0 :=
  thetaSeries_zpow (by exact_mod_cast (Fact.out : p.Prime).ne_zero) Padic.norm_p_lt_one a

/-- The norm of the ratio `Θ(p^j · c)/Θ(c) = p^{−j²}` over `ℚ_[p]` is `p^{j²}`, for any `c` with
`c² = −1`. -/
theorem padic_norm_thetaRatio {c : ℚ_[p]} (hc : c ^ 2 = -1) (j : ℤ) :
    ‖thetaSeries (p : ℚ_[p]) ((p : ℚ_[p]) ^ j * c) / thetaSeries (p : ℚ_[p]) c‖ =
      (p : ℝ) ^ (j ^ 2) := by
  have h2 : (2 : ℚ_[p]) ≠ 0 := two_ne_zero
  rw [thetaSeries_div_of_sq_eq_neg_one (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    Padic.norm_p_lt_one hc h2, Padic.norm_p_zpow, neg_neg]

/-- Nonvacuity of the hypothesis `c² = −1`: `ℚ_[5]` contains a square root of `−1` (Hensel's
lemma applied to `X² + 1` at `2`). -/
theorem exists_sq_eq_neg_one_padic_five (hp : p = 5) : ∃ c : ℚ_[p], c ^ 2 = -1 := by
  subst hp
  have hnorm : ‖(Polynomial.X ^ 2 + 1 : Polynomial ℤ).aeval (2 : ℤ_[5])‖ <
      ‖(Polynomial.derivative (Polynomial.X ^ 2 + 1 : Polynomial ℤ)).aeval (2 : ℤ_[5])‖ ^ 2 := by
    have h5 : (Polynomial.X ^ 2 + 1 : Polynomial ℤ).aeval (2 : ℤ_[5]) = ((5 : ℕ) : ℤ_[5]) := by
      simp; norm_num
    have hd : Polynomial.derivative (Polynomial.X ^ 2 + 1 : Polynomial ℤ) =
        Polynomial.C 2 * Polynomial.X := by
      rw [Polynomial.derivative_add, Polynomial.derivative_X_pow, Polynomial.derivative_one,
        add_zero]
      simp
    have h4 : (Polynomial.derivative (Polynomial.X ^ 2 + 1 : Polynomial ℤ)).aeval (2 : ℤ_[5]) =
        ((4 : ℕ) : ℤ_[5]) := by
      rw [hd, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      simp; norm_num
    rw [h5, h4, PadicInt.norm_p, PadicInt.norm_natCast_eq_one_iff.mpr (by norm_num)]
    norm_num
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  refine ⟨(z : ℚ_[5]), ?_⟩
  have h : z ^ 2 + 1 = 0 := by simpa using hz
  have h' : ((z ^ 2 + 1 : ℤ_[5]) : ℚ_[5]) = 0 := by rw [h]; simp
  push_cast at h'
  linear_combination h'

/-- An unconditional value over `ℚ_[5]` with `r = 5`: there is `c` with `c² = −1`, and for it
`‖Θ(5^j · c)/Θ(c)‖ = 5^{j²}` for every `j ∈ ℤ`. -/
theorem padic_five_norm_thetaRatio (hp : p = 5) :
    ∃ c : ℚ_[p], c ^ 2 = -1 ∧ ∀ j : ℤ,
      ‖thetaSeries (p : ℚ_[p]) ((p : ℚ_[p]) ^ j * c) / thetaSeries (p : ℚ_[p]) c‖ =
        (p : ℝ) ^ (j ^ 2) := by
  obtain ⟨c, hc⟩ := exists_sq_eq_neg_one_padic_five hp
  exact ⟨c, hc, padic_norm_thetaRatio hc⟩

end Padic

end IUT.Prerequisites.ThetaFunction
