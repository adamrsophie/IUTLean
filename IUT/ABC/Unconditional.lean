import IUT.ABC.Variants

/-!
# Unconditional theorems and an exact reduction around the abc conjecture

This file proves unconditional statements about triples `a + b = c` and one reduction of the abc
conjecture to a restricted form, equivalent to it for every `D ≥ 1` (the instance `D = 0` holds
vacuously). Nothing here says whether the abc conjecture holds, and no page of the IUT papers
is used.

**Triples supported on `{2, 3}`.** A coprime triple of positive integers `a + b = c` whose
product has no prime factor other than `2` and `3` is, up to the order of `a` and `b`, one of
`1 + 1 = 2`, `1 + 2 = 3`, `1 + 3 = 4`, `1 + 8 = 9` (`uncond_triples_two_three`, with the
converse `uncond_triples_two_three_mem`). The proof solves `3^y + 1 = 2^x` modulo `8` and
`2^x + 1 = 3^y` modulo `4` and by factoring `3^(2k) - 1`. Consequently the largest quality
`log c / log rad(abc)` on this family is `log 9 / log 6`, attained by `1 + 8 = 9`
(`uncond_quality_le_two_three`, `uncond_quality_one_eight_nine`). These are classical facts
(Catalan type equations with the bases `2` and `3`); no source page was read for them.

**Restriction to triples with `D ∣ abc`.** `uncondABCRestrictedToStatement D` is the abc
conjecture, with the quantifiers, the constant and the inequality of `Challenge.ABC`, for the
triples with `D ∣ abc` only. For every `D ≥ 1` it is equivalent to `Challenge.ABC`
(`uncondABCRestrictedToStatement_iff`); for `D ≥ 1` it is therefore an open statement, and
nothing here proves it; for `D = 0` it holds vacuously. The nontrivial direction is the power
trick: from `(a, b, c)` pass to `(a^n, c^n - a^n, c^n)` with `n = D φ(D)`. Then `D` divides
the new product (`uncond_dvd_power_triple`, by Euler's theorem modulo each prime power of `D`),
the new radical is at most `rad(abc) n c^(n - 1)` (`uncond_rad_power_triple_le`, from
`c^n - a^n = b ∑ c^i a^(n - 1 - i)`), and the factor `c^(n - 1)` is absorbed: with the restricted
statement used at `δ = ε / (n (1 + ε))`, one gets `c^t ≤ K n^(1 + δ) rad(abc)^(1 + δ)` with
`t = 1 - (n - 1) δ > 0`, and `(1 + δ) / t ≤ 1 + ε` (`uncond_power_trick_real`). So the loss is
absorbed into `ε` because `n` depends on `D` only. Source of the idea: M. van Frankenhuijsen,
*Two restricted abc conjectures*, arXiv 2010.09493, pages 1 and 2 (Ellenberg's theorem, with
the Euler indicator `n = φ(D)` and the cover `x ↦ x^n`; read and checked against rendered
images), and Theorem 4.5 with its proof and the two lemmas of Section 2 on heights of powers
that it uses (read in the TeX source, not rendered). The exponent `n = D φ(D)` (larger than
the `φ(D)` of the source, which makes the case `p ∣ ac` immediate) and the inequalities are
worked out for this file.

**Mason–Stothers on `ℙ¹`.** For coprime nonzero polynomials `A`, `B` over a field of
characteristic zero, not both constant, `max(deg A, deg B) + 2 ≤ deg rad(A B (B - A)) + δ`,
where `δ = 0` if `A`, `B`, `B - A` have the same degree (the point at infinity is not mapped
into `{0, 1, ∞}` by `A/B`) and `δ = 1` otherwise (`uncond_masonStothers_projective`). This is
the count of the points over `{0, 1, ∞}` given by the Riemann–Hurwitz formula; the case `δ = 1`
is Mathlib's `Polynomial.abc`, and the case `δ = 0` gains `1` from the cancellation of the
leading terms of the Wronskian. It is a theorem about polynomials and implies nothing about
integers.

**An infinite family.** For primes `p < q ≤ 2p`, the triple `(p², q², p² + q²)` is coprime with
`2c ≤ 5 rad(abc)` (`uncond_two_mul_le_five_mul_rad`); by Bertrand's postulate the set of
coprime triples with `2c ≤ 5 rad(abc)` is infinite (`uncond_infinite_two_mul_le_five_mul_rad`).

**Two roots of bounded degree.** For a field `K`, `x ∈ K` and `n ≥ 1`, an intermediate field
`L` of an algebraic closure contains `u`, `v` with `u^n = x`, `v^n = 1 - x` and `[L : K] ≤ n²`
(`uncond_exists_roots_finrank_le`). This is the first step of the passage to the Fermat curve
`X^n + Y^n = Z^n` with the map `[X : Y : Z] ↦ [X^n : Z^n]` of degree `n²` in V. Dimitrov,
*Effectivity in Mochizuki's work on the abc-conjecture*, arXiv 1601.03572, page 9 (Section 5;
the choice of `Q ∈ π_n⁻¹(P)`); page 3 (the statement of the main theorem) was read for context.
Both pages were checked against rendered images. The degree bound is not stated as such on
page 9; it is the degree `n²` of the map stated there. The hypotheses `x ≠ 0, 1` are not needed
for this step. Nothing further along that route is formalized.

## Not proved

* No unconditional upper or lower bound beyond those above (for example bounds on `c` in terms
  of the number of prime factors of `abc` by counting `S`-units) is stated: none was proved.
* The equality case `A = t^n`, `B = t^n + 1` of `uncond_masonStothers_projective` is checked by
  hand in the docstring, not formalized (it needs the squarefreeness of `t^n + 1`).
-/

namespace IUT.ABC.Unconditional

open Challenge IUT.ABC IUT.ABC.Variants

/-! ## Triples supported on the primes `2` and `3` -/

/-- `3^y` modulo `8` is `1` or `3`. -/
theorem uncond_three_pow_mod_eight (y : ℕ) : 3 ^ y % 8 = 1 ∨ 3 ^ y % 8 = 3 := by
  induction y with
  | zero => left; rfl
  | succ y ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

/-- The only solution of `3^y + 1 = 2^x` with `y ≥ 1` is `y = 1`, `x = 2`. Modulo `8`, the left
side is `2` or `4`, so `x ≤ 2`. -/
theorem uncond_three_pow_add_one_eq_two_pow {x y : ℕ} (hy : 1 ≤ y) (h : 3 ^ y + 1 = 2 ^ x) :
    y = 1 ∧ x = 2 := by
  have hx : x ≤ 2 := by
    by_contra hx
    have h8 : 2 ^ x % 8 = 0 := by
      obtain ⟨j, rfl⟩ : ∃ j, x = j + 3 := ⟨x - 3, by omega⟩
      rw [pow_add]
      norm_num [Nat.mul_mod]
    rcases uncond_three_pow_mod_eight y with h3 | h3 <;> omega
  have h4 : 2 ^ x ≤ 4 := by
    calc 2 ^ x ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hx
      _ = 4 := by norm_num
  have hy1 : y = 1 := by
    by_contra hy1
    have : 3 ^ 2 ≤ 3 ^ y := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  subst hy1
  refine ⟨rfl, ?_⟩
  interval_cases x <;> simp_all

/-- The solutions of `2^x + 1 = 3^y` with `x ≥ 1` are `(x, y) = (1, 1)` and `(3, 2)`. For
`x ≥ 2`, modulo `4` the exponent `y` is even, `y = 2k`, and `3^k + 1` divides
`2^x = (3^k + 1)(3^k - 1)`, so it is a power of `2`; then `k = 1` by
`uncond_three_pow_add_one_eq_two_pow`. -/
theorem uncond_two_pow_add_one_eq_three_pow {x y : ℕ} (hx : 1 ≤ x) (h : 2 ^ x + 1 = 3 ^ y) :
    (x = 1 ∧ y = 1) ∨ (x = 3 ∧ y = 2) := by
  rcases Nat.lt_or_ge x 2 with hx2 | hx2
  · have hx1 : x = 1 := by omega
    subst hx1
    left
    refine ⟨rfl, ?_⟩
    have h3 : 3 ^ y = 3 ^ 1 := by omega
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h3
  · right
    have h4 : 2 ^ x % 4 = 0 := by
      obtain ⟨j, rfl⟩ : ∃ j, x = j + 2 := ⟨x - 2, by omega⟩
      rw [pow_add]
      norm_num [Nat.mul_mod]
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' y
    · subst hk
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · exfalso
          rw [mul_zero, pow_zero] at h
          have : 0 < 2 ^ x := by positivity
          omega
        · exact hk
      obtain ⟨m, hm⟩ : ∃ m, 3 ^ k = m + 1 := ⟨3 ^ k - 1, by
        have := Nat.one_le_pow k 3 (by norm_num); omega⟩
      have hsq : 2 ^ x = (m + 2) * m := by
        rw [pow_mul', hm] at h
        nlinarith
      have hdvd : m + 2 ∣ 2 ^ x := ⟨m, hsq⟩
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      have hj' : 3 ^ k + 1 = 2 ^ j := by omega
      obtain ⟨rfl, -⟩ := uncond_three_pow_add_one_eq_two_pow hk1 hj'
      refine ⟨?_, rfl⟩
      have h8 : 2 ^ x = 2 ^ 3 := by
        have : 3 ^ (2 * 1) = 9 := by norm_num
        omega
      exact Nat.pow_right_injective (le_refl 2) h8
    · exfalso
      subst hk
      have : 3 ^ (2 * k + 1) % 4 = 3 := by
        rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
        norm_num
      omega

/-- A prime dividing both members of a coprime pair does not exist. -/
theorem uncond_prime_not_dvd_both {b c p : ℕ} (hbc : b.Coprime c) (hp : p.Prime) (hb : p ∣ b)
    (hc : p ∣ c) : False := by
  have := Nat.dvd_gcd hb hc
  rw [hbc.gcd_eq_one] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-- A positive number all of whose prime divisors are `2` or `3`, and which is coprime to a
number divisible by `q`, where `q` is `2` or `3`, is a power of the other prime. -/
theorem uncond_eq_pow_of_support {b c q : ℕ} (hb0 : b ≠ 0) (hbc : b.Coprime c) (hqc : q ∣ c)
    (hq : q = 2 ∨ q = 3) (hS : ∀ p : ℕ, p.Prime → p ∣ b → p = 2 ∨ p = 3) :
    (q = 3 → ∃ e, b = 2 ^ e) ∧ (q = 2 → ∃ e, b = 3 ^ e) := by
  have hqp : q.Prime := by rcases hq with rfl | rfl <;> norm_num
  refine ⟨fun h3 => ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hb0 fun {d} hd hdb => ?_⟩,
    fun h2 => ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hb0 fun {d} hd hdb => ?_⟩⟩
  · rcases hS d hd hdb with h | h
    · exact h
    · subst h; subst h3
      exact (uncond_prime_not_dvd_both hbc hd hdb hqc).elim
  · rcases hS d hd hdb with h | h
    · subst h; subst h2
      exact (uncond_prime_not_dvd_both hbc hd hdb hqc).elim
    · exact h

/-- **The coprime triples supported on `{2, 3}`.** Let `a`, `b`, `c` be positive integers with
`a` and `b` coprime, `a + b = c`, and every prime factor of `abc` equal to `2` or `3`. Then the
triple is one of `(1, 1, 2)`, `(1, 2, 3)`, `(2, 1, 3)`, `(1, 3, 4)`, `(3, 1, 4)`, `(1, 8, 9)`,
`(8, 1, 9)`.

The three numbers are pairwise coprime, so at most two of them exceed `1`; since `c ≥ 2`, one of
`a`, `b` is `1`. The other two are then coprime powers of `2` and `3` differing by `1`, and
`uncond_three_pow_add_one_eq_two_pow` and `uncond_two_pow_add_one_eq_three_pow` list the
solutions. -/
theorem uncond_triples_two_three {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : a + b = c) (hS : ∀ p : ℕ, p.Prime → p ∣ a * b * c → p = 2 ∨ p = 3) :
    (a, b, c) = (1, 1, 2) ∨ (a, b, c) = (1, 2, 3) ∨ (a, b, c) = (2, 1, 3) ∨
      (a, b, c) = (1, 3, 4) ∨ (a, b, c) = (3, 1, 4) ∨ (a, b, c) = (1, 8, 9) ∨
      (a, b, c) = (8, 1, 9) := by
  obtain ⟨hac, hbc⟩ := coprime_sum_of_coprime hab h
  have hSa : ∀ p : ℕ, p.Prime → p ∣ a → p = 2 ∨ p = 3 := fun p hp hpa =>
    hS p hp ((hpa.mul_right b).mul_right c)
  have hSb : ∀ p : ℕ, p.Prime → p ∣ b → p = 2 ∨ p = 3 := fun p hp hpb =>
    hS p hp ((Dvd.dvd.mul_left hpb a).mul_right c)
  have hSc : ∀ p : ℕ, p.Prime → p ∣ c → p = 2 ∨ p = 3 := fun p hp hpc =>
    hS p hp (Dvd.dvd.mul_left hpc (a * b))
  -- the pair `x + 1 = z` case, for `x ≥ 2`
  have pair : ∀ x z : ℕ, 2 ≤ x → x.Coprime z → 1 + x = z →
      (∀ p : ℕ, p.Prime → p ∣ x → p = 2 ∨ p = 3) →
      (∀ p : ℕ, p.Prime → p ∣ z → p = 2 ∨ p = 3) →
      (x = 2 ∧ z = 3) ∨ (x = 3 ∧ z = 4) ∨ (x = 8 ∧ z = 9) := by
    intro x z hx hxz hsum hSx hSz
    obtain ⟨q, hq, hqz⟩ := Nat.exists_prime_and_dvd (show z ≠ 1 by omega)
    have hq23 := hSz q hq hqz
    obtain ⟨hx3, hx2⟩ := uncond_eq_pow_of_support (by omega) hxz hqz hq23 hSx
    obtain ⟨r, hr, hrx⟩ := Nat.exists_prime_and_dvd (show x ≠ 1 by omega)
    have hr23 := hSx r hr hrx
    obtain ⟨hz3, hz2⟩ := uncond_eq_pow_of_support (by omega) hxz.symm hrx hr23 hSz
    rcases hq23 with rfl | rfl
    · -- `z` even, `x` a power of `3`
      obtain ⟨i, hxe⟩ := hx2 rfl
      have hr3 : r = 3 := by
        rcases hr23 with rfl | rfl
        · exact (uncond_prime_not_dvd_both hxz Nat.prime_two hrx hqz).elim
        · rfl
      obtain ⟨j, hze⟩ := hz3 hr3
      have hi : 1 ≤ i := by
        rcases Nat.eq_zero_or_pos i with h0 | h0
        · rw [h0] at hxe; omega
        · exact h0
      have he : 3 ^ i + 1 = 2 ^ j := by rw [hxe, hze] at hsum; omega
      obtain ⟨hi1, hj2⟩ := uncond_three_pow_add_one_eq_two_pow hi he
      right; left
      rw [hxe, hze, hi1, hj2]; norm_num
    · -- `z` a multiple of `3`, `x` a power of `2`
      obtain ⟨i, hxe⟩ := hx3 rfl
      have hr2 : r = 2 := by
        rcases hr23 with rfl | rfl
        · rfl
        · exact (uncond_prime_not_dvd_both hxz Nat.prime_three hrx hqz).elim
      obtain ⟨j, hze⟩ := hz2 hr2
      have hi : 1 ≤ i := by
        rcases Nat.eq_zero_or_pos i with h0 | h0
        · rw [h0] at hxe; omega
        · exact h0
      have he : 2 ^ i + 1 = 3 ^ j := by rw [hxe, hze] at hsum; omega
      rcases uncond_two_pow_add_one_eq_three_pow hi he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; rw [hxe, hze, h1, h2]; norm_num
      · right; right; rw [hxe, hze, h1, h2]; norm_num
  -- one of `a`, `b` is `1`
  have hone : a = 1 ∨ b = 1 := by
    by_contra hne
    push Not at hne
    obtain ⟨pa, hpa, hpaa⟩ := Nat.exists_prime_and_dvd hne.1
    obtain ⟨pb, hpb, hpbb⟩ := Nat.exists_prime_and_dvd hne.2
    obtain ⟨pc, hpc, hpcc⟩ := Nat.exists_prime_and_dvd (show c ≠ 1 by omega)
    have h1 : pa ≠ pb := fun e => uncond_prime_not_dvd_both hab hpa hpaa (e ▸ hpbb)
    have h2 : pa ≠ pc := fun e => uncond_prime_not_dvd_both hac hpa hpaa (e ▸ hpcc)
    have h3 : pb ≠ pc := fun e => uncond_prime_not_dvd_both hbc hpb hpbb (e ▸ hpcc)
    rcases hSa pa hpa hpaa with e1 | e1 <;> rcases hSb pb hpb hpbb with e2 | e2 <;>
      rcases hSc pc hpc hpcc with e3 | e3 <;> omega
  rcases hone with rfl | rfl
  · rcases Nat.lt_or_ge b 2 with hb2 | hb2
    · have : b = 1 := by omega
      subst this; subst h; left; rfl
    · rcases pair b c hb2 hbc h hSb hSc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · right; left; rfl
      · right; right; right; left; rfl
      · right; right; right; right; right; left; rfl
  · rcases Nat.lt_or_ge a 2 with ha2 | ha2
    · have : a = 1 := by omega
      subst this; subst h; left; rfl
    · rcases pair a c ha2 hac (by omega) hSa hSc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · right; right; left; rfl
      · right; right; right; right; left; rfl
      · right; right; right; right; right; right; rfl

/-- Conversely, the seven triples of `uncond_triples_two_three` are coprime triples supported on
`{2, 3}`. -/
theorem uncond_triples_two_three_mem :
    ∀ t ∈ ({(1, 1, 2), (1, 2, 3), (2, 1, 3), (1, 3, 4), (3, 1, 4), (1, 8, 9), (8, 1, 9)} :
      Finset (ℕ × ℕ × ℕ)), 0 < t.1 ∧ 0 < t.2.1 ∧ t.1.Coprime t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧
      ∀ p : ℕ, p.Prime → p ∣ t.1 * t.2.1 * t.2.2 → p = 2 ∨ p = 3 := by
  have h72 : ∀ p : ℕ, p.Prime → p ∣ 72 → p = 2 ∨ p = 3 := by
    intro p hp hd
    have h : 72 = 2 ^ 3 * 3 ^ 2 := by norm_num
    rw [h] at hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h2 | h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3))
  have hsub : ∀ n : ℕ, n ∣ 72 → ∀ p : ℕ, p.Prime → p ∣ n → p = 2 ∨ p = 3 :=
    fun n hn p hp hpn => h72 p hp (hpn.trans hn)
  intro t ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, hsub _ (by norm_num)⟩

/-- **The maximal quality on the triples supported on `{2, 3}`** is `log 9 / log 6`, attained by
`1 + 8 = 9`: every coprime triple of positive integers `a + b = c` whose product has only the
prime factors `2` and `3` has `log c / log rad(abc) ≤ log 9 / log 6`. -/
theorem uncond_quality_le_two_three {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : a + b = c) (hS : ∀ p : ℕ, p.Prime → p ∣ a * b * c → p = 2 ∨ p = 3) :
    Real.log c / Real.log (rad (a * b * c)) ≤ Real.log 9 / Real.log 6 := by
  have h6 : rad (2 ^ 1 * 3 ^ 1) = 6 := by
    rw [rad_mul_of_coprime (by norm_num), rad_prime_pow Nat.prime_two (by norm_num),
      rad_prime_pow Nat.prime_three (by norm_num)]
  have h6' : rad (2 ^ 2 * 3 ^ 1) = 6 := by
    rw [rad_mul_of_coprime (by norm_num), rad_prime_pow Nat.prime_two (by norm_num),
      rad_prime_pow Nat.prime_three (by norm_num)]
  have hl6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hmono : ∀ x : ℝ, 0 < x → x ≤ 9 → Real.log x / Real.log 6 ≤ Real.log 9 / Real.log 6 :=
    fun x hx hx9 => div_le_div_of_nonneg_right (Real.log_le_log hx hx9) hl6.le
  rcases uncond_triples_two_three ha hb hab h hS with e | e | e | e | e | e | e <;>
    simp only [Prod.mk.injEq] at e <;> obtain ⟨rfl, rfl, rfl⟩ := e
  · rw [show (1 * 1 * 2 : ℕ) = 2 ^ 1 by norm_num, rad_prime_pow Nat.prime_two (by norm_num),
      div_self (Real.log_pos (by norm_num)).ne', le_div_iff₀ hl6, one_mul]
    exact Real.log_le_log (by norm_num) (by norm_num)
  · rw [show (1 * 2 * 3 : ℕ) = 2 ^ 1 * 3 ^ 1 by norm_num, h6]
    exact hmono _ (by norm_num) (by norm_num)
  · rw [show (2 * 1 * 3 : ℕ) = 2 ^ 1 * 3 ^ 1 by norm_num, h6]
    exact hmono _ (by norm_num) (by norm_num)
  · rw [show (1 * 3 * 4 : ℕ) = 2 ^ 2 * 3 ^ 1 by norm_num, h6']
    exact hmono _ (by norm_num) (by norm_num)
  · rw [show (3 * 1 * 4 : ℕ) = 2 ^ 2 * 3 ^ 1 by norm_num, h6']
    exact hmono _ (by norm_num) (by norm_num)
  · rw [rad_one_eight_nine]
    exact hmono _ (by norm_num) (by norm_num)
  · rw [show (8 * 1 * 9 : ℕ) = 1 * 8 * 9 by norm_num, rad_one_eight_nine]
    exact hmono _ (by norm_num) (by norm_num)

/-- The bound of `uncond_quality_le_two_three` is attained by `1 + 8 = 9`. -/
theorem uncond_quality_one_eight_nine :
    Real.log ((9 : ℕ) : ℝ) / Real.log (rad (1 * 8 * 9)) = Real.log 9 / Real.log 6 := by
  rw [rad_one_eight_nine]; norm_num

/-! ## Restriction to triples with `D ∣ abc`: the power trick -/

/-- **The abc conjecture restricted to triples with `D ∣ abc`.** For every real `ε > 0` there
is a real `K > 0` such that every coprime triple of positive integers `a + b = c` with `D`
dividing `abc` satisfies `c ≤ K * rad(abc)^(1 + ε)`. The quantifiers, the constant and the
non-strict inequality are those of `Challenge.ABC`; the only change is the extra hypothesis
`D ∣ a * b * c`.

This is an open statement for every `D ≥ 1`: it is equivalent to `Challenge.ABC`
(`uncondABCRestrictedToStatement_iff`). For `D = 0` it is vacuously true, since `abc > 0`. -/
def uncondABCRestrictedToStatement (D : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
    Nat.Coprime a b → a + b = c → D ∣ a * b * c → (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε)

/-- The exponent of the power trick: `n = D * φ(D)`. -/
def uncondPowerExponent (D : ℕ) : ℕ := D * D.totient

theorem uncond_one_le_powerExponent {D : ℕ} (hD : 0 < D) : 1 ≤ uncondPowerExponent D :=
  Nat.mul_pos hD (Nat.totient_pos.mpr hD)

/-- **Divisibility after the power map.** For `D ≥ 1`, `n = D * φ(D)`, and `a ≤ c`,
`D` divides `a^n * (c^n - a^n) * c^n`. For a prime power `p^k ∣ D`: if `p` divides `a` or `c`
then `p^k` divides `a^n` or `c^n`, because `k < p^k ≤ D ≤ n`; otherwise Euler's theorem modulo
`p^k`, with `φ(p^k) ∣ φ(D) ∣ n`, gives `a^n ≡ 1 ≡ c^n`. -/
theorem uncond_dvd_power_triple {D a c : ℕ} (hD : 0 < D) (hle : a ≤ c) :
    D ∣ a ^ uncondPowerExponent D * (c ^ uncondPowerExponent D - a ^ uncondPowerExponent D) *
      c ^ uncondPowerExponent D := by
  set n := uncondPowerExponent D with hn
  have hDn : D ≤ n := Nat.le_mul_of_pos_right D (Nat.totient_pos.mpr hD)
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  have hp' : p.Prime := hp
  have hkn : k ≤ n := by
    have h1 : k < p ^ k := Nat.lt_pow_self hp'.one_lt
    have h2 : p ^ k ≤ D := Nat.le_of_dvd hD hpk
    omega
  by_cases hpa : p ∣ a
  · have : p ^ k ∣ a ^ n := (pow_dvd_pow_of_dvd hpa k).trans (pow_dvd_pow a hkn)
    exact (this.mul_right _).mul_right _
  by_cases hpc : p ∣ c
  · have : p ^ k ∣ c ^ n := (pow_dvd_pow_of_dvd hpc k).trans (pow_dvd_pow c hkn)
    exact this.mul_left _
  have hca : (a.Coprime (p ^ k)) :=
    Nat.Coprime.pow_right k ((hp'.coprime_iff_not_dvd.mpr hpa).symm)
  have hcc : (c.Coprime (p ^ k)) :=
    Nat.Coprime.pow_right k ((hp'.coprime_iff_not_dvd.mpr hpc).symm)
  have htot : (p ^ k).totient ∣ n := (Nat.totient_dvd_of_dvd hpk).trans (Dvd.intro_left D rfl)
  obtain ⟨m, hm⟩ := htot
  have ha1 : a ^ n ≡ 1 [MOD p ^ k] := by
    rw [hm, pow_mul]
    simpa using (Nat.ModEq.pow_totient hca).pow m
  have hc1 : c ^ n ≡ 1 [MOD p ^ k] := by
    rw [hm, pow_mul]
    simpa using (Nat.ModEq.pow_totient hcc).pow m
  have hd : p ^ k ∣ c ^ n - a ^ n :=
    (Nat.modEq_iff_dvd' (Nat.pow_le_pow_left hle n)).mp (ha1.trans hc1.symm)
  exact (hd.mul_left _).mul_right _

/-- **The radical after the power map.** For positive `a`, `b` with `a + b = c` and `n ≥ 1`,
`rad(a^n * (c^n - a^n) * c^n) ≤ rad(abc) * (n * c^(n - 1))`. Indeed `c^n - a^n = b * S` with
`S = ∑_{i < n} c^i a^(n - 1 - i) ≤ n c^(n - 1)`, the product divides `(abc)^n * S`, and the
radical of that is at most `rad(abc) * S`. -/
theorem uncond_rad_power_triple_le {a b c n : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a + b = c)
    (hn : 1 ≤ n) :
    rad (a ^ n * (c ^ n - a ^ n) * c ^ n) ≤ rad (a * b * c) * (n * c ^ (n - 1)) := by
  set S := ∑ i ∈ Finset.range n, c ^ i * a ^ (n - 1 - i) with hSdef
  have hle : a ^ n ≤ c ^ n := Nat.pow_le_pow_left (by omega) n
  have hsub : c ^ n - a ^ n = b * S := by
    have hz : ((c ^ n - a ^ n : ℕ) : ℤ) = (b : ℤ) * (S : ℤ) := by
      rw [Nat.cast_sub hle]
      have hbz : (b : ℤ) = (c : ℤ) - a := by omega
      rw [hbz, hSdef]
      push_cast
      rw [mul_comm, geom_sum₂_mul]
    exact_mod_cast hz
  have hSle : S ≤ n * c ^ (n - 1) := by
    calc S ≤ ∑ _i ∈ Finset.range n, c ^ (n - 1) := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' : i < n := Finset.mem_range.mp hi
          calc c ^ i * a ^ (n - 1 - i) ≤ c ^ i * c ^ (n - 1 - i) :=
                Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
            _ = c ^ (n - 1) := by rw [← pow_add]; congr 1; omega
      _ = n * c ^ (n - 1) := by simp
  have hSpos : 0 < S := by
    have : 0 < b * S := by
      rw [← hsub]
      exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_left (by omega) (by omega))
    exact Nat.pos_of_mul_pos_left this
  have hP : 0 < a * b * c := Nat.mul_pos (Nat.mul_pos ha hb) (by omega)
  have hdvd : a ^ n * (c ^ n - a ^ n) * c ^ n ∣ (a * b * c) ^ n * S := by
    rw [hsub]
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine ⟨b ^ m, ?_⟩
    rw [hm]
    ring
  have hne : (a * b * c) ^ n * S ≠ 0 := by positivity
  have h1 : rad (a ^ n * (c ^ n - a ^ n) * c ^ n) ≤ rad ((a * b * c) ^ n * S) := by
    apply Nat.le_of_dvd (rad_pos _)
    rw [rad_eq_radical, rad_eq_radical]
    exact UniqueFactorizationMonoid.radical_dvd_radical hdvd hne
  have h2 : rad ((a * b * c) ^ n) = rad (a * b * c) := by
    rw [rad_eq_radical, rad_eq_radical, UniqueFactorizationMonoid.radical_pow _ (by omega)]
  calc rad (a ^ n * (c ^ n - a ^ n) * c ^ n) ≤ rad ((a * b * c) ^ n * S) := h1
    _ ≤ rad ((a * b * c) ^ n) * rad S := rad_mul_le_mul_rad _ _
    _ ≤ rad (a * b * c) * S := by rw [h2]; exact Nat.mul_le_mul_left _ (rad_le hSpos)
    _ ≤ rad (a * b * c) * (n * c ^ (n - 1)) := Nat.mul_le_mul_left _ hSle

/-- **The real inequality of the power trick.** Let `n ≥ 1`, `ε > 0`, `δ = ε / (n (1 + ε))`,
`t = 1 - (n - 1) δ`, `x ≥ 1`, `R ≥ 1` and `K > 0`. If `x^n ≤ K (R n x^(n - 1))^(1 + δ)` then
`x ≤ (K n^(1 + δ))^(1 / t) R^(1 + ε)`. The exponent bookkeeping: `t > 0`,
`x^n = x^((n - 1)(1 + δ)) x^t`, and `(1 + δ) / t ≤ 1 + ε` because
`(1 + ε) t - (1 + δ) = δ ε ≥ 0`. -/
theorem uncond_power_trick_real {n : ℕ} (hn : 1 ≤ n) {ε x R K : ℝ} (hε : 0 < ε) (hx : 1 ≤ x)
    (hR : 1 ≤ R) (hK : 0 < K)
    (h : x ^ n ≤ K * (R * (n * x ^ (n - 1))) ^ (1 + ε / (n * (1 + ε)))) :
    x ≤ (K * (n : ℝ) ^ (1 + ε / (n * (1 + ε)))) ^ (1 - ((n : ℝ) - 1) * (ε / (n * (1 + ε))))⁻¹ *
      R ^ (1 + ε) := by
  set δ := ε / (n * (1 + ε)) with hδdef
  set t := 1 - ((n : ℝ) - 1) * δ with htdef
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hδn : δ * (n * (1 + ε)) = ε := by
    rw [hδdef]; field_simp
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have ht : 0 < t := by rw [htdef]; nlinarith
  have hkey : (1 + δ) * t⁻¹ ≤ 1 + ε := by
    rw [← div_eq_mul_inv, div_le_iff₀ ht]
    have : (1 + ε) * t - (1 + δ) = δ * ε := by
      rw [htdef]; linear_combination (-1 : ℝ) * hδn
    nlinarith [mul_pos hδ hε]
  have hx0 : 0 < x := by linarith
  have hR0 : 0 < R := by linarith
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; simp
  -- rewrite both sides with real exponents
  have hxn : x ^ n = x ^ (((n : ℝ) - 1) * (1 + δ)) * x ^ t := by
    rw [← Real.rpow_add hx0, ← Real.rpow_natCast]
    congr 1; rw [htdef]; ring
  have hrhs : (R * (n * x ^ (n - 1))) ^ (1 + δ) =
      R ^ (1 + δ) * (n : ℝ) ^ (1 + δ) * x ^ (((n : ℝ) - 1) * (1 + δ)) := by
    rw [Real.mul_rpow hR0.le (by positivity), Real.mul_rpow (by positivity) (by positivity),
      ← hn1, Real.rpow_natCast_mul hx0.le]
    ring
  rw [hxn, hrhs] at h
  have hpos : 0 < x ^ (((n : ℝ) - 1) * (1 + δ)) := Real.rpow_pos_of_pos hx0 _
  have hxt : x ^ t ≤ K * (n : ℝ) ^ (1 + δ) * R ^ (1 + δ) := by
    have : x ^ (((n : ℝ) - 1) * (1 + δ)) * x ^ t ≤
        x ^ (((n : ℝ) - 1) * (1 + δ)) * (K * (n : ℝ) ^ (1 + δ) * R ^ (1 + δ)) := by
      calc _ ≤ _ := h
        _ = _ := by ring
    exact le_of_mul_le_mul_left this hpos
  have hKn : 0 < K * (n : ℝ) ^ (1 + δ) := by positivity
  calc x = (x ^ t) ^ t⁻¹ := (Real.rpow_rpow_inv hx0.le ht.ne').symm
    _ ≤ (K * (n : ℝ) ^ (1 + δ) * R ^ (1 + δ)) ^ t⁻¹ :=
        Real.rpow_le_rpow (by positivity) hxt (inv_nonneg.mpr ht.le)
    _ = (K * (n : ℝ) ^ (1 + δ)) ^ t⁻¹ * R ^ ((1 + δ) * t⁻¹) := by
        rw [Real.mul_rpow hKn.le (by positivity), ← Real.rpow_mul hR0.le]
    _ ≤ (K * (n : ℝ) ^ (1 + δ)) ^ t⁻¹ * R ^ (1 + ε) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR hkey) (by positivity)

/-- **The power trick.** For `D ≥ 1`, the abc conjecture restricted to triples with `D ∣ abc`
implies the abc conjecture. Given `ε > 0`, let `n = D φ(D)` and apply the restricted statement
with `δ = ε / (n (1 + ε))` to `(a^n, c^n - a^n, c^n)`, a coprime triple with `D` dividing the
product (`uncond_dvd_power_triple`) and radical at most `rad(abc) n c^(n - 1)`
(`uncond_rad_power_triple_le`); then `uncond_power_trick_real` absorbs the loss into the
exponent `1 + ε`.

Source of the idea: van Frankenhuijsen, arXiv 2010.09493, the introduction (Ellenberg's
theorem, pages 1 and 2) and Theorem 4.5, where `a/c` is replaced by `(a/c)^n`. The exponent
`n = D φ(D)` and the inequalities here are worked out for this file. -/
theorem uncond_ABC_of_restricted {D : ℕ} (hD : 0 < D) (h : uncondABCRestrictedToStatement D) :
    ABC := by
  intro ε hε
  set n := uncondPowerExponent D with hndef
  have hn : 1 ≤ n := uncond_one_le_powerExponent hD
  set δ := ε / (n * (1 + ε)) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  obtain ⟨K, hK, hb⟩ := h δ hδ
  refine ⟨(K * (n : ℝ) ^ (1 + δ)) ^ (1 - ((n : ℝ) - 1) * δ)⁻¹, by positivity, ?_⟩
  intro a b c ha hb' hc hab habc
  obtain ⟨hac, -⟩ := coprime_sum_of_coprime hab habc
  have hle : a ^ n ≤ c ^ n := Nat.pow_le_pow_left (by omega) n
  have hlt : a ^ n < c ^ n := Nat.pow_lt_pow_left (by omega) (by omega)
  have hcop : (a ^ n).Coprime (c ^ n - a ^ n) :=
    (Nat.coprime_sub_self_right hle).mpr (Nat.Coprime.pow n n hac)
  have hbound := hb (a ^ n) (c ^ n - a ^ n) (c ^ n) (by positivity) (Nat.sub_pos_of_lt hlt)
    (by positivity) hcop (Nat.add_sub_cancel' hle) (uncond_dvd_power_triple hD (by omega))
  have hrad := uncond_rad_power_triple_le ha hb' habc hn
  have hradr : ((rad (a ^ n * (c ^ n - a ^ n) * c ^ n) : ℕ) : ℝ) ≤
      (rad (a * b * c) : ℝ) * (n * (c : ℝ) ^ (n - 1)) := by exact_mod_cast hrad
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast (show 1 ≤ c by omega)
  have hmain : (c : ℝ) ^ n ≤ K * ((rad (a * b * c) : ℝ) * (n * (c : ℝ) ^ (n - 1))) ^ (1 + δ) := by
    calc (c : ℝ) ^ n = ((c ^ n : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ K * (rad (a ^ n * (c ^ n - a ^ n) * c ^ n) : ℝ) ^ (1 + δ) := hbound
      _ ≤ K * ((rad (a * b * c) : ℝ) * (n * (c : ℝ) ^ (n - 1))) ^ (1 + δ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hradr (by positivity))
            hK.le
  exact uncond_power_trick_real hn hε hc1 (one_le_rad_cast _) hK hmain

/-- The abc conjecture implies its restriction to triples with `D ∣ abc`. -/
theorem uncond_restricted_of_ABC (h : ABC) (D : ℕ) : uncondABCRestrictedToStatement D := by
  intro ε hε
  obtain ⟨K, hK, hb⟩ := h ε hε
  exact ⟨K, hK, fun a b c ha hb' hc hab habc _ => hb a b c ha hb' hc hab habc⟩

/-- **For every `D ≥ 1`, the abc conjecture restricted to triples with `D ∣ abc` is equivalent
to the abc conjecture.** -/
theorem uncondABCRestrictedToStatement_iff {D : ℕ} (hD : 0 < D) :
    uncondABCRestrictedToStatement D ↔ ABC :=
  ⟨uncond_ABC_of_restricted hD, fun h => uncond_restricted_of_ABC h D⟩

/-! ## Mason–Stothers on the projective line -/

/-- For nonzero `a`, `b`, `c` with `a` and `b` coprime and `a + b + c = 0`, the non-radical part
of `abc` divides the Wronskian `W(a, b)`. This is the divisibility step of the proof of
Mathlib's `Polynomial.abc`, repeated here because it is not exported there. -/
theorem uncond_divRadical_dvd_wronskian {k : Type*} [Field k] [DecidableEq k]
    {a b c : Polynomial k} (hab : IsCoprime a b) (hsum : a + b + c = 0) :
    EuclideanDomain.divRadical (a * b * c) ∣ Polynomial.wronskian a b := by
  have hbc : IsCoprime b c := by
    rw [add_eq_zero_iff_neg_eq] at hsum
    rw [← hsum, IsCoprime.neg_right_iff]
    convert IsCoprime.add_mul_left_right hab.symm 1
    rw [mul_one]
  have hsum' : b + c + a = 0 := by rwa [add_rotate] at hsum
  have hca : IsCoprime c a := by
    rw [add_eq_zero_iff_neg_eq] at hsum'
    rw [← hsum', IsCoprime.neg_right_iff]
    convert IsCoprime.add_mul_left_right hbc.symm 1
    rw [mul_one]
  have wbc : Polynomial.wronskian a b = Polynomial.wronskian b c :=
    Polynomial.wronskian_eq_of_sum_zero hsum
  have adr := divRadical_dvd_wronskian_left a b
  have bdr := divRadical_dvd_wronskian_right a b
  have cdr := divRadical_dvd_wronskian_right b c
  rw [← wbc] at cdr
  rw [EuclideanDomain.divRadical_mul (hca.symm.mul_left hbc),
    EuclideanDomain.divRadical_mul hab]
  exact (hca.divRadical.symm.mul_left hbc.divRadical).mul_dvd
    (hab.divRadical.mul_dvd adr bdr) cdr

/-- Whether the point at infinity of `ℙ¹` is mapped by `t ↦ A(t)/B(t)` to a point outside the
tripod `{0, 1, ∞}`: this happens exactly when `A`, `B` and `B - A` have the same degree. -/
def uncondInfinityOffTripod {k : Type*} [Field k] (A B : Polynomial k) : Prop :=
  A.natDegree = B.natDegree ∧ (B - A).natDegree = B.natDegree

open Classical in
/-- **Mason–Stothers for the rational function `A/B` on `ℙ¹`, with the point at infinity.**
Let `k` be a field of characteristic zero and `A`, `B` nonzero coprime polynomials, not both
constant (so that `f = A/B` is a nonconstant rational function of degree
`d = max(deg A, deg B)`). The number of points of `ℙ¹` over `0`, `1`, `∞` is at least `d + 2`:
the finite ones are the distinct roots of `A·B·(B - A)`, counted by `deg rad(A·B·(B - A))`, and
infinity is one of them unless `A`, `B`, `B - A` have the same degree
(`uncondInfinityOffTripod`). So
`max(deg A, deg B) + 2 ≤ deg rad(A·B·(B - A)) + (0 if infinity is off the tripod, else 1)`.

When infinity lies over the tripod this is Mathlib's `Polynomial.abc`. When it does not, the
Wronskian `W(A, B) = W(A, B - λA)` with `λ = lc(B)/lc(A)` has degree at most `2d - 2`, one less
than in the general bound, which gives the extra `1`. Example (not formalized): `A = t^n`,
`B = t^n + 1` has `d = n`, infinity over `1`, and both sides equal `n + 2`. -/
theorem uncond_masonStothers_projective {k : Type*} [Field k] [CharZero k] [DecidableEq k]
    {A B : Polynomial k} (hA : A ≠ 0) (hB : B ≠ 0) (hAB : IsCoprime A B)
    (hnc : ¬ (A.natDegree = 0 ∧ B.natDegree = 0)) :
    max A.natDegree B.natDegree + 2 ≤
      (UniqueFactorizationMonoid.radical (A * B * (B - A))).natDegree +
        (if uncondInfinityOffTripod A B then 0 else 1) := by
  have hAC : IsCoprime A (B - A) := by
    convert IsCoprime.add_mul_left_right hAB (-1) using 1
    ring
  have hC : B - A ≠ 0 := by
    intro h0
    have hBA : B = A := (sub_eq_zero.mp h0)
    rw [hBA] at hAB
    have hu : IsUnit A := isCoprime_self.mp hAB
    exact hnc ⟨Polynomial.natDegree_eq_zero_of_isUnit hu,
      hBA ▸ Polynomial.natDegree_eq_zero_of_isUnit hu⟩
  have hsum : A + (B - A) + -B = 0 := by ring
  have hrad : UniqueFactorizationMonoid.radical (A * (B - A) * -B) =
      UniqueFactorizationMonoid.radical (A * B * (B - A)) := by
    rw [show A * (B - A) * -B = -(A * B * (B - A)) by ring]
    exact UniqueFactorizationDomain.radical_neg
  set r := (UniqueFactorizationMonoid.radical (A * B * (B - A))).natDegree with hr
  by_cases hoff : uncondInfinityOffTripod A B
  · simp only [hoff, ↓reduceIte]
    obtain ⟨hdA, hdC⟩ := hoff
    set d := B.natDegree with hd
    have hd1 : 1 ≤ d := by omega
    have hlA : A.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hA
    have hlB : B.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hB
    set l := B.leadingCoeff / A.leadingCoeff with hl
    have hl0 : l ≠ 0 := div_ne_zero hlB hlA
    set E := B - Polynomial.C l * A with hE
    have hW : Polynomial.wronskian A (B - A) = Polynomial.wronskian A E := by
      simp only [hE, Polynomial.wronskian, Polynomial.derivative_sub,
        Polynomial.derivative_C_mul]
      ring
    have hW0 : Polynomial.wronskian A (B - A) ≠ 0 := by
      intro h0
      obtain ⟨h1, h2⟩ := hAC.wronskian_eq_zero_iff.mp h0
      have h3 : Polynomial.derivative B = 0 := by
        have : Polynomial.derivative (B - A) + Polynomial.derivative A = 0 := by
          rw [h1, h2, add_zero]
        rwa [← Polynomial.derivative_add, sub_add_cancel] at this
      exact hnc ⟨Polynomial.derivative_eq_zero.mp h1,
        Polynomial.derivative_eq_zero.mp h3⟩
    have hE0 : E ≠ 0 := by
      intro h0
      rw [hW, h0, Polynomial.wronskian_zero_right] at hW0
      exact hW0 rfl
    have hEdeg : E.natDegree < d := by
      have hdeg : B.degree = (Polynomial.C l * A).degree := by
        rw [Polynomial.degree_C_mul hl0, Polynomial.degree_eq_natDegree hA,
          Polynomial.degree_eq_natDegree hB, hdA]
      have hlc : B.leadingCoeff = (Polynomial.C l * A).leadingCoeff := by
        rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hl, div_mul_cancel₀ _ hlA]
      exact Polynomial.natDegree_lt_natDegree hE0 (Polynomial.degree_sub_lt_left hdeg hB hlc)
    have hWdeg : (Polynomial.wronskian A (B - A)).natDegree < A.natDegree + E.natDegree := by
      rw [hW] at hW0 ⊢
      exact Polynomial.natDegree_wronskian_lt_add hW0
    have hdvd := uncond_divRadical_dvd_wronskian hAC hsum
    have hP0 : A * (B - A) * -B ≠ 0 := mul_ne_zero (mul_ne_zero hA hC) (neg_ne_zero.mpr hB)
    have hdr : (EuclideanDomain.divRadical (A * (B - A) * -B)).natDegree ≤
        (Polynomial.wronskian A (B - A)).natDegree := Polynomial.natDegree_le_of_dvd hdvd hW0
    have htot : (A * (B - A) * -B).natDegree =
        (EuclideanDomain.divRadical (A * (B - A) * -B)).natDegree + r := by
      rw [hr, ← hrad, ← Polynomial.natDegree_mul (EuclideanDomain.divRadical_ne_zero hP0)
        UniqueFactorizationMonoid.radical_ne_zero, EuclideanDomain.divRadical_mul_radical]
    rw [Polynomial.natDegree_mul (mul_ne_zero hA hC) (neg_ne_zero.mpr hB),
      Polynomial.natDegree_mul hA hC, Polynomial.natDegree_neg] at htot
    rw [hdA, max_self]
    omega
  · simp only [hoff, ↓reduceIte]
    have h := Polynomial.abc hA hC (neg_ne_zero.mpr hB) hAC hsum
    rw [hrad, Polynomial.natDegree_neg] at h
    rcases h with ⟨h1, -, h3⟩ | ⟨h1, -, h3⟩
    · omega
    · exfalso
      rw [Polynomial.derivative_neg, neg_eq_zero] at h3
      exact hnc ⟨Polynomial.derivative_eq_zero.mp h1,
        Polynomial.derivative_eq_zero.mp h3⟩

/-! ## An infinite family with `c ≤ (5/2) rad(abc)` -/

/-- For primes `p < q ≤ 2p`, the triple `a = p²`, `b = q²`, `c = p² + q²` is coprime and
satisfies `2c ≤ 5 rad(abc)`: `pq` divides `rad(abc)`, and
`5pq - 2(p² + q²) = (2p - q)(2q - p) ≥ 0`. -/
theorem uncond_two_mul_le_five_mul_rad {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hq2 : q ≤ 2 * p) :
    (p ^ 2).Coprime (q ^ 2) ∧
      2 * (p ^ 2 + q ^ 2) ≤ 5 * rad (p ^ 2 * q ^ 2 * (p ^ 2 + q ^ 2)) := by
  have hcop : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq.ne
  refine ⟨Nat.Coprime.pow 2 2 hcop, ?_⟩
  set N := p ^ 2 * q ^ 2 * (p ^ 2 + q ^ 2)
  have hN : N ≠ 0 := by
    have h1 := pow_pos hp.pos 2
    have h2 := pow_pos hq.pos 2
    exact Nat.ne_of_gt (Nat.mul_pos (Nat.mul_pos h1 h2) (by omega))
  have hmem : ∀ r : ℕ, r.Prime → r ∣ N → r ∣ rad N := fun r hr hrN =>
    Finset.dvd_prod_of_mem (fun x => x) (Nat.mem_primeFactors.mpr ⟨hr, hrN, hN⟩)
  have hpN : p ∣ rad N := hmem p hp (((dvd_pow_self p two_ne_zero).mul_right _).mul_right _)
  have hqN : q ∣ rad N := hmem q hq ((Dvd.dvd.mul_left (dvd_pow_self q two_ne_zero) _).mul_right _)
  have hpqN : p * q ∣ rad N := hcop.mul_dvd_of_dvd_of_dvd hpN hqN
  have hle : p * q ≤ rad N := Nat.le_of_dvd (rad_pos N) hpqN
  have hineq : 2 * (p ^ 2 + q ^ 2) ≤ 5 * (p * q) := by
    have h1 : (0 : ℤ) ≤ (2 * p - q) * (2 * q - p) := mul_nonneg (by omega) (by omega)
    have : (2 * (p ^ 2 + q ^ 2) : ℤ) ≤ 5 * (p * q) := by nlinarith
    exact_mod_cast this
  omega

/-- **Infinitely many coprime triples with `2c ≤ 5 rad(abc)`.** By Bertrand's postulate, for every
prime `p` there is a prime `q` with `p < q ≤ 2p`, and `uncond_two_mul_le_five_mul_rad` applies to
`(p², q², p² + q²)`. -/
theorem uncond_infinite_two_mul_le_five_mul_rad :
    {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ t.1.Coprime t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧
      2 * t.2.2 ≤ 5 * rad (t.1 * t.2.1 * t.2.2)}.Infinite := by
  intro hfin
  obtain ⟨M, hM⟩ := (hfin.image (fun t => t.2.2)).bddAbove
  obtain ⟨p, hMp, hp⟩ := Nat.exists_infinite_primes (M + 1)
  obtain ⟨q, hq, hpq, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul p hp.ne_zero
  obtain ⟨hcop, hineq⟩ := uncond_two_mul_le_five_mul_rad hp hq hpq hq2
  have hmem : (p ^ 2, q ^ 2, p ^ 2 + q ^ 2) ∈ {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧
      t.1.Coprime t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧ 2 * t.2.2 ≤ 5 * rad (t.1 * t.2.1 * t.2.2)} :=
    ⟨pow_pos hp.pos 2, pow_pos hq.pos 2, hcop, rfl, hineq⟩
  have hle := hM ⟨_, hmem, rfl⟩
  have : p ≤ p ^ 2 := Nat.le_self_pow two_ne_zero p
  simp only at hle
  omega

/-! ## Two roots in an extension of degree at most `n²` -/

/-- **Adjoining an `n`-th root of `x` and of `1 - x`.** For a field `K`, an element `x` of `K`
and `n ≥ 1`, there is a finite extension `L` of `K` (an intermediate field of an algebraic
closure) containing `u`, `v` with `u^n = x`, `v^n = 1 - x` and `[L : K] ≤ n²`. This is the
first step of the passage to the Fermat curve `u^n + v^n = 1` (Dimitrov, arXiv 1601.03572; see
the module docstring). The hypotheses `x ≠ 0, 1` of that source are not needed for this step.

Proof: `L = K(u) ⊔ K(v)`; each of `K(u)`, `K(v)` has degree the degree of a minimal polynomial
dividing `X^n - x` or `X^n - (1 - x)`, so at most `n`, and the degree of a compositum is at
most the product. -/
theorem uncond_exists_roots_finrank_le {K : Type*} [Field K] (x : K) {n : ℕ} (hn : 0 < n) :
    ∃ L : IntermediateField K (AlgebraicClosure K), ∃ u v : L,
      u ^ n = algebraMap K L x ∧ v ^ n = 1 - algebraMap K L x ∧
      FiniteDimensional K L ∧ Module.finrank K L ≤ n ^ 2 := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) x) hn
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) (1 - x)) hn
  have hdeg : ∀ (w : AlgebraicClosure K) (y : K),
      w ^ n = algebraMap K (AlgebraicClosure K) y →
      FiniteDimensional K (IntermediateField.adjoin K {w}) ∧
        Module.finrank K (IntermediateField.adjoin K {w}) ≤ n := by
    intro w y hw
    have hint : IsIntegral K w := Algebra.IsIntegral.isIntegral w
    refine ⟨IntermediateField.adjoin.finiteDimensional hint, ?_⟩
    rw [IntermediateField.adjoin.finrank hint]
    have hdvd : minpoly K w ∣ Polynomial.X ^ n - Polynomial.C y :=
      minpoly.dvd K w (by simp [hw])
    calc (minpoly K w).natDegree ≤ (Polynomial.X ^ n - Polynomial.C y).natDegree :=
          Polynomial.natDegree_le_of_dvd hdvd (Polynomial.X_pow_sub_C_ne_zero hn y)
      _ = n := Polynomial.natDegree_X_pow_sub_C y
  obtain ⟨hfu, hu'⟩ := hdeg u x hu
  obtain ⟨hfv, hv'⟩ := hdeg v (1 - x) hv
  set Lu := IntermediateField.adjoin K {u}
  set Lv := IntermediateField.adjoin K {v}
  have huL : u ∈ Lu ⊔ Lv := le_sup_left (a := Lu) (IntermediateField.mem_adjoin_simple_self K u)
  have hvL : v ∈ Lu ⊔ Lv := le_sup_right (a := Lu) (IntermediateField.mem_adjoin_simple_self K v)
  refine ⟨Lu ⊔ Lv, ⟨u, huL⟩, ⟨v, hvL⟩, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    simp [hu]
  · apply Subtype.ext
    simp [hv]
  · exact IntermediateField.finiteDimensional_sup Lu Lv
  · calc Module.finrank K ↥(Lu ⊔ Lv) ≤ Module.finrank K Lu * Module.finrank K Lv :=
          IntermediateField.finrank_sup_le Lu Lv
      _ ≤ n * n := Nat.mul_le_mul hu' hv'
      _ = n ^ 2 := (sq n).symm

end IUT.ABC.Unconditional
