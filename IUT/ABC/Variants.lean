import IUT.Applications.ABCFormalConjectures

/-!
# Variants of the abc conjecture and elementary facts about abc triples

This file collects reformulations of the abc conjecture and elementary, unconditional facts about
triples `a + b = c` that other formalizations commonly use as reference points. Nothing here says
whether the abc conjecture holds. No page of the IUT papers is used.

**Reformulations, each proved equivalent to `Challenge.ABC`.**

* `ABCInt`: the signed integer form, with nonzero pairwise coprime integers `a + b + c = 0` and
  the bound `max(|a|, |b|, |c|) ≤ K * rad(|abc|)^(1 + ε)`; `ABCIntSum` is the same with
  `a + b = c` and signs arbitrary. The shape (a constant `K > 0` and the non-strict `≤`) is the
  shape of `Challenge.ABC`, so the comparison is exact. Equivalences: `abcInt_iff_ABC`,
  `abcIntSum_iff_ABC`.
* `ABCWithExponent κ`: the bound `c ≤ K * rad(abc)^κ` with one fixed exponent `κ`. The
  conjecture is `∀ ε > 0, ABCWithExponent (1 + ε)` (`abc_iff_forall_abcWithExponent`, true by
  definition). For one fixed `κ > 1` the statement `ABCWithExponent κ` is implied by the
  conjecture (`abcWithExponent_of_ABC`) and is strictly weaker as a statement: knowing it for one
  `κ > 1` gives no bound with any smaller exponent, so it does not give the conjecture by any
  argument in this file. Results and claims with one fixed exponent larger than `1` (for example
  of the form `24 + ε`) appear in the literature; each is a statement of this weaker shape, not
  the conjecture. For `κ ≤ 1` the statement is false (`not_abcWithExponent_of_le_one`).

The quality form `q(a, b, c) = log c / log rad(abc)` and its finiteness statement are already in
`IUT.ABC.FormalConjectures` (`quality`, `qualityVariant`, `qualityVariant_iff_ABC`); this file
reuses that definition of the quality and does not restate the finiteness form.

**Elementary facts.**

* Trivial bounds: `2 ≤ rad(abc)` (`two_le_rad_of_triple`), `rad(abc) ≤ abc`
  (`rad_le_mul_mul`), `abc < c^3` (`mul_mul_lt_cube`), and `6 ≤ rad(abc)` once `c ≥ 3`
  (`six_le_rad_of_three_le`); the triple `1 + 1 = 2` with `rad = 2` shows that `c ≥ 3` is needed
  (`rad_one_one_two`). The bound `c < rad(abc)^2` is a conjecture and is not stated.
* Lemma 2.2 of R. Laniewski and K. Müller, *The quality plane of abc-triples and the
  decomposition into gains* (page 2, read and checked against a rendered image). Their triples
  are coprime positive `a + b = c` with `a < b`, and their balance is `λ = log(abc) / log c`. The
  lemma says `2 < λ < 3` when `a ≥ 2` and `2 - 1 / ((c - 1) log c) < λ < 2` when `a = 1`. All
  four inequalities are proved here, multiplied out by `log c > 0`: `log_mul_mul_lt_three_mul_log`,
  `two_mul_log_lt_log_mul_mul`, `log_mul_mul_lt_two_mul_log_of_one`,
  `two_mul_log_sub_lt_log_mul_mul_of_one`. The hypothesis `a ≥ 2` of the lower bound `λ > 2` is
  needed (`1 + 2 = 3`: `abc = 6 < 9 = c^2`), and so is `a < b`, which the lemma takes from the
  definition of a triple (`2 + 2 = 4`: `abc = 16 = c^2`, so `λ = 2`). Coprimality is not used
  by the lower bound once `a < b`.
* Classical examples: `1 + 8 = 9` with `rad = 6` and quality greater than `1`; Reyssat's triple
  `2 + 3^10 * 109 = 23^5` with `rad = 15042` and quality greater than `1.62`;
  `1 + 2 * 3^7 = 5^4 * 7` with `rad = 210` and quality greater than `1.56`.
* The exponent `1 + ε` cannot be replaced by `1`: the triples `1 + (3^(2^k) - 1) = 3^(2^k)`
  satisfy `2^k * rad(abc) < 3 c`, because `2^(k + 1)` divides `3^(2^k) - 1`
  (`two_pow_mul_rad_family_lt`). Hence for every real `K` there is a coprime triple with
  `c > K * rad(abc)` (`exists_coprime_triple_gt_mul_rad`), and `ABCWithExponent 1` is false
  (`not_abcWithExponent_one`). This guards against a statement of the conjecture with `ε = 0`.

**The polynomial analog.** Mathlib proves the Mason–Stothers theorem (`Polynomial.abc`, in
`Mathlib/NumberTheory/FLT/MasonStothers.lean`): for nonzero polynomials `a`, `b`, `c` over a
field with `a` and `b` coprime and `a + b + c = 0`, either all three derivatives vanish or each
degree is less than the degree of `radical (a * b * c)`. `masonStothers_natDegree_lt` restates
it for `a + b = c`. This is the function field analog of the abc conjecture; it is a theorem, and
it implies nothing about the statement for integers.
-/

namespace IUT.ABC.Variants

open Challenge IUT.ABC

/-! ## The signed integer form -/

/-- **The abc conjecture, signed integer form.** For every real `ε > 0` there is a real `K > 0`
such that all nonzero, pairwise coprime integers `a`, `b`, `c` with `a + b + c = 0` satisfy
`max(|a|, |b|, |c|) ≤ K * rad(|abc|)^(1 + ε)`. The absolute values are `Int.natAbs`, and the
constant and the non-strict inequality are those of `Challenge.ABC`. Equivalent to
`Challenge.ABC` (`abcInt_iff_ABC`). -/
def ABCInt : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 →
    IsCoprime a b → IsCoprime a c → IsCoprime b c → a + b + c = 0 →
      ((max a.natAbs (max b.natAbs c.natAbs) : ℕ) : ℝ) ≤
        K * (rad (a * b * c).natAbs : ℝ) ^ (1 + ε)

/-- **The abc conjecture, signed form with `a + b = c`.** As `ABCInt`, with `a + b = c` in place
of `a + b + c = 0` and the signs of `a`, `b`, `c` arbitrary. Equivalent to `Challenge.ABC`
(`abcIntSum_iff_ABC`). -/
def ABCIntSum : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 →
    IsCoprime a b → IsCoprime a c → IsCoprime b c → a + b = c →
      ((max a.natAbs (max b.natAbs c.natAbs) : ℕ) : ℝ) ≤
        K * (rad (a * b * c).natAbs : ℝ) ^ (1 + ε)

/-- The constant form, made symmetric: for pairwise coprime positive `A`, `B`, `C` one of which
is the sum of the other two, the largest is bounded by `K * rad(ABC)^(1 + ε)`. -/
theorem abc_symmetric_of_ABC (h : ABC) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ A B C : ℕ, 0 < A → 0 < B → 0 < C →
      A.Coprime B → A.Coprime C → B.Coprime C → (A + B = C ∨ A + C = B ∨ B + C = A) →
        ((max A (max B C) : ℕ) : ℝ) ≤ K * (rad (A * B * C) : ℝ) ^ (1 + ε) := by
  obtain ⟨K, hK, hb⟩ := h ε hε
  refine ⟨K, hK, fun A B C hA hB hC hAB hAC hBC hs => ?_⟩
  rcases hs with hs | hs | hs
  · have hm : max A (max B C) = C := by omega
    rw [hm]
    exact hb A B C hA hB hC hAB hs
  · have hm : max A (max B C) = B := by omega
    rw [hm, show A * B * C = A * C * B by ring]
    exact hb A C B hA hC hB hAC hs
  · have hm : max A (max B C) = A := by omega
    rw [hm, show A * B * C = B * C * A by ring]
    exact hb B C A hB hC hA hBC hs

/-- The constant form implies the signed integer form. Of three nonzero integers with sum `0`,
the absolute value of one is the sum of the other two absolute values. -/
theorem abcInt_of_ABC (h : ABC) : ABCInt := by
  intro ε hε
  obtain ⟨K, hK, hb⟩ := abc_symmetric_of_ABC h hε
  refine ⟨K, hK, fun a b c ha hb' hc hab hac hbc hs => ?_⟩
  rw [Int.natAbs_mul, Int.natAbs_mul]
  exact hb _ _ _ (Int.natAbs_pos.mpr ha) (Int.natAbs_pos.mpr hb') (Int.natAbs_pos.mpr hc)
    (Int.isCoprime_iff_nat_coprime.mp hab) (Int.isCoprime_iff_nat_coprime.mp hac)
    (Int.isCoprime_iff_nat_coprime.mp hbc) (by omega)

/-- For positive `a`, `b` with `a + b = c`, coprimality of `a` and `b` gives coprimality of
`a` and `c` and of `b` and `c`. -/
theorem coprime_sum_of_coprime {a b c : ℕ} (hab : a.Coprime b) (h : a + b = c) :
    a.Coprime c ∧ b.Coprime c := by
  subst h
  refine ⟨Nat.coprime_self_add_right.mpr hab, ?_⟩
  rw [add_comm]
  exact Nat.coprime_self_add_right.mpr hab.symm

/-- The signed integer form implies the constant form: apply it to `(a, b, -c)`. -/
theorem ABC_of_abcInt (h : ABCInt) : ABC := by
  intro ε hε
  obtain ⟨K, hK, hb⟩ := h ε hε
  refine ⟨K, hK, fun a b c ha hb' hc hab habc => ?_⟩
  obtain ⟨hac, hbc⟩ := coprime_sum_of_coprime hab habc
  have := hb (a : ℤ) b (-(c : ℤ)) (by omega) (by omega) (by omega)
    (Nat.Coprime.isCoprime hab) (Nat.Coprime.isCoprime hac).neg_right
    (Nat.Coprime.isCoprime hbc).neg_right (by omega)
  have hm : max (a : ℤ).natAbs (max (b : ℤ).natAbs (-(c : ℤ)).natAbs) = c := by
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    omega
  have hr : ((a : ℤ) * b * -(c : ℤ)).natAbs = a * b * c := by
    simp [Int.natAbs_mul]
  rwa [hm, hr] at this

/-- **The signed integer form is equivalent to `Challenge.ABC`.** -/
theorem abcInt_iff_ABC : ABCInt ↔ ABC := ⟨ABC_of_abcInt, abcInt_of_ABC⟩

/-- The two signed forms are equivalent: replace `c` by `-c`. -/
theorem abcIntSum_iff_abcInt : ABCIntSum ↔ ABCInt := by
  have key : ∀ a b c : ℤ,
      max a.natAbs (max b.natAbs (-c).natAbs) = max a.natAbs (max b.natAbs c.natAbs) ∧
      (a * b * -c).natAbs = (a * b * c).natAbs := fun a b c => by
    simp [Int.natAbs_mul]
  constructor
  · intro h ε hε
    obtain ⟨K, hK, hb⟩ := h ε hε
    refine ⟨K, hK, fun a b c ha hb' hc hab hac hbc hs => ?_⟩
    have := hb a b (-c) ha hb' (neg_ne_zero.mpr hc) hab hac.neg_right hbc.neg_right (by omega)
    rwa [(key a b c).1, (key a b c).2] at this
  · intro h ε hε
    obtain ⟨K, hK, hb⟩ := h ε hε
    refine ⟨K, hK, fun a b c ha hb' hc hab hac hbc hs => ?_⟩
    have := hb a b (-c) ha hb' (neg_ne_zero.mpr hc) hab hac.neg_right hbc.neg_right (by omega)
    rwa [(key a b c).1, (key a b c).2] at this

/-- **The signed form with `a + b = c` is equivalent to `Challenge.ABC`.** -/
theorem abcIntSum_iff_ABC : ABCIntSum ↔ ABC := abcIntSum_iff_abcInt.trans abcInt_iff_ABC

/-! ## A fixed exponent -/

/-- The bound of the abc conjecture with one fixed exponent `κ`: there is a real `K > 0` such that
every coprime triple of positive integers `a + b = c` satisfies `c ≤ K * rad(abc)^κ`. The
hypotheses, the constant and the non-strict inequality are those of `Challenge.ABC`.

The abc conjecture is `∀ ε > 0, ABCWithExponent (1 + ε)` (`abc_iff_forall_abcWithExponent`).
For one fixed `κ > 1` this proposition is implied by the conjecture and is an open, strictly
weaker statement; it does not give the conjecture. For `κ ≤ 1` it is false
(`not_abcWithExponent_of_le_one`). -/
def ABCWithExponent (κ : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → Nat.Coprime a b → a + b = c →
    (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ κ

/-- The abc conjecture is the fixed exponent bound for every exponent `1 + ε` with `ε > 0`. -/
theorem abc_iff_forall_abcWithExponent : ABC ↔ ∀ ε : ℝ, 0 < ε → ABCWithExponent (1 + ε) :=
  Iff.rfl

/-- The fixed exponent bound is monotone in the exponent, because `rad(abc) ≥ 1`. -/
theorem abcWithExponent_mono {κ κ' : ℝ} (h : κ ≤ κ') :
    ABCWithExponent κ → ABCWithExponent κ' := by
  rintro ⟨K, hK, hb⟩
  refine ⟨K, hK, fun a b c ha hb' hc hab habc => (hb a b c ha hb' hc hab habc).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (one_le_rad_cast _) h) hK.le

/-- The abc conjecture implies the fixed exponent bound for every exponent `κ > 1`. -/
theorem abcWithExponent_of_ABC (h : ABC) {κ : ℝ} (hκ : 1 < κ) : ABCWithExponent κ := by
  have := h (κ - 1) (by linarith)
  rwa [show 1 + (κ - 1) = κ by ring] at this

/-! ## Trivial bounds -/

/-- For positive `a`, `b` with `a + b = c`, `rad(abc) ≥ 2`. -/
theorem two_le_rad_of_triple {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a + b = c) :
    2 ≤ rad (a * b * c) :=
  FormalConjectures.two_le_rad
    (calc 2 ≤ c := by omega
      _ ≤ a * b * c := Nat.le_mul_of_pos_left c (Nat.mul_pos ha hb))

/-- For positive `a`, `b` with `a + b = c`, `rad(abc) ≤ abc`. -/
theorem rad_le_mul_mul {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a + b = c) :
    rad (a * b * c) ≤ a * b * c :=
  rad_le (Nat.mul_pos (Nat.mul_pos ha hb) (by omega))

/-- For positive `a`, `b` with `a + b = c`, `abc < c^3`. -/
theorem mul_mul_lt_cube {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a + b = c) :
    a * b * c < c ^ 3 := by
  have h1 : a * b < c * c := Nat.mul_lt_mul'' (by omega) (by omega)
  calc a * b * c < c * c * c := Nat.mul_lt_mul_of_pos_right h1 (by omega)
    _ = c ^ 3 := by ring

/-- For a coprime triple of positive integers `a + b = c` with `c ≥ 3`, `rad(abc) ≥ 6`: a prime
divisor of `c` and a prime divisor of whichever of `a`, `b` is at least `2` are distinct, so
their product, which is at least `2 * 3`, divides `rad(abc)`. The bound is attained by
`1 + 2 = 3`. -/
theorem six_le_rad_of_three_le {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : a + b = c) (hc : 3 ≤ c) : 6 ≤ rad (a * b * c) := by
  obtain ⟨hac, hbc⟩ := coprime_sum_of_coprime hab h
  have hn : a * b * c ≠ 0 := Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (by omega)) (by omega)
  obtain ⟨x, hx2, hxc, hxd⟩ : ∃ x, 2 ≤ x ∧ x.Coprime c ∧ x ∣ a * b * c := by
    rcases Nat.lt_or_ge 1 a with h1 | h1
    · exact ⟨a, h1, hac, (Dvd.intro b rfl).mul_right c⟩
    · exact ⟨b, by omega, hbc, (Dvd.intro_left a rfl).mul_right c⟩
  obtain ⟨q, hq, hqx⟩ := Nat.exists_prime_and_dvd (show x ≠ 1 by omega)
  obtain ⟨p, hp, hpc⟩ := Nat.exists_prime_and_dvd (show c ≠ 1 by omega)
  have hpq : p ≠ q := by
    rintro rfl
    have hd := Nat.dvd_gcd hqx hpc
    rw [hxc.gcd_eq_one] at hd
    exact hp.one_lt.ne' (Nat.dvd_one.mp hd)
  have hsub : ({p, q} : Finset ℕ) ⊆ (a * b * c).primeFactors := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact Nat.mem_primeFactors.mpr ⟨hp, hpc.trans (Dvd.intro_left (a * b) rfl), hn⟩
    · exact Nat.mem_primeFactors.mpr ⟨hq, hqx.trans hxd, hn⟩
  have hd : p * q ∣ rad (a * b * c) := by
    have hpair : ∏ r ∈ ({p, q} : Finset ℕ), r = p * q := Finset.prod_pair hpq
    unfold rad
    rw [← hpair]
    exact Finset.prod_dvd_prod_of_subset _ _ (fun r => r) hsub
  have hle := Nat.le_of_dvd (rad_pos _) hd
  have h2p := hp.two_le
  have h2q := hq.two_le
  rcases (show 3 ≤ p ∨ 3 ≤ q by omega) with h3 | h3 <;> nlinarith

/-- The hypothesis `c ≥ 3` of `six_le_rad_of_three_le` is needed: `1 + 1 = 2` has
`rad(1 * 1 * 2) = 2`. -/
theorem rad_one_one_two : rad (1 * 1 * 2) = 2 := by
  rw [show (1 * 1 * 2 : ℕ) = 2 ^ 1 by norm_num, rad_prime_pow Nat.prime_two (by norm_num)]

/-! ## Lemma 2.2 of Laniewski and Müller -/

/-- For positive `a`, `b` with `a + b = c`: `log(abc) < 3 log c`, that is, the balance is less
than `3` (Laniewski and Müller, *The quality plane of abc-triples and the decomposition into
gains*, Lemma 2.2, page 2). No coprimality and no order of `a`, `b` is needed. -/
theorem log_mul_mul_lt_three_mul_log {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a + b = c) :
    Real.log ((a * b * c : ℕ) : ℝ) < 3 * Real.log c := by
  have hpos : (0 : ℝ) < ((a * b * c : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos ha hb) (show 0 < c by omega)
  calc Real.log ((a * b * c : ℕ) : ℝ) < Real.log ((c ^ 3 : ℕ) : ℝ) :=
        Real.log_lt_log hpos (by exact_mod_cast mul_mul_lt_cube ha hb h)
    _ = 3 * Real.log c := by push_cast; rw [Real.log_pow]; norm_num

/-- For `2 ≤ a < b` with `a + b = c`: `c^2 < abc`, because `ab ≥ 2b > a + b = c`. -/
theorem sq_lt_mul_mul_of_two_le {a b c : ℕ} (ha : 2 ≤ a) (hab : a < b) (h : a + b = c) :
    c ^ 2 < a * b * c := by
  have h1 : c < a * b := by nlinarith
  calc c ^ 2 = c * c := by ring
    _ < a * b * c := Nat.mul_lt_mul_of_pos_right h1 (by omega)

/-- For `2 ≤ a < b` with `a + b = c`: `2 log c < log(abc)`, that is, the balance is greater than
`2` (Laniewski and Müller, *The quality plane of abc-triples and the decomposition into gains*,
Lemma 2.2, page 2). Coprimality is not needed. Both other hypotheses are needed:
`not_sq_lt_of_a_eq_one` and `not_sq_lt_of_a_eq_b`. -/
theorem two_mul_log_lt_log_mul_mul {a b c : ℕ} (ha : 2 ≤ a) (hab : a < b) (h : a + b = c) :
    2 * Real.log c < Real.log ((a * b * c : ℕ) : ℝ) := by
  calc 2 * Real.log c = Real.log ((c ^ 2 : ℕ) : ℝ) := by push_cast; rw [Real.log_pow]; norm_num
    _ < Real.log ((a * b * c : ℕ) : ℝ) :=
        Real.log_lt_log (by exact_mod_cast pow_pos (show 0 < c by omega) 2)
          (by exact_mod_cast sq_lt_mul_mul_of_two_le ha hab h)

/-- The hypothesis `a ≥ 2` of `two_mul_log_lt_log_mul_mul` is needed: `1 + 2 = 3` has
`abc = 6 < 9 = c^2`. -/
theorem not_sq_lt_of_a_eq_one : ¬ ((3 : ℕ) ^ 2 < 1 * 2 * 3) := by norm_num

/-- The hypothesis `a < b` of `two_mul_log_lt_log_mul_mul` is needed: `2 + 2 = 4` has
`abc = 16 = c^2`. -/
theorem not_sq_lt_of_a_eq_b : ¬ ((4 : ℕ) ^ 2 < 2 * 2 * 4) := by norm_num

/-- For `1 + b = c` with `b > 0`: `log(abc) < 2 log c`, that is, the balance is less than `2`
when `a = 1` (Laniewski and Müller, *The quality plane of abc-triples and the decomposition into
gains*, Lemma 2.2, page 2). -/
theorem log_mul_mul_lt_two_mul_log_of_one {b c : ℕ} (hb : 0 < b) (h : 1 + b = c) :
    Real.log ((1 * b * c : ℕ) : ℝ) < 2 * Real.log c := by
  have hlt : 1 * b * c < c ^ 2 := by
    calc 1 * b * c < c * c := by
          rw [one_mul]; exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      _ = c ^ 2 := by ring
  have hpos : (0 : ℝ) < ((1 * b * c : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos one_pos hb) (show 0 < c by omega)
  calc Real.log ((1 * b * c : ℕ) : ℝ) < Real.log ((c ^ 2 : ℕ) : ℝ) :=
        Real.log_lt_log hpos (by exact_mod_cast hlt)
    _ = 2 * Real.log c := by push_cast; rw [Real.log_pow]; norm_num

/-- For `1 + b = c` with `b ≥ 2`: `2 log c - 1 / (c - 1) < log(abc)`, that is,
`λ > 2 - 1 / ((c - 1) log c)` when `a = 1` (Laniewski and Müller, *The quality plane of
abc-triples and the decomposition into gains*, Lemma 2.2, page 2). The proof is theirs:
`log(c / (c - 1)) < c / (c - 1) - 1 = 1 / (c - 1)`. -/
theorem two_mul_log_sub_lt_log_mul_mul_of_one {b c : ℕ} (hb : 2 ≤ b) (h : 1 + b = c) :
    2 * Real.log c - 1 / ((c : ℝ) - 1) < Real.log ((1 * b * c : ℕ) : ℝ) := by
  have hB : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hC : (c : ℝ) = b + 1 := by rw [← h]; push_cast; ring
  have hne : ((b : ℝ) + 1) / b ≠ 1 := by
    rw [ne_eq, div_eq_one_iff_eq hb0.ne']
    linarith
  have hlt := Real.log_lt_sub_one_of_pos (x := ((b : ℝ) + 1) / b) (by positivity) hne
  rw [Real.log_div (by linarith) hb0.ne'] at hlt
  have heq : ((b : ℝ) + 1) / b - 1 = 1 / b := by field_simp; ring
  rw [heq] at hlt
  push_cast
  rw [one_mul, Real.log_mul hb0.ne' (by linarith), hC, show (b : ℝ) + 1 - 1 = b by ring]
  linarith

/-! ## Classical examples -/

/-- The radical of a prime is the prime. -/
theorem rad_of_prime {p : ℕ} (hp : p.Prime) : rad p = p := by
  simpa using rad_prime_pow hp one_ne_zero

/-- `1 + 8 = 9`: the radical of `1 * 8 * 9` is `6`. -/
theorem rad_one_eight_nine : rad (1 * 8 * 9) = 6 := by
  rw [show (1 * 8 * 9 : ℕ) = 2 ^ 3 * 3 ^ 2 by norm_num, rad_mul_of_coprime (by norm_num),
    rad_prime_pow Nat.prime_two (by norm_num), rad_prime_pow Nat.prime_three (by norm_num)]

/-- `1 + 8 = 9` has quality `log 9 / log 6 > 1`. -/
theorem one_lt_quality_one_eight_nine : 1 < FormalConjectures.quality 1 8 9 := by
  have := (FormalConjectures.quality_gt_iff (a := 1) (b := 8) (c := 9) one_pos (by norm_num)
    rfl 0).mpr (by rw [rad_one_eight_nine]; norm_num)
  simpa using this

/-- Reyssat's triple `2 + 3^10 * 109 = 23^5` is a coprime triple. -/
theorem reyssat_triple : 2 + 3 ^ 10 * 109 = 23 ^ 5 ∧ Nat.Coprime 2 (3 ^ 10 * 109) := by
  norm_num

/-- Reyssat's triple has radical `2 * 3 * 109 * 23 = 15042`. -/
theorem rad_reyssat : rad (2 * (3 ^ 10 * 109) * 23 ^ 5) = 15042 := by
  have h1 : Nat.Coprime (2 * (3 ^ 10 * 109)) (23 ^ 5) := by norm_num
  have h2 : Nat.Coprime 2 (3 ^ 10 * 109) := by norm_num
  have h3 : Nat.Coprime (3 ^ 10) 109 := by norm_num
  rw [rad_mul_of_coprime h1, rad_mul_of_coprime h2, rad_mul_of_coprime h3,
    rad_of_prime Nat.prime_two, rad_prime_pow Nat.prime_three (by norm_num),
    rad_of_prime (by norm_num : Nat.Prime 109), rad_prime_pow (by norm_num : Nat.Prime 23)
    (by norm_num)]

/-- Reyssat's triple has quality greater than `1.62`: `81 log 15042 < 50 log 23^5`, checked
as `15042^81 < (23^5)^50`. -/
theorem quality_reyssat_gt : (1.62 : ℝ) < FormalConjectures.quality 2 (3 ^ 10 * 109) (23 ^ 5) := by
  unfold FormalConjectures.quality
  rw [FormalConjectures.radical_eq_rad, rad_reyssat]
  have hl : 0 < Real.log ((15042 : ℕ) : ℝ) := Real.log_pos (by norm_num)
  rw [lt_div_iff₀ hl]
  have h : Real.log (((15042 : ℕ) : ℝ) ^ 81) < Real.log ((((23 ^ 5 : ℕ)) : ℝ) ^ 50) :=
    Real.log_lt_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h ⊢
  linarith

/-- The triple `1 + 2 * 3^7 = 5^4 * 7` is a coprime triple with radical `2 * 3 * 5 * 7 = 210`. -/
theorem rad_one_two_three_pow_seven :
    1 + 2 * 3 ^ 7 = 5 ^ 4 * 7 ∧ rad (1 * (2 * 3 ^ 7) * (5 ^ 4 * 7)) = 210 := by
  refine ⟨by norm_num, ?_⟩
  have h1 : Nat.Coprime (1 * (2 * 3 ^ 7)) (5 ^ 4 * 7) := by norm_num
  have h2 : Nat.Coprime 2 (3 ^ 7) := by norm_num
  have h3 : Nat.Coprime (5 ^ 4) 7 := by norm_num
  rw [rad_mul_of_coprime h1, one_mul, rad_mul_of_coprime h2, rad_mul_of_coprime h3,
    rad_of_prime Nat.prime_two, rad_prime_pow Nat.prime_three (by norm_num),
    rad_prime_pow (by norm_num : Nat.Prime 5) (by norm_num),
    rad_of_prime (by norm_num : Nat.Prime 7)]

/-- The triple `1 + 2 * 3^7 = 5^4 * 7` has quality greater than `1.56`:
`39 log 210 < 25 log 4375`. -/
theorem quality_one_two_three_pow_seven_gt :
    (1.56 : ℝ) < FormalConjectures.quality 1 (2 * 3 ^ 7) (5 ^ 4 * 7) := by
  unfold FormalConjectures.quality
  rw [FormalConjectures.radical_eq_rad, rad_one_two_three_pow_seven.2]
  have hl : 0 < Real.log ((210 : ℕ) : ℝ) := Real.log_pos (by norm_num)
  rw [lt_div_iff₀ hl]
  have h : Real.log (((210 : ℕ) : ℝ) ^ 39) < Real.log ((((5 ^ 4 * 7 : ℕ)) : ℝ) ^ 25) :=
    Real.log_lt_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h ⊢
  linarith

/-! ## The exponent `1` is too small -/

/-- `2^(k + 1)` divides `3^(2^k) - 1`, in the form `3^(2^k) = 2^(k + 1) * m + 1` with `m > 0`.
The step is `x^2 - 1 = (x - 1)(x + 1)` with `x + 1` even. -/
theorem three_pow_two_pow_eq_two_pow_mul_add_one (k : ℕ) :
    ∃ m : ℕ, 0 < m ∧ 3 ^ 2 ^ k = 2 ^ (k + 1) * m + 1 := by
  induction k with
  | zero => exact ⟨1, by norm_num, by norm_num⟩
  | succ k ih =>
    obtain ⟨m, hm, h⟩ := ih
    refine ⟨2 ^ k * m ^ 2 + m, by positivity, ?_⟩
    rw [pow_succ 2 k, pow_mul, h]
    ring

/-- The radical of a product is at most the product of the radicals. -/
theorem rad_mul_le_mul_rad (x y : ℕ) : rad (x * y) ≤ rad x * rad y := by
  have h := UniqueFactorizationMonoid.radical_mul_dvd (a := x) (b := y)
  rw [← rad_eq_radical, ← rad_eq_radical, ← rad_eq_radical] at h
  exact Nat.le_of_dvd (Nat.mul_pos (rad_pos x) (rad_pos y)) h

/-- The triples `1 + (3^(2^k) - 1) = 3^(2^k)` satisfy `2^k * rad(abc) < 3 c`. With
`3^(2^k) - 1 = 2^(k + 1) m`, the radical is at most `2 * m * 3`. -/
theorem two_pow_mul_rad_family_lt (k : ℕ) :
    2 ^ k * rad (1 * (3 ^ 2 ^ k - 1) * 3 ^ 2 ^ k) < 3 * 3 ^ 2 ^ k := by
  obtain ⟨m, hm, h⟩ := three_pow_two_pow_eq_two_pow_mul_add_one k
  have hrc : rad (3 ^ 2 ^ k) = 3 := rad_prime_pow Nat.prime_three (by positivity)
  have hr2 : rad (2 ^ (k + 1)) = 2 := rad_prime_pow Nat.prime_two (by omega)
  have hb : 3 ^ 2 ^ k - 1 = 2 ^ (k + 1) * m := by rw [h, Nat.add_sub_cancel]
  have hbnd : rad (1 * (3 ^ 2 ^ k - 1) * 3 ^ 2 ^ k) ≤ 2 * m * 3 := by
    rw [one_mul, hb]
    calc rad (2 ^ (k + 1) * m * 3 ^ 2 ^ k)
        ≤ rad (2 ^ (k + 1) * m) * rad (3 ^ 2 ^ k) := rad_mul_le_mul_rad _ _
      _ ≤ (rad (2 ^ (k + 1)) * rad m) * rad (3 ^ 2 ^ k) :=
          Nat.mul_le_mul_right _ (rad_mul_le_mul_rad _ _)
      _ ≤ (2 * m) * 3 := by
          rw [hr2, hrc]
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (rad_le hm))
  calc 2 ^ k * rad (1 * (3 ^ 2 ^ k - 1) * 3 ^ 2 ^ k) ≤ 2 ^ k * (2 * m * 3) :=
        Nat.mul_le_mul_left _ hbnd
    _ = 3 * (2 ^ (k + 1) * m) := by ring
    _ < 3 * 3 ^ 2 ^ k := by rw [h]; linarith

/-- **For every real `K` there is a coprime triple of positive integers `a + b = c` with
`c > K * rad(abc)`.** Take `k` with `2^k > 3 K` in `two_pow_mul_rad_family_lt`. -/
theorem exists_coprime_triple_gt_mul_rad (K : ℝ) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a.Coprime b ∧ a + b = c ∧
      K * (rad (a * b * c) : ℝ) < c := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (3 * K) (by norm_num : (1 : ℝ) < 2)
  obtain ⟨m, hm, h⟩ := three_pow_two_pow_eq_two_pow_mul_add_one k
  have hb : 3 ^ 2 ^ k - 1 = 2 ^ (k + 1) * m := by rw [h, Nat.add_sub_cancel]
  have key := two_pow_mul_rad_family_lt k
  refine ⟨1, 3 ^ 2 ^ k - 1, 3 ^ 2 ^ k, one_pos, by rw [hb]; positivity, by positivity,
    Nat.coprime_one_left _, Nat.add_sub_of_le (Nat.one_le_pow _ _ (by norm_num)), ?_⟩
  have hr : (2 : ℝ) ^ k * (rad (1 * (3 ^ 2 ^ k - 1) * 3 ^ 2 ^ k) : ℝ) <
      3 * ((3 ^ 2 ^ k : ℕ) : ℝ) := by
    exact_mod_cast key
  have hr1 := one_le_rad_cast (1 * (3 ^ 2 ^ k - 1) * 3 ^ 2 ^ k)
  have hprod := mul_pos (sub_pos.mpr hk) (show (0 : ℝ) < rad (1 * (3 ^ 2 ^ k - 1) * 3 ^ 2 ^ k) by
    linarith)
  nlinarith

/-- **The bound with exponent `1` is false**: no constant `K` gives `c ≤ K * rad(abc)` for all
coprime triples. So `ε > 0` in the abc conjecture cannot be dropped. -/
theorem not_abcWithExponent_one : ¬ ABCWithExponent 1 := by
  rintro ⟨K, _, hb⟩
  obtain ⟨a, b, c, ha, hb', hc, hab, habc, hlt⟩ := exists_coprime_triple_gt_mul_rad K
  have := hb a b c ha hb' hc hab habc
  rw [Real.rpow_one] at this
  linarith

/-- The bound with any exponent `κ ≤ 1` is false. -/
theorem not_abcWithExponent_of_le_one {κ : ℝ} (h : κ ≤ 1) : ¬ ABCWithExponent κ :=
  fun hk => not_abcWithExponent_one (abcWithExponent_mono h hk)

/-! ## The polynomial analog -/

/-- **Mason–Stothers for `a + b = c`.** For nonzero polynomials over a field with `a` and `b`
coprime, `a + b = c`, and not all three derivatives zero, the degree of `c` is less than the
degree of the radical of `abc`. This restates Mathlib's `Polynomial.abc` (stated there for
`a + b + c = 0`). It is the function field analog of the abc conjecture, a theorem, and it implies
nothing about the integer statement. -/
theorem masonStothers_natDegree_lt {k : Type*} [Field k] [DecidableEq k] {a b c : Polynomial k}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b) (hsum : a + b = c)
    (hder : ¬ (Polynomial.derivative a = 0 ∧ Polynomial.derivative b = 0 ∧
      Polynomial.derivative c = 0)) :
    c.natDegree < (UniqueFactorizationMonoid.radical (a * b * c)).natDegree := by
  have h := Polynomial.abc ha hb (neg_ne_zero.mpr hc) hab (by rw [← hsum]; ring)
  have hr : UniqueFactorizationMonoid.radical (a * b * -c) =
      UniqueFactorizationMonoid.radical (a * b * c) := by
    rw [mul_neg]
    exact UniqueFactorizationDomain.radical_neg
  rw [hr, Polynomial.natDegree_neg] at h
  rcases h with ⟨_, _, h⟩ | ⟨h1, h2, h3⟩
  · omega
  · exact absurd ⟨h1, h2, by simpa using h3⟩ hder

end IUT.ABC.Variants
