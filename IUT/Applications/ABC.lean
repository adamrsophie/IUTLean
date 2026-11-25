import Challenge.Defs

/-!
# The abc conjecture: basic facts and equivalent formulations

Everything here is unconditional. Nothing in this file says anything about whether the abc
conjecture holds. The file proves that the three formulations in `Challenge.Defs` are
equivalent, that the radical defined there is the one in Mathlib, and that the coprimality
hypothesis can be written in either of the two usual ways.
-/

namespace IUT.ABC

open Challenge

/-! ## The radical -/

/-- The radical of `Challenge.Defs` is Mathlib's radical on `ℕ`. -/
theorem rad_eq_radical (n : ℕ) : rad n = UniqueFactorizationMonoid.radical n :=
  Nat.radical_eq_prod_primeFactors.symm

theorem rad_pos (n : ℕ) : 0 < rad n :=
  Finset.prod_pos fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos

theorem rad_dvd (n : ℕ) : rad n ∣ n := Nat.prod_primeFactors_dvd n

theorem rad_le {n : ℕ} (hn : 0 < n) : rad n ≤ n := Nat.le_of_dvd hn (rad_dvd n)

theorem rad_zero : rad 0 = 1 := by simp [rad]

theorem rad_one : rad 1 = 1 := by simp [rad]

theorem rad_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) : rad (p ^ k) = p := by
  simp [rad, Nat.primeFactors_prime_pow hk hp]

theorem rad_mul_of_coprime {a b : ℕ} (h : a.Coprime b) : rad (a * b) = rad a * rad b := by
  unfold rad
  rw [h.primeFactors_mul, Finset.prod_union h.disjoint_primeFactors]

/-- Sanity check: `rad 12 = 6`. -/
example : rad 12 = 6 := by
  have h : (12 : ℕ) = 2 ^ 2 * 3 ^ 1 := by norm_num
  rw [h, rad_mul_of_coprime (by decide), rad_prime_pow Nat.prime_two (by decide),
    rad_prime_pow Nat.prime_three (by decide)]

/-- Sanity check: the triple `1 + 8 = 9` has `rad (1 * 8 * 9) = 6 < 9`. -/
example : rad (1 * 8 * 9) = 6 := by
  have h : (1 * 8 * 9 : ℕ) = 2 ^ 3 * 3 ^ 2 := by norm_num
  rw [h, rad_mul_of_coprime (by decide), rad_prime_pow Nat.prime_two (by decide),
    rad_prime_pow Nat.prime_three (by decide)]

theorem one_le_rad_cast (n : ℕ) : (1 : ℝ) ≤ rad n := by exact_mod_cast rad_pos n

theorem one_le_rad_rpow (n : ℕ) {y : ℝ} (hy : 0 ≤ y) : (1 : ℝ) ≤ (rad n : ℝ) ^ y :=
  Real.one_le_rpow (one_le_rad_cast n) hy

/-! ## Coprimality -/

/-- For positive `a`, `b` with `a + b = c`, coprimality of `a` and `b` is the same as pairwise
coprimality of `a`, `b`, `c` in the form used by the Formal Conjectures project. Positivity is
needed: for `a = b = c = 0` the set `{a, b, c}` is a singleton, so it is pairwise coprime,
while `0` and `0` are not coprime. -/
theorem coprime_iff_pairwise {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a + b = c) :
    a.Coprime b ↔ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime := by
  subst h
  constructor
  · intro hab
    have hac : a.Coprime (a + b) := by simpa using hab
    have hbc : b.Coprime (a + b) := by simpa using hab.symm
    intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hxy
        | assumption
        | exact Nat.Coprime.symm (by assumption)
  · intro hp
    by_cases hab : a = b
    · subst hab
      have hne : a ≠ a + a := by omega
      have := hp (by simp) (by simp) hne
      have h1 : a = 1 := by simpa [Nat.Coprime] using this
      simp [h1]
    · exact hp (by simp) (by simp) hab

/-! ## Equivalence of the formulations -/

/-- The constant form implies the logarithmic form, with `C = log K`. -/
theorem abcLog_of_abc (h : ABC) : ABCLog := by
  intro ε hε
  obtain ⟨K, hK, hbound⟩ := h ε hε
  refine ⟨Real.log K, fun a b c ha hb hc hab habc => ?_⟩
  have hr : (0 : ℝ) < rad (a * b * c) := by exact_mod_cast rad_pos _
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  calc Real.log c ≤ Real.log (K * (rad (a * b * c) : ℝ) ^ (1 + ε)) :=
        Real.log_le_log hc' (hbound a b c ha hb hc hab habc)
    _ = (1 + ε) * Real.log (rad (a * b * c)) + Real.log K := by
        rw [Real.log_mul hK.ne' (Real.rpow_pos_of_pos hr _).ne', Real.log_rpow hr]; ring

/-- The logarithmic form implies the constant form, with `K = exp C`. -/
theorem abc_of_abcLog (h : ABCLog) : ABC := by
  intro ε hε
  obtain ⟨C, hbound⟩ := h ε hε
  refine ⟨Real.exp C, Real.exp_pos C, fun a b c ha hb hc hab habc => ?_⟩
  have hr : (0 : ℝ) < rad (a * b * c) := by exact_mod_cast rad_pos _
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  calc (c : ℝ) = Real.exp (Real.log c) := (Real.exp_log hc').symm
    _ ≤ Real.exp ((1 + ε) * Real.log (rad (a * b * c)) + C) :=
        Real.exp_le_exp.mpr (hbound a b c ha hb hc hab habc)
    _ = Real.exp C * (rad (a * b * c) : ℝ) ^ (1 + ε) := by
        rw [Real.rpow_def_of_pos hr, Real.exp_add]; ring_nf

theorem abc_iff_abcLog : ABC ↔ ABCLog := ⟨abcLog_of_abc, abc_of_abcLog⟩

/-- The finiteness form implies the constant form. The constant is one plus a bound for the
values of `c` over the finitely many exceptional triples. -/
theorem abc_of_abcFinite (h : ABCFinite) : ABC := by
  intro ε hε
  obtain ⟨M, hM⟩ := ((h ε hε).image fun t : ℕ × ℕ × ℕ => t.2.2).bddAbove
  refine ⟨1 + M, by positivity, fun a b c ha hb hc hab habc => ?_⟩
  have hr1 : (1 : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε) := one_le_rad_rpow _ (by linarith)
  have hM0 : (0 : ℝ) ≤ M := by positivity
  by_cases hex : (rad (a * b * c) : ℝ) ^ (1 + ε) < c
  · have hcM : c ≤ M := hM ⟨(a, b, c), ⟨ha, hb, hc, hab, habc, hex⟩, rfl⟩
    have hcM' : (c : ℝ) ≤ M := by exact_mod_cast hcM
    calc (c : ℝ) ≤ (1 + M) * 1 := by linarith
      _ ≤ (1 + M) * (rad (a * b * c) : ℝ) ^ (1 + ε) :=
          mul_le_mul_of_nonneg_left hr1 (by linarith)
  · calc (c : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε) := not_lt.mp hex
      _ = 1 * (rad (a * b * c) : ℝ) ^ (1 + ε) := (one_mul _).symm
      _ ≤ (1 + M) * (rad (a * b * c) : ℝ) ^ (1 + ε) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)

/-- The constant form implies the finiteness form. One applies the constant form with `ε / 2`:
an exceptional triple for `ε` then has `rad ^ (ε / 2) < K`, which bounds the radical, hence
`c`, hence `a` and `b`. -/
theorem abcFinite_of_abc (h : ABC) : ABCFinite := by
  intro ε hε
  obtain ⟨K, hK, hbound⟩ := h (ε / 2) (by linarith)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = K * (K ^ (2 / ε)) ^ (1 + ε / 2) := ⟨_, rfl⟩
  refine (Set.finite_Iic ((⌊B⌋₊, ⌊B⌋₊, ⌊B⌋₊) : ℕ × ℕ × ℕ)).subset ?_
  rintro ⟨a, b, c⟩ ⟨ha, hb, hc, hab, habc, hex⟩
  simp only at ha hb hc hab habc hex
  have hle := hbound a b c ha hb hc hab habc
  have hr1 : (1 : ℝ) ≤ (rad (a * b * c) : ℕ) := one_le_rad_cast _
  generalize ((rad (a * b * c) : ℕ) : ℝ) = r at hex hle hr1
  have hr0 : 0 < r := by linarith
  have hsplit : r ^ (1 + ε) = r ^ (1 + ε / 2) * r ^ (ε / 2) := by
    rw [← Real.rpow_add hr0]; congr 1; ring
  have hpos : 0 < r ^ (1 + ε / 2) := Real.rpow_pos_of_pos hr0 _
  have hsmall : r ^ (ε / 2) < K := by
    have : r ^ (1 + ε / 2) * r ^ (ε / 2) < r ^ (1 + ε / 2) * K := by
      calc r ^ (1 + ε / 2) * r ^ (ε / 2) = r ^ (1 + ε) := hsplit.symm
        _ < c := hex
        _ ≤ K * r ^ (1 + ε / 2) := hle
        _ = r ^ (1 + ε / 2) * K := mul_comm _ _
    exact lt_of_mul_lt_mul_left this hpos.le
  have hrK : r ≤ K ^ (2 / ε) := by
    have hexp : r = (r ^ (ε / 2)) ^ (2 / ε) := by
      rw [← Real.rpow_mul hr0.le]
      have : ε / 2 * (2 / ε) = 1 := by field_simp
      rw [this, Real.rpow_one]
    rw [hexp]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hr0.le _) hsmall.le (by positivity)
  have hcB : (c : ℝ) ≤ B := by
    rw [hB]
    calc (c : ℝ) ≤ K * r ^ (1 + ε / 2) := hle
      _ ≤ K * (K ^ (2 / ε)) ^ (1 + ε / 2) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr0.le hrK (by linarith)) hK.le
  have hcN : c ≤ ⌊B⌋₊ := Nat.le_floor hcB
  rw [Set.mem_Iic, Prod.mk_le_mk, Prod.mk_le_mk]
  exact ⟨by omega, by omega, hcN⟩

theorem abc_iff_abcFinite : ABC ↔ ABCFinite := ⟨abcFinite_of_abc, abc_of_abcFinite⟩

/-- The set of triples the conjecture quantifies over is not empty: `1 + 1 = 2`. So no
formulation above is true for the empty reason that nothing satisfies its hypotheses. -/
theorem hypotheses_nonvacuous :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ Nat.Coprime a b ∧ a + b = c :=
  ⟨1, 1, 2, by decide, by decide, by decide, by decide, rfl⟩

end IUT.ABC
