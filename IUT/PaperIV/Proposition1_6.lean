import Mathlib

/-!
# IUT IV, Proposition 1.6: the consequence of the prime number theorem defining `η_prm`

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Proposition 1.6 and its proof,
page 16 of the April 2020 manuscript. Page 16 was read from the extracted text and from the
rendered page; both displays below were checked against the render.

The paper writes `p_n` for the `n`-th smallest prime (so `p_1 = 2`, `p_2 = 3`) and states:

* there is an integer `n₀` with `n ≤ 4·p_n / (3·log(p_n))` for all `n ≥ n₀`;
* "in particular" there is a positive real `η_prm` with
  `∑_{p ≤ η} 1 ≤ 4·η / (3·log(η))` for all real `η ≥ η_prm`, the sum over primes `p ≤ η`.

The paper derives the first display from the prime number theorem, cited as [DmMn], §3.10,
and says the second "follows formally".

What is proved here, unconditionally: both displays, from Mathlib's prime number theorem
`Nat.isEquivalent_primeCounting` (`π(x) ~ x / log x`). We also check the paper's step "the
final portion follows formally", that is, the second display follows from the first one alone
(`counting_of_nth`).

## Conventions

* `∑_{p ≤ η} 1` is `Nat.primeCounting ⌊η⌋₊`, the number of primes `≤ ⌊η⌋`, which is the
  number of primes `≤ η`.
* The paper's `p_n` is `Nat.nth Nat.Prime (n - 1)`, since Mathlib's `Nat.nth` is 0-indexed.
* We produce `η_prm ≥ 2`, which is stronger than the paper's "positive". Nothing later needs
  more than positivity: Step (viii) of the proof of Theorem 1.10 divides by `log(η_prm)` only in
  the case `1 < e*_mod·l < η_prm`, where `log(η_prm) > 0` already holds (page 31; see
  `IUT.PaperIV.Theorem1_10.StepVIII`).
* `proposition1_6` states both displays together, as the proposition does.
-/

open Filter Asymptotics

namespace IUT.PaperIV.Proposition1_6

/-- The paper's `p_n`, the `n`-th smallest prime for `n ≥ 1`: `p 1 = 2`, `p 2 = 3`. -/
noncomputable def p (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

theorem p_one : p 1 = 2 := by simp [p, Nat.nth_prime_zero_eq_two]

/-- `π(p_n) = n` for `n ≥ 1`. -/
theorem primeCounting_p {n : ℕ} (hn : 1 ≤ n) : Nat.primeCounting (p n) = n := by
  have hpr : (Nat.nth Nat.Prime (n - 1)).Prime := Nat.prime_nth_prime (n - 1)
  rw [p, Nat.primeCounting, Nat.primeCounting', Nat.count_succ]
  simp only [hpr, ite_true]
  rw [show Nat.count Nat.Prime (Nat.nth Nat.Prime (n - 1)) = n - 1 from
    Nat.primeCounting'_nth_eq (n - 1)]
  omega

/-- **Proposition 1.6, second display** (unconditional). There is a real `η_prm ≥ 2` such that
for every real `η ≥ η_prm` the number of primes `p ≤ η` is at most `4·η / (3·log(η))`. -/
theorem exists_eta_prm :
    ∃ ηprm : ℝ, 2 ≤ ηprm ∧ ∀ η : ℝ, ηprm ≤ η →
      (Nat.primeCounting ⌊η⌋₊ : ℝ) ≤ 4 * η / (3 * Real.log η) := by
  have h := (Nat.isEquivalent_primeCounting).def (c := 1 / 3) (by norm_num)
  obtain ⟨a, ha⟩ := eventually_atTop.mp (h.and (eventually_ge_atTop (2 : ℝ)))
  refine ⟨max a 2, le_max_right _ _, fun η hη => ?_⟩
  obtain ⟨hb, h2⟩ := ha η (le_trans (le_max_left _ _) hη)
  have hlog : 0 < Real.log η := Real.log_pos (by linarith)
  have hv : 0 ≤ η / Real.log η := div_nonneg (by linarith) hlog.le
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg hv] at hb
  have := (abs_le.mp hb).2
  have e : 4 * η / (3 * Real.log η) = η / Real.log η + 1 / 3 * (η / Real.log η) := by
    field_simp; ring
  rw [e]; linarith

/-- **Proposition 1.6, first display** (unconditional). There is an `n₀` such that
`n ≤ 4·p_n / (3·log(p_n))` for every `n ≥ n₀`. We include `1 ≤ n` among the conclusions'
hypotheses because `p_n` is only defined by the paper for positive `n`. -/
theorem exists_n0 :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 1 ≤ n →
      (n : ℝ) ≤ 4 * (p n : ℝ) / (3 * Real.log (p n)) := by
  obtain ⟨ηprm, -, h⟩ := exists_eta_prm
  refine ⟨⌈ηprm⌉₊, fun n hn h1 => ?_⟩
  have hge : n + 1 ≤ p n := by
    have := Nat.add_two_le_nth_prime (n - 1); simp only [p]; omega
  have hη : ηprm ≤ (p n : ℝ) := by
    have : (⌈ηprm⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    have h2 : ((n : ℕ) : ℝ) + 1 ≤ (p n : ℝ) := by exact_mod_cast hge
    linarith [Nat.le_ceil ηprm]
  have := h (p n) hη
  rwa [Nat.floor_natCast, primeCounting_p h1] at this

/-- **Proposition 1.6** (both displays, unconditional): there is an `n₀` with
`n ≤ 4·p_n / (3·log(p_n))` for all `n ≥ n₀` (`n ≥ 1`), and there is a real `η_prm > 0`
(in fact `≥ 2`) with `∑_{p ≤ η} 1 ≤ 4·η / (3·log(η))` for all real `η ≥ η_prm`. -/
theorem proposition1_6 :
    (∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 1 ≤ n →
      (n : ℝ) ≤ 4 * (p n : ℝ) / (3 * Real.log (p n))) ∧
    ∃ ηprm : ℝ, 0 < ηprm ∧ 2 ≤ ηprm ∧ ∀ η : ℝ, ηprm ≤ η →
      (Nat.primeCounting ⌊η⌋₊ : ℝ) ≤ 4 * η / (3 * Real.log η) := by
  obtain ⟨η, h2, h⟩ := exists_eta_prm
  exact ⟨exists_n0, η, by linarith, h2, h⟩

/-- The function `x / log x` is monotone on `[e, ∞)`. -/
theorem div_log_monotoneOn {x y : ℝ} (hx : Real.exp 1 ≤ x) (hxy : x ≤ y) :
    x / Real.log x ≤ y / Real.log y := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hlx : 1 ≤ Real.log x := by rwa [Real.le_log_iff_exp_le hx0]
  have hly : 1 ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le hy0]; exact hx.trans hxy
  have := Real.log_div_self_antitoneOn (Set.mem_Ici.mpr hx)
    (Set.mem_Ici.mpr (hx.trans hxy)) hxy
  simp only at this
  rw [div_le_div_iff₀ hy0 hx0] at this
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  linarith

/-- **"The final portion of Proposition 1.6 follows formally."** The second display follows
from the first one, with no further input from analytic number theory. -/
theorem counting_of_nth
    (h : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 1 ≤ n →
      (n : ℝ) ≤ 4 * (p n : ℝ) / (3 * Real.log (p n))) :
    ∃ ηprm : ℝ, 0 < ηprm ∧ ∀ η : ℝ, ηprm ≤ η →
      (Nat.primeCounting ⌊η⌋₊ : ℝ) ≤ 4 * η / (3 * Real.log η) := by
  obtain ⟨n₀, hn₀⟩ := h
  set m := max n₀ 2 with hm
  refine ⟨(p m : ℝ), ?_, fun η hη => ?_⟩
  · have : 0 < p m := by have := Nat.add_two_le_nth_prime (m - 1); simp only [p]; omega
    exact_mod_cast this
  have hpm : m + 1 ≤ p m := by have := Nat.add_two_le_nth_prime (m - 1); simp only [p]; omega
  have hm2 : 2 ≤ m := le_max_right _ _
  have hη0 : 0 ≤ η := le_trans (by positivity) hη
  -- `n = π(⌊η⌋) ≥ π(p_m) = m`.
  set n := Nat.primeCounting ⌊η⌋₊ with hn
  have hfl : p m ≤ ⌊η⌋₊ := Nat.le_floor hη
  have hnm : m ≤ n := by
    rw [← primeCounting_p (by omega : 1 ≤ m)]; exact Nat.monotone_primeCounting hfl
  have hn1 : 1 ≤ n := by omega
  -- `p_n ≤ η`.
  have hpn : p n ≤ ⌊η⌋₊ := by
    have hlt : n - 1 < Nat.count Nat.Prime (⌊η⌋₊ + 1) := by
      rw [← Nat.primeCounting', ← Nat.primeCounting]; omega
    have := Nat.nth_lt_of_lt_count hlt
    simp only [p]; omega
  have hpnη : (p n : ℝ) ≤ η := le_trans (by exact_mod_cast hpn) (Nat.floor_le hη0)
  -- `p_n ≥ 3 > e`.
  have hp3 : (3 : ℝ) ≤ p n := by
    have := Nat.add_two_le_nth_prime (n - 1); simp only [p]
    have : 3 ≤ Nat.nth Nat.Prime (n - 1) := by omega
    exact_mod_cast this
  have he : Real.exp 1 ≤ (p n : ℝ) := by
    have := Real.exp_one_lt_d9; linarith
  have key := hn₀ n (le_trans (le_max_left _ _) hnm) hn1
  have hmono := div_log_monotoneOn he hpnη
  have hlp : 0 < Real.log (p n : ℝ) := Real.log_pos (by linarith)
  have hlη : 0 < Real.log η := Real.log_pos (by linarith)
  have e1 : 4 * (p n : ℝ) / (3 * Real.log (p n)) = 4 / 3 * ((p n : ℝ) / Real.log (p n)) := by
    field_simp
  have e2 : 4 * η / (3 * Real.log η) = 4 / 3 * (η / Real.log η) := by field_simp
  rw [e2]; rw [e1] at key; linarith

end IUT.PaperIV.Proposition1_6
