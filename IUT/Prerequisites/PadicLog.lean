import Mathlib

/-!
# The p-adic logarithm on `ℚ_p` and the log-shell of `ℚ_p`

Sources:
* Mochizuki, *Inter-universal Teichmüller Theory III*, Definition 1.1, PDF pages 23 and 24
  (rendered and read): for a nonarchimedean `v`, the pre-log-shell is the image under the
  `p_v`-adic logarithm of the Galois-invariant units, and the log-shell is the pre-log-shell
  multiplied by `(p_v^*)⁻¹`, with `p_v^* = p_v` for odd `p_v` and `p_v^* = p_v ^ 2` for `p_v = 2`
  (page 24, citing [AbsTopIII], Definition 5.4 (iii)).
* Mochizuki, *Inter-universal Teichmüller Theory III*, Proposition 1.2 (v), PDF pages 31 and 32
  (rendered and read): at nonarchimedean `v` the log-shell is compact, contains the invariants of
  the integers of the codomain, and contains the image of the invariant units.
* Mochizuki, *Inter-universal Teichmüller Theory IV*, Proposition 1.2 (i), PDF pages 10 and 11
  (rendered and read; page 9, read, fixes the notation `R_i`, `ord`, `p ^ λ` of Proposition 1.1
  used there): for a finite extension `k_i` of `ℚ_p` with ramification index `e_i`,
  `p ^ (a_i) R_i ⊆ log_p (R_i^×) ⊆ p ^ (- b_i) R_i`, with equalities when `p > 2` and
  `e_i ≤ p - 2`; the proof cites [Kobl], page 81.

Pages read for this file: IUT III pages 23, 24, 31 and 32; IUT IV pages 9, 10 and 11. Pages
checked against rendered images: the same.

This file is a prerequisite for log-shells over `ℚ_p` only. Finite extensions of `ℚ_p`, tensor
products of rings of integers, and the Frobenioid-theoretic setting of IUT III are not treated
here; the logarithm on a finite extension of `ℚ_p` is in
`IUT/PaperIV/LocalFields/Logarithm.lean`.
It does not formalize IUT III Definition 1.1, IUT III Proposition 1.2 or IUT IV Proposition 1.2;
it proves, for the base field `k = ℚ_p` (so `e = 1`, `R = ℤ_p`), the facts about the logarithm on
which they rest.

## Contents

* `padicLogOnePlus p x = ∑_{n ≥ 1} (-1) ^ (n + 1) x ^ n / n`, which agrees with Mathlib's
  `NormedSpace.log (1 + x)` (`padicLogOnePlus_eq_normedSpace_log`) and converges for `‖x‖ < 1`
  (`padicLogSeries_summable`). Outside the open unit disc the value is a junk value.
* `‖log (1 + x)‖ = ‖x‖` for `‖x‖ ≤ 1 / p*` (`padicLogOnePlus_norm_eq`), that is `‖x‖ ≤ 1 / p` for
  odd `p` and `‖x‖ ≤ 1 / 4` for `p = 2`.
* The homomorphism property `log ((1 + x) (1 + y)) = log (1 + x) + log (1 + y)` on the whole open
  unit disc (`padicLogOnePlus_add_add_mul`), proved by re-expanding the series around `x` as a
  norm-summable double series and summing it in both orders.
* The logarithm of a unit, `padicLogUnit p u = (p - 1)⁻¹ log (u ^ (p - 1))`, which agrees with
  `log u` on `1 + p ℤ_p` (`padicLogUnit_one_add`), and its image
  `log (ℤ_p^×) = {z | ‖z‖ ≤ 1 / p*}` (`padicLogUnit_range`), that is `p ℤ_p` for odd `p` and
  `4 ℤ_2` for `p = 2`. Surjectivity is proved by the contraction mapping principle.
* The log-shell `padicLogShell p = (p*)⁻¹ · log (ℤ_p^×)` and its computation
  `padicLogShell p = ℤ_p` (`padicLogShell_eq_range_coe`), with the three properties of
  IUT III Proposition 1.2 (v) at nonarchimedean `v` in this case: compactness
  (`padicLogShell_isCompact`), `ℤ_p ⊆ I` (`padicInt_subset_padicLogShell`) and
  `log (ℤ_p^×) ⊆ I` (`padicLogUnit_range_subset_padicLogShell`).

## Interpretation choices, recorded

* The "Galois-invariant units" of IUT III page 24 are taken to be `ℤ_p^×` for the base field
  `ℚ_p` (the invariants of the units of the ring of integers of an algebraic closure under the
  absolute Galois group of `ℚ_p`); this identification is not formalized here.
* The papers write `log_p` without fixing the extension to all units on the pages read. The
  extension `(p - 1)⁻¹ log (u ^ (p - 1))` used here is the standard one; for `p = 2` it is
  `log u` itself. Since `log` is a homomorphism on `1 + p ℤ_p` (`padicLogOnePlus_add_add_mul`),
  this extension is a homomorphism on `ℤ_p^×` (`padicLogUnit_mul`), and it is the unique
  homomorphic extension into the torsion-free group `ℚ_p`; that uniqueness statement is not
  formalized here.
* For `k = ℚ_p`, the constants of IUT IV Proposition 1.2 are `a = 1`, `b = -1` for `p > 2` and
  `a = 2`, `b = 0` for `p = 2` (computed from the displays on page 10). The theorem
  `padicLogUnit_range` gives the equality `log (ℤ_p^×) = p ℤ_p` asserted there for `p > 2` and,
  for `p = 2`, the sharper `log (ℤ_2^×) = 4 ℤ_2`, which implies the two inclusions
  `4 ℤ_2 ⊆ log (ℤ_2^×) ⊆ ℤ_2`.
* Some secondary sources write the log-shell as `(2p)⁻¹ log (O_k^×)`. For `p = 2` this is
  `(p*)⁻¹`; for odd `p`, `2p` and `p* = p` differ by the unit `2`, so the set is the same. Only the
  `(p*)⁻¹` form of page 24 is defined; `padicLogShell_eq_two_mul` proves the two forms equal.
-/

namespace IUT.Prerequisites.PadicLog

variable {p : ℕ} [hp : Fact p.Prime]

/-- The `n`-th term `(-1) ^ (n + 1) x ^ n / n` of the logarithm series; the `0`-th term is `0`
because `1 / 0 = 0`. -/
noncomputable def padicLogSeries (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) (n : ℕ) : ℚ_[p] :=
  (-1) ^ (n + 1) / n * x ^ n

/-- `log (1 + x) = ∑_{n ≥ 1} (-1) ^ (n + 1) x ^ n / n`; meaningful for `‖x‖ < 1`, where the series
converges (`padicLogSeries_summable`), and a junk value otherwise. -/
noncomputable def padicLogOnePlus (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) : ℚ_[p] :=
  ∑' n : ℕ, padicLogSeries p x n

/-- Agreement with Mathlib's `NormedSpace.log`. -/
theorem padicLogOnePlus_eq_normedSpace_log (x : ℚ_[p]) :
    padicLogOnePlus p x = NormedSpace.log (1 + x) := by
  rw [NormedSpace.log_eq_tsum ℚ_[p]]
  simp [padicLogOnePlus, padicLogSeries, smul_eq_mul]

/-- For `n ≠ 0`, `‖1 / n‖ = p ^ e` for some `e` with `p ^ e ∣ n`. -/
theorem padicLog_exists_norm_inv_natCast {n : ℕ} (hn : n ≠ 0) :
    ∃ e : ℕ, p ^ e ∣ n ∧ ‖((n : ℚ_[p]))⁻¹‖ = (p : ℝ) ^ e := by
  obtain ⟨e, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.out.ne_one
  refine ⟨e, dvd_mul_right _ _, ?_⟩
  have hm : ‖(m : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpm)
  rw [norm_inv, Nat.cast_mul, norm_mul, hm, Nat.cast_pow, Padic.norm_p_pow]
  simp [zpow_neg]

/-- `‖1 / n‖ ≤ n` in `ℚ_p`. -/
theorem padicLog_norm_inv_natCast_le (n : ℕ) : ‖((n : ℚ_[p]))⁻¹‖ ≤ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  obtain ⟨e, hdvd, he⟩ := padicLog_exists_norm_inv_natCast (p := p) hn
  rw [he]
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd

/-- `‖x ^ n / n‖ ≤ n ‖x‖ ^ n`. -/
theorem padicLogSeries_norm_le (x : ℚ_[p]) (n : ℕ) :
    ‖padicLogSeries p x n‖ ≤ n * ‖x‖ ^ n := by
  rw [padicLogSeries, div_eq_mul_inv, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (padicLog_norm_inv_natCast_le n) (by positivity)

/-- The logarithm series converges on the open unit disc. -/
theorem padicLogSeries_summable {x : ℚ_[p]} (hx : ‖x‖ < 1) : Summable (padicLogSeries p x) := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => (n : ℝ) ^ 1 * ‖x‖ ^ n) ?_ ?_
  · exact summable_pow_mul_geometric_of_norm_lt_one 1 (by simpa using hx)
  · intro n; simpa using padicLogSeries_norm_le x n

/-- `log 1 = 0`. -/
theorem padicLogOnePlus_zero : padicLogOnePlus p 0 = 0 := by
  rw [padicLogOnePlus]
  convert tsum_zero with n
  rcases n with _ | n <;> simp [padicLogSeries]

/-- `p*` of IUT III page 24: `p` for odd `p` and `p ^ 2 = 4` for `p = 2`. -/
def padicLogPStar (p : ℕ) : ℕ := if p = 2 then p ^ 2 else p

/-- An elementary inequality: `m + 2 < 3 ^ (m + 1)`. -/
theorem padicLog_aux_lt_three_pow (m : ℕ) : m + 2 < 3 ^ (m + 1) := by
  induction m with
  | zero => norm_num
  | succ m ih => rw [pow_succ]; omega

/-- Key arithmetic: for `n ≥ 2` and `p ^ e ∣ n`, `p ^ e * p ≤ (p*) ^ (n - 1)`. -/
theorem padicLog_pow_mul_le_pStar_pow {n e : ℕ} (hn : 2 ≤ n) (hdvd : p ^ e ∣ n) :
    p ^ e * p ≤ padicLogPStar p ^ (n - 1) := by
  have h2 := hp.out.two_le
  have hle : p ^ e ≤ n := Nat.le_of_dvd (by omega) hdvd
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h3 := padicLog_aux_lt_three_pow m
  simp only [padicLogPStar, show m + 2 - 1 = m + 1 by omega]
  split_ifs with h
  · subst h
    rw [← pow_succ, ← pow_mul]
    apply Nat.pow_le_pow_right (by norm_num)
    by_contra hc
    have : 2 ^ (2 * (m + 1)) ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 3 ^ (m + 1) ≤ 2 ^ (2 * (m + 1)) := by
      rw [pow_mul]; exact Nat.pow_le_pow_left (by norm_num) _
    omega
  · rw [← pow_succ]
    apply Nat.pow_le_pow_right (by omega)
    by_contra hc
    have : p ^ (m + 1) ≤ p ^ e := Nat.pow_le_pow_right (by omega) (by omega)
    have h4 : 3 ^ (m + 1) ≤ p ^ (m + 1) := by
      have : p ≠ 2 := h
      exact Nat.pow_le_pow_left (by
        rcases hp.out.eq_two_or_odd' with h' | h'
        · exact absurd h' h
        · obtain ⟨k, hk⟩ := h'; omega) _
    omega

/-- For `n ≥ 2` and `‖x‖ ≤ 1 / p*`, the `n`-th term has norm at most `‖x‖ / p`. -/
theorem padicLogSeries_norm_le_of_two_le {x : ℚ_[p]} (hx : ‖x‖ ≤ (padicLogPStar p : ℝ)⁻¹)
    {n : ℕ} (hn : 2 ≤ n) : ‖padicLogSeries p x n‖ ≤ ‖x‖ / p := by
  obtain ⟨e, hdvd, he⟩ := padicLog_exists_norm_inv_natCast (p := p) (n := n) (by omega)
  have hkey : ((p : ℝ) ^ e * p) ≤ (padicLogPStar p : ℝ) ^ (n - 1) := by
    exact_mod_cast padicLog_pow_mul_le_pStar_pow hn hdvd
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hs0 : (0 : ℝ) < padicLogPStar p := by
    unfold padicLogPStar; split_ifs <;> positivity
  rw [padicLogSeries, div_eq_mul_inv, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, norm_pow, he]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hkey
  have hxm : ‖x‖ ^ m ≤ ((padicLogPStar p : ℝ)⁻¹) ^ m := pow_le_pow_left₀ (norm_nonneg _) hx m
  rw [le_div_iff₀ hp0, pow_succ]
  calc (p : ℝ) ^ e * (‖x‖ ^ m * ‖x‖) * p = ‖x‖ * (‖x‖ ^ m * ((p : ℝ) ^ e * p)) := by ring
    _ ≤ ‖x‖ * (((padicLogPStar p : ℝ)⁻¹) ^ m * (padicLogPStar p : ℝ) ^ m) := by
        gcongr
    _ = ‖x‖ := by rw [← mul_pow, inv_mul_cancel₀ hs0.ne', one_pow, mul_one]

/-- `log (1 + x) = x + ∑_{n ≥ 2} (-1) ^ (n + 1) x ^ n / n` for `‖x‖ < 1`. -/
theorem padicLogOnePlus_eq_add_tail {x : ℚ_[p]} (hx : ‖x‖ < 1) :
    padicLogOnePlus p x = x + ∑' n : ℕ, padicLogSeries p x (n + 2) := by
  rw [padicLogOnePlus, ← (padicLogSeries_summable hx).sum_add_tsum_nat_add 2]
  simp [Finset.sum_range_succ, padicLogSeries]

/-- `‖log (1 + x)‖ = ‖x‖` for `‖x‖ ≤ 1 / p*`. -/
theorem padicLogOnePlus_norm_eq {x : ℚ_[p]} (hx : ‖x‖ ≤ (padicLogPStar p : ℝ)⁻¹) :
    ‖padicLogOnePlus p x‖ = ‖x‖ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hs1 : (1 : ℝ) < padicLogPStar p := by
    unfold padicLogPStar; split_ifs <;> push_cast <;> nlinarith
  have hx1 : ‖x‖ < 1 := hx.trans_lt (inv_lt_one_of_one_lt₀ hs1)
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [padicLogOnePlus_zero]
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have htail : ‖∑' n : ℕ, padicLogSeries p x (n + 2)‖ ≤ ‖x‖ / p :=
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity)
      fun n => padicLogSeries_norm_le_of_two_le hx (by omega)
  have hlt : ‖∑' n : ℕ, padicLogSeries p x (n + 2)‖ < ‖x‖ :=
    htail.trans_lt (div_lt_self hpos hp1)
  rw [padicLogOnePlus_eq_add_tail hx1, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne',
    max_eq_left hlt.le]


/-- The double family used to re-expand `log (1 + x + w)` around `x`. -/
noncomputable def padicLogDouble (p : ℕ) [Fact p.Prime] (x w : ℚ_[p]) (nk : ℕ × ℕ) : ℚ_[p] :=
  (-1) ^ (nk.1 + 1) / nk.1 * (nk.1.choose nk.2) * x ^ (nk.1 - nk.2) * w ^ nk.2

/-- The double family is norm-summable for `‖x‖, ‖w‖ < 1`. -/
theorem padicLogDouble_summable {x w : ℚ_[p]} (hx : ‖x‖ < 1) (hw : ‖w‖ < 1) :
    Summable (padicLogDouble p x w) := by
  set r := max ‖x‖ ‖w‖
  have hr0 : 0 ≤ r := le_max_of_le_left (norm_nonneg _)
  have hr1 : r < 1 := max_lt hx hw
  set s := Real.sqrt r
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s < 1 := (Real.sqrt_lt' one_pos).mpr (by simpa using hr1)
  have hss : s * s = r := Real.mul_self_sqrt hr0
  refine Summable.of_norm_bounded
    (g := fun nk : ℕ × ℕ => ((nk.1 : ℝ) ^ 1 * s ^ nk.1) * s ^ nk.2) ?_ ?_
  · refine Summable.mul_of_nonneg (f := fun n : ℕ => (n : ℝ) ^ 1 * s ^ n) (g := fun k => s ^ k)
      (summable_pow_mul_geometric_of_norm_lt_one 1 (by rwa [Real.norm_of_nonneg hs0]))
      (summable_geometric_of_lt_one hs0 hs1) (fun n => by positivity) (fun k => by positivity)
  · rintro ⟨n, k⟩
    simp only [padicLogDouble, pow_one]
    rcases lt_or_ge n k with hnk | hkn
    · simp [Nat.choose_eq_zero_of_lt hnk]; positivity
    rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, norm_one,
      one_pow, one_mul, norm_pow, norm_pow]
    have hc : ‖((n.choose k : ℕ) : ℚ_[p])‖ ≤ 1 := by
      simpa using Padic.norm_int_le_one (p := p) (n.choose k : ℤ)
    have h1 : ‖x‖ ^ (n - k) * ‖w‖ ^ k ≤ s ^ n * s ^ k := by
      have : ‖x‖ ^ (n - k) * ‖w‖ ^ k ≤ r ^ (n - k) * r ^ k := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
      calc ‖x‖ ^ (n - k) * ‖w‖ ^ k ≤ r ^ (n - k) * r ^ k := this
        _ = r ^ n := by rw [← pow_add, Nat.sub_add_cancel hkn]
        _ = s ^ n * s ^ n := by rw [← mul_pow, hss]
        _ ≤ s ^ n * s ^ k :=
            mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hs0 hs1.le hkn) (by positivity)
    calc ‖((n : ℚ_[p]))⁻¹‖ * ‖((n.choose k : ℕ) : ℚ_[p])‖ * ‖x‖ ^ (n - k) * ‖w‖ ^ k
        ≤ n * 1 * (‖x‖ ^ (n - k) * ‖w‖ ^ k) := by
          rw [mul_assoc _ (‖x‖ ^ _)]
          gcongr
          exact padicLog_norm_inv_natCast_le n
      _ ≤ n * 1 * (s ^ n * s ^ k) := by gcongr
      _ = n * s ^ n * s ^ k := by ring

/-- Summing the double family over `k` first gives the series of `log (1 + (x + w))`. -/
theorem padicLogDouble_hasSum_fst (x w : ℚ_[p]) (n : ℕ) :
    HasSum (fun k => padicLogDouble p x w (n, k)) (padicLogSeries p (x + w) n) := by
  have hzero : ∀ k ∉ Finset.range (n + 1), padicLogDouble p x w (n, k) = 0 := by
    intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    simp [padicLogDouble, Nat.choose_eq_zero_of_lt (by omega : n < k)]
  convert hasSum_sum_of_ne_finset_zero hzero using 1
  swap; · infer_instance
  rw [padicLogSeries, add_comm x w, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [padicLogDouble]
  ring

/-- Summing the double family over `n` first, for fixed `k ≥ 1`. -/
theorem padicLogDouble_hasSum_snd_succ {x : ℚ_[p]} (hx : ‖x‖ < 1) (w : ℚ_[p]) (j : ℕ) :
    HasSum (fun n => padicLogDouble p x w (n, j + 1))
      ((-1) ^ (j + 2) / (j + 1 : ℕ) * (w / (1 + x)) ^ (j + 1)) := by
  have hx' : ‖-x‖ < 1 := by rwa [norm_neg]
  have h1x : (1 + x) ≠ 0 := by
    intro h
    have : x = -1 := by linear_combination h
    rw [this, norm_neg, norm_one] at hx
    exact lt_irrefl _ hx
  have hgeom := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℚ_[p]) j hx').mul_left
    ((-1) ^ j / (j + 1 : ℕ) * w ^ (j + 1))
  rw [← hasSum_nat_add_iff' (j + 1)]
  have hlow : ∑ i ∈ Finset.range (j + 1), padicLogDouble p x w (i, j + 1) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    simp only [Finset.mem_range] at hi
    simp [padicLogDouble, Nat.choose_eq_zero_of_lt hi]
  rw [hlow, sub_zero]
  convert hgeom using 1
  · funext m
    simp only [padicLogDouble]
    have hc : ((m + (j + 1)).choose (j + 1) : ℚ_[p]) * (j + 1 : ℕ) =
        (m + j + 1 : ℕ) * ((m + j).choose j : ℕ) := by
      have := Nat.add_one_mul_choose_eq (m + j) j
      rw [show m + (j + 1) = m + j + 1 by omega]
      exact_mod_cast this.symm
    have hj : ((j + 1 : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    have hmj : ((m + (j + 1) : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (by omega : m + (j + 1) ≠ 0)
    rw [show m + (j + 1) - (j + 1) = m by omega]
    field_simp
    rw [show ((m + (j + 1) : ℕ) : ℚ_[p]) = ((m + j + 1 : ℕ) : ℚ_[p]) by push_cast; ring] at hmj ⊢
    rw [show (-1 : ℚ_[p]) ^ (m + (j + 1) + 1) * ((m + (j + 1)).choose (j + 1) : ℕ) * x ^ m *
        w ^ (j + 1) * ((j + 1 : ℕ) : ℚ_[p]) = (-1) ^ (m + j) * x ^ m * w ^ (j + 1) *
        ((((m + (j + 1)).choose (j + 1) : ℕ) : ℚ_[p]) * ((j + 1 : ℕ) : ℚ_[p])) by ring, hc]
    ring
  · rw [sub_neg_eq_add, div_pow]
    field_simp
    ring


/-- `‖1 + x‖ = 1` for `‖x‖ < 1`. -/
theorem padicLog_norm_one_add {x : ℚ_[p]} (hx : ‖x‖ < 1) : ‖1 + x‖ = 1 := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hx.ne'),
    norm_one, max_eq_left hx.le]

/-- **Homomorphism property** on the open unit disc:
`log ((1 + x) (1 + y)) = log (1 + x) + log (1 + y)` for `‖x‖, ‖y‖ < 1`. -/
theorem padicLogOnePlus_add_add_mul {x y : ℚ_[p]} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    padicLogOnePlus p (x + y + x * y) = padicLogOnePlus p x + padicLogOnePlus p y := by
  set w := (1 + x) * y with hwdef
  have h1x := padicLog_norm_one_add hx
  have hw : ‖w‖ < 1 := by rw [hwdef, norm_mul, h1x, one_mul]; exact hy
  have hxw : x + y + x * y = x + w := by rw [hwdef]; ring
  have hS := (padicLogDouble_summable hx hw).hasSum
  have hfst : HasSum (padicLogSeries p (x + w)) (∑' nk, padicLogDouble p x w nk) :=
    hS.prod_fiberwise (padicLogDouble_hasSum_fst x w)
  have hswap := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hS
  have h1x0 : (1 + x) ≠ 0 := by
    intro h; rw [h, norm_zero] at h1x; exact zero_ne_one h1x
  have hsnd : HasSum (fun k => padicLogSeries p y k + if k = 0 then padicLogOnePlus p x else 0)
      (∑' nk, padicLogDouble p x w nk) := by
    refine hswap.prod_fiberwise fun k => ?_
    rcases k with _ | j
    · simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, ite_true]
      have : padicLogSeries p y 0 = 0 := by simp [padicLogSeries]
      rw [this, zero_add, padicLogOnePlus]
      convert (padicLogSeries_summable hx).hasSum using 1
      funext n
      simp [padicLogDouble, padicLogSeries]
    · simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.swap_prod_mk,
        show j + 1 ≠ 0 from Nat.succ_ne_zero j, ite_false, add_zero]
      convert padicLogDouble_hasSum_snd_succ (p := p) hx w j using 1
      rw [hwdef, mul_div_cancel_left₀ _ h1x0, padicLogSeries]
  have hsnd' : HasSum (fun k => padicLogSeries p y k + if k = 0 then padicLogOnePlus p x else 0)
      (padicLogOnePlus p y + padicLogOnePlus p x) :=
    (padicLogSeries_summable hy).hasSum.add (hasSum_ite_eq 0 _)
  rw [hxw, padicLogOnePlus, hfst.tsum_eq, hsnd.unique hsnd', add_comm]


/-- The ultrametric inequality for a difference. -/
theorem padicLog_norm_sub_le_max (u v : ℚ_[p]) : ‖u - v‖ ≤ max ‖u‖ ‖v‖ := by
  simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max u (-v)

/-- `p ≤ p*`. -/
theorem padicLog_pStar_ge : p ≤ padicLogPStar p := by
  unfold padicLogPStar; split_ifs with h
  · subst h; norm_num
  · exact le_rfl

/-- `1 / p* ≤ 1 / p`. -/
theorem padicLog_inv_pStar_le_inv_p : ((padicLogPStar p : ℕ) : ℝ)⁻¹ ≤ (p : ℝ)⁻¹ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  exact inv_anti₀ hp0 (by exact_mod_cast padicLog_pStar_ge)

/-- `1 / p* < 1`. -/
theorem padicLog_inv_pStar_lt_one : ((padicLogPStar p : ℕ) : ℝ)⁻¹ < 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  exact padicLog_inv_pStar_le_inv_p.trans_lt (inv_lt_one_of_one_lt₀ hp1)

/-- Key contraction estimate: for `a, b` in the closed ball of radius `1 / p*`,
`‖(a - b) - (log (1 + a) - log (1 + b))‖ ≤ ‖a - b‖ / p`. -/
theorem padicLogOnePlus_sub_sub_norm_le {a b : ℚ_[p]} (ha : ‖a‖ ≤ (padicLogPStar p : ℝ)⁻¹)
    (hb : ‖b‖ ≤ (padicLogPStar p : ℝ)⁻¹) :
    ‖(a - b) - (padicLogOnePlus p a - padicLogOnePlus p b)‖ ≤ ‖a - b‖ / p := by
  have hρ := padicLog_inv_pStar_lt_one (p := p)
  have hb1 : ‖b‖ < 1 := hb.trans_lt hρ
  have h1b := padicLog_norm_one_add hb1
  have h1b0 : (1 + b) ≠ 0 := by intro h; rw [h, norm_zero] at h1b; exact zero_ne_one h1b
  set c := (a - b) / (1 + b) with hcdef
  have hc : ‖c‖ = ‖a - b‖ := by rw [hcdef, norm_div, h1b, div_one]
  have hcρ : ‖c‖ ≤ (padicLogPStar p : ℝ)⁻¹ := by
    rw [hc]
    refine (padicLog_norm_sub_le_max a b).trans (max_le ha hb)
  have hc1 : ‖c‖ < 1 := hcρ.trans_lt hρ
  have habc : b + c + b * c = a := by rw [hcdef]; field_simp; ring
  have hL : padicLogOnePlus p a - padicLogOnePlus p b = padicLogOnePlus p c := by
    rw [← habc, padicLogOnePlus_add_add_mul hb1 hc1]; ring
  have hab : a - b = c + c * b := by rw [hcdef]; field_simp
  have htail : ‖∑' n : ℕ, padicLogSeries p c (n + 2)‖ ≤ ‖c‖ / p :=
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity)
      fun n => padicLogSeries_norm_le_of_two_le hcρ (by omega)
  have hcb : ‖c * b‖ ≤ ‖c‖ / p := by
    rw [norm_mul, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (hb.trans padicLog_inv_pStar_le_inv_p) (norm_nonneg _)
  rw [hL, padicLogOnePlus_eq_add_tail hc1, ← hc, hab,
    show c + c * b - (c + ∑' n : ℕ, padicLogSeries p c (n + 2)) =
      c * b - ∑' n : ℕ, padicLogSeries p c (n + 2) by ring]
  exact (padicLog_norm_sub_le_max _ _).trans (max_le hcb htail)

/-- Surjectivity of `x ↦ log (1 + x)` onto the closed ball of radius `1 / p*`. -/
theorem padicLogOnePlus_surjOn {z : ℚ_[p]} (hz : ‖z‖ ≤ (padicLogPStar p : ℝ)⁻¹) :
    ∃ x : ℚ_[p], ‖x‖ ≤ (padicLogPStar p : ℝ)⁻¹ ∧ padicLogOnePlus p x = z := by
  set ρ : ℝ := (padicLogPStar p : ℝ)⁻¹
  set B := Metric.closedBall (0 : ℚ_[p]) ρ
  have hρ1 : ρ < 1 := padicLog_inv_pStar_lt_one
  have hρ0 : 0 ≤ ρ := (norm_nonneg z).trans hz
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hmem : ∀ x : B, x.1 + (z - padicLogOnePlus p x.1) ∈ B := by
    intro ⟨x, hx⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    have hx1 : ‖x‖ < 1 := hx.trans_lt hρ1
    have htail : ‖∑' n : ℕ, padicLogSeries p x (n + 2)‖ ≤ ‖x‖ / p :=
      IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity)
        fun n => padicLogSeries_norm_le_of_two_le hx (by omega)
    rw [padicLogOnePlus_eq_add_tail hx1,
      show x + (z - (x + ∑' n : ℕ, padicLogSeries p x (n + 2))) =
        z - ∑' n : ℕ, padicLogSeries p x (n + 2) by ring]
    refine (padicLog_norm_sub_le_max _ _).trans (max_le hz (htail.trans ?_))
    exact (div_le_self (norm_nonneg _) hp1.le).trans hx
  let T : B → B := fun x => ⟨x.1 + (z - padicLogOnePlus p x.1), hmem x⟩
  have hT : ContractingWith (p : NNReal)⁻¹ T := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    · rw [inv_lt_one₀ (by exact_mod_cast hp.out.pos)]; exact_mod_cast hp.out.one_lt
    · rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
      have ha := a.2; have hb := b.2
      rw [Metric.mem_closedBall, dist_zero_right] at ha hb
      have := padicLogOnePlus_sub_sub_norm_le ha hb
      simp only [T]
      rw [show a.1 + (z - padicLogOnePlus p a.1) - (b.1 + (z - padicLogOnePlus p b.1)) =
        (a.1 - b.1) - (padicLogOnePlus p a.1 - padicLogOnePlus p b.1) by ring]
      push_cast
      rw [inv_mul_eq_div]
      exact this
  have : CompleteSpace B := Metric.isClosed_closedBall.completeSpace_coe
  have : Nonempty B := ⟨⟨0, Metric.mem_closedBall_self hρ0⟩⟩
  set x := ContractingWith.fixedPoint T hT
  have hfix : T x = x := ContractingWith.fixedPoint_isFixedPt hT
  have hx := x.2
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  refine ⟨x.1, hx, ?_⟩
  have := congrArg Subtype.val hfix
  simp only [T] at this
  linear_combination -this


/-- `log ((1 + x) ^ n) = n log (1 + x)` on the open unit disc. -/
theorem padicLogOnePlus_pow_sub_one {x : ℚ_[p]} (hx : ‖x‖ < 1) (n : ℕ) :
    ‖(1 + x) ^ n - 1‖ < 1 ∧ padicLogOnePlus p ((1 + x) ^ n - 1) = n * padicLogOnePlus p x := by
  induction n with
  | zero => simp [padicLogOnePlus_zero]
  | succ n ih =>
    obtain ⟨hy, hL⟩ := ih
    have he : (1 + x) ^ (n + 1) - 1 = ((1 + x) ^ n - 1) + x + ((1 + x) ^ n - 1) * x := by ring
    refine ⟨?_, ?_⟩
    · rw [he]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
      · exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hy hx)
      · rw [norm_mul]; exact (mul_le_of_le_one_right (norm_nonneg _) hx.le).trans_lt hy
    · rw [he, padicLogOnePlus_add_add_mul hy hx, hL]; push_cast; ring

/-- The p-adic logarithm of a unit `u` of `ℤ_p`, as `(p - 1)⁻¹ log (u ^ (p - 1))`, where `log` is
the series `padicLogOnePlus` at `u ^ (p - 1) - 1`. Meaningful for `‖u‖ = 1`. -/
noncomputable def padicLogUnit (p : ℕ) [Fact p.Prime] (u : ℚ_[p]) : ℚ_[p] :=
  ((p - 1 : ℕ) : ℚ_[p])⁻¹ * padicLogOnePlus p (u ^ (p - 1) - 1)

/-- On `1 + x` with `‖x‖ < 1`, the logarithm of units agrees with the series `log (1 + x)`. -/
theorem padicLogUnit_one_add {x : ℚ_[p]} (hx : ‖x‖ < 1) :
    padicLogUnit p (1 + x) = padicLogOnePlus p x := by
  have hne : ((p - 1 : ℕ) : ℚ_[p]) ≠ 0 := by
    have := hp.out.two_le; exact_mod_cast (by omega : p - 1 ≠ 0)
  rw [padicLogUnit, (padicLogOnePlus_pow_sub_one hx (p - 1)).2, ← mul_assoc, inv_mul_cancel₀ hne,
    one_mul]

/-- An element of `ℤ_p` with zero residue has norm at most `1 / p`. -/
theorem padicLog_norm_le_inv_of_toZMod_eq_zero {z : ℤ_[p]} (hz : PadicInt.toZMod z = 0) :
    ‖(z : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
  have hmem : z ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod]; exact hz
  have hlt : ‖z‖ < 1 := PadicInt.mem_nonunits.mp ((IsLocalRing.mem_maximalIdeal z).mp hmem)
  have := (PadicInt.norm_le_pow_iff_norm_lt_pow_add_one z (-1)).mpr (by simpa using hlt)
  rw [← PadicInt.norm_def]; simpa using this

/-- Fermat: `‖u ^ (p - 1) - 1‖ ≤ 1 / p` for `u ∈ ℤ_p^×`. -/
theorem padicLog_norm_pow_sub_one_le (u : ℤ_[p]ˣ) :
    ‖((u : ℤ_[p]) : ℚ_[p]) ^ (p - 1) - 1‖ ≤ (p : ℝ)⁻¹ := by
  have hu : PadicInt.toZMod (u : ℤ_[p]) ≠ 0 := ((u.isUnit).map PadicInt.toZMod).ne_zero
  have h := padicLog_norm_le_inv_of_toZMod_eq_zero (z := (u : ℤ_[p]) ^ (p - 1) - 1)
    (by rw [map_sub, map_pow, ZMod.pow_card_sub_one_eq_one hu, map_one, sub_self])
  simpa using h

/-- For `u ∈ ℤ_2^×`, `‖u ^ 2 - 1‖ ≤ 1 / 8`. -/
theorem padicLog_two_norm_sq_sub_one_le (u : ℤ_[2]ˣ) :
    ‖((u : ℤ_[2]) : ℚ_[2]) ^ 2 - 1‖ ≤ (8 : ℝ)⁻¹ := by
  have h1 : ‖(u : ℤ_[2]) - 1‖ < 1 := by
    have := padicLog_norm_pow_sub_one_le u
    rw [PadicInt.norm_def]; push_cast; norm_num at this ⊢; linarith
  obtain ⟨a, ha⟩ := (PadicInt.norm_lt_one_iff_dvd _).mp h1
  have hu : (u : ℤ_[2]) = 1 + ((2 : ℕ) : ℤ_[2]) * a := by linear_combination ha
  have hpar : PadicInt.toZMod (a * (a + 1)) = 0 := by
    rw [map_mul, map_add, map_one]
    generalize PadicInt.toZMod a = b
    revert b; decide
  have hb := padicLog_norm_le_inv_of_toZMod_eq_zero hpar
  have hb' : ‖((a * (a + 1) : ℤ_[2]) : ℚ_[2])‖ ≤ 1 / 2 := by simpa using hb
  have hz : (u : ℤ_[2]) ^ 2 - 1 = ((2 : ℕ) : ℤ_[2]) ^ 2 * (a * (a + 1)) := by rw [hu]; ring
  have heq : ((u : ℤ_[2]) : ℚ_[2]) ^ 2 - 1 =
      ((2 : ℕ) : ℚ_[2]) ^ 2 * ((a * (a + 1) : ℤ_[2]) : ℚ_[2]) := by
    have := congrArg (fun t : ℤ_[2] => (t : ℚ_[2])) hz
    simpa only [PadicInt.coe_sub, PadicInt.coe_pow, PadicInt.coe_one, PadicInt.coe_mul,
      PadicInt.coe_natCast] using this
  rw [heq, norm_mul]
  have h2 : ‖((2 : ℕ) : ℚ_[2]) ^ 2‖ = (4 : ℝ)⁻¹ := by
    rw [Padic.norm_p_pow]; norm_num
  rw [h2]
  nlinarith [norm_nonneg ((a * (a + 1) : ℤ_[2]) : ℚ_[2])]

/-- `‖p*‖ = 1 / p*` in `ℚ_p`. -/
theorem padicLog_norm_pStar :
    ‖((padicLogPStar p : ℕ) : ℚ_[p])‖ = ((padicLogPStar p : ℕ) : ℝ)⁻¹ := by
  unfold padicLogPStar
  split_ifs with h
  · rw [Nat.cast_pow, Padic.norm_p_pow]; simp [zpow_neg]
  · exact Padic.norm_p

/-- **Image of the logarithm on units**: `log (ℤ_p^×)` is the closed ball of radius `1 / p*`,
that is `p ℤ_p` for odd `p` and `4 ℤ_2` for `p = 2`. -/
theorem padicLogUnit_range :
    Set.range (fun u : ℤ_[p]ˣ => padicLogUnit p ((u : ℤ_[p]) : ℚ_[p])) =
      {z : ℚ_[p] | ‖z‖ ≤ ((padicLogPStar p : ℕ) : ℝ)⁻¹} := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    show ‖padicLogUnit p _‖ ≤ _
    by_cases h2 : p = 2
    · subst h2
      have hx := padicLog_norm_pow_sub_one_le u
      norm_num at hx
      set x : ℚ_[2] := ((u : ℤ_[2]) : ℚ_[2]) - 1
      have hx1 : ‖x‖ < 1 := hx.trans_lt (by norm_num)
      have hux : ((u : ℤ_[2]) : ℚ_[2]) = 1 + x := by simp [x]
      have hsq := padicLog_two_norm_sq_sub_one_le u
      rw [hux] at hsq ⊢
      rw [padicLogUnit_one_add hx1]
      have hpow := (padicLogOnePlus_pow_sub_one (p := 2) hx1 2).2
      have hn : ‖padicLogOnePlus 2 ((1 + x) ^ 2 - 1)‖ = ‖(1 + x) ^ 2 - 1‖ :=
        padicLogOnePlus_norm_eq (hsq.trans (by simp [padicLogPStar]; norm_num))
      rw [hpow, norm_mul] at hn
      have h2n : ‖((2 : ℕ) : ℚ_[2])‖ = (2 : ℝ)⁻¹ := Padic.norm_p
      rw [h2n] at hn
      simp only [padicLogPStar]
      push_cast
      nlinarith
    · have hodd : padicLogPStar p = p := by simp [padicLogPStar, h2]
      rw [hodd, padicLogUnit, norm_mul]
      have hpm : ‖((p - 1 : ℕ) : ℚ_[p])‖ = 1 := by
        refine Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr ?_)
        have := hp.out.two_le
        exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
      have hy := padicLog_norm_pow_sub_one_le u
      rw [norm_inv, hpm, inv_one, one_mul,
        padicLogOnePlus_norm_eq (by rw [hodd]; exact hy)]
      exact hy
  · intro hz
    obtain ⟨x, hx, rfl⟩ := padicLogOnePlus_surjOn hz
    have hx1 : ‖x‖ < 1 := hx.trans_lt padicLog_inv_pStar_lt_one
    have hn : ‖(1 + x : ℚ_[p])‖ = 1 := padicLog_norm_one_add hx1
    let v : ℤ_[p] := ⟨1 + x, hn.le⟩
    have hv : IsUnit v := PadicInt.isUnit_iff.mpr hn
    refine ⟨hv.unit, ?_⟩
    show padicLogUnit p (1 + x) = _
    exact padicLogUnit_one_add hx1

/-- IUT IV Proposition 1.2 (i) for `k_i = ℚ_p` and `p > 2`: `log (ℤ_p^×) = p ℤ_p`, written as the
closed ball of radius `1 / p`. -/
theorem padicLogUnit_range_of_ne_two (h2 : p ≠ 2) :
    Set.range (fun u : ℤ_[p]ˣ => padicLogUnit p ((u : ℤ_[p]) : ℚ_[p])) =
      {z : ℚ_[p] | ‖z‖ ≤ (p : ℝ)⁻¹} := by
  rw [padicLogUnit_range]; simp [padicLogPStar, h2]

/-- IUT IV Proposition 1.2 (i) for `k_i = ℚ_2` (`a = 2`, `b = 0`):
`4 ℤ_2 ⊆ log (ℤ_2^×) ⊆ ℤ_2`, written with closed balls. -/
theorem padicLogUnit_range_two_bounds :
    {z : ℚ_[2] | ‖z‖ ≤ (4 : ℝ)⁻¹} ⊆
        Set.range (fun u : ℤ_[2]ˣ => padicLogUnit 2 ((u : ℤ_[2]) : ℚ_[2])) ∧
      Set.range (fun u : ℤ_[2]ˣ => padicLogUnit 2 ((u : ℤ_[2]) : ℚ_[2])) ⊆
        {z : ℚ_[2] | ‖z‖ ≤ 1} := by
  have h4 : (((padicLogPStar 2 : ℕ) : ℝ))⁻¹ = (4 : ℝ)⁻¹ := by norm_num [padicLogPStar]
  rw [padicLogUnit_range, h4]
  exact ⟨subset_rfl, fun z (hz : ‖z‖ ≤ (4 : ℝ)⁻¹) => hz.trans (by norm_num)⟩

/-- The log-shell of `ℚ_p` in the sense of IUT III Definition 1.1, page 24, for the base field
`ℚ_p`: `(p*)⁻¹ · log (ℤ_p^×)`. -/
noncomputable def padicLogShell (p : ℕ) [Fact p.Prime] : Set ℚ_[p] :=
  (fun z => ((padicLogPStar p : ℕ) : ℚ_[p])⁻¹ * z) ''
    Set.range (fun u : ℤ_[p]ˣ => padicLogUnit p ((u : ℤ_[p]) : ℚ_[p]))

/-- The log-shell of `ℚ_p` is the closed unit ball, that is `ℤ_p`. -/
theorem padicLog_image_inv_mul_range {c : ℚ_[p]} (hc : ‖c‖ = ((padicLogPStar p : ℕ) : ℝ)⁻¹) :
    (fun z => c⁻¹ * z) '' Set.range (fun u : ℤ_[p]ˣ => padicLogUnit p ((u : ℤ_[p]) : ℚ_[p])) =
      {y : ℚ_[p] | ‖y‖ ≤ 1} := by
  have hspos : (0 : ℝ) < ((padicLogPStar p : ℕ) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le hp.out.pos padicLog_pStar_ge
  have hpos : (0 : ℝ) < ((padicLogPStar p : ℕ) : ℝ)⁻¹ := inv_pos.mpr hspos
  have hs0 : c ≠ 0 := by rw [← norm_pos_iff, hc]; exact hpos
  rw [padicLogUnit_range]
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [norm_mul, norm_inv, hc, inv_inv]
    calc ((padicLogPStar p : ℕ) : ℝ) * ‖z‖ ≤
          ((padicLogPStar p : ℕ) : ℝ) * ((padicLogPStar p : ℕ) : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left hz hspos.le
      _ = 1 := mul_inv_cancel₀ hspos.ne'
  · intro hy
    refine ⟨c * y, ?_, by rw [← mul_assoc, inv_mul_cancel₀ hs0, one_mul]⟩
    rw [norm_mul, hc]
    calc ((padicLogPStar p : ℕ) : ℝ)⁻¹ * ‖y‖ ≤ ((padicLogPStar p : ℕ) : ℝ)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hy hpos.le
      _ = _ := mul_one _

/-- The log-shell of `ℚ_p` is the closed unit ball of `ℚ_p`. -/
theorem padicLogShell_eq : padicLogShell p = {y : ℚ_[p] | ‖y‖ ≤ 1} :=
  padicLog_image_inv_mul_range padicLog_norm_pStar

/-- The variant with the factor `(2p)⁻¹` in place of `(p*)⁻¹` gives the same set: for odd `p`,
`2p` and `p* = p` have the same norm, and for `p = 2`, `2p = 4 = p*`. -/
theorem padicLogShell_eq_two_mul :
    (fun z => ((2 * p : ℕ) : ℚ_[p])⁻¹ * z) ''
        Set.range (fun u : ℤ_[p]ˣ => padicLogUnit p ((u : ℤ_[p]) : ℚ_[p])) =
      padicLogShell p := by
  rw [padicLogShell_eq]
  refine padicLog_image_inv_mul_range ?_
  rw [padicLog_norm_pStar.symm]
  unfold padicLogPStar
  split_ifs with h
  · subst h; norm_num
  · have h2 : ‖((2 : ℕ) : ℚ_[p])‖ = 1 := by
      refine Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr ?_)
      intro hd
      exact h ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hd)
    rw [Nat.cast_mul, norm_mul, h2, one_mul]

/-- The log-shell of `ℚ_p` equals `ℤ_p`, viewed inside `ℚ_p`. -/
theorem padicLogShell_eq_range_coe :
    padicLogShell p = Set.range ((↑) : ℤ_[p] → ℚ_[p]) := by
  rw [padicLogShell_eq]
  ext y
  exact ⟨fun hy => ⟨⟨y, hy⟩, rfl⟩, by rintro ⟨z, rfl⟩; exact z.2⟩

/-- IUT III Proposition 1.2 (v) (b_non), page 32, for the base field `ℚ_p`: the log-shell contains
the integers `ℤ_p` (the invariants of the integers of the codomain), viewed inside `ℚ_p`. -/
theorem padicInt_subset_padicLogShell : Set.range ((↑) : ℤ_[p] → ℚ_[p]) ⊆ padicLogShell p :=
  padicLogShell_eq_range_coe.symm.subset

/-- IUT III Proposition 1.2 (v) (c_non), page 32, for the base field `ℚ_p`: the log-shell
contains the image `log (ℤ_p^×)` of the units (the pre-log-shell). -/
theorem padicLogUnit_range_subset_padicLogShell :
    Set.range (fun u : ℤ_[p]ˣ => padicLogUnit p ((u : ℤ_[p]) : ℚ_[p])) ⊆ padicLogShell p := by
  rw [padicLogUnit_range, padicLogShell_eq]
  exact fun z (hz : ‖z‖ ≤ _) => hz.trans (padicLog_inv_pStar_lt_one.le)

/-- IUT III Proposition 1.2 (v) (a_non), page 31, for the base field `ℚ_p`: the log-shell is
compact. -/
theorem padicLogShell_isCompact : IsCompact (padicLogShell p) := by
  have : padicLogShell p = Metric.closedBall (0 : ℚ_[p]) 1 := by
    rw [padicLogShell_eq]; ext y; simp
  rw [this]
  exact isCompact_closedBall _ _

/-- `log` on units is a homomorphism `ℤ_p^× → ℚ_p`. -/
theorem padicLogUnit_mul (u v : ℤ_[p]ˣ) :
    padicLogUnit p (((u * v : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) =
      padicLogUnit p ((u : ℤ_[p]) : ℚ_[p]) + padicLogUnit p ((v : ℤ_[p]) : ℚ_[p]) := by
  have hρ : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  set a := ((u : ℤ_[p]) : ℚ_[p]) ^ (p - 1) - 1
  set b := ((v : ℤ_[p]) : ℚ_[p]) ^ (p - 1) - 1
  have ha : ‖a‖ < 1 := (padicLog_norm_pow_sub_one_le u).trans_lt hρ
  have hb : ‖b‖ < 1 := (padicLog_norm_pow_sub_one_le v).trans_lt hρ
  have he : (((u * v : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) ^ (p - 1) - 1 = a + b + a * b := by
    simp only [a, b, Units.val_mul, PadicInt.coe_mul, mul_pow]; ring
  rw [padicLogUnit, padicLogUnit, padicLogUnit, he, padicLogOnePlus_add_add_mul ha hb, mul_add]

end IUT.Prerequisites.PadicLog

