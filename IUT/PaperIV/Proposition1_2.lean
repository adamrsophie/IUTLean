import IUT.PaperIV.Theorem1_10.ElementaryFacts

/-!
# IUT IV, Proposition 1.2: the constants `a_i`, `b_i` (elementary part)

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Proposition 1.2 and its proof, and
the uses of `a_i`, `b_i` in the proof of Proposition 1.4 (iii), pages 10, 11, 13 and 14 of the
April 2020 manuscript, read from the extracted text and from the rendered pages 10 to 14. The
definitions of `a_i`, `b_i` were checked against the render of page 10, which shows a ceiling in
`a_i` and a floor in `b_i` (both lost in the text extraction).

The paper defines, for a finite extension `k_i/ℚ_p` with ramification index `e_i`,

* `a_i = (1/e_i)·⌈e_i/(p-2)⌉` if `p > 2`, and `a_i = 2` if `p = 2`;
* `b_i = ⌊log(p·e_i/(p-1))/log(p)⌋ - 1/e_i`.

This file is not a formalization of Proposition 1.2. The inclusions of (i) to (iv) concern
`p`-adic logarithms of unit groups and tensor products of rings of integers (they rest on
[Kobl], p. 81, and Proposition 1.1), which need local field theory not formalized here. On the
papers' objects, (ii) to (iv) are proved for two factors in
`IUT/PaperIV/LocalFields/TensorLogShell.lean` and for any finite number of factors in
`IUT/PaperIV/LocalFields/TensorLogShellMany.lean`. This file checks every elementary statement
about `a_i` and `b_i` that the proposition and its proof, and the proof of Proposition 1.4 (iii),
use:

* `p > 2`, `e_i ≤ p - 2` imply `a_i = 1/e_i = -b_i` (`a_b_of_le`), and `e_i = 1`, `p > 2`
  imply `a_i = 1 = -b_i` (`a_b_of_e_one`, used in (iv));
* `a_i > 1/(p-1)` and `p^{b_i + 1/e_i}/e_i > 1/(p-1)` (`a_gt`, `rpow_b_gt`), the inputs to (i);
* the floor estimate used in (iii) (`iii_floor`);
* `a_i - 1/e_i ≤ 4/p ≤ 2/log(p)` and `(b_i + 1/e_i)·log(p) ≤ log(2e_i) ≤ 1 + log(e_i)`
  (`a_sub_le`, `b_add_le`), used in Proposition 1.4 (iii);
* `a_i ≥ 1/e_i` for `p > 2`, hence `d_i + a_i ≥ 1` when `d_i ≥ (e_i - 1)/e_i`, and
  `d_i + a_i ≥ 2` for `p = 2` when `d_i ≥ 0` (`d_add_a_ge`), used in Proposition 1.4 (iii).

Hypotheses: `p` is a natural number `≥ 2` (the primality of `p` is not needed) and `e ≥ 1`.
-/

namespace IUT.PaperIV.Proposition1_2

/-- `a_i` of Proposition 1.2, as a function of `p` and `e = e_i`. -/
noncomputable def a (p e : ℕ) : ℝ :=
  if p = 2 then 2 else (1 / (e : ℝ)) * ⌈(e : ℝ) / ((p : ℝ) - 2)⌉

/-- `b_i` of Proposition 1.2, as a function of `p` and `e = e_i`. -/
noncomputable def b (p e : ℕ) : ℝ :=
  ⌊Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log p⌋ - 1 / (e : ℝ)

/-- `b_i + 1/e_i = ⌊log_p(p·e_i/(p-1))⌋`. -/
theorem b_add_inv (p e : ℕ) :
    b p e + 1 / (e : ℝ) = ⌊Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log p⌋ := by
  simp [b]

/-- If `p > 2` and `1 ≤ e ≤ p - 2`, then `a_i = 1/e_i = -b_i`. -/
theorem a_b_of_le {p e : ℕ} (hp : 2 < p) (he : 1 ≤ e) (hep : e ≤ p - 2) :
    a p e = 1 / (e : ℝ) ∧ b p e = -(1 / (e : ℝ)) := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hep' : (e : ℝ) ≤ (p : ℝ) - 2 := by
    have : e + 2 ≤ p := by omega
    have : (e : ℝ) + 2 ≤ p := by exact_mod_cast this
    linarith
  constructor
  · have hc : ⌈(e : ℝ) / ((p : ℝ) - 2)⌉ = 1 := by
      rw [Int.ceil_eq_iff]
      constructor
      · push_cast; norm_num; exact div_pos (by linarith) (by linarith)
      · push_cast; rw [div_le_one (by linarith)]; exact hep'
    simp [a, hp.ne', hc]
  · have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
    have hx1 : 1 ≤ (p : ℝ) * e / ((p : ℝ) - 1) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    have hxp : (p : ℝ) * e / ((p : ℝ) - 1) < p := by
      rw [div_lt_iff₀ (by linarith)]; nlinarith
    have hf : ⌊Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log p⌋ = 0 := by
      rw [Int.floor_eq_zero_iff]
      constructor
      · exact div_nonneg (Real.log_nonneg hx1) hlogp.le
      · rw [div_lt_one hlogp]
        exact Real.log_lt_log (by linarith) hxp
    simp [b, hf]

/-- Proposition 1.2 (iv) uses: if `p > 2` and `e_i = 1`, then `a_i = 1` and `b_i = -1`. -/
theorem a_b_of_e_one {p : ℕ} (hp : 2 < p) : a p 1 = 1 ∧ b p 1 = -1 := by
  have := a_b_of_le hp le_rfl (by omega)
  simpa using this

/-- `a_i > 1/(p-1)`, the first input to Proposition 1.2 (i). -/
theorem a_gt {p e : ℕ} (hp : 2 ≤ p) (he : 1 ≤ e) : 1 / ((p : ℝ) - 1) < a p e := by
  have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
  rcases eq_or_lt_of_le hp with h | h
  · subst h; simp [a]; norm_num
  · have hp' : (3 : ℝ) ≤ p := by exact_mod_cast h
    have hne : p ≠ 2 := by omega
    have hc : (e : ℝ) / ((p : ℝ) - 2) ≤ ⌈(e : ℝ) / ((p : ℝ) - 2)⌉ := Int.le_ceil _
    have h1 : 1 / ((p : ℝ) - 2) ≤ 1 / (e : ℝ) * ⌈(e : ℝ) / ((p : ℝ) - 2)⌉ := by
      have e1 : 1 / ((p : ℝ) - 2) = 1 / (e : ℝ) * ((e : ℝ) / ((p : ℝ) - 2)) := by
        field_simp
      rw [e1]; exact mul_le_mul_of_nonneg_left hc (by positivity)
    have h2 : 1 / ((p : ℝ) - 1) < 1 / ((p : ℝ) - 2) :=
      one_div_lt_one_div_of_lt (by linarith) (by linarith)
    simp only [a, hne, ite_false]; linarith

/-- `p^{b_i + 1/e_i}/e_i > 1/(p-1)`, the second input to Proposition 1.2 (i). -/
theorem rpow_b_gt {p e : ℕ} (hp : 2 ≤ p) (he : 1 ≤ e) :
    1 / ((p : ℝ) - 1) < (p : ℝ) ^ (b p e + 1 / (e : ℝ)) / e := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
  set x : ℝ := (p : ℝ) * e / ((p : ℝ) - 1) with hx
  have hx0 : 0 < x := by rw [hx]; apply div_pos <;> nlinarith
  set k : ℤ := ⌊Real.log x / Real.log p⌋ with hk
  have hlt : Real.log x / Real.log p < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have hlog : Real.log x / Real.log p = Real.logb p x := Real.log_div_log
  have h1 : x < (p : ℝ) ^ ((k : ℝ) + 1) := by
    have := Real.rpow_lt_rpow_of_exponent_lt (by linarith : (1 : ℝ) < p) hlt
    rwa [hlog, Real.rpow_logb (by linarith) (by linarith) hx0] at this
  rw [Real.rpow_add (by linarith), Real.rpow_one] at h1
  rw [b_add_inv, ← hk, div_lt_div_iff₀ (by linarith) (by linarith)]
  rw [hx, div_lt_iff₀ (by linarith)] at h1
  nlinarith [Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < p) (k : ℝ)]

/-- The estimate in the proof of Proposition 1.2 (iii): if `a = -b`, then for every real `y`,
`⌊y - a⌋ - b ≥ y - 1`. With `y = λ - d_I` this is `⌊λ - d_I - a_I⌋ - b_I ≥ λ - d_I - 1`. -/
theorem iii_floor (y a b : ℝ) (hab : a = -b) : y - 1 ≤ (⌊y - a⌋ : ℝ) - b := by
  have := Int.sub_one_lt_floor (y - a); rw [hab] at this ⊢; linarith

/-- `a_i - 1/e_i ≤ 4/p`, used in the proof of Proposition 1.4 (iii). -/
theorem a_sub_le {p e : ℕ} (hp : 2 ≤ p) (he : 1 ≤ e) : a p e - 1 / (e : ℝ) ≤ 4 / p := by
  have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
  rcases eq_or_lt_of_le hp with h | h
  · subst h; simp only [a, ite_true]; norm_num
  · have hp' : (3 : ℝ) ≤ p := by exact_mod_cast h
    have hne : p ≠ 2 := by omega
    have hc : (⌈(e : ℝ) / ((p : ℝ) - 2)⌉ : ℝ) < (e : ℝ) / ((p : ℝ) - 2) + 1 :=
      Int.ceil_lt_add_one _
    have h1 : 1 / (e : ℝ) * ⌈(e : ℝ) / ((p : ℝ) - 2)⌉ ≤ 1 / ((p : ℝ) - 2) + 1 / (e : ℝ) := by
      have e1 : 1 / ((p : ℝ) - 2) + 1 / (e : ℝ) = 1 / (e : ℝ) * ((e : ℝ) / ((p : ℝ) - 2) + 1) := by
        field_simp
      rw [e1]; exact mul_le_mul_of_nonneg_left hc.le (by positivity)
    have h2 : 1 / ((p : ℝ) - 2) ≤ 4 / p := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
    simp only [a, hne, ite_false]; linarith

/-- `4/p ≤ 2/log(p)` for `p ≥ 2`, used in the proof of Proposition 1.4 (iii). -/
theorem four_div_le {p : ℝ} (hp : 2 ≤ p) : 4 / p ≤ 2 / Real.log p := by
  have hlog : 0 < Real.log p := Real.log_pos (by linarith)
  rw [div_le_div_iff₀ (by linarith) hlog]
  linarith [Theorem1_10.two_log_le_self (by linarith : (0 : ℝ) < p)]

/-- `(b_i + 1/e_i)·log(p) ≤ log(2e_i) ≤ 1 + log(e_i)`, used in the proof of Proposition 1.4
(iii). -/
theorem b_add_le {p e : ℕ} (hp : 2 ≤ p) (he : 1 ≤ e) :
    (b p e + 1 / (e : ℝ)) * Real.log p ≤ Real.log (2 * e) ∧
      Real.log (2 * e) ≤ 1 + Real.log e := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hlog : 0 < Real.log p := Real.log_pos (by linarith)
  constructor
  · rw [b_add_inv]
    have h1 := Int.floor_le (Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log p)
    have h2 : (⌊Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log p⌋ : ℝ) * Real.log p
        ≤ Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) := by
      have := mul_le_mul_of_nonneg_right h1 hlog.le
      rwa [div_mul_cancel₀ _ hlog.ne'] at this
    have h3 : Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) ≤ Real.log (2 * e) := by
      apply Real.log_le_log (by apply div_pos <;> nlinarith)
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  · rw [Real.log_mul (by norm_num) (by positivity)]
    linarith [Theorem1_10.log_two_le_one]

/-- `a_i ≥ 1/e_i` for `p > 2`. -/
theorem a_ge_inv {p e : ℕ} (hp : 2 < p) (he : 1 ≤ e) : 1 / (e : ℝ) ≤ a p e := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hne : p ≠ 2 := by omega
  have hc : (1 : ℤ) ≤ ⌈(e : ℝ) / ((p : ℝ) - 2)⌉ := by
    rw [Int.one_le_ceil_iff]; exact div_pos (by linarith) (by linarith)
  have hc' : (1 : ℝ) ≤ ⌈(e : ℝ) / ((p : ℝ) - 2)⌉ := by exact_mod_cast hc
  simp only [a, hne, ite_false]
  have := mul_le_mul_of_nonneg_left hc' (by positivity : (0 : ℝ) ≤ 1 / (e : ℝ))
  linarith

/-- `d_i + a_i ≥ 1` when `p > 2` and `d_i ≥ (e_i - 1)/e_i` (Proposition 1.3 (i) with
`k_0 = ℚ_p`); `d_i + a_i ≥ 2` when `p = 2` and `d_i ≥ 0`. Used in Proposition 1.4 (iii). -/
theorem d_add_a_ge {p e : ℕ} {d : ℝ} (he : 1 ≤ e) :
    (2 < p → ((e : ℝ) - 1) / e ≤ d → 1 ≤ d + a p e) ∧ (p = 2 → 0 ≤ d → 2 ≤ d + a p e) := by
  have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
  constructor
  · intro hp hd
    have := a_ge_inv hp he
    have e1 : ((e : ℝ) - 1) / e + 1 / e = 1 := by field_simp; ring
    linarith
  · intro hp hd; subst hp; simp only [a, ite_true]; linarith

end IUT.PaperIV.Proposition1_2
