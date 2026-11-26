import IUT.Applications.ABC
import IUT.ABC.Variants
import IUT.PaperIV.Theorem1_10.StepV

/-!
# Zhou's explicit consequences of inter-universal Teichmüller theory over `ℚ` (elementary part)

Sources:

* Zhong-Peng Zhou, *The inter-universal Teichmüller theory and new Diophantine results over the
  rational numbers. I*, arXiv 2503.14510, version 1 (called Zhou I below): Definition 1.7 (i)
  and Definition 1.8 (page 11), Lemma 1.3 (page 7), Lemma 1.4 (page 8), Lemma 1.5 (page 9),
  Proposition 1.9 and Proposition 1.10 with its proof (pages 12 and 13), Corollary 1.13
  (page 14), Proposition 2.7 with its proof (page 21), Lemma 3.1 (page 25), Theorem 3.2 with
  its proof (pages 27 to 29), Corollary 3.3 with its proof (page 29).
* Zhong-Peng Zhou, *The inter-universal Teichmüller theory and new Diophantine results over
  rational numbers. II*, arXiv 2510.05448 (Zhou II): Remark 1.1.1 (page 6), which claims that
  the results of IUT I to IV hold for "2-torsion initial Θ-data". Nothing in this file uses it.

Pages read for this file: Zhou I pages 1 to 38 (the whole paper); Zhou II pages 1 to 24 and 36.
Formulas were taken from the TeX sources of both papers and compared with the extracted text of
the PDFs; no page was checked against a rendered image.

## What this file is and is not

**This file is not a formalization of Zhou's Definition 1.8, nor of IUT III, Corollary 3.12.**
The number `−|log(Θ)|` of Zhou I, Definition 1.8, is the log-volume of holomorphic hulls in
tensor products `⊗_{ℤ_p} O_{k_i}` of rings of integers of local fields, normalized as in
[AbsTopIII], Proposition 5.7. Neither these tensor products and their normalizations nor the
log-volume are available in this library or in Mathlib, so the model cannot be given with its
real meaning. What is formalized is its **numerical shadow**: the procession average over
`j ∈ {1, …, l*}` and the sum over places (Definition 1.8 (ii), (iii) for `F_mod = ℚ`, where the
weighted average over tuples of places is trivial), applied to local real numbers that are
hypotheses, bounded above by the right side of Lemma 1.4 (1.1) and of Lemma 1.5.

The model, the inequality of Proposition 1.9 (`−(1/2l)·log 𝔮 ≤ −|log(Θ)|`, "the μ6-version of
[IUT III], Corollary 3.12") and every explicit statement here are **the author's (Zhou's)
formulations**. Zhou I introduces the model as "a modified version of [IUT IV], Theorem 1.10 and
[ExpEst], Theorem 5.1"; Proposition 1.9 is assumed there with a one-sentence proof. In
particular Zhou's `a_v`, `b_v` (`zhouA`, `zhouB` below) differ from the `a_i`, `b_i` of IUT IV,
Proposition 1.2 (`IUT.PaperIV.Proposition1_2.a`, `b`).

## Contents

1. `zhouA`, `zhouB`: the constants of Definition 1.7 (i); `a_v = -b_v = 1/e_v` when
   `e_v ≤ p_v - 2` (`zhouA_eq_inv_of_le`, `zhouB_eq_neg_inv_of_le`), the case
   `p - 1 ≤ e ≤ p(p - 1)` of the proof of Proposition 1.10 (`zhouB_eq_of_mid`,
   `zhouA_add_zhouB_le_of_mid`).
2. The chain from the model inequality (Proposition 1.9) and the local bounds (Lemmas 1.4,
   1.5) to the inequality (1.11-eq7 in the TeX) of the proof of Proposition 1.10:
   `zhou_prop110_of_model`.
3. Proposition 2.7 from Corollary 1.13 (the coefficient identity): `zhou_prop27_of_cor113`.
4. Lemma 3.1 (ii), the averaging lemma, in full: `zhou_lemma31_ii`.
5. Theorem 3.2 (i) and Corollary 3.3 as statements (`ZhouTheorem32i`, `ZhouCorollary33`), the
   transfer from the `N`-level inequality of the proof (3-2-eq4) to Theorem 3.2 (i)
   (`zhouTheorem32i_of_nLevel`), and Corollary 3.3 from Theorem 3.2 (i)
   (`zhouCorollary33_of_theorem32i`).
6. The relation to the abc conjecture: Corollary 3.3 gives the library's fixed exponent bound
   `IUT.ABC.Variants.ABCWithExponent κ` (`c ≤ K·rad(abc)^κ`) for every `κ > 3/2`
   (`abcWithExponent_of_zhouCorollary33`).

## Open statements and what is not proved

`ZhouTheorem32i`, `ZhouCorollary33`, `ZhouNLevelBound` and `ZhouComputedRange` are open
statements, and so is `IUT.ABC.Variants.ABCWithExponent κ` for every `κ > 1` (for `κ ≤ 1` the
library proves it false, `IUT.ABC.Variants.not_abcWithExponent_of_le_one`). None of the first
four is proved here, and each is conditional in the papers on Proposition 1.9 (the μ6-version
of IUT III, Corollary 3.12), on
Lemmas 1.1 to 1.5 (local field theory, partly "proved similarly to" IUT IV, Proposition 1.2), on
the construction of initial Θ-data in Section 2, on analytic prime number estimates (Lemma 2.8,
citing Dusart and Rosser and Schoenfeld), on a real inequality asserted in the proof of
Theorem 3.2, and on computations in the author's code repository that are not published in the
papers (`ZhouComputedRange` is one of them). Not formalized: Lemma 1.4 itself (it needs the
tensor products), Corollary 1.13 (the algorithm for `Vol(R)`), Lemma 2.8, Proposition 2.9, and
the analytic part of Theorem 3.2 for `log N ≥ e^31`.

What does not follow: `ZhouCorollary33` does not imply `Challenge.ABC`; the exponent it gives on
`rad(abc)` for `c` is `(3 + 3ε)/2 > 3/2`, never `1 + ε` for small `ε`. Conversely
`Challenge.ABC` gives no explicit constant, so it does not imply `ZhouCorollary33` or
`ZhouTheorem32i`; it implies only bounds of the same shape with unspecified constants.
-/

open Finset

namespace IUT.Applications.ZhouExplicit

open Challenge

/-! ## 1. The constants `a_v`, `b_v` of Definition 1.7 (i) -/

/-- Zhou I, Definition 1.7 (i) and Lemma 1.3: `a_v = (1/e_v)·⌈(e_v + 1)/(p_v - 1)⌉`, as a
function of the residue characteristic `p` and the ramification index `e`. -/
noncomputable def zhouA (p e : ℕ) : ℝ := 1 / (e : ℝ) * ⌈((e : ℝ) + 1) / ((p : ℝ) - 1)⌉

/-- Zhou I, Definition 1.7 (i) and Lemma 1.3: `b_v = sup_{n ≥ 0} (n - p_v^n / e_v)`. The
supremum is Mathlib's `iSup` over `ℕ`; it is attained (the theorems below exhibit the
maximizing `n` in the cases used). -/
noncomputable def zhouB (p e : ℕ) : ℝ := ⨆ n : ℕ, ((n : ℝ) - (p : ℝ) ^ n / e)

/-- Bernoulli's inequality `1 + n(p - 1) ≤ p^n` for real `p ≥ 1`. -/
theorem zhou_bernoulli {p : ℝ} (hp : 1 ≤ p) (n : ℕ) : 1 + n * (p - 1) ≤ p ^ n := by
  have h := one_add_mul_le_pow (a := p - 1) (by linarith) n
  simpa using h

/-- Zhou I, Definition 1.7 (i): `a_v = 1/e_v` when `1 ≤ e_v ≤ p_v - 2`. -/
theorem zhouA_eq_inv_of_le {p e : ℕ} (he : 1 ≤ e) (hep : e + 2 ≤ p) :
    zhouA p e = 1 / (e : ℝ) := by
  have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hep' : (e : ℝ) + 2 ≤ p := by exact_mod_cast hep
  have hc : ⌈((e : ℝ) + 1) / ((p : ℝ) - 1)⌉ = 1 := by
    rw [Int.ceil_eq_iff]
    constructor
    · push_cast; norm_num; exact div_pos (by linarith) (by linarith)
    · push_cast; rw [div_le_one (by linarith)]; linarith
  simp [zhouA, hc]

/-- Zhou I, Definition 1.7 (i): `b_v = -1/e_v` when `1 ≤ e_v ≤ p_v - 2` (attained at `n = 0`,
by `n·e + 1 ≤ p^n`). -/
theorem zhouB_eq_neg_inv_of_le {p e : ℕ} (he : 1 ≤ e) (hep : e + 2 ≤ p) :
    zhouB p e = -(1 / (e : ℝ)) := by
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hep' : (e : ℝ) + 2 ≤ p := by exact_mod_cast hep
  have hterm : ∀ n : ℕ, (n : ℝ) - (p : ℝ) ^ n / e ≤ -(1 / (e : ℝ)) := by
    intro n
    have hb := zhou_bernoulli (p := (p : ℝ)) (by linarith) n
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    have key : (n : ℝ) * e + 1 ≤ (p : ℝ) ^ n := by nlinarith
    have e1 : (n : ℝ) - (p : ℝ) ^ n / e = ((n : ℝ) * e - (p : ℝ) ^ n) / e := by
      field_simp
    have e2 : -(1 / (e : ℝ)) = (-1) / e := by ring
    rw [e1, e2]
    exact div_le_div_of_nonneg_right (by linarith) he'.le
  have hbdd : BddAbove (Set.range fun n : ℕ => (n : ℝ) - (p : ℝ) ^ n / e) :=
    ⟨_, Set.forall_mem_range.2 hterm⟩
  apply le_antisymm (ciSup_le hterm)
  refine le_trans ?_ (le_ciSup hbdd 0)
  simp

/-- The proof of Zhou I, Proposition 1.10, page 13: `b_p = 1 - p/e_p` when
`p - 1 ≤ e_p ≤ p(p - 1)` (attained at `n = 1`). -/
theorem zhouB_eq_of_mid {p e : ℕ} (hp : 2 ≤ p) (h1 : p ≤ e + 1) (h2 : e ≤ p * (p - 1)) :
    zhouB p e = 1 - (p : ℝ) / e := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h1' : (p : ℝ) ≤ e + 1 := by exact_mod_cast h1
  have h2' : (e : ℝ) ≤ (p : ℝ) * ((p : ℝ) - 1) := by
    have h := (Nat.cast_le (α := ℝ)).2 h2
    rwa [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one] at h
  have he' : (0 : ℝ) < e := by linarith
  have hterm : ∀ n : ℕ, (n : ℝ) - (p : ℝ) ^ n / e ≤ 1 - (p : ℝ) / e := by
    intro n
    have key : (n : ℝ) * e - (p : ℝ) ^ n ≤ e - p := by
      rcases n with _ | m
      · simp; linarith
      · have hb := zhou_bernoulli (p := (p : ℝ)) (by linarith) m
        have hm : (0 : ℝ) ≤ m := m.cast_nonneg
        have h3 : (m : ℝ) * e ≤ m * ((p : ℝ) * ((p : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_left h2' hm
        push_cast
        rw [pow_succ]
        nlinarith
    have e1 : (n : ℝ) - (p : ℝ) ^ n / e = ((n : ℝ) * e - (p : ℝ) ^ n) / e := by
      field_simp
    have e2 : 1 - (p : ℝ) / e = ((e : ℝ) - p) / e := by field_simp
    rw [e1, e2]
    exact div_le_div_of_nonneg_right key he'.le
  have hbdd : BddAbove (Set.range fun n : ℕ => (n : ℝ) - (p : ℝ) ^ n / e) :=
    ⟨_, Set.forall_mem_range.2 hterm⟩
  apply le_antisymm (ciSup_le hterm)
  refine le_trans ?_ (le_ciSup hbdd 1)
  simp

/-- For integers `k` and `m > 0`, `⌈k/m⌉ ≤ (k + m - 1)/m`. -/
theorem zhou_ceil_div_le (k : ℤ) {m : ℤ} (hm : 0 < m) :
    (⌈(k : ℝ) / m⌉ : ℝ) ≤ ((k : ℝ) + m - 1) / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : (⌈(k : ℝ) / m⌉ : ℝ) - 1 < k / m := by
    have := Int.ceil_lt_add_one ((k : ℝ) / m); linarith
  have h2 : ((⌈(k : ℝ) / m⌉ : ℝ) - 1) * m < k := by rwa [lt_div_iff₀ hm'] at h1
  have h3 : (⌈(k : ℝ) / m⌉ - 1) * m < k := by exact_mod_cast h2
  have h4 : (⌈(k : ℝ) / m⌉ - 1) * m ≤ k - 1 := Int.le_sub_one_of_lt h3
  have h5 : ((⌈(k : ℝ) / m⌉ : ℝ) - 1) * m ≤ k - 1 := by exact_mod_cast h4
  rw [le_div_iff₀ hm']
  linarith

/-- The proof of Zhou I, Proposition 1.10, page 13: `a_p ≤ 1/(p - 1) + 1/e_p`. -/
theorem zhouA_le {p e : ℕ} (hp : 2 ≤ p) (he : 1 ≤ e) :
    zhouA p e ≤ 1 / ((p : ℝ) - 1) + 1 / (e : ℝ) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hc := zhou_ceil_div_le ((e : ℤ) + 1) (m := (p : ℤ) - 1) (by omega)
  push_cast at hc
  unfold zhouA
  calc 1 / (e : ℝ) * ⌈((e : ℝ) + 1) / ((p : ℝ) - 1)⌉
      ≤ 1 / (e : ℝ) * (((e : ℝ) + 1 + ((p : ℝ) - 1) - 1) / ((p : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
    _ = 1 / ((p : ℝ) - 1) + 1 / (e : ℝ) := by
        have : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp
        ring

/-- The proof of Zhou I, Proposition 1.10, page 13: `a_p + b_p = 0` when `e_p ≤ p - 2`. -/
theorem zhouA_add_zhouB_of_le {p e : ℕ} (he : 1 ≤ e) (hep : e + 2 ≤ p) :
    zhouA p e + zhouB p e = 0 := by
  rw [zhouA_eq_inv_of_le he hep, zhouB_eq_neg_inv_of_le he hep]; ring

/-- The proof of Zhou I, Proposition 1.10, page 13: when `p - 1 ≤ e_p ≤ p(p - 1)`,
`a_p + b_p ≤ 1/(p - 1) + 1 - (p - 1)/e_p`. -/
theorem zhouA_add_zhouB_le_of_mid {p e : ℕ} (hp : 2 ≤ p) (h1 : p ≤ e + 1)
    (h2 : e ≤ p * (p - 1)) :
    zhouA p e + zhouB p e ≤ 1 / ((p : ℝ) - 1) + 1 - ((p : ℝ) - 1) / e := by
  have he : 1 ≤ e := by omega
  rw [zhouB_eq_of_mid hp h1 h2]
  have := zhouA_le hp he
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have e1 : ((p : ℝ) - 1) / e = (p : ℝ) / e - 1 / e := by field_simp
  rw [e1]
  linarith

/-- `v_p(2p)` for a prime `p`: `2` if `p = 2`, `1` otherwise. -/
noncomputable def zhouVp2p (p : ℕ) : ℝ := if p = 2 then 2 else 1

/-- The proof of Zhou I, Proposition 1.10, page 13: if `d_p ≥ 1 - 1/e_p` (Lemma 1.2), then
`d_p + a_p ≥ v_p(2p)`. -/
theorem zhouVp2p_le {p e : ℕ} (hp : 2 ≤ p) (he : 1 ≤ e) {d : ℝ} (hd : 1 - 1 / (e : ℝ) ≤ d) :
    zhouVp2p p ≤ d + zhouA p e := by
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  unfold zhouVp2p zhouA
  split_ifs with h2
  · subst h2
    have hc : ⌈((e : ℝ) + 1) / (((2 : ℕ) : ℝ) - 1)⌉ = (e : ℤ) + 1 := by
      rw [show (((2 : ℕ) : ℝ) - 1) = 1 by norm_num, div_one]
      exact_mod_cast Int.ceil_natCast (e + 1)
    rw [hc]
    push_cast
    have : 1 / (e : ℝ) * ((e : ℝ) + 1) = 1 + 1 / e := by field_simp
    linarith
  · have hc : (1 : ℝ) ≤ ⌈((e : ℝ) + 1) / ((p : ℝ) - 1)⌉ := by
      have : (0 : ℤ) < ⌈((e : ℝ) + 1) / ((p : ℝ) - 1)⌉ :=
        Int.ceil_pos.2 (div_pos (by linarith) (by linarith))
      exact_mod_cast this
    have : 1 / (e : ℝ) ≤ 1 / (e : ℝ) * ⌈((e : ℝ) + 1) / ((p : ℝ) - 1)⌉ := by
      have h0 : (0 : ℝ) ≤ 1 / (e : ℝ) := by positivity
      nlinarith
    linarith

/-! ## 2. From the model inequality (Proposition 1.9) to the bound of Proposition 1.10 -/

/-- Zhou I, Definition 1.8 (ii), the procession normalization:
`(1/l*)·∑_{j=1}^{l*} f(j)`, with `m = l*`. -/
noncomputable def zhouProcessionAverage (m : ℕ) (f : ℕ → ℝ) : ℝ :=
  1 / (m : ℝ) * ∑ j ∈ Icc 1 m, f j

/-- The numerical shadow of Zhou I, Definition 1.8 (iii), for `F_mod = ℚ`: the archimedean
term plus the sum over a finite set `P` of primes of the procession averages of local real
numbers `vol p j` (standing for `−|log(Θ)|_{v_p, j}`) and `volArc j` (for `−|log(Θ)|_{v_ℝ, j}`).
For `F_mod = ℚ` the weighted average of Definition 1.8 (ii) over tuples of places has one term.
The paper sums over all of `𝕍_ℚ`; here the primes outside `P` are absent, which is the case
only if their terms vanish (not addressed). -/
noncomputable def zhouLogVolumeQ (m : ℕ) (P : Finset ℕ) (volArc : ℕ → ℝ)
    (vol : ℕ → ℕ → ℝ) : ℝ :=
  zhouProcessionAverage m volArc + ∑ p ∈ P, zhouProcessionAverage m (vol p)

/-- The right side of Zhou I, Lemma 1.4 (1.1), at the tuple `(v_p, …, v_p)` of length `j + 1`
(as in (1.11-eq3) of the proof of Proposition 1.10, where `F_mod = ℚ`): with `|I| = j + 1`
copies of one field, `d'_I = j·d_p`, `a_I = (j+1)·a_p`, `b_I = (j+1)·b_p`, and degree
`λ = (j²/2l)·v_p(q_p)`. -/
noncomputable def zhouLemma14Bound (l : ℝ) (p e : ℕ) (d vq : ℝ) (j : ℕ) : ℝ :=
  (max (⌈-((j : ℝ) ^ 2 / (2 * l)) * vq + j * d + (j + 1) * zhouA p e⌉ : ℝ)
      (-((j : ℝ) ^ 2 / (2 * l)) * vq + zhouVp2p p * (j + 1)) + (j + 1) * zhouB p e)
    * Real.log p

/-- The proof of Zhou I, Proposition 1.10, (1.11-eq4) and (1.11-eq5): if `2l ∣ e_p·v_p(q_p)`,
`d_p ∈ (1/e_p)ℤ` and `d_p ≥ 1 - 1/e_p`, the right side of Lemma 1.4 is at most
`(-(j²/2l)·v_p(q_p) + (j+1)(d_p + a_p + b_p))·log p`. -/
theorem zhouLemma14Bound_le {l : ℝ} (hl : 0 < l) {p e : ℕ} (hp : 2 ≤ p) (he : 1 ≤ e)
    {d vq : ℝ} (hd : 1 - 1 / (e : ℝ) ≤ d) (hdint : ∃ s : ℤ, d = s / e)
    (hq : ∃ t : ℤ, vq * e = 2 * l * t) (j : ℕ) :
    zhouLemma14Bound l p e d vq j
      ≤ (-((j : ℝ) ^ 2 / (2 * l)) * vq + (j + 1) * (d + zhouA p e + zhouB p e))
        * Real.log p := by
  obtain ⟨s, hs⟩ := hdint
  obtain ⟨t, ht⟩ := hq
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hj : (0 : ℝ) ≤ j := j.cast_nonneg
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
  set x := -((j : ℝ) ^ 2 / (2 * l)) * vq + j * d + (j + 1) * zhouA p e with hx
  -- `x ∈ (1/e)ℤ`
  have hxk : x = ((-(j : ℤ) ^ 2 * t + j * s + (j + 1) * ⌈((e : ℝ) + 1) / ((p : ℝ) - 1)⌉ : ℤ)
      : ℝ) / ((e : ℤ) : ℝ) := by
    have hvq : vq = 2 * l * t / e := by field_simp; linarith
    rw [hx, hvq, hs]
    unfold zhouA
    push_cast
    field_simp
  have hceil : (⌈x⌉ : ℝ) ≤ x + 1 - 1 / e := by
    have h := zhou_ceil_div_le (-(j : ℤ) ^ 2 * t + j * s
      + (j + 1) * ⌈((e : ℝ) + 1) / ((p : ℝ) - 1)⌉) (m := (e : ℤ)) (by exact_mod_cast he)
    rw [← hxk] at h
    have : ((((-(j : ℤ) ^ 2 * t + j * s + (j + 1) * ⌈((e : ℝ) + 1) / ((p : ℝ) - 1)⌉ : ℤ)
        : ℝ) + ((e : ℤ) : ℝ) - 1) / ((e : ℤ) : ℝ)) = x + 1 - 1 / e := by
      rw [hxk]; push_cast; field_simp
    linarith
  have hw := zhouVp2p_le hp he hd
  have hmax : max (⌈x⌉ : ℝ) (-((j : ℝ) ^ 2 / (2 * l)) * vq + zhouVp2p p * (j + 1))
      ≤ -((j : ℝ) ^ 2 / (2 * l)) * vq + (j + 1) * (d + zhouA p e) := by
    apply max_le
    · rw [hx] at hceil ⊢; nlinarith
    · nlinarith
  unfold zhouLemma14Bound
  rw [← hx]
  apply mul_le_mul_of_nonneg_right _ hlog
  linarith

/-- Monotonicity of the procession average. -/
theorem zhouProcessionAverage_mono {m : ℕ} {f g : ℕ → ℝ} (h : ∀ j ∈ Icc 1 m, f j ≤ g j) :
    zhouProcessionAverage m f ≤ zhouProcessionAverage m g :=
  mul_le_mul_of_nonneg_left (sum_le_sum h) (by positivity)

/-- The averaging of the proof of Zhou I, Proposition 1.10, page 13, with `l = 2m + 1`,
`m = l*`: `(1/l*)·∑_{j=1}^{l*} (-(j²/2l)·Q + (j+1)·X) = -((l+1)/24)·Q + ((l+5)/4)·X`.
(The same computation as `IUT.PaperIV.Theorem1_10.procession_average`.) -/
theorem zhou_procession_identity (Q X : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    zhouProcessionAverage m (fun j => -((j : ℝ) ^ 2 / (2 * (2 * m + 1))) * Q + (j + 1) * X)
      = -(((2 * m + 1 : ℝ) + 1) / 24) * Q + ((2 * m + 1 : ℝ) + 5) / 4 * X := by
  have h1 := IUT.PaperIV.Theorem1_10.procession_average X Q 0 0 (2 * m + 1) m hm
  rw [IUT.PaperIV.Theorem1_10.procession_average_l] at h1
  unfold zhouProcessionAverage
  have h2 : ∑ j ∈ Icc 1 m, (-((j : ℝ) ^ 2 / (2 * (2 * m + 1))) * Q + (j + 1) * X)
      = ∑ j ∈ Icc 1 m, (((j : ℝ) + 1) * X - (j : ℝ) ^ 2 / (2 * (2 * m + 1)) * Q + 0
        + 4 * ((j : ℝ) + 1) * 0) :=
    sum_congr rfl fun j _ => by ring
  rw [h2, h1]
  ring

/-- The last step of the proof of Zhou I, Proposition 1.10, page 13: for `l ≥ 5`,
`-(1/2l)·Q ≤ -((l+1)/24)·Q + ((l+5)/4)·X` gives `(1/6)·Q ≤ ((l² + 5l)/(l² + l - 12))·X`. -/
theorem zhou_prop110_coefficient {l Q X : ℝ} (hl : 5 ≤ l)
    (h : -(1 / (2 * l)) * Q ≤ -((l + 1) / 24) * Q + (l + 5) / 4 * X) :
    1 / 6 * Q ≤ (l ^ 2 + 5 * l) / (l ^ 2 + l - 12) * X := by
  have hl0 : 0 < l := by linarith
  have hD : 0 < l ^ 2 + l - 12 := by nlinarith
  have h' : -(1 / (2 * l)) * Q * (24 * l) ≤ (-((l + 1) / 24) * Q + (l + 5) / 4 * X) * (24 * l) :=
    mul_le_mul_of_nonneg_right h (by linarith)
  have e1 : -(1 / (2 * l)) * Q * (24 * l) = -12 * Q := by field_simp; ring
  have e2 : (-((l + 1) / 24) * Q + (l + 5) / 4 * X) * (24 * l)
      = -(l * (l + 1)) * Q + 6 * l * (l + 5) * X := by ring
  rw [e1, e2] at h'
  have hc : (l ^ 2 + 5 * l) / (l ^ 2 + l - 12) * X = (l ^ 2 + 5 * l) * X / (l ^ 2 + l - 12) := by
    ring
  rw [hc, le_div_iff₀ hD]
  nlinarith

/-- **From the model inequality to (1.11-eq7) of the proof of Zhou I, Proposition 1.10.**
Let `l = 2m + 1` with `m = l* ≥ 2` (so `l ≥ 5`), `P` a finite set of primes, and at each
`p ∈ P` a ramification index `e_p ≥ 1`, a different index `d_p ∈ (1/e_p)ℤ` with
`d_p ≥ 1 - 1/e_p` (Lemma 1.2), and `v_p(q_p)` with `2l ∣ e_p·v_p(q_p)` ((1.8-eq), from the
`2l`-torsion). Assume:

* `hloc`: each local term `vol p j` (standing for `−|log(Θ)|_{v_p, j}`) is at most the right
  side of Lemma 1.4 (1.1) at the tuple `(v_p, …, v_p)`;
* `harc`: each archimedean term is at most `(j+1)·log π` (Lemma 1.5 with `|I| = j + 1`);
* `hmodel`: Proposition 1.9 in the numerical form `-(1/2l)·log 𝔮 ≤ −|log(Θ)|`, with
  `log 𝔮 = ∑_p v_p(q_p)·log p` and `−|log(Θ)|` as in `zhouLogVolumeQ`.

Then `(1/6)·log 𝔮 ≤ ((l² + 5l)/(l² + l - 12))·(log π + ∑_p (d_p + a_p + b_p)·log p)`.

`hmodel` is the assumed IUT input (Zhou's form of the μ6-version of IUT III, Corollary 3.12);
`hloc` and `harc` stand for Lemmas 1.4 and 1.5, which are not formalized. -/
theorem zhou_prop110_of_model (m : ℕ) (hm : 2 ≤ m) (P : Finset ℕ) (hP : ∀ p ∈ P, 2 ≤ p)
    (e : ℕ → ℕ) (he : ∀ p ∈ P, 1 ≤ e p) (d vq : ℕ → ℝ)
    (hd : ∀ p ∈ P, 1 - 1 / (e p : ℝ) ≤ d p) (hdint : ∀ p ∈ P, ∃ s : ℤ, d p = s / e p)
    (hq : ∀ p ∈ P, ∃ t : ℤ, vq p * e p = 2 * (2 * m + 1 : ℝ) * t)
    (vol : ℕ → ℕ → ℝ) (volArc : ℕ → ℝ)
    (hloc : ∀ p ∈ P, ∀ j ∈ Icc 1 m,
      vol p j ≤ zhouLemma14Bound (2 * m + 1) p (e p) (d p) (vq p) j)
    (harc : ∀ j ∈ Icc 1 m, volArc j ≤ (j + 1) * Real.log Real.pi)
    (hmodel : -(1 / (2 * (2 * m + 1 : ℝ))) * ∑ p ∈ P, vq p * Real.log p
      ≤ zhouLogVolumeQ m P volArc vol) :
    1 / 6 * ∑ p ∈ P, vq p * Real.log p
      ≤ ((2 * m + 1 : ℝ) ^ 2 + 5 * (2 * m + 1)) / ((2 * m + 1 : ℝ) ^ 2 + (2 * m + 1) - 12)
        * (Real.log Real.pi
          + ∑ p ∈ P, (d p + zhouA p (e p) + zhouB p (e p)) * Real.log p) := by
  have hm1 : 1 ≤ m := by omega
  have hl : (5 : ℝ) ≤ 2 * m + 1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  set l : ℝ := 2 * m + 1 with hl_def
  have hl0 : 0 < l := by linarith
  -- local averages
  have hlocavg : ∀ p ∈ P, zhouProcessionAverage m (vol p)
      ≤ -((l + 1) / 24) * (vq p * Real.log p)
        + (l + 5) / 4 * ((d p + zhouA p (e p) + zhouB p (e p)) * Real.log p) := by
    intro p hp
    have h1 : zhouProcessionAverage m (vol p) ≤ zhouProcessionAverage m (fun j =>
        -((j : ℝ) ^ 2 / (2 * (2 * m + 1))) * (vq p * Real.log p)
          + (j + 1) * ((d p + zhouA p (e p) + zhouB p (e p)) * Real.log p)) := by
      apply zhouProcessionAverage_mono
      intro j hj
      refine (hloc p hp j hj).trans ?_
      refine (zhouLemma14Bound_le hl0 (hP p hp) (he p hp) (hd p hp) (hdint p hp)
        (hq p hp) j).trans (le_of_eq ?_)
      ring
    rw [zhou_procession_identity _ _ m hm1] at h1
    exact h1
  have harcavg : zhouProcessionAverage m volArc ≤ (l + 5) / 4 * Real.log Real.pi := by
    have h1 : zhouProcessionAverage m volArc ≤ zhouProcessionAverage m (fun j =>
        -((j : ℝ) ^ 2 / (2 * (2 * m + 1))) * 0 + (j + 1) * Real.log Real.pi) := by
      apply zhouProcessionAverage_mono
      intro j hj
      simpa using harc j hj
    rw [zhou_procession_identity _ _ m hm1] at h1
    simpa using h1
  have htot : zhouLogVolumeQ m P volArc vol
      ≤ -((l + 1) / 24) * ∑ p ∈ P, vq p * Real.log p
        + (l + 5) / 4 * (Real.log Real.pi
          + ∑ p ∈ P, (d p + zhouA p (e p) + zhouB p (e p)) * Real.log p) := by
    unfold zhouLogVolumeQ
    have hs := sum_le_sum hlocavg
    rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hs
    linarith
  exact zhou_prop110_coefficient hl (hmodel.trans htot)

/-! ## 3. Proposition 2.7 from Corollary 1.13 -/

/-- The coefficient identity behind Zhou I, Proposition 2.7, page 21:
`((l² + 5l)/(l² + l - 12))·(1 - 1/(3l)) = 1 + (11l + 31)/(3l² + 3l - 36)`. -/
theorem zhou_prop27_coefficient {l : ℝ} (hl : 5 ≤ l) :
    (l ^ 2 + 5 * l) / (l ^ 2 + l - 12) * (1 - 1 / (3 * l))
      = 1 + (11 * l + 31) / (3 * l ^ 2 + 3 * l - 36) := by
  have hl0 : l ≠ 0 := by intro h; linarith
  have hD : l ^ 2 + l - 12 ≠ 0 := by nlinarith
  rw [show 3 * l ^ 2 + 3 * l - 36 = 3 * (l ^ 2 + l - 12) by ring]
  have h3 : (3 : ℝ) * (l ^ 2 + l - 12) ≠ 0 := mul_ne_zero three_ne_zero hD
  have h3l : (3 : ℝ) * l ≠ 0 := mul_ne_zero three_ne_zero hl0
  rw [one_sub_div h3l, one_add_div h3, div_mul_div_comm,
    div_eq_div_iff (mul_ne_zero hD h3l) h3]
  ring

/-- **Zhou I, Proposition 2.7, from Corollary 1.13** (the step "(2-1-eq1) follows directly from
Corollary 1.13", page 21). For μ6-initial Θ-data of type `(l, N², N'²)` admitting a dataset
with `e_0 = 3`, Corollary 1.13 reads
`(1/6)·log(N'²) ≤ ((l²+5l)/(l²+l-12))·((1 - 1/(3l))·log rad(N²) - (1/3)(1 - 1/l)·log rad(N_l)) + Vol`.
With `LN' = log N'`, `R = log rad N = log rad N²` and `R_l = log rad(N_l) ≥ 0`, this gives
`log N' ≤ (3 + (11l + 31)/(l² + l - 12))·R + 3·Vol`, the hypothesis (3-1-eq1) of Lemma 3.1
(there `log N'_l = ∑_{p ≠ l, l ∤ v_p(N)} v_p(N)·log p`). Corollary 1.13 itself is a hypothesis. -/
theorem zhou_prop27_of_cor113 {l LN' R Rl V : ℝ} (hl : 5 ≤ l) (hRl : 0 ≤ Rl)
    (hcor : 1 / 6 * (2 * LN') ≤ (l ^ 2 + 5 * l) / (l ^ 2 + l - 12)
      * ((1 - 1 / (3 * l)) * R - 1 / 3 * (1 - 1 / l) * Rl) + V) :
    LN' ≤ (3 + (11 * l + 31) / (l ^ 2 + l - 12)) * R + 3 * V := by
  have hl0 : 0 < l := by linarith
  have hD : 0 < l ^ 2 + l - 12 := by nlinarith
  have hc : 0 ≤ (l ^ 2 + 5 * l) / (l ^ 2 + l - 12) := by positivity
  have hneg : 0 ≤ (l ^ 2 + 5 * l) / (l ^ 2 + l - 12) * (1 / 3 * (1 - 1 / l) * Rl) := by
    have : 0 ≤ 1 - 1 / l := by rw [sub_nonneg, div_le_one hl0]; linarith
    positivity
  have hcoef := zhou_prop27_coefficient hl
  have e3 : (3 + (11 * l + 31) / (l ^ 2 + l - 12))
      = 3 * (1 + (11 * l + 31) / (3 * l ^ 2 + 3 * l - 36)) := by
    have hD' := hD.ne'
    rw [show 3 * l ^ 2 + 3 * l - 36 = 3 * (l ^ 2 + l - 12) by ring]
    field_simp
  rw [e3, ← hcoef]
  have : (l ^ 2 + 5 * l) / (l ^ 2 + l - 12) * ((1 - 1 / (3 * l)) * R - 1 / 3 * (1 - 1 / l) * Rl)
      = (l ^ 2 + 5 * l) / (l ^ 2 + l - 12) * (1 - 1 / (3 * l)) * R
        - (l ^ 2 + 5 * l) / (l ^ 2 + l - 12) * (1 / 3 * (1 - 1 / l) * Rl) := by ring
  rw [this] at hcor
  linarith

/-! ## 4. Lemma 3.1 (ii): the averaging lemma -/

/-- The coefficient `(11l + 31)/(l² + l - 12)` of Zhou I, Proposition 2.7 and Lemma 3.1. -/
noncomputable def zhouCoeff (l : ℕ) : ℝ := (11 * (l : ℝ) + 31) / ((l : ℝ) ^ 2 + l - 12)

/-- **Zhou I, Lemma 3.1 (ii)**, page 25. Let `N` be a natural number, `h = log N`, `S` a finite nonempty set of
primes with `n = |S|`, and `k` such that every `k`-element subset of `S` has product
`> h/log 2` (this is the paper's `k(S) > h/log 2`, since `k(S)`, the product of the `k`
smallest elements of `S`, is the least such product). Suppose that for each `l ∈ S`
`∑_{p ≠ l, l ∤ v_p(N)} v_p(N)·log p ≤ (3 + (11l+31)/(l²+l-12))·log rad N + 3·Vol(l)` (3-1-eq1).
Then `h ≤ (3 + a_1)·log rad N + a_2 + k·h/n` with `a_1 = (1/n)∑_{l ∈ S} (11l+31)/(l²+l-12)` and
`a_2 = (3/n)∑_{l ∈ S} Vol(l)`.

The paper also assumes `N > 0`, `l ≥ 5` for `l ∈ S`, `n ≥ 2`, `2 ≤ k ≤ n` and `Vol(l) ≥ 0`; the proof
does not use them, and they are dropped here. -/
theorem zhou_lemma31_ii (N : ℕ) (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime)
    (hSne : S.Nonempty) (k : ℕ)
    (hk : ∀ T ∈ S.powersetCard k, Real.log N < (∏ p ∈ T, (p : ℝ)) * Real.log 2)
    (Vol : ℕ → ℝ)
    (hpart : ∀ l ∈ S, ∑ p ∈ N.primeFactors with (p ≠ l ∧ ¬ l ∣ N.factorization p),
        (N.factorization p : ℝ) * Real.log p
      ≤ (3 + zhouCoeff l) * Real.log (rad N) + 3 * Vol l) :
    Real.log N ≤ (3 + 1 / (S.card : ℝ) * ∑ l ∈ S, zhouCoeff l) * Real.log (rad N)
      + 3 / (S.card : ℝ) * ∑ l ∈ S, Vol l + k * Real.log N / S.card := by
  classical
  set PF := N.primeFactors with hPF
  set f : ℕ → ℝ := fun p => (N.factorization p : ℝ) * Real.log p with hf
  set R := Real.log (rad N) with hR
  have hf0 : ∀ p ∈ PF, 0 ≤ f p := fun p hp =>
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le))
  have hlogN : Real.log N = ∑ p ∈ PF, f p := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
  -- each prime factor has weight at most `k`
  have hcount : ∀ p ∈ PF, (if p ∈ S then (1 : ℝ) else 0)
      + ((S.filter (fun l => l ∣ N.factorization p)).card : ℝ) ≤ k := by
    intro p hp
    have hlt : (S.filter (fun l => l ∣ N.factorization p)).card < k := by
      by_contra hge
      push Not at hge
      obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hge
      have hTS : T ∈ S.powersetCard k :=
        Finset.mem_powersetCard.2 ⟨hTsub.trans (filter_subset _ _), hTcard⟩
      have hdvd : ∏ q ∈ T, q ∣ N.factorization p :=
        Finset.prod_primes_dvd _ (fun q hq => (hS q ((filter_subset _ _) (hTsub hq))).prime)
          (fun q hq => (mem_filter.1 (hTsub hq)).2)
      have hvne : N.factorization p ≠ 0 :=
        Finsupp.mem_support_iff.1 (by rw [Nat.support_factorization]; exact hp)
      have hle : ∏ q ∈ T, q ≤ N.factorization p := Nat.le_of_dvd (Nat.pos_of_ne_zero hvne) hdvd
      have h1 := hk T hTS
      have h2 : f p ≤ Real.log N := hlogN ▸ single_le_sum hf0 hp
      have h3 : (N.factorization p : ℝ) * Real.log 2 ≤ f p :=
        mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num)
          (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le)) (Nat.cast_nonneg _)
      have h4 : (∏ q ∈ T, (q : ℝ)) ≤ N.factorization p := by
        rw [← Nat.cast_prod]; exact_mod_cast hle
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      nlinarith
    have h1 : (if p ∈ S then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
    have h2 : ((S.filter (fun l => l ∣ N.factorization p)).card : ℝ) + 1 ≤ k := by
      exact_mod_cast hlt
    linarith
  -- the inequality for one `l`
  have hper : ∀ l ∈ S, Real.log N ≤ (3 + zhouCoeff l) * R + 3 * Vol l
      + ∑ p ∈ PF, f p * ((if p = l then (1 : ℝ) else 0)
        + (if l ∣ N.factorization p then (1 : ℝ) else 0)) := by
    intro l hl
    have hsplit := Finset.sum_filter_add_sum_filter_not PF
      (fun p => p ≠ l ∧ ¬ l ∣ N.factorization p) f
    have hrest : ∑ p ∈ PF with ¬(p ≠ l ∧ ¬ l ∣ N.factorization p), f p
        ≤ ∑ p ∈ PF, f p * ((if p = l then (1 : ℝ) else 0)
          + (if l ∣ N.factorization p then (1 : ℝ) else 0)) := by
      rw [Finset.sum_filter]
      refine sum_le_sum fun p hp => ?_
      have h0 := hf0 p hp
      have hind : (0 : ℝ) ≤ (if p = l then (1 : ℝ) else 0)
          + (if l ∣ N.factorization p then (1 : ℝ) else 0) := by
        split_ifs <;> norm_num
      by_cases h : p ≠ l ∧ ¬ l ∣ N.factorization p
      · rw [ite_eq_right (not_not_intro h)]
        exact mul_nonneg h0 hind
      · rw [ite_eq_left h]
        have hone : (1 : ℝ) ≤ (if p = l then (1 : ℝ) else 0)
            + (if l ∣ N.factorization p then (1 : ℝ) else 0) := by
          by_cases hpl : p = l
          · rw [ite_eq_left hpl]
            split_ifs <;> norm_num
          · have hd : l ∣ N.factorization p := by
              by_contra hnd
              exact h ⟨hpl, hnd⟩
            rw [ite_eq_right hpl, ite_eq_left hd]
            norm_num
        nlinarith
    have hp := hpart l hl
    rw [hlogN, ← hsplit]
    linarith
  -- sum over `l ∈ S`
  have hsum : (S.card : ℝ) * Real.log N
      ≤ ∑ l ∈ S, ((3 + zhouCoeff l) * R + 3 * Vol l) + k * Real.log N := by
    have h1 := sum_le_sum hper
    rw [sum_const, nsmul_eq_mul, sum_add_distrib] at h1
    have h2 : ∑ l ∈ S, ∑ p ∈ PF, f p * ((if p = l then (1 : ℝ) else 0)
        + (if l ∣ N.factorization p then (1 : ℝ) else 0)) ≤ k * Real.log N := by
      rw [sum_comm, hlogN, mul_sum]
      refine sum_le_sum fun p hp => ?_
      rw [← mul_sum, sum_add_distrib, sum_ite_eq, sum_boole]
      have := hcount p hp
      have h0 := hf0 p hp
      nlinarith
    linarith
  have hn : (0 : ℝ) < S.card := by exact_mod_cast hSne.card_pos
  have hexp : ∑ l ∈ S, ((3 + zhouCoeff l) * R + 3 * Vol l)
      = S.card * 3 * R + (∑ l ∈ S, zhouCoeff l) * R + 3 * ∑ l ∈ S, Vol l := by
    rw [sum_add_distrib, ← sum_mul, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
    ring
  rw [hexp] at hsum
  have key : (3 + 1 / (S.card : ℝ) * ∑ l ∈ S, zhouCoeff l) * R
      + 3 / (S.card : ℝ) * ∑ l ∈ S, Vol l + k * Real.log N / S.card
      = (S.card * 3 * R + (∑ l ∈ S, zhouCoeff l) * R + 3 * ∑ l ∈ S, Vol l
        + k * Real.log N) / S.card := by
    field_simp
  rw [key, le_div_iff₀ hn]
  linarith

/-! ## 5. Theorem 3.2 (i) and Corollary 3.3 -/

/-- `N = |abc|/gcd(16, abc)` of the proof of Zhou I, Theorem 3.2 (and Proposition 2.7). -/
def zhouN (a b c : ℤ) : ℕ := (a * b * c).natAbs / Nat.gcd 16 (a * b * c).natAbs

/-- **Zhou I, Theorem 3.2 (i)** (page 27), the author's statement; not proved here. For nonzero
integers `a`, `b`, `c` with `gcd(a, b) = 1` and `a + b = c`: if `log|abc| ≥ 700`, then
`log|abc| ≤ 3·log rad(abc) + 8·√(log|abc|·log log|abc|)`. ("Coprime" for the triple is read as
`gcd(a, b) = 1`, equivalent to pairwise coprimality since `a + b = c`.) -/
def ZhouTheorem32i : Prop :=
  ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 → Int.gcd a b = 1 → a + b = c →
    700 ≤ Real.log ((a * b * c).natAbs : ℝ) →
    Real.log ((a * b * c).natAbs : ℝ)
      ≤ 3 * Real.log (rad (a * b * c).natAbs : ℝ)
        + 8 * Real.sqrt (Real.log ((a * b * c).natAbs : ℝ)
          * Real.log (Real.log ((a * b * c).natAbs : ℝ)))

/-- The inequality (3-2-eq4) of the proof of Zhou I, Theorem 3.2, page 28, for `log N ≥ h_0`:
`log N - 3·log rad N + 4·log 2 < 8·√(log N · log log N)` with `N = |abc|/gcd(16, abc)`. The paper
asserts it for `h_0 = 680`, from (3-2-eq3) (for `log N ≥ e^31`: Proposition 2.9, Lemma 3.1,
Lemma 2.8 and a real inequality) and from `ZhouComputedRange` (for `680 ≤ log N ≤ e^31`). -/
def ZhouNLevelBound (h₀ : ℝ) : Prop :=
  ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 → Int.gcd a b = 1 → a + b = c →
    h₀ ≤ Real.log (zhouN a b c : ℝ) →
    Real.log (zhouN a b c : ℝ) - 3 * Real.log (rad (zhouN a b c) : ℝ) + 4 * Real.log 2
      < 8 * Real.sqrt (Real.log (zhouN a b c : ℝ) * Real.log (Real.log (zhouN a b c : ℝ)))

/-- The range of the proof of Zhou I, Theorem 3.2 (i), page 28, covered by "the computation in
[code_of_zpzhou]" and not by an argument in the paper: (3-2-eq4) for `680 ≤ log N ≤ e^31`. -/
def ZhouComputedRange : Prop :=
  ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 → Int.gcd a b = 1 → a + b = c →
    680 ≤ Real.log (zhouN a b c : ℝ) → Real.log (zhouN a b c : ℝ) ≤ Real.exp 31 →
    Real.log (zhouN a b c : ℝ) - 3 * Real.log (rad (zhouN a b c) : ℝ) + 4 * Real.log 2
      < 8 * Real.sqrt (Real.log (zhouN a b c : ℝ) * Real.log (Real.log (zhouN a b c : ℝ)))

/-- The radical is monotone for divisibility: `m ∣ n`, `n ≠ 0` give `rad m ≤ rad n`. -/
theorem zhou_rad_le_of_dvd {m n : ℕ} (h : m ∣ n) (hn : n ≠ 0) : rad m ≤ rad n :=
  Nat.le_of_dvd (IUT.ABC.rad_pos n)
    (Finset.prod_dvd_prod_of_subset _ _ _ (Nat.primeFactors_mono h hn))

/-- **The transfer step of the proof of Zhou I, Theorem 3.2 (i)**, pages 28 and 29: the
`N`-level inequality (3-2-eq4) for `log N ≥ 680` gives Theorem 3.2 (i), using
`log N ≤ log|abc| ≤ log N + 4·log 2` and `rad N ≤ rad(abc)`. -/
theorem zhouTheorem32i_of_nLevel (h : ZhouNLevelBound 680) : ZhouTheorem32i := by
  intro a b c ha hb hc hab habc h700
  set M := (a * b * c).natAbs with hM
  have hM0 : M ≠ 0 := by
    rw [hM]; exact Int.natAbs_ne_zero.2 (mul_ne_zero (mul_ne_zero ha hb) hc)
  set g := Nat.gcd 16 M with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hg16 : g ≤ 16 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 16 M)
  have hNg : zhouN a b c * g = M := Nat.div_mul_cancel (Nat.gcd_dvd_right 16 M)
  have hN0 : zhouN a b c ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hNg; exact hM0 hNg.symm
  have hNdvd : zhouN a b c ∣ M := ⟨g, hNg.symm⟩
  have hNpos : (0 : ℝ) < zhouN a b c := by exact_mod_cast Nat.pos_of_ne_zero hN0
  have hgpos' : (0 : ℝ) < g := by exact_mod_cast hgpos
  have hlogM : Real.log (M : ℝ) = Real.log (zhouN a b c : ℝ) + Real.log (g : ℝ) := by
    rw [← Real.log_mul hNpos.ne' hgpos'.ne', ← Nat.cast_mul, hNg]
  have hlogg : Real.log (g : ℝ) ≤ 4 * Real.log 2 := by
    have : Real.log (g : ℝ) ≤ Real.log 16 :=
      Real.log_le_log hgpos' (by exact_mod_cast hg16)
    have e16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    linarith
  have hlogg0 : 0 ≤ Real.log (g : ℝ) := Real.log_nonneg (by exact_mod_cast hgpos)
  have hrad : Real.log (rad (zhouN a b c) : ℝ) ≤ Real.log (rad M : ℝ) :=
    Real.log_le_log (by exact_mod_cast IUT.ABC.rad_pos _)
      (by exact_mod_cast zhou_rad_le_of_dvd hNdvd hM0)
  have hl2 := Real.log_two_lt_d9
  have h680 : 680 ≤ Real.log (zhouN a b c : ℝ) := by linarith
  have key := h a b c ha hb hc hab habc h680
  -- monotonicity of `x ↦ √(x·log x)`
  have hLN1 : 1 < Real.log (zhouN a b c : ℝ) := by linarith
  have hloglog0 : 0 < Real.log (Real.log (zhouN a b c : ℝ)) := Real.log_pos hLN1
  have hle : Real.log (zhouN a b c : ℝ) ≤ Real.log (M : ℝ) := by linarith
  have hloglog : Real.log (Real.log (zhouN a b c : ℝ)) ≤ Real.log (Real.log (M : ℝ)) :=
    Real.log_le_log (by linarith) hle
  have hprod : Real.log (zhouN a b c : ℝ) * Real.log (Real.log (zhouN a b c : ℝ))
      ≤ Real.log (M : ℝ) * Real.log (Real.log (M : ℝ)) :=
    mul_le_mul hle hloglog hloglog0.le (by linarith)
  have hsqrt := Real.sqrt_le_sqrt hprod
  linarith

/-- **Zhou I, Corollary 3.3** (page 29), the author's statement; not proved here. For
`0 < ε ≤ 1/10` and nonzero integers `a`, `b`, `c` with `gcd(a, b) = 1` and `a + b = c`:
`|abc| ≤ max{exp(400·ε^{-2}·log(ε^{-1})), rad(abc)^{3 + 3ε}}`. -/
def ZhouCorollary33 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 10 →
    ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 → Int.gcd a b = 1 → a + b = c →
      ((a * b * c).natAbs : ℝ)
        ≤ max (Real.exp (400 * ε⁻¹ ^ 2 * Real.log ε⁻¹))
          ((rad (a * b * c).natAbs : ℝ) ^ (3 + 3 * ε))

/-- `log 10 > 2.28`, from `2^33 < 10^10` and `log 2 > 0.6931471803`. -/
theorem zhou_log_ten_gt : (2.28 : ℝ) < Real.log 10 := by
  have h : ((2 : ℝ) ^ 33) < 10 ^ 10 := by norm_num
  have h2 := Real.log_lt_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at h2
  have := Real.log_two_gt_d9
  push_cast at h2
  nlinarith

/-- `log 400 < 6.24`, from `400 < 2^9` and `log 2 < 0.6931471808`. -/
theorem zhou_log_four_hundred_lt : Real.log 400 < (6.24 : ℝ) := by
  have h : (400 : ℝ) < 2 ^ 9 := by norm_num
  have h2 := Real.log_lt_log (by norm_num) h
  rw [Real.log_pow] at h2
  have := Real.log_two_lt_d9
  push_cast at h2
  nlinarith

/-- `log y ≤ y/e` for `y > 0`. -/
theorem zhou_log_le_div_exp_one {y : ℝ} (hy : 0 < y) : Real.log y ≤ y / Real.exp 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy (Real.exp_pos 1))
  rw [Real.log_div hy.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
  linarith

/-- The scalar inequality (3-3-eq1) of the proof of Zhou I, Corollary 3.3, page 29: for
`x = ε^{-1} ≥ 10`, `h_0 = 400·x²·log x` and `u_0 = 64·(1 + x)²`, `u_0·log h_0 < h_0`. (The paper
proves `f(x) = log h_0 - log log h_0 - log u_0 > 0` from `f(10) > 0` and `f' > 0`; here it is
proved from `log x ≥ log 10 > 2.28`, `log 400 < 6.24`, `log log x ≤ (log x)/e` and
`(1 + x)² ≤ 1.21·x²`.) -/
theorem zhou_cor33_scalar {x : ℝ} (hx : 10 ≤ x) :
    64 * (1 + x) ^ 2 * Real.log (400 * x ^ 2 * Real.log x) < 400 * x ^ 2 * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hL : 2.28 < Real.log x :=
    lt_of_lt_of_le zhou_log_ten_gt (Real.log_le_log (by norm_num) hx)
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hx2 : 0 < x ^ 2 := by positivity
  have hsplit : Real.log (400 * x ^ 2 * L) = Real.log 400 + 2 * L + Real.log L := by
    rw [Real.log_mul (by positivity) hL0.ne', Real.log_mul (by norm_num) hx2.ne',
      Real.log_pow]
    push_cast
    ring
  have hlogL : Real.log L ≤ 0.368 * L := by
    have h1 := zhou_log_le_div_exp_one hL0
    have h2 := Real.exp_one_gt_d9
    have h3 : L / Real.exp 1 ≤ 0.368 * L := by
      rw [div_le_iff₀ (Real.exp_pos 1)]; nlinarith
    linarith
  have h400 := zhou_log_four_hundred_lt
  have hbound : Real.log (400 * x ^ 2 * L) ≤ 6.24 + 2.368 * L := by
    rw [hsplit]; linarith
  have hpos : 0 < Real.log (400 * x ^ 2 * L) := by
    apply Real.log_pos
    have : (1 : ℝ) ≤ 400 * x ^ 2 * L := by nlinarith
    linarith [show (1 : ℝ) < 400 * x ^ 2 * L by nlinarith]
  have hsq : (1 + x) ^ 2 ≤ 1.21 * x ^ 2 := by nlinarith
  calc 64 * (1 + x) ^ 2 * Real.log (400 * x ^ 2 * L)
      ≤ 64 * (1.21 * x ^ 2) * (6.24 + 2.368 * L) := by
        apply mul_le_mul (by linarith) hbound hpos.le (by positivity)
    _ < 400 * x ^ 2 * L := by nlinarith

/-- For `e ≤ a ≤ b`: `log b · a ≤ log a · b` (the monotonicity of `y/log y` used in the proof of
Zhou I, Corollary 3.3, (3-3-eq2)). -/
theorem zhou_log_mul_le {a b : ℝ} (ha : Real.exp 1 ≤ a) (hab : a ≤ b) :
    Real.log b * a ≤ Real.log a * b := by
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 1) ha
  have hb0 : 0 < b := by linarith
  have hla : 1 ≤ Real.log a := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) ha
  have h1 := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
  rw [Real.log_div hb0.ne' ha0.ne'] at h1
  have h2 : (Real.log b - Real.log a) * a ≤ (b / a - 1) * a :=
    mul_le_mul_of_nonneg_right h1 ha0.le
  have e1 : (b / a - 1) * a = b - a := by field_simp
  rw [e1] at h2
  nlinarith

/-- **Zhou I, Corollary 3.3 from Theorem 3.2 (i)** (the proof on page 29). -/
theorem zhouCorollary33_of_theorem32i (h : ZhouTheorem32i) : ZhouCorollary33 := by
  intro ε hε hε10 a b c ha hb hc hab habc
  set x := ε⁻¹ with hxdef
  have hx : 10 ≤ x := by
    rw [hxdef, ← one_div, le_div_iff₀ hε]; linarith
  have hx0 : 0 < x := by linarith
  set h₀ := 400 * x ^ 2 * Real.log x with hh0
  set M := (a * b * c).natAbs with hM
  have hM0 : M ≠ 0 := by
    rw [hM]; exact Int.natAbs_ne_zero.2 (mul_ne_zero (mul_ne_zero ha hb) hc)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM0
  by_cases hsmall : (M : ℝ) ≤ Real.exp h₀
  · exact le_max_of_le_left hsmall
  apply le_max_of_le_right
  push Not at hsmall
  set hh := Real.log (M : ℝ) with hhdef
  have hgt : h₀ < hh := by rw [hhdef, Real.lt_log_iff_exp_lt hMpos]; exact hsmall
  have hL : 2.28 < Real.log x :=
    lt_of_lt_of_le zhou_log_ten_gt (Real.log_le_log (by norm_num) hx)
  have hh0big : 700 ≤ h₀ := by
    have : (100 : ℝ) ≤ x ^ 2 := by nlinarith
    rw [hh0]; nlinarith
  have hhpos : 0 < hh := by linarith
  have hthm := h a b c ha hb hc hab habc (by linarith)
  rw [← hM, ← hhdef] at hthm
  set R := Real.log (rad M : ℝ) with hRdef
  set u₀ := 64 * (1 + x) ^ 2 with hu0
  have hscal : u₀ * Real.log h₀ < h₀ := zhou_cor33_scalar hx
  have he : Real.exp 1 ≤ h₀ := by
    have := Real.exp_one_lt_d9; linarith
  have hmono := zhou_log_mul_le he hgt.le
  have hu0pos : 0 < u₀ := by positivity
  have hh0pos : 0 < h₀ := by linarith
  -- `u_0·log h < h`
  have hkey : u₀ * Real.log hh < hh := by
    have h1 : u₀ * (Real.log hh * h₀) ≤ u₀ * (Real.log h₀ * hh) :=
      mul_le_mul_of_nonneg_left hmono hu0pos.le
    have h2 : u₀ * Real.log h₀ * hh < h₀ * hh := mul_lt_mul_of_pos_right hscal hhpos
    have h3 : u₀ * Real.log hh * h₀ < hh * h₀ := by nlinarith
    exact lt_of_mul_lt_mul_right h3 hh0pos.le
  -- `8·√(h·log h) < h/(1 + x)`
  have hsq : Real.sqrt (hh * Real.log hh) < hh / (8 * (1 + x)) := by
    rw [Real.sqrt_lt' (by positivity), div_pow, lt_div_iff₀ (by positivity)]
    have : (8 * (1 + x)) ^ 2 = u₀ := by rw [hu0]; ring
    rw [this]
    nlinarith
  have hlt : hh < 3 * R + hh / (1 + x) := by
    have : 8 * Real.sqrt (hh * Real.log hh) < hh / (1 + x) := by
      have e : hh / (1 + x) = 8 * (hh / (8 * (1 + x))) := by field_simp
      rw [e]; linarith
    linarith
  have hfinal : hh ≤ (3 + 3 * ε) * R := by
    have hε' : ε = 1 / x := by rw [hxdef, one_div, inv_inv]
    have h1 : hh * x < 3 * R * (1 + x) := by
      have e : hh / (1 + x) * (1 + x) = hh := by field_simp
      nlinarith [mul_lt_mul_of_pos_right hlt (by linarith : (0 : ℝ) < 1 + x)]
    rw [hε']
    have : (3 + 3 * (1 / x)) * R = 3 * R * (1 + x) / x := by field_simp; ring
    rw [this, le_div_iff₀ hx0]
    linarith
  have hradpos : (0 : ℝ) < rad M := by exact_mod_cast IUT.ABC.rad_pos M
  rw [Real.rpow_def_of_pos hradpos]
  calc (M : ℝ) = Real.exp hh := (Real.exp_log hMpos).symm
    _ ≤ Real.exp (Real.log (rad M : ℝ) * (3 + 3 * ε)) := by
        apply Real.exp_le_exp.2; rw [← hRdef]; linarith

/-! ## 6. Relation to the abc conjecture -/

/-- **Zhou's Corollary 3.3 gives the fixed exponent bound `IUT.ABC.Variants.ABCWithExponent κ`
for every `κ > 3/2`.** From `ab ≥ a + b - 1 = c - 1` we get `abc ≥ c(c - 1) ≥ c²/2`, so
Corollary 3.3 with `3 + 3ε ≤ 2κ` gives `c² ≤ 2·exp(h_0(ε))·rad(abc)^{3 + 3ε}`. Nothing better
than `3/2` follows, and in particular not `Challenge.ABC` (exponent `1 + ε`). -/
theorem abcWithExponent_of_zhouCorollary33 (h : ZhouCorollary33) (κ : ℝ) (hκ : 3 / 2 < κ) :
    IUT.ABC.Variants.ABCWithExponent κ := by
  set ε := min (1 / 10 : ℝ) ((2 * κ - 3) / 3) with hεdef
  have hε0 : 0 < ε := lt_min (by norm_num) (by linarith)
  have hε10 : ε ≤ 1 / 10 := min_le_left _ _
  have hεκ : (3 + 3 * ε) / 2 ≤ κ := by
    have : ε ≤ (2 * κ - 3) / 3 := min_le_right _ _
    linarith
  set E := Real.exp (400 * ε⁻¹ ^ 2 * Real.log ε⁻¹) with hE
  have hE1 : 1 ≤ E := by
    rw [hE]
    apply Real.one_le_exp
    have : 1 ≤ ε⁻¹ := by rw [← one_div, le_div_iff₀ hε0]; linarith
    have := Real.log_nonneg this
    positivity
  refine ⟨Real.sqrt (2 * E), Real.sqrt_pos.2 (by linarith), ?_⟩
  intro a b c ha hb hc hab habc
  have hc2 : 2 ≤ c := by omega
  have hcop : Int.gcd (a : ℤ) (b : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]; exact hab
  have hsum : (a : ℤ) + b = c := by exact_mod_cast habc
  have habs : ((a : ℤ) * b * c).natAbs = a * b * c := by
    simp [Int.natAbs_mul]
  have hcor := h ε hε0 hε10 a b c (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne')
    (by exact_mod_cast hc.ne') hcop hsum
  rw [habs] at hcor
  set r := (rad (a * b * c) : ℝ) with hr
  set s := 3 + 3 * ε with hs
  have hr1 : 1 ≤ r := IUT.ABC.one_le_rad_cast _
  have hrs1 : 1 ≤ r ^ s := Real.one_le_rpow hr1 (by linarith)
  have hmax : max E (r ^ s) ≤ E * r ^ s := by
    apply max_le
    · nlinarith
    · nlinarith
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hc2' : (2 : ℝ) ≤ c := by exact_mod_cast hc2
  have hcab : (c : ℝ) = a + b := by exact_mod_cast habc.symm
  have hab' : (c : ℝ) - 1 ≤ (a : ℝ) * b := by nlinarith
  have habc' : (c : ℝ) ^ 2 / 2 ≤ (a : ℝ) * b * c := by nlinarith
  have hcast : (((a * b * c : ℕ)) : ℝ) = (a : ℝ) * b * c := by push_cast; ring
  rw [hcast] at hcor
  have hc2le : (c : ℝ) ^ 2 ≤ 2 * E * r ^ s := by nlinarith
  have hr0 : 0 ≤ r := by linarith
  calc (c : ℝ) = Real.sqrt ((c : ℝ) ^ 2) := (Real.sqrt_sq (by linarith)).symm
    _ ≤ Real.sqrt (2 * E * r ^ s) := Real.sqrt_le_sqrt hc2le
    _ = Real.sqrt (2 * E) * r ^ (s / 2) := by
        rw [Real.sqrt_mul (by linarith), Real.sqrt_eq_rpow (r ^ s), ← Real.rpow_mul hr0]
        ring_nf
    _ ≤ Real.sqrt (2 * E) * r ^ κ := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        exact Real.rpow_le_rpow_of_exponent_le hr1 hεκ

end IUT.Applications.ZhouExplicit
