import IUT.PaperIV.Theorem1_10.Arithmetic
import IUT.PaperIV.Proposition1_7

/-!
# IUT IV, Theorem 1.10, Steps (v) and (vii): weighted averages and procession-normalized bounds

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, proof of Theorem 1.10, Steps (v)
and (vii), pages 27 to 30 of the April 2020 manuscript, read from the extracted text and from
the rendered pages; every display formalized here was checked against the renders of pages 28,
29 and 30.

This file is not a formalization of Steps (v) and (vii). Those steps apply Propositions 1.4 and
1.5 to the tensor packets of log-shells of IUT III, Theorem 3.11, and that application is not
formalized. Here the local log-volume bounds are real variables, and what is checked is the
arithmetic the paper performs on them:

* the bound `∑_{i ∈ I*} {3 + log(e_i)} ≤ 4(j+1)·l*_mod` that turns the second inequality of
  Proposition 1.4 (iii) into the third display of page 28, given (R4) (`sum_Istar_le`);
* the passage to weighted averages via Proposition 1.7, including the fact that the weighted
  average of the local quantities `log(𝔡^K_v)` with weights `[(F_mod)_v : ℚ_{v_ℚ}]` is
  `log(𝔡^K_{v_ℚ})` when these are normalized as in Definition 1.9 (ii) with the unnormalized
  degree in the numerator (`weighted_average_normalized`);
* the "procession-normalized upper bound": averaging over `j ∈ {1, …, l*}` with (E1), (E2)
  (`procession_average`), its rewriting with `l* = (l-1)/2` (`procession_average_l`), and the
  final inequality of Step (v) (`step_v_final`);
* the averaging of Step (vii) (`step_vii_average`).

Step (vi) (page 29) is in `StepsIVtoVII.lean`: the container `(R_I)^∼` with log-volume `0`
for any number of factors (`stepsVI_packet_container`), the inclusion of Proposition 1.4 (iv)
for two factors (`stepsVI_two_factors`), and the procession-normalized bound `0`
(`stepsVI_procession_le_zero`).

Notation: `n` is `l* = (l-1)/2`, a natural number with `l = 2n+1`; `A = log(𝔡^K_{v_ℚ})`,
`B = log(𝔮_{v_ℚ})`, `C = log(𝔰^ℚ_{v_ℚ})`, `T = l*_mod·log(𝔰^≤_{v_ℚ})`, `L = l*_mod`.
-/

open Finset

namespace IUT.PaperIV.Theorem1_10

/-- Page 28: if every `i ∈ I*` satisfies `log(e_i) ≤ -3 + 4·l*_mod` (this is (R4)), `I* ⊆ I`
and `|I| = j+1`, then `∑_{i ∈ I*} {3 + log(e_i)} ≤ 4(j+1)·l*_mod`. Needs `l*_mod ≥ 0`, which
holds since `l*_mod = log(e*_mod·l)` and `e*_mod·l ≥ 1`. -/
theorem sum_Istar_le {ι : Type*} {I Istar : Finset ι} {loge : ι → ℝ} {L : ℝ} {j : ℕ}
    (hsub : Istar ⊆ I) (hcard : I.card = j + 1) (hL : 0 ≤ L)
    (hR4 : ∀ i ∈ Istar, loge i ≤ -3 + 4 * L) :
    ∑ i ∈ Istar, (3 + loge i) ≤ 4 * (j + 1) * L := by
  have h1 : ∑ i ∈ Istar, (3 + loge i) ≤ ∑ _i ∈ Istar, 4 * L :=
    Finset.sum_le_sum fun i hi => by linarith [hR4 i hi]
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  have h2 : (Istar.card : ℝ) ≤ j + 1 := by
    have := Finset.card_le_card hsub; rw [hcard] at this; exact_mod_cast this
  nlinarith

/-- The weighted average used in Step (v), with the normalization of Definition 1.9 (ii).
For each `v` over `v_ℚ` let `N v` be the unnormalized degree of the portion over `v` of an
arithmetic divisor on `K`, `λ v = [(F_mod)_v : ℚ_{v_ℚ}] > 0`, and `κ = [K : F_mod] > 0`, so that
`∑_{w | v} [K_w : ℚ_{v_ℚ}] = κ·λ v`. The local quantity is `x v = N v / (κ·λ v)`. Then the
`λ`-weighted average of `x` is `(∑_v N v) / (κ·∑_v λ v)`, which is the quantity at `v_ℚ` (with
`∑_v λ v = [F_mod : ℚ]` and `κ·[F_mod : ℚ] = [K : ℚ]`). -/
theorem weighted_average_normalized {ι : Type*} [Fintype ι] [Nonempty ι] (N lam : ι → ℝ)
    (κ : ℝ) (hκ : 0 < κ) (hlam : ∀ v, 0 < lam v) :
    Proposition1_7.betaAvg lam (fun v => N v / (κ * lam v)) = (∑ v, N v) / (κ * ∑ v, lam v) := by
  unfold Proposition1_7.betaAvg
  have : ∀ v, N v / (κ * lam v) * lam v = N v / κ := by
    intro v; have := (hlam v).ne'; field_simp
  simp_rw [this, ← Finset.sum_div]
  rw [div_div]

/-- Linearity of the weighted average, used to pass from the bound `β_e` of page 28 to the
"weighted average upper bound": `avg(a·f + b·g + c) = a·avg(f) + b·avg(g) + c`. -/
theorem betaAvg_affine {ι : Type*} [Fintype ι] [Nonempty ι] (lam f g : ι → ℝ) (a b c : ℝ)
    (hlam : ∀ v, 0 < lam v) :
    Proposition1_7.betaAvg lam (fun v => a * f v + b * g v + c)
      = a * Proposition1_7.betaAvg lam f + b * Proposition1_7.betaAvg lam g + c := by
  unfold Proposition1_7.betaAvg
  have hL : 0 < ∑ v, lam v := Finset.sum_pos (fun v _ => hlam v) univ_nonempty
  have e : ∑ v, (a * f v + b * g v + c) * lam v
      = a * ∑ v, f v * lam v + b * ∑ v, g v * lam v + c * ∑ v, lam v := by
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  rw [e]; field_simp

/-- **The "weighted average upper bound" of Step (v)** (last display of page 28). With
`β_v = A_v - j²/(2l(j+1))·B_v + 1/(j+1)·log(p) + 4·ι·L` (page 28), Proposition 1.7 with
`n = j+1` gives, for every index `i`, that the weighted average of the symmetrized bound
`β_e⃗` equals
`(j+1)·avg(A) - j²/(2l)·avg(B) + log(p) + 4(j+1)·ι·L`. -/
theorem step_v_weighted {ι : Type*} [Fintype ι] [Nonempty ι] (lam Aloc Bloc : ι → ℝ)
    (hlam : ∀ v, 0 < lam v) (j : ℕ) (l logp iota L : ℝ) (hl : l ≠ 0) (i : Fin (j + 1)) :
    (∑ v : Fin (j + 1) → ι,
        Proposition1_7.betaVec
          (fun w => Aloc w - (j : ℝ) ^ 2 / (2 * l * (j + 1)) * Bloc w
            + 1 / (j + 1) * logp + 4 * iota * L) v * Proposition1_7.lamProd lam v)
      / (∑ v : Fin (j + 1) → ι, Proposition1_7.lamProd lam v)
      = (j + 1) * Proposition1_7.betaAvg lam Aloc
        - (j : ℝ) ^ 2 / (2 * l) * Proposition1_7.betaAvg lam Bloc
        + logp + 4 * (j + 1) * iota * L := by
  have h := (Proposition1_7.weighted_averages (n := j + 1) (by omega) lam
    (fun w => Aloc w - (j : ℝ) ^ 2 / (2 * l * (j + 1)) * Bloc w
      + 1 / (j + 1) * logp + 4 * iota * L) hlam i)
  rw [h.1, h.2]
  have e := betaAvg_affine lam Aloc Bloc 1 (-((j : ℝ) ^ 2 / (2 * l * (j + 1))))
    (1 / (j + 1) * logp + 4 * iota * L) hlam
  have e' : (fun w => Aloc w - (j : ℝ) ^ 2 / (2 * l * (j + 1)) * Bloc w
      + 1 / (j + 1) * logp + 4 * iota * L)
      = (fun w => 1 * Aloc w + -((j : ℝ) ^ 2 / (2 * l * (j + 1))) * Bloc w
      + (1 / (j + 1) * logp + 4 * iota * L)) := by
    funext w; ring
  rw [e', e]
  push_cast
  field_simp
  ring

/-- Closed form of the sum over `j` used in the procession-normalized bound. -/
theorem procession_sum (A B C T l : ℝ) (k : ℕ) :
    ∑ j ∈ Icc 1 k, (((j : ℝ) + 1) * A - (j : ℝ) ^ 2 / (2 * l) * B + C + 4 * ((j : ℝ) + 1) * T)
      = k * (k + 3) / 2 * A - k * (k + 1) * (2 * k + 1) / (12 * l) * B + k * C
        + 2 * k * (k + 3) * T := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]; push_cast; ring

/-- **First line of the display of page 29.** Averaging the weighted average upper bound over
`j ∈ {1, …, l*}` with (E1), (E2):
`(1/l*)·∑_{j=1}^{l*} [(j+1)A - j²/(2l)·B + C + 4(j+1)T]
  = (l*+3)/2·A - (2l*+1)(l*+1)/(12l)·B + C + 2(l*+3)·T`. -/
theorem procession_average (A B C T l : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    1 / (n : ℝ) * ∑ j ∈ Icc 1 n,
        (((j : ℝ) + 1) * A - (j : ℝ) ^ 2 / (2 * l) * B + C + 4 * ((j : ℝ) + 1) * T)
      = (n + 3) / 2 * A - (2 * n + 1) * (n + 1) / (12 * l) * B + C + 2 * (n + 3) * T := by
  rw [procession_sum]
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Second line of the display of page 29.** With `l = 2·l* + 1`:
`(l*+3)/2 = (l+5)/4`, `(2l*+1)(l*+1)/(12l) = (l+1)/24`, `2(l*+3) = l+5`. -/
theorem procession_average_l (A B C T : ℝ) (n : ℕ) :
    ((n : ℝ) + 3) / 2 * A - (2 * n + 1) * (n + 1) / (12 * (2 * n + 1)) * B + C
        + 2 * (n + 3) * T
      = ((2 * n + 1) + 5) / 4 * A - ((2 * n + 1) + 1) / 24 * B + C + ((2 * n + 1) + 5) * T := by
  have : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  field_simp; ring

/-- **Third line of the display of page 29 (final inequality of Step (v)).** Using
`1/(l+1) ≤ 1/l` and `4(l+5)/(l+1) ≤ 20/3`, "consequences of the fact that `l ≥ 5`":
`(l+5)/4·A - (l+1)/24·B + C + (l+5)·T
  ≤ (l+1)/4·{(1 + 4/l)·A - 1/6·B + 4/l·C + 20/3·T}`.
The inequality needs `A, C, T ≥ 0`; in the paper these are `log(𝔡^K_{v_ℚ})`,
`log(𝔰^ℚ_{v_ℚ})` and `l*_mod·log(𝔰^≤_{v_ℚ})`, all nonnegative by definition. -/
theorem step_v_final {A B C T l : ℝ} (hl : 5 ≤ l) (hA : 0 ≤ A) (hC : 0 ≤ C) (hT : 0 ≤ T) :
    (l + 5) / 4 * A - (l + 1) / 24 * B + C + (l + 5) * T
      ≤ (l + 1) / 4 * ((1 + 4 / l) * A - 1 / 6 * B + 4 / l * C + 20 / 3 * T) := by
  have hl0 : 0 < l := by linarith
  have eA : (l + 1) / 4 * ((1 + 4 / l) * A) - (l + 5) / 4 * A = A / l := by
    field_simp; ring
  have eC : (l + 1) / 4 * (4 / l * C) - C = C / l := by field_simp; ring
  have eT : (l + 1) / 4 * (20 / 3 * T) - (l + 5) * T = (2 * l - 10) / 3 * T := by ring
  have h1 : 0 ≤ A / l := div_nonneg hA hl0.le
  have h2 : 0 ≤ C / l := div_nonneg hC hl0.le
  have h3 : 0 ≤ (2 * l - 10) / 3 * T := mul_nonneg (by linarith) hT
  nlinarith

/-- **Step (vii), averaging.** With local bound `(j+1)·log(π)`, the procession-normalized bound
is `(l*+3)/2·log(π) = (l+5)/4·log(π)` for `l = 2l*+1`; the existing theorem
`step_vii_archimedean` then gives `≤ (l+1)/4·4`. -/
theorem step_vii_average (n : ℕ) (hn : 1 ≤ n) :
    1 / (n : ℝ) * ∑ j ∈ Icc 1 n, ((j : ℝ) + 1) * Real.log Real.pi
      = ((2 * n + 1) + 5) / 4 * Real.log Real.pi := by
  have := procession_average (Real.log Real.pi) 0 0 0 1 n hn
  simp only [mul_zero, sub_zero, add_zero] at this
  rw [this]; ring

end IUT.PaperIV.Theorem1_10
