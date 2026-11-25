import IUT.PaperIV.Theorem1_10.ElementaryFacts
import IUT.PaperIV.Proposition2_1

/-!
# IUT IV, Corollary 2.2: the real arithmetic of (C1), (C2) and of the proof

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Corollary 2.2 and its proof,
pages 41 to 48 of the April 2020 manuscript, read from the extracted text and from the rendered
pages 42 to 48; every display formalized here was checked against the renders.

This file is not a formalization of Corollary 2.2. The corollary constructs initial Θ-data from
a point of a compactly bounded subset of the `λ`-line and applies Theorem 1.10; that uses the
theory of elliptic curves, [GenEll] (Lemma 3.5, Proposition 3.4, Lemma 3.1, Proposition 1.4),
[CanLift] and [IUTchI], none of which is formalized. Every arithmetic fact about the curve is a
hypothesis here; what is checked is the real arithmetic of the proof:

* the bound on `θ_A` (`thetaA_chain`) and the choice of `l` in (P1) (`P1_upper`, `P1_lower`,
  `P1_l_ge_seven`, `P1_bound`), which is condition (C1);
* the boundedness arguments behind (P4) and (P5) (`P4_bound`, `P5_bound`) and the chain
  `h^{1/2}·log(l) ≤ 16·δ^{1/4}·h^{3/4}` (`sqrt_mul_log_l`);
* the application of Theorem 1.10 (`apply_theorem_1_10`), the comparison of `log(𝔮^{∤2})` with
  `log(𝔮)` (`q_not2_step`), the constant `(15δ)²` (`fifteen_delta_step`) and the assembly of the
  bound `(1/6)·h ≤ (1 + ε_E/5)·D + (2/5)·ε_E·(1/6)·h + C_K/2` (`assembly`);
* the lower bound `ε_E ≥ 5·δ·h^{-1/2}` (`epsE_ge`) and the real-power estimate showing that
  `ε < ε_E` bounds `h` (`h_lt_of_eps_lt_epsE`), with the explicit constant `H_unif`
  (`h_bound_Hunif`);
* the final step `(1/6)·h ≤ (1 + ε_E)·D + C_K` for `0 < ε_E ≤ 1` (`final_step`), which is the
  inequality (C2) after `D ≤ log-diff_X(x_E) + log-cond_D(x_E)` (`C2_of_final`).

Notation: `s = h^{1/2}` with `h = s² = log(𝔮^∀)`; `L = log(2δh)`;
`D = log(𝔡^{F_tpd}) + log(𝔣^{F_tpd})`; `Q = log(𝔮)`, `Q2 = log(𝔮^{∤2})`.
-/

namespace IUT.PaperIV.Corollary2_2

open IUT.PaperIV.Theorem1_10

/-- **The bound on `θ_A`** (page 45). If `θ_A ≤ 2s + δs + 2δsL` (the contributions of (S1),
(S3), (S2)), `δ ≥ 2`, `L ≥ 1` and `0 ≤ ξ ≤ s`, then
`θ_A ≤ 4δ·s·L ≤ -ξ + 5δ·s·L`. -/
theorem thetaA_chain {θ s δ L ξ : ℝ} (hδ : 2 ≤ δ) (hL : 1 ≤ L) (hξ : 0 ≤ ξ) (hs : ξ ≤ s)
    (h : θ ≤ 2 * s + δ * s + 2 * δ * s * L) :
    θ ≤ 4 * δ * s * L ∧ θ ≤ -ξ + 5 * δ * s * L := by
  have hs0 : 0 ≤ s := le_trans hξ hs
  have h1 : 2 * s ≤ δ * s * L := by nlinarith [mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ L - 1)]
  have h2 : δ * s ≤ δ * s * L := by nlinarith [mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ δ)]
  have h3 : ξ ≤ δ * s * L := by nlinarith
  constructor <;> linarith

/-- The contribution of (S1): with `ξ ≤ s` and `θ(x) ≤ (4/3)·x` for `x ≥ ξ`, `θ(s) ≤ 2s`. -/
theorem S1_bound {ξ s : ℝ} (hs : ξ ≤ s) (hξ : 0 ≤ ξ)
    (hθ : ∀ x : ℝ, ξ ≤ x → Chebyshev.theta x ≤ 4 / 3 * x) : Chebyshev.theta s ≤ 2 * s := by
  have := hθ s hs; linarith

/-- **(P1), upper bound.** If `l ≤ 2(θ_A + ξ)` (Proposition 2.1 (ii)) and
`θ_A ≤ -ξ + 5δ·s·L`, then `l ≤ 10δ·s·L`. -/
theorem P1_upper {l θ ξ δ s L : ℝ} (hl : l ≤ 2 * (θ + ξ)) (hθ : θ ≤ -ξ + 5 * δ * s * L) :
    l ≤ 10 * δ * s * L := by linarith

/-- **(P1), lower bound.** If every prime `≤ s` lies in `A` (condition (S1)) and the prime `l`
does not, then `s < l`. -/
theorem P1_lower {A : Finset ℕ} {l : ℕ} {s : ℝ} (hS1 : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ s → p ∈ A)
    (hl : l.Prime) (hlA : l ∉ A) : s < l := by
  by_contra h; push Not at h; exact hlA (hS1 l hl h)

/-- **`l ≥ 7`.** Theorem 1.10 in its final form requires `l ≥ 7`. The paper notes on page 22
that `l ≠ 5` follows from [IUTchI] Definition 3.1 (c), since the 5-torsion points are rational
over `F`. Independently, since `5 ≤ s < l` (with `s = h^{1/2}`) and `l` is prime, `l ≥ 7`. -/
theorem P1_l_ge_seven {l : ℕ} {s : ℝ} (hl : l.Prime) (hs : 5 ≤ s) (hsl : s < l) : 7 ≤ l := by
  have h5 : 5 < l := by exact_mod_cast (show (5 : ℝ) < l by linarith)
  by_contra h
  interval_cases l; norm_num at hl

/-- **(P1), parenthetical bound.** `10δ·s·log(2δh) ≤ 20·δ²·h²` for `h = s²`, `s ≥ 1`, `δ ≥ 1`;
uses Proposition 2.1 (i). -/
theorem P1_bound {δ s : ℝ} (hδ : 1 ≤ δ) (hs : 1 ≤ s) :
    10 * δ * s * Real.log (2 * δ * s ^ 2) ≤ 20 * δ ^ 2 * (s ^ 2) ^ 2 := by
  have hx : 1 ≤ 2 * δ * s ^ 2 := by nlinarith
  have hlog := Proposition2_1.log_le_self_of_one_le hx
  have h0 : 0 ≤ 10 * δ * s := by positivity
  have := mul_le_mul_of_nonneg_left hlog h0
  have hs3 : s ^ 3 ≤ s ^ 4 := pow_le_pow_right₀ hs (by norm_num)
  have hδ2 : 0 ≤ δ ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hs3 hδ2
  nlinarith

/-- **(P4), boundedness.** `(l-2)/24·Q ≤ 2·log(l) + T` with `l ≥ 5` and `T ≥ 0` implies
`Q ≤ 48·(1 + T)`; the paper uses `1 ≤ 2·log(l) ≤ 48·(l-2)/24`. -/
theorem P4_bound {l Q T : ℝ} (hl : 5 ≤ l) (hT : 0 ≤ T)
    (h : (l - 2) / 24 * Q ≤ 2 * Real.log l + T) : Q ≤ 48 * (1 + T) := by
  have hl0 : 0 < l := by linarith
  have h1 : 1 ≤ 2 * Real.log l := by
    have := Real.log_le_log (by norm_num) (by linarith : (3 : ℝ) ≤ l)
    linarith [one_le_log_three]
  have h2 : 2 * Real.log l ≤ 2 * (l - 2) := by linarith [two_log_le_self hl0]
  have h3 : 2 * Real.log l + T ≤ (1 + T) * (2 * (l - 2)) := by nlinarith
  have hpos : 0 < (l - 2) / 24 := by linarith
  by_contra hQ; push Not at hQ
  have : (l - 2) / 24 * (48 * (1 + T)) < (l - 2) / 24 * Q := mul_lt_mul_of_pos_left hQ hpos
  nlinarith

/-- **The chain `h^{1/2}·log(l) ≤ 16·δ^{1/4}·h^{3/4}`** (pages 45 and 46), written with
`δ = a⁴`, `h = b⁴` (so `h^{1/2} = b²`). Uses (P1) `l ≤ 20δ²h²`, `20 ≤ 5²`, `5 ≤ 2⁴` and
Proposition 2.1 (i). -/
theorem sqrt_mul_log_l {a b l : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hl0 : 0 < l)
    (hl : l ≤ 20 * (a ^ 4) ^ 2 * (b ^ 4) ^ 2) :
    b ^ 2 * Real.log l ≤ 16 * a * b ^ 3 := by
  have hab : 1 ≤ 2 * a * b := by nlinarith
  -- `l ≤ (2ab)^8`, since `20 ≤ 2^8`.
  have hl8 : l ≤ (2 * a * b) ^ 8 := by
    have : 20 * (a ^ 4) ^ 2 * (b ^ 4) ^ 2 ≤ 2 ^ 8 * a ^ 8 * b ^ 8 := by
      have : 0 ≤ a ^ 8 * b ^ 8 := by positivity
      nlinarith
    calc l ≤ _ := hl
      _ ≤ 2 ^ 8 * a ^ 8 * b ^ 8 := this
      _ = (2 * a * b) ^ 8 := by ring
  have h1 : Real.log l ≤ 8 * Real.log (2 * a * b) := by
    have := Real.log_le_log hl0 hl8
    rwa [Real.log_pow] at this
  have h2 : Real.log (2 * a * b) ≤ 2 * a * b := Proposition2_1.log_le_self_of_one_le hab
  have hb2 : 0 ≤ b ^ 2 := by positivity
  calc b ^ 2 * Real.log l ≤ b ^ 2 * (8 * (2 * a * b)) := by
        apply mul_le_mul_of_nonneg_left _ hb2; linarith
    _ = 16 * a * b ^ 3 := by ring

/-- The paper's intermediate steps of the same chain: `log(20δ²h²) ≤ 2·log(5δh)` and
`log(5δh) ≤ 4·log(2·δ^{1/4}·h^{1/4})`, with `δ = a⁴`, `h = b⁴`. -/
theorem sqrt_mul_log_l_steps {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Real.log (20 * (a ^ 4) ^ 2 * (b ^ 4) ^ 2) ≤ 2 * Real.log (5 * a ^ 4 * b ^ 4) ∧
      Real.log (5 * a ^ 4 * b ^ 4) ≤ 4 * Real.log (2 * a * b) := by
  have ha4 : 0 < a ^ 4 := by positivity
  have hb4 : 0 < b ^ 4 := by positivity
  constructor
  · rw [show (2 : ℝ) * Real.log (5 * a ^ 4 * b ^ 4) = Real.log ((5 * a ^ 4 * b ^ 4) ^ 2) by
      rw [Real.log_pow]; norm_num]
    apply Real.log_le_log (by positivity)
    nlinarith [mul_pos (pow_pos ha4 2) (pow_pos hb4 2)]
  · rw [show (4 : ℝ) * Real.log (2 * a * b) = Real.log ((2 * a * b) ^ 4) by
      rw [Real.log_pow]; norm_num]
    apply Real.log_le_log (by positivity)
    have : (2 * a * b) ^ 4 = 16 * a ^ 4 * b ^ 4 := by ring
    rw [this]; nlinarith [mul_pos ha4 hb4]

/-- **(P5), boundedness.** If `h ≤ B + c·h^{3/4}` with `h ≥ 1` and `B, c ≥ 0`, then `h` is
bounded; written with `h = b⁴`: `b⁴ ≤ B + c·b³` and `b ≥ 1` imply `b ≤ B + c`. -/
theorem P5_bound {b B c : ℝ} (hb : 1 ≤ b) (hB : 0 ≤ B) (h : b ^ 4 ≤ B + c * b ^ 3) :
    b ≤ B + c := by
  have hb3 : 1 ≤ b ^ 3 := one_le_pow₀ hb
  have : b ^ 4 ≤ (B + c) * b ^ 3 := by nlinarith
  have hb3' : 0 < b ^ 3 := by linarith
  have e : b ^ 4 = b * b ^ 3 := by ring
  rw [e] at this
  exact le_of_mul_le_mul_right this hb3'

/-- **Applying Theorem 1.10** (page 46). From the final inequality of Theorem 1.10 with
`E ≤ d*_mod·l + η_prm` (Remark 1.10.7 (i): `e*_mod ≤ d*_mod`), `20·d_mod ≤ d*_mod ≤ δ`,
`s ≤ l ≤ 10δ·s·L` and `D ≥ 0`:
`(1/6)·Q ≤ (1 + δ/s)·D + 200·δ²·s·L + 20·η_prm`. -/
theorem apply_theorem_1_10 {Q D d dstar l E η δ s L : ℝ} (hs : 0 < s) (hD : 0 ≤ D)
    (hd : 0 ≤ d) (hdd : 20 * d ≤ dstar) (hdδ : dstar ≤ δ) (hsl : s ≤ l)
    (hl : l ≤ 10 * δ * s * L) (hE : E ≤ dstar * l + η)
    (h : 1 / 6 * Q ≤ (1 + 20 * d / l) * D + 20 * E) :
    1 / 6 * Q ≤ (1 + δ / s) * D + 200 * δ ^ 2 * s * L + 20 * η := by
  have hl0 : 0 < l := lt_of_lt_of_le hs hsl
  have hδ0 : 0 ≤ δ := by linarith
  have h1 : 20 * d / l ≤ δ / s := by
    rw [div_le_div_iff₀ hl0 hs]; nlinarith
  have h2 : (1 + 20 * d / l) * D ≤ (1 + δ / s) * D := by nlinarith
  have h3 : dstar * l ≤ δ * (10 * δ * s * L) := by
    have hds0 : 0 ≤ dstar := by linarith
    calc dstar * l ≤ δ * l := mul_le_mul_of_nonneg_right hdδ hl0.le
      _ ≤ δ * (10 * δ * s * L) := mul_le_mul_of_nonneg_left hl hδ0
  nlinarith

/-- **The comparison of `log(𝔮^{∤2})` with `log(𝔮)`** (page 47). Given
`(1/6)·Q2 - (1/6)·Q ≤ (1/6)·s·log(l)` (from (P3)) and `s·log(l) ≤ 2·s·log(5δh)`, with
`δ, h ≥ 1` and `5 ≤ 2³`: `(1/6)·Q2 - (1/6)·Q ≤ s·log(2δh)`. -/
theorem q_not2_step {Q Q2 s l δ h : ℝ} (hs : 0 ≤ s) (hδ : 1 ≤ δ) (hh : 1 ≤ h)
    (h1 : 1 / 6 * Q2 - 1 / 6 * Q ≤ 1 / 6 * (s * Real.log l))
    (h2 : s * Real.log l ≤ 2 * s * Real.log (5 * δ * h)) :
    1 / 6 * Q2 - 1 / 6 * Q ≤ s * Real.log (2 * δ * h) := by
  have h3 : Real.log (5 * δ * h) ≤ 3 * Real.log (2 * δ * h) := by
    rw [show (3 : ℝ) * Real.log (2 * δ * h) = Real.log ((2 * δ * h) ^ 3) by
      rw [Real.log_pow]; norm_num]
    apply Real.log_le_log (by positivity)
    have : 1 ≤ δ * h := by nlinarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ δ * h - 1) (by linarith : (0 : ℝ) ≤ δ * h)]
  have := mul_le_mul_of_nonneg_left h3 hs
  nlinarith

/-- **The constant `(15δ)²`** (page 47): `200·δ² + 1 ≤ (15δ)² ≤ (1/6)·(2/5)·(60δ)²` for
`δ ≥ 1`; the second inequality is the paper's "`6·5 ≤ 2·4²`". -/
theorem fifteen_delta_step {δ : ℝ} (hδ : 1 ≤ δ) :
    200 * δ ^ 2 + 1 ≤ (15 * δ) ^ 2 ∧ (15 * δ) ^ 2 ≤ 1 / 6 * (2 / 5) * (60 * δ) ^ 2 := by
  constructor <;> nlinarith

/-- **Assembly of the bound on `(1/6)·h`** (page 47). With `(1/6)·h - (1/6)·Q2 ≤ B` (the bounded
discrepancy `B_K` of assertion (i)), the two preceding steps, `C = 40·η + 2·B`, `h = s²`,
`ε_E = (60δ)²·s⁻¹·L`, and `δ/s ≤ ε_E/5`:
`(1/6)·h ≤ (1 + ε_E/5)·D + (2/5)·ε_E·(1/6)·h + C/2`. -/
theorem assembly {Q Q2 D s δ L η B εE : ℝ} (hs : 0 < s) (hδ : 1 ≤ δ) (hL : 0 ≤ L)
    (hD : 0 ≤ D)
    (hB : 1 / 6 * s ^ 2 - 1 / 6 * Q2 ≤ B)
    (hq2 : 1 / 6 * Q2 - 1 / 6 * Q ≤ s * L)
    (hthm : 1 / 6 * Q ≤ (1 + δ / s) * D + 200 * δ ^ 2 * s * L + 20 * η)
    (hεE : εE = (60 * δ) ^ 2 * s⁻¹ * L) (hδε : δ / s ≤ εE / 5) :
    1 / 6 * s ^ 2 ≤ (1 + εE / 5) * D + 2 / 5 * εE * (1 / 6 * s ^ 2) + (40 * η + 2 * B) / 2 := by
  have h15 := fifteen_delta_step hδ
  have hsL : 0 ≤ s * L := mul_nonneg hs.le hL
  have e : 2 / 5 * εE * (1 / 6 * s ^ 2) = 1 / 6 * (2 / 5) * (60 * δ) ^ 2 * (s * L) := by
    rw [hεE]; field_simp
  have h1 : (200 * δ ^ 2 + 1) * (s * L) ≤ 1 / 6 * (2 / 5) * (60 * δ) ^ 2 * (s * L) :=
    mul_le_mul_of_nonneg_right (h15.1.trans h15.2) hsL
  have h2 : (1 + δ / s) * D ≤ (1 + εE / 5) * D := by nlinarith
  rw [e]; nlinarith

/-- **`ε_E ≥ 5·δ·h^{-1/2}`** (page 47): `(60δ)²·s⁻¹·L ≥ 5δ·s⁻¹` for `δ ≥ 1`, `L ≥ 1`,
`s > 0`. -/
theorem epsE_ge {δ s L : ℝ} (hδ : 1 ≤ δ) (hL : 1 ≤ L) (hs : 0 < s) :
    5 * δ * s⁻¹ ≤ (60 * δ) ^ 2 * s⁻¹ * L := by
  have hs' : 0 < s⁻¹ := inv_pos.mpr hs
  have : 5 * δ ≤ (60 * δ) ^ 2 * L := by nlinarith
  nlinarith

/-- The two estimates of page 47 for `ε*_d = ε_d/16`: `1/(1/2 - ε*_d) = 16/(8 - ε_d) ≤ 3` and
`(2 + ε*_d)/(1/2 - ε*_d) = (32 + ε_d)/(8 - ε_d) ≤ 4 + ε_d ≤ 5`, for `0 < ε_d ≤ 1`. -/
theorem eps_star_estimates {εd : ℝ} (h0 : 0 < εd) (h1 : εd ≤ 1) :
    1 / (1 / 2 - εd / 16) ≤ 3 ∧ (2 + εd / 16) / (1 / 2 - εd / 16) ≤ 4 + εd ∧ 4 + εd ≤ 5 := by
  have hpos : 0 < 1 / 2 - εd / 16 := by linarith
  refine ⟨?_, ?_, by linarith⟩
  · rw [div_le_iff₀ hpos]; linarith
  · rw [div_le_iff₀ hpos]; nlinarith

/-- **The real-power estimate of page 47.** Let `h ≥ 1`, `δ ≥ 1`, `0 < ε_d ≤ 1`,
`ε*_d = ε_d/16` and `0 < ε ≤ 1`. If `ε < ε_E = (60δ)²·h^{-1/2}·log(2δh)`, then
`h < (ε·ε*_d)^{-3}·(60δ)^{4+ε_d}`. For `ε = 1` this is the paper's argument for (ii); for
general `ε` it is the argument for (iii). -/
theorem h_lt_of_eps_lt_epsE {h δ εd ε : ℝ} (hh : 1 ≤ h) (hδ : 1 ≤ δ) (hεd0 : 0 < εd)
    (hεd1 : εd ≤ 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hlt : ε < (60 * δ) ^ 2 * h ^ (-(1 / 2 : ℝ)) * Real.log (2 * δ * h)) :
    h < (ε * (εd / 16)) ^ (-(3 : ℝ)) * (60 * δ) ^ (4 + εd) := by
  set t := εd / 16 with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by linarith
  have hh0 : 0 < h := by linarith
  have hx : 0 < 2 * δ * h := by positivity
  have hM : 1 ≤ 60 * δ := by linarith
  have hM0 : 0 < 60 * δ := by linarith
  -- `log(2δh) ≤ (2δh)^t / t` (Proposition 2.1 (i) applied to `(2δh)^t`).
  have hL : Real.log (2 * δ * h) ≤ (2 * δ * h) ^ t / t := by
    have h1 : Real.log ((2 * δ * h) ^ t) ≤ (2 * δ * h) ^ t := by
      have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx t); linarith
    rw [Real.log_rpow hx] at h1
    rw [le_div_iff₀ ht0]; linarith
  -- `(2δh)^t ≤ (60δ)^t·h^t`.
  have h2 : (2 * δ * h) ^ t ≤ (60 * δ) ^ t * h ^ t := by
    rw [Real.mul_rpow (by positivity) hh0.le]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hh0.le t)
    exact Real.rpow_le_rpow (by positivity) (by linarith) ht0.le
  have hhneg : 0 < h ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hh0 _
  -- `ε < (60δ)^(2+t)·h^(t-1/2) / t`.
  have h3 : ε < (60 * δ) ^ (2 + t) * h ^ (t - 1 / 2) / t := by
    have hc : 0 ≤ (60 * δ) ^ 2 * h ^ (-(1 / 2 : ℝ)) := by positivity
    calc ε < (60 * δ) ^ 2 * h ^ (-(1 / 2 : ℝ)) * Real.log (2 * δ * h) := hlt
      _ ≤ (60 * δ) ^ 2 * h ^ (-(1 / 2 : ℝ)) * ((60 * δ) ^ t * h ^ t / t) := by
          apply mul_le_mul_of_nonneg_left _ hc
          exact hL.trans (div_le_div_of_nonneg_right h2 ht0.le)
      _ = (60 * δ) ^ (2 + t) * h ^ (t - 1 / 2) / t := by
          rw [Real.rpow_add hM0, Real.rpow_two, sub_eq_add_neg, Real.rpow_add hh0]
          ring
  -- `h^(1/2-t) < (60δ)^(2+t) / (ε·t)`.
  set M := (60 * δ) ^ (2 + t) / (ε * t) with hMdef
  have hk : 0 < 1 / 2 - t := by linarith
  have h4 : h ^ (1 / 2 - t) < M := by
    have hp : 0 < h ^ (1 / 2 - t) := Real.rpow_pos_of_pos hh0 _
    have e1 : h ^ (t - 1 / 2) * h ^ (1 / 2 - t) = 1 := by
      rw [← Real.rpow_add hh0]; simp
    rw [hMdef, lt_div_iff₀ (by positivity)]
    have := mul_lt_mul_of_pos_right h3 (mul_pos hp ht0)
    calc h ^ (1 / 2 - t) * (ε * t) = ε * (h ^ (1 / 2 - t) * t) := by ring
      _ < (60 * δ) ^ (2 + t) * h ^ (t - 1 / 2) / t * (h ^ (1 / 2 - t) * t) := this
      _ = (60 * δ) ^ (2 + t) * (h ^ (t - 1 / 2) * h ^ (1 / 2 - t)) := by
          field_simp
      _ = (60 * δ) ^ (2 + t) := by rw [e1, mul_one]
  -- raise to the power `r = 1/(1/2 - t)`.
  set r := 1 / (1 / 2 - t) with hr
  have hr0 : 0 < r := by positivity
  have h5 : h < M ^ r := by
    have := Real.rpow_lt_rpow (Real.rpow_nonneg hh0.le _) h4 hr0
    rwa [← Real.rpow_mul hh0.le, hr, mul_one_div_cancel hk.ne', Real.rpow_one] at this
  have hest := eps_star_estimates hεd0 hεd1
  have hr3 : r ≤ 3 := hest.1
  have hr4 : (2 + t) * r ≤ 4 + εd := by
    rw [hr, mul_one_div]; exact hest.2.1
  have hεt0 : 0 < ε * t := mul_pos hε0 ht0
  have hεt1 : ε * t ≤ 1 := by nlinarith
  have h6 : M ^ r = (60 * δ) ^ ((2 + t) * r) * (ε * t) ^ (-r) := by
    rw [hMdef, Real.div_rpow (by positivity) hεt0.le, ← Real.rpow_mul hM0.le,
      Real.rpow_neg hεt0.le, div_eq_mul_inv]
  have h7 : (60 * δ) ^ ((2 + t) * r) ≤ (60 * δ) ^ (4 + εd) :=
    Real.rpow_le_rpow_of_exponent_le hM hr4
  have h8 : (ε * t) ^ (-r) ≤ (ε * t) ^ (-(3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hεt0 hεt1 (by linarith)
  calc h < M ^ r := h5
    _ = (60 * δ) ^ ((2 + t) * r) * (ε * t) ^ (-r) := h6
    _ ≤ (60 * δ) ^ (4 + εd) * (ε * t) ^ (-(3 : ℝ)) :=
        mul_le_mul h7 h8 (by positivity) (by positivity)
    _ = (ε * t) ^ (-(3 : ℝ)) * (60 * δ) ^ (4 + εd) := by ring

/-- **The explicit constant `H_unif`.** With `δ = 2¹²·3³·5·d` and `d ≥ 1`, the bound of
`h_lt_of_eps_lt_epsE` is at most `H_unif·ε^{-3}·ε_d^{-3}·d^{4+ε_d}` with
`H_unif = 16³·(60·2¹²·3³·5)⁵`, a constant independent of `K_V`, `d`, `ε_d` and `ε`. -/
theorem h_bound_Hunif {d εd ε : ℝ} (hd : 1 ≤ d) (hεd0 : 0 < εd) (hεd1 : εd ≤ 1)
    (hε0 : 0 < ε) :
    (ε * (εd / 16)) ^ (-(3 : ℝ)) * (60 * (2 ^ 12 * 3 ^ 3 * 5 * d)) ^ (4 + εd)
      ≤ 16 ^ 3 * (60 * (2 ^ 12 * 3 ^ 3 * 5)) ^ 5 * ε ^ (-(3 : ℝ)) * εd ^ (-(3 : ℝ))
        * d ^ (4 + εd) := by
  set K : ℝ := 60 * (2 ^ 12 * 3 ^ 3 * 5) with hK
  have hK1 : 1 ≤ K := by norm_num [hK]
  have hd0 : 0 < d := by linarith
  have e1 : (60 * (2 ^ 12 * 3 ^ 3 * 5 * d) : ℝ) = K * d := by rw [hK]; ring
  have e2 : (ε * (εd / 16)) ^ (-(3 : ℝ)) = 16 ^ 3 * ε ^ (-(3 : ℝ)) * εd ^ (-(3 : ℝ)) := by
    rw [Real.mul_rpow hε0.le (by positivity), Real.div_rpow hεd0.le (by norm_num)]
    rw [show (16 : ℝ) ^ (-(3 : ℝ)) = (16 ^ 3)⁻¹ by
      rw [Real.rpow_neg (by norm_num)]; norm_num]
    field_simp
  have h3 : K ^ (4 + εd) ≤ K ^ (5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hK1 (by linarith)
  rw [e1, e2, Real.mul_rpow (by positivity) hd0.le]
  rw [show K ^ (5 : ℝ) = K ^ (5 : ℕ) by norm_cast] at h3
  have hp : 0 ≤ 16 ^ 3 * ε ^ (-(3 : ℝ)) * εd ^ (-(3 : ℝ)) := by positivity
  have hdp : 0 ≤ d ^ (4 + εd) := by positivity
  calc 16 ^ 3 * ε ^ (-(3 : ℝ)) * εd ^ (-(3 : ℝ)) * (K ^ (4 + εd) * d ^ (4 + εd))
      ≤ 16 ^ 3 * ε ^ (-(3 : ℝ)) * εd ^ (-(3 : ℝ)) * (K ^ 5 * d ^ (4 + εd)) := by
        apply mul_le_mul_of_nonneg_left _ hp
        exact mul_le_mul_of_nonneg_right h3 hdp
    _ = 16 ^ 3 * K ^ 5 * ε ^ (-(3 : ℝ)) * εd ^ (-(3 : ℝ)) * d ^ (4 + εd) := by ring

/-- **The final step** (page 48). For `0 < ε ≤ 1`, `D, C ≥ 0` and
`(1/6)·h ≤ (1 + ε/5)·D + (2/5)·ε·(1/6)·h + C/2`, one has `(1/6)·h ≤ (1 + ε)·D + C`, by
`(1 + ε/5)/(1 - 2ε/5) ≤ 1 + ε` and `1 - 2ε/5 ≥ 1/2`. -/
theorem final_step {H D C ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (h : 1 / 6 * H ≤ (1 + ε / 5) * D + 2 / 5 * ε * (1 / 6 * H) + C / 2) :
    1 / 6 * H ≤ (1 + ε) * D + C := by
  have hk : 1 / 2 ≤ 1 - 2 / 5 * ε := by linarith
  have h1 : (1 - 2 / 5 * ε) * (1 / 6 * H) ≤ (1 + ε / 5) * D + C / 2 := by linarith
  have h2 : (1 + ε / 5) * D ≤ (1 - 2 / 5 * ε) * ((1 + ε) * D) := by
    have : 1 + ε / 5 ≤ (1 - 2 / 5 * ε) * (1 + ε) := by nlinarith
    nlinarith
  have h3 : C / 2 ≤ (1 - 2 / 5 * ε) * C := by nlinarith
  have h4 : (1 - 2 / 5 * ε) * (1 / 6 * H) ≤ (1 - 2 / 5 * ε) * ((1 + ε) * D + C) := by
    nlinarith
  exact le_of_mul_le_mul_left h4 (by linarith)

/-- **(C2) from the final step.** With `log-diff_X(x_E) = log(𝔡^{F_tpd})` and
`log(𝔣^{F_tpd}) ≤ log-cond_D(x_E)` (stated in Corollary 2.2 (ii)) and `1 + ε ≥ 0`, the bound
on `log(𝔡^{F_tpd}) + log(𝔣^{F_tpd})` becomes the bound of (C2). -/
theorem C2_of_final {H dF fF logdiff logcond C ε : ℝ} (hε : 0 ≤ 1 + ε)
    (hdiff : logdiff = dF) (hcond : fF ≤ logcond)
    (h : 1 / 6 * H ≤ (1 + ε) * (dF + fF) + C) :
    1 / 6 * H ≤ (1 + ε) * (logdiff + logcond) + C := by
  subst hdiff; nlinarith

end IUT.PaperIV.Corollary2_2
