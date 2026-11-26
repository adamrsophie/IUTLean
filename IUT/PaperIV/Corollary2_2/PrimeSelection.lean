import IUT.PaperIV.Corollary2_2.Arithmetic

/-!
# IUT IV, Corollary 2.2: the choice of the prime `l`

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, the proof of Corollary 2.2,
pages 44 and 45 of the April 2020 manuscript (the choice of `l`, conditions (P1), (P2), (P3)),
with Proposition 2.1 on page 40 for `ξ_prm` and the prime estimate. Pages read for this file:
40, 43, 44, 45, 46; all of them were checked against rendered images, and every display used
here was transcribed from the render.

This file is not a formalization of Corollary 2.2. On the page, `h = log(𝔮^∀)` is attached to an
elliptic curve `E_F` over a number field `F`; `h_v` is the local height of `E_F` at the
nonarchimedean place `v` (zero at places of good reduction), `p_v` the residue characteristic,
and `δ` a bound on `[F : ℚ]` from properties (E3), (E4), (E5) of the proof of Theorem 1.10.
Here all of these are plain numbers: a finite index type `V` of places, a prime `p v`, a natural
number `hv v`, a positive natural `f v` for each `v`, a natural `n` (for `[F : ℚ]`) and a real
`δ`, with

  `h = (1/n)·∑_v hv v · f v · log(p v)`        (page 44, the definition of `h`).

What is checked is the arithmetic of pages 44 and 45: under the printed numerical hypotheses
`h^{1/2} ≥ ξ_prm ≥ 5`, `[F : ℚ] ≤ δ` and `δ ≥ 2`, the set `A` of primes that (S1) are `≤ h^{1/2}`,
(S2) divide a nonzero `h_v`, or (S3) equal `p_v` for some `v` with `h_v ≥ h^{1/2}` has
`θ_A ≤ -ξ_prm + 5δ·h^{1/2}·log(2δh)`, so that Proposition 2.1 (ii) gives a prime `l ∉ A` with

* (P1) `(5 ≤) h^{1/2} ≤ l ≤ 10δ·h^{1/2}·log(2δh) (≤ 20·δ²·h²)`;
* (P2) `l` divides no nonzero `h_v`;
* (P3) if `l = p_v`, then `h_v < h^{1/2}`.

The page bounds the (S2) part only through the primes dividing some `h_v ≥ h^{1/2}`; that the
remaining primes of (S2) lie in (S1) is left implicit on the page and is proved here
(`primeSel_A_subset`). Proposition 2.1 (ii) is used through `Proposition2_1.lean`; no further
prime number estimate is needed.

Main results: `primeSel_exists_prime_of` (for any `ξ ≥ 5` with the two bounds of
Proposition 2.1 (ii)) and `primeSel_exists_prime` (with the `ξ_prm` provided by
`Proposition2_1.exists_xi_prm`). Nonvacuity: `primeSel_hypotheses_satisfiable`.

Not proved: nothing that the page proves in this passage is left out. Not addressed: the link of
the numbers `h`, `h_v`, `p_v`, `f_v`, `n`, `δ` with an elliptic curve, and the enlargement of the
exceptional set that makes `h^{1/2} ≥ ξ_prm` hold (page 44, via [GenEll] Proposition 1.4 (iv)).
-/

namespace IUT.PaperIV.Corollary2_2

open Finset

/-! ### The data and the sets (S1), (S2), (S3) -/

/-- The quantity `h = (1/[F:ℚ])·∑_v h_v·f_v·log(p_v)` of page 44, for numerical data. -/
noncomputable def primeSelHeight {V : Type*} [Fintype V] (p hv f : V → ℕ) (n : ℕ) : ℝ :=
  1 / (n : ℝ) * ∑ v, (hv v : ℝ) * f v * Real.log (p v)

/-- (S1): the primes `≤ s`, written as in the definition of `Chebyshev.theta`. -/
noncomputable def primeSelS1 (s : ℝ) : Finset ℕ := {q ∈ Ioc 0 ⌊s⌋₊ | q.Prime}

/-- (S2): the primes dividing some nonzero `h_v` (`primeFactors 0 = ∅`). -/
def primeSelS2 {V : Type*} [Fintype V] (hv : V → ℕ) : Finset ℕ :=
  univ.biUnion fun v => (hv v).primeFactors

/-- The places with `h_v ≥ s`. -/
noncomputable def primeSelBig {V : Type*} [Fintype V] (hv : V → ℕ) (s : ℝ) : Finset V :=
  {v | s ≤ (hv v : ℝ)}

/-- (S3): the primes equal to `p_v` for some `v` with `h_v ≥ s`. -/
noncomputable def primeSelS3 {V : Type*} [Fintype V] (p hv : V → ℕ) (s : ℝ) : Finset ℕ :=
  (primeSelBig hv s).image p

/-- The set `A` of page 44: primes in (S1), (S2) or (S3), with `s = h^{1/2}`. -/
noncomputable def primeSelA {V : Type*} [Fintype V] (p hv : V → ℕ) (s : ℝ) : Finset ℕ :=
  primeSelS1 s ∪ primeSelS2 hv ∪ primeSelS3 p hv s

/-- The part of (S2) that the page estimates: primes dividing some `h_v ≥ s`. -/
noncomputable def primeSelS2big {V : Type*} [Fintype V] (hv : V → ℕ) (s : ℝ) : Finset ℕ :=
  (primeSelBig hv s).biUnion fun v => (hv v).primeFactors

/-! ### Elementary sum estimates -/

/-- A sum of nonnegative terms over a union is at most the sum of the two sums. -/
theorem primeSel_sum_union_le (A B : Finset ℕ) {g : ℕ → ℝ} (hg : ∀ q, 0 ≤ g q) :
    ∑ q ∈ A ∪ B, g q ≤ ∑ q ∈ A, g q + ∑ q ∈ B, g q := by
  have := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := g)
  have h0 : 0 ≤ ∑ q ∈ A ∩ B, g q := sum_nonneg fun q _ => hg q
  linarith

/-- A sum of nonnegative terms over a `biUnion` is at most the double sum. -/
theorem primeSel_sum_biUnion_le {κ : Type*} (s : Finset κ) (t : κ → Finset ℕ) {g : ℕ → ℝ}
    (hg : ∀ q, 0 ≤ g q) : ∑ q ∈ s.biUnion t, g q ≤ ∑ i ∈ s, ∑ q ∈ t i, g q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    exact (primeSel_sum_union_le _ _ hg).trans (by linarith)

/-- `∑_{q ∣ m} log(q) ≤ log(m)` for `m ≠ 0`, the sum over the distinct prime factors. -/
theorem primeSel_sum_log_primeFactors_le {m : ℕ} (hm : m ≠ 0) :
    ∑ q ∈ m.primeFactors, Real.log q ≤ Real.log m := by
  have hne : ∀ q ∈ m.primeFactors, ((q : ℕ) : ℝ) ≠ 0 := fun q hq => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hq).ne_zero
  rw [← Real.log_prod hne, ← Nat.cast_prod]
  have hpos : 0 < ∏ q ∈ m.primeFactors, q :=
    Finset.prod_pos fun q hq => (Nat.prime_of_mem_primeFactors hq).pos
  apply Real.log_le_log (by exact_mod_cast hpos)
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.prod_primeFactors_dvd m)

/-- Each term `h_v·f_v·log(p_v)` is nonnegative. -/
theorem primeSel_term_nonneg {V : Type*} {p hv f : V → ℕ} (v : V) :
    0 ≤ (hv v : ℝ) * f v * Real.log (p v) := by
  have := Real.log_natCast_nonneg (p v); positivity

/-! ### The two chains of page 44 -/

section Chains

variable {V : Type*} [Fintype V] (p hv f : V → ℕ) (n : ℕ)

/-- `[F:ℚ]·h = ∑_v h_v·f_v·log(p_v)` for `[F:ℚ] ≠ 0`. -/
theorem primeSel_sum_eq (hn : n ≠ 0) :
    ∑ v, (hv v : ℝ) * f v * Real.log (p v) = n * primeSelHeight p hv f n := by
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [primeSelHeight]; field_simp

/-- `n ≠ 0` as soon as `h > 0` (with `n = 0`, the formula gives `h = 0`). -/
theorem primeSel_n_ne_zero (hh : 0 < primeSelHeight p hv f n) : n ≠ 0 := by
  rintro rfl; simp [primeSelHeight] at hh

variable {p hv f n}

/-- **First chain of page 44.** With `s = h^{1/2}` and `[F:ℚ] ≤ δ`:
`δ·h^{1/2} ≥ [F:ℚ]·h^{1/2} = ∑_v h^{-1/2}·h_v·f_v·log(p_v) ≥ ∑_{h_v ≥ h^{1/2}} log(p_v)`. -/
theorem primeSel_S3_sum_le {δ : ℝ} (hf : ∀ v, 0 < f v) (hnδ : (n : ℝ) ≤ δ)
    (hh : 0 < primeSelHeight p hv f n) :
    ∑ v ∈ primeSelBig hv (Real.sqrt (primeSelHeight p hv f n)), Real.log (p v)
      ≤ δ * Real.sqrt (primeSelHeight p hv f n) := by
  set h := primeSelHeight p hv f n with hhdef
  set s := Real.sqrt h with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hh
  have hsq : s ^ 2 = h := Real.sq_sqrt hh.le
  have hn := primeSel_n_ne_zero p hv f n hh
  -- termwise: `log(p_v)·s ≤ h_v·f_v·log(p_v)` when `h_v ≥ s`
  have hterm : ∀ v ∈ primeSelBig hv s,
      Real.log (p v) * s ≤ (hv v : ℝ) * f v * Real.log (p v) := by
    intro v hv'
    have hvs : s ≤ (hv v : ℝ) := by simpa [primeSelBig] using hv'
    have hlog := Real.log_natCast_nonneg (p v)
    have hf1 : (1 : ℝ) ≤ f v := by exact_mod_cast hf v
    have hv0 : (0 : ℝ) ≤ hv v := by positivity
    calc Real.log (p v) * s ≤ Real.log (p v) * hv v := mul_le_mul_of_nonneg_left hvs hlog
      _ ≤ Real.log (p v) * (hv v * f v) := by
          apply mul_le_mul_of_nonneg_left _ hlog; nlinarith
      _ = _ := by ring
  have h1 : (∑ v ∈ primeSelBig hv s, Real.log (p v)) * s
      ≤ ∑ v, (hv v : ℝ) * f v * Real.log (p v) := by
    rw [Finset.sum_mul]
    exact (Finset.sum_le_sum hterm).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun v _ _ => primeSel_term_nonneg v)
  rw [primeSel_sum_eq p hv f n hn, ← hhdef, ← hsq] at h1
  have h2 : (n : ℝ) * s ^ 2 ≤ δ * s * s := by
    have := mul_le_mul_of_nonneg_right hnδ (sq_nonneg s); nlinarith
  exact le_of_mul_le_mul_right (by nlinarith) hs0

/-- **Second chain of page 44.** With `s = h^{1/2}`, `[F:ℚ] ≤ δ`, `1 ≤ δ` and `h^{1/2} ≥ 1`:
`2δ·h^{1/2}·log(2δh) ≥ ∑_{h_v ≠ 0} 2·h^{-1/2}·log(2·h_v·f_v·log(p_v))·h_v·f_v·log(p_v)
≥ ∑_{h_v ≥ h^{1/2}} log(h_v)`, using `2·log(p_v) ≥ log(4) ≥ 1` (property (E6)). -/
theorem primeSel_S2_sum_le {δ : ℝ} (hp : ∀ v, (p v).Prime) (hf : ∀ v, 0 < f v)
    (hnδ : (n : ℝ) ≤ δ) (hδ : 1 ≤ δ) (hs1 : 1 ≤ Real.sqrt (primeSelHeight p hv f n)) :
    ∑ v ∈ primeSelBig hv (Real.sqrt (primeSelHeight p hv f n)), Real.log (hv v)
      ≤ 2 * δ * Real.sqrt (primeSelHeight p hv f n)
          * Real.log (2 * δ * primeSelHeight p hv f n) := by
  set h := primeSelHeight p hv f n with hhdef
  set s := Real.sqrt h with hsdef
  set L := Real.log (2 * δ * h) with hLdef
  have hs0 : 0 < s := by linarith
  have hh : 0 < h := Real.sqrt_pos.mp hs0
  have hsq : s ^ 2 = h := Real.sq_sqrt hh.le
  have hh1 : 1 ≤ h := by nlinarith
  have hn := primeSel_n_ne_zero p hv f n hh
  have hsum := primeSel_sum_eq p hv f n hn
  rw [← hhdef] at hsum
  set Y : V → ℝ := fun v => (hv v : ℝ) * f v * Real.log (p v) with hY
  have hY0 : ∀ v, 0 ≤ Y v := fun v => primeSel_term_nonneg v
  have hYle : ∀ v, Y v ≤ n * h := fun v => by
    rw [← hsum]
    exact Finset.single_le_sum (f := Y) (fun w _ => hY0 w) (mem_univ v)
  have hnh : (n : ℝ) * h ≤ δ * h := mul_le_mul_of_nonneg_right hnδ hh.le
  have hL0 : 0 ≤ L := Real.log_nonneg (by nlinarith)
  -- termwise: `log(h_v)·s ≤ 2·L·h_v·f_v·log(p_v)` when `h_v ≥ s`
  have hterm : ∀ v ∈ primeSelBig hv s, Real.log (hv v) * s ≤ 2 * L * Y v := by
    intro v hv'
    have hvs : s ≤ (hv v : ℝ) := by simpa [primeSelBig] using hv'
    have hv1 : (1 : ℝ) ≤ hv v := by
      have : 0 < hv v := by exact_mod_cast hs0.trans_le hvs
      exact_mod_cast this
    have hf1 : (1 : ℝ) ≤ f v := by exact_mod_cast hf v
    -- `2·f_v·log(p_v) ≥ 2·log(2) ≥ 1`
    have hlp : Real.log 2 ≤ Real.log (p v) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (hp v).two_le)
    have hc : 1 ≤ 2 * (f v * Real.log (p v)) := by
      have := Real.log_two_gt_d9
      have h0 : 0 ≤ Real.log (p v) := by linarith
      nlinarith
    have hYv : Y v = hv v * (f v * Real.log (p v)) := by rw [hY]; ring
    -- `X = 2·h_v·f_v·log(p_v)` satisfies `h_v ≤ X ≤ 2δh`
    have hX1 : (hv v : ℝ) ≤ 2 * Y v := by rw [hYv]; nlinarith
    have hX2 : 2 * Y v ≤ 2 * δ * h := by nlinarith [hYle v]
    have hlogX : Real.log (hv v) ≤ Real.log (2 * Y v) := Real.log_le_log (by linarith) hX1
    have hlogXL : Real.log (2 * Y v) ≤ L := Real.log_le_log (by linarith) hX2
    have hloghv : 0 ≤ Real.log (hv v) := Real.log_nonneg hv1
    calc Real.log (hv v) * s ≤ Real.log (hv v) * hv v := mul_le_mul_of_nonneg_left hvs hloghv
      _ ≤ Real.log (2 * Y v) * (2 * Y v) := mul_le_mul hlogX hX1 (by linarith) (by linarith)
      _ ≤ L * (2 * Y v) := mul_le_mul_of_nonneg_right hlogXL (by linarith [hY0 v])
      _ = 2 * L * Y v := by ring
  have h1 : (∑ v ∈ primeSelBig hv s, Real.log (hv v)) * s ≤ 2 * L * (n * h) := by
    rw [Finset.sum_mul, ← hsum, Finset.mul_sum]
    exact (Finset.sum_le_sum hterm).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _)
        fun v _ _ => mul_nonneg (by linarith) (hY0 v))
  have h2 : 2 * L * (n * h) ≤ 2 * δ * s * L * s := by
    rw [← hsq] at hnh ⊢; nlinarith
  exact le_of_mul_le_mul_right (h1.trans h2) hs0

end Chains

/-! ### The set `A` and the bound on `θ_A` (page 45) -/

/-- The bridge left implicit on page 44: a prime dividing a nonzero `h_v < s` is `≤ s`, hence in
(S1); so `A ⊆ (S1) ∪ (S2 restricted to h_v ≥ s) ∪ (S3)`. -/
theorem primeSel_A_subset {V : Type*} [Fintype V] (p hv : V → ℕ) (s : ℝ) :
    primeSelA p hv s ⊆ primeSelS1 s ∪ primeSelS2big hv s ∪ primeSelS3 p hv s := by
  intro q hq
  simp only [primeSelA, Finset.mem_union] at hq ⊢
  rcases hq with (hq | hq) | hq
  · exact Or.inl (Or.inl hq)
  · obtain ⟨v, -, hqv⟩ := Finset.mem_biUnion.mp hq
    by_cases hvs : s ≤ (hv v : ℝ)
    · exact Or.inl (Or.inr (Finset.mem_biUnion.mpr ⟨v, by simpa [primeSelBig] using hvs, hqv⟩))
    · push Not at hvs
      left; left
      have hqle : q ≤ hv v := Nat.le_of_mem_primeFactors hqv
      have hqp := Nat.prime_of_mem_primeFactors hqv
      simp only [primeSelS1, Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨hqp.pos, Nat.le_floor ?_⟩, hqp⟩
      exact (show (q : ℝ) ≤ hv v by exact_mod_cast hqle).trans hvs.le
  · exact Or.inr hq

/-- **The bound on `θ_A`, first line of page 45.** Under the hypotheses of page 44 (`s = h^{1/2}`
with `ξ ≤ s` and `θ(x) ≤ (4/3)·x` for `x ≥ ξ ≥ 1`, `[F:ℚ] ≤ δ`, `1 ≤ δ`):
`θ_A ≤ 2·h^{1/2} + δ·h^{1/2} + 2δ·h^{1/2}·log(2δh)`, the three terms bounding (S1), (S3), (S2). -/
theorem primeSel_thetaA_le {V : Type*} [Fintype V] {p hv f : V → ℕ} {n : ℕ} {δ ξ : ℝ}
    (hp : ∀ v, (p v).Prime) (hf : ∀ v, 0 < f v) (hnδ : (n : ℝ) ≤ δ) (hδ : 1 ≤ δ)
    (hξ1 : 1 ≤ ξ) (hθ : ∀ x : ℝ, ξ ≤ x → Chebyshev.theta x ≤ 4 / 3 * x)
    (hh : 0 < primeSelHeight p hv f n) (hs : ξ ≤ Real.sqrt (primeSelHeight p hv f n)) :
    Proposition2_1.thetaA (primeSelA p hv (Real.sqrt (primeSelHeight p hv f n)))
      ≤ 2 * Real.sqrt (primeSelHeight p hv f n) + δ * Real.sqrt (primeSelHeight p hv f n)
        + 2 * δ * Real.sqrt (primeSelHeight p hv f n)
          * Real.log (2 * δ * primeSelHeight p hv f n) := by
  set h := primeSelHeight p hv f n with hhdef
  set s := Real.sqrt h with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg h
  have hξ0 : 0 ≤ ξ := by linarith
  have hg : ∀ q : ℕ, 0 ≤ Real.log q := fun q => Real.log_natCast_nonneg q
  -- (S1): `θ(h^{1/2}) ≤ 2·h^{1/2}`
  have hS1 : ∑ q ∈ primeSelS1 s, Real.log q ≤ 2 * s := by
    have := S1_bound hs hξ0 hθ
    simpa [Chebyshev.theta, primeSelS1] using this
  -- (S2), restricted to `h_v ≥ h^{1/2}`: at most `∑_{h_v ≥ h^{1/2}} log(h_v)`
  have hS2 : ∑ q ∈ primeSelS2big hv s, Real.log q ≤ 2 * δ * s * Real.log (2 * δ * h) := by
    refine (primeSel_sum_biUnion_le _ _ hg).trans ((Finset.sum_le_sum fun v hv' => ?_).trans
      (primeSel_S2_sum_le hp hf hnδ hδ (hξ1.trans hs)))
    have hvs : s ≤ (hv v : ℝ) := by simpa [primeSelBig] using hv'
    have : hv v ≠ 0 := by
      intro h0; rw [h0] at hvs
      have : 0 < s := (Real.sqrt_pos.mpr hh); simp at hvs; linarith
    exact primeSel_sum_log_primeFactors_le this
  -- (S3): at most `∑_{h_v ≥ h^{1/2}} log(p_v) ≤ δ·h^{1/2}`
  have hS3 : ∑ q ∈ primeSelS3 p hv s, Real.log q ≤ δ * s :=
    (Finset.sum_image_le_of_nonneg fun q _ => hg q).trans (primeSel_S3_sum_le hf hnδ hh)
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg (primeSel_A_subset p hv s)
    (f := fun q : ℕ => Real.log q) fun q _ _ => hg q
  have hu1 := primeSel_sum_union_le (primeSelS1 s ∪ primeSelS2big hv s) (primeSelS3 p hv s) hg
  have hu2 := primeSel_sum_union_le (primeSelS1 s) (primeSelS2big hv s) hg
  rw [Proposition2_1.thetaA]
  linarith

/-! ### The choice of `l` -/

/-- **The choice of the prime `l`** (pages 44 and 45), for any `ξ ≥ 5` satisfying the two bounds
of Proposition 2.1 (ii). Data: places `V`, primes `p_v`, naturals `h_v`, positive naturals
`f_v`, a natural `n` (for `[F:ℚ]`), a real `δ`, and `h` given by the formula of page 44.
Hypotheses as printed: `h^{1/2} ≥ ξ_prm (≥ 5)`, `[F:ℚ] ≤ δ`, `δ ≥ 2`. Conclusion: a prime `l`
with (P1) `5 ≤ h^{1/2} ≤ l ≤ 10δ·h^{1/2}·log(2δh) ≤ 20·δ²·h²`, (P2) `l` divides no nonzero
`h_v`, and (P3) `l = p_v` implies `h_v < h^{1/2}`. -/
theorem primeSel_exists_prime_of {ξ : ℝ} (hξ5 : 5 ≤ ξ)
    (hθ : ∀ x : ℝ, ξ ≤ x → 2 / 3 * x ≤ Chebyshev.theta x ∧ Chebyshev.theta x ≤ 4 / 3 * x)
    {V : Type*} [Fintype V] (p hv f : V → ℕ) (n : ℕ) (δ h : ℝ)
    (hp : ∀ v, (p v).Prime) (hf : ∀ v, 0 < f v) (hh : h = primeSelHeight p hv f n)
    (hξh : ξ ≤ Real.sqrt h) (hnδ : (n : ℝ) ≤ δ) (hδ : 2 ≤ δ) :
    ∃ l : ℕ, l.Prime ∧
      (5 ≤ Real.sqrt h ∧ Real.sqrt h ≤ l ∧
        (l : ℝ) ≤ 10 * δ * Real.sqrt h * Real.log (2 * δ * h) ∧
        10 * δ * Real.sqrt h * Real.log (2 * δ * h) ≤ 20 * δ ^ 2 * h ^ 2) ∧
      (∀ v, hv v ≠ 0 → ¬ l ∣ hv v) ∧
      (∀ v, l = p v → (hv v : ℝ) < Real.sqrt h) := by
  subst hh
  set h := primeSelHeight p hv f n with hhdef
  set s := Real.sqrt h with hsdef
  have hs5 : 5 ≤ s := hξ5.trans hξh
  have hh0 : 0 < h := Real.sqrt_pos.mp (by linarith)
  have hsq : s ^ 2 = h := Real.sq_sqrt hh0.le
  set L := Real.log (2 * δ * h) with hLdef
  -- `log(2δh) ≥ log(4) ≥ 1` (page 45, property (E6)); here `2δh ≥ 3`.
  have hL1 : 1 ≤ L := by
    have h3 : (3 : ℝ) ≤ 2 * δ * h := by nlinarith
    exact Theorem1_10.one_le_log_three.trans (Real.log_le_log (by norm_num) h3)
  -- page 45: `θ_A ≤ 2h^{1/2} + δh^{1/2} + 2δh^{1/2}log(2δh) ≤ -ξ_prm + 5δh^{1/2}log(2δh)`
  have hA := primeSel_thetaA_le hp hf hnδ (by linarith) (by linarith)
    (fun x hx => (hθ x hx).2) hh0 hξh
  have hchain := (thetaA_chain hδ hL1 (by linarith) hξh hA).2
  -- Proposition 2.1 (ii): a prime `l ∉ A` with `l ≤ 2(θ_A + ξ_prm)`
  obtain ⟨l, hl, hlA, hlle⟩ := Proposition2_1.exists_prime_not_mem_of (by linarith)
    (fun x hx => (hθ x hx).1) (primeSelA p hv s)
  refine ⟨l, hl, ⟨hs5, ?_, P1_upper hlle hchain, ?_⟩, ?_, ?_⟩
  · -- (P1), lower bound: every prime `≤ h^{1/2}` lies in (S1)
    refine (P1_lower (fun q hq hqs => ?_) hl hlA).le
    simp only [primeSelA, primeSelS1, Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc]
    exact Or.inl (Or.inl ⟨⟨hq.pos, Nat.le_floor hqs⟩, hq⟩)
  · -- (P1), parenthetical bound `≤ 20·δ²·h²` (Proposition 2.1 (i))
    have := P1_bound (δ := δ) (s := s) (by linarith) (by linarith)
    rwa [hsq] at this
  · -- (P2): otherwise `l ∈ (S2)`
    intro v hv0 hdvd
    apply hlA
    simp only [primeSelA, primeSelS2, Finset.mem_union, Finset.mem_biUnion]
    exact Or.inl (Or.inr ⟨v, mem_univ v, Nat.mem_primeFactors.mpr ⟨hl, hdvd, hv0⟩⟩)
  · -- (P3): otherwise `l ∈ (S3)`
    intro v hlv
    by_contra hcon
    push Not at hcon
    apply hlA
    simp only [primeSelA, Finset.mem_union]
    refine Or.inr (Finset.mem_image.mpr ⟨v, ?_, hlv.symm⟩)
    simpa [primeSelBig] using hcon

/-- **The choice of the prime `l`**, with the `ξ_prm` of Proposition 2.1 (ii): there is
`ξ_prm ≥ 5` with `(2/3)·x ≤ θ(x) ≤ (4/3)·x` for `x ≥ ξ_prm` such that for all data as in
`primeSel_exists_prime_of` with `h^{1/2} ≥ ξ_prm`, `[F:ℚ] ≤ δ` and `δ ≥ 2`, there is a prime `l`
satisfying (P1), (P2), (P3). -/
theorem primeSel_exists_prime :
    ∃ ξ : ℝ, 5 ≤ ξ ∧
      (∀ x : ℝ, ξ ≤ x → 2 / 3 * x ≤ Chebyshev.theta x ∧ Chebyshev.theta x ≤ 4 / 3 * x) ∧
      ∀ {V : Type} [Fintype V] (p hv f : V → ℕ) (n : ℕ) (δ h : ℝ),
        (∀ v, (p v).Prime) → (∀ v, 0 < f v) → h = primeSelHeight p hv f n →
        ξ ≤ Real.sqrt h → (n : ℝ) ≤ δ → 2 ≤ δ →
        ∃ l : ℕ, l.Prime ∧
          (5 ≤ Real.sqrt h ∧ Real.sqrt h ≤ l ∧
            (l : ℝ) ≤ 10 * δ * Real.sqrt h * Real.log (2 * δ * h) ∧
            10 * δ * Real.sqrt h * Real.log (2 * δ * h) ≤ 20 * δ ^ 2 * h ^ 2) ∧
          (∀ v, hv v ≠ 0 → ¬ l ∣ hv v) ∧
          (∀ v, l = p v → (hv v : ℝ) < Real.sqrt h) := by
  obtain ⟨ξ, hξ5, hθ⟩ := Proposition2_1.exists_xi_prm
  exact ⟨ξ, hξ5, hθ, fun p hv f n δ h hp hf hh hξh hnδ hδ =>
    primeSel_exists_prime_of hξ5 hθ p hv f n δ h hp hf hh hξh hnδ hδ⟩

/-! ### Nonvacuity -/

/-- **Nonvacuity.** For every real `ξ` there are data satisfying all hypotheses of
`primeSel_exists_prime_of`: one place with `p = 2`, `f = 1`, `[F:ℚ] = 1`, `δ = 2` and `h_v = N`
for `N` large. -/
theorem primeSel_hypotheses_satisfiable (ξ : ℝ) :
    ∃ (p hv f : Unit → ℕ) (n : ℕ) (δ : ℝ), (∀ v, (p v).Prime) ∧ (∀ v, 0 < f v) ∧
      (n : ℝ) ≤ δ ∧ 2 ≤ δ ∧ ξ ≤ Real.sqrt (primeSelHeight p hv f n) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨fun _ => 2, fun _ => ⌈ξ ^ 2 / Real.log 2⌉₊, fun _ => 1, 1, 2,
    fun _ => Nat.prime_two, fun _ => one_pos, by norm_num, le_rfl, ?_⟩
  refine (le_abs_self ξ).trans (Real.abs_le_sqrt ?_)
  have hc := Nat.le_ceil (ξ ^ 2 / Real.log 2)
  rw [div_le_iff₀ hl2] at hc
  simp only [primeSelHeight, Finset.univ_unique, Finset.sum_singleton, Nat.cast_one,
    Nat.cast_ofNat]
  linarith

end IUT.PaperIV.Corollary2_2
