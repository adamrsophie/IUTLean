import Mathlib

/-!
# IUT IV, Proposition 2.1: well-known estimates

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Proposition 2.1 and its proof,
page 40 of the April 2020 manuscript, read from the extracted text and from the rendered page;
the displays were checked against the render. The extracted text of the final sentence reads
"`p ∈ A`"; the render shows "`p ∉ A`", which is what is proved here.

Statement of the paper:

* (i) `log(x) ≤ x` for all real `x ≥ 1`;
* (ii) there is a real `ξ_prm ≥ 5` with `(2/3)·x ≤ θ(x) ≤ (4/3)·x` for all real `x ≥ ξ_prm`,
  where `θ(x) = ∑_{p ≤ x} log(p)`; in particular, for a finite set `A` of primes with
  `θ_A = ∑_{p ∈ A} log(p)`, there is a prime `p ∉ A` with `p ≤ 2(θ_A + ξ_prm)`.

The paper derives (ii) from the prime number theorem ([Edw], [GenEll] Lemma 4.1). Here both
parts are proved unconditionally; (ii) uses Mathlib's `Chebyshev.tendsto_theta_div_atTop`
(`θ(x)/x → 1`).
-/

open Filter Finset

namespace IUT.PaperIV.Proposition2_1

/-- **Proposition 2.1 (i).** `log(x) ≤ x` for `x ≥ 1` (it holds for every `x > 0`). -/
theorem log_le_self {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ x := by
  have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < x); linarith

/-- **Proposition 2.1 (ii), first part.** There is `ξ_prm ≥ 5` with
`(2/3)·x ≤ θ(x) ≤ (4/3)·x` for all `x ≥ ξ_prm`. -/
theorem exists_xi_prm :
    ∃ ξ : ℝ, 5 ≤ ξ ∧ ∀ x : ℝ, ξ ≤ x → 2 / 3 * x ≤ Chebyshev.theta x ∧
      Chebyshev.theta x ≤ 4 / 3 * x := by
  have h := Chebyshev.tendsto_theta_div_atTop
  have hev : ∀ᶠ x : ℝ in atTop, Chebyshev.theta x / x ∈ Set.Icc (2 / 3 : ℝ) (4 / 3) :=
    h (Icc_mem_nhds (by norm_num) (by norm_num))
  obtain ⟨a, ha⟩ := eventually_atTop.mp (hev.and (eventually_ge_atTop (5 : ℝ)))
  refine ⟨max a 5, le_max_right _ _, fun x hx => ?_⟩
  obtain ⟨⟨h1, h2⟩, h5⟩ := ha x (le_trans (le_max_left _ _) hx)
  have hx0 : 0 < x := by linarith
  rw [le_div_iff₀ hx0] at h1
  rw [div_le_iff₀ hx0] at h2
  exact ⟨by linarith, by linarith⟩

/-- `θ_A = ∑_{p ∈ A} log(p)`. -/
noncomputable def thetaA (A : Finset ℕ) : ℝ := ∑ p ∈ A, Real.log p

/-- **Proposition 2.1 (ii), "in particular".** Let `ξ > 0` satisfy `(2/3)·x ≤ θ(x)` for
`x ≥ ξ`. For any finite set `A` of natural numbers (in the paper, of primes) there is a
prime `p ∉ A` with `p ≤ 2(θ_A + ξ)`. -/
theorem exists_prime_not_mem_of {ξ : ℝ} (hξ : 0 < ξ)
    (hθ : ∀ x : ℝ, ξ ≤ x → 2 / 3 * x ≤ Chebyshev.theta x)
    (A : Finset ℕ) :
    ∃ p : ℕ, p.Prime ∧ p ∉ A ∧ (p : ℝ) ≤ 2 * (thetaA A + ξ) := by
  have hA0 : 0 ≤ thetaA A :=
    Finset.sum_nonneg fun p hp => Real.log_natCast_nonneg p
  set x : ℝ := 2 * (thetaA A + ξ) with hx
  have hxξ : ξ ≤ x := by rw [hx]; linarith
  have hx0 : 0 ≤ x := by linarith
  have hlow := hθ x hxξ
  by_contra hcon
  push Not at hcon
  -- every prime `≤ x` lies in `A`
  have hsub : {p ∈ Ioc 0 ⌊x⌋₊ | p.Prime} ⊆ A := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    by_contra hpA
    have := hcon p hp.2 hpA
    have : (p : ℝ) ≤ x := le_trans (by exact_mod_cast hp.1.2) (Nat.floor_le hx0)
    linarith
  have hle : Chebyshev.theta x ≤ thetaA A := by
    rw [Chebyshev.theta, thetaA]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p _ _ => Real.log_natCast_nonneg p)
  linarith

/-- **Proposition 2.1 (ii), "in particular"**, with the `ξ_prm` of `exists_xi_prm`. -/
theorem exists_prime_not_mem :
    ∃ ξ : ℝ, 5 ≤ ξ ∧ ∀ A : Finset ℕ,
      ∃ p : ℕ, p.Prime ∧ p ∉ A ∧ (p : ℝ) ≤ 2 * (thetaA A + ξ) := by
  obtain ⟨ξ, hξ, h⟩ := exists_xi_prm
  exact ⟨ξ, hξ, fun A =>
    exists_prime_not_mem_of (by linarith) (fun x hx => (h x hx).1) A⟩

/-- **Proposition 2.1**, both parts with a single `ξ_prm`, as on page 40: (i) `log(x) ≤ x` for
`x ≥ 1`; (ii) there is `ξ_prm ≥ 5` with `(2/3)·x ≤ θ(x) ≤ (4/3)·x` for all `x ≥ ξ_prm`, and, for
the same `ξ_prm`, every finite set `A` admits a prime `p ∉ A` with `p ≤ 2(θ_A + ξ_prm)`. The
paper takes `A` to be a set of primes; here `A` is any finite set of natural numbers, which is
more general. -/
theorem proposition2_1 :
    (∀ x : ℝ, 1 ≤ x → Real.log x ≤ x) ∧
    ∃ ξ : ℝ, 5 ≤ ξ ∧ (∀ x : ℝ, ξ ≤ x → 2 / 3 * x ≤ Chebyshev.theta x ∧
      Chebyshev.theta x ≤ 4 / 3 * x) ∧
      ∀ A : Finset ℕ, ∃ p : ℕ, p.Prime ∧ p ∉ A ∧ (p : ℝ) ≤ 2 * (thetaA A + ξ) := by
  refine ⟨fun x hx => log_le_self hx, ?_⟩
  obtain ⟨ξ, hξ, h⟩ := exists_xi_prm
  exact ⟨ξ, hξ, h, fun A =>
    exists_prime_not_mem_of (by linarith) (fun x hx => (h x hx).1) A⟩

end IUT.PaperIV.Proposition2_1
