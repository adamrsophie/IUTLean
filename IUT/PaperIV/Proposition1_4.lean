import IUT.PaperIV.Proposition1_2

/-!
# IUT IV, Proposition 1.4: nonarchimedean normalized log-volume estimates (elementary part)

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Proposition 1.4 and its proof,
pages 13 and 14 of the April 2020 manuscript, read from the extracted text and from the rendered
pages 13 and 14; the displays formalized here were checked against the renders.

This file is not a formalization of Proposition 1.4. For one finite extension of `ℚ_p`, (ii) is
proved with the normalized Haar log-volume in `IUT/PaperIV/LocalFields/UnitVolume.lean`, and (i)
for tensor packets in `IUT/PaperIV/LocalFields/Packets.lean`; their identification with the
log-volume of [AbsTopIII] is not formalized. For two factors, (iv) and the second inequality of
(iii) are proved with the normalized Haar log-volume in
`IUT/PaperIV/LocalFields/TensorLogShell.lean`, and the first inequality of (iii), with the
additivity of page 14, in `IUT/PaperIV/LocalFields/TensorAdditivity.lean`. The log-volume `μ^log` of
[AbsTopIII], Proposition 5.7, on compact open subsets of `p`-adic fields and their tensor
products, is not formalized. Its properties used in the proof enter here as real-number hypotheses:

* `μ^log(p^k·M) = μ^log(M) - k·log(p)` (normalization of (i));
* `μ^log(log_p(R_I^×)) = ∑_{i ∈ I} μ^log(log_p(R_i^×)) + μ^log(R_I)` (the paper's display);
* `μ^log(R_I) ≤ 0` and `μ^log((R_I)^∼) = 0` ((i) together with Proposition 1.1).

What is checked:

* the computation of (ii): `(1/(e·f))·(log(1 - p^{-f}) - log(p^m·(p^f - 1))) =
  -(1/e + m/(e·f))·log(p)` (`ii_identity`), so `μ^log(log_p(R_i^×)) ≤ -(1/e_i)·log(p)`
  (`ii_le`);
* the two summation chains of (iii) (`iii_first`, `iii_second`), with the per-index estimates of
  Proposition 1.2 (`Proposition1_2.a_sub_le`, `Proposition1_2.b_add_le`) and the fact that
  `a_i = 1/e_i = -b_i` for `i ∉ I*`;
* the lower bounds `d_I + a_I ≥ |I|` (`p > 2`) and `d_I + a_I ≥ 2|I|` (`p = 2`)
  (`dI_add_aI_ge`).

In the first chain the paper writes `p^{λ - d_I - a_I}`; the render shows a floor, which is the
source of the `+1`. Here the floor step is a hypothesis `hfloor` of the form
`μ ≤ (-λ + d_I + a_I + 1)·log(p) + μ^log(log_p(R_I^×))`.
-/

open Finset

namespace IUT.PaperIV.Proposition1_4

open Proposition1_2

/-- **Proposition 1.4 (ii), the computation.** For `p > 1`, `e, f > 0` and `m ≥ 0`:
`(1/(e·f))·(log(1 - p^{-f}) - log(p^m·(p^f - 1))) = -(1/e + m/(e·f))·log(p)`. -/
theorem ii_identity {p e : ℝ} {f m : ℕ} (hp : 1 < p) (he : 0 < e) (hf : 1 ≤ f) :
    1 / (e * f) * (Real.log (1 - (p ^ f)⁻¹) - Real.log (p ^ m * (p ^ f - 1)))
      = -(1 / e + m / (e * f)) * Real.log p := by
  have hpf : 1 < p ^ f := one_lt_pow₀ hp (by omega)
  have hp0 : 0 < p := by linarith
  have e1 : 1 - (p ^ f)⁻¹ = (p ^ f - 1) / p ^ f := by field_simp
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  rw [e1, Real.log_div (by linarith) (by positivity), Real.log_mul (by positivity) (by linarith),
    Real.log_pow, Real.log_pow]
  field_simp
  ring

/-- Consequence used in (iii): `μ^log(log_p(R_i^×)) ≤ -(1/e_i)·log(p)`. -/
theorem ii_le {p e mu : ℝ} {m f : ℕ} (hp : 1 < p) (he : 0 < e) (hf : 1 ≤ f)
    (hmu : mu = -(1 / e + m / (e * f)) * Real.log p) : mu ≤ -(1 / e) * Real.log p := by
  have hlog : 0 < Real.log p := Real.log_pos hp
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have : 0 ≤ (m : ℝ) / (e * f) * Real.log p := by positivity
  rw [hmu]; nlinarith

variable {ι : Type*} [DecidableEq ι]

/-- **Proposition 1.4 (iii), first chain.** Let `p ≥ 2`, `e : ι → ℕ` with `e_i ≥ 1`, and
`I* ⊆ I` such that `e_i ≤ p - 2` for `i ∈ I \ I*`. Assume the floor step `hfloor`, the
decomposition `hsum`, `μ^log(log_p(R_i^×)) ≤ -(1/e_i)·log(p)` and `μ^log(R_I) ≤ 0`. Then
`μ^log(p^{⌊λ - d_I - a_I⌋}·log_p(R_I^×)) ≤ (-λ + d_I + 1 + 4·|I*|/p)·log(p)`. -/
theorem iii_first {p : ℕ} (hp : 2 ≤ p) (I Istar : Finset ι) (hsub : Istar ⊆ I) (e : ι → ℕ)
    (he : ∀ i, 1 ≤ e i) (hout : ∀ i ∈ I, i ∉ Istar → e i ≤ p - 2)
    {lam dI mu muM muR : ℝ} (mui : ι → ℝ)
    (hfloor : mu ≤ (-lam + dI + ∑ i ∈ I, a p (e i) + 1) * Real.log p + muM)
    (hsum : muM = ∑ i ∈ I, mui i + muR)
    (hmui : ∀ i ∈ I, mui i ≤ -(1 / (e i : ℝ)) * Real.log p) (hR : muR ≤ 0) :
    mu ≤ (-lam + dI + 1 + 4 * Istar.card / p) * Real.log p := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hlog : 0 < Real.log p := Real.log_pos (by linarith)
  -- `∑_{i ∈ I} (a_i - 1/e_i) ≤ 4·|I*|/p`
  have hterm : ∀ i ∈ I, a p (e i) - 1 / (e i : ℝ) ≤ if i ∈ Istar then (4 : ℝ) / p else 0 := by
    intro i hi
    split_ifs with hs
    · have := Proposition1_2.a_sub_le hp (he i); linarith
    · have h2 : 2 < p := by have := he i; have := hout i hi hs; omega
      have := (Proposition1_2.a_b_of_le h2 (he i) (hout i hi hs)).1; linarith
  have hsumle : ∑ i ∈ I, (a p (e i) - 1 / (e i : ℝ)) ≤ 4 * Istar.card / p := by
    calc ∑ i ∈ I, (a p (e i) - 1 / (e i : ℝ))
        ≤ ∑ i ∈ I, (if i ∈ Istar then (4 : ℝ) / p else 0) := Finset.sum_le_sum hterm
      _ = ∑ i ∈ Istar, (4 : ℝ) / p := by
          rw [← Finset.sum_filter]; congr 1; ext i; simp only [Finset.mem_filter]
          exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
      _ = 4 * Istar.card / p := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hmusum : ∑ i ∈ I, mui i ≤ ∑ i ∈ I, -(1 / (e i : ℝ)) * Real.log p :=
    Finset.sum_le_sum hmui
  have e1 : ∑ i ∈ I, -(1 / (e i : ℝ)) * Real.log p = -(∑ i ∈ I, 1 / (e i : ℝ)) * Real.log p := by
    rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]; simp only [neg_mul]
  have e2 : ∑ i ∈ I, a p (e i) = ∑ i ∈ I, (a p (e i) - 1 / (e i : ℝ)) + ∑ i ∈ I, 1 / (e i : ℝ) := by
    rw [← Finset.sum_add_distrib]; simp
  rw [e2] at hfloor
  have := mul_le_mul_of_nonneg_right hsumle hlog.le
  linarith

/-- Per-index estimate of (iii): `(a_i + b_i)·log(p) ≤ 3 + log(e_i)`. -/
theorem a_add_b_le {p e : ℕ} (hp : 2 ≤ p) (he : 1 ≤ e) :
    (a p e + b p e) * Real.log p ≤ 3 + Real.log e := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hlog : 0 < Real.log p := Real.log_pos (by linarith)
  have h1 := Proposition1_2.a_sub_le hp he
  have h2 := Proposition1_2.four_div_le hp'
  have h3 := Proposition1_2.b_add_le hp he
  have h4 : (a p e - 1 / (e : ℝ)) * Real.log p ≤ 2 := by
    have := mul_le_mul_of_nonneg_right (h1.trans h2) hlog.le
    rwa [div_mul_cancel₀ _ hlog.ne'] at this
  nlinarith [h3.1, h3.2]

/-- **Proposition 1.4 (iii), second chain.** With the same `I*` and the hypothesis
`μ ≤ (-λ + d_I + a_I + b_I + 1)·log(p)` (from `μ^log((R_I)^∼) = 0` and the floor step):
`μ^log(p^{⌊λ - d_I - a_I⌋ - b_I}·(R_I)^∼) ≤ (-λ + d_I + 1)·log(p) + ∑_{i ∈ I*} {3 + log(e_i)}`. -/
theorem iii_second {p : ℕ} (hp : 2 ≤ p) (I Istar : Finset ι) (hsub : Istar ⊆ I) (e : ι → ℕ)
    (he : ∀ i, 1 ≤ e i) (hout : ∀ i ∈ I, i ∉ Istar → e i ≤ p - 2) {lam dI mu : ℝ}
    (h : mu ≤ (-lam + dI + ∑ i ∈ I, a p (e i) + ∑ i ∈ I, b p (e i) + 1) * Real.log p) :
    mu ≤ (-lam + dI + 1) * Real.log p + ∑ i ∈ Istar, (3 + Real.log (e i)) := by
  have hterm : ∀ i ∈ I, (a p (e i) + b p (e i)) * Real.log p
      ≤ if i ∈ Istar then 3 + Real.log (e i) else 0 := by
    intro i hi
    split_ifs with hs
    · exact a_add_b_le hp (he i)
    · have h2 : 2 < p := by have := he i; have := hout i hi hs; omega
      have := Proposition1_2.a_b_of_le h2 (he i) (hout i hi hs)
      rw [this.1, this.2]; simp
  have hs : ∑ i ∈ I, (a p (e i) + b p (e i)) * Real.log p ≤ ∑ i ∈ Istar, (3 + Real.log (e i)) := by
    calc ∑ i ∈ I, (a p (e i) + b p (e i)) * Real.log p
        ≤ ∑ i ∈ I, (if i ∈ Istar then 3 + Real.log (e i) else 0) := Finset.sum_le_sum hterm
      _ = ∑ i ∈ Istar, (3 + Real.log (e i)) := by
          rw [← Finset.sum_filter]; congr 1; ext i; simp only [Finset.mem_filter]
          exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  have e1 : (-lam + dI + ∑ i ∈ I, a p (e i) + ∑ i ∈ I, b p (e i) + 1) * Real.log p
      = (-lam + dI + 1) * Real.log p + ∑ i ∈ I, (a p (e i) + b p (e i)) * Real.log p := by
    rw [← Finset.sum_mul, Finset.sum_add_distrib]; ring
  linarith

omit [DecidableEq ι] in
/-- **`d_I + a_I ≥ |I|` for `p > 2`, `d_I + a_I ≥ 2|I|` for `p = 2`.** Here `d_I = ∑ d_i` with
`d_i ≥ (e_i - 1)/e_i` (Proposition 1.3 (i) with `k_0 = ℚ_p`) when `p > 2`, and `d_i ≥ 0` when
`p = 2`. -/
theorem dI_add_aI_ge {p : ℕ} (I : Finset ι) (e : ι → ℕ) (he : ∀ i, 1 ≤ e i) (d : ι → ℝ) :
    (2 < p → (∀ i ∈ I, ((e i : ℝ) - 1) / e i ≤ d i) →
        (I.card : ℝ) ≤ ∑ i ∈ I, d i + ∑ i ∈ I, a p (e i)) ∧
      (p = 2 → (∀ i ∈ I, 0 ≤ d i) →
        2 * (I.card : ℝ) ≤ ∑ i ∈ I, d i + ∑ i ∈ I, a p (e i)) := by
  constructor
  · intro hp hd
    rw [← Finset.sum_add_distrib]
    have : ∑ _i ∈ I, (1 : ℝ) ≤ ∑ i ∈ I, (d i + a p (e i)) :=
      Finset.sum_le_sum fun i hi => (Proposition1_2.d_add_a_ge (he i)).1 hp (hd i hi)
    simpa using this
  · intro hp hd
    rw [← Finset.sum_add_distrib]
    have : ∑ _i ∈ I, (2 : ℝ) ≤ ∑ i ∈ I, (d i + a p (e i)) :=
      Finset.sum_le_sum fun i hi => (Proposition1_2.d_add_a_ge (he i)).2 hp (hd i hi)
    simpa [mul_comm] using this

end IUT.PaperIV.Proposition1_4
