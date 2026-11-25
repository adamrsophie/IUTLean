import Mathlib

/-!
# IUT IV, Proposition 1.7: weighted averages

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Proposition 1.7 and its proof,
pages 16 and 17 of the April 2020 manuscript. Both pages were read from the extracted text and
from the rendered pages; the displays were checked against the renders.

Statement of the paper. Let `E` be a nonempty finite set and `n` a positive integer; for
`e ∈ E` let `λ_e > 0` and `β_e ∈ ℝ`. For an `n`-tuple `e⃗ = (e₁, …, eₙ) ∈ Eⁿ` put
`β_e⃗ = ∑_j β_{e_j}` and `λ_Πe⃗ = ∏_j λ_{e_j}`; put `λ_E = ∑_e λ_e`, `β_E = ∑_e β_e·λ_e`,
`β_avg = β_E / λ_E`. Then for every `i = 1, …, n`

`(∑_{e⃗} β_e⃗ · λ_Πe⃗) / (∑_{e⃗} λ_Πe⃗) = (∑_{e⃗} n·β_{e_i} · λ_Πe⃗) / (∑_{e⃗} λ_Πe⃗) = n·β_avg`.

This file proves the statement exactly, together with the two identities of its proof
(`sum_lamProd`, `sum_beta_i_mul_lamProd`). The proposition is elementary; it does not depend on
any other result of the papers.

Indexing: `i` ranges over `Fin n`, which is the paper's `1, …, n` shifted by one.
-/

open Finset

namespace IUT.PaperIV.Proposition1_7

variable {E : Type*} [Fintype E] {n : ℕ}

/-- `λ_Πe⃗ = ∏_j λ_{e_j}`. -/
def lamProd (lam : E → ℝ) (v : Fin n → E) : ℝ := ∏ j, lam (v j)

/-- `β_e⃗ = ∑_j β_{e_j}`. -/
def betaVec (beta : E → ℝ) (v : Fin n → E) : ℝ := ∑ j, beta (v j)

/-- `β_avg = β_E / λ_E` with `β_E = ∑_e β_e·λ_e` and `λ_E = ∑_e λ_e`. -/
noncomputable def betaAvg (lam beta : E → ℝ) : ℝ := (∑ e, beta e * lam e) / ∑ e, lam e

/-- First identity of the proof: `λ_Eⁿ = ∑_{e⃗} λ_Πe⃗`. -/
theorem sum_lamProd (lam : E → ℝ) :
    ∑ v : Fin n → E, lamProd lam v = (∑ e, lam e) ^ n := by
  rw [← Fin.prod_const, prod_univ_sum]
  simp [lamProd, Fintype.piFinset_univ]

/-- Second identity of the proof: `β_E · λ_E^{n-1} = ∑_{e⃗} β_{e_i} · λ_Πe⃗` for every `i`. -/
theorem sum_beta_i_mul_lamProd (lam beta : E → ℝ) (i : Fin n) :
    ∑ v : Fin n → E, beta (v i) * lamProd lam v
      = (∑ e, beta e * lam e) * (∑ e, lam e) ^ (n - 1) := by
  classical
  set g : Fin n → E → ℝ := fun j e => if j = i then beta e * lam e else lam e with hg
  have hprod : ∀ v : Fin n → E, beta (v i) * lamProd lam v = ∏ j, g j (v j) := by
    intro v
    have : ∀ j, g j (v j) = (if j = i then beta (v j) else 1) * lam (v j) := by
      intro j; by_cases h : j = i <;> simp [hg, h]
    rw [Finset.prod_congr rfl (fun j _ => this j), Finset.prod_mul_distrib,
      Finset.prod_ite_eq' univ i]
    simp [lamProd]
  simp_rw [hprod]
  have hx := prod_univ_sum (fun _ => (univ : Finset E)) g
  rw [Fintype.piFinset_univ] at hx
  rw [← hx]
  rw [← Finset.mul_prod_erase univ (fun j => ∑ e, g j e) (mem_univ i)]
  congr 1
  · simp [hg]
  · have hj : ∀ j ∈ univ.erase i, ∑ e, g j e = ∑ e, lam e := by
      intro j hj; rw [Finset.mem_erase] at hj; simp [hg, hj.1]
    rw [Finset.prod_congr rfl hj, Finset.prod_const, Finset.card_erase_of_mem (mem_univ i)]
    simp

/-- Summing the second identity over `i`: `n · β_E · λ_E^{n-1} = ∑_{e⃗} β_e⃗ · λ_Πe⃗`. -/
theorem sum_betaVec_mul_lamProd (lam beta : E → ℝ) :
    ∑ v : Fin n → E, betaVec beta v * lamProd lam v
      = n * ((∑ e, beta e * lam e) * (∑ e, lam e) ^ (n - 1)) := by
  simp_rw [betaVec, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [sum_beta_i_mul_lamProd, Finset.sum_mul]

/-- **Proposition 1.7.** For a nonempty finite `E`, `n ≥ 1`, positive weights `λ` and real
`β`, and every index `i`, both weighted averages of the display equal `n·β_avg`. -/
theorem weighted_averages [Nonempty E] (hn : 1 ≤ n) (lam beta : E → ℝ)
    (hlam : ∀ e, 0 < lam e) (i : Fin n) :
    (∑ v : Fin n → E, betaVec beta v * lamProd lam v) / (∑ v : Fin n → E, lamProd lam v)
        = (∑ v : Fin n → E, n * beta (v i) * lamProd lam v) / (∑ v : Fin n → E, lamProd lam v)
      ∧ (∑ v : Fin n → E, n * beta (v i) * lamProd lam v) / (∑ v : Fin n → E, lamProd lam v)
        = n * betaAvg lam beta := by
  have hL : 0 < ∑ e, lam e := Finset.sum_pos (fun e _ => hlam e) univ_nonempty
  have h2 : ∑ v : Fin n → E, n * beta (v i) * lamProd lam v
      = n * ((∑ e, beta e * lam e) * (∑ e, lam e) ^ (n - 1)) := by
    simp_rw [mul_assoc]; rw [← Finset.mul_sum, sum_beta_i_mul_lamProd]
  refine ⟨by rw [sum_betaVec_mul_lamProd, h2], ?_⟩
  rw [h2, sum_lamProd, betaAvg]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ]
  field_simp

end IUT.PaperIV.Proposition1_7
