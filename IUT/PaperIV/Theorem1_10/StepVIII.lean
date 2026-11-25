import IUT.PaperIV.Theorem1_10.StepIII
import IUT.PaperIV.Theorem1_10.Arithmetic
import IUT.PaperIV.Proposition1_6

/-!
# IUT IV, Theorem 1.10, Step (viii): summing the local bounds and the prime count

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, proof of Theorem 1.10, Step (viii),
pages 30 and 31 of the April 2020 manuscript, read from the extracted text and from the
rendered pages; every display formalized here was checked against the renders.

This file is not a formalization of Step (viii). The step sums the local
procession-normalized bounds of Steps (v), (vi), (vii) over the places of `ℚ`, applies the final
display of Step (iii), and bounds `l*_mod·log(𝔰^≤)` with Proposition 1.6. The local bounds and the
identification of `log(𝔰^≤)` with a count of primes are taken as hypotheses (they rest on the
unformalized Steps (iii) to (vii)). What is checked:

* summing the local bounds (`step_viii_sum`) and passing to the form `hraw` of
  `constant_bound_of_raw`, using the estimate `(l+1)/4·(1/6)·(12/l²) ≥ 1/(2l)` and
  `log(𝔮) ≥ 0` (`step_viii_raw`);
* the two-case bound `l*_mod·log(𝔰^≤) ≤ (4/3)(e*_mod·l + η_prm)` (`step_viii_prime_count`),
  and its instance with the `η_prm` produced by `Proposition1_6.exists_eta_prm`
  (`step_viii_prime_count_prm`);
* the assembly into the bound `C_Θ ≤ constant` of Theorem 1.10 (`step_viii_constant`), given
  that `C_Θ·|log(𝔮)|` is at most the summed bound.

The first case of the prime count (`e*_mod·l ≥ η_prm`) divides by `log(e*_mod·l)` and the second
(`e*_mod·l < η_prm`) by `log(η_prm)`. No condition on `η_prm` beyond the paper's positivity is
needed: since `e*_mod·l ≥ 1`, the second case has `1 ≤ e*_mod·l < η_prm`, which already gives
`log(η_prm) > 0` (page 31). Accordingly `step_viii_prime_count` and `step_viii_constant` assume
only `η > 0`, the positivity stated in Proposition 1.6, together with `e*_mod·l > 1`, which holds
since `e*_mod·l ≥ 2¹²·3³·5·5`.

Notation: `x = e*_mod·l`, `sle = log(𝔰^≤)`, `Q = log(𝔮)`, `L = l*_mod·log(𝔰^≤)`,
`E = e*_mod·l + η_prm`.
-/

open Finset

namespace IUT.PaperIV.Theorem1_10

/-- **Summing the local bounds.** Over a finite set `S` of nonarchimedean places, local
procession-normalized bounds of the form of the last line of page 29 (`step_v_final`), together
with an archimedean bound `(l+1)/4·4` (Step (vii), `step_vii_archimedean`), sum to the bound with
the global quantities `∑_v A_v`, `∑_v B_v`, `∑_v C_v`, `∑_v T_v`. -/
theorem step_viii_sum {ι : Type*} (S : Finset ι) (X A B C T : ι → ℝ) (Xarc l : ℝ)
    (hloc : ∀ v ∈ S,
      X v ≤ (l + 1) / 4 * ((1 + 4 / l) * A v - 1 / 6 * B v + 4 / l * C v + 20 / 3 * T v))
    (harc : Xarc ≤ (l + 1) / 4 * 4) :
    ∑ v ∈ S, X v + Xarc
      ≤ (l + 1) / 4 * ((1 + 4 / l) * ∑ v ∈ S, A v - 1 / 6 * ∑ v ∈ S, B v
          + 4 / l * ∑ v ∈ S, C v + 20 / 3 * ∑ v ∈ S, T v + 4) := by
  have h := Finset.sum_le_sum hloc
  have e : ∑ v ∈ S, (l + 1) / 4 * ((1 + 4 / l) * A v - 1 / 6 * B v + 4 / l * C v
      + 20 / 3 * T v)
      = (l + 1) / 4 * ((1 + 4 / l) * ∑ v ∈ S, A v - 1 / 6 * ∑ v ∈ S, B v
          + 4 / l * ∑ v ∈ S, C v + 20 / 3 * ∑ v ∈ S, T v) := by
    rw [← Finset.mul_sum]; congr 1
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [e] at h
  nlinarith

/-- **First display of Step (viii).** From the summed bound and the final display of Step (iii),
with `log(𝔮) ≥ 0` and the estimate `(l+1)/4·(1/6)·(12/l²) ≥ 1/(2l)`, one obtains the bound in
the form `hraw` of `constant_bound_of_raw`:
`X ≤ (l+1)/4·{(1 + 12·d_mod/l)·D + 2·log(l) + 56 - 1/6·(1 - 12/l²)·Q + 20/3·L} - 1/(2l)·Q`. -/
theorem step_viii_raw {X dK Q sQ L d D l : ℝ} (hl : 5 ≤ l) (hQ : 0 ≤ Q)
    (hsum : X ≤ (l + 1) / 4 * ((1 + 4 / l) * dK - 1 / 6 * Q + 4 / l * sQ + 20 / 3 * L + 4))
    (hiii : (1 + 4 / l) * dK + 4 / l * sQ ≤ (1 + 12 * d / l) * D + 2 * Real.log l + 52) :
    X ≤ (l + 1) / 4 * ((1 + 12 * d / l) * D + 2 * Real.log l + 56
      - 1 / 6 * (1 - 12 / l ^ 2) * Q + 20 / 3 * L) - 1 / (2 * l) * Q := by
  have hl0 : 0 < l := by linarith
  have hest := step_viii_estimate hl0
  have h1 : 0 ≤ (l + 1) / 4 := by linarith
  have h2 : (l + 1) / 4 * ((1 + 4 / l) * dK + 4 / l * sQ)
      ≤ (l + 1) / 4 * ((1 + 12 * d / l) * D + 2 * Real.log l + 52) :=
    mul_le_mul_of_nonneg_left hiii h1
  have h3 : 1 / (2 * l) * Q ≤ (l + 1) / 4 * (1 / 6) * (12 / l ^ 2) * Q :=
    mul_le_mul_of_nonneg_right hest hQ
  have e : (l + 1) / 4 * ((1 + 12 * d / l) * D + 2 * Real.log l + 56
      - 1 / 6 * (1 - 12 / l ^ 2) * Q + 20 / 3 * L)
      = (l + 1) / 4 * ((1 + 12 * d / l) * D + 2 * Real.log l + 52)
        + (l + 1) / 4 * (4 - 1 / 6 * Q + 20 / 3 * L)
        + (l + 1) / 4 * (1 / 6) * (12 / l ^ 2) * Q := by ring
  rw [e]
  nlinarith

/-- **The prime count of Step (viii)** (two cases, pages 30 and 31). Let `x = e*_mod·l > 1` and
let `η > 0` satisfy the conclusion of Proposition 1.6. In the case `x < η` the inequality
`1 < x < η` gives `log(η) > 0`, so no further condition on `η` is used. If `0 ≤ sle ≤ π(x)` (the paper's
`log(𝔰^≤) = ∑_{p ≤ x} 1` over the distinguished primes, so at most the number of primes
`≤ x`), then `log(x)·sle ≤ (4/3)·(x + η)`. -/
theorem step_viii_prime_count {x η sle : ℝ} (hx : 1 < x) (hη : 0 < η)
    (hprm : ∀ y : ℝ, η ≤ y → (Nat.primeCounting ⌊y⌋₊ : ℝ) ≤ 4 * y / (3 * Real.log y))
    (hs0 : 0 ≤ sle) (hs : sle ≤ Nat.primeCounting ⌊x⌋₊) :
    Real.log x * sle ≤ 4 / 3 * (x + η) := by
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx.le
  rcases le_or_gt η x with hxη | hxη
  · have hlog : 0 < Real.log x := Real.log_pos hx
    have h1 := hprm x hxη
    have h2 : Real.log x * sle ≤ Real.log x * (4 * x / (3 * Real.log x)) :=
      mul_le_mul_of_nonneg_left (hs.trans h1) hlx
    have e : Real.log x * (4 * x / (3 * Real.log x)) = 4 / 3 * x := by
      field_simp
    linarith
  · have hlη : 0 < Real.log η := Real.log_pos (by linarith)
    have hmono : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ Nat.primeCounting ⌊η⌋₊ := by
      exact_mod_cast Nat.monotone_primeCounting (Nat.floor_le_floor hxη.le)
    have h1 := hprm η le_rfl
    have hle : Real.log x ≤ Real.log η := Real.log_le_log (by linarith) hxη.le
    have hsη : sle ≤ 4 * η / (3 * Real.log η) := hs.trans (hmono.trans h1)
    have hpos : 0 ≤ 4 * η / (3 * Real.log η) := by positivity
    have h2 : Real.log x * sle ≤ Real.log η * (4 * η / (3 * Real.log η)) :=
      mul_le_mul hle hsη hs0 hlη.le
    have e : Real.log η * (4 * η / (3 * Real.log η)) = 4 / 3 * η := by
      field_simp
    linarith

/-- The prime count bound with the `η_prm` of Proposition 1.6, proved unconditionally from
Mathlib's prime number theorem. -/
theorem step_viii_prime_count_prm :
    ∃ η : ℝ, 2 ≤ η ∧ ∀ x sle : ℝ, 1 < x → 0 ≤ sle → sle ≤ Nat.primeCounting ⌊x⌋₊ →
      Real.log x * sle ≤ 4 / 3 * (x + η) := by
  obtain ⟨η, hη, hprm⟩ := Proposition1_6.exists_eta_prm
  exact ⟨η, hη, fun x sle hx hs0 hs => step_viii_prime_count hx (by linarith) hprm hs0 hs⟩

/-- **Assembly of Step (viii).** Let `e = e_mod ≥ 1`, `x = 2¹²·3³·5·e·l = e*_mod·l`,
`E = x + η` with `η > 0` as in Proposition 1.6, `L = log(x)·sle` with `0 ≤ sle ≤ π(x)`,
`q = Q/(2l) > 0`, and `X` bounded by the summed local bound. Then
`X/q ≤ constant l d D E Q q`, the right-hand side of the bound for `C_Θ` in Theorem 1.10. -/
theorem step_viii_constant {X dK Q sQ sle d D l e η q : ℝ} (hl : 5 ≤ l) (he : 1 ≤ e)
    (hη : 0 < η)
    (hprm : ∀ y : ℝ, η ≤ y → (Nat.primeCounting ⌊y⌋₊ : ℝ) ≤ 4 * y / (3 * Real.log y))
    (hs0 : 0 ≤ sle) (hs : sle ≤ Nat.primeCounting ⌊2 ^ 12 * 3 ^ 3 * 5 * e * l⌋₊)
    (hq : 0 < q) (hqQ : q = Q / (2 * l))
    (hsum : X ≤ (l + 1) / 4 * ((1 + 4 / l) * dK - 1 / 6 * Q + 4 / l * sQ
      + 20 / 3 * (Real.log (2 ^ 12 * 3 ^ 3 * 5 * e * l) * sle) + 4))
    (hiii : (1 + 4 / l) * dK + 4 / l * sQ ≤ (1 + 12 * d / l) * D + 2 * Real.log l + 52) :
    X / q ≤ constant l d D (2 ^ 12 * 3 ^ 3 * 5 * e * l + η) Q q := by
  have hl0 : 0 < l := by linarith
  have hQ : 0 ≤ Q := by
    have : Q = q * (2 * l) := by rw [hqQ]; field_simp
    rw [this]; positivity
  have hx : 1 < 2 ^ 12 * 3 ^ 3 * 5 * e * l := by nlinarith
  have hL := step_viii_prime_count hx hη hprm hs0 hs
  have habs := step_viii_absorb hl he hη.le
  have hraw := step_viii_raw hl hQ hsum hiii
  exact constant_bound_of_raw hl0 hq hqQ (by positivity) hL habs hraw

end IUT.PaperIV.Theorem1_10
