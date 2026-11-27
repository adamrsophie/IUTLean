import IUT.PaperIV.LocalFields.DifferentBound

/-!
# IUT IV, Proposition 1.3 as printed, in one statement

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Proposition 1.3, pages 11 and 12 of
the April 2020 manuscript, with the notation of Proposition 1.1 (page 9) and the ramification
index `e_i` of Proposition 1.2 (page 10). Pages read for this file: 9, 10, 11 and 12. Pages
checked against rendered images: 9, 10, 11 and 12 (the normalization `ord(p) = 1` and the order
`𝔡_i` of the different on page 9; `e_i` on page 10; the notation `R_0`, `𝔡_0`, `e_0`,
`e_{i/0}`, `[k_i : k_0]`, `n_i` and the display of (i) on page 11; the tame equality of (i) and
assertion (ii) on page 12).

This file adds no new mathematics. It collects the results of `IUT.PaperIV.LocalFields.Tower`
and `IUT.PaperIV.LocalFields.DifferentBound` into the single theorem `prop1_3Full`, whose
statement follows the page clause by clause.

## The objects

The setting is that of `IUT.PaperIV.LocalFields.Tower`. `K = k_0`, `K₁ = k_1` and `L = k_i` are
fields with finite-dimensional `ℚ_[p]`-algebra structures, algebra maps `K → K₁ → L` and `K → L`
forming scalar towers, and compatible `ℤ_[p]`-algebra structures. `R_K = integralClosure ℤ_[p] K`
is `R_0`, `R_L = integralClosure ℤ_[p] L` is `R_i`, and `towerAlgebra p K L` is the inclusion
`R_K → R_L`. `P₀` and `P` are primes of `R_K` and `R_L` over `pℤ_p` (each is the maximal ideal).
`e_0 = P₀.ramificationIdx ℤ_[p]`, `e_i = P.ramificationIdx ℤ_[p]`, and the relative index
`e = P.ramificationIdx R_K` of `P` over `P₀`. `𝔡_0 = differentOrder ℤ_[p] R_K P₀` and
`𝔡_i = differentOrder ℤ_[p] R_L P`: the exponent of the different divided by the ramification
index over `ℤ_p`, which is the order `ord` of a generator of the different in the normalization
`ord(p) = 1`. `[k_i : k_0] = Module.finrank K L` and `n_i = multiplicity p [L : K]`.

## Clause by clause

Below, `R_K = integralClosure ℤ_[p] K` and `e` is the relative index `P.ramificationIdx R_K`.

| Printed clause (pages 11 and 12) | Lean |
| --- | --- |
| `k_0 ⊆ k_i` a subfield containing `ℚ_p` | fields `K`, `L`; `IsScalarTower ℚ_[p] K L` |
| `R_0 = 𝒪_{k_0}` | `R_K` |
| `𝔡_0` (order of a generator of the different) | `differentOrder ℤ_[p] R_K P₀` |
| `e_0` (ramification index of `k_0` over `ℚ_p`) | `P₀.ramificationIdx ℤ_[p]` |
| `e_{i/0} = e_i/e_0 (∈ ℤ)` | conjunct 1: `(e : ℝ) = e_i / e_0`, `e : ℕ` |
| `[k_i : k_0]` | `Module.finrank K L` |
| `n_i`: unique `n ≥ 0`, `[k_i : k_0]/p^n` prime to `p` | conjunct 2 (an `iff` for every `m`) |
| (i) `𝔡_i ≥ 𝔡_0 + (e_{i/0} - 1)/(e_{i/0}·e_0)` | conjunct 3, first part |
| (i) `… = 𝔡_0 + (e_{i/0} - 1)/e_i` | conjunct 3, second part |
| (i) equality if `k_i` is tame over `k_0` | conjunct 3, third part, under `¬ p ∣ e` |
| (ii) a subfield `k_1 ⊆ k_i` with `k_0 ⊆ k_1` | field `K₁`; `IsScalarTower K K₁ L` |
| (ii) `k_i` finite Galois over `k_1` | `IsGalois K₁ L` |
| (ii) `k_1` tamely ramified over `k_0` | `¬ p ∣ e_{K₁/K}` at every `P₁` over `p` |
| (ii) `𝔡_i ≤ 𝔡_0 + n_i + 1/e_0` | conjunct 4, conclusion |

## Readings the page leaves implicit

* The fields are abstract finite extensions of `ℚ_p` with compatible maps, not subfields of a
  fixed algebraic closure `\bar ℚ_p`.
* `𝔡` is defined as the exponent of the prime in the different ideal divided by the
  ramification index over `ℤ_p` (`differentOrder`). This is `ord` of any generator of the
  different with `ord(p) = 1`, the normalization of page 9.
* "Tamely ramified" is read as: `p` does not divide the relative ramification index. The residue
  fields are finite, hence perfect, so this is the usual definition.
* The primes `P₀`, `P`, `P₁` over `p` are universally quantified; each ring of integers has
  exactly one (`padicBridge_prime_eq_maximalIdeal`), so no choice is involved.
* `e_{i/0}` is the ramification index of `P` over `P₀`; the first conjunct proves that it equals
  the quotient `e_i/e_0` of the page.

## What is proved

`prop1_3Full`: all clauses of the table, with the hypotheses of (ii) as printed. The proof uses
`towerRamificationIdx_eq_mul`, `towerProp1_3i_ge`, `towerProp1_3i_eq_of_tame` and
`diffBound_prop1_3ii`; the last holds for every finite `L/K`, so the Galois and tameness
hypotheses of (ii) are carried by the statement but not used by the proof.
`prop1_3Full_nExponent_iff` characterizes `multiplicity p d` for `d ≠ 0` as the unique `n` with
`d/p^n` an integer prime to `p`.

## Not proved

* The paper's proofs are not followed. For (i) the page reduces to the totally ramified case and
  computes the different as `ord(f'(π_i))` for a monic `f ≡ x^{e_{i/0}}` modulo `π_0`; the library
  proves (i) through the transitivity of the different and the tame equality. For (ii) the page
  inducts on `n_i` through Galois `p`-subextensions and Kummer generators `x^p - ϖ_*`; the
  library proves (ii) from the trace of `1` (see `IUT.PaperIV.LocalFields.DifferentBound`).
* Nothing is stated about the converse of the tame equality over a general base.
-/

namespace IUT.PaperIV.LocalFields

/-- **The integer `n_i` of page 11.** For a nonzero natural number `d` and a prime `p`, the
natural numbers `m` such that `d / p ^ m` is an integer prime to `p` are exactly `m = v_p(d)`,
the multiplicity of `p` in `d`. -/
theorem prop1_3Full_nExponent_iff (p : ℕ) [Fact p.Prime] {d : ℕ} (hd : d ≠ 0) (m : ℕ) :
    (p ^ m ∣ d ∧ ¬ p ∣ d / p ^ m) ↔ m = multiplicity p d := by
  have hp : p.Prime := Fact.out
  constructor
  · rintro ⟨⟨c, hc⟩, hnd⟩
    have hpos : 0 < p ^ m := pow_pos hp.pos m
    have hdiv : d / p ^ m = c := by rw [hc, Nat.mul_div_cancel_left c hpos]
    refine (multiplicity_eq_of_dvd_of_not_dvd ⟨c, hc⟩ fun h => hnd ?_).symm
    rw [hdiv]
    rw [hc, pow_succ] at h
    exact Nat.dvd_of_mul_dvd_mul_left hpos h
  · rintro rfl
    refine ⟨pow_multiplicity_dvd p d, fun h => pow_succ_multiplicity_not_dvd (p := p) hd ?_⟩
    rw [pow_succ]
    conv_rhs => rw [← Nat.mul_div_cancel' (pow_multiplicity_dvd p d)]
    exact mul_dvd_mul_left _ h

/-- **IUT IV, Proposition 1.3, as printed** (pages 11 and 12). For finite extensions
`ℚ_p ⊆ K ⊆ K₁ ⊆ L` (the paper's `k_0 ⊆ k_1 ⊆ k_i`), primes `P₀` of `R_K` and `P` of `R_L` over
`p`, with `e_0`, `e_i` the ramification indices over `ℤ_p`, `e` the ramification index of `P`
over `P₀`, `𝔡_0`, `𝔡_i` the orders of the differents (`ord(p) = 1`) and `n_i = v_p([L : K])`:

* `e = e_i/e_0` (the definition `e_{i/0} = e_i/e_0 ∈ ℤ`);
* `n_i` is the unique `m ≥ 0` with `[L : K]/p^m` an integer prime to `p`;
* (i) `𝔡_i ≥ 𝔡_0 + (e - 1)/(e·e_0)`, the printed rewriting
  `𝔡_0 + (e - 1)/(e·e_0) = 𝔡_0 + (e - 1)/e_i`, and equality when `L` is tamely ramified over `K`
  (`p ∤ e`);
* (ii) if `L` is Galois over `K₁` and `K₁` is tamely ramified over `K`, then
  `𝔡_i ≤ 𝔡_0 + n_i + 1/e_0`. -/
theorem prop1_3Full (p : ℕ) [Fact p.Prime] (K K₁ L : Type*) [Field K] [Field K₁] [Field L]
    [Algebra ℚ_[p] K] [Algebra ℚ_[p] K₁] [Algebra ℚ_[p] L]
    [Algebra K K₁] [Algebra K₁ L] [Algebra K L]
    [IsScalarTower ℚ_[p] K K₁] [IsScalarTower ℚ_[p] K₁ L] [IsScalarTower ℚ_[p] K L]
    [IsScalarTower K K₁ L]
    [Algebra ℤ_[p] K] [Algebra ℤ_[p] K₁] [Algebra ℤ_[p] L]
    [IsScalarTower ℤ_[p] ℚ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K₁] [IsScalarTower ℤ_[p] ℚ_[p] L]
    [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] K₁] [FiniteDimensional ℚ_[p] L]
    (P₀ : Ideal (integralClosure ℤ_[p] K)) [P₀.IsPrime]
    [P₀.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] (P : Ideal (integralClosure ℤ_[p] L))
    [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    letI := isDedekindDomain_ringOfIntegers_padic p K
    letI := isDedekindDomain_ringOfIntegers_padic p L
    letI := isTorsionFree_ringOfIntegers_padic p K
    letI := isTorsionFree_ringOfIntegers_padic p L
    letI := towerAlgebra p K L
    -- notation: `e_{i/0} = e_i/e_0 (∈ ℤ)`
    ((P.ramificationIdx (integralClosure ℤ_[p] K) : ℝ) =
        (P.ramificationIdx ℤ_[p] : ℝ) / P₀.ramificationIdx ℤ_[p]) ∧
    -- notation: `n_i`
    (∀ m : ℕ, (p ^ m ∣ Module.finrank K L ∧ ¬ p ∣ Module.finrank K L / p ^ m) ↔
        m = multiplicity p (Module.finrank K L)) ∧
    -- assertion (i)
    (differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P₀ +
          ((P.ramificationIdx (integralClosure ℤ_[p] K) : ℝ) - 1) /
            ((P.ramificationIdx (integralClosure ℤ_[p] K) : ℝ) * P₀.ramificationIdx ℤ_[p]) ≤
        differentOrder ℤ_[p] (integralClosure ℤ_[p] L) P ∧
      differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P₀ +
          ((P.ramificationIdx (integralClosure ℤ_[p] K) : ℝ) - 1) /
            ((P.ramificationIdx (integralClosure ℤ_[p] K) : ℝ) * P₀.ramificationIdx ℤ_[p]) =
        differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P₀ +
          ((P.ramificationIdx (integralClosure ℤ_[p] K) : ℝ) - 1) / P.ramificationIdx ℤ_[p] ∧
      (¬ p ∣ P.ramificationIdx (integralClosure ℤ_[p] K) →
        differentOrder ℤ_[p] (integralClosure ℤ_[p] L) P =
          differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P₀ +
            ((P.ramificationIdx (integralClosure ℤ_[p] K) : ℝ) - 1) /
              ((P.ramificationIdx (integralClosure ℤ_[p] K) : ℝ) *
                P₀.ramificationIdx ℤ_[p]))) ∧
    -- assertion (ii)
    (IsGalois K₁ L →
      (∀ P₁ : Ideal (integralClosure ℤ_[p] K₁), P₁.IsPrime →
        P₁.LiesOver (IsLocalRing.maximalIdeal ℤ_[p]) →
        letI := towerAlgebra p K K₁
        ¬ p ∣ P₁.ramificationIdx (integralClosure ℤ_[p] K)) →
      differentOrder ℤ_[p] (integralClosure ℤ_[p] L) P ≤
        differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P₀ +
          (multiplicity p (Module.finrank K L) : ℝ) + 1 / P₀.ramificationIdx ℤ_[p]) := by
  have := isDedekindDomain_ringOfIntegers_padic p K
  have := isDedekindDomain_ringOfIntegers_padic p L
  have := isTorsionFree_ringOfIntegers_padic p K
  have := isTorsionFree_ringOfIntegers_padic p L
  let := towerAlgebra p K L
  have htow := towerRamificationIdx_eq_mul p K L P₀ P
  have hge := towerProp1_3i_ge p K L P₀ P
  have htame := towerProp1_3i_eq_of_tame p K L P₀ P
  have hii := diffBound_prop1_3ii p K L P₀ P
  have : FiniteDimensional K L := Module.Finite.right ℚ_[p] K L
  have hfin : Module.finrank K L ≠ 0 := Module.finrank_pos.ne'
  have hpm : IsLocalRing.maximalIdeal ℤ_[p] ≠ ⊥ := IsDiscreteValuationRing.not_a_field ℤ_[p]
  have he₀ : 0 < P₀.ramificationIdx ℤ_[p] := ramificationIdx_pos_of_liesOver hpm P₀
  have h0 : (P₀.ramificationIdx ℤ_[p] : ℝ) ≠ 0 := by exact_mod_cast he₀.ne'
  have hrw : ((P.ramificationIdx (integralClosure ℤ_[p] K) : ℝ) - 1) /
        ((P.ramificationIdx (integralClosure ℤ_[p] K) : ℝ) * P₀.ramificationIdx ℤ_[p]) =
      ((P.ramificationIdx (integralClosure ℤ_[p] K) : ℝ) - 1) / P.ramificationIdx ℤ_[p] := by
    rw [htow, Nat.cast_mul, mul_comm]
  refine ⟨?_, prop1_3Full_nExponent_iff p hfin, ⟨?_, by rw [hrw], fun hp => ?_⟩,
    fun _ _ => hii⟩
  · rw [htow, Nat.cast_mul, mul_div_cancel_left₀ _ h0]
  · rw [hrw]
    exact hge
  · rw [hrw]
    exact htame hp

end IUT.PaperIV.LocalFields
