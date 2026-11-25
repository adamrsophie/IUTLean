import IUT.PaperIV.LocalFields.Different
import IUT.PaperIV.Proposition1_4

/-!
# IUT IV, Propositions 1.2 to 1.4: the different of a finite extension of `ℚ_p`

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Propositions 1.1 to 1.4, pages 9 to
14 of the April 2020 manuscript. Pages read for this file: 9 to 15. Pages checked against
rendered images: 9 to 14 (the normalization `ord(p) = 1` and the definition of `𝔡_i` on page 9,
the definitions of `e_i`, `a_i`, `b_i` on page 10, Proposition 1.3 (i) on pages 11 and 12, the
inequalities `𝔡_I + a_I ≥ |I|`, `𝔡_I + a_I ≥ 2|I|` of Proposition 1.4 (iii) on page 13 with
their proof on page 14).

This file specializes `IUT.PaperIV.LocalFields.Different` to the paper's objects: `A = ℤ_p`,
`K = ℚ_p`, `L = k_i` a finite extension of `ℚ_p`, and `R_i = integralClosure ℤ_p k_i` its ring
of integers. Here `p` is a prime number, `ℤ_[p]`, `ℚ_[p]` are Mathlib's `p`-adic integers and
numbers, and `k_i` is any field with a finite-dimensional `ℚ_[p]`-algebra structure (and the
compatible `ℤ_[p]`-algebra structure). The ramification index `e_i` is that of a prime `P` of
`R_i` over the maximal ideal `pℤ_p`, and `𝔡_i = differentOrder ℤ_[p] R_i P` (exponent of `P` in
the different divided by `e_i`); since `p` generates the maximal ideal of `ℤ_p`, this is the
paper's normalization `ord(p) = 1`. The ring `R_i` has only one such prime `P`, but that is not
proved here, so the statements hold for every prime `P` over `p`.

What is proved:

* `isDedekindDomain_ringOfIntegers_padic`, `isTorsionFree_ringOfIntegers_padic`: `R_i` is a
  Dedekind domain, torsion free over `ℤ_p` (so the general results apply; this also shows that
  their hypotheses are satisfiable);
* `padic_differentOrder_ge`: Proposition 1.3 (i) with `k_0 = ℚ_p`, i.e. `𝔡_i ≥ (e_i - 1)/e_i`;
* `padic_differentOrder_add_a_ge`: `𝔡_i + a_i ≥ 1` if `p > 2` and `𝔡_i + a_i ≥ 2` if `p = 2`,
  with `a_i = Proposition1_2.a p e_i` the constant of page 10 evaluated at the actual `p` and
  `e_i` (the inequality `Proposition1_2.d_add_a_ge` with its hypothesis discharged);
* `padic_dI_add_aI_ge`: for finitely many such extensions `k_i` (`i ∈ I`), the last sentence of
  Proposition 1.4 (iii), `𝔡_I + a_I ≥ |I|` if `p > 2` and `𝔡_I + a_I ≥ 2|I|` if `p = 2`, with
  `𝔡_I = ∑ 𝔡_i` and `a_I = ∑ a_i` (`Proposition1_4.dI_add_aI_ge` with its hypothesis discharged).

Not formalized here: the inclusions of Propositions 1.1 and 1.2 (tensor products of the `R_i`,
their normalization, `p`-adic logarithms), the tame equality of Proposition 1.3 (i), Proposition
1.3 (ii), and the log-volumes of Proposition 1.4.
-/

open Ideal

namespace IUT.PaperIV.LocalFields

variable (p : ℕ) [Fact p.Prime] (L : Type*) [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
  [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L]

/-- The ring of integers `integralClosure ℤ_[p] L` of a finite extension `L` of `ℚ_[p]` is a
Dedekind domain. -/
theorem isDedekindDomain_ringOfIntegers_padic : IsDedekindDomain (integralClosure ℤ_[p] L) :=
  integralClosure.isDedekindDomain ℤ_[p] ℚ_[p] L

omit [FiniteDimensional ℚ_[p] L] in
/-- The ring of integers of a finite extension of `ℚ_[p]` is torsion free over `ℤ_[p]`. -/
theorem isTorsionFree_ringOfIntegers_padic :
    Module.IsTorsionFree ℤ_[p] (integralClosure ℤ_[p] L) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
  have h' : algebraMap ℤ_[p] L r * (m : L) = 0 := by
    have := congrArg (fun x : integralClosure ℤ_[p] L => (x : L)) h
    simpa [Algebra.smul_def] using this
  rcases mul_eq_zero.mp h' with hr | hm
  · left
    rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] L, map_eq_zero] at hr
    exact IsFractionRing.injective ℤ_[p] ℚ_[p] (hr.trans (map_zero _).symm)
  · right
    exact Subtype.ext hm

/-- **Proposition 1.3 (i) for `k_0 = ℚ_p`** (pages 11 and 12): for a finite extension `L` of
`ℚ_[p]` and a prime `P` of its ring of integers over `p`, `𝔡 ≥ (e - 1)/e`, where `e` is the
ramification index and `𝔡 = differentOrder` the order of the different normalized by
`ord(p) = 1`. -/
theorem padic_differentOrder_ge (P : Ideal (integralClosure ℤ_[p] L)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    letI := isDedekindDomain_ringOfIntegers_padic p L
    letI := isTorsionFree_ringOfIntegers_padic p L
    ((P.ramificationIdx ℤ_[p] : ℝ) - 1) / P.ramificationIdx ℤ_[p] ≤
      differentOrder ℤ_[p] (integralClosure ℤ_[p] L) P := by
  let := isDedekindDomain_ringOfIntegers_padic p L
  let := isTorsionFree_ringOfIntegers_padic p L
  exact differentOrder_ge ℤ_[p] ℚ_[p] L (integralClosure ℤ_[p] L)
    (IsDiscreteValuationRing.not_a_field ℤ_[p]) P

/-- **`𝔡_i + a_i ≥ 1` (`p > 2`) and `𝔡_i + a_i ≥ 2` (`p = 2`)** for an actual finite extension
`L = k_i` of `ℚ_[p]` (page 14, proof of Proposition 1.4 (iii)): here `𝔡_i = differentOrder` and
`a_i = Proposition1_2.a p e_i` with `e_i` the ramification index of `P` over `p`. The input
`𝔡_i ≥ (e_i - 1)/e_i` of `Proposition1_2.d_add_a_ge` is `padic_differentOrder_ge`. -/
theorem padic_differentOrder_add_a_ge (P : Ideal (integralClosure ℤ_[p] L)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    letI := isDedekindDomain_ringOfIntegers_padic p L
    letI := isTorsionFree_ringOfIntegers_padic p L
    (2 < p → 1 ≤ differentOrder ℤ_[p] (integralClosure ℤ_[p] L) P +
        Proposition1_2.a p (P.ramificationIdx ℤ_[p])) ∧
      (p = 2 → 2 ≤ differentOrder ℤ_[p] (integralClosure ℤ_[p] L) P +
        Proposition1_2.a p (P.ramificationIdx ℤ_[p])) := by
  let := isDedekindDomain_ringOfIntegers_padic p L
  let := isTorsionFree_ringOfIntegers_padic p L
  have he : 1 ≤ P.ramificationIdx ℤ_[p] :=
    ramificationIdx_pos_of_liesOver (IsDiscreteValuationRing.not_a_field ℤ_[p]) P
  have hd := padic_differentOrder_ge p L P
  have h0 : 0 ≤ differentOrder ℤ_[p] (integralClosure ℤ_[p] L) P := by
    unfold differentOrder; positivity
  exact ⟨fun hp => (Proposition1_2.d_add_a_ge he).1 hp hd,
    fun hp => (Proposition1_2.d_add_a_ge he).2 hp h0⟩

/-- **Proposition 1.4 (iii), last sentence** (page 13, proof on page 14), for actual finite
extensions `k_i` of `ℚ_[p]`, `i ∈ I`, with a prime `P_i` of the ring of integers of each over
`p`: `𝔡_I + a_I ≥ |I|` if `p > 2`, and `𝔡_I + a_I ≥ 2|I|` if `p = 2`, where
`𝔡_I = ∑_{i ∈ I} 𝔡_i` and `a_I = ∑_{i ∈ I} a_i`. -/
theorem padic_dI_add_aI_ge {ι : Type*} (I : Finset ι) (k : ι → Type*) [∀ i, Field (k i)]
    [∀ i, Algebra ℚ_[p] (k i)] [∀ i, FiniteDimensional ℚ_[p] (k i)] [∀ i, Algebra ℤ_[p] (k i)]
    [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (k i)] (P : ∀ i, Ideal (integralClosure ℤ_[p] (k i)))
    [∀ i, (P i).IsPrime] [∀ i, (P i).LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    letI := fun i => isDedekindDomain_ringOfIntegers_padic p (k i)
    letI := fun i => isTorsionFree_ringOfIntegers_padic p (k i)
    (2 < p → (I.card : ℝ) ≤ ∑ i ∈ I, differentOrder ℤ_[p] (integralClosure ℤ_[p] (k i)) (P i) +
        ∑ i ∈ I, Proposition1_2.a p ((P i).ramificationIdx ℤ_[p])) ∧
      (p = 2 → 2 * (I.card : ℝ) ≤
        ∑ i ∈ I, differentOrder ℤ_[p] (integralClosure ℤ_[p] (k i)) (P i) +
          ∑ i ∈ I, Proposition1_2.a p ((P i).ramificationIdx ℤ_[p])) := by
  let := fun i => isDedekindDomain_ringOfIntegers_padic p (k i)
  let := fun i => isTorsionFree_ringOfIntegers_padic p (k i)
  have he : ∀ i, 1 ≤ (P i).ramificationIdx ℤ_[p] := fun i =>
    ramificationIdx_pos_of_liesOver (IsDiscreteValuationRing.not_a_field ℤ_[p]) (P i)
  have h := Proposition1_4.dI_add_aI_ge (p := p) I (fun i => (P i).ramificationIdx ℤ_[p]) he
    (fun i => differentOrder ℤ_[p] (integralClosure ℤ_[p] (k i)) (P i))
  refine ⟨fun hp => h.1 hp fun i _ => padic_differentOrder_ge p (k i) (P i),
    fun hp => h.2 hp fun i _ => ?_⟩
  unfold differentOrder; positivity

end IUT.PaperIV.LocalFields
