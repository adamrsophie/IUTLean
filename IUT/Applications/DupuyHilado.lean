import IUT.Prerequisites.PadicLog
import IUT.PaperIII.Remark3_9_5.HullOperator
import IUT.PaperIV.Theorem1_10.StepV
import IUT.PaperIV.Theorem1_10.ElementaryFacts

/-!
# Dupuy and Hilado's reading of IUT III Corollary 3.12: the local layer and the deductions

Sources, read from their TeX sources:

* T. Dupuy, A. Hilado, *The Statement of Mochizuki's Corollary 3.12, Initial Theta Data, and the
  First Two Indeterminacies*, arXiv 2004.13228 (version 2, 2025, titled *The Statement of
  Mochizuki's Corollary 3.12: Initial Theta Data*; cited below as [DH-ITD]): §1 (Inequality
  1.0.1, Theorem 1.0.2), §2.1 to §2.10 (Fricke involution, arithmetic Riemann surfaces, pre theta
  data, Tate uniformization, multiplicative subspaces, Definition 2.8.1 of initial theta data,
  Lemmas 2.9.1 and 2.9.2, the example 11a1). Read: all of §1 and §2.1 to §2.10.
* T. Dupuy, A. Hilado, *Probabilistic Szpiro, Baby Szpiro, and Explicit Szpiro from Mochizuki's
  Corollary 3.12*, arXiv 2004.13108 (version 2, 2020; cited below as [DH-Szpiro]): read in full,
  §1 to §8, in particular Definition 1.0.1, §3.5 to §3.8, Lemmas 4.2.1 and 4.2.3, Definition and
  Lemma 4.3.2 (log-shells), Claim 5.0.1, §6 (hulls, Lemma 6.3.1), §7 (Theorem 7.5.1,
  computations of `I_p` to `V_p`, Theorems 7.12.1 and 7.13.1) and §8 (Lemmas 8.1.1 and 8.1.2,
  Theorem 8.2.1).

No page of Mochizuki's papers was read for this file; IUT III, IUT IV and IUT I are cited only
as Dupuy and Hilado cite them. Formulas are taken from the TeX sources. Pages checked against
rendered images of the arXiv PDFs: [DH-Szpiro] (2004.13108v2) pages 2, 3, 13, 14, 18, 19, 25 to
35; [DH-ITD] (2004.13228v2) pages 1, 6, 12, 13, 14. Every display named in a docstring below was
compared with its rendered page; equation numbers are the printed ones.

## The formulation is Dupuy and Hilado's

[DH-ITD] Inequality 1.0.1 writes Corollary 3.12 as `−deĝ(P_q) ≤ −deĝ_lgp(P_{hull(U_Θ)})` and
calls it "a compact version of what is stated in the PRIMS volume", corresponding to the last
sentence of the corollary. [DH-Szpiro] Theorem 7.5.1 ("Tautological Probabilistic Inequality")
states, "Using the Probabilistic formalism developed in [DH20b, §3.1.2]", that assuming
Corollary 3.12, `−deĝ_{F_0}(P_q) ≤ Σ_p E²_p(ln R°_{v⃗})` (7.3), where
`R°_{v⃗} = sup {R : U_{v⃗} ⊂ D_{L_{v⃗}}(0, R)}` (7.2, printed with `sup`; the hull radius would be
the infimum) and `U_{v⃗}` is "the component of the multiradial representation in `L_{v⃗}`". This
is their reading of the corollary, not Mochizuki's statement, and nothing here is a statement of
Corollary 3.12.

Every main result of [DH-Szpiro] (Theorems 1.0.3 to 1.0.5, 7.12.1, 7.13.1, 8.2.1) assumes:

1. Corollary 3.12 in the form (7.3);
2. Claim 5.0.1 (archimedean hulls: `ln R_{v⃗} = (j+1) ln π`), attributed to IUT IV Proposition 1.5
   and Step (vii) of the proof of Theorem 1.10, and not proved;
3. that `E/F` sits in initial theta data ([DH-ITD] Definition 2.8.1: pre theta data with
   non-arithmeticity, `ρ_l(G_F) ⊇ SL_2(F_l)` with `F/ℚ(j_E)` Galois, `√−1 ∈ F` and
   `E[30] ⊆ E(F)` (30-torsion where IUT I gives 6-torsion, by the authors' choice, made because
   IUT IV later imposes a condition on 30-torsion, [DH-ITD] Remark 2.4.2), a non-empty set of odd
   multiplicative places, `l ≥ 5`, `l ∤ char(v)`, `l ∤ ord_v(q_v)`, `l ∤ [F : ℚ(j_E)]`; a lift
   `V̲` of `V(ℚ(j_E))`; `M̲` and `ε̲` in place of IUT I's `C̲_K` and cusp, an equivalence they
   claim and sketch, [DH-ITD] Remark 2.9.3) built from the field of moduli ([DH-Szpiro]
   Definition 1.0.1: `F = F_0(√−1, E_0[30])`, `F_0 = ℚ(j_E)`, all multiplicative places).
   [DH-Szpiro] cites §5 of version 1 of [DH-ITD] for the definition of initial theta data; that
   version was not available, and Definition 2.4.1 (and Definition 2.8.1) of version 2 is used in
   its place. The authors state `l ≥ 5` ([DH-ITD] Definition 2.4.1 (5c)); [DH-Szpiro] states no
   bound. The range `l ≥ 7` used below is an inference, not a statement of the papers: the
   30-torsion condition makes the mod 5 representation `ρ_5(G_F)` trivial, so `l = 5` cannot
   satisfy the condition `ρ_l(G_F) ⊇ SL_2(F_l)`;
4. semistability (§3.5);
5. for the hull bound, the stand-in `Aut(L : I)` for ind1 and ind2 (§6.2) and "the main result
   concerning ind3", cited to a reference that does not resolve in their bibliography (printed
   `[?]`);
6. Lemma 4.2.3 of [DH-Szpiro] (bounds for the `p`-adic logarithm over a finite extension of
   `ℚ_p`), stated with proofs omitted ("We state these results and omit the proofs").

The hull material (polyradius, hull, the rules for unions and scaling, the determinant
sentence) is in §6.1 of [DH-Szpiro], pages 18 to 19; version 2 of [DH-ITD] has no section on
hulls.

## Why there is no `Prop` for the inequality

The region `U_{v⃗}` (equivalently `U_p^{(j)} = ind2(ind1(O^{ind3(a⃗_j)}))`, §6.3) is built from
the indeterminacies ind1, ind2, ind3, the peel decomposition and the "fake adeles", whose
definitions [DH-Szpiro] cites to the 2020 version of [DH-ITD] (§3.1 to §3.3, §3.3.7, §4) and to a
paper on the third indeterminacy, neither of which is available here; version 2 of [DH-ITD]
no longer contains them. The probability formalism behind `E²_p` is cited to the same place. The
toy region of §6.2 needs `O_L^{ind3(a)}` as well. Further, `P_q` is defined from Tate parameters
and `ln|Δ^min_{E/F}|` from minimal discriminants over number fields, which Mathlib does not
have; and `L_{v⃗}` is a tensor product of local fields split by the Chinese remainder theorem,
which is not available either. So no restricted inequality can be stated with every term
defined; this file states none. The local objects are defined below for a finite family of
normed fields (in place of the factors of `L_{v⃗}`), and the deductions take the numbers they use
as explicit hypotheses.

## Contents

Local layer (§4, §6.1):
* `dhPolyRadius`, `dhPolydisc`, `dhHull`: the polyradius `R_i(Ω) = sup |x_i|` (in `[0, ∞]`) and
  the hull `D(0, R⃗(Ω))`; `dhHull_isHullMap` (conditions (P1) to (P3) of IUT III Remark 3.9.5 (ii)
  for polydiscs), `dhPolyRadius_iUnion`, `dhPolyRadius_mul` (the two rules of §6.1).
* `dh_det_one_not_hull_subset`: the sufficient condition "`A ⊂~ B` if `T(A) ⊂ B` for a linear `T`
  with `|det T|_p = 1`" of §6.1 (page 19), as printed, fails (`T = diag(p, p⁻¹)` on `ℚ_p²`). The
  instance the paper names, multiplication by a unit of `L`, holds by `dhPolyRadius_mul` when the
  unit is a unit of `O_L`; multiplication by the invertible element `(p, p⁻¹)` of `L` is the
  counterexample itself.
* `dh_crude_log_estimate`: Lemma 4.2.1 for `a ∈ ℚ_p`; `dh_log_units_subset_disc`: Lemma 4.2.3 (1)
  for `K = ℚ_p`. Lemma 4.2.3 (2) and Lemma 4.3.2 for `K = ℚ_p` are already in
  `IUT.Prerequisites.PadicLog` (`padicLogUnit_range_of_ne_two`, `padicLogShell_eq_two_mul`,
  `padicInt_subset_padicLogShell`, `padicLogUnit_range_subset_padicLogShell`). Ramified `K` and
  tensor products are not treated. The normalized log-volume `ln μ(A)/dim V` of §7.4 is not
  defined here: the paper does not fix the normalization of `μ`
  (`IUT.PaperIII.Corollary312.logVolume` is the unnormalized version).

Deductions (§3.8, §7, §8), all real arithmetic:
* pilot degrees from given data (`dhQPilotDegreeOfData`, `dhThetaPilotDegreeOfData`,
  `dhThetaPilotLgpDegreeOfData`), the relation `deĝ_lgp(P_Θ) = (l(l+1)/12) deĝ(P_q)`
  (`dhThetaPilotLgp_eq_mul_qPilot`), and the fact that display (3.3) as printed, which has
  the factor on the other side, would force `deĝ(P_q) = 0`; the numbers of the example 11a1;
* label averages (`dh_avg_id`, `dh_avg_succ`, `dh_sum_sq`), Lemma 7.7.1 (1), the bound (7.11) on
  `III_p`, a bound on `IV_p` that holds (`dh_IV_bound`);
* `dh_IV_printed_bound_fails`, `dh_IV_printed_exponent_bound_fails`, `dh_combined_bound_fails`:
  the bound (7.12) on `IV_p` as printed (with the exponent read as `(l+1)/2`, and with the
  exponent `l + 1/2` exactly as printed) and the step from the four terms to the summand of
  `A_{l,V}` in the proof of Theorem 7.12.1 fail at `l = 7` for `P_unr = 1/2` and `9/10`, because
  `ln b_p < 0`; these concern one display or step each, not the theorem. The step holds at
  `P_unr = 0` (`dh_combined_bound_P_zero`); `P_unr ∈ {0, 1}` when `F_0 = ℚ`. Values
  `0 < P_unr < 1` need `F_0 ≠ ℚ`; no stated assumption excludes them, and whether they occur
  for curves in initial theta data is not examined;
* the coefficient identities with `6 + ε_l` and `24 + ε_l`, the final algebra of Theorem 7.12.1
  from its intermediate display (`dh_probSzpiro_of_intermediate`, a conditional theorem), the last
  step of Theorem 7.13.1 and the numerical claims around it, and the last steps of Theorem 8.2.1
  (`dh_explicit_pre_result`, `dh_explicit_constant` with Dusart's bound at one point as a
  hypothesis, `dh_explicit_exp`).

## Interpretation choices, recorded

* `l = 2n + 1` throughout, so `2/(l−1) = 1/n`. The exponent is printed `l+1/2` in (7.12), in
  Theorem 1.0.3 and in the first display of the proof of Theorem 7.12.1, and `(l+1)/2` in (7.11)
  and (7.15); it is read as `(l+1)/2 = n + 1`. The failure of (7.12) is proved for both the
  reading and the printed exponent (`dh_IV_printed_bound_fails`,
  `dh_IV_printed_exponent_bound_fails`).
* `b_p`, printed "`1/exp(1) ln(p)`", is read as `(exp(1) ln p)⁻¹`, the constant `c_p` of Lemma
  4.2.1 (written there with parentheses), which Lemma 6.3.1 uses in place of `c_p`. Then
  `ln b_p < 0` for every prime (`dh_log_bp_neg`). Under the other parse `(ln p)/exp(1)`,
  `ln b_p < 0` only for `p ≤ 13`, which still includes `p = 2`.
* Sums `Σ_p` over all primes are sums over a given finite set of primes.
* The polyradius uses `sup` in `[0, ∞]` where the paper writes `max`; for compact regions they
  agree.
* `IUT.PaperIV.LocalFields` and `IUT.PaperIII.Corollary312` are not imported: the local
  statements here are over `ℚ_p` only, which `IUT.Prerequisites.PadicLog` covers, and no
  declaration here needs the region comparison or log-volume of `Corollary312`.
-/

namespace IUT.Applications.DupuyHilado

open Finset IUT.Prerequisites.PadicLog IUT.PaperIII.Remark3_9_5

/-! ## Polyradii and hulls of regions in a finite product of normed groups (§6.1) -/

section Hull

variable {ι : Type*} {X : ι → Type*} [∀ i, NormedAddCommGroup (X i)]

/-- The polyradius of a region `Ω ⊆ ∏ X i` (§6.1 of the Szpiro paper): its `i`-th component is
`R_i(Ω) = sup {|x_i| : x ∈ Ω}`, taken in `[0, ∞]` so that it is defined for every region. -/
noncomputable def dhPolyRadius (Ω : Set (∀ i, X i)) (i : ι) : ENNReal :=
  ⨆ x ∈ Ω, ENNReal.ofReal ‖x i‖

/-- The closed polydisc `D(0, r) = {x | |x_i| ≤ r_i for all i}` of polyradius `r`. -/
def dhPolydisc (r : ι → ENNReal) : Set (∀ i, X i) :=
  {x | ∀ i, ENNReal.ofReal ‖x i‖ ≤ r i}

/-- The hull of a region (§6.1): the polydisc of its polyradius, `hull(Ω) = D(0, R(Ω))`. -/
noncomputable def dhHull (Ω : Set (∀ i, X i)) : Set (∀ i, X i) :=
  dhPolydisc (dhPolyRadius Ω)

theorem dh_subset_hull (Ω : Set (∀ i, X i)) : Ω ⊆ dhHull Ω := fun x hx i =>
  le_iSup₂ (f := fun y (_ : y ∈ Ω) => ENNReal.ofReal ‖y i‖) x hx

theorem dhPolyRadius_mono {Ω Ω' : Set (∀ i, X i)} (h : Ω ⊆ Ω') (i : ι) :
    dhPolyRadius Ω i ≤ dhPolyRadius Ω' i :=
  biSup_mono fun _ hx => h hx

theorem dhPolyRadius_polydisc_le (r : ι → ENNReal) (i : ι) :
    dhPolyRadius (dhPolydisc (X := X) r) i ≤ r i :=
  iSup₂_le fun _ hx => hx i

/-- The hull of a polydisc is the polydisc itself, whether or not its radii are attained. -/
theorem dhHull_polydisc (r : ι → ENNReal) : dhHull (dhPolydisc (X := X) r) = dhPolydisc r :=
  Set.Subset.antisymm (fun _ hx i => (hx i).trans (dhPolyRadius_polydisc_le r i))
    (dh_subset_hull _)

/-- The polydisc hull satisfies the conditions (P1), (P2), (P3) of IUT III Remark 3.9.5 (ii),
with all regions as `ℙ` and the polydiscs as `ℍ`. -/
theorem dhHull_isHullMap :
    IsHullMap Set.univ (Set.range (dhPolydisc (X := X))) (dhHull (X := X)) where
  hull_sub _ _ := Set.mem_univ _
  maps_to P _ := ⟨dhPolyRadius P, rfl⟩
  P1 := by rintro _ ⟨r, rfl⟩; exact dhHull_polydisc r
  P2 P _ := dh_subset_hull P
  P3 _ _ _ _ h _ hx i := (hx i).trans (dhPolyRadius_mono h i)

/-- The `j`-th radius of a union is the supremum of the `j`-th radii (§6.1, possibly `∞`). -/
theorem dhPolyRadius_iUnion {κ : Type*} (Ω : κ → Set (∀ i, X i)) (j : ι) :
    dhPolyRadius (⋃ k, Ω k) j = ⨆ k, dhPolyRadius (Ω k) j := by
  simp only [dhPolyRadius]
  apply le_antisymm
  · refine iSup₂_le fun x hx => ?_
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    exact le_iSup_of_le k (le_iSup₂_of_le x hk le_rfl)
  · exact iSup_le fun k => biSup_mono fun x hx => Set.mem_iUnion.mpr ⟨k, hx⟩

end Hull

section HullScaling

variable {ι : Type*} {X : ι → Type*} [∀ i, NormedField (X i)]

/-- Scaling (§6.1): for `α ∈ ∏ X i`, `R_i(α · Ω) = |α_i| · R_i(Ω)`. -/
theorem dhPolyRadius_mul (α : ∀ i, X i) (Ω : Set (∀ i, X i)) (i : ι) :
    dhPolyRadius ((fun x => α * x) '' Ω) i = ENNReal.ofReal ‖α i‖ * dhPolyRadius Ω i := by
  simp only [dhPolyRadius, ENNReal.mul_iSup]
  apply le_antisymm
  · refine iSup₂_le ?_
    rintro _ ⟨x, hx, rfl⟩
    refine le_iSup₂_of_le x hx (le_of_eq ?_)
    show ENNReal.ofReal ‖α i * x i‖ = _
    rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
  · refine iSup₂_le fun x hx => le_iSup₂_of_le (α * x) ⟨x, hx, rfl⟩ (le_of_eq ?_)
    show _ = ENNReal.ofReal ‖α i * x i‖
    rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]

end HullScaling

/-! ### The sufficient condition of §6.1 with `|det T| = 1` fails -/

section DetCounterexample

variable (p : ℕ) [hp : Fact p.Prime]

/-- The `ℚ_p`-linear map `diag(p, p⁻¹)` of `ℚ_p²`. -/
noncomputable def dhDiagMap : (Fin 2 → ℚ_[p]) →ₗ[ℚ_[p]] (Fin 2 → ℚ_[p]) :=
  Matrix.toLin' (Matrix.diagonal ![(p : ℚ_[p]), (p : ℚ_[p])⁻¹])

theorem dhDiagMap_det_norm : ‖LinearMap.det (dhDiagMap p)‖ = 1 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [dhDiagMap, LinearMap.det_toLin', Matrix.det_diagonal, Fin.prod_univ_two]
  simp [hp0]

/-- **The sufficient condition of §6.1 of the Szpiro paper, as printed, fails** (page 19, a
sentence rather than a numbered display): "`A ⊂~ B` if there exists some `ℚ_p`-linear
transformation `T : L → L` with `|det(T)|_p = 1` and `T(A) ⊂ B`", where `L` is a finite direct sum
of `p`-adic fields and `A ⊂~ B` means `hull(A) ⊂ hull(B)`. On `L = ℚ_p ⊕ ℚ_p`, with
`T = diag(p, p⁻¹)`, `A` the unit polydisc and `B = T(A)`, the hull of `A` is not contained in the
hull of `B`. This `T` is multiplication by the invertible element `(p, p⁻¹)` of `L`; for a unit of
`O_L` the paper's example holds (`dhPolyRadius_mul`). The itemized justifications of (6.3) to (6.8)
do not cite this condition; whether a later step relies on it implicitly was not determined. -/
theorem dh_det_one_not_hull_subset :
    ‖LinearMap.det (dhDiagMap p)‖ = 1 ∧
      (dhDiagMap p) '' dhPolydisc (fun _ => 1) ⊆ (dhDiagMap p) '' dhPolydisc (fun _ => 1) ∧
      ¬ dhHull (dhPolydisc (X := fun _ : Fin 2 => ℚ_[p]) (fun _ => 1)) ⊆
        dhHull ((dhDiagMap p) '' dhPolydisc (fun _ => 1)) := by
  refine ⟨dhDiagMap_det_norm p, subset_rfl, fun h => ?_⟩
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  set x : Fin 2 → ℚ_[p] := ![1, 0]
  have hx : x ∈ dhHull (dhPolydisc (X := fun _ : Fin 2 => ℚ_[p]) (fun _ => 1)) := by
    rw [dhHull_polydisc]; intro i; fin_cases i <;> simp [x]
  have hle : dhPolyRadius ((dhDiagMap p) '' dhPolydisc (fun _ => 1)) 0 ≤
      ENNReal.ofReal (p : ℝ)⁻¹ := by
    refine iSup₂_le ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy0 : ‖y 0‖ ≤ 1 := ENNReal.ofReal_le_one.mp (hy 0)
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [dhDiagMap, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
    rw [show (![(p : ℚ_[p]), (p : ℚ_[p])⁻¹] 0) = (p : ℚ_[p]) from rfl, norm_mul,
      Padic.norm_p]
    exact mul_le_of_le_one_right (by positivity) hy0
  have h1 := (h hx 0).trans hle
  simp only [x, Matrix.cons_val_zero, norm_one, ENNReal.ofReal_one] at h1
  rw [ENNReal.one_le_ofReal] at h1
  exact absurd h1 (not_le.mpr (inv_lt_one_of_one_lt₀ hp1))

end DetCounterexample

/-! ## The p-adic logarithm over `ℚ_p` (§4.2) -/

section NatBounds

variable {p : ℕ}

/-- `e · ln p < p` for every natural number `p ≥ 2`; equivalently `c_p = (e ln p)⁻¹ > 1 / p`. -/
theorem dh_exp_one_mul_log_lt (hp2 : 2 ≤ p) : Real.exp 1 * Real.log p < p := by
  have he := Real.exp_pos 1
  have hpe : (p : ℝ) / Real.exp 1 ≠ 1 := by
    intro h
    have h' : (p : ℝ) = Real.exp 1 := by field_simp at h; linarith
    have h2 := Real.exp_one_gt_d9
    have h3 := Real.exp_one_lt_d9
    rcases Nat.lt_or_ge p 3 with h | h
    · have : p = 2 := by omega
      subst this; norm_num at h'; linarith
    · have : (3 : ℝ) ≤ p := by exact_mod_cast h
      linarith
  have hlog := Real.log_lt_sub_one_of_pos (by positivity) hpe
  rw [Real.log_div (by positivity) he.ne', Real.log_exp] at hlog
  have : Real.log p < p / Real.exp 1 := by linarith
  rw [lt_div_iff₀ he] at this
  linarith

/-- `p · k ≤ p ^ k` for `p ≥ 2` and `k ≥ 1`. -/
theorem dh_mul_le_pow {k : ℕ} (hp2 : 2 ≤ p) (hk : 1 ≤ k) : p * k ≤ p ^ k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have : m + 1 ≤ p ^ m := Nat.lt_pow_self (by omega)
  calc p * (m + 1) ≤ p * p ^ m := Nat.mul_le_mul_left p this
    _ = p ^ (m + 1) := by ring

end NatBounds

section PadicLogBounds

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Lemma 4.2.3 (1) of the Szpiro paper for `K = ℚ_p`** (so `e(K/ℚ_p) = 1`):
`log(ℤ_p^×) ⊆ D(0, 1 / (ln(p) · exp(1)))`. -/
theorem dh_log_units_subset_disc :
    Set.range (fun u : ℤ_[p]ˣ => padicLogUnit p ((u : ℤ_[p]) : ℚ_[p])) ⊆
      {z : ℚ_[p] | ‖z‖ ≤ (Real.log p * Real.exp 1)⁻¹} := by
  rw [padicLogUnit_range]
  intro z (hz : ‖z‖ ≤ _)
  refine hz.trans ?_
  have hp2 : 2 ≤ p := hp.out.two_le
  have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.out.one_lt)
  have hlt := dh_exp_one_mul_log_lt hp2
  have hstar : (p : ℝ) ≤ ((padicLogPStar p : ℕ) : ℝ) := by exact_mod_cast padicLog_pStar_ge
  exact inv_anti₀ (by positivity) (by nlinarith)

/-- **Lemma 4.2.1 of the Szpiro paper (crude estimate) for `a ∈ ℚ_p`**: if `ord_p(a) > 1`, then
`|log(1 + a)|_p < c_p / ord_p(a)` with `c_p = (exp(1) ln(p))⁻¹`. The paper states it for
`a ∈ ℂ_p`; here `a ∈ ℚ_p ⊆ ℂ_p` and `ord_p` is `Padic.valuation`. -/
theorem dh_crude_log_estimate {a : ℚ_[p]} (ha : a ≠ 0) (hv : 1 < a.valuation) :
    ‖padicLogOnePlus p a‖ < (Real.exp 1 * Real.log p)⁻¹ / a.valuation := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  obtain ⟨k, hk⟩ : ∃ k : ℕ, a.valuation = k := ⟨a.valuation.toNat, by omega⟩
  have hk2 : 2 ≤ k := by omega
  have hnorm : ‖a‖ = ((p : ℝ) ^ k)⁻¹ := by
    rw [Padic.norm_eq_zpow_neg_valuation ha, hk, zpow_neg, zpow_natCast]
  have hsmall : ‖a‖ ≤ ((padicLogPStar p : ℕ) : ℝ)⁻¹ := by
    rw [hnorm]
    refine inv_anti₀ (by unfold padicLogPStar; split_ifs <;> positivity) ?_
    have h2 : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ k := pow_le_pow_right₀ hp1.le hk2
    unfold padicLogPStar
    split_ifs with h
    · subst h; norm_num at h2 ⊢; linarith
    · nlinarith
  rw [padicLogOnePlus_norm_eq hsmall, hnorm, hk]
  have hlog : 0 < Real.log p := Real.log_pos hp1
  have hlt := dh_exp_one_mul_log_lt hp2
  have hpk : ((p * k : ℕ) : ℝ) ≤ ((p ^ k : ℕ) : ℝ) := by exact_mod_cast dh_mul_le_pow hp2 (by omega)
  push_cast at hpk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  rw [Int.cast_natCast, div_eq_mul_inv, ← mul_inv]
  refine inv_strictAnti₀ (by positivity) ?_
  calc Real.exp 1 * Real.log p * k < p * k := by nlinarith
    _ ≤ (p : ℝ) ^ k := hpk

end PadicLogBounds

/-! ## Pilot degrees from given data (§3.8) -/

section Pilots

variable {V : Type*} (S : Finset V) (ordq inertia resChar : V → ℕ) (d0 : ℕ)

/-- The normalized degree of the q-pilot divisor of Definition 3.8.1, computed from given data:
a finite set `S` of bad places `v` of `F_0` with `ord_v(q_v)`, the inertia degree `f_v`, the
residue characteristic `p_v`, `d_0 = [F_0 : ℚ]` and the prime `l`:
`deĝ(P_q) = (1/d_0) Σ_{v ∈ S} (ord_v(q_v)/(2l)) f_v ln p_v`. Nothing here asserts that the
numbers come from Tate parameters of an elliptic curve. -/
noncomputable def dhQPilotDegreeOfData (l : ℕ) : ℝ :=
  (1 / (d0 : ℝ)) * ∑ v ∈ S, (ordq v : ℝ) / (2 * l) * inertia v * Real.log (resChar v)

/-- The normalized degree of the `j`-th component `P_{Θ,j}` of the theta pilot divisor of
Definition 3.8.2, from the same data: coefficients `ord_v(q_v^{j²/2l}) = j² ord_v(q_v)/(2l)`. -/
noncomputable def dhThetaPilotDegreeOfData (l j : ℕ) : ℝ :=
  (1 / (d0 : ℝ)) * ∑ v ∈ S, (j : ℝ) ^ 2 * ordq v / (2 * l) * inertia v * Real.log (resChar v)

/-- The label average `deĝ_lgp(P_Θ) = (2/(l−1)) Σ_{j=1}^{(l−1)/2} deĝ(P_{Θ,j})` for
`l = 2n + 1`, so that `2/(l−1) = 1/n`. -/
noncomputable def dhThetaPilotLgpDegreeOfData (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * ∑ j ∈ Icc 1 n, dhThetaPilotDegreeOfData S ordq inertia resChar d0 (2 * n + 1) j

theorem dhThetaPilotDegreeOfData_eq (l j : ℕ) :
    dhThetaPilotDegreeOfData S ordq inertia resChar d0 l j =
      (j : ℝ) ^ 2 * dhQPilotDegreeOfData S ordq inertia resChar d0 l := by
  simp only [dhThetaPilotDegreeOfData, dhQPilotDegreeOfData, mul_sum]
  refine sum_congr rfl fun v _ => ?_
  ring

/-- `Σ_{j=1}^n j² = n(n+1)(2n+1)/6`. -/
theorem dh_sum_sq (n : ℕ) : ∑ j ∈ Icc 1 n, ((j : ℝ) ^ 2) = n * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero => simp
  | succ k ih => rw [sum_Icc_succ_top (by omega), ih]; push_cast; ring

/-- **The relation between the pilots (§3.8, derived direction)**: for `l = 2n + 1`,
`deĝ_lgp(P_Θ) = (l(l+1)/12) · deĝ(P_q)`. -/
theorem dhThetaPilotLgp_eq_mul_qPilot {n : ℕ} (hn : 1 ≤ n) :
    dhThetaPilotLgpDegreeOfData S ordq inertia resChar d0 n =
      ((2 * n + 1 : ℝ) * ((2 * n + 1 : ℝ) + 1) / 12) *
        dhQPilotDegreeOfData S ordq inertia resChar d0 (2 * n + 1) := by
  simp only [dhThetaPilotLgpDegreeOfData, dhThetaPilotDegreeOfData_eq, ← sum_mul, dh_sum_sq]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp
  ring

/-- **Display (3.3) of the Szpiro paper as printed** (§3.8, page 14) reads
`deĝ(P_q) = (l(l+1)/12) deĝ_lgp(P_Θ)`, the factor on the other side from the computation printed
directly below it, which gives `deĝ_lgp(P_Θ) = (l(l+1)/12) deĝ(P_q)`
(`dhThetaPilotLgp_eq_mul_qPilot`). Together with the derived relation the display as printed
forces `deĝ(P_q) = 0` as soon as `l ≥ 5`. The display as printed differs from the derived
relation; the proof of Theorem 7.12.1 (page 28), the left side of (8.9) and Remark 3.8.3 use the
derived relation, so the paper's conclusions do not depend on the display as printed, as far as
the text shows. -/
theorem dh_printed_pilot_relation_forces_zero {n : ℕ} (hn : 2 ≤ n)
    (h : dhQPilotDegreeOfData S ordq inertia resChar d0 (2 * n + 1) =
      ((2 * n + 1 : ℝ) * ((2 * n + 1 : ℝ) + 1) / 12) *
        dhThetaPilotLgpDegreeOfData S ordq inertia resChar d0 n) :
    dhQPilotDegreeOfData S ordq inertia resChar d0 (2 * n + 1) = 0 := by
  rw [dhThetaPilotLgp_eq_mul_qPilot S ordq inertia resChar d0 (by omega)] at h
  set c : ℝ := (2 * n + 1 : ℝ) * ((2 * n + 1 : ℝ) + 1) / 12
  have hc : 1 < c := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    simp only [c]; nlinarith
  have h' : (c * c - 1) * dhQPilotDegreeOfData S ordq inertia resChar d0 (2 * n + 1) = 0 := by
    linear_combination -h
  rcases mul_eq_zero.mp h' with h0 | h0
  · nlinarith
  · exact h0

/-- **The curve 11a1 (§2.10 of the initial theta data paper)**: with `F_0 = ℚ`, the single bad
place `11`, `ord_{11}(q) = 5`, `f = 1` and `l = 13`, the q-pilot degree is `ln(11⁵)/(2 · 13)`,
that is `ln|Δ^min_{E/ℚ}|/(2l)` for the minimal discriminant `Δ = −11⁵`. -/
theorem dh_qPilot_11a1 :
    dhQPilotDegreeOfData ({11} : Finset ℕ) (fun _ => 5) (fun _ => 1) (fun _ => 11) 1 13 =
      Real.log (11 ^ 5) / (2 * 13) := by
  simp only [dhQPilotDegreeOfData, sum_singleton, Real.log_pow]
  push_cast; ring

/-- The invariants of 11a1 recorded in §2.10: `c_4 = 496`, `c_6 = 20008` give
`Δ = (c_4³ − c_6²)/1728 = −11⁵` and `j = c_4³/Δ = −2¹² 31³ / 11⁵`. -/
theorem dh_invariants_11a1 :
    ((496 : ℤ) ^ 3 - 20008 ^ 2) = 1728 * (-(11 ^ 5)) ∧
      ((496 : ℚ) ^ 3 / (-(11 ^ 5)) = -(2 ^ 12 * 31 ^ 3) / 11 ^ 5) := by
  norm_num

/-- The congruence conditions of pre theta data for 11a1 with `l = 13` (§2.10): `13 ∤ 11`,
`13 ∤ ord(q) = 5`, `13 ≥ 5`, and `13` divides no divisor of `276480 = 2 · 6 · 48 · 480`, the
bound for `[F : ℚ]` read off from the table of `|GL_2(F_r)|`, `r = 2, 3, 5`, and the adjunction
of `√−1`. -/
theorem dh_congruence_11a1 :
    ¬ 13 ∣ 11 ∧ ¬ 13 ∣ 5 ∧ 5 ≤ 13 ∧ 2 * 6 * 48 * 480 = 276480 ∧
      ∀ d, d ∣ 276480 → ¬ 13 ∣ d := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, fun d hd h13 => ?_⟩
  have : 13 ∣ 276480 := h13.trans hd
  norm_num at this

end Pilots

/-! ## Label averages and the per-prime bounds of §7 -/

section Averages

theorem dh_card_Icc_one (n : ℕ) : ((Icc 1 n).card : ℝ) = n := by
  rw [Nat.card_Icc]; push_cast; simp

/-- An average over `j ∈ {1, …, n}` of terms bounded by `c` is bounded by `c`. -/
theorem dh_avg_le_of_le {n : ℕ} (hn : 1 ≤ n) {f : ℕ → ℝ} {c : ℝ}
    (h : ∀ j ∈ Icc 1 n, f j ≤ c) : 1 / (n : ℝ) * ∑ j ∈ Icc 1 n, f j ≤ c := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs := sum_le_card_nsmul (Icc 1 n) f c h
  rw [nsmul_eq_mul, dh_card_Icc_one] at hs
  rw [one_div, inv_mul_le_iff₀ hn0]
  linarith

/-- `(1/n) Σ_{j=1}^n j = (n+1)/2`, which is `(l+1)/4` for `l = 2n + 1` (§7.7). -/
theorem dh_avg_id {n : ℕ} (hn : 1 ≤ n) :
    1 / (n : ℝ) * ∑ j ∈ Icc 1 n, (j : ℝ) = ((2 * n + 1 : ℝ) + 1) / 4 := by
  have h : ∀ m : ℕ, ∑ j ∈ Icc 1 m, (j : ℝ) = m * (m + 1) / 2 := by
    intro m
    induction m with
    | zero => simp
    | succ k ih => rw [sum_Icc_succ_top (by omega), ih]; push_cast; ring
  rw [h]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp
  ring

/-- `(1/n) Σ_{j=1}^n (j+1) = (n+3)/2`, which is `(l+5)/4` for `l = 2n + 1` (§7.9, §7.10, §7.11). -/
theorem dh_avg_succ {n : ℕ} (hn : 1 ≤ n) :
    1 / (n : ℝ) * ∑ j ∈ Icc 1 n, ((j : ℝ) + 1) = ((2 * n + 1 : ℝ) + 5) / 4 := by
  have h : ∀ m : ℕ, ∑ j ∈ Icc 1 m, ((j : ℝ) + 1) = m * (m + 3) / 2 := by
    intro m
    induction m with
    | zero => simp
    | succ k ih => rw [sum_Icc_succ_top (by omega), ih]; push_cast; ring
  rw [h]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp
  ring

/-- **Lemma 7.7.1 (1) of the Szpiro paper**, in the form used: for a finite family `a` with an
upper bound `M` (for instance `M = ‖a‖_∞`), `‖a‖_1 − M ≤ ((n−1)/n) ‖a‖_1` where `n` is the
number of terms. Nonnegativity is not needed. -/
theorem dh_l1_sub_linf_le {κ : Type*} (s : Finset κ) (hs : s.Nonempty) (a : κ → ℝ) {M : ℝ}
    (hM : ∀ i ∈ s, a i ≤ M) :
    ∑ i ∈ s, a i - M ≤ ((s.card : ℝ) - 1) / s.card * ∑ i ∈ s, a i := by
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have h := sum_le_card_nsmul s a M hM
  rw [nsmul_eq_mul] at h
  rw [sub_div, div_self hn.ne', sub_mul, one_mul, div_mul_eq_mul_div, one_mul]
  have : (∑ i ∈ s, a i) / s.card ≤ M := by
    rw [div_le_iff₀ hn]; linarith
  linarith

/-- **Display (7.11) of the Szpiro paper** (§7.8, page 26; the ramification term `III_p`): for
`0 ≤ P ≤ 1`,
`(1/n) Σ_{j=1}^n (1 − P^{j+1}) ≤ 1 − P^{n+1}`, with `n + 1 = (l+1)/2`. -/
theorem dh_avg_one_sub_pow_le {n : ℕ} (hn : 1 ≤ n) {P : ℝ} (h0 : 0 ≤ P) (h1 : P ≤ 1) :
    1 / (n : ℝ) * ∑ j ∈ Icc 1 n, (1 - P ^ (j + 1)) ≤ 1 - P ^ (n + 1) := by
  refine dh_avg_le_of_le hn fun j hj => ?_
  have : P ^ (n + 1) ≤ P ^ (j + 1) :=
    pow_le_pow_of_le_one h0 h1 (by have := (mem_Icc.mp hj).2; omega)
  linarith

/-- `ln b_p < 0` for every `x ≥ 2`, where `b_x = 1/(exp(1) ln x)` (§1, §6.3). -/
theorem dh_log_bp_neg {x : ℝ} (hx : 2 ≤ x) : Real.log ((Real.exp 1 * Real.log x)⁻¹) < 0 := by
  have h2 := Real.log_two_gt_d9
  have he := Real.exp_one_gt_d9
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  rw [Real.log_inv, neg_lt_zero]
  exact Real.log_pos (by nlinarith)

/-- `ln b_p ≤ −2` for every `x ≥ 16`. -/
theorem dh_log_bp_le_neg_two {x : ℝ} (hx : 16 ≤ x) :
    Real.log ((Real.exp 1 * Real.log x)⁻¹) ≤ -2 := by
  have h2 := Real.log_two_gt_d9
  have he := Real.exp_one_lt_d9
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have hlx : Real.log 16 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlpos : 0 < Real.log x := by linarith
  have hll : 1 ≤ Real.log (Real.log x) := by
    rw [Real.le_log_iff_exp_le hlpos]; linarith
  rw [Real.log_inv, Real.log_mul (Real.exp_pos 1).ne' hlpos.ne', Real.log_exp]
  linarith

/-- The correct direction of the bound on `IV_p` (§7.9 of the Szpiro paper, where display (7.12)
prints the other factor): since `ln b_p ≤ 0`, enlarging the factor `1 − P^{j+1}` bounds `IV_p`
from below; the bound from above uses the smallest factor `1 − P²`:
`ln(b) · (1/n) Σ (j+1)(1 − P^{j+1}) ≤ ((l+5)/4) ln(b) (1 − P²)`. -/
theorem dh_IV_bound {n : ℕ} (hn : 1 ≤ n) {P lb : ℝ} (h0 : 0 ≤ P) (h1 : P ≤ 1) (hlb : lb ≤ 0) :
    lb * (1 / (n : ℝ) * ∑ j ∈ Icc 1 n, ((j : ℝ) + 1) * (1 - P ^ (j + 1))) ≤
      ((2 * n + 1 : ℝ) + 5) / 4 * lb * (1 - P ^ 2) := by
  have hsum : (1 - P ^ 2) * ∑ j ∈ Icc 1 n, ((j : ℝ) + 1) ≤
      ∑ j ∈ Icc 1 n, ((j : ℝ) + 1) * (1 - P ^ (j + 1)) := by
    rw [mul_sum]
    refine sum_le_sum fun j hj => ?_
    have : P ^ (j + 1) ≤ P ^ 2 :=
      pow_le_pow_of_le_one h0 h1 (by have := (mem_Icc.mp hj).1; omega)
    have : (0 : ℝ) ≤ j + 1 := by positivity
    nlinarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have havg := dh_avg_succ hn
  have h3 : (1 - P ^ 2) * (((2 * n + 1 : ℝ) + 5) / 4) ≤
      1 / (n : ℝ) * ∑ j ∈ Icc 1 n, ((j : ℝ) + 1) * (1 - P ^ (j + 1)) := by
    rw [← havg, ← mul_assoc, mul_comm (1 - P ^ 2), mul_assoc]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  nlinarith

/-- **Display (7.12) of the Szpiro paper as printed fails** (§7.9, page 26):
`IV_p ≤ ((l+5)/4) ln(b_p)(1 − P_unr,p^{l+1/2})`, the exponent printed verbatim as `l+1/2`,
where the paper computes `IV_p = ln(b_p) (2/(l−1)) Σ_{j=1}^{(l−1)/2} (j+1)(1 − P^{j+1})`.
Here the exponent is read as `(l+1)/2 = n + 1`, the exponent of Theorem 7.12.1; the exponent
exactly as printed, `l + 1/2`, is treated in `dh_IV_printed_exponent_bound_fails`. With `l = 7`
(`n = 3`; by inference the smallest admissible prime, see the module docstring), `P_unr = 1/2`
and any `ln b < 0`, the value `(21/8) ln b` of `IV_p` exceeds the right side `(45/16) ln b`.
`ln b_p < 0` for every prime with `b_p = (e ln p)⁻¹` (`dh_log_bp_neg`), and for `p ≤ 13` under
the other parse of `b_p`. Values `0 < P_unr,p < 1` need `F_0 ≠ ℚ`; whether they occur is not
examined. The proof of Theorem 7.12.1 uses (7.12) in its first display; the correct upper bound
is `dh_IV_bound`. -/
theorem dh_IV_printed_bound_fails {lb : ℝ} (hlb : lb < 0) :
    ((2 * 3 + 1 : ℝ) + 5) / 4 * lb * (1 - (1 / 2 : ℝ) ^ (3 + 1)) <
      lb * (1 / (3 : ℝ) * ∑ j ∈ (Icc 1 3 : Finset ℕ),
        ((j : ℝ) + 1) * (1 - (1 / 2 : ℝ) ^ (j + 1))) := by
  rw [show (Icc 1 3 : Finset ℕ) = {1, 2, 3} by decide, sum_insert (by decide),
    sum_pair (by norm_num)]
  norm_num
  linarith

/-- **Display (7.12) of the Szpiro paper as printed, with the exponent exactly as printed, fails**
(§7.9, page 26): `IV_p ≤ ((l+5)/4) ln(b_p)(1 − P_unr,p^{l+1/2})`, with `l + 1/2` a real exponent.
With `l = 7`, `P_unr = 1/2` and any `ln b < 0`, the value `(21/8) ln b` of `IV_p` exceeds the
right side `3 (1 − 2^{−15/2}) ln b ≈ 2.9834 ln b` (at `ln b = ln b_11 ≈ −1.8746`: `−4.92` against
`−5.59`). The same provisos as for `dh_IV_printed_bound_fails` apply. -/
theorem dh_IV_printed_exponent_bound_fails {lb : ℝ} (hlb : lb < 0) :
    ((2 * 3 + 1 : ℝ) + 5) / 4 * lb * (1 - (1 / 2 : ℝ) ^ ((2 * 3 + 1 : ℝ) + 1 / 2)) <
      lb * (1 / (3 : ℝ) * ∑ j ∈ (Icc 1 3 : Finset ℕ),
        ((j : ℝ) + 1) * (1 - (1 / 2 : ℝ) ^ (j + 1))) := by
  have hx : (1 / 2 : ℝ) ^ ((2 * 3 + 1 : ℝ) + 1 / 2) ≤ (1 / 2 : ℝ) ^ ((7 : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
  rw [Real.rpow_natCast] at hx
  generalize (1 / 2 : ℝ) ^ ((2 * 3 + 1 : ℝ) + 1 / 2) = x at hx ⊢
  rw [show (Icc 1 3 : Finset ℕ) = {1, 2, 3} by decide, sum_insert (by decide),
    sum_pair (by norm_num)]
  norm_num at hx ⊢
  nlinarith [mul_neg_of_neg_of_pos hlb (show (0 : ℝ) < 3 * (1 - x) - 21 / 8 by linarith)]

/-- **The step from the four terms to the summand of `A_{l,V}` in the proof of Theorem 7.12.1
fails at `l = 7`, `P_unr = 9/10`, `p ≥ 17`** (pages 27 to 28). This is not a numbered display:
it is the passage, through (7.11), (7.12) and the division by `(l+5)/4`, from the exact terms
to the summand of `A_{l,V}` in (7.15). The proof turns `III_p + IV_p`, whose exact values the
paper prints in §7.8 and §7.9 as `(2/(l−1)) Σ_j (1 − P^{j+1})` and
`ln(b_p)(2/(l−1)) Σ_j (j+1)(1 − P^{j+1})`, into the summand `(1 − P^{(l+1)/2})(ln b_p + 5/(l+4))`
of `A_{l,V}`. With `l = 7` (by inference the smallest admissible prime),
`P_unr = 9/10` and `ln b ≤ −2` (true for every prime `p ≥ 17` with `b_p = (e ln p)⁻¹`,
`dh_log_bp_le_neg_two`), `(4/(l+5))(III_p + IV_p)` is larger than that summand. Values
`0 < P_unr,p < 1` need `F_0 ≠ ℚ`; whether they occur is not examined. The theorem concerns this
one step only; it says nothing about Theorem 7.12.1 itself. -/
theorem dh_combined_bound_fails {lb : ℝ} (hlb : lb ≤ -2) :
    (1 - (9 / 10 : ℝ) ^ (3 + 1)) * (lb + 5 / ((2 * 3 + 1 : ℝ) + 4)) <
      4 / ((2 * 3 + 1 : ℝ) + 5) *
        (1 / (3 : ℝ) * ∑ j ∈ (Icc 1 3 : Finset ℕ),
          (1 - (9 / 10 : ℝ) ^ (j + 1)) * (1 + ((j : ℝ) + 1) * lb)) := by
  rw [show (Icc 1 3 : Finset ℕ) = {1, 2, 3} by decide, sum_insert (by decide),
    sum_pair (by norm_num)]
  norm_num
  linarith

/-- For `P_unr = 0` (every place over `p` ramified) the step to the summand of `A_{l,V}` holds
for every `l = 2n + 1` and every `ln b`. (For `F_0 = ℚ`, `P_unr ∈ {0, 1}`; the case
`P_unr = 1` is not treated here.) -/
theorem dh_combined_bound_P_zero {n : ℕ} (hn : 1 ≤ n) (lb : ℝ) :
    4 / ((2 * n + 1 : ℝ) + 5) *
        (1 / (n : ℝ) * ∑ j ∈ Icc 1 n, (1 - (0 : ℝ) ^ (j + 1)) * (1 + ((j : ℝ) + 1) * lb)) ≤
      (1 - (0 : ℝ) ^ (n + 1)) * (lb + 5 / ((2 * n + 1 : ℝ) + 4)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have havg := dh_avg_succ hn
  have hS : ∑ j ∈ Icc 1 n, ((j : ℝ) + 1) = n * (((2 * n + 1 : ℝ) + 5) / 4) := by
    rw [← havg]; field_simp
  simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
    sub_zero, one_mul]
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one, dh_card_Icc_one, ← sum_mul, hS]
  have hl : (0 : ℝ) < (2 * n + 1 : ℝ) + 4 := by positivity
  have hl' : (0 : ℝ) < (2 * n + 1 : ℝ) + 5 := by positivity
  have e : 4 / ((2 * n + 1 : ℝ) + 5) *
      (1 / (n : ℝ) * (n + n * (((2 * n + 1 : ℝ) + 5) / 4) * lb)) =
      4 / ((2 * n + 1 : ℝ) + 5) + lb := by
    field_simp
  rw [e]
  have : 4 / ((2 * n + 1 : ℝ) + 5) ≤ 5 / ((2 * n + 1 : ℝ) + 4) := by
    rw [div_le_div_iff₀ hl' hl]; nlinarith
  linarith

end Averages

/-! ## Coefficients and the final algebra of the Szpiro-type inequalities (§7.12, §7.13, §8) -/

section Szpiro

/-- **The coefficient identity of the proof of Theorem 7.12.1**:
`(l(l+1)/12 − 1) (1/(2l)) (4/(l+5)) = 1/(6 + ε_l)` with `ε_l = 24(l+3)/(l² + l − 12)`. -/
theorem dh_coeff_six {l : ℝ} (hl : 5 ≤ l) :
    (l * (l + 1) / 12 - 1) * (1 / (2 * l)) * (4 / (l + 5)) =
      1 / (6 + 24 * (l + 3) / (l ^ 2 + l - 12)) := by
  have h1 : 0 < l ^ 2 + l - 12 := by nlinarith
  have h2 : 0 < l := by linarith
  have h3 : 0 < l + 5 := by linarith
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h3' := h3.ne'
  rw [show 6 + 24 * (l + 3) / (l ^ 2 + l - 12) = 6 * l * (l + 5) / (l ^ 2 + l - 12) by
    rw [eq_div_iff h1', add_mul, div_mul_cancel₀ _ h1']; ring]
  field_simp
  ring

/-- **The coefficient identity of the proof of Theorem 8.2.1**:
`(l(l+1)/12 − 1) (1/(2l)) (1/(l+5)) = 1/(24 + ε_l)` with `ε_l = 96(l+3)/(l² + l − 12)`. -/
theorem dh_coeff_twentyfour {l : ℝ} (hl : 5 ≤ l) :
    (l * (l + 1) / 12 - 1) * (1 / (2 * l)) * (1 / (l + 5)) =
      1 / (24 + 96 * (l + 3) / (l ^ 2 + l - 12)) := by
  have h1 : 0 < l ^ 2 + l - 12 := by nlinarith
  have h2 : 0 < l := by linarith
  have h3 : 0 < l + 5 := by linarith
  have h1' := h1.ne'
  have h2' := h2.ne'
  have h3' := h3.ne'
  rw [show 24 + 96 * (l + 3) / (l ^ 2 + l - 12) = 24 * l * (l + 5) / (l ^ 2 + l - 12) by
    rw [eq_div_iff h1', add_mul, div_mul_cancel₀ _ h1']; ring]
  field_simp
  ring

/-- **The final algebra of the proof of Theorem 7.12.1 (Probabilistic Szpiro)**, conditional.
Hypotheses: `hθ`, `hq`: the pilot relations `deĝ_lgp(P_Θ) = (l(l+1)/12) deĝ(P_q)`
(`dhThetaPilotLgp_eq_mul_qPilot`) and `deĝ(P_q) = X/(2l)` with `X = ln|Δ^min_{E/F}|/[F:ℚ]`
(display (3.2), which rests on Tate uniformization, Ogg's formula and Lemma 3.6.1, none of which
is formalized); `hinter`: the first display of the proof (page 28, unnumbered), which the paper
obtains from Theorem 7.5.1, Lemma 6.3.1, Claim 5.0.1 and the bounds (7.6), (7.8), (7.11),
(7.12) and (7.14), with `Σ_p` over a finite set `S`, `logDiff = ln Diff̄(V̲/ℚ)`,
`Punr p = P_{unr,p}`, `logb p = ln b_p`, `loge p = ln ē_p`. The display prints the exponent
verbatim as `l+1/2`, in `(1 − P_unr,p^{l+1/2})`; `hinter` reads it as `(l+1)/2 = n + 1`, the
exponent of (7.15), under which the final algebra closes (with `l + 1/2` taken literally, the
passage to (7.15) at a prime with `ln b_p + 4/(l+5) > 0` would need
`1 − P^{l+1/2} ≤ 1 − P^{(l+1)/2}`, which goes the other way).
The side conditions `hP0`, `hP1` (`0 ≤ P_{unr,p} ≤ 1`) and `hD` (`ln Diff̄ ≥ 0`) hold by
definition and are not displays of the paper. Conclusion: display (7.15) of Theorem 7.12.1 as
printed, with `5/(l+4)`. No hypothesis restates the conclusion; the theorem checks only the
final algebra and says nothing about whether `hinter` holds or about Theorem 7.12.1 itself.
The paper derives `hinter` using display (7.12), whose printed form fails when
`0 < P_{unr,p} < 1` (`dh_IV_printed_bound_fails`). -/
theorem dh_probSzpiro_of_intermediate {n : ℕ} (hn : 2 ≤ n) {l : ℝ} (hl : l = 2 * n + 1)
    (S : Finset ℕ) (Punr logb loge : ℕ → ℝ) {logDiff X dq dθ : ℝ}
    (hP0 : ∀ p ∈ S, 0 ≤ Punr p) (hP1 : ∀ p ∈ S, Punr p ≤ 1) (hD : 0 ≤ logDiff)
    (hθ : dθ = l * (l + 1) / 12 * dq) (hq : dq = X / (2 * l))
    (hinter : -dq ≤ -dθ + (l + 1) / 4 * logDiff +
      ∑ p ∈ S, (1 - Punr p ^ (n + 1)) * (1 + (l + 5) / 4 * logb p) +
      (l + 5) / 4 * ∑ p ∈ S, loge p + (l + 5) / 4 * Real.log Real.pi) :
    1 / (6 + 24 * (l + 3) / (l ^ 2 + l - 12)) * X ≤
      logDiff + ∑ p ∈ S, loge p +
        (Real.log Real.pi + ∑ p ∈ S, (1 - Punr p ^ (n + 1)) * (logb p + 5 / (l + 4))) := by
  have hl5 : 5 ≤ l := by
    rw [hl]; have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hl0 : 0 < l := by linarith
  have hc : 0 < 4 / (l + 5) := by positivity
  have hL : 1 / (6 + 24 * (l + 3) / (l ^ 2 + l - 12)) * X = 4 / (l + 5) * (dθ - dq) := by
    rw [← dh_coeff_six hl5, hθ, hq]; field_simp
  have h1 : dθ - dq ≤ (l + 1) / 4 * logDiff +
      ∑ p ∈ S, (1 - Punr p ^ (n + 1)) * (1 + (l + 5) / 4 * logb p) +
      (l + 5) / 4 * ∑ p ∈ S, loge p + (l + 5) / 4 * Real.log Real.pi := by linarith
  have h2 := mul_le_mul_of_nonneg_left h1 hc.le
  have e1 : 4 / (l + 5) * ((l + 1) / 4 * logDiff) = (l + 1) / (l + 5) * logDiff := by
    field_simp
  have e2 : 4 / (l + 5) * ∑ p ∈ S, (1 - Punr p ^ (n + 1)) * (1 + (l + 5) / 4 * logb p) =
      ∑ p ∈ S, (1 - Punr p ^ (n + 1)) * (logb p + 4 / (l + 5)) := by
    rw [mul_sum]; refine sum_congr rfl fun p _ => ?_; field_simp; ring
  have e3 : 4 / (l + 5) * ((l + 5) / 4 * ∑ p ∈ S, loge p) = ∑ p ∈ S, loge p := by field_simp
  have e4 : 4 / (l + 5) * ((l + 5) / 4 * Real.log Real.pi) = Real.log Real.pi := by field_simp
  rw [mul_add, mul_add, mul_add, e1, e2, e3, e4] at h2
  have h45 : 4 / (l + 5) ≤ 5 / (l + 4) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
  have hB : ∑ p ∈ S, (1 - Punr p ^ (n + 1)) * (logb p + 4 / (l + 5)) ≤
      ∑ p ∈ S, (1 - Punr p ^ (n + 1)) * (logb p + 5 / (l + 4)) := by
    refine sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (by linarith) ?_
    have := pow_le_one₀ (n := n + 1) (hP0 p hp) (hP1 p hp)
    linarith
  have hD' : (l + 1) / (l + 5) * logDiff ≤ logDiff := by
    have : (l + 1) / (l + 5) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    nlinarith
  rw [hL]
  linarith

/-- `exp 8 < 6840`, so `ln 6840 > 8`: the threshold `e⁸ ≈ 2981` is what the last step of the
proof of Theorem 7.13.1 (Baby Szpiro) needs. -/
theorem dh_exp_eight_lt : Real.exp 8 < 6840 := by
  have h := Real.exp_one_lt_d9
  have h8 : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h8]
  calc Real.exp 1 ^ 8 < (2.7182818286 : ℝ) ^ 8 := by gcongr
    _ < 6840 := by norm_num

/-- **The last step of the proof of Theorem 7.13.1 (Baby Szpiro)** (page 29): for `D, d ≥ e⁸`,
`ln(Dd) + ln(D) ln(d) + ln(D) ≤ (ln D + 2)(ln d + 2) ≤ ln(d^{5/4}) ln(D^{5/4})`, with
`D = |Disc(K/ℚ)|` and `d = [K:ℚ]`. The paper asserts `D, d ≥ |SL_2(F_l)| ≥ 6840`; see
`dh_SL2_card_values`. Whether `D, d ≥ e⁸` holds for every curve in the paper's setting was not
determined. -/
theorem dh_baby_final_step {D d : ℝ} (hD : Real.exp 8 ≤ D) (hd : Real.exp 8 ≤ d) :
    Real.log (D * d) + Real.log D * Real.log d + Real.log D ≤
        (Real.log D + 2) * (Real.log d + 2) ∧
      (Real.log D + 2) * (Real.log d + 2) ≤
        Real.log (d ^ (5 / 4 : ℝ)) * Real.log (D ^ (5 / 4 : ℝ)) := by
  have hD0 : 0 < D := lt_of_lt_of_le (Real.exp_pos 8) hD
  have hd0 : 0 < d := lt_of_lt_of_le (Real.exp_pos 8) hd
  have ha : 8 ≤ Real.log D := by rw [Real.le_log_iff_exp_le hD0]; exact hD
  have hb : 8 ≤ Real.log d := by rw [Real.le_log_iff_exp_le hd0]; exact hd
  rw [Real.log_mul hD0.ne' hd0.ne', Real.log_rpow hD0, Real.log_rpow hd0]
  constructor
  · nlinarith
  · nlinarith

/-- **The claim "`SL_2(F_l) ≥ 6840`" of the proof of Theorem 7.13.1 as printed** (page 29, a
sentence rather than a numbered display). This theorem proves the arithmetic of `l(l² − 1)` only:
it takes the values `120, 336, 1320, 2184, 4896, 6840` at `l = 5, 7, 11, 13, 17, 19`, and is
below `6840` for every `l ≤ 18`. The formula `|SL_2(F_l)| = l(l² − 1)` is standard and is not
proved here. With it, the group-order bound holds only from `l = 19` on, so it fails for
`l = 7, 11, 13, 17` (inside the range `l ≥ 7`, itself an inference; see the module docstring),
including the value `l = 13` of the 11a1 example. The step that follows
needs only `D, d ≥ e⁸` (`dh_exp_eight_lt`, `dh_baby_final_step`); whether the conclusion depends
on the printed claim beyond that was not determined. -/
theorem dh_SL2_card_values :
    5 * (5 ^ 2 - 1) = 120 ∧ 7 * (7 ^ 2 - 1) = 336 ∧ 11 * (11 ^ 2 - 1) = 1320 ∧
      13 * (13 ^ 2 - 1) = 2184 ∧ 17 * (17 ^ 2 - 1) = 4896 ∧ 19 * (19 ^ 2 - 1) = 6840 ∧
      ∀ l : ℕ, l ≤ 18 → l * (l ^ 2 - 1) < 6840 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  intro l hl
  interval_cases l <;> norm_num

/-- **The bound "`ω(N) ≤ ln(N)/ln²(N)`" of the proof of Theorem 7.13.1 as printed** (page 29,
an unnumbered display after (7.19) and (7.20)), with `ln²(N) = (ln N)²`, **fails for every
`N ≥ 3`**, both for the number of divisors (the definition of `ω` printed there) and for the
number of distinct prime factors: the right side is `1/ln N < 1`. For the iterated-logarithm
reading see `dh_omega_loglog_bound_fails`. The next step of the proof needs only `ω(D) ≤ ln D`;
for the number of distinct prime factors this holds for `D ≥ 7` (not formalized here), for the
number of divisors it does not (`D = 12`). So the conclusion of Theorem 7.13.1 does not rest on
the printed bound, as far as the text shows, provided `ω` counts distinct prime factors. -/
theorem dh_omega_printed_bound_fails {N : ℕ} (hN : 3 ≤ N) :
    Real.log N / Real.log N ^ 2 < (N.divisors.card : ℝ) ∧
      Real.log N / Real.log N ^ 2 < (N.primeFactors.card : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have he := Real.exp_one_lt_d9
  have hL : 1 < Real.log N := by rw [Real.lt_log_iff_exp_lt hN0]; linarith
  have hlt : Real.log N / Real.log N ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  have hd : (1 : ℝ) ≤ N.divisors.card := by
    have : 1 ≤ N.divisors.card :=
      card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
    exact_mod_cast this
  have hp : (1 : ℝ) ≤ N.primeFactors.card := by
    have : 1 ≤ N.primeFactors.card := card_pos.mpr (Nat.nonempty_primeFactors.mpr (by omega))
    exact_mod_cast this
  exact ⟨by linarith, by linarith⟩

/-- **The bound "`ω(N) ≤ ln(N)/ln²(N)`" of the proof of Theorem 7.13.1 as printed, read with
`ln²(N) = ln ln N`, also fails**: at `N = 210 = 2 · 3 · 5 · 7`, `ln 210 / ln ln 210 < 4`, while
`210` has four distinct prime factors and sixteen divisors. -/
theorem dh_omega_loglog_bound_fails :
    Real.log 210 / Real.log (Real.log 210) < ((210 : ℕ).primeFactors.card : ℝ) ∧
      Real.log 210 / Real.log (Real.log 210) < ((210 : ℕ).divisors.card : ℝ) := by
  have h5 : (5 : ℝ) < Real.log 210 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have h := Real.exp_one_lt_d9
    have e5 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e5]
    calc Real.exp 1 ^ 5 < (2.7182818286 : ℝ) ^ 5 := by gcongr
      _ < 210 := by norm_num
  have hll : Real.log 5 < Real.log (Real.log 210) := Real.log_lt_log (by norm_num) h5
  have h625 : Real.log 210 < 4 * Real.log 5 := by
    have e : Real.log ((5 : ℝ) ^ 4) = 4 * Real.log 5 := by rw [Real.log_pow]; norm_num
    rw [← e]; exact Real.log_lt_log (by norm_num) (by norm_num)
  have hl5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hpos : 0 < Real.log (Real.log 210) := by linarith
  have hlt : Real.log 210 / Real.log (Real.log 210) < 4 := by
    rw [div_lt_iff₀ hpos]; nlinarith
  have hsub1 : ({2, 3, 5, 7} : Finset ℕ) ⊆ (210 : ℕ).primeFactors := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rw [Nat.mem_primeFactors]
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  have hsub2 : ({2, 3, 5, 7} : Finset ℕ) ⊆ (210 : ℕ).divisors := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rw [Nat.mem_divisors]
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  have h4 : ({2, 3, 5, 7} : Finset ℕ).card = 4 := by decide
  have c1 := Finset.card_le_card hsub1
  have c2 := Finset.card_le_card hsub2
  rw [h4] at c1 c2
  have c1' : (4 : ℝ) ≤ ((210 : ℕ).primeFactors.card : ℝ) := by exact_mod_cast c1
  have c2' : (4 : ℝ) ≤ ((210 : ℕ).divisors.card : ℝ) := by exact_mod_cast c2
  exact ⟨by linarith, by linarith⟩

/-- **The group orders in Lemma 8.1.1**: `|GL_2(F_l)| ≤ l⁴`, and the constants of the tower:
`|GL_2(F_3)| · |GL_2(F_5)| = 48 · 480 = 23040` (for `F/F_2'`), `12` (for `F_2'/F_0`) and
`23040 · 12 = 276480`. -/
theorem dh_GL2_card_le (l : ℕ) [Fact l.Prime] :
    Nat.card (GL (Fin 2) (ZMod l)) ≤ l ^ 4 ∧ 48 * 480 = 23040 ∧ 23040 * 12 = 276480 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  rw [IUT.PaperIV.Theorem1_10.card_GL2]
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by have := (Fact.out : l.Prime).one_lt; omega⟩
  simp only [Nat.add_sub_cancel]
  nlinarith [Nat.zero_le k, Nat.zero_le (k * k)]

/-- **Display (8.10) of the proof of Theorem 8.2.1 (Explicit Szpiro)**, conditional (page 35).
Hypotheses: `hred` is (8.9) with its left side rewritten through the pilot relations and its
right side split into the three sums, as printed on page 35; `hsmall` is the penultimate line of
the proof of (8.7) (page 34), `((l+3) ln B + 1) π(B)`, whose `+1` the printed last line drops;
`hlarge` is the per-prime bound `((l+5)/2) ln(p) 1_ram(p)` that ends the proof of (8.4) (page 32;
the printed (8.4) has `(l+5)/4`), summed and combined with (8.5), as on page 35; `hinf` is (8.3)
(page 31). The side conditions `hl`, `hF`, `hPi` and `hlogB` (`ln B ≥ 1/2`, true for
`B = 276480 l⁴ d_0`) are not displays. No hypothesis restates the conclusion; the `+1` is
absorbed after division by `l + 5`. Variables: `X = ln|Δ^min_{E/F}|`, `Fdeg = [F:ℚ]`,
`LD = ln|Disc(F/ℚ)|`, `LC = ln|Cond(E/F)|`, `Pi = π(B)`, `logB = ln B`;
`Ssmall`, `Slarge`, `Sinf` are the three sums of `E²_p`. -/
theorem dh_explicit_pre_result {l X Fdeg LD LC Ssmall Slarge Sinf logB Pi : ℝ} (hl : 5 ≤ l)
    (hF : 0 < Fdeg) (hPi : 0 ≤ Pi) (hlogB : 1 / 2 ≤ logB)
    (hred : (l * (l + 1) / 12 - 1) * (1 / (2 * l)) * (X / Fdeg) ≤ Ssmall + Slarge + Sinf)
    (hsmall : Ssmall ≤ ((l + 3) * logB + 1) * Pi)
    (hlarge : Slarge ≤ (l + 5) / 2 * (2 * (LD / Fdeg + LC / Fdeg)))
    (hinf : Sinf ≤ (l + 5) / 4 * Real.log Real.pi) :
    1 / (24 + 96 * (l + 3) / (l ^ 2 + l - 12)) * X ≤
      (logB * Pi + Real.log Real.pi) * Fdeg + LD + LC := by
  have hl5 : 0 < l + 5 := by linarith
  have hpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  set T := (l * (l + 1) / 12 - 1) * (1 / (2 * l)) * (X / Fdeg) with hT
  have hcoef : 1 / (24 + 96 * (l + 3) / (l ^ 2 + l - 12)) * X = 1 / (l + 5) * T * Fdeg := by
    rw [← dh_coeff_twentyfour hl, hT]; field_simp
  have hsm : ((l + 3) * logB + 1) * Pi ≤ (l + 5) * (logB * Pi) := by nlinarith
  have hbound : T ≤ (l + 5) * (logB * Pi + (LD / Fdeg + LC / Fdeg) + Real.log Real.pi) := by
    nlinarith
  have h1 : 1 / (l + 5) * T ≤ logB * Pi + (LD / Fdeg + LC / Fdeg) + Real.log Real.pi := by
    rw [one_div, inv_mul_le_iff₀ hl5]; exact hbound
  have h2 := mul_le_mul_of_nonneg_right h1 hF.le
  have e : (logB * Pi + (LD / Fdeg + LC / Fdeg) + Real.log Real.pi) * Fdeg =
      (logB * Pi + Real.log Real.pi) * Fdeg + LD + LC := by field_simp; ring
  rw [hcoef]; linarith

/-- **The last bound of the proof of Theorem 8.2.1** (page 35), with Dusart's estimate, display
(8.8), taken at the one point `x = B` as an explicit hypothesis (`hDusart`:
`π(B) ≤ (B/ln B)(1 + 1.3/ln B)`, Dusart, Ramanujan J. 45 (2018)) and `[F:ℚ] ≤ d_1 d_0` with
`d_1 = 276480` (the bound on `[F:F_0]` of Lemma 8.1.1): `(ln(B) π(B) + ln π)[F:ℚ] ≤
d_1² (1 + 1.3/ln d_1) d_0² l⁴ + d_1 ln(π) d_0` for `B = l⁴ d_1 d_0`. The middle expression
printed on page 35 multiplies `ln π` by `l⁴ d_0` as well; the final line `A_0 d_0² l⁴ + B_0 d_0`
follows from the form proved here, not from that middle expression. The paper's
`A_0 = 84372107405` and `B_0 = 316495` are the ceilings of the two coefficients (a decimal
computation, not proved here). -/
theorem dh_explicit_constant {l d0 Fdeg Pi B : ℝ} (hl : 1 ≤ l) (hd0 : 1 ≤ d0) (hF0 : 0 ≤ Fdeg)
    (hF : Fdeg ≤ 276480 * d0) (hB : B = l ^ 4 * 276480 * d0)
    (hDusart : Pi ≤ B / Real.log B * (1 + 1.3 / Real.log B)) :
    (Real.log B * Pi + Real.log Real.pi) * Fdeg ≤
      276480 ^ 2 * (1 + 1.3 / Real.log 276480) * d0 ^ 2 * l ^ 4 +
        276480 * Real.log Real.pi * d0 := by
  have hl4 : 1 ≤ l ^ 4 := one_le_pow₀ hl
  have hBge : 276480 ≤ B := by rw [hB]; nlinarith
  have hld1 : 0 < Real.log 276480 := Real.log_pos (by norm_num)
  have hlB : Real.log 276480 ≤ Real.log B := Real.log_le_log (by norm_num) hBge
  have hlBpos : 0 < Real.log B := by linarith
  have hpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hk : 1 + 1.3 / Real.log B ≤ 1 + 1.3 / Real.log 276480 := by
    have := one_div_le_one_div_of_le hld1 hlB
    have h13 : (1.3 : ℝ) / Real.log B = 1.3 * (1 / Real.log B) := by ring
    have h13' : (1.3 : ℝ) / Real.log 276480 = 1.3 * (1 / Real.log 276480) := by ring
    rw [h13, h13']; linarith
  have h1 : Real.log B * Pi ≤ B * (1 + 1.3 / Real.log 276480) := by
    have := mul_le_mul_of_nonneg_left hDusart hlBpos.le
    have e : Real.log B * (B / Real.log B * (1 + 1.3 / Real.log B)) =
        B * (1 + 1.3 / Real.log B) := by field_simp
    rw [e] at this
    nlinarith
  have hk0 : 0 ≤ 1 + 1.3 / Real.log 276480 := by positivity
  have h2 : (Real.log B * Pi + Real.log Real.pi) * Fdeg ≤
      (B * (1 + 1.3 / Real.log 276480) + Real.log Real.pi) * (276480 * d0) := by
    have hnn : 0 ≤ B * (1 + 1.3 / Real.log 276480) + Real.log Real.pi := by positivity
    calc (Real.log B * Pi + Real.log Real.pi) * Fdeg
        ≤ (B * (1 + 1.3 / Real.log 276480) + Real.log Real.pi) * Fdeg :=
          mul_le_mul_of_nonneg_right (by linarith) hF0
      _ ≤ _ := mul_le_mul_of_nonneg_left hF hnn
  rw [hB] at h2 ⊢
  calc _ ≤ _ := h2
    _ = _ := by ring

/-- **Exponentiating (8.10)**: if `(1/(24+ε)) ln|Δ| ≤ C + ln|Disc| + ln|Cond|`, then
`|Δ| ≤ exp((24+ε) C) · (|Cond| · |Disc|)^{24+ε}`. With `C = A_0 d_0² l⁴ + B_0 d_0` this gives
the prefactor `exp((24 + ε_l) C)`; display (8.1) prints the prefactor `exp(C)`. This theorem
concerns the exponentiation step only, not Theorem 8.2.1. -/
theorem dh_explicit_exp {Δ Cond Disc ε C : ℝ} (hΔ : 0 < Δ) (hC : 0 < Cond) (hD : 0 < Disc)
    (hε : 0 < 24 + ε) (h : 1 / (24 + ε) * Real.log Δ ≤ C + Real.log Disc + Real.log Cond) :
    Δ ≤ Real.exp ((24 + ε) * C) * (Cond * Disc) ^ (24 + ε) := by
  have h' : Real.log Δ ≤ (24 + ε) * (C + Real.log Disc + Real.log Cond) := by
    have := mul_le_mul_of_nonneg_left h hε.le
    rwa [← mul_assoc, mul_one_div_cancel hε.ne', one_mul] at this
  rw [Real.rpow_def_of_pos (mul_pos hC hD), ← Real.exp_add]
  calc Δ = Real.exp (Real.log Δ) := (Real.exp_log hΔ).symm
    _ ≤ _ := by
      rw [Real.exp_le_exp, Real.log_mul hC.ne' hD.ne']
      linarith

end Szpiro

end IUT.Applications.DupuyHilado
