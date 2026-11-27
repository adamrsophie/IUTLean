import IUT.PaperIV.Theorem1_10.StepV
import IUT.PaperIV.LocalFields.TensorLogShell
import IUT.PaperII.Labels

/-!
# IUT IV, Theorem 1.10, Steps (iv), (vi) and (vii): the local estimates on their objects

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, proof of Theorem 1.10, Step (iv)
(pages 26 and 27), Step (vi) (page 29) and Step (vii) (pages 29 and 30); for comparison Step (v)
(pages 27 to 29) and Step (iii) (pages 25 and 26, the distinguished places). Also *Inter-universal
Teichmüller Theory I*, page 3 (the definitions `l^⋇ = (l − 1)/2` and `𝔽_l^⋇ = 𝔽_l^× / {±1}`).
Pages read for this file: IUT IV pages 13 to 16 and 25 to 31; IUT I page 3. Pages checked against
rendered images: IUT IV pages 26, 27, 29 and 30; IUT I page 3.

## What the pages say

* Step (iv), pages 26 and 27: to bound `C_Θ` one bounds the procession-normalized mono-analytic
  log-volume of the holomorphic hull of the union of the possible images of a Θ-pilot object in
  the multiradial representation of IUT III, Theorem 3.11. At each `v_ℚ` this is the component
  in `ℐ^ℚ(𝕊^±_{j+1}; …)` for each `j ∈ {1, …, l^⋇}`, "which we shall also regard as an element
  of `𝔽_l^⋇`", followed by the average over `j`. `𝕊^±_{j+1} = {0, 1, …, j}`, and the packet is
  a tensor product of `j + 1` copies, indexed by `𝕊^±_{j+1}`, of a direct sum over
  `𝕍(F_mod)_{v_ℚ}`; "in particular, for each collection `{v_i}_{i ∈ 𝕊^±_{j+1}}`" one estimates
  the component of that tensor product and then computes the weighted average over the
  collections.
* Step (vi), page 29: for `v_ℚ` nonarchimedean and not distinguished, Proposition 1.4 (iv) with
  `I = 𝕊^±_{j+1}`, `k_i = K_{v_i}` gives the inclusion `φ((R_I)^∼) ⊆ (R_I)^∼`, so `(R_I)^∼` is a
  container of the possible images; its log-volume, the upper bound `0`, is the final equality
  of Proposition 1.4 (iv); the procession-normalized upper bound "is clearly equal to 0".
* Step (vii), pages 29 and 30: for `v_ℚ` archimedean, Proposition 1.5 (iii), (iv) give the
  container `π^{j+1} · B_I`; since the log-volume of `B_I` is `0`, its log-volume is at most
  `(j + 1) · log(π)`; the procession-normalized upper bound is
  `(l+5)/4 · log(π) ≤ (l+1)/4 · 4`.

## What is proved

Step (iv).
* `stepsIVLabel`, `stepsIVLabel_bijective`: the class of `j` modulo `±1` identifies
  `{1, …, l^⋇}` with `𝔽_l^⋇ = (ZMod l)ˣ ⧸ ⟨−1⟩` (`IUT.PaperII.Labels.FlStar`) for every odd prime
  `l`.
* `stepsIV_tensor_components`: for modules `M_v`, the tensor product of `n` copies of `⊕_v M_v`
  is the direct sum, over the collections `w : Fin n → E`, of the tensor products
  `⊗_i M_{w i}`, the component of `⊗_i x_i` at `w` being `⊗_i (x_i)_{w i}` (Mathlib's
  `PiTensorProduct.ofDirectSumEquiv`). `Fin (j + 1)` stands for `𝕊^±_{j+1} = {0, …, j}`.
* `stepsIVCollectionAvg`, `stepsIVProcession`: the weighted average over collections with the
  weights `λ_Π` of Proposition 1.7 (as Step (v) uses it, page 28), and its average over
  `j ∈ {1, …, l^⋇}`. They are monotone (`stepsIVCollectionAvg_mono`, `stepsIVProcession_mono`),
  so upper bounds on the components pass to upper bounds on the procession-normalized value,
  and they fix values that do not depend on the collection (`stepsIVCollectionAvg_const`).
  `stepsIVProcession_stepV` checks that this averaging reproduces the first line of the display
  of page 29 from the bound `β_e` of Step (v).

Step (vi).
* `stepsVI_muLog_le_zero_of_subset`: every subset of a reference set `Λ` of positive finite
  measure has packet log-volume `≤ 0 = μ^log(Λ)`.
* `stepsVI_packet_container`: for any finite family of finite extensions of `ℚ_p`, indexed by
  `Fin (j + 1)`, the packet `⊗_i K_i` over `ℚ_p` has `μ^log((R_I)^∼) = 0` (Proposition 1.4 (i),
  (iv), from `packet_muLog_normalization_tensor`) and every subset of `(R_I)^∼` has
  `μ^log ≤ 0`.
* `stepsVI_two_factors`: for two factors (`j = 1`) with `p > 2` and `e_1 = e_2 = 1`, the
  hypotheses of Proposition 1.4 (iv), every admissible `φ` maps `(R_I)^∼` into `(R_I)^∼`
  (`tensorLog_prop1_4_iv`) and `μ^log(φ((R_I)^∼)) ≤ 0`; and the union of the images
  `φ((R_I)^∼)` over all admissible `φ` is `(R_I)^∼`.
* `stepsVI_procession_zero`, `stepsVI_procession_le_zero`: the procession-normalized value of
  the bound `0` is `0`, and the procession-normalized value of any components that are `≤ 0` is
  `≤ 0`.

Step (vii).
* `stepsVII_logVolume_smul`: on a finite-dimensional real normed space with a Haar measure, the
  log-volume normalized at `B` and divided by the real dimension satisfies
  `μ^log(c · B) = log(c)` for `c > 0`; so `μ^log(π^{j+1} · B) = (j + 1) · log(π)`
  (`stepsVII_logVolume_container`), and every subset of `π^{j+1} · B` of positive measure has
  `μ^log ≤ (j + 1) · log(π)` (`stepsVII_logVolume_le`).
* `stepsVII_unitBalls_logVolume`: the same for `B` the product of the closed unit balls in
  `ℂ^N` (`stepsVIIUnitBalls`), the integral structure of Proposition 1.5 (iii) read in the
  coordinates of the direct sum decomposition of `M_I` into `N` copies of `ℂ`.
* `stepsVII_procession`, `stepsVII_procession_le`: the procession-normalized value of these
  log-volumes is `(l+5)/4 · log(π) ≤ (l+1)/4 · 4` with `l = 2·l^⋇ + 1 ≥ 5`, and the same upper
  bound holds for any components bounded by `(j + 1) · log(π)`.

## Readings chosen here

* The archimedean log-volume is the logarithm of a Haar measure ratio divided by the real
  dimension. With this normalization the printed bound `(j + 1) · log(π)` is the log-volume of
  `π^{j+1} · B_I` when `B_I` has log-volume `0`, as page 30 asserts. The normalization of IUT
  III, Proposition 3.9 (iii), that the page cites is not formalized.
* The nonarchimedean packet is the tensor product over `ℚ_p` (`PiTensorProduct ℚ_[p] K`), as in
  `IUT.PaperIV.LocalFields.Packets`; the pages take it over `ℤ_p`.
* The weights of the weighted average over collections are the `λ_Π` of Proposition 1.7, as in
  Step (v) (page 28, `λ_e = [(F_mod)_v : ℚ_{v_ℚ}]`).

## Not proved

* The object of Step (iv): the procession-normalized mono-analytic log-volume of the
  holomorphic hull of the union of the possible images of a Θ-pilot object, the multiradial
  representation and the indeterminacies (Ind1) to (Ind3) of IUT III, Theorem 3.11 and
  Corollary 3.12. None is constructed here; that the containers above contain the possible
  images is the content of the IUT III input and is not formalized.
* Step (vi): that `v_ℚ ∈ 𝕍_ℚ^non \ 𝕍_ℚ^dst` gives `p > 2` and `e_i = 1` (conditions (D4) to
  (D7), page 25, on the global objects); here they are the hypotheses of Proposition 1.4 (iv).
  The inclusion `φ((R_I)^∼) ⊆ (R_I)^∼` for more than two factors (`j ≥ 2`): the library proves
  Proposition 1.4 (iv) for two factors only. The identification of `(R_I)^∼` with the tensor
  product of the log-shells ("precisely equal", page 29).
* Step (vii): the space `M_I` with its tensor product metric, the decomposition of Proposition
  1.5 (iii) into `2^{|I|−1}·|V|^{|I|}` copies of `ℂ`, the invariance of `B_I` under the
  primitive automorphisms, and the inclusion of Proposition 1.5 (iv) that puts the tensor
  products of elements of the log-shells into `π^{j+1} · B_I`. Here `B_I` enters through
  coordinates only (`stepsVIIUnitBalls`), and the container property is not proved.
-/

open Finset MeasureTheory
open scoped Pointwise

namespace IUT.PaperIV.Theorem1_10

/-! ## Step (iv): the labels `j ∈ {1, …, l^⋇}` as elements of `𝔽_l^⋇` -/

/-- `j ∈ {1, …, l^⋇}` is prime to the prime `l`. -/
theorem stepsIV_coprime {l : ℕ} [hp : Fact l.Prime] (j : Icc 1 (IUT.PaperII.Labels.lstar l)) :
    Nat.Coprime (j : ℕ) l := by
  have hj := Finset.mem_Icc.mp j.2
  have hlt : (j : ℕ) < l := by
    have := hj.2; unfold IUT.PaperII.Labels.lstar at this; have := hp.out.two_le; omega
  exact (Nat.coprime_of_lt_prime (by omega) hlt hp.out).symm

/-- The element of `𝔽_l^⋇ = 𝔽_l^× / {±1}` attached to `j ∈ {1, …, l^⋇}`: the class of the unit
`j mod l` (IUT IV page 27: `j` "which we shall also regard as an element of `𝔽_l^⋇`"). -/
def stepsIVLabel {l : ℕ} [Fact l.Prime] (j : Icc 1 (IUT.PaperII.Labels.lstar l)) :
    IUT.PaperII.Labels.FlStar l :=
  QuotientGroup.mk (ZMod.unitOfCoprime (j : ℕ) (stepsIV_coprime j))

/-- **Step (iv), the labels.** For an odd prime `l`, `j ↦ (j mod l) · {±1}` is a bijection from
`{1, …, l^⋇}` onto `𝔽_l^⋇`. -/
theorem stepsIVLabel_bijective {l : ℕ} [hp : Fact l.Prime] (hl : l ≠ 2) :
    Function.Bijective (stepsIVLabel (l := l)) := by
  have hodd : Odd l := hp.out.odd_of_ne_two hl
  have hinj : Function.Injective (stepsIVLabel (l := l)) := by
    intro i j hij
    rw [stepsIVLabel, stepsIVLabel, QuotientGroup.eq, Subgroup.mem_zpowers_iff] at hij
    obtain ⟨k, hk⟩ := hij
    have hpm : (((j : ℕ) : ZMod l) = (i : ℕ)) ∨ (((j : ℕ) : ZMod l) = -((i : ℕ) : ZMod l)) := by
      have hk' : ZMod.unitOfCoprime (j : ℕ) (stepsIV_coprime j)
          = ZMod.unitOfCoprime (i : ℕ) (stepsIV_coprime i) * (-1) ^ k := by
        rw [hk, mul_inv_cancel_left]
      have hv := congrArg (fun u : (ZMod l)ˣ => (u : ZMod l)) hk'
      simp only [ZMod.coe_unitOfCoprime, Units.val_mul] at hv
      rcases Int.even_or_odd k with he | ho
      · left; rw [hv, he.neg_one_zpow]; simp
      · right; rw [hv, ho.neg_one_zpow]; simp
    have hi := Finset.mem_Icc.mp i.2
    have hj := Finset.mem_Icc.mp j.2
    have hb := (IUT.PaperII.Labels.labelRep_bijective hodd).1
    have heq : IUT.PaperII.Labels.labelRep l ⟨(i : ℕ), by omega⟩
        = IUT.PaperII.Labels.labelRep l ⟨(j : ℕ), by omega⟩ := by
      apply Quotient.sound
      rcases hpm with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h, neg_neg])
    have := congrArg Fin.val (hb heq)
    exact Subtype.ext this
  refine hinj.bijective_of_nat_card_le ?_
  rw [IUT.PaperII.Labels.card_flStar hl, Nat.card_eq_fintype_card, Fintype.card_coe,
    Nat.card_Icc]
  omega

/-! ## Step (iv): components indexed by collections -/

/-- **Step (iv), the components.** The tensor product of `n` copies of a direct sum `⊕_{v ∈ E}
M_v` is the direct sum, over the collections `w : Fin n → E` ("not necessarily distinct"), of
the tensor products `⊗_i M_{w i}`; the component of `⊗_i x_i` at `w` is `⊗_i (x_i)_{w i}`. With
`n = j + 1`, `E = 𝕍(F_mod)_{v_ℚ}` and `M_v` the `ℚ`-span of the log-shell at `v`, this is the
decomposition of page 27. -/
theorem stepsIV_tensor_components (R : Type*) [CommSemiring R] {E : Type*} [Fintype E]
    (M : E → Type*) [∀ v, AddCommMonoid (M v)] [∀ v, Module R (M v)] (n : ℕ) :
    ∃ e : PiTensorProduct R (fun _ : Fin n => DirectSum E M) ≃ₗ[R]
        DirectSum (Fin n → E) (fun w => PiTensorProduct R (fun i => M (w i))),
      ∀ (x : Fin n → DirectSum E M) (w : Fin n → E),
        e (PiTensorProduct.tprod R x) w = PiTensorProduct.tprod R (fun i => x i (w i)) :=
  ⟨PiTensorProduct.ofDirectSumEquiv (κ := fun _ => E) (M := fun _ v => M v),
    fun x w => PiTensorProduct.ofDirectSumEquiv_tprod_apply x w⟩

/-! ## Step (iv): weighted averages over collections and the average over `j` -/

/-- The weighted average over the collections `w : Fin n → E` of local values `b w`, with the
weights `λ_Π w = ∏_i λ_{w i}` of Proposition 1.7. -/
noncomputable def stepsIVCollectionAvg {E : Type*} [Fintype E] (lam : E → ℝ) (n : ℕ)
    (b : (Fin n → E) → ℝ) : ℝ :=
  (∑ w : Fin n → E, b w * Proposition1_7.lamProd lam w) /
    ∑ w : Fin n → E, Proposition1_7.lamProd lam w

/-- The procession-normalized value: the average over `j ∈ {1, …, l^⋇}` of the weighted
averages over the collections indexed by `𝕊^±_{j+1}` (here `Fin (j + 1)`). -/
noncomputable def stepsIVProcession {E : Type*} [Fintype E] (lam : E → ℝ) (lstar : ℕ)
    (b : (j : ℕ) → (Fin (j + 1) → E) → ℝ) : ℝ :=
  1 / (lstar : ℝ) * ∑ j ∈ Icc 1 lstar, stepsIVCollectionAvg lam (j + 1) (b j)

theorem stepsIV_lamProd_pos {E : Type*} [Fintype E] {lam : E → ℝ} (hlam : ∀ v, 0 < lam v)
    {n : ℕ} (w : Fin n → E) : 0 < Proposition1_7.lamProd lam w :=
  Finset.prod_pos fun i _ => hlam (w i)

theorem stepsIV_sum_lamProd_pos {E : Type*} [Fintype E] [Nonempty E] {lam : E → ℝ}
    (hlam : ∀ v, 0 < lam v) (n : ℕ) : 0 < ∑ w : Fin n → E, Proposition1_7.lamProd lam w :=
  Finset.sum_pos (fun w _ => stepsIV_lamProd_pos hlam w) univ_nonempty

/-- A value that does not depend on the collection is its own weighted average. -/
theorem stepsIVCollectionAvg_const {E : Type*} [Fintype E] [Nonempty E] {lam : E → ℝ}
    (hlam : ∀ v, 0 < lam v) (n : ℕ) (c : ℝ) :
    stepsIVCollectionAvg lam n (fun _ => c) = c := by
  unfold stepsIVCollectionAvg
  rw [← Finset.mul_sum, mul_div_assoc, div_self (stepsIV_sum_lamProd_pos hlam n).ne', mul_one]

/-- Upper bounds pass to weighted averages. -/
theorem stepsIVCollectionAvg_mono {E : Type*} [Fintype E] [Nonempty E] {lam : E → ℝ}
    (hlam : ∀ v, 0 < lam v) {n : ℕ} {b b' : (Fin n → E) → ℝ} (h : ∀ w, b w ≤ b' w) :
    stepsIVCollectionAvg lam n b ≤ stepsIVCollectionAvg lam n b' := by
  unfold stepsIVCollectionAvg
  apply div_le_div_of_nonneg_right _ (stepsIV_sum_lamProd_pos hlam n).le
  exact Finset.sum_le_sum fun w _ =>
    mul_le_mul_of_nonneg_right (h w) (stepsIV_lamProd_pos hlam w).le

/-- Upper bounds pass to procession-normalized values. -/
theorem stepsIVProcession_mono {E : Type*} [Fintype E] [Nonempty E] {lam : E → ℝ}
    (hlam : ∀ v, 0 < lam v) (lstar : ℕ) {b b' : (j : ℕ) → (Fin (j + 1) → E) → ℝ}
    (h : ∀ j w, b j w ≤ b' j w) :
    stepsIVProcession lam lstar b ≤ stepsIVProcession lam lstar b' := by
  unfold stepsIVProcession
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum fun j _ => stepsIVCollectionAvg_mono hlam (h j)

/-- If the local value depends only on `j`, the procession-normalized value is the plain average
over `j ∈ {1, …, l^⋇}`. -/
theorem stepsIVProcession_const {E : Type*} [Fintype E] [Nonempty E] {lam : E → ℝ}
    (hlam : ∀ v, 0 < lam v) (lstar : ℕ) (c : ℕ → ℝ) :
    stepsIVProcession lam lstar (fun j _ => c j) = 1 / (lstar : ℝ) * ∑ j ∈ Icc 1 lstar, c j := by
  unfold stepsIVProcession
  congr 1
  exact Finset.sum_congr rfl fun j _ => stepsIVCollectionAvg_const hlam (j + 1) (c j)

/-- **The averaging of Step (iv) reproduces Step (v).** With the symmetrized local bound
`β_e⃗` of page 28 for `β_v = A_v − j²/(2l(j+1))·B_v + 1/(j+1)·log(p) + 4·ι·L`, the
procession-normalized value is the first line of the display of page 29:
`(l^⋇+3)/2·avg(A) − (2l^⋇+1)(l^⋇+1)/(12l)·avg(B) + log(p) + 2(l^⋇+3)·ι·L`. -/
theorem stepsIVProcession_stepV {E : Type*} [Fintype E] [Nonempty E] (lam Aloc Bloc : E → ℝ)
    (hlam : ∀ v, 0 < lam v) (n : ℕ) (hn : 1 ≤ n) (l logp iota L : ℝ) (hl : l ≠ 0) :
    stepsIVProcession lam n (fun j => Proposition1_7.betaVec
        (fun w => Aloc w - (j : ℝ) ^ 2 / (2 * l * (j + 1)) * Bloc w
          + 1 / (j + 1) * logp + 4 * iota * L))
      = (n + 3) / 2 * Proposition1_7.betaAvg lam Aloc
        - (2 * n + 1) * (n + 1) / (12 * l) * Proposition1_7.betaAvg lam Bloc
        + logp + 2 * (n + 3) * (iota * L) := by
  unfold stepsIVProcession
  have h : ∀ j ∈ Icc 1 n, stepsIVCollectionAvg lam (j + 1) (Proposition1_7.betaVec
        (fun w => Aloc w - (j : ℝ) ^ 2 / (2 * l * (j + 1)) * Bloc w
          + 1 / (j + 1) * logp + 4 * iota * L))
      = ((j : ℝ) + 1) * Proposition1_7.betaAvg lam Aloc
        - (j : ℝ) ^ 2 / (2 * l) * Proposition1_7.betaAvg lam Bloc + logp
        + 4 * ((j : ℝ) + 1) * (iota * L) := by
    intro j _
    have := step_v_weighted lam Aloc Bloc hlam j l logp iota L hl 0
    unfold stepsIVCollectionAvg
    rw [this]; ring
  rw [Finset.sum_congr rfl h]
  exact procession_average _ _ _ _ l n hn

/-! ## Step (vi): the container `(R_I)^∼` and the bound `0` -/

section StepVI

variable {p : ℕ} [hp : Fact p.Prime]

/-- Every subset of the reference set `Λ` (of positive finite measure) has packet log-volume
`≤ 0 = μ^log(Λ)`. With Lean's `Real.log 0 = 0`, a null subset has value `0`. -/
theorem stepsVI_muLog_le_zero_of_subset {W : Type*} [AddCommGroup W] [Module ℚ_[p] W]
    [FiniteDimensional ℚ_[p] W] [MeasurableSpace (Fin (Module.finrank ℚ_[p] W) → ℚ_[p])]
    (μ : Measure (Fin (Module.finrank ℚ_[p] W) → ℚ_[p])) {Λ A : Set W}
    (hΛ0 : μ ((Module.finBasis ℚ_[p] W).equivFun '' Λ) ≠ 0)
    (hΛ : μ ((Module.finBasis ℚ_[p] W).equivFun '' Λ) ≠ ⊤) (hA : A ⊆ Λ) :
    IUT.Prerequisites.PadicVolume.padicPacketMuLog p W μ Λ A ≤ 0 := by
  unfold IUT.Prerequisites.PadicVolume.padicPacketMuLog
  by_cases hA0 : μ ((Module.finBasis ℚ_[p] W).equivFun '' A) = 0
  · unfold IUT.Prerequisites.PadicVolume.padicMuLog
    simp [hA0]
  · have h := IUT.Prerequisites.PadicVolume.padicMuLog_mono p μ (Set.image_mono hA) hΛ0 hΛ
      hA0 hΛ
    rwa [IUT.Prerequisites.PadicVolume.padicMuLog_self] at h

/-- **Step (vi), the container and its log-volume, for any number of factors.** For finite
extensions `K_i` of `ℚ_p`, `i ∈ Fin (j + 1)`, the packet `⊗_i K_i` (over `ℚ_p`) has
`μ^log((R_I)^∼) = 0`, the upper bound "0" of page 29 (Proposition 1.4 (i), and the final
equality of (iv)), and every subset of `(R_I)^∼` has log-volume `≤ 0`. -/
theorem stepsVI_packet_container (j : ℕ) (K : Fin (j + 1) → Type) [∀ i, Field (K i)]
    [∀ i, Algebra ℚ_[p] (K i)] [∀ i, FiniteDimensional ℚ_[p] (K i)]
    [MeasurableSpace (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] K)) → ℚ_[p])]
    [BorelSpace (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] K)) → ℚ_[p])]
    (μ : Measure (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] K)) → ℚ_[p]))
    [μ.IsAddHaarMeasure] :
    IUT.Prerequisites.PadicVolume.padicPacketMuLog p (PiTensorProduct ℚ_[p] K) μ
        (IUT.PaperIV.LocalFields.packetNormalizationSet p (PiTensorProduct ℚ_[p] K))
        (IUT.PaperIV.LocalFields.packetNormalizationSet p (PiTensorProduct ℚ_[p] K)) = 0 ∧
      ∀ A ⊆ IUT.PaperIV.LocalFields.packetNormalizationSet p (PiTensorProduct ℚ_[p] K),
        IUT.Prerequisites.PadicVolume.padicPacketMuLog p (PiTensorProduct ℚ_[p] K) μ
          (IUT.PaperIV.LocalFields.packetNormalizationSet p (PiTensorProduct ℚ_[p] K)) A ≤ 0 := by
  obtain ⟨-, -, h0, hfin, hself, -⟩ :=
    IUT.PaperIV.LocalFields.packet_muLog_normalization_tensor p K μ
  exact ⟨hself, fun A hA => stepsVI_muLog_le_zero_of_subset μ h0 hfin hA⟩

/-- **Step (vi) for two factors (`j = 1`).** Let `K₁`, `K₂` be finite extensions of `ℚ_p` with
`p > 2` and ramification indices `e_1 = e_2 = 1` (the hypotheses of Proposition 1.4 (iv)), and
let `φ` be a `ℚ_p`-linear automorphism of `K₁ ⊗ K₂` preserving `log_p(R_I^×)`. Then
`φ((R_I)^∼) ⊆ (R_I)^∼` and `μ^log(φ((R_I)^∼)) ≤ 0 = μ^log((R_I)^∼)`. Moreover the union of the
images `φ((R_I)^∼)` over all such `φ` is `(R_I)^∼` (the identity is one of them). -/
theorem stepsVI_two_factors (K₁ K₂ : Type*) [Field K₁] [Field K₂] [Algebra ℚ_[p] K₁]
    [Algebra ℚ_[p] K₂] [FiniteDimensional ℚ_[p] K₁] [FiniteDimensional ℚ_[p] K₂]
    [Algebra ℤ_[p] K₁] [Algebra ℤ_[p] K₂] [IsScalarTower ℤ_[p] ℚ_[p] K₁]
    [IsScalarTower ℤ_[p] ℚ_[p] K₂]
    [MeasurableSpace (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) → ℚ_[p])]
    [BorelSpace (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) → ℚ_[p])]
    (μ : Measure (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) → ℚ_[p]))
    [μ.IsAddHaarMeasure]
    (P₁ : Ideal (integralClosure ℤ_[p] K₁)) [P₁.IsPrime]
    [P₁.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (P₂ : Ideal (integralClosure ℤ_[p] K₂)) [P₂.IsPrime]
    [P₂.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (hp2 : 2 < p) (he₁ : P₁.ramificationIdx ℤ_[p] = 1) (he₂ : P₂.ramificationIdx ℤ_[p] = 1) :
    (∀ φ : TensorProduct ℚ_[p] K₁ K₂ ≃ₗ[ℚ_[p]] TensorProduct ℚ_[p] K₁ K₂,
      φ '' IUT.PaperIV.LocalFields.tensorLogLattice p K₁ K₂
          = IUT.PaperIV.LocalFields.tensorLogLattice p K₁ K₂ →
        φ '' IUT.Prerequisites.PadicVolume.padicPacketNormalization p K₁ K₂
            ⊆ IUT.Prerequisites.PadicVolume.padicPacketNormalization p K₁ K₂ ∧
          IUT.Prerequisites.PadicVolume.padicPacketMuLog p (TensorProduct ℚ_[p] K₁ K₂) μ
            (IUT.Prerequisites.PadicVolume.padicPacketNormalization p K₁ K₂)
            (φ '' IUT.Prerequisites.PadicVolume.padicPacketNormalization p K₁ K₂) ≤ 0) ∧
      (⋃ φ : {φ : TensorProduct ℚ_[p] K₁ K₂ ≃ₗ[ℚ_[p]] TensorProduct ℚ_[p] K₁ K₂ //
          φ '' IUT.PaperIV.LocalFields.tensorLogLattice p K₁ K₂
            = IUT.PaperIV.LocalFields.tensorLogLattice p K₁ K₂},
        (φ : TensorProduct ℚ_[p] K₁ K₂ ≃ₗ[ℚ_[p]] TensorProduct ℚ_[p] K₁ K₂) ''
          IUT.Prerequisites.PadicVolume.padicPacketNormalization p K₁ K₂)
        = IUT.Prerequisites.PadicVolume.padicPacketNormalization p K₁ K₂ := by
  obtain ⟨h0, hfin, -, -⟩ := IUT.PaperIV.LocalFields.tensorLog_normalization_measure p K₁ K₂ μ
  refine ⟨fun φ hφ => ?_, ?_⟩
  · have hsub := (IUT.PaperIV.LocalFields.tensorLog_prop1_4_iv p K₁ K₂ μ P₁ P₂ hp2 he₁ he₂ φ
      hφ).1
    exact ⟨hsub, stepsVI_muLog_le_zero_of_subset μ h0 hfin hsub⟩
  · apply Set.Subset.antisymm
    · refine Set.iUnion_subset fun φ => ?_
      exact (IUT.PaperIV.LocalFields.tensorLog_prop1_4_iv p K₁ K₂ μ P₁ P₂ hp2 he₁ he₂ φ.1
        φ.2).1
    · intro x hx
      refine Set.mem_iUnion.2 ⟨⟨LinearEquiv.refl ℚ_[p] _, by
        rw [show ⇑(LinearEquiv.refl ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) = id from rfl,
          Set.image_id]⟩, ?_⟩
      exact ⟨x, hx, rfl⟩

/-- **Step (vi), the procession-normalized upper bound** "is clearly equal to 0": the
procession-normalized value of the local bound `0`. -/
theorem stepsVI_procession_zero {E : Type*} [Fintype E] (lam : E → ℝ) (lstar : ℕ) :
    stepsIVProcession lam lstar (fun _ _ => 0) = 0 := by
  simp [stepsIVProcession, stepsIVCollectionAvg]

/-- Step (vi): components whose log-volumes are `≤ 0` (as `stepsVI_packet_container` and
`stepsVI_two_factors` give for subsets of the container) have procession-normalized value
`≤ 0`. -/
theorem stepsVI_procession_le_zero {E : Type*} [Fintype E] [Nonempty E] {lam : E → ℝ}
    (hlam : ∀ v, 0 < lam v) (lstar : ℕ) {x : (j : ℕ) → (Fin (j + 1) → E) → ℝ}
    (hx : ∀ j w, x j w ≤ 0) : stepsIVProcession lam lstar x ≤ 0 := by
  have := stepsIVProcession_mono hlam lstar (b := x) (b' := fun _ _ => 0) hx
  rwa [stepsVI_procession_zero] at this

end StepVI

/-! ## Step (vii): the container `π^{j+1} · B_I` and the bound `(j+1)·log(π)` -/

section StepVII

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] (μ : Measure W) [μ.IsAddHaarMeasure]

/-- **The scaling law of the archimedean log-volume.** For a Haar measure on a real
finite-dimensional space of dimension `d > 0`, `B` of positive finite measure and `c > 0`,
`log(μ(c·B)/μ(B))/d = log(c)`: the log-volume normalized at `B` (so that `B` has log-volume
`0`) and divided by the real dimension. -/
theorem stepsVII_logVolume_smul (hd : 0 < Module.finrank ℝ W) {B : Set W} (hB0 : μ B ≠ 0)
    (hB : μ B ≠ ⊤) {c : ℝ} (hc : 0 < c) :
    Real.log ((μ (c • B)).toReal / (μ B).toReal) / Module.finrank ℝ W = Real.log c := by
  have hBpos : 0 < (μ B).toReal := ENNReal.toReal_pos hB0 hB
  rw [Measure.addHaar_smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
    mul_div_assoc, div_self hBpos.ne', mul_one, abs_of_pos (pow_pos hc _), Real.log_pow]
  have : (0 : ℝ) < Module.finrank ℝ W := by exact_mod_cast hd
  field_simp

/-- **Step (vii), the upper bound `(j + 1)·log(π)`**: the container `π^{j+1}·B` has log-volume
`(j + 1)·log(π)` when `B` has log-volume `0`. -/
theorem stepsVII_logVolume_container (hd : 0 < Module.finrank ℝ W) {B : Set W} (hB0 : μ B ≠ 0)
    (hB : μ B ≠ ⊤) (j : ℕ) :
    Real.log ((μ ((Real.pi ^ (j + 1)) • B)).toReal / (μ B).toReal) / Module.finrank ℝ W
      = (j + 1) * Real.log Real.pi := by
  rw [stepsVII_logVolume_smul μ hd hB0 hB (pow_pos Real.pi_pos _), Real.log_pow]
  push_cast; ring

/-- Every subset of the container `c·B` of positive measure has log-volume `≤ log(c)`. -/
theorem stepsVII_logVolume_le (hd : 0 < Module.finrank ℝ W) {A B : Set W} (hA0 : μ A ≠ 0)
    (hB0 : μ B ≠ 0) (hB : μ B ≠ ⊤) {c : ℝ} (hc : 0 < c) (hAB : A ⊆ c • B) :
    Real.log ((μ A).toReal / (μ B).toReal) / Module.finrank ℝ W ≤ Real.log c := by
  rw [← stepsVII_logVolume_smul μ hd hB0 hB hc]
  have hBpos : 0 < (μ B).toReal := ENNReal.toReal_pos hB0 hB
  have hcB : μ (c • B) ≠ ⊤ := by
    rw [Measure.addHaar_smul]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Real.log_le_log
  · exact div_pos (ENNReal.toReal_pos hA0 (ne_top_of_le_ne_top hcB (measure_mono hAB))) hBpos
  · exact div_le_div_of_nonneg_right (ENNReal.toReal_mono hcB (measure_mono hAB)) hBpos.le

end StepVII

/-- The product of the closed unit balls of `N` copies of `ℂ`: the integral structure `B_I` of
Proposition 1.5 (iii), in the coordinates of a decomposition of `M_I` into `N` copies of `ℂ`
(`N = 2^{|I|−1}·|V|^{|I|}` on page 15). -/
noncomputable def stepsVIIUnitBalls (N : ℕ) : Set (Fin N → ℂ) :=
  Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) 1

/-- **Step (vii) on the product of unit balls.** For `N ≥ 1` copies of `ℂ` with Lebesgue measure,
`π^{j+1}·B` has log-volume `(j + 1)·log(π)` relative to `B = stepsVIIUnitBalls N`. -/
theorem stepsVII_unitBalls_logVolume (N j : ℕ) (hN : 0 < N) :
    Real.log ((volume ((Real.pi ^ (j + 1)) • stepsVIIUnitBalls N)).toReal
        / (volume (stepsVIIUnitBalls N)).toReal) / Module.finrank ℝ (Fin N → ℂ)
      = (j + 1) * Real.log Real.pi := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hd : 0 < Module.finrank ℝ (Fin N → ℂ) := Module.finrank_pos
  have hopen : IsOpen (Set.univ.pi fun _ : Fin N => Metric.ball (0 : ℂ) 1) :=
    isOpen_set_pi Set.finite_univ fun _ _ => Metric.isOpen_ball
  have hpos : volume (Set.univ.pi fun _ : Fin N => Metric.ball (0 : ℂ) 1) ≠ 0 :=
    hopen.measure_ne_zero volume ⟨0, by simp⟩
  have hB0 : volume (stepsVIIUnitBalls N) ≠ 0 := fun h0 =>
    hpos (measure_mono_null (Set.pi_mono fun _ _ => Metric.ball_subset_closedBall) h0)
  have hB : volume (stepsVIIUnitBalls N) ≠ ⊤ :=
    (isCompact_univ_pi fun _ => isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne
  exact stepsVII_logVolume_container volume hd hB0 hB j

/-- **Step (vii), the procession-normalized upper bound.** Let `l = 2·l^⋇ + 1 ≥ 5`. If the
component for `j` and every collection is the log-volume of the container `π^{j+1}·B` in `N_j`
copies of `ℂ` (`N_j ≥ 1`), the procession-normalized value is `(l+5)/4·log(π)`, and
`(l+5)/4·log(π) ≤ (l+1)/4·4` (page 30). -/
theorem stepsVII_procession {E : Type*} [Fintype E] [Nonempty E] {lam : E → ℝ}
    (hlam : ∀ v, 0 < lam v) (n : ℕ) (hn : 2 ≤ n) (N : ℕ → ℕ) (hN : ∀ j, 0 < N j) :
    stepsIVProcession lam n (fun j _ =>
        Real.log ((volume ((Real.pi ^ (j + 1)) • stepsVIIUnitBalls (N j))).toReal
          / (volume (stepsVIIUnitBalls (N j))).toReal) / Module.finrank ℝ (Fin (N j) → ℂ))
      = ((2 * n + 1) + 5) / 4 * Real.log Real.pi ∧
      ((2 * (n : ℝ) + 1) + 5) / 4 * Real.log Real.pi ≤ ((2 * n + 1) + 1) / 4 * 4 := by
  have e : (fun (j : ℕ) (_ : Fin (j + 1) → E) =>
      Real.log ((volume ((Real.pi ^ (j + 1)) • stepsVIIUnitBalls (N j))).toReal
          / (volume (stepsVIIUnitBalls (N j))).toReal) / Module.finrank ℝ (Fin (N j) → ℂ))
      = fun (j : ℕ) (_ : Fin (j + 1) → E) => ((j : ℝ) + 1) * Real.log Real.pi := by
    funext j _; exact stepsVII_unitBalls_logVolume (N j) j (hN j)
  rw [e, stepsIVProcession_const hlam n (fun j => ((j : ℝ) + 1) * Real.log Real.pi),
    step_vii_average n (by omega)]
  refine ⟨rfl, ?_⟩
  have := step_vii_archimedean (l := 2 * (n : ℝ) + 1) (by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith)
  linarith

/-- **Step (vii), upper bounds.** If every component (for `j` and each collection) is at most
`(j + 1)·log(π)`, as `stepsVII_logVolume_le` gives for subsets of the container, the
procession-normalized value is at most `(l+1)/4·4` with `l = 2·l^⋇ + 1 ≥ 5`. -/
theorem stepsVII_procession_le {E : Type*} [Fintype E] [Nonempty E] {lam : E → ℝ}
    (hlam : ∀ v, 0 < lam v) (n : ℕ) (hn : 2 ≤ n) {x : (j : ℕ) → (Fin (j + 1) → E) → ℝ}
    (hx : ∀ j w, x j w ≤ ((j : ℝ) + 1) * Real.log Real.pi) :
    stepsIVProcession lam n x ≤ ((2 * n + 1) + 1) / 4 * 4 := by
  have h1 := stepsIVProcession_mono hlam n
    (b' := fun j _ => ((j : ℝ) + 1) * Real.log Real.pi) hx
  rw [stepsIVProcession_const hlam n (fun j => ((j : ℝ) + 1) * Real.log Real.pi),
    step_vii_average n (by omega)] at h1
  have := step_vii_archimedean (l := 2 * (n : ℝ) + 1) (by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith)
  linarith

end IUT.PaperIV.Theorem1_10
