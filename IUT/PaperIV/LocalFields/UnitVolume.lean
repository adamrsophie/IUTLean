import IUT.PaperIV.LocalFields.VolumeBridge

/-!
# IUT IV Proposition 1.4 (ii): the log-volume of `log_p(R^×)`

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Proposition 1.4 (ii) and its proof,
pages 13 and 14, with the notation of Propositions 1.1 and 1.2 on pages 9 and 10. Pages read for
this file: 9, 10, 13 and 14. Pages checked against rendered images: the same. Displays relied on:
* page 9: `ord` normalized by `ord(p) = 1`; `R_i = 𝒪_{k_i}` the ring of integers of a finite
  extension `k_i` of `ℚ_p`;
* page 10: `e_i` the ramification index of `k_i` over `ℚ_p`; `log_p` the `p`-adic logarithm;
* page 13, the preamble of Proposition 1.4: `R_i^μ ⊆ R_i^×` the torsion subgroup,
  `R_i^{×μ} = R_i^× / R_i^μ`, `p ^ (f_i)` the cardinality of the residue field of `k_i`,
  `p ^ (m_i)` the order of the `p`-primary component of `R_i^μ`, and "Thus, the order of `R_i^μ`
  is equal to `p ^ (m_i) · (p ^ (f_i) − 1)`"; assertion (i), the normalization `μ^log(R_i) = 0`,
  `μ^log(p · R_i) = −log(p)` "by dividing by the degree of the finite extension"; assertion (ii)
  `μ^log(log_p(R_i^×)) = −(1 / e_i + m_i / (e_i f_i)) · log(p)`;
* page 14, the proof of (ii): `μ^log(log_p(R_i^×)) = μ^log(R_i^{×μ})`,
  `e_i f_i μ^log(R_i^{×μ}) = e_i f_i μ^log(R_i^×) − log(p ^ (m_i) · (p ^ (f_i) − 1))`,
  `e_i f_i μ^log(R_i^×) = log(1 − p ^ (−f_i))`, hence
  `e_i f_i μ^log(R_i^{×μ}) = −(f_i + m_i) · log(p)`.

## The objects

As in `IUT.PaperIV.LocalFields.VolumeBridge`: `L` is a finite extension of `ℚ_[p]` normed by its
spectral norm, with the Borel structure; `R = integralClosure ℤ_[p] L`; `R^×` is the image in `L`
of the unit group of `R`; `log_p` is `extLogUnit` of `Logarithm.lean`; `e = P.ramificationIdx ℤ_[p]`
for a prime `P` of `R` over `p` (there is only one); `μ^log` is `padicMuLog`, normalized at `R` and
divided by `[L : ℚ_p]`. New here:
* `f = unitVolResidueDegree p L`, Mathlib's `Ideal.inertiaDeg` of the maximal ideal of `R`;
  `unitVol_card_residueField`: the residue field `R ⧸ P` has `p ^ f` elements;
* `R^μ = CommGroup.torsion (R)ˣ`, and `m = unitVolTorsionExponent p L`, defined by
  `p ^ m = |CommGroup.primaryComponent (R)ˣ p|`; `unitVol_card_primaryComponent`: this component
  (the elements of `p`-power order, which all lie in `R^μ`) is finite of order `p ^ m`.

The measure on `R^×` is the restriction of an additive Haar measure of `L`, as in the formula
`e_i f_i μ^log(R_i^×) = log(1 − p ^ (−f_i))` of page 14. The paper passes to the quotient
`R^{×μ}` and uses the compatibility of the log-volume with `log_p` ([AbsTopIII] Proposition 5.7,
(i), (c)); here that step is replaced by a counting argument inside `L` (below), so no measure on
the quotient group and no result of [AbsTopIII] is used.

## What is proved

1. `unitVol_ramificationIdx_mul_residueDegree`: `e f = [L : ℚ_p]` (Mathlib's
   `Ideal.sum_ramification_inertia_eq_finrank` with one prime, and `IsIntegralClosure.rank`);
   `unitVol_card_residueField`: `|R ⧸ P| = p ^ f`.
2. `unitVol_measure_units`: `μ(R^×) = μ(R) − p ^ (−f) μ(R)` for every additive Haar measure: the
   nonunits are `ϖ R`, of measure `‖ϖ‖ ^ (e f) μ(R) = p ^ (−f) μ(R)`.
3. `unitVol_measure_logUnit_mul_card` (with the normed form
   `unitVol_measure_logUnit_mul_card_of_normed`): `log_p u = 0` exactly for `u ∈ R^μ`
   (`unitVol_extLogUnit_eq_zero_iff`), `R^μ` is finite, and `μ(log_p(R^×)) · |R^μ| = μ(R^×)`.
   The proof takes `r = 1 / (2p)`, so that `x ↦ log(1 + x)` maps the ball `B_r = {‖x‖ ≤ r}`
   bijectively onto itself (`extLogOnePlus_image_closedBall`, `extLogOnePlus_injOn` of
   `Logarithm.lean`); then `U_r = 1 + B_r` is a subgroup of `R^×` on which `log_p` is injective
   with image `B_r`, `R^×` is a disjoint union of `[R^× : U_r]` balls `u + B_r`, `log_p(R^×)` is a
   disjoint union of `[log_p(R^×) : B_r]` balls `z + B_r` (`unitVol_measure_range_eq_index`, which
   also gives the finiteness of the indices), and
   `[R^× : U_r] = |ker log_p| · [log_p(R^×) : B_r]` since `log_p⁻¹(B_r) = ker log_p · U_r` and
   `ker log_p ∩ U_r = 1`. An element of the kernel has its `[R^× : U_r]`-th power in `U_r`, hence
   equal to `1`; so the kernel is `R^μ`.
4. `unitVol_card_torsion`: `|R^μ| = p ^ m (p ^ f − 1)`, the sentence of page 13. Reduction modulo
   `P` maps `R^μ` onto `(R ⧸ P)^×` (Hensel's lemma for `X ^ (p ^ f − 1) − 1`, from Mathlib's
   `IsAdicComplete.henselianRing` and `unitVol_isAdicComplete`: `R` is `P`-adically complete), with
   kernel the `p`-primary component.
5. **Proposition 1.4 (ii)**: `unitVol_muLog_logUnit_eq_card`:
   `μ^log(log_p(R^×)) = (log(1 − p ^ (−f)) − log |R^μ|) / (e f)`;
   `unitVol_muLog_logUnit_eq_of_card`: the value `−(1 / e + m / (e f)) log p` from the order
   count; `unitVol_muLog_logUnit_eq`: the same with the order count proved, for every additive
   Haar measure, with no hypothesis beyond the setting.
6. `unitVol_card_torsion_of_le`: for `p > 2` and `e ≤ p − 2`, `|R^μ| = p ^ f − 1` and `m = 0`, by
   comparing with `volBridge_muLog_logUnit_eq_of_le` (the equality case of Proposition 1.2 (i)); so
   that value is the case `m = 0` of (ii).

## Not proved

* The log-volume of [AbsTopIII] Proposition 5.7 itself, the quotient `R^{×μ}` with its induced
  log-volume, and the compatibility of log-volumes with `log_p` cited on page 14: the statement
  is proved for the Haar measure of `L` restricted to `R^×` and `log_p(R^×)`, which is the model of
  `μ^log` used in `VolumeBridge.lean`.
* Tensor packets: (ii) concerns one field `k_i`; the sums over `i ∈ I` used on page 14 for (iii)
  are not formalized here. For two factors, (iv), the second inequality of (iii) and the first
  inequality of (iii) when every `e_i ≤ p − 2` are proved in `TensorLogShell.lean`, without the
  additivity over the factors; the additivity and the first inequality of (iii) for every `I*`
  are proved for two factors in `TensorAdditivity.lean`.
-/

open MeasureTheory Measure IUT.Prerequisites.PadicVolume
open scoped Pointwise

namespace IUT.PaperIV.LocalFields

/-! ## 1. Counting cosets by Haar measure -/

section Counting

/-- **Counting cosets by measure.** Let `φ : A → K` be an injective map from a group `A` to a
metric space with a measure, and `V` a subgroup of `A` such that `φ` maps every left coset
`a V` onto the closed ball of radius `r` around `φ a`. If these balls all have the same measure
`c ≠ 0` and `φ (A)` has finite measure, then `V` has finite index and
`μ (φ (A)) = [A : V] · c`. -/
theorem unitVol_measure_range_eq_index {K : Type*} [PseudoMetricSpace K] [MeasurableSpace K]
    [OpensMeasurableSpace K] (μ : Measure K) {A : Type*} [Group A] (V : Subgroup A)
    (φ : A → K) (hφ : Function.Injective φ) {r : ℝ} {c : ENNReal}
    (hcoset : ∀ a : A, φ '' {b | a⁻¹ * b ∈ V} = Metric.closedBall (φ a) r)
    (hball : ∀ x : K, μ (Metric.closedBall x r) = c) (h0 : c ≠ 0)
    (htop : μ (Set.range φ) ≠ ⊤) :
    V.FiniteIndex ∧ μ (Set.range φ) = V.index * c := by
  set F : A ⧸ V → Set K := fun q => φ '' {b | (b : A ⧸ V) = q} with hF
  have hFq : ∀ q, F q = Metric.closedBall (φ q.out) r := by
    intro q
    rw [← hcoset]
    simp only [hF]
    congr 1
    ext b
    simp only [Set.mem_ofPred_eq]
    rw [← QuotientGroup.eq, QuotientGroup.out_eq', eq_comm]
  have hU : Set.range φ = ⋃ q, F q := by
    ext x
    simp only [Set.mem_range, Set.mem_iUnion, hF, Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b, b, rfl, rfl⟩
    · rintro ⟨q, b, -, rfl⟩
      exact ⟨b, rfl⟩
  have hmeas : ∀ q, MeasurableSet (F q) := fun q => by
    rw [hFq]
    exact Metric.isClosed_closedBall.measurableSet
  have hdisj : Pairwise (Function.onFun Disjoint F) := by
    intro q q' hqq'
    simp only [Function.onFun, hF]
    rw [Set.disjoint_image_iff hφ, Set.disjoint_left]
    intro b hb hb'
    exact hqq' (hb.symm.trans hb')
  have hμF : ∀ q, μ (F q) = c := fun q => by rw [hFq, hball]
  have hfin : Finite (A ⧸ V) := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    have h := tsum_meas_le_meas_iUnion_of_disjoint μ hmeas hdisj
    simp only [hμF, ENNReal.tsum_const_eq_top_of_ne_zero h0, top_le_iff] at h
    rw [← hU] at h
    exact htop h
  refine ⟨Subgroup.finiteIndex_of_finite_quotient, ?_⟩
  rw [hU, measure_iUnion hdisj hmeas]
  simp only [hμF]
  rw [ENNReal.tsum_const, ENat.card_eq_coe_natCard, Subgroup.index]
  simp

end Counting

/-! ## 2. The logarithm on a group of units of norm one -/

section LogHom

variable (p : ℕ) [hp : Fact p.Prime] {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K]

include hp

/-- `log (u v) = log u + log v` for `‖u‖ = ‖v‖ = 1` in a finite extension of `ℚ_p`. -/
theorem unitVol_extLogUnit_mul {u v : K} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    extLogUnit (u * v) = extLogUnit u + extLogUnit v := by
  have : CompleteSpace K := FiniteDimensional.completeSpace ℚ_[p] K
  have : ProperSpace K := FiniteDimensional.proper ℚ_[p] K
  obtain ⟨M, hM, hMu⟩ := extLog_exists_pow_near_one hu
  obtain ⟨N, hN, hNv⟩ := extLog_exists_pow_near_one hv
  have h1 : ‖u ^ (M * N) - 1‖ < 1 := by
    have := (extLogOnePlus_pow_sub_one p hMu N).1
    rwa [add_sub_cancel, ← pow_mul] at this
  have h2 : ‖v ^ (M * N) - 1‖ < 1 := by
    have := (extLogOnePlus_pow_sub_one p hNv M).1
    rwa [add_sub_cancel, ← pow_mul, mul_comm N M] at this
  exact extLogUnit_mul p (Nat.mul_pos hM hN) h1 h2

/-- `log 1 = 0`. -/
theorem unitVol_extLogUnit_one : extLogUnit (1 : K) = 0 := by
  have : CompleteSpace K := FiniteDimensional.completeSpace ℚ_[p] K
  have h := extLogUnit_one_add p (K := K) (x := 0) (by simp)
  rw [add_zero, extLogOnePlus_zero] at h
  exact h

variable {G : Type*} [CommGroup G] (ι : G →* K)

/-- The logarithm `g ↦ log (ι g)` on a group `G` mapped by `ι` into the elements of norm one, as a
homomorphism to the additive group of `K` (written multiplicatively). -/
noncomputable def unitVolLogHom (hS : ∀ g, ‖ι g‖ = 1) : G →* Multiplicative K where
  toFun g := Multiplicative.ofAdd (extLogUnit (ι g))
  map_one' := by
    rw [map_one, unitVol_extLogUnit_one p, ofAdd_zero]
  map_mul' g h := by
    rw [map_mul, unitVol_extLogUnit_mul p (hS g) (hS h), ofAdd_add]

/-- The subgroup `{g | ‖ι g − 1‖ ≤ r}` of `G`, for `0 ≤ r`. -/
noncomputable def unitVolNearOne (hS : ∀ g, ‖ι g‖ = 1) {r : ℝ} (hr0 : 0 ≤ r) : Subgroup G where
  carrier := {g | ‖ι g - 1‖ ≤ r}
  mul_mem' := by
    intro a b ha hb
    have := extLog_isUltrametricDist p (K := K)
    simp only [Set.mem_ofPred_eq, map_mul] at *
    have h : ι a * ι b - 1 = (ι a - 1) * ι b + (ι b - 1) := by ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hb)
    rw [norm_mul, hS b, mul_one]
    exact ha
  one_mem' := by simp [hr0]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, map_inv] at *
    have ha0 : ι a ≠ 0 := by
      intro h0
      have := hS a
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have h : (ι a)⁻¹ - 1 = -((ι a - 1) * (ι a)⁻¹) := by
      rw [sub_mul, mul_inv_cancel₀ ha0, one_mul]
      ring
    rw [h, norm_neg, norm_mul, norm_inv, hS a, inv_one, mul_one]
    exact ha

omit [FiniteDimensional ℚ_[p] K] in
/-- The closed ball `{‖x‖ ≤ r}` of `K` as a subgroup of `Multiplicative K`. -/
noncomputable def unitVolLogBall {r : ℝ} (hr0 : 0 ≤ r) : Subgroup (Multiplicative K) where
  carrier := {x | ‖Multiplicative.toAdd x‖ ≤ r}
  mul_mem' := by
    intro a b ha hb
    have := extLog_isUltrametricDist p (K := K)
    simp only [Set.mem_ofPred_eq, toAdd_mul] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  one_mem' := by simp [hr0]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, toAdd_inv, norm_neg] at *
    exact ha

omit hp [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] in
/-- `‖ι (a⁻¹ b) − 1‖ = ‖ι b − ι a‖` when `ι` takes values of norm one. -/
theorem unitVol_norm_inv_mul_sub_one (hS : ∀ g, ‖ι g‖ = 1) (a b : G) :
    ‖ι (a⁻¹ * b) - 1‖ = ‖ι b - ι a‖ := by
  have h : ι (a⁻¹ * b) - 1 = ι a⁻¹ * (ι b - ι a) := by
    rw [mul_sub, ← map_mul, ← map_mul, inv_mul_cancel, map_one]
  rw [h, norm_mul, hS, one_mul]

/-- **The log-volume of the image of the logarithm, counted against the torsion** (the argument of
IUT IV page 14, in a normed model). Let `K` be a finite extension of `ℚ_p` with a norm extending
the `p`-adic one, `e ≥ 1` with `‖x‖ ^ e ≤ 1 / p` on the open unit disc, `G` a commutative group
and `ι : G →* K` injective with image the unit sphere `{‖x‖ = 1}`. Then the logarithm vanishes on
`ι g` exactly when `g` is a torsion element, the torsion subgroup of `G` is finite, and for every
additive Haar measure `μ` on `K`,
`μ (log {‖u‖ = 1}) · |torsion G| = μ {‖u‖ = 1}`. -/
theorem unitVol_measure_logUnit_mul_card_of_normed [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure] (hι : Function.Injective ι) (hS : ∀ g, ‖ι g‖ = 1)
    (hsurj : ∀ x : K, ‖x‖ = 1 → ∃ g, ι g = x) {e : ℕ} (he : 1 ≤ e)
    (hval : ∀ x : K, ‖x‖ < 1 → ‖x‖ ^ e ≤ (p : ℝ)⁻¹) :
    (∀ g : G, extLogUnit (ι g) = 0 ↔ g ∈ CommGroup.torsion G) ∧
      Finite (CommGroup.torsion G) ∧
      μ (extLogUnit '' {u : K | ‖u‖ = 1}) * Nat.card (CommGroup.torsion G) =
        μ {u : K | ‖u‖ = 1} := by
  have : CompleteSpace K := FiniteDimensional.completeSpace ℚ_[p] K
  have : ProperSpace K := FiniteDimensional.proper ℚ_[p] K
  have := extLog_isUltrametricDist p (K := K)
  have := extLog_charZero p (K := K)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  -- the radius
  set r : ℝ := 1 / (2 * p) with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by
    rw [hr, div_lt_one (by positivity)]
    linarith
  have hpr : (p : ℝ) * r ^ (p - 1) < 1 := by
    have h1 : r ^ (p - 1) ≤ r :=
      pow_le_of_le_one hr0.le hr1.le (by have := hp.out.two_le; omega)
    have h2 : (p : ℝ) * r = 1 / 2 := by
      rw [hr]
      field_simp
    nlinarith
  have hdisc : ∀ x : K, ‖x‖ ≤ r → (p : ℝ) * ‖x‖ ^ (p - 1) < 1 := by
    intro x hx
    refine lt_of_le_of_lt ?_ hpr
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx _) hp0.le
  set ℓ := unitVolLogHom p ι hS with hℓ
  set U := unitVolNearOne p ι hS hr0.le with hU
  set B := unitVolLogBall p (K := K) hr0.le with hB
  have hℓapp : ∀ g, Multiplicative.toAdd (ℓ g) = extLogUnit (ι g) := fun g => rfl
  have hmemU : ∀ g, g ∈ U ↔ ‖ι g - 1‖ ≤ r := fun g => Iff.rfl
  have hmemB : ∀ x, x ∈ B ↔ ‖Multiplicative.toAdd x‖ ≤ r := fun x => Iff.rfl
  -- the logarithm on `U`
  have hℓU : ∀ g ∈ U, extLogUnit (ι g) = extLogOnePlus (ι g - 1) := by
    intro g hg
    have h := extLogUnit_one_add p (K := K) (x := ι g - 1)
      (lt_of_le_of_lt ((hmemU g).1 hg) hr1)
    rwa [add_sub_cancel] at h
  have hinj : ∀ g ∈ U, ∀ h ∈ U, ℓ g = ℓ h → g = h := by
    intro g hg h hh hgh
    have h1 : extLogUnit (ι g) = extLogUnit (ι h) := by
      rw [← hℓapp, ← hℓapp, hgh]
    rw [hℓU g hg, hℓU h hh] at h1
    have h2 := extLogOnePlus_injOn p (K := K) (hdisc _ ((hmemU g).1 hg))
      (hdisc _ ((hmemU h).1 hh)) h1
    exact hι (sub_left_injective h2)
  have hUB : ∀ g ∈ U, ℓ g ∈ B := by
    intro g hg
    rw [hmemB, hℓapp, hℓU g hg, extLogOnePlus_norm_eq p (hdisc _ ((hmemU g).1 hg))]
    exact (hmemU g).1 hg
  have hBU : ∀ x ∈ B, ∃ g ∈ U, ℓ g = x := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := extLogOnePlus_surjOn p hr0.le hpr ((hmemB x).1 hx)
    obtain ⟨g, hg⟩ := hsurj (1 + y) (extLog_norm_one_add (lt_of_le_of_lt hy hr1))
    have hgU : g ∈ U := by
      rw [hmemU, hg, add_sub_cancel_left]
      exact hy
    refine ⟨g, hgU, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hℓapp, hℓU g hgU, hg, add_sub_cancel_left, hyx]
  -- the kernel meets `U` trivially, and `ℓ⁻¹ (B) = ker ℓ ⊔ U`
  have hinf : U ⊓ ℓ.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgU, hgk⟩
    rw [Subgroup.mem_bot]
    exact hinj g hgU 1 U.one_mem (by rw [map_one]; exact hgk)
  have hcomap : B.comap ℓ = ℓ.ker ⊔ U := by
    apply le_antisymm
    · intro g hg
      obtain ⟨u, hu, hug⟩ := hBU (ℓ g) hg
      rw [Subgroup.mem_sup]
      refine ⟨g * u⁻¹, ?_, u, hu, by group⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hug, mul_inv_cancel]
    · refine sup_le (fun g hg => ?_) (fun g hg => hUB g hg)
      rw [MonoidHom.mem_ker] at hg
      show ℓ g ∈ B
      rw [hg]
      exact B.one_mem
  -- index computation
  have hUle : U ≤ B.comap ℓ := fun g hg => hUB g hg
  have hcomap' : B.comap ℓ = (B.subgroupOf ℓ.range).comap ℓ.rangeRestrict := by
    ext g
    simp [Subgroup.mem_subgroupOf]
  have hidx : U.index = Nat.card ℓ.ker * (B.subgroupOf ℓ.range).index := by
    rw [← Subgroup.relIndex_mul_index hUle, hcomap', Subgroup.index_comap_of_surjective _
      ℓ.rangeRestrict_surjective, ← hcomap', hcomap, Subgroup.relIndex_sup_right,
      ← Subgroup.inf_relIndex_right, hinf, Subgroup.relIndex_bot_left]
  -- the measure of balls
  set c := μ (Metric.closedBall (0 : K) r) with hc
  have hball : ∀ x : K, μ (Metric.closedBall x r) = c := fun x =>
    Measure.addHaar_closedBall_center μ x r
  have hc0 : c ≠ 0 := (Metric.measure_closedBall_pos μ 0 hr0).ne'
  have hsphere : Set.range ι = {u : K | ‖u‖ = 1} := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact hS g
    · intro hx
      exact hsurj x hx
  -- counting `U`-cosets in the unit sphere
  have hcosetU : ∀ a : G, ι '' {b | a⁻¹ * b ∈ U} = Metric.closedBall (ι a) r := by
    intro a
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, Metric.mem_closedBall, dist_eq_norm]
    constructor
    · rintro ⟨b, hb, rfl⟩
      rw [← unitVol_norm_inv_mul_sub_one ι hS]
      exact hb
    · intro hx
      have hx1 : ‖x‖ = 1 := by
        have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
          (show ‖ι a‖ ≠ ‖x - ι a‖ by rw [hS a]; exact (lt_of_le_of_lt hx hr1).ne')
        rw [add_sub_cancel, hS a] at h
        rw [h]
        exact max_eq_left (lt_of_le_of_lt hx hr1).le
      obtain ⟨b, rfl⟩ := hsurj x hx1
      refine ⟨b, ?_, rfl⟩
      rw [hmemU, unitVol_norm_inv_mul_sub_one ι hS]
      exact hx
  have htopS : μ (Set.range ι) ≠ ⊤ := by
    rw [hsphere]
    refine ne_top_of_le_ne_top (measure_closedBall_lt_top (x := (0 : K)) (r := 1)).ne
      (measure_mono fun x hx => ?_)
    simp only [Set.mem_ofPred_eq] at hx
    simp [hx]
  obtain ⟨hUfin, hμS⟩ :=
    unitVol_measure_range_eq_index μ U ι hι hcosetU hball hc0 htopS
  -- counting `B`-cosets in the image of the logarithm
  set φ : ℓ.range → K := fun h => Multiplicative.toAdd (h : Multiplicative K) with hφ
  have hφinj : Function.Injective φ := fun a b hab =>
    Subtype.ext (Multiplicative.toAdd.injective hab)
  have hrangeφ : Set.range φ = extLogUnit '' {u : K | ‖u‖ = 1} := by
    ext x
    constructor
    · rintro ⟨⟨h, g, rfl⟩, rfl⟩
      exact ⟨ι g, hS g, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨g, rfl⟩ := hsurj u hu
      exact ⟨⟨ℓ g, g, rfl⟩, rfl⟩
  have hBle : B ≤ ℓ.range := by
    intro x hx
    obtain ⟨g, -, hg⟩ := hBU x hx
    exact ⟨g, hg⟩
  have hcosetB : ∀ a : ℓ.range, φ '' {b | a⁻¹ * b ∈ B.subgroupOf ℓ.range} =
      Metric.closedBall (φ a) r := by
    intro a
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, Metric.mem_closedBall, dist_eq_norm,
      Subgroup.mem_subgroupOf, hφ]
    constructor
    · rintro ⟨b, hb, rfl⟩
      rw [hmemB] at hb
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, toAdd_mul, toAdd_inv] at hb
      rwa [neg_add_eq_sub] at hb
    · intro hx
      have hxB : Multiplicative.ofAdd (x - Multiplicative.toAdd (a : Multiplicative K)) ∈ B := by
        rw [hmemB]
        exact hx
      have hmem : Multiplicative.ofAdd x ∈ ℓ.range := by
        have h := ℓ.range.mul_mem a.2 (hBle hxB)
        convert h using 1
        apply Multiplicative.toAdd.injective
        simp
      refine ⟨⟨Multiplicative.ofAdd x, hmem⟩, ?_, rfl⟩
      rw [hmemB]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, toAdd_mul, toAdd_inv, toAdd_ofAdd]
      rwa [neg_add_eq_sub]
  have htopH : μ (Set.range φ) ≠ ⊤ := by
    rw [hrangeφ]
    refine ne_top_of_le_ne_top (measure_closedBall_lt_top (x := (0 : K))
      (r := (p : ℝ) ^ (Proposition1_2.b p e))).ne (measure_mono fun x hx => ?_)
    have h := extLogUnit_image_upper p he hval hx
    simp only [Set.mem_ofPred_eq] at h
    simpa using h
  obtain ⟨-, hμH⟩ :=
    unitVol_measure_range_eq_index μ (B.subgroupOf ℓ.range) φ hφinj hcosetB hball hc0 htopH
  -- the kernel is the torsion subgroup
  have hUidx : U.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hker : ℓ.ker = CommGroup.torsion G := by
    ext g
    rw [MonoidHom.mem_ker, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    constructor
    · intro hg
      refine ⟨U.index, Nat.pos_of_ne_zero hUidx, ?_⟩
      refine hinj _ (Subgroup.pow_index_mem U g) 1 U.one_mem ?_
      rw [map_pow, hg, one_pow, map_one]
    · rintro ⟨n, hn, hgn⟩
      have h1 : ℓ g ^ n = 1 := by rw [← map_pow, hgn, map_one]
      apply Multiplicative.toAdd.injective
      have h2 := congrArg Multiplicative.toAdd h1
      rw [toAdd_pow, toAdd_one, nsmul_eq_mul, mul_eq_zero] at h2
      rw [toAdd_one]
      exact h2.resolve_left (Nat.cast_ne_zero.mpr hn.ne')
  have hcardne : Nat.card ℓ.ker ≠ 0 := by
    intro h0
    rw [hidx, h0, zero_mul] at hUidx
    exact hUidx rfl
  refine ⟨fun g => ?_, ?_, ?_⟩
  · rw [← hker, MonoidHom.mem_ker]
    exact ⟨fun h => by apply Multiplicative.toAdd.injective; exact h,
      fun h => congrArg Multiplicative.toAdd h⟩
  · rw [← hker]
    exact (Nat.card_ne_zero.mp hcardne).2
  · rw [← hrangeφ, hμH, ← hsphere, hμS, hidx, ← hker]
    push_cast
    ring

end LogHom

/-! ## 3. The residue degree `f`, the torsion exponent `m`, and `e f = [L : ℚ_p]` -/

section Field

variable (p : ℕ) [hp : Fact p.Prime] (L : Type*) [Field L] [Algebra ℚ_[p] L]
  [FiniteDimensional ℚ_[p] L] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L]

/-- **The residue degree `f`** of a finite extension `L` of `ℚ_[p]`: the inertia degree
(Mathlib's `Ideal.inertiaDeg`, the degree of the residue field `R ⧸ P` over `ℤ_p ⧸ p = 𝔽_p`) of the
maximal ideal `P` of `R = integralClosure ℤ_[p] L`, the only prime over `p`. The residue field has
cardinality `p ^ f` (`unitVol_card_residueField`). -/
noncomputable def unitVolResidueDegree : ℕ :=
  haveI := padicBridge_isLocalRing p L
  (IsLocalRing.maximalIdeal (integralClosure ℤ_[p] L)).inertiaDeg ℤ_[p]

/-- **The torsion exponent `m`** of a finite extension `L` of `ℚ_[p]`: `p ^ m` is the order of the
`p`-primary component of the unit group of `R = integralClosure ℤ_[p] L` (the elements of
`p`-power order, equivalently the `p`-power roots of unity of `L`); that component is finite of
order exactly `p ^ m` (`unitVol_card_primaryComponent`). -/
noncomputable def unitVolTorsionExponent : ℕ :=
  (Nat.card (CommGroup.primaryComponent (integralClosure ℤ_[p] L)ˣ p)).factorization p

/-- For every prime `P` of `R` over `p`, `P.inertiaDeg ℤ_[p]` is the residue degree `f`. -/
theorem unitVol_inertiaDeg_eq (P : Ideal (integralClosure ℤ_[p] L)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    P.inertiaDeg ℤ_[p] = unitVolResidueDegree p L := by
  have := padicBridge_isLocalRing p L
  rw [unitVolResidueDegree, padicBridge_prime_eq_maximalIdeal p L P]

/-- `R = integralClosure ℤ_[p] L` is a finitely generated `ℤ_[p]`-module. -/
theorem unitVol_moduleFinite : Module.Finite ℤ_[p] (integralClosure ℤ_[p] L) :=
  IsIntegralClosure.finite ℤ_[p] ℚ_[p] L (integralClosure ℤ_[p] L)

omit [FiniteDimensional ℚ_[p] L] in
/-- `L` is torsion free as a `ℤ_[p]`-module. -/
theorem unitVol_isTorsionFree_field : Module.IsTorsionFree ℤ_[p] L := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun r x h => ?_
  rw [Algebra.smul_def] at h
  rcases mul_eq_zero.mp h with hr | hx
  · left
    rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] L, map_eq_zero] at hr
    exact IsFractionRing.injective ℤ_[p] ℚ_[p] (hr.trans (map_zero _).symm)
  · right
    exact hx

/-- **`e f = [L : ℚ_p]`**: the fundamental identity for the unique prime `P` of
`R = integralClosure ℤ_[p] L` over `p` (Mathlib's `Ideal.sum_ramification_inertia_eq_finrank`
with one prime, and `IsIntegralClosure.rank`). -/
theorem unitVol_ramificationIdx_mul_residueDegree (P : Ideal (integralClosure ℤ_[p] L))
    [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    P.ramificationIdx ℤ_[p] * unitVolResidueDegree p L = Module.finrank ℚ_[p] L := by
  have := padicBridge_isLocalRing p L
  have := isDedekindDomain_ringOfIntegers_padic p L
  have := isTorsionFree_ringOfIntegers_padic p L
  have := unitVol_isTorsionFree_field p L
  have := unitVol_moduleFinite p L
  have : Module.Free ℤ_[p] (integralClosure ℤ_[p] L) :=
    IsIntegralClosure.module_free ℤ_[p] ℚ_[p] L (integralClosure ℤ_[p] L)
  set M := IsLocalRing.maximalIdeal ℤ_[p]
  have huniq : ∀ q : M.primesOver (integralClosure ℤ_[p] L), q.1 = P := by
    intro q
    rw [padicBridge_prime_eq_maximalIdeal p L q.1, padicBridge_prime_eq_maximalIdeal p L P]
  have : Subsingleton (M.primesOver (integralClosure ℤ_[p] L)) :=
    ⟨fun a b => Subtype.ext ((huniq a).trans (huniq b).symm)⟩
  let q0 : M.primesOver (integralClosure ℤ_[p] L) := ⟨P, ⟨inferInstance, inferInstance⟩⟩
  let _ : Fintype (M.primesOver (integralClosure ℤ_[p] L)) := Fintype.ofSubsingleton q0
  have h := Ideal.sum_ramification_inertia_eq_finrank M (integralClosure ℤ_[p] L)
  rw [Fintype.sum_subsingleton _ q0,
    IsIntegralClosure.rank ℤ_[p] ℚ_[p] L (integralClosure ℤ_[p] L)] at h
  rw [← unitVol_inertiaDeg_eq p L P]
  exact h

/-- `f ≥ 1`. -/
theorem unitVol_residueDegree_pos : 0 < unitVolResidueDegree p L := by
  have := padicBridge_isLocalRing p L
  have := unitVol_moduleFinite p L
  exact Ideal.inertiaDeg_pos _ _

/-- **The residue field has `p ^ f` elements**: `|R ⧸ P| = p ^ f` for the prime `P` of
`R = integralClosure ℤ_[p] L` over `p` (Mathlib's `Ideal.cardQuot_pow_inertiaDeg`, with
`ℤ_p ⧸ p ≅ ℤ / p`). -/
theorem unitVol_card_residueField (P : Ideal (integralClosure ℤ_[p] L)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    Nat.card (integralClosure ℤ_[p] L ⧸ P) = p ^ unitVolResidueDegree p L := by
  have := padicBridge_isLocalRing p L
  have := unitVol_moduleFinite p L
  have hPm : P.IsMaximal := by
    rw [padicBridge_prime_eq_maximalIdeal p L P]
    exact IsLocalRing.maximalIdeal.isMaximal _
  have h := Ideal.cardQuot_pow_inertiaDeg (IsLocalRing.maximalIdeal ℤ_[p]) P
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at h
  have hM : Nat.card (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) = p := by
    rw [← PadicInt.ker_toZMod, Nat.card_congr (RingHom.quotientKerEquivOfSurjective
      (ZMod.ringHom_surjective (PadicInt.toZMod (p := p)))).toEquiv, Nat.card_zmod]
  rw [← h, hM, unitVol_inertiaDeg_eq p L P]

/-! ## 4. Haar measure of the units and the image of the logarithm -/

/-- The inclusion of the unit group of `R = integralClosure ℤ_[p] L` into `L`. -/
noncomputable def unitVolIncl : (integralClosure ℤ_[p] L)ˣ →* L :=
  (algebraMap (integralClosure ℤ_[p] L) L).toMonoidHom.comp
    (Units.coeHom (integralClosure ℤ_[p] L))

omit [FiniteDimensional ℚ_[p] L] [Algebra ℚ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] in
theorem unitVolIncl_apply (u : (integralClosure ℤ_[p] L)ˣ) :
    unitVolIncl p L u = ((u : integralClosure ℤ_[p] L) : L) := rfl

/-- **The kernel of the logarithm and the measure of its image** for a finite extension `L` of
`ℚ_[p]` (IUT IV page 14, proof of Proposition 1.4 (ii)), with `R = integralClosure ℤ_[p] L`, its
unit group `R^×`, the spectral norm and the Borel structure: for `u ∈ R^×`, `log_p u = 0` if and
only if `u` lies in the torsion subgroup `R^μ` of `R^×`; `R^μ` is finite; and for every additive
Haar measure `μ`, `μ (log_p (R^×)) · |R^μ| = μ (R^×)`. -/
theorem unitVol_measure_logUnit_mul_card :
    letI := spectralNorm.normedField ℚ_[p] L
    letI := spectralNorm.normedAlgebra ℚ_[p] L
    letI : MeasurableSpace L := borel L
    ∀ (μ : Measure L) [μ.IsAddHaarMeasure],
      (∀ u : (integralClosure ℤ_[p] L)ˣ, extLogUnit ((u : integralClosure ℤ_[p] L) : L) = 0 ↔
          u ∈ CommGroup.torsion (integralClosure ℤ_[p] L)ˣ) ∧
        Finite (CommGroup.torsion (integralClosure ℤ_[p] L)ˣ) ∧
        μ (extLogUnit '' Set.range
            (fun u : (integralClosure ℤ_[p] L)ˣ => ((u : integralClosure ℤ_[p] L) : L))) *
            Nat.card (CommGroup.torsion (integralClosure ℤ_[p] L)ˣ) =
          μ (Set.range
            (fun u : (integralClosure ℤ_[p] L)ˣ => ((u : integralClosure ℤ_[p] L) : L))) := by
  let := spectralNorm.normedField ℚ_[p] L
  let := spectralNorm.normedAlgebra ℚ_[p] L
  let _ : MeasurableSpace L := borel L
  have : BorelSpace L := ⟨rfl⟩
  intro μ _
  have := padicBridge_isLocalRing p L
  have := padicBridge_maximalIdeal_liesOver p L
  have := isDedekindDomain_ringOfIntegers_padic p L
  have := isTorsionFree_ringOfIntegers_padic p L
  set M := IsLocalRing.maximalIdeal (integralClosure ℤ_[p] L)
  have he : 1 ≤ M.ramificationIdx ℤ_[p] :=
    ramificationIdx_pos_of_liesOver (IsDiscreteValuationRing.not_a_field ℤ_[p]) M
  have hι : Function.Injective (unitVolIncl p L) := fun a b h => Units.ext (Subtype.ext h)
  have hS : ∀ u, ‖unitVolIncl p L u‖ = 1 := fun u =>
    (padicBridge_isUnit_iff p L _).1 u.isUnit
  have hsurj : ∀ x : L, ‖x‖ = 1 → ∃ u, unitVolIncl p L u = x := by
    intro x hx
    have hx' : x ∈ Set.range
        (fun u : (integralClosure ℤ_[p] L)ˣ => ((u : integralClosure ℤ_[p] L) : L)) := by
      rw [padicBridge_range_units_eq_unitSphere p L]
      exact hx
    obtain ⟨u, hu⟩ := hx'
    exact ⟨u, hu⟩
  have h := unitVol_measure_logUnit_mul_card_of_normed p (unitVolIncl p L) μ hι hS hsurj he
    (padicBridge_hval p L M)
  rw [padicBridge_range_units_eq_unitSphere p L]
  exact h

/-- **The kernel of `log_p` on `R^×` is the torsion subgroup**: for `u` in the unit group of
`R = integralClosure ℤ_[p] L`, `log_p u = 0` if and only if `u` has finite order. -/
theorem unitVol_extLogUnit_eq_zero_iff (u : (integralClosure ℤ_[p] L)ˣ) :
    letI := spectralNorm.normedField ℚ_[p] L
    extLogUnit ((u : integralClosure ℤ_[p] L) : L) = 0 ↔
      u ∈ CommGroup.torsion (integralClosure ℤ_[p] L)ˣ := by
  let := spectralNorm.normedField ℚ_[p] L
  let := spectralNorm.normedAlgebra ℚ_[p] L
  let _ : MeasurableSpace L := borel L
  have : BorelSpace L := ⟨rfl⟩
  have : ProperSpace L := FiniteDimensional.proper ℚ_[p] L
  exact (unitVol_measure_logUnit_mul_card p L Measure.addHaar).1 u

omit [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] in
/-- The `p`-primary component of `R^×` lies in the torsion subgroup `R^μ`. -/
theorem unitVol_primaryComponent_le_torsion :
    CommGroup.primaryComponent (integralClosure ℤ_[p] L)ˣ p ≤
      CommGroup.torsion (integralClosure ℤ_[p] L)ˣ := by
  rintro g ⟨k, hk⟩
  rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  exact ⟨p ^ k, pow_pos hp.out.pos k, hk⟩

/-- **`R^μ` is finite** and its `p`-primary component has order `p ^ m`,
`m = unitVolTorsionExponent p L`. -/
theorem unitVol_card_primaryComponent :
    Finite (CommGroup.torsion (integralClosure ℤ_[p] L)ˣ) ∧
      Finite (CommGroup.primaryComponent (integralClosure ℤ_[p] L)ˣ p) ∧
      Nat.card (CommGroup.primaryComponent (integralClosure ℤ_[p] L)ˣ p) =
        p ^ unitVolTorsionExponent p L := by
  let := spectralNorm.normedField ℚ_[p] L
  let := spectralNorm.normedAlgebra ℚ_[p] L
  let _ : MeasurableSpace L := borel L
  have : BorelSpace L := ⟨rfl⟩
  have : ProperSpace L := FiniteDimensional.proper ℚ_[p] L
  have hT := (unitVol_measure_logUnit_mul_card p L Measure.addHaar).2.1
  have hle := unitVol_primaryComponent_le_torsion p L
  have hP : Finite (CommGroup.primaryComponent (integralClosure ℤ_[p] L)ˣ p) :=
    Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  refine ⟨hT, hP, ?_⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp
    (CommGroup.primaryComponent.isPGroup (G := (integralClosure ℤ_[p] L)ˣ) (p := p))
  rw [unitVolTorsionExponent, hn, Nat.factorization_pow, Finsupp.smul_apply,
    hp.out.factorization_self, smul_eq_mul, mul_one]

/-- **Haar measure of the units**: `μ (R^×) = μ (R) − p ^ (−f) μ (R)`, that is
`μ (R^×) = (1 − p ^ (−f)) μ (R)`, for `R = integralClosure ℤ_[p] L` and every additive Haar
measure `μ` on `L` (IUT IV page 14: "`e_i f_i μ^log(R_i^×) = log(1 − p ^ (−f_i))`"). The
nonunits form the ideal `P = ϖ R`, of measure `‖ϖ‖ ^ d μ (R)`, and `‖ϖ‖ ^ d = p ^ (−f)` since
`‖ϖ‖ ^ e = p⁻¹` and `d = e f`. -/
theorem unitVol_measure_units (P : Ideal (integralClosure ℤ_[p] L)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    letI := spectralNorm.normedField ℚ_[p] L
    letI := spectralNorm.normedAlgebra ℚ_[p] L
    letI : MeasurableSpace L := borel L
    ∀ (μ : Measure L) [μ.IsAddHaarMeasure],
      μ (Set.range
          (fun u : (integralClosure ℤ_[p] L)ˣ => ((u : integralClosure ℤ_[p] L) : L))) =
        μ (integralClosure ℤ_[p] L : Set L) -
          ((p : ENNReal) ^ unitVolResidueDegree p L)⁻¹ * μ (integralClosure ℤ_[p] L : Set L) := by
  let := spectralNorm.normedField ℚ_[p] L
  let := spectralNorm.normedAlgebra ℚ_[p] L
  let _ : MeasurableSpace L := borel L
  have : BorelSpace L := ⟨rfl⟩
  intro μ _
  have : ProperSpace L := FiniteDimensional.proper ℚ_[p] L
  obtain ⟨ϖ, -, -, -, hpos, hlt1, hpe, -, hle⟩ := padicBridge_uniformizer p L P
  have hϖ0 : (ϖ : L) ≠ 0 := norm_pos_iff.mp hpos
  rw [padicBridge_range_units_eq_unitSphere p L, padicBridge_integralClosure_eq_unitBall p L]
  set Bl : Set L := {y : L | ‖y‖ ≤ 1}
  have hopen : {y : L | ‖y‖ < 1} = (ϖ : L) • Bl := by
    rw [padicVol_smul_ball hϖ0, mul_one]
    ext y
    simp only [Set.mem_ofPred_eq]
    exact ⟨hle y, fun h => lt_of_le_of_lt h hlt1⟩
  have hdiff : {y : L | ‖y‖ = 1} = Bl \ {y : L | ‖y‖ < 1} := by
    ext y
    simp only [Bl, Set.mem_sdiff, Set.mem_ofPred_eq, not_lt]
    constructor
    · intro h
      exact ⟨h.le, h.ge⟩
    · rintro ⟨h1, h2⟩
      exact le_antisymm h1 h2
  have hsub : {y : L | ‖y‖ < 1} ⊆ Bl := fun y (hy : ‖y‖ < 1) => show ‖y‖ ≤ 1 from hy.le
  have hmeas : MeasurableSet {y : L | ‖y‖ < 1} :=
    (isOpen_lt continuous_norm continuous_const).measurableSet
  have hBtop := padicVol_unitBall_ne_top p μ (K := L)
  have hfin : μ {y : L | ‖y‖ < 1} ≠ ⊤ := ne_top_of_le_ne_top hBtop (measure_mono hsub)
  rw [hdiff, measure_sdiff hsub hmeas.nullMeasurableSet hfin, hopen,
    volBridge_measure_smul p L hϖ0 Bl μ]
  congr 2
  -- `‖ϖ‖ ^ d = p ^ (-f)`
  have hd := unitVol_ramificationIdx_mul_residueDegree p L P
  have hnn : (‖(ϖ : L)‖₊ ^ Module.finrank ℚ_[p] L : NNReal) =
      ((p : NNReal) ^ unitVolResidueDegree p L)⁻¹ := by
    apply NNReal.eq
    push_cast
    rw [← hd, pow_mul, hpe, inv_pow]
  have hp0 : ((p : NNReal) ^ unitVolResidueDegree p L) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  rw [hnn, ENNReal.coe_inv hp0]
  push_cast
  rfl

/-! ## 5. Proposition 1.4 (ii) -/

/-- **IUT IV Proposition 1.4 (ii), with the order of the torsion as a parameter** (pages 13 and
14): for a finite extension `L` of `ℚ_[p]`, `R = integralClosure ℤ_[p] L`, its unit group `R^×`,
`e = P.ramificationIdx ℤ_[p]`, `f = unitVolResidueDegree p L` and the normalized log-volume
`μ^log` of `VolumeBridge.lean` (normalized by `μ^log(R) = 0`, divided by `[L : ℚ_p] = e f`),
`μ^log(log_p(R^×)) = (log(1 − p ^ (−f)) − log |R^μ|) / (e f)`, with `R^μ` the torsion subgroup of
`R^×`. This is the computation `e f μ^log(R^{×μ}) = e f μ^log(R^×) − log |R^μ|` of page 14,
with `e f μ^log(R^×) = log(1 − p ^ (−f))`. -/
theorem unitVol_muLog_logUnit_eq_card (P : Ideal (integralClosure ℤ_[p] L)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    letI := spectralNorm.normedField ℚ_[p] L
    letI := spectralNorm.normedAlgebra ℚ_[p] L
    letI : MeasurableSpace L := borel L
    ∀ (μ : Measure L) [μ.IsAddHaarMeasure],
      padicMuLog p μ (integralClosure ℤ_[p] L : Set L) (extLogUnit '' Set.range
          (fun u : (integralClosure ℤ_[p] L)ˣ => ((u : integralClosure ℤ_[p] L) : L))) =
        (Real.log (1 - ((p : ℝ) ^ unitVolResidueDegree p L)⁻¹) -
            Real.log (Nat.card (CommGroup.torsion (integralClosure ℤ_[p] L)ˣ))) /
          ((P.ramificationIdx ℤ_[p] : ℝ) * unitVolResidueDegree p L) := by
  let := spectralNorm.normedField ℚ_[p] L
  let := spectralNorm.normedAlgebra ℚ_[p] L
  let _ : MeasurableSpace L := borel L
  have : BorelSpace L := ⟨rfl⟩
  intro μ _
  obtain ⟨-, hT, hmain⟩ := unitVol_measure_logUnit_mul_card p L μ
  have hU := unitVol_measure_units p L P μ
  obtain ⟨hR0, hRtop, -, -⟩ := volBridge_muLog_integralClosure p L μ
  have hd := unitVol_ramificationIdx_mul_residueDegree p L P
  have hf := unitVol_residueDegree_pos p L
  set f := unitVolResidueDegree p L
  set N := Nat.card (CommGroup.torsion (integralClosure ℤ_[p] L)ˣ) with hNdef
  set R : Set L := (integralClosure ℤ_[p] L : Set L)
  set S : Set L :=
    Set.range (fun u : (integralClosure ℤ_[p] L)ˣ => ((u : integralClosure ℤ_[p] L) : L))
  set H : Set L := extLogUnit '' S
  have hN : 0 < N := by
    have := hT
    exact Nat.card_pos
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpf : (1 : ℝ) < (p : ℝ) ^ f := one_lt_pow₀ hp1 hf.ne'
  have hq : ((p : ENNReal) ^ f)⁻¹ * μ R ≤ μ R := by
    refine mul_le_of_le_one_left (by positivity) ?_
    rw [ENNReal.inv_le_one]
    exact one_le_pow₀ (by exact_mod_cast hp.out.one_lt.le)
  have hSr : (μ S).toReal = (1 - ((p : ℝ) ^ f)⁻¹) * (μ R).toReal := by
    rw [hU, ENNReal.toReal_sub_of_le hq hRtop, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_pow, ENNReal.toReal_natCast]
    ring
  have hHr : (μ H).toReal * N = (μ S).toReal := by
    rw [← hmain, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hRpos : 0 < (μ R).toReal := ENNReal.toReal_pos hR0 hRtop
  have hratio : (μ H).toReal / (μ R).toReal = (1 - ((p : ℝ) ^ f)⁻¹) / N := by
    rw [div_eq_div_iff hRpos.ne' hN', hHr, hSr]
  have hpos : (1 : ℝ) - ((p : ℝ) ^ f)⁻¹ ≠ 0 := by
    have : ((p : ℝ) ^ f)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpf
    linarith
  have hd' : (Module.finrank ℚ_[p] L : ℝ) = (P.ramificationIdx ℤ_[p] : ℝ) * f := by
    rw [← hd]
    push_cast
    ring
  unfold padicMuLog
  rw [hratio, Real.log_div hpos hN']
  congr 1

/-- **IUT IV Proposition 1.4 (ii)** (page 13), assuming the order count stated just before it:
if the torsion subgroup `R^μ` of `R^×` has order `p ^ m (p ^ f − 1)`, with
`m = unitVolTorsionExponent p L` (`p ^ m` the order of the `p`-primary component) and
`f = unitVolResidueDegree p L` (`p ^ f` the cardinality of the residue field), then
`μ^log(log_p(R^×)) = −(1 / e + m / (e f)) log p`, `e = P.ramificationIdx ℤ_[p]`. The hypothesis is
the sentence "the order of `R_i^μ` is equal to `p ^ (m_i) · (p ^ (f_i) − 1)`" of page 13; it is
proved in `unitVol_card_torsion`. -/
theorem unitVol_muLog_logUnit_eq_of_card (P : Ideal (integralClosure ℤ_[p] L)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (hcard : Nat.card (CommGroup.torsion (integralClosure ℤ_[p] L)ˣ) =
      p ^ unitVolTorsionExponent p L * (p ^ unitVolResidueDegree p L - 1)) :
    letI := spectralNorm.normedField ℚ_[p] L
    letI := spectralNorm.normedAlgebra ℚ_[p] L
    letI : MeasurableSpace L := borel L
    ∀ (μ : Measure L) [μ.IsAddHaarMeasure],
      padicMuLog p μ (integralClosure ℤ_[p] L : Set L) (extLogUnit '' Set.range
          (fun u : (integralClosure ℤ_[p] L)ˣ => ((u : integralClosure ℤ_[p] L) : L))) =
        -(1 / (P.ramificationIdx ℤ_[p] : ℝ) +
            (unitVolTorsionExponent p L : ℝ) /
              ((P.ramificationIdx ℤ_[p] : ℝ) * unitVolResidueDegree p L)) * Real.log p := by
  let := spectralNorm.normedField ℚ_[p] L
  let := spectralNorm.normedAlgebra ℚ_[p] L
  let _ : MeasurableSpace L := borel L
  intro μ _
  have := isDedekindDomain_ringOfIntegers_padic p L
  have := isTorsionFree_ringOfIntegers_padic p L
  rw [unitVol_muLog_logUnit_eq_card p L P μ, hcard]
  have hf := unitVol_residueDegree_pos p L
  have he : 0 < P.ramificationIdx ℤ_[p] :=
    ramificationIdx_pos_of_liesOver (IsDiscreteValuationRing.not_a_field ℤ_[p]) P
  set f := unitVolResidueDegree p L
  set m := unitVolTorsionExponent p L
  set e := P.ramificationIdx ℤ_[p]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpf : (1 : ℝ) < (p : ℝ) ^ f := one_lt_pow₀ hp1 hf.ne'
  have hpf0 : (0 : ℝ) < (p : ℝ) ^ f - 1 := by linarith
  have h1 : (1 : ℝ) - ((p : ℝ) ^ f)⁻¹ = ((p : ℝ) ^ f - 1) / (p : ℝ) ^ f := by
    field_simp
  have hcast : (((p ^ m * (p ^ f - 1) : ℕ)) : ℝ) = (p : ℝ) ^ m * ((p : ℝ) ^ f - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (Nat.one_le_pow _ _ hp.out.pos)]
    push_cast
    ring
  have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have hf0 : (f : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
  rw [hcast, h1, Real.log_div hpf0.ne' (by positivity), Real.log_mul (by positivity) hpf0.ne',
    Real.log_pow, Real.log_pow]
  field_simp
  ring

/-- **Consistency with the equality case of Proposition 1.2 (i)**: for `p > 2` and
`e = P.ramificationIdx ℤ_[p] ≤ p − 2`, the torsion subgroup `R^μ` of `R^×` has order `p ^ f − 1`
and `m = 0`, so the value `−(1 / e) log p` of `volBridge_muLog_logUnit_eq_of_le` is the value
`−(1 / e + m / (e f)) log p` of Proposition 1.4 (ii). The proof compares that value with
`unitVol_muLog_logUnit_eq_card`. -/
theorem unitVol_card_torsion_of_le (P : Ideal (integralClosure ℤ_[p] L)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] (hp2 : 2 < p)
    (hep : P.ramificationIdx ℤ_[p] ≤ p - 2) :
    Nat.card (CommGroup.torsion (integralClosure ℤ_[p] L)ˣ) = p ^ unitVolResidueDegree p L - 1 ∧
      unitVolTorsionExponent p L = 0 := by
  let := spectralNorm.normedField ℚ_[p] L
  let := spectralNorm.normedAlgebra ℚ_[p] L
  let _ : MeasurableSpace L := borel L
  have : BorelSpace L := ⟨rfl⟩
  have : ProperSpace L := FiniteDimensional.proper ℚ_[p] L
  have := isDedekindDomain_ringOfIntegers_padic p L
  have := isTorsionFree_ringOfIntegers_padic p L
  have h1 := unitVol_muLog_logUnit_eq_card p L P (Measure.addHaar : Measure L)
  have h2 := volBridge_muLog_logUnit_eq_of_le p L P hp2 hep (Measure.addHaar : Measure L)
  rw [h1] at h2
  obtain ⟨hT, hPfin, hPcard⟩ := unitVol_card_primaryComponent p L
  have hf := unitVol_residueDegree_pos p L
  have he : 0 < P.ramificationIdx ℤ_[p] :=
    ramificationIdx_pos_of_liesOver (IsDiscreteValuationRing.not_a_field ℤ_[p]) P
  set f := unitVolResidueDegree p L
  set e := P.ramificationIdx ℤ_[p]
  set N := Nat.card (CommGroup.torsion (integralClosure ℤ_[p] L)ˣ) with hNdef
  have hN : 0 < N := by
    have := hT
    exact Nat.card_pos
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpf : (1 : ℝ) < (p : ℝ) ^ f := one_lt_pow₀ hp1 hf.ne'
  have hpf0 : (0 : ℝ) < (p : ℝ) ^ f - 1 := by linarith
  have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have hf0 : (f : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
  have hA : Real.log (1 - ((p : ℝ) ^ f)⁻¹) = Real.log ((p : ℝ) ^ f - 1) - f * Real.log p := by
    have h1 : (1 : ℝ) - ((p : ℝ) ^ f)⁻¹ = ((p : ℝ) ^ f - 1) / (p : ℝ) ^ f := by
      field_simp
    rw [h1, Real.log_div hpf0.ne' (by positivity), Real.log_pow]
  rw [div_eq_iff (mul_ne_zero he0 hf0)] at h2
  have h3 : -(1 / (e : ℝ)) * Real.log p * ((e : ℝ) * f) = -(f * Real.log p) := by
    field_simp
  have hlog : Real.log N = Real.log ((p : ℝ) ^ f - 1) := by
    linarith
  have hNr : (N : ℝ) = (p : ℝ) ^ f - 1 :=
    Real.log_injOn_pos (Set.mem_Ioi.2 (by exact_mod_cast hN)) (Set.mem_Ioi.2 hpf0) hlog
  have hNn : N = p ^ f - 1 := by
    have hc : ((p ^ f - 1 : ℕ) : ℝ) = (p : ℝ) ^ f - 1 := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ hp.out.pos)]
      push_cast
      ring
    exact_mod_cast hNr.trans hc.symm
  refine ⟨hNn, ?_⟩
  have hdvd := Subgroup.card_dvd_of_le (unitVol_primaryComponent_le_torsion p L)
  rw [hPcard, ← hNdef, hNn] at hdvd
  by_contra hm
  have hpd : p ∣ p ^ f - 1 := (dvd_pow_self p hm).trans hdvd
  have hpd2 : p ∣ p ^ f := dvd_pow_self p hf.ne'
  have h1p : p ∣ p ^ f - (p ^ f - 1) := Nat.dvd_sub hpd2 hpd
  rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.out.pos)] at h1p
  exact hp.out.not_dvd_one h1p

/-! ## 6. The order of the torsion subgroup -/

/-- **`R` is complete for its maximal ideal**: `R = integralClosure ℤ_[p] L` is `P`-adically
complete, from the completeness of `L` for the spectral norm and `P ^ n = {‖x‖ ≤ ‖ϖ‖ ^ n}`. -/
theorem unitVol_isAdicComplete :
    haveI := padicBridge_isLocalRing p L
    IsAdicComplete (IsLocalRing.maximalIdeal (integralClosure ℤ_[p] L))
      (integralClosure ℤ_[p] L) := by
  let := spectralNorm.normedField ℚ_[p] L
  let := spectralNorm.normedAlgebra ℚ_[p] L
  have := padicBridge_isLocalRing p L
  have := padicBridge_maximalIdeal_liesOver p L
  have : CompleteSpace L := FiniteDimensional.completeSpace ℚ_[p] L
  set M := IsLocalRing.maximalIdeal (integralClosure ℤ_[p] L)
  obtain ⟨ϖ, -, hPϖ, -, hpos, hlt1, -, -, -⟩ := padicBridge_uniformizer p L M
  have hϖ0 : (ϖ : L) ≠ 0 := norm_pos_iff.mp hpos
  have hmem : ∀ (n : ℕ) (x : integralClosure ℤ_[p] L),
      x ∈ (M ^ n • ⊤ : Submodule (integralClosure ℤ_[p] L) (integralClosure ℤ_[p] L)) ↔
        ‖(x : L)‖ ≤ ‖(ϖ : L)‖ ^ n := by
    intro n x
    rw [Ideal.smul_eq_mul, Ideal.mul_top, hPϖ, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, rfl⟩
      push_cast
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) n)
        (padicBridge_norm_le_one p L y)
    · intro hx
      have hy : (x : L) / (ϖ : L) ^ n ∈ integralClosure ℤ_[p] L := by
        rw [padicBridge_mem_integralClosure_iff, norm_div, norm_pow,
          div_le_one (pow_pos hpos n)]
        exact hx
      refine ⟨⟨_, hy⟩, Subtype.ext ?_⟩
      push_cast
      field_simp
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have hx' : ∀ n : ℕ, ‖(x : L)‖ ≤ ‖(ϖ : L)‖ ^ n := by
      intro n
      have h := SModEq.sub_mem.mp (hx n)
      rw [sub_zero] at h
      exact (hmem n x).1 h
    by_contra hne
    have hx0 : 0 < ‖(x : L)‖ := by
      rw [norm_pos_iff]
      intro h
      exact hne (Subtype.ext h)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hx0 hlt1
    exact absurd (hx' n) (not_le.mpr hn)
  · intro f hf
    have hle : ∀ m n : ℕ, m ≤ n → ‖(f m : L) - f n‖ ≤ ‖(ϖ : L)‖ ^ m := by
      intro m n hmn
      have h := (hmem m _).1 (SModEq.sub_mem.mp (hf hmn))
      push_cast at h
      exact h
    have hcs : CauchySeq (fun n => (f n : L)) := by
      refine cauchySeq_of_le_tendsto_0 (fun N => 2 * ‖(ϖ : L)‖ ^ N) ?_ ?_
      · intro n m N hn hm
        rw [dist_eq_norm]
        calc ‖(f n : L) - f m‖ = ‖((f N : L) - f m) - ((f N : L) - f n)‖ := by ring_nf
          _ ≤ ‖(f N : L) - f m‖ + ‖(f N : L) - f n‖ := norm_sub_le _ _
          _ ≤ ‖(ϖ : L)‖ ^ N + ‖(ϖ : L)‖ ^ N := add_le_add (hle N m hm) (hle N n hn)
          _ = 2 * ‖(ϖ : L)‖ ^ N := by ring
      · have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hlt1).const_mul 2
        simpa using h
    obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcs
    have hl1 : ‖l‖ ≤ 1 :=
      le_of_tendsto' hl.norm (fun n => padicBridge_norm_le_one p L (f n))
    have hlR : l ∈ integralClosure ℤ_[p] L := (padicBridge_mem_integralClosure_iff p L l).2 hl1
    refine ⟨⟨l, hlR⟩, fun n => SModEq.sub_mem.mpr ((hmem n _).2 ?_)⟩
    have hT : Filter.Tendsto (fun k => ‖(f n : L) - f k‖) Filter.atTop (nhds ‖(f n : L) - l‖) :=
      (tendsto_const_nhds.sub hl).norm
    have h := le_of_tendsto hT (Filter.eventually_atTop.2 ⟨n, fun k hk => hle n k hk⟩)
    push_cast
    exact h

omit hp in
/-- `p ∤ p ^ f − 1` for `f ≥ 1`. -/
theorem unitVol_not_dvd_pow_sub_one (hp1 : 1 < p) {f : ℕ} (hf : 0 < f) : ¬ p ∣ p ^ f - 1 := by
  intro hpd
  have hpd2 : p ∣ p ^ f := dvd_pow_self p hf.ne'
  have h1p : p ∣ p ^ f - (p ^ f - 1) := Nat.dvd_sub hpd2 hpd
  rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (by omega))] at h1p
  exact absurd (Nat.le_of_dvd one_pos h1p) (by omega)

/-- **The order of the torsion of `R^×`** (IUT IV page 13: "the order of `R_i^μ` is equal to
`p ^ (m_i) · (p ^ (f_i) − 1)`"): `|R^μ| = p ^ m (p ^ f − 1)`. Reduction modulo the maximal ideal
`P` maps `R^μ` to `(R ⧸ P)^×`, a group of order `p ^ f − 1`; its kernel is the `p`-primary
component (an element of `p`-power order reduces to `1` in characteristic `p`, and an element of
`1 + P` of order prime to `p` is `1`, since `1 + x + ⋯ + x ^ (n − 1)` reduces to `n ≠ 0`); it is
onto, by Hensel's lemma for `X ^ (p ^ f − 1) − 1` (Mathlib's `IsAdicComplete.henselianRing`, with
`unitVol_isAdicComplete`). -/
theorem unitVol_card_torsion :
    Nat.card (CommGroup.torsion (integralClosure ℤ_[p] L)ˣ) =
      p ^ unitVolTorsionExponent p L * (p ^ unitVolResidueDegree p L - 1) := by
  let := spectralNorm.normedField ℚ_[p] L
  have := padicBridge_isLocalRing p L
  have := padicBridge_maximalIdeal_liesOver p L
  have := isDedekindDomain_ringOfIntegers_padic p L
  have hAC := unitVol_isAdicComplete p L
  obtain ⟨hT, hPfin, hPcard⟩ := unitVol_card_primaryComponent p L
  have hf := unitVol_residueDegree_pos p L
  set R := integralClosure ℤ_[p] L
  set M := IsLocalRing.maximalIdeal R
  set f := unitVolResidueDegree p L
  have hcardk : Nat.card (R ⧸ M) = p ^ f := unitVol_card_residueField p L M
  let _ : Field (R ⧸ M) := Ideal.Quotient.field M
  have hkfin : Finite (R ⧸ M) :=
    Nat.finite_of_card_ne_zero (by rw [hcardk]; exact pow_ne_zero _ hp.out.ne_zero)
  classical
  let _ : Fintype (R ⧸ M) := Fintype.ofFinite _
  have hpk : ((p : ℕ) : R ⧸ M) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq_zero_iff_mem,
      padicBridge_mem_maximalIdeal_iff]
    push_cast
    rw [padicBridge_norm_natCast_p p L]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  have hchar : CharP (R ⧸ M) p := (CharP.charP_iff_prime_eq_zero hp.out).2 hpk
  set T := CommGroup.torsion Rˣ
  let red : T →* (R ⧸ M)ˣ := (Units.map (Ideal.Quotient.mk M).toMonoidHom).comp T.subtype
  have hred : ∀ ζ : T, ((red ζ : (R ⧸ M)ˣ) : R ⧸ M) = Ideal.Quotient.mk M ((ζ : Rˣ) : R) :=
    fun _ => rfl
  have hle := unitVol_primaryComponent_le_torsion p L
  -- the kernel of the reduction is the `p`-primary component
  have hker : red.ker = (CommGroup.primaryComponent Rˣ p).subgroupOf T := by
    ext ζ
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Units.ext_iff, hred, Units.val_one]
    constructor
    · intro h1
      obtain ⟨n, hn, hζn⟩ := isOfFinOrder_iff_pow_eq_one.mp ((CommGroup.mem_torsion _).mp ζ.2)
      obtain ⟨a, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.out.ne_one
      refine ⟨a, ?_⟩
      set η : Rˣ := (ζ : Rˣ) ^ p ^ a
      have hη : η ^ n' = 1 := by rw [← pow_mul]; exact hζn
      have hηk : Ideal.Quotient.mk M (η : R) = 1 := by
        rw [Units.val_pow_eq_pow_val, map_pow, h1, one_pow]
      set S : R := ∑ i ∈ Finset.range n', (η : R) ^ i
      have hS : S * ((η : R) - 1) = 0 := by
        rw [geom_sum_mul, ← Units.val_pow_eq_pow_val, hη, Units.val_one, sub_self]
      have hSk : Ideal.Quotient.mk M S = (n' : R ⧸ M) := by
        simp [S, _root_.map_sum, map_pow, hηk]
      have hS0 : S ≠ 0 := by
        intro h0
        have : (n' : R ⧸ M) = 0 := by rw [← hSk, h0, map_zero]
        exact hn' ((CharP.cast_eq_zero_iff (R ⧸ M) p n').mp this)
      have hη1 : (η : R) = 1 := sub_eq_zero.mp ((mul_eq_zero.mp hS).resolve_left hS0)
      exact Units.ext hη1
    · rintro ⟨k, hk⟩
      have h1 : (Ideal.Quotient.mk M ((ζ : Rˣ) : R)) ^ p ^ k = 1 := by
        rw [← map_pow, ← Units.val_pow_eq_pow_val, hk, Units.val_one, map_one]
      have h2 : (Ideal.Quotient.mk M ((ζ : Rˣ) : R) - 1) ^ p ^ k = 0 := by
        rw [sub_pow_char_pow, h1, one_pow, sub_self]
      exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero k hp.out.ne_zero) |>.mp h2)
  -- the reduction is onto `(R ⧸ M)ˣ`
  have hq : Fintype.card (R ⧸ M) = p ^ f := by rw [← Nat.card_eq_fintype_card, hcardk]
  have hq1 : p ^ f - 1 ≠ 0 := by
    have : 1 < p ^ f := Nat.one_lt_pow hf.ne' hp.out.one_lt
    omega
  have hsurj : Function.Surjective red := by
    intro x
    obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective (x : R ⧸ M)
    let F : Polynomial R := Polynomial.X ^ (p ^ f - 1) - Polynomial.C 1
    have hF : F.Monic := Polynomial.monic_X_pow_sub_C 1 hq1
    have hx1 : (x : R ⧸ M) ^ (p ^ f - 1) = 1 := by
      rw [← hq]
      exact FiniteField.pow_card_sub_one_eq_one _ x.ne_zero
    have h₁ : F.eval a₀ ∈ M := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp [F, ha₀, hx1]
    have h₂ : IsUnit (Ideal.Quotient.mk M (F.derivative.eval a₀)) := by
      rw [isUnit_iff_ne_zero]
      have hc : ((p ^ f - 1 : ℕ) : R ⧸ M) ≠ 0 := fun h0 =>
        unitVol_not_dvd_pow_sub_one p hp.out.one_lt hf
          ((CharP.cast_eq_zero_iff (R ⧸ M) p _).mp h0)
      simp only [F, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
        Polynomial.derivative_C, sub_zero, Polynomial.eval_mul, Polynomial.eval_natCast,
        Polynomial.eval_pow, Polynomial.eval_X, map_mul, map_pow, map_natCast, ha₀]
      exact mul_ne_zero hc (pow_ne_zero _ x.ne_zero)
    obtain ⟨a, ha, haa⟩ := HenselianRing.is_henselian (I := M) F hF a₀ h₁ h₂
    have ha1 : a ^ (p ^ f - 1) = 1 := by
      have := ha.eq_zero
      simp only [F, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C] at this
      exact sub_eq_zero.mp this
    let u : Rˣ := Units.ofPowEqOne a (p ^ f - 1) ha1 hq1
    have hu : u ∈ T := by
      rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
      exact ⟨p ^ f - 1, Nat.pos_of_ne_zero hq1, Units.pow_ofPowEqOne ha1 hq1⟩
    refine ⟨⟨u, hu⟩, Units.ext ?_⟩
    rw [hred]
    show Ideal.Quotient.mk M a = (x : R ⧸ M)
    rw [← ha₀]
    exact Ideal.Quotient.eq.mpr haa
  -- counting
  have h1 := Subgroup.card_mul_index red.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective red hsurj, Subgroup.card_top,
    Nat.card_units, hcardk, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hPcard] at h1
  exact h1.symm

/-- **IUT IV Proposition 1.4 (ii)** (page 13): for a finite extension `L` of `ℚ_[p]`, with
`R = integralClosure ℤ_[p] L`, its unit group `R^×`, `e = P.ramificationIdx ℤ_[p]` for the prime
`P` over `p`, `f = unitVolResidueDegree p L` (`p ^ f` the cardinality of the residue field),
`m = unitVolTorsionExponent p L` (`p ^ m` the order of the `p`-primary component of the torsion of
`R^×`), the spectral norm, and `μ^log` the log-volume normalized by `μ^log(R) = 0` and divided by
`[L : ℚ_p]`: for every additive Haar measure,
`μ^log(log_p(R^×)) = −(1 / e + m / (e f)) · log p`. -/
theorem unitVol_muLog_logUnit_eq (P : Ideal (integralClosure ℤ_[p] L)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    letI := spectralNorm.normedField ℚ_[p] L
    letI := spectralNorm.normedAlgebra ℚ_[p] L
    letI : MeasurableSpace L := borel L
    ∀ (μ : Measure L) [μ.IsAddHaarMeasure],
      padicMuLog p μ (integralClosure ℤ_[p] L : Set L) (extLogUnit '' Set.range
          (fun u : (integralClosure ℤ_[p] L)ˣ => ((u : integralClosure ℤ_[p] L) : L))) =
        -(1 / (P.ramificationIdx ℤ_[p] : ℝ) +
            (unitVolTorsionExponent p L : ℝ) /
              ((P.ramificationIdx ℤ_[p] : ℝ) * unitVolResidueDegree p L)) * Real.log p :=
  unitVol_muLog_logUnit_eq_of_card p L P (unitVol_card_torsion p L)

end Field

end IUT.PaperIV.LocalFields
