import IUT.PaperIV.LocalFields.Logarithm
import IUT.PaperIII.Corollary312.Comparison

/-!
# Haar measure and normalized log-volume on finite-dimensional `ℚ_p`-vector spaces

Sources:
* Mochizuki, *Inter-universal Teichmüller Theory IV*, Proposition 1.4 (i), page 13: the
  log-volumes of [AbsTopIII], Proposition 5.7, on finite extensions of `ℚ_p` "may be suitably
  normalized [i.e., by dividing by the degree of the finite extension] so as to yield a notion of
  log-volume `μ^log(−)` defined on compact open subsets of finite extensions of `ℚ_p` contained in
  `ℚ̄_p`, valued in `ℝ`, and normalized so that `μ^log(R_i) = 0`, `μ^log(p · R_i) = −log(p)`";
  on tensor products, which "decompose, naturally, as direct sums of finitely many finite
  extensions of `ℚ_p`", one obtains a log-volume "defined on compact open subsets of such tensor
  products, valued in `ℝ`, and normalized so that `μ^log((R_E)^∼) = 0`,
  `μ^log(p · (R_E)^∼) = −log(p)`". Proposition 1.4 (ii) to (iv), pages 13 and 14, and the proof
  on page 14 (which uses `μ^log(R_I) ≤ μ^log((R_I)^∼) = 0` and the additivity of `μ^log` over
  tensor products).
* IUT IV, Proposition 1.1, page 9 (`R_E = ⊗_{i ∈ E} R_i` over `ℤ_p`, and `(−)^∼` the
  normalization of the reduced ring in its ring of fractions), and Proposition 1.2, pages 10
  and 11 (the constants `a_i`, `b_i` and the inclusions (i) to (iv)).
* Mochizuki, *Inter-universal Teichmüller Theory III*, Proposition 3.9 (i), pages 115 and 116:
  the `p_v`-adic log-volume on each direct summand, normalized so that the integral structures
  have log-volume zero and "multiplication of an element of `𝔐(−)` by `p_v` corresponds to adding
  the quantity `−log(p_v)`" (the packet-normalization). Remark 3.1.1 (ii), (iii), pages 94 and 95:
  the normalized weights, and the warning that weighted sums of log-volumes do not in general
  arise as a positive multiple of the logarithm of a measure.

Pages read for this file: IUT IV pages 9, 10, 11, 13 and 14; IUT III pages 94, 95, 115 and 116.
Pages checked against rendered images: the same.

## What is proved

1. *Scaling of Haar measure.* For a finite-dimensional normed `ℚ_p`-vector space `V` of
   dimension `d` and any additive Haar measure `μ` on `V`:
   `μ (c • A) = ‖c‖ ^ d · μ A` for every `c ≠ 0` in `ℚ_p` and every set `A`
   (`padicVol_measure_smul`). The proof computes the distributive Haar character of `ℚ_p^×`
   (`MeasureTheory.distribHaarChar`) on one box `{x | ∀ i, ‖x_i‖ ≤ 1}` in coordinates: the box is
   the disjoint union of `p ^ d` translates of `p` times itself (`padicVolBox_measure_one`).
2. *Normalized log-volume.* `padicMuLog p μ Λ A = log (μ A / μ Λ) / d`, real valued, normalized
   at a set `Λ`. It does not depend on the Haar measure (`padicMuLog_haar_indep`), nor on a
   change of coordinates by a continuous linear automorphism (`padicMuLog_image_equiv`). Laws:
   `μ^log(Λ) = 0` (`padicMuLog_self`), translation invariance (`padicMuLog_vadd`), monotonicity
   (`padicMuLog_mono`), `μ^log(c • A) = μ^log(A) + log ‖c‖` (`padicMuLog_smul`), hence
   `μ^log(p ^ n • A) = μ^log(A) − n log p` (`padicMuLog_p_zpow_smul`). The `EReal` form
   `padicMuLogE` is monotone on all sets (`padicMuLogE_mono`), agrees with `padicMuLog` on sets of
   positive finite measure (`padicMuLogE_eq`), and is a region log-volume for the interface of
   `IUT.PaperIII.Corollary312.Comparison` (`padicRegionComparison`).
3. *A finite extension `K` of `ℚ_p`* (a normed field that is a finite-dimensional normed
   `ℚ_p`-algebra; `R` is the closed unit ball, as in `IUT.PaperIV.LocalFields.Logarithm`):
   `μ^log(R) = 0` and `μ^log(p · R) = −log p` with the normalization of IUT IV page 13
   (`padicMuLog_unitBall`, `padicMuLog_p_smul_unitBall`); `μ (x • A) = ‖x‖ ^ d · μ A` for
   `x ∈ K^×` with `‖x‖ ^ m = p ^ (−n)` for some `m ≥ 1` (`padicVol_field_measure_smul`); for a
   uniformizer `π` (`‖π‖ ^ e = 1 / p`), the closed ball of radius `‖π‖ ^ k` has log-volume
   `−(k / e) log p` (`padicMuLog_ball_uniformizer`). From IUT IV Proposition 1.2 (i) as proved
   in `Logarithm.lean`: `−a · log p ≤ μ^log(log_p(R^×)) ≤ b · log p`
   (`padicMuLog_logUnit_bounds`) and the corresponding bounds for the log-shell
   `I = (p*)⁻¹ · log_p(R^×)`, shifted by `log p*` (`padicMuLog_logShell_bounds`).
4. *Tensor packets.* For a finite-dimensional `ℚ_p`-vector space `W` without topology (for
   example `K₁ ⊗[ℚ_p] K₂`), `padicPacketMuLog` is the normalized log-volume computed in the
   coordinates of `Module.finBasis`; by `padicMuLog_image_equiv` any other linear coordinates give
   the same value (`padicPacketMuLog_coord_indep`). Laws: `padicPacketMuLog_self`,
   `padicPacketMuLog_p_zpow_smul` (`μ^log(p ^ n • A) = μ^log(A) − n log p` for any `Λ`, `A` of
   positive finite measure), and `padicVol_finrank_tensor` (`dim (K₁ ⊗ K₂) = dim K₁ · dim K₂`,
   the degree by which the log-volume of the packet is divided). For two finite extensions the
   lattice `R_E` (`padicPacketIntegers`, the additive span of `x ⊗ y` with `x`, `y` integral over
   `ℤ_p`) and `(R_E)^∼` (`padicPacketNormalization`, the elements of `K₁ ⊗ K₂` integral over
   `ℤ_p`) are defined, and `R_E ⊆ (R_E)^∼` is proved (`padicPacketIntegers_subset`).
5. *Nonvacuity on `ℚ_p`* (`d = 1`): for the Haar measure normalized on `ℤ_p`,
   `μ(ℤ_p) = 1` (`padicVol_padic_unitBall`), `μ(p ^ n ℤ_p) = p ^ (−n)` (`padicVol_padic_p_zpow`),
   the log-shell of `ℚ_p` of `IUT.Prerequisites.PadicLog` has measure `1`
   (`padicVol_padicLogShell`) and normalized log-volume `0` (`padicMuLog_padicLogShell`), and the
   hypotheses `hval`, `hπ` of step 3 hold together for `K = ℚ_p`, `e = 1`, `π = p`
   (`padicMuLog_logUnit_bounds_padic`).

## Interpretation choices

* *The normalization.* IUT IV page 13 fixes `μ^log` on a finite extension `k_i` by the two
  values `μ^log(R_i) = 0` and `μ^log(p · R_i) = −log p`, "dividing by the degree". With `μ` a Haar
  measure on `k_i` and `d = [k_i : ℚ_p]`, the function `log (μ A / μ R_i) / d` has both values
  (`padicMuLog_unitBall`, `padicMuLog_p_smul_unitBall`); that it is the only function of the
  form `α log μ + β` with them is elementary and not formalized. The paper's `μ^log` is the log-volume of [AbsTopIII], Proposition
  5.7, which is not read here; that it is of this form is an interpretation, not a quotation.
* *The ring of integers.* As in `Logarithm.lean`, `R_i` is modeled by the closed unit ball of a
  norm extending the `p`-adic norm, `p ^ λ · R_i` by the closed ball of radius `p ^ (−λ)`, and the
  ramification index by a positive integer `e` with `‖x‖ ^ e ≤ 1 / p` on the open unit disc
  (`hval`). A uniformizer is an element `π` with `‖π‖ ^ e = 1 / p` (`hπ`). Both are standing
  properties of a finite extension with its ramification index, not claims of the papers; their
  derivation from `integralClosure ℤ_p k_i` and `Ideal.ramificationIdx` is not formalized.
* *Real values.* `padicMuLog` is real valued with Lean's `Real.log 0 = 0`; it is meaningful on
  sets of positive finite measure (the compact open sets of page 13), and every law below that
  needs it assumes it. The value `padicMuLog_self` holds for every `Λ`, so it carries content only
  when `0 < μ Λ < ∞`.
* *Tensor packets.* Page 13 obtains the log-volume on `⊗ k_i` from the decomposition into a
  direct sum of fields without saying how the summands are weighted. Here the packet log-volume
  is `log (μ A / μ Λ) / D` for one Haar measure `μ` on the `D`-dimensional space `⊗ k_i`, which
  has the two normalizing values of page 13 whenever `0 < μ Λ < ∞`. On a product region with
  respect to the decomposition it should be the sum of the log-volumes of the factors weighted
  by `[K_j : ℚ_p] / D` (not formalized; the decomposition itself is not formalized); other
  weightings are possible (IUT III Remark 3.1.1 (iii), page 95), and
  this one is a choice.
* *Normalization of `R_E`.* Page 9 defines `(R_E)^∼` as the normalization of the reduced ring
  `R_E` in its ring of fractions. Here `padicPacketNormalization` is the set of elements of
  `K₁ ⊗ K₂` integral over `ℤ_p`. The two agree because the ring of fractions of `R_E` is
  `K₁ ⊗ K₂` and `R_E` is integral over `ℤ_p`; neither fact is formalized.

## Not proved

* That `padicPacketNormalization` (that is `(R_E)^∼`) is compact and open in `K₁ ⊗ K₂`, so has
  positive finite Haar measure; without it the normalization `μ^log((R_E)^∼) = 0`,
  `μ^log(p · (R_E)^∼) = −log p` of page 13 is only an instance of the general laws for sets of
  positive finite measure. Its finiteness needs that `K₁ ⊗ K₂` is reduced (a product of
  fields), its openness that it contains a lattice.
* The general index formula `μ(Λ') = [Λ : Λ']⁻¹ μ(Λ)` for sublattices; only the case
  `Λ' = p Λ` of a coordinate box is proved (`padicVolBox_measure_one`).
* IUT IV Proposition 1.1 (`p ^ 𝔡 · (R_I)^∼ ⊆ R_I`), hence Proposition 1.2 (ii) to (iv).
* The additivity used on page 14, `μ^log(⊗ A_i) = ∑ μ^log(A_i) + μ^log(R_I)`: it needs the
  index formula for tensor products of lattices, or the determinant formula for Haar measure
  over `ℚ_p` (Mathlib has the latter only over `ℝ`).
* IUT IV Proposition 1.4 (ii), the exact value `−(1/e_i + m_i/(e_i f_i)) log p`: it needs the
  residue field, the torsion of `R_i^×`, and Haar measure on the unit group. The bounds of
  `padicMuLog_logUnit_bounds` come from Proposition 1.2 (i) only and are weaker.
* The identification of the closed unit ball with `integralClosure ℤ_p k_i` and of `π`, `e` with
  a uniformizer and the ramification index, and `μ (x • A) = ‖x‖ ^ d μ A` for every `x ∈ K^×`
  without the hypothesis on a power of `‖x‖`.
-/

namespace IUT.Prerequisites.PadicVolume

open MeasureTheory Measure Set
open scoped Pointwise

/-! ## Digits in `ℚ_p` -/

section Digits

variable {p : ℕ} [hp : Fact p.Prime]

/-- Every `z` with `‖z‖ ≤ 1` lies within `1 / p` of one of `0, …, p - 1`. -/
theorem padicVol_exists_digit {z : ℚ_[p]} (hz : ‖z‖ ≤ 1) :
    ∃ k : Fin p, ‖z - ((k : ℕ) : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
  obtain ⟨n, hn, hmem⟩ := PadicInt.exists_mem_range (⟨z, hz⟩ : ℤ_[p])
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
    ← PadicInt.norm_lt_one_iff_dvd] at hmem
  refine ⟨⟨n, hn⟩, ?_⟩
  have e : ((n : ℤ_[p]) : ℚ_[p]) = n := PadicInt.coe_natCast n
  have h : ‖z - (n : ℚ_[p])‖ < 1 := by rw [← e]; exact hmem
  exact IUT.PaperIV.LocalFields.extLog_padic_disc p _ h

/-- Two of the digits `0, …, p - 1` within `1 / p` of the same `z` are equal. -/
theorem padicVol_digit_unique {z : ℚ_[p]} {k k' : Fin p}
    (hk : ‖z - ((k : ℕ) : ℚ_[p])‖ ≤ (p : ℝ)⁻¹) (hk' : ‖z - ((k' : ℕ) : ℚ_[p])‖ ≤ (p : ℝ)⁻¹) :
    k = k' := by
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  have h : ‖((((k : ℕ) : ℤ) - ((k' : ℕ) : ℤ) : ℤ) : ℚ_[p])‖ < 1 := by
    have e : ((((k : ℕ) : ℤ) - ((k' : ℕ) : ℤ) : ℤ) : ℚ_[p]) =
        (z - ((k' : ℕ) : ℚ_[p])) - (z - ((k : ℕ) : ℚ_[p])) := by
      push_cast; ring
    rw [e]
    calc _ ≤ max ‖z - ((k' : ℕ) : ℚ_[p])‖ ‖z - ((k : ℕ) : ℚ_[p])‖ :=
          IUT.PaperIV.LocalFields.extLog_norm_sub_le_max _ _
      _ ≤ (p : ℝ)⁻¹ := max_le hk' hk
      _ < 1 := hp1
  rw [Padic.norm_intCast_lt_one_iff] at h
  obtain ⟨c, hc⟩ := h
  have hk1 : ((k : ℕ) : ℤ) < p := by exact_mod_cast k.isLt
  have hk2 : ((k' : ℕ) : ℤ) < p := by exact_mod_cast k'.isLt
  have hk3 : (0 : ℤ) ≤ ((k : ℕ) : ℤ) := by positivity
  have hk4 : (0 : ℤ) ≤ ((k' : ℕ) : ℤ) := by positivity
  have hc0 : c = 0 := by
    rcases lt_trichotomy c 0 with h0 | h0 | h0
    · have : c ≤ -1 := by omega
      nlinarith
    · exact h0
    · have : 1 ≤ c := by omega
      nlinarith
  subst hc0
  apply Fin.ext
  simp only [mul_zero] at hc
  omega

/-- A point within `1 / p` of a digit has norm at most `1`. -/
theorem padicVol_norm_le_one_of_digit {z : ℚ_[p]} (k : Fin p)
    (h : ‖z - ((k : ℕ) : ℚ_[p])‖ ≤ (p : ℝ)⁻¹) : ‖z‖ ≤ 1 := by
  have hp1 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_lt.le)
  have hk : ‖((k : ℕ) : ℚ_[p])‖ ≤ 1 := by
    simpa using Padic.norm_int_le_one (p := p) ((k : ℕ) : ℤ)
  calc ‖z‖ = ‖(z - ((k : ℕ) : ℚ_[p])) + ((k : ℕ) : ℚ_[p])‖ := by rw [sub_add_cancel]
    _ ≤ max ‖z - ((k : ℕ) : ℚ_[p])‖ ‖((k : ℕ) : ℚ_[p])‖ := Padic.nonarchimedean _ _
    _ ≤ 1 := max_le (h.trans hp1) hk

end Digits

/-! ## Boxes in coordinates and the scaling of Haar measure -/

section General

variable (p : ℕ) [hp : Fact p.Prime] (V : Type*) [NormedAddCommGroup V] [NormedSpace ℚ_[p] V]
  [FiniteDimensional ℚ_[p] V]

/-- Coordinates of `V` in the basis `Module.finBasis`, as a continuous linear equivalence. -/
noncomputable def padicVolCoord : V ≃L[ℚ_[p]] (Fin (Module.finrank ℚ_[p] V) → ℚ_[p]) :=
  (Module.finBasis ℚ_[p] V).equivFun.toContinuousLinearEquiv

/-- The box `{x | ∀ i, ‖x_i‖ ≤ r}` in the coordinates `padicVolCoord`. For `r = 1` it is the
`ℤ_p`-span of the basis. -/
noncomputable def padicVolBox (r : ℝ) : Set V := {x | ∀ i, ‖padicVolCoord p V x i‖ ≤ r}

variable {V}

/-- `c • box r = box (‖c‖ r)` for `c ≠ 0`. -/
theorem padicVolBox_smul {c : ℚ_[p]} (hc : c ≠ 0) (r : ℝ) :
    c • padicVolBox p V r = padicVolBox p V (‖c‖ * r) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc]
  simp only [padicVolBox, Set.mem_ofPred_eq, map_smul, Pi.smul_apply, smul_eq_mul, norm_mul,
    norm_inv]
  have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
  exact forall_congr' fun i => inv_mul_le_iff₀ hc'

/-- The box as the preimage of a product of closed balls. -/
theorem padicVolBox_eq_preimage (r : ℝ) :
    padicVolBox p V r =
      padicVolCoord p V ⁻¹' Set.univ.pi fun _ => Metric.closedBall (0 : ℚ_[p]) r := by
  ext x
  simp [padicVolBox]

/-- A box of positive radius is open (closed balls of `ℚ_p` are open). -/
theorem padicVolBox_isOpen {r : ℝ} (hr : 0 < r) : IsOpen (padicVolBox p V r) := by
  rw [padicVolBox_eq_preimage]
  exact (isOpen_set_pi Set.finite_univ fun _ _ =>
    IsUltrametricDist.isOpen_closedBall _ hr.ne').preimage (padicVolCoord p V).continuous

/-- A box is compact. -/
theorem padicVolBox_isCompact (r : ℝ) : IsCompact (padicVolBox p V r) := by
  rw [padicVolBox_eq_preimage]
  exact (padicVolCoord p V).toHomeomorph.isCompact_preimage.mpr
    (isCompact_univ_pi fun _ => isCompact_closedBall _ _)

variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]

omit [BorelSpace V] in
/-- A box of positive radius has positive Haar measure. -/
theorem padicVolBox_measure_ne_zero {r : ℝ} (hr : 0 < r) : μ (padicVolBox p V r) ≠ 0 :=
  (padicVolBox_isOpen p hr).measure_ne_zero μ ⟨0, by simp [padicVolBox, hr.le]⟩

omit [BorelSpace V] in
/-- A box has finite Haar measure. -/
theorem padicVolBox_measure_ne_top (r : ℝ) : μ (padicVolBox p V r) ≠ ⊤ :=
  (padicVolBox_isCompact p r).measure_lt_top.ne

/-- **The counting step.** The unit box is the disjoint union of the `p ^ d` translates
`k + p · box` (`k ∈ {0, …, p - 1} ^ d` in coordinates), so its measure is `p ^ d` times that of
`box (1 / p)`. -/
theorem padicVolBox_measure_one :
    μ (padicVolBox p V 1) =
      (p : ENNReal) ^ Module.finrank ℚ_[p] V * μ (padicVolBox p V (p : ℝ)⁻¹) := by
  let t : (Fin (Module.finrank ℚ_[p] V) → Fin p) → V := fun k =>
    -((padicVolCoord p V).symm fun i => (((k i : ℕ)) : ℚ_[p]))
  let T : (Fin (Module.finrank ℚ_[p] V) → Fin p) → Set V := fun k =>
    (fun x => t k + x) ⁻¹' padicVolBox p V (p : ℝ)⁻¹
  have hT : ∀ k x, x ∈ T k ↔
      ∀ i, ‖padicVolCoord p V x i - ((k i : ℕ) : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    intro k x
    simp only [T, t, Set.mem_preimage, padicVolBox, Set.mem_ofPred_eq, map_add, map_neg,
      ContinuousLinearEquiv.apply_symm_apply, Pi.add_apply, Pi.neg_apply]
    exact forall_congr' fun i => by rw [neg_add_eq_sub]
  have hU : padicVolBox p V 1 = ⋃ k, T k := by
    ext x
    simp only [Set.mem_iUnion, hT, padicVolBox, Set.mem_ofPred_eq]
    constructor
    · intro hx
      choose k hk using fun i => padicVol_exists_digit (hx i)
      exact ⟨k, hk⟩
    · rintro ⟨k, hk⟩ i
      exact padicVol_norm_le_one_of_digit (k i) (hk i)
  have hD : Pairwise (Function.onFun Disjoint T) := by
    intro k k' hkk'
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    rw [hT] at hx hx'
    exact hkk' (funext fun i => padicVol_digit_unique (hx i) (hx' i))
  have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.out.pos)
  have hM : ∀ k, MeasurableSet (T k) := fun k =>
    (padicVolBox_isOpen p hpos).measurableSet.preimage (measurable_const_add _)
  rw [hU, measure_iUnion hD hM]
  simp only [T, measure_preimage_add, tsum_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rfl

/-- A unit of `ℚ_p` acts on sets as its value. -/
theorem padicVol_units_smul_set {W : Type*} [AddCommGroup W] [Module ℚ_[p] W] (u : ℚ_[p]ˣ)
    (A : Set W) : u • A = (u : ℚ_[p]) • A := by
  ext x
  simp [Set.mem_smul_set, Units.smul_def]

include μ in
/-- The distributive Haar character of the unit `p` of `ℚ_p` on `V` is `(p ^ d)⁻¹`. -/
theorem padicVol_distribHaarChar_p :
    haveI : ProperSpace V := FiniteDimensional.proper ℚ_[p] V
    distribHaarChar V (Units.mk0 (p : ℚ_[p]) (by exact_mod_cast hp.out.ne_zero)) =
      ((p : NNReal) ^ Module.finrank ℚ_[p] V)⁻¹ := by
  have : ProperSpace V := FiniteDimensional.proper ℚ_[p] V
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ)
    (padicVolBox_measure_ne_zero p μ one_pos) (padicVolBox_measure_ne_top p μ 1)
  rw [padicVol_units_smul_set, Units.val_mk0, padicVolBox_smul p hp0, mul_one, Padic.norm_p,
    padicVolBox_measure_one p μ, ← mul_assoc]
  have hpd : ((p : ENNReal) ^ Module.finrank ℚ_[p] V) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hpd' : ((p : ENNReal) ^ Module.finrank ℚ_[p] V) ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  rw [ENNReal.coe_inv (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)), ENNReal.coe_pow,
    ENNReal.coe_natCast, ENNReal.inv_mul_cancel hpd hpd', one_mul]

/-- **Scaling of Haar measure by a scalar of `ℚ_p`.** For every additive Haar measure `μ` on a
`d`-dimensional normed `ℚ_p`-vector space, every `c ≠ 0` in `ℚ_p` and every set `A`,
`μ (c • A) = ‖c‖ ^ d · μ A`. -/
theorem padicVol_measure_smul {c : ℚ_[p]} (hc : c ≠ 0) (A : Set V) :
    μ (c • A) = ((‖c‖₊ ^ Module.finrank ℚ_[p] V : NNReal) : ENNReal) * μ A := by
  have : ProperSpace V := FiniteDimensional.proper ℚ_[p] V
  set d := Module.finrank ℚ_[p] V
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set P : ℚ_[p]ˣ := Units.mk0 (p : ℚ_[p]) hp0
  set n : ℤ := c.valuation
  have hnorm : ‖c‖ = ‖((p : ℚ_[p]) ^ n)‖ := by
    rw [Padic.norm_eq_zpow_neg_valuation hc, Padic.norm_p_zpow]
  have key : distribHaarChar V (Units.mk0 c hc) = ‖c‖₊ ^ d := by
    apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ)
      (padicVolBox_measure_ne_zero p μ one_pos) (padicVolBox_measure_ne_top p μ 1)
    have hbox : (Units.mk0 c hc) • padicVolBox p V 1 = (P ^ n) • padicVolBox p V 1 := by
      rw [padicVol_units_smul_set, padicVol_units_smul_set, Units.val_mk0, Units.val_zpow_eq_zpow_val,
        Units.val_mk0, padicVolBox_smul p hc, padicVolBox_smul p (zpow_ne_zero _ hp0), hnorm]
    rw [hbox, ← distribHaarChar_mul μ, map_zpow, padicVol_distribHaarChar_p p μ]
    congr 1
    apply ENNReal.coe_injective.eq_iff.mpr
    apply NNReal.eq
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    simp only [NNReal.coe_zpow, NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_natCast, coe_nnNorm]
    rw [hnorm, Padic.norm_p_zpow, ← zpow_natCast, ← zpow_natCast, inv_zpow', ← zpow_mul,
      ← zpow_mul]
    congr 1
    simp only [d]
    ring
  have h := distribHaarChar_mul μ (Units.mk0 c hc) A
  rw [padicVol_units_smul_set, Units.val_mk0, key] at h
  exact h.symm

end General

/-! ## The normalized log-volume -/

section MuLog

variable (p : ℕ) [hp : Fact p.Prime] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℚ_[p] V]
  [FiniteDimensional ℚ_[p] V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)

/-- **The normalized log-volume** `μ^log(A) = log (μ A / μ Λ) / d`, `d = dim_{ℚ_p} V`, normalized
at `Λ`: the normalization "by dividing by the degree" of IUT IV Proposition 1.4 (i), page 13.
Real valued, with Lean's `Real.log 0 = 0`; it is meaningful when `μ A` and `μ Λ` are positive
and finite. -/
noncomputable def padicMuLog (Λ A : Set V) : ℝ :=
  Real.log ((μ A).toReal / (μ Λ).toReal) / (Module.finrank ℚ_[p] V : ℝ)

omit [FiniteDimensional ℚ_[p] V] [BorelSpace V] in
/-- `μ^log(Λ) = 0`, the first normalizing value of IUT IV page 13. -/
theorem padicMuLog_self (Λ : Set V) : padicMuLog p μ Λ Λ = 0 := by
  unfold padicMuLog
  by_cases h : (μ Λ).toReal = 0
  · simp [h]
  · simp [div_self h]

/-- The `EReal` form `ENNReal.log ((μ A / μ Λ) ^ (1 / d))` of the normalized log-volume. It is
defined and monotone on all sets (`padicMuLogE_mono`), with `−∞` on null sets. -/
noncomputable def padicMuLogE (Λ A : Set V) : EReal :=
  ENNReal.log ((μ A / μ Λ) ^ ((Module.finrank ℚ_[p] V : ℝ)⁻¹))

omit [FiniteDimensional ℚ_[p] V] [BorelSpace V] in
/-- The `EReal` form is monotone on all sets. -/
theorem padicMuLogE_mono (Λ : Set V) : Monotone (padicMuLogE p μ Λ) := fun A B hAB =>
  ENNReal.log_monotone (ENNReal.rpow_le_rpow (ENNReal.div_le_div_right (measure_mono hAB) _)
    (by positivity))

omit [FiniteDimensional ℚ_[p] V] [BorelSpace V] in
/-- On sets of positive finite measure the `EReal` form is the real normalized log-volume. -/
theorem padicMuLogE_eq {Λ A : Set V} (hΛ0 : μ Λ ≠ 0) (hΛ : μ Λ ≠ ⊤) (hA0 : μ A ≠ 0)
    (hA : μ A ≠ ⊤) : padicMuLogE p μ Λ A = (padicMuLog p μ Λ A : EReal) := by
  unfold padicMuLogE padicMuLog
  have h0 : μ A / μ Λ ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hA0, hΛ⟩
  have h1 : μ A / μ Λ ≠ ⊤ := ENNReal.div_ne_top hA hΛ0
  rw [ENNReal.log_rpow, ENNReal.log_pos_real h0 h1, ENNReal.toReal_div, ← EReal.coe_mul,
    div_eq_inv_mul (Real.log _)]

variable [μ.IsAddHaarMeasure]

/-- The normalized log-volume does not depend on the Haar measure. -/
theorem padicMuLog_haar_indep (μ' : Measure V) [μ'.IsAddHaarMeasure] :
    padicMuLog p μ' = padicMuLog p μ := by
  have : ProperSpace V := FiniteDimensional.proper ℚ_[p] V
  have hμ' := isAddLeftInvariant_eq_smul μ' μ
  set c := addHaarScalarFactor μ' μ
  have hc : (c : ℝ) ≠ 0 := by
    intro h0
    have h0' : c = 0 := NNReal.coe_eq_zero.mp h0
    have := (isOpen_univ.measure_ne_zero μ' Set.univ_nonempty)
    rw [hμ', h0', zero_smul] at this
    exact this rfl
  funext Λ A
  unfold padicMuLog
  rw [hμ']
  simp only [FunLike.coe_smul, Pi.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.coe_toReal]
  rw [mul_div_mul_left _ _ hc]

/-- **Scaling by a scalar of `ℚ_p`**: `μ^log(c • A) = μ^log(A) + log ‖c‖` for `c ≠ 0`, when `A`
and `Λ` have positive finite measure and `V ≠ 0`. -/
theorem padicMuLog_smul (hd : 0 < Module.finrank ℚ_[p] V) {Λ A : Set V} (hΛ0 : μ Λ ≠ 0)
    (hΛ : μ Λ ≠ ⊤) (hA0 : μ A ≠ 0) (hA : μ A ≠ ⊤) {c : ℚ_[p]} (hc : c ≠ 0) :
    padicMuLog p μ Λ (c • A) = padicMuLog p μ Λ A + Real.log ‖c‖ := by
  unfold padicMuLog
  rw [padicVol_measure_smul p μ hc A, ENNReal.toReal_mul]
  simp only [ENNReal.coe_toReal, NNReal.coe_pow, coe_nnNorm]
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hApos := ENNReal.toReal_pos hA0 hA
  have hΛpos := ENNReal.toReal_pos hΛ0 hΛ
  have hd' : (Module.finrank ℚ_[p] V : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [mul_div_assoc, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  field_simp
  ring

/-- `μ^log(p ^ n • A) = μ^log(A) − n log p`: with `A = Λ` this is the second normalizing value
`μ^log(p · Λ) = −log p` of IUT IV page 13, and the packet-normalization of IUT III page 115. -/
theorem padicMuLog_p_zpow_smul (hd : 0 < Module.finrank ℚ_[p] V) {Λ A : Set V} (hΛ0 : μ Λ ≠ 0)
    (hΛ : μ Λ ≠ ⊤) (hA0 : μ A ≠ 0) (hA : μ A ≠ ⊤) (n : ℤ) :
    padicMuLog p μ Λ (((p : ℚ_[p]) ^ n) • A) = padicMuLog p μ Λ A - n * Real.log p := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [padicMuLog_smul p μ hd hΛ0 hΛ hA0 hA (zpow_ne_zero _ hp0), Padic.norm_p_zpow,
    Real.log_zpow]
  push_cast
  ring

omit [FiniteDimensional ℚ_[p] V] in
/-- **Translation invariance**: `μ^log(x + A) = μ^log(A)`. -/
theorem padicMuLog_vadd (Λ A : Set V) (x : V) :
    padicMuLog p μ Λ (x +ᵥ A) = padicMuLog p μ Λ A := by
  unfold padicMuLog
  rw [measure_vadd]

omit [FiniteDimensional ℚ_[p] V] [BorelSpace V] [μ.IsAddHaarMeasure] in
/-- **Monotonicity** on sets of positive finite measure. -/
theorem padicMuLog_mono {Λ A B : Set V} (hAB : A ⊆ B) (hΛ0 : μ Λ ≠ 0) (hΛ : μ Λ ≠ ⊤)
    (hA0 : μ A ≠ 0) (hB : μ B ≠ ⊤) : padicMuLog p μ Λ A ≤ padicMuLog p μ Λ B := by
  unfold padicMuLog
  have hApos := ENNReal.toReal_pos hA0 (ne_top_of_le_ne_top hB (measure_mono hAB))
  have hΛpos := ENNReal.toReal_pos hΛ0 hΛ
  have hle : (μ A).toReal ≤ (μ B).toReal := ENNReal.toReal_mono hB (measure_mono hAB)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hle hΛpos.le)

/-- **Invariance under a change of coordinates**: for a continuous linear automorphism `h` of
`V`, `μ^log(h Λ, h A) = μ^log(Λ, A)`. -/
theorem padicMuLog_image_equiv (h : V ≃L[ℚ_[p]] V) (Λ A : Set V) :
    padicMuLog p μ (h '' Λ) (h '' A) = padicMuLog p μ Λ A := by
  have hH := h.symm.isAddHaarMeasure_map μ
  have key : ∀ S : Set V, μ (h '' S) = (Measure.map h.symm μ) S := by
    intro S
    rw [show (Measure.map h.symm μ) S =
        (Measure.map (h.symm.toHomeomorph.toMeasurableEquiv) μ) S from rfl,
      MeasurableEquiv.map_apply]
    congr 1
    ext x
    simp [ContinuousLinearEquiv.image_eq_preimage_symm]
  have := padicMuLog_haar_indep p μ (Measure.map h.symm μ)
  unfold padicMuLog at this ⊢
  rw [key, key]
  exact congrFun (congrFun this Λ) A

/-- **The interface of `IUT.PaperIII.Corollary312.Comparison`** with the region log-volume
`padicMuLogE p μ Λ` of an actual Haar measure. The hull data, the q-pilot region and the
possible images are inputs, as in `RegionComparison`; the theorems there (for example
`RegionComparison.logVolumeComparison_of_containment`) apply to it. -/
noncomputable def padicRegionComparison {ι : Type*} (Λ : Set V) (hullDomain hulls : Set (Set V))
    (hull : Set V → Set V) (isHullMap : IUT.PaperIII.Remark3_9_5.IsHullMap hullDomain hulls hull)
    (qPilot : Set V) (image : ι → Set V) (union_mem : (⋃ i, image i) ∈ hullDomain) :
    IUT.PaperIII.Corollary312.RegionComparison V ι where
  hullDomain := hullDomain
  hulls := hulls
  hull := hull
  isHullMap := isHullMap
  logVol := padicMuLogE p μ Λ
  logVol_mono _ _ h _ := padicMuLogE_mono p μ Λ h
  qPilot := qPilot
  image := image
  union_mem := union_mem

end MuLog

/-! ## Elementary facts in a normed field -/

section NormedFieldFacts

variable {K : Type*} [NormedField K]

/-- `x • {‖y‖ ≤ r} = {‖y‖ ≤ ‖x‖ r}` for `x ≠ 0`. -/
theorem padicVol_smul_ball {x : K} (hx : x ≠ 0) (r : ℝ) :
    x • {y : K | ‖y‖ ≤ r} = {y : K | ‖y‖ ≤ ‖x‖ * r} := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hx]
  simp only [Set.mem_ofPred_eq, smul_eq_mul, norm_mul, norm_inv]
  exact inv_mul_le_iff₀ (norm_pos_iff.mpr hx)

/-- A unit of `K` acts on sets as its value. -/
theorem padicVol_field_units_smul_set (u : Kˣ) (A : Set K) : u • A = (u : K) • A := by
  ext x
  simp [Set.mem_smul_set, Units.smul_def]

/-- `log ‖π‖ = −(1 / e) log p` for `‖π‖ ^ e = 1 / p`. -/
theorem padicVol_log_uniformizer (p : ℕ) {π : K} {e : ℕ} (he : 1 ≤ e) (hπ : ‖π‖ ^ e = (p : ℝ)⁻¹) :
    Real.log ‖π‖ = -(1 / (e : ℝ)) * Real.log p := by
  have h := congrArg Real.log hπ
  rw [Real.log_pow, Real.log_inv] at h
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
  field_simp
  linarith

/-- For a uniformizer `π` and `t e = k ∈ ℤ`: `p ^ (−t) = ‖π‖ ^ k`. -/
theorem padicVol_rpow_eq_uniformizer (p : ℕ) [hp : Fact p.Prime] {π : K} {e : ℕ} (he : 1 ≤ e) (hπ : ‖π‖ ^ e = (p : ℝ)⁻¹)
    {t : ℝ} {k : ℤ} (htk : t * e = k) : (p : ℝ) ^ (-t) = ‖π‖ ^ k := by
  have hp1 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have he0 : e ≠ 0 := by omega
  have hπn : ‖π‖ = (p : ℝ) ^ (-(1 / (e : ℝ))) := by
    have h := Real.pow_rpow_inv_natCast (norm_nonneg π) he0
    rw [hπ, Real.inv_rpow hp1.le, ← Real.rpow_neg hp1.le] at h
    rw [← h]; congr 1; field_simp
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he0
  rw [hπn, ← Real.rpow_intCast, ← Real.rpow_mul hp1.le]
  congr 1
  rw [← htk]
  field_simp

/-- The integer `e · a` for the constant `a = Proposition1_2.a p e` of IUT IV page 10. -/
noncomputable def padicVolAInt (p e : ℕ) : ℤ :=
  if p = 2 then 2 * e else ⌈(e : ℝ) / ((p : ℝ) - 2)⌉

/-- The integer `−e · b` for the constant `b = Proposition1_2.b p e` of IUT IV page 10. -/
noncomputable def padicVolBInt (p e : ℕ) : ℤ :=
  1 - e * ⌊Real.log ((p : ℝ) * e / ((p : ℝ) - 1)) / Real.log p⌋

/-- `a · e = padicVolAInt p e`, so `a ∈ (1 / e) ℤ`. -/
theorem padicVolAInt_spec (p : ℕ) {e : ℕ} (he : 1 ≤ e) :
    IUT.PaperIV.Proposition1_2.a p e * e = padicVolAInt p e := by
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
  unfold IUT.PaperIV.Proposition1_2.a padicVolAInt
  split_ifs <;> push_cast <;> field_simp

/-- `−b · e = padicVolBInt p e`, so `b ∈ (1 / e) ℤ`. -/
theorem padicVolBInt_spec (p : ℕ) {e : ℕ} (he : 1 ≤ e) :
    -IUT.PaperIV.Proposition1_2.b p e * e = padicVolBInt p e := by
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
  unfold IUT.PaperIV.Proposition1_2.b padicVolBInt
  push_cast
  field_simp
  ring

end NormedFieldFacts

/-! ## A finite extension of `ℚ_p` -/

section Field

variable (p : ℕ) [hp : Fact p.Prime] {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K]

include hp

/-- The closed unit ball `R` of `K` is open and compact. -/
theorem padicVol_unitBall_isOpen_isCompact :
    IsOpen {y : K | ‖y‖ ≤ 1} ∧ IsCompact {y : K | ‖y‖ ≤ 1} := by
  have : IsUltrametricDist K := IUT.PaperIV.LocalFields.extLog_isUltrametricDist p
  have : ProperSpace K := FiniteDimensional.proper ℚ_[p] K
  have e : {y : K | ‖y‖ ≤ 1} = Metric.closedBall 0 1 := by
    ext y; simp
  rw [e]
  exact ⟨IsUltrametricDist.isOpen_closedBall _ one_ne_zero, isCompact_closedBall _ _⟩

variable [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]

omit [BorelSpace K] in
/-- The closed unit ball has positive Haar measure. -/
theorem padicVol_unitBall_ne_zero : μ {y : K | ‖y‖ ≤ 1} ≠ 0 :=
  (padicVol_unitBall_isOpen_isCompact p).1.measure_ne_zero μ ⟨0, by simp⟩

omit [BorelSpace K] in
/-- The closed unit ball has finite Haar measure. -/
theorem padicVol_unitBall_ne_top : μ {y : K | ‖y‖ ≤ 1} ≠ ⊤ :=
  (padicVol_unitBall_isOpen_isCompact p).2.measure_lt_top.ne

omit [FiniteDimensional ℚ_[p] K] [BorelSpace K] [μ.IsAddHaarMeasure] in
/-- **IUT IV Proposition 1.4 (i), first normalizing value** (page 13), for `K` with `R` the closed
unit ball: `μ^log(R) = 0`. -/
theorem padicMuLog_unitBall : padicMuLog p μ {y : K | ‖y‖ ≤ 1} {y : K | ‖y‖ ≤ 1} = 0 :=
  padicMuLog_self p μ _

/-- **IUT IV Proposition 1.4 (i), second normalizing value** (page 13): `μ^log(p · R) = −log p`
for the normalization by the degree `d = [K : ℚ_p]`. -/
theorem padicMuLog_p_smul_unitBall :
    padicMuLog p μ {y : K | ‖y‖ ≤ 1} ((p : ℚ_[p]) • {y : K | ‖y‖ ≤ 1}) = -Real.log p := by
  have hd : 0 < Module.finrank ℚ_[p] K := Module.finrank_pos
  have h := padicMuLog_p_zpow_smul p μ hd (padicVol_unitBall_ne_zero p μ)
    (padicVol_unitBall_ne_top p μ) (padicVol_unitBall_ne_zero p μ) (padicVol_unitBall_ne_top p μ) 1
  rw [zpow_one, padicMuLog_self] at h
  rw [h]; simp

/-- **Scaling of Haar measure by an element of `K`.** If `x ≠ 0` and `‖x‖ ^ m = p ^ (−n)` for
some `m ≥ 1` and `n ∈ ℤ` (true for every nonzero element of a finite extension of `ℚ_p`, whose
value group is `p ^ (ℤ / e)`; here a hypothesis on `x`), then `μ (x • A) = ‖x‖ ^ d · μ A`,
`d = [K : ℚ_p]`. -/
theorem padicVol_field_measure_smul {x : K} (hx : x ≠ 0) {m : ℕ} (hm : 0 < m) {n : ℤ}
    (hxn : ‖x‖ ^ m = (p : ℝ) ^ (-n)) (A : Set K) :
    μ (x • A) = ((‖x‖₊ ^ Module.finrank ℚ_[p] K : NNReal) : ENNReal) * μ A := by
  have : ProperSpace K := FiniteDimensional.proper ℚ_[p] K
  set d := Module.finrank ℚ_[p] K
  set B : Set K := {y : K | ‖y‖ ≤ 1}
  have hB0 := padicVol_unitBall_ne_zero p μ
  have hB1 := padicVol_unitBall_ne_top p μ
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpK : (algebraMap ℚ_[p] K p) ≠ 0 := (map_ne_zero _).mpr hp0
  set P : Kˣ := Units.mk0 _ hpK
  -- the character on units of norm one
  have hunit : ∀ u : Kˣ, ‖(u : K)‖ = 1 → distribHaarChar K u = 1 := by
    intro u hu
    apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) hB0 hB1
    rw [padicVol_field_units_smul_set, padicVol_smul_ball u.ne_zero, hu, one_mul]
    simp
  -- the character of `p`
  have hP : distribHaarChar K P = ‖(p : ℚ_[p])‖₊ ^ d := by
    apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) hB0 hB1
    rw [padicVol_field_units_smul_set, Units.val_mk0]
    have : (algebraMap ℚ_[p] K p) • B = (p : ℚ_[p]) • B := by
      ext y; simp only [Set.mem_smul_set, algebraMap_smul]
    rw [this, padicVol_measure_smul p μ hp0]
  -- the character of `x`
  set X : Kˣ := Units.mk0 x hx
  have hnormp : ‖algebraMap ℚ_[p] K ((p : ℚ_[p]) ^ n)‖ = (p : ℝ) ^ (-n) := by
    rw [norm_algebraMap', Padic.norm_p_zpow]
  set U : Kˣ := X ^ m * (P ^ n)⁻¹
  have hU : ‖(U : K)‖ = 1 := by
    have hpn : ((P ^ n : Kˣ) : K) = algebraMap ℚ_[p] K ((p : ℚ_[p]) ^ n) := by
      rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, map_zpow₀]
    have hpos : (0 : ℝ) < (p : ℝ) ^ (-n) := zpow_pos (by exact_mod_cast hp.out.pos) _
    rw [Units.val_mul, Units.val_inv_eq_inv_val, hpn, norm_mul, norm_inv, hnormp,
      Units.val_pow_eq_pow_val, Units.val_mk0, norm_pow, hxn, mul_inv_cancel₀ hpos.ne']
  have hXm : distribHaarChar K X ^ m = (‖(p : ℚ_[p])‖₊ ^ d) ^ n := by
    have hXU : X ^ m = P ^ n * U := by simp [U]
    rw [← map_pow, hXU, map_mul, hunit U hU, mul_one, map_zpow, hP]
  have key : distribHaarChar K X = ‖x‖₊ ^ d := by
    apply NNReal.eq
    have h1 := congrArg (fun t : NNReal => (t : ℝ)) hXm
    simp only [NNReal.coe_pow, NNReal.coe_zpow, coe_nnNorm, Padic.norm_p] at h1
    have h3 : (((p : ℝ)⁻¹) ^ d) ^ n = ((p : ℝ) ^ (-n)) ^ d := by
      rw [inv_pow, inv_zpow, zpow_neg, inv_pow, ← zpow_natCast ((p : ℝ)) d,
        ← zpow_natCast ((p : ℝ) ^ n) d, ← zpow_mul, ← zpow_mul, mul_comm]
    have h2 : (‖x‖ ^ d) ^ m = (((p : ℝ)⁻¹) ^ d) ^ n := by
      rw [h3, ← pow_mul, mul_comm, pow_mul, hxn]
    simp only [NNReal.coe_pow, coe_nnNorm]
    exact (pow_left_inj₀ (NNReal.coe_nonneg _) (by positivity) hm.ne').mp (h1.trans h2.symm)
  have h := distribHaarChar_mul μ X A
  rw [padicVol_field_units_smul_set, Units.val_mk0, key] at h
  exact h.symm

/-- `μ^log(x • A) = μ^log(A) + log ‖x‖` for `x ∈ K^×` with `‖x‖ ^ m = p ^ (−n)`, `m ≥ 1`, when
`A` has positive finite measure; normalized at the unit ball. -/
theorem padicMuLog_field_smul {x : K} (hx : x ≠ 0) {m : ℕ} (hm : 0 < m) {n : ℤ}
    (hxn : ‖x‖ ^ m = (p : ℝ) ^ (-n)) {A : Set K} (hA0 : μ A ≠ 0) (hA : μ A ≠ ⊤) :
    padicMuLog p μ {y : K | ‖y‖ ≤ 1} (x • A) =
      padicMuLog p μ {y : K | ‖y‖ ≤ 1} A + Real.log ‖x‖ := by
  unfold padicMuLog
  rw [padicVol_field_measure_smul p μ hx hm hxn A, ENNReal.toReal_mul]
  simp only [ENNReal.coe_toReal, NNReal.coe_pow, coe_nnNorm]
  have hxn' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hApos := ENNReal.toReal_pos hA0 hA
  have hBpos := ENNReal.toReal_pos (padicVol_unitBall_ne_zero p μ)
    (padicVol_unitBall_ne_top p μ)
  have hd : (Module.finrank ℚ_[p] K : ℝ) ≠ 0 := by
    have : 0 < Module.finrank ℚ_[p] K := Module.finrank_pos
    exact_mod_cast this.ne'
  rw [mul_div_assoc, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  field_simp
  ring

/-- **Balls of radius `‖π‖ ^ k`**: for a uniformizer `π` (`‖π‖ ^ e = 1 / p`, `e ≥ 1`) and
`k ∈ ℤ`, the ball `{‖y‖ ≤ ‖π‖ ^ k}`, that is `p ^ (k / e) · R`, has normalized log-volume
`−(k / e) log p`. -/
theorem padicMuLog_ball_uniformizer {π : K} {e : ℕ} (he : 1 ≤ e) (hπ : ‖π‖ ^ e = (p : ℝ)⁻¹)
    (k : ℤ) :
    padicMuLog p μ {y : K | ‖y‖ ≤ 1} {y : K | ‖y‖ ≤ ‖π‖ ^ k} = -((k : ℝ) / e) * Real.log p := by
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [norm_zero, zero_pow (by omega)] at hπ
    exact absurd hπ.symm (inv_ne_zero (by exact_mod_cast hp.out.ne_zero))
  have hball : {y : K | ‖y‖ ≤ ‖π‖ ^ k} = (π ^ k) • {y : K | ‖y‖ ≤ 1} := by
    rw [padicVol_smul_ball (zpow_ne_zero _ hπ0), mul_one, norm_zpow]
  have hpow : ‖π ^ k‖ ^ e = (p : ℝ) ^ (-k) := by
    rw [norm_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hπ, inv_zpow',
      zpow_neg]
  rw [hball, padicMuLog_field_smul p μ (zpow_ne_zero _ hπ0) (by omega : 0 < e) hpow
    (padicVol_unitBall_ne_zero p μ) (padicVol_unitBall_ne_top p μ), padicMuLog_self, norm_zpow,
    Real.log_zpow, padicVol_log_uniformizer p he hπ]
  ring

/-- **Bounds for `μ^log(log_p(R^×))` from IUT IV Proposition 1.2 (i)** (pages 10 and 11): with
`R` the closed unit ball, `R^×` the unit sphere, `log_p` the function `extLogUnit` of
`Logarithm.lean`, `e ≥ 1` with `‖x‖ ^ e ≤ 1 / p` on the open unit disc (`hval`) and a
uniformizer `π` (`‖π‖ ^ e = 1 / p`):
`−a · log p ≤ μ^log(log_p(R^×)) ≤ b · log p`, with `a`, `b` the constants of page 10. These are
consequences of the inclusions `p ^ a · R ⊆ log_p(R^×) ⊆ p ^ (−b) · R`; they are not the exact
value of Proposition 1.4 (ii). -/
theorem padicMuLog_logUnit_bounds {e : ℕ} (he : 1 ≤ e)
    (hval : ∀ x : K, ‖x‖ < 1 → ‖x‖ ^ e ≤ (p : ℝ)⁻¹) {π : K} (hπ : ‖π‖ ^ e = (p : ℝ)⁻¹) :
    -IUT.PaperIV.Proposition1_2.a p e * Real.log p ≤
        padicMuLog p μ {y : K | ‖y‖ ≤ 1}
          (IUT.PaperIV.LocalFields.extLogUnit '' {u : K | ‖u‖ = 1}) ∧
      padicMuLog p μ {y : K | ‖y‖ ≤ 1}
          (IUT.PaperIV.LocalFields.extLogUnit '' {u : K | ‖u‖ = 1}) ≤
        IUT.PaperIV.Proposition1_2.b p e * Real.log p := by
  have : CompleteSpace K := FiniteDimensional.completeSpace ℚ_[p] K
  have : ProperSpace K := FiniteDimensional.proper ℚ_[p] K
  obtain ⟨hlo, hhi⟩ := IUT.PaperIV.LocalFields.extLogUnit_image_bounds p he hval
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
  have hA : (p : ℝ) ^ (-IUT.PaperIV.Proposition1_2.a p e) = ‖π‖ ^ padicVolAInt p e :=
    padicVol_rpow_eq_uniformizer p he hπ (padicVolAInt_spec p he)
  have hB : (p : ℝ) ^ (IUT.PaperIV.Proposition1_2.b p e) = ‖π‖ ^ padicVolBInt p e := by
    rw [← padicVol_rpow_eq_uniformizer p he hπ (padicVolBInt_spec p he), neg_neg]
  rw [hA] at hlo
  rw [hB] at hhi
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [norm_zero, zero_pow (by omega)] at hπ
    exact absurd hπ.symm (inv_ne_zero (by exact_mod_cast hp.out.ne_zero))
  -- the two balls have positive finite measure
  have hball : ∀ k : ℤ, {y : K | ‖y‖ ≤ ‖π‖ ^ k} = (π ^ k) • {y : K | ‖y‖ ≤ 1} := fun k => by
    rw [padicVol_smul_ball (zpow_ne_zero _ hπ0), mul_one, norm_zpow]
  have hpow : ∀ k : ℤ, ‖π ^ k‖ ^ e = (p : ℝ) ^ (-k) := fun k => by
    rw [norm_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hπ, inv_zpow',
      zpow_neg]
  have hfin : ∀ k : ℤ, μ {y : K | ‖y‖ ≤ ‖π‖ ^ k} ≠ 0 ∧ μ {y : K | ‖y‖ ≤ ‖π‖ ^ k} ≠ ⊤ :=
    fun k => by
      rw [hball k, padicVol_field_measure_smul p μ (zpow_ne_zero _ hπ0) (by omega : 0 < e)
        (hpow k)]
      have hc : ((‖π ^ k‖₊ ^ Module.finrank ℚ_[p] K : NNReal) : ENNReal) ≠ 0 := by
        have : ‖π ^ k‖₊ ≠ 0 := nnNorm_ne_zero_iff.mpr (zpow_ne_zero _ hπ0)
        exact_mod_cast pow_ne_zero _ this
      exact ⟨mul_ne_zero hc (padicVol_unitBall_ne_zero p μ),
        ENNReal.mul_ne_top ENNReal.coe_ne_top (padicVol_unitBall_ne_top p μ)⟩
  have hB0 := padicVol_unitBall_ne_zero p μ
  have hB1 := padicVol_unitBall_ne_top p μ
  constructor
  · have h := padicMuLog_mono p μ hlo hB0 hB1 (hfin _).1
      (ne_top_of_le_ne_top (hfin (padicVolBInt p e)).2 (measure_mono hhi))
    rw [padicMuLog_ball_uniformizer p μ he hπ, ← padicVolAInt_spec p he] at h
    convert h using 1
    field_simp
  · have h := padicMuLog_mono p μ hhi hB0 hB1
      (fun h0 => (hfin (padicVolAInt p e)).1 (measure_mono_null hlo h0)) (hfin _).2
    rw [padicMuLog_ball_uniformizer p μ he hπ, ← padicVolBInt_spec p he] at h
    convert h using 1
    field_simp

/-- **Bounds for the log-shell** `I = (p*)⁻¹ · log_p(R^×)` of IUT III Definition 1.1 (page 24),
as `extLogShell` of `Logarithm.lean`: `μ^log(I) = μ^log(log_p(R^×)) + log p*`, hence
`−a · log p + log p* ≤ μ^log(I) ≤ b · log p + log p*`. -/
theorem padicMuLog_logShell_bounds {e : ℕ} (he : 1 ≤ e)
    (hval : ∀ x : K, ‖x‖ < 1 → ‖x‖ ^ e ≤ (p : ℝ)⁻¹) {π : K} (hπ : ‖π‖ ^ e = (p : ℝ)⁻¹) :
    padicMuLog p μ {y : K | ‖y‖ ≤ 1} (IUT.PaperIV.LocalFields.extLogShell p K) =
        padicMuLog p μ {y : K | ‖y‖ ≤ 1}
          (IUT.PaperIV.LocalFields.extLogUnit '' {u : K | ‖u‖ = 1}) +
          Real.log (IUT.Prerequisites.PadicLog.padicLogPStar p) ∧
      -IUT.PaperIV.Proposition1_2.a p e * Real.log p +
          Real.log (IUT.Prerequisites.PadicLog.padicLogPStar p) ≤
        padicMuLog p μ {y : K | ‖y‖ ≤ 1} (IUT.PaperIV.LocalFields.extLogShell p K) ∧
      padicMuLog p μ {y : K | ‖y‖ ≤ 1} (IUT.PaperIV.LocalFields.extLogShell p K) ≤
        IUT.PaperIV.Proposition1_2.b p e * Real.log p +
          Real.log (IUT.Prerequisites.PadicLog.padicLogPStar p) := by
  have : CompleteSpace K := FiniteDimensional.completeSpace ℚ_[p] K
  have : ProperSpace K := FiniteDimensional.proper ℚ_[p] K
  set S := IUT.PaperIV.LocalFields.extLogUnit '' {u : K | ‖u‖ = 1}
  set s : ℕ := IUT.Prerequisites.PadicLog.padicLogPStar p
  have hs0 : (s : ℚ_[p]) ≠ 0 := by
    have : 0 < s := lt_of_lt_of_le hp.out.pos IUT.Prerequisites.PadicLog.padicLog_pStar_ge
    exact_mod_cast this.ne'
  have hshell : IUT.PaperIV.LocalFields.extLogShell p K = ((s : ℚ_[p])⁻¹) • S := by
    unfold IUT.PaperIV.LocalFields.extLogShell
    ext y
    simp only [Set.mem_image, Set.mem_smul_set]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, by rw [Algebra.smul_def, map_inv₀, map_natCast]⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, by rw [Algebra.smul_def, map_inv₀, map_natCast]⟩
  -- `S` has positive finite measure, from the bounds of Proposition 1.2 (i)
  obtain ⟨hlo, hhi⟩ := IUT.PaperIV.LocalFields.extLogUnit_image_bounds p he hval
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [norm_zero, zero_pow (by omega)] at hπ
    exact absurd hπ.symm (inv_ne_zero (by exact_mod_cast hp.out.ne_zero))
  have hpow : ∀ k : ℤ, ‖π ^ k‖ ^ e = (p : ℝ) ^ (-k) := fun k => by
    rw [norm_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hπ, inv_zpow',
      zpow_neg]
  have hball : ∀ r : ℝ, (∃ k : ℤ, r = ‖π‖ ^ k) →
      μ {y : K | ‖y‖ ≤ r} ≠ 0 ∧ μ {y : K | ‖y‖ ≤ r} ≠ ⊤ := by
    rintro r ⟨k, rfl⟩
    have hb : {y : K | ‖y‖ ≤ ‖π‖ ^ k} = (π ^ k) • {y : K | ‖y‖ ≤ 1} := by
      rw [padicVol_smul_ball (zpow_ne_zero _ hπ0), mul_one, norm_zpow]
    rw [hb, padicVol_field_measure_smul p μ (zpow_ne_zero _ hπ0) (by omega : 0 < e) (hpow k)]
    have hc : ((‖π ^ k‖₊ ^ Module.finrank ℚ_[p] K : NNReal) : ENNReal) ≠ 0 := by
      have : ‖π ^ k‖₊ ≠ 0 := nnNorm_ne_zero_iff.mpr (zpow_ne_zero _ hπ0)
      exact_mod_cast pow_ne_zero _ this
    exact ⟨mul_ne_zero hc (padicVol_unitBall_ne_zero p μ),
      ENNReal.mul_ne_top ENNReal.coe_ne_top (padicVol_unitBall_ne_top p μ)⟩
  have hlo' := hball _ ⟨_, padicVol_rpow_eq_uniformizer p he hπ (padicVolAInt_spec p he)⟩
  have hhi' := hball (p ^ (IUT.PaperIV.Proposition1_2.b p e))
    ⟨_, by rw [← padicVol_rpow_eq_uniformizer p he hπ (padicVolBInt_spec p he), neg_neg]⟩
  have hS0 : μ S ≠ 0 := fun h0 => hlo'.1 (measure_mono_null hlo h0)
  have hS1 : μ S ≠ ⊤ := ne_top_of_le_ne_top hhi'.2 (measure_mono hhi)
  have hd : 0 < Module.finrank ℚ_[p] K := Module.finrank_pos
  have heq : padicMuLog p μ {y : K | ‖y‖ ≤ 1} (IUT.PaperIV.LocalFields.extLogShell p K) =
      padicMuLog p μ {y : K | ‖y‖ ≤ 1} S + Real.log s := by
    rw [hshell, padicMuLog_smul p μ hd (padicVol_unitBall_ne_zero p μ)
      (padicVol_unitBall_ne_top p μ) hS0 hS1 (inv_ne_zero hs0), norm_inv,
      IUT.Prerequisites.PadicLog.padicLog_norm_pStar, inv_inv]
  obtain ⟨h1, h2⟩ := padicMuLog_logUnit_bounds p μ he hval hπ
  exact ⟨heq, by rw [heq]; linarith, by rw [heq]; linarith⟩

end Field

/-! ## Tensor packets -/

section Packet

variable (p : ℕ) [hp : Fact p.Prime]

/-- The packet log-volume on a finite-dimensional `ℚ_p`-vector space `W` with no topology (for
example a tensor product `K₁ ⊗[ℚ_p] K₂`): the normalized log-volume of the images in the
coordinates of `Module.finBasis`, for a Haar measure `μ` on the coordinate space `ℚ_p ^ D`,
`D = dim W`, normalized at `Λ` and divided by `D`. -/
noncomputable def padicPacketMuLog (W : Type*) [AddCommGroup W] [Module ℚ_[p] W]
    [FiniteDimensional ℚ_[p] W] [MeasurableSpace (Fin (Module.finrank ℚ_[p] W) → ℚ_[p])]
    (μ : Measure (Fin (Module.finrank ℚ_[p] W) → ℚ_[p])) (Λ A : Set W) : ℝ :=
  padicMuLog p μ ((Module.finBasis ℚ_[p] W).equivFun '' Λ)
    ((Module.finBasis ℚ_[p] W).equivFun '' A)

/-- Linear equivalences commute with scalar multiplication of sets. -/
theorem padicVol_image_smul {W U : Type*} [AddCommGroup W] [Module ℚ_[p] W] [AddCommGroup U]
    [Module ℚ_[p] U] (f : W ≃ₗ[ℚ_[p]] U)
    (c : ℚ_[p]) (A : Set W) : f '' (c • A) = c • (f '' A) := by
  ext y
  simp only [Set.mem_smul_set, Set.mem_image]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨f a, ⟨a, ha, rfl⟩, (map_smul f c a).symm⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨c • a, ⟨a, ha, rfl⟩, map_smul f c a⟩

variable {W : Type*} [AddCommGroup W] [Module ℚ_[p] W] [FiniteDimensional ℚ_[p] W]
  [MeasurableSpace (Fin (Module.finrank ℚ_[p] W) → ℚ_[p])]
  [BorelSpace (Fin (Module.finrank ℚ_[p] W) → ℚ_[p])]
  (μ : Measure (Fin (Module.finrank ℚ_[p] W) → ℚ_[p])) [μ.IsAddHaarMeasure]

/-- **Independence of the coordinates**: any linear coordinates `g : W ≃ ℚ_p ^ D` give the same
packet log-volume. -/
theorem padicPacketMuLog_coord_indep
    (g : W ≃ₗ[ℚ_[p]] (Fin (Module.finrank ℚ_[p] W) → ℚ_[p])) (Λ A : Set W) :
    padicMuLog p μ (g '' Λ) (g '' A) = padicPacketMuLog p W μ Λ A := by
  set f := (Module.finBasis ℚ_[p] W).equivFun
  set h : (Fin (Module.finrank ℚ_[p] W) → ℚ_[p]) ≃L[ℚ_[p]]
      (Fin (Module.finrank ℚ_[p] W) → ℚ_[p]) := (f.symm.trans g).toContinuousLinearEquiv
  have hS : ∀ S : Set W, g '' S = h '' (f '' S) := by
    intro S
    rw [Set.image_image]
    congr 1
    funext x
    simp [h]
  rw [hS, hS, padicMuLog_image_equiv]
  rfl

omit [BorelSpace (Fin (Module.finrank ℚ_[p] W) → ℚ_[p])] [μ.IsAddHaarMeasure] in
/-- `μ^log(Λ) = 0` for the packet log-volume. -/
theorem padicPacketMuLog_self (Λ : Set W) : padicPacketMuLog p W μ Λ Λ = 0 :=
  padicMuLog_self p μ _

/-- **The scaling law on a packet**: `μ^log(p ^ n • A) = μ^log(A) − n log p` when the images of
`Λ` and `A` have positive finite measure. With `A = Λ = (R_E)^∼` and `n = 1` it would give the
normalization `μ^log(p · (R_E)^∼) = −log(p)` of IUT IV page 13, but that `(R_E)^∼`
(`padicPacketNormalization`) has positive finite measure is not proved here. -/
theorem padicPacketMuLog_p_zpow_smul (hD : 0 < Module.finrank ℚ_[p] W) {Λ A : Set W}
    (hΛ0 : μ ((Module.finBasis ℚ_[p] W).equivFun '' Λ) ≠ 0)
    (hΛ : μ ((Module.finBasis ℚ_[p] W).equivFun '' Λ) ≠ ⊤)
    (hA0 : μ ((Module.finBasis ℚ_[p] W).equivFun '' A) ≠ 0)
    (hA : μ ((Module.finBasis ℚ_[p] W).equivFun '' A) ≠ ⊤) (n : ℤ) :
    padicPacketMuLog p W μ Λ (((p : ℚ_[p]) ^ n) • A) =
      padicPacketMuLog p W μ Λ A - n * Real.log p := by
  unfold padicPacketMuLog
  rw [padicVol_image_smul p]
  have hD' : 0 < Module.finrank ℚ_[p] (Fin (Module.finrank ℚ_[p] W) → ℚ_[p]) := by
    rwa [Module.finrank_fin_fun]
  exact padicMuLog_p_zpow_smul p μ hD' hΛ0 hΛ hA0 hA n

/-- The dimension of a two-factor packet: `dim (K₁ ⊗ K₂) = dim K₁ · dim K₂`, the degree by which
its log-volume is divided. -/
theorem padicVol_finrank_tensor (K₁ K₂ : Type*) [Field K₁] [Field K₂] [Algebra ℚ_[p] K₁]
    [Algebra ℚ_[p] K₂] [FiniteDimensional ℚ_[p] K₁] [FiniteDimensional ℚ_[p] K₂] :
    Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂) = Module.finrank ℚ_[p] K₁ * Module.finrank ℚ_[p] K₂ :=
  Module.finrank_tensorProduct

variable (K₁ K₂ : Type*) [Field K₁] [Field K₂] [Algebra ℚ_[p] K₁] [Algebra ℚ_[p] K₂]

/-- `x` is integral over `ℤ_p` (through `ℤ_p → ℚ_p → A`). -/
noncomputable def padicVolIntegral {A : Type*} [Ring A] [Algebra ℚ_[p] A] (x : A) : Prop :=
  ((algebraMap ℚ_[p] A).comp (algebraMap ℤ_[p] ℚ_[p])).IsIntegralElem x

/-- Integrality over `ℤ_p` is preserved by `ℚ_p`-algebra maps. -/
theorem padicVolIntegral_map {A B : Type*} [CommRing A] [CommRing B] [Algebra ℚ_[p] A]
    [Algebra ℚ_[p] B] (g : A →ₐ[ℚ_[p]] B) {x : A} (hx : padicVolIntegral p x) :
    padicVolIntegral p (g x) := by
  obtain ⟨P, hP, h0⟩ := hx
  refine ⟨P, hP, ?_⟩
  have hc : (algebraMap ℚ_[p] B).comp (algebraMap ℤ_[p] ℚ_[p]) =
      (g : A →+* B).comp ((algebraMap ℚ_[p] A).comp (algebraMap ℤ_[p] ℚ_[p])) :=
    RingHom.ext fun r => by simp
  rw [hc]
  have h := Polynomial.hom_eval₂ P ((algebraMap ℚ_[p] A).comp (algebraMap ℤ_[p] ℚ_[p]))
    (g : A →+* B) x
  rw [h0, map_zero] at h
  exact h.symm

/-- `R_E = R_1 ⊗_{ℤ_p} R_2` of IUT IV Proposition 1.1 (page 9) for two factors, as its image in
`K₁ ⊗[ℚ_p] K₂`: the additive span of the `x ⊗ y` with `x`, `y` integral over `ℤ_p` (the rings of
integers `R_i`). -/
noncomputable def padicPacketIntegers : Set (TensorProduct ℚ_[p] K₁ K₂) :=
  ((AddSubmonoid.closure
    {z | ∃ x y, padicVolIntegral p x ∧ padicVolIntegral p y ∧ z = TensorProduct.tmul ℚ_[p] x y} :
      AddSubmonoid (TensorProduct ℚ_[p] K₁ K₂)) : Set (TensorProduct ℚ_[p] K₁ K₂))

/-- `(R_E)^∼` of IUT IV Proposition 1.1 (page 9) for two factors: the elements of `K₁ ⊗ K₂`
integral over `ℤ_p` (see the interpretation choices in the module docstring). -/
noncomputable def padicPacketNormalization : Set (TensorProduct ℚ_[p] K₁ K₂) :=
  {z | padicVolIntegral p z}

/-- `R_E ⊆ (R_E)^∼`, the trivial inclusion of the proof of Proposition 1.1, page 9. -/
theorem padicPacketIntegers_subset :
    padicPacketIntegers p K₁ K₂ ⊆ padicPacketNormalization p K₁ K₂ := by
  set φ := (algebraMap ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).comp (algebraMap ℤ_[p] ℚ_[p])
  let M : AddSubmonoid (TensorProduct ℚ_[p] K₁ K₂) :=
    { carrier := {z | φ.IsIntegralElem z}
      add_mem' := fun ha hb => RingHom.IsIntegralElem.add φ ha hb
      zero_mem' := by
        show φ.IsIntegralElem 0
        rw [← φ.map_zero]; exact φ.isIntegralElem_map }
  have hgen : {z | ∃ x y, padicVolIntegral p x ∧ padicVolIntegral p y ∧
      z = TensorProduct.tmul ℚ_[p] x y} ⊆ (M : Set (TensorProduct ℚ_[p] K₁ K₂)) := by
    rintro _ ⟨x, y, hx, hy, rfl⟩
    have hxy : TensorProduct.tmul ℚ_[p] x y =
        Algebra.TensorProduct.includeLeft (S := ℚ_[p]) x *
          Algebra.TensorProduct.includeRight y := by
      simp
    show φ.IsIntegralElem _
    rw [hxy]
    exact RingHom.IsIntegralElem.mul φ (padicVolIntegral_map p _ hx) (padicVolIntegral_map p _ hy)
  intro z hz
  exact (AddSubmonoid.closure_le.mpr hgen) hz

end Packet

/-! ## Nonvacuity on `ℚ_p` -/

section Padic

variable (p : ℕ) [hp : Fact p.Prime]

/-- `ℤ_p = {‖x‖ ≤ 1}` as a compact set with nonempty interior, to normalize Haar measure. -/
noncomputable def padicVolZp : TopologicalSpace.PositiveCompacts ℚ_[p] where
  carrier := {x : ℚ_[p] | ‖x‖ ≤ 1}
  isCompact' := by
    have e : {x : ℚ_[p] | ‖x‖ ≤ 1} = Metric.closedBall 0 1 := by
      ext y; simp
    rw [e]; exact isCompact_closedBall _ _
  interior_nonempty' := by
    have e : {x : ℚ_[p] | ‖x‖ ≤ 1} = Metric.closedBall 0 1 := by
      ext y; simp
    rw [e, (IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero).interior_eq]
    exact ⟨0, by simp⟩

/-- The Borel structure exists on `ℚ_p`, so the hypotheses `[MeasurableSpace ℚ_[p]]`,
`[BorelSpace ℚ_[p]]` above are satisfiable. -/
theorem padicVol_borelSpace : @BorelSpace ℚ_[p] _ (borel ℚ_[p]) := @BorelSpace.mk _ _ (borel ℚ_[p]) rfl

variable [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]

/-- `μ(ℤ_p) = 1` for the Haar measure normalized on `ℤ_p`. -/
theorem padicVol_padic_unitBall :
    addHaarMeasure (padicVolZp p) {x : ℚ_[p] | ‖x‖ ≤ 1} = 1 :=
  addHaarMeasure_self

/-- `μ(p ^ n ℤ_p) = p ^ (−n)` for the Haar measure normalized on `ℤ_p` (`d = 1`). -/
theorem padicVol_padic_p_zpow (n : ℤ) :
    (addHaarMeasure (padicVolZp p) (((p : ℚ_[p]) ^ n) • {x : ℚ_[p] | ‖x‖ ≤ 1})).toReal =
      (p : ℝ) ^ (-n) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [padicVol_measure_smul p _ (zpow_ne_zero _ hp0), padicVol_padic_unitBall,
    Module.finrank_self, mul_one, pow_one, ENNReal.coe_toReal, coe_nnNorm, Padic.norm_p_zpow]

/-- The log-shell of `ℚ_p` has measure `1` for the Haar measure normalized on `ℤ_p`. -/
theorem padicVol_padicLogShell :
    addHaarMeasure (padicVolZp p) (IUT.Prerequisites.PadicLog.padicLogShell p) = 1 := by
  rw [IUT.Prerequisites.PadicLog.padicLogShell_eq]
  exact addHaarMeasure_self

/-- The bounds of `padicMuLog_logUnit_bounds` for `K = ℚ_p`, `e = 1`, `π = p`: the hypotheses
`hval` and `hπ` hold together there. -/
theorem padicMuLog_logUnit_bounds_padic (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure] :
    -IUT.PaperIV.Proposition1_2.a p 1 * Real.log p ≤
        padicMuLog p μ {y : ℚ_[p] | ‖y‖ ≤ 1}
          (IUT.PaperIV.LocalFields.extLogUnit '' {u : ℚ_[p] | ‖u‖ = 1}) ∧
      padicMuLog p μ {y : ℚ_[p] | ‖y‖ ≤ 1}
          (IUT.PaperIV.LocalFields.extLogUnit '' {u : ℚ_[p] | ‖u‖ = 1}) ≤
        IUT.PaperIV.Proposition1_2.b p 1 * Real.log p :=
  padicMuLog_logUnit_bounds p μ le_rfl
    (fun x hx => by simpa using IUT.PaperIV.LocalFields.extLog_padic_disc p x hx)
    (π := (p : ℚ_[p])) (by rw [pow_one, Padic.norm_p])

omit [BorelSpace ℚ_[p]] in
/-- **The log-shell of `ℚ_p` has normalized log-volume `0`**: it equals `ℤ_p`
(`IUT.Prerequisites.PadicLog.padicLogShell_eq`). -/
theorem padicMuLog_padicLogShell (μ : Measure ℚ_[p]) :
    padicMuLog p μ {x : ℚ_[p] | ‖x‖ ≤ 1} (IUT.Prerequisites.PadicLog.padicLogShell p) = 0 := by
  rw [IUT.Prerequisites.PadicLog.padicLogShell_eq]
  exact padicMuLog_self p μ _

/-- `μ^log(p ^ n ℤ_p) = −n log p` on `ℚ_p`. -/
theorem padicMuLog_padic_p_zpow (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure] (n : ℤ) :
    padicMuLog p μ {x : ℚ_[p] | ‖x‖ ≤ 1} (((p : ℚ_[p]) ^ n) • {x : ℚ_[p] | ‖x‖ ≤ 1}) =
      -(n * Real.log p) := by
  rw [padicMuLog_p_zpow_smul p μ (by rw [Module.finrank_self]; exact one_pos)
    (padicVol_unitBall_ne_zero p μ) (padicVol_unitBall_ne_top p μ)
    (padicVol_unitBall_ne_zero p μ) (padicVol_unitBall_ne_top p μ), padicMuLog_self]
  ring

end Padic

end IUT.Prerequisites.PadicVolume
