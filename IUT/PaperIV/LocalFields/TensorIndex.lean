import IUT.PaperIV.LocalFields.Packets
import IUT.PaperIV.LocalFields.TensorDifferent
import IUT.PaperIV.LocalFields.Tame

/-!
# The integral tensor order `R_E` of two finite extensions of `ℚ_p`: index and log-volume

Sources: Mochizuki, *Inter-universal Teichmüller Theory IV*, Proposition 1.1 (page 9, proof on
pages 9 and 10), Proposition 1.2 (pages 10 and 11; page 10 read), Proposition 1.4 (pages 13 and
14). Pages read for this file: 9, 10, 13 and 14. Pages checked against rendered images: 9, 10, 13
and 14. Displays relied on:
* page 9: `R_E = ⊗_{i ∈ E} R_i` "where the tensor product is over `ℤ_p`",
  `p ^ (𝔡_{I*}) · (R_I)^∼ ⊆ R_I ⊆ (R_I)^∼`, where `(−)^∼` is "the normalization of the
  [reduced] ring in parentheses in its ring of fractions", and `𝔡_i ∈ ℚ_{≥0}` is the order of
  any generator of the different ideal of `R_i` over `ℤ_p`. The exponent printed is `𝔡_{I*}`,
  with no ceiling;
* page 10: the proof of Proposition 1.1 reduces to `|I| = 2`, where the inclusion "follows
  immediately from the definition of the different ideal";
* page 13, Proposition 1.4 (i): the log-volume on compact open subsets of the tensor products,
  "normalized so that `μ^log((R_E)^∼) = 0`, `μ^log(p · (R_E)^∼) = −log(p)`";
* page 14, proof of Proposition 1.4 (iii): "by assertion (i), we have
  `μ^log(R_I) ≤ μ^log((R_I)^∼) = 0`", and the term `μ^log(R_I)` in the second line of the
  computation, `μ^log(log_p(R_I^×)) = ∑_{i ∈ I} μ^log(log_p(R_i^×)) + μ^log(R_I)`.
The pages do not print a formula for `μ^log(R_I)`; the index formula below is a fact about the
normalized log-volume used here, not a quotation.

## The objects

Two factors: `K₁`, `K₂` are finite extensions of `ℚ_[p]` (fields with finite-dimensional
`ℚ_[p]`-algebra structures). As in `IUT.Prerequisites.PadicVolume`, the tensor product is taken
over `ℚ_p` (for fields it agrees with the one over `ℤ_p`, `packet_tensor_zp_bijective`), and:
* `R_E` is `tensorIdxRing`, the subring of `K₁ ⊗[ℚ_p] K₂` additively spanned by the `x ⊗ y` with
  `x`, `y` integral over `ℤ_p` (the image of `R₁ ⊗_{ℤ_p} R₂`); its carrier is
  `padicPacketIntegers` (`tensorIdxRing_coe`);
* `(R_E)^∼` is `tensorIdxNormRing`, the subring of elements integral over `ℤ_p`; its carrier is
  `padicPacketNormalization`;
* `μ^log` is `padicPacketMuLog`, normalized at `(R_E)^∼`: the logarithm of the ratio of Haar
  measures in the coordinates of `Module.finBasis`, divided by `D = dim_{ℚ_p}(K₁ ⊗ K₂)`. It does
  not depend on the coordinates (`padicPacketMuLog_coord_indep`) nor on the Haar measure;
* `𝔡_i` is `differentOrder ℤ_[p] R_i P` at the prime `P` of `R_i = integralClosure ℤ_[p] K_i`
  over `p` (the exponent of `P` in the different divided by the ramification index);
* the index `[(R_E)^∼ : R_E]` is `AddSubgroup.relIndex` of the additive groups, that is the
  cardinality of `(R_E)^∼ / R_E` (`0` when infinite, which is excluded by
  `tensorIdx_relIndex_ne_zero`).

## What is proved

1. *`R_E` as a lattice.* `tensorIdxRing` is a subring and a `ℤ_p`-submodule
   (`tensorIdx_smul_mem`), `R_E ≤ (R_E)^∼` (`tensorIdxRing_le`).
   `tensorIdx_pow_mem_differentIdeal`, `tensorIdx_pow_smul_mem`: `p ^ k` lies in the different of
   `R₂` as soon as `k · e₂ ≥ n₂` (exponent of the different), hence `p ^ k · (R_E)^∼ ⊆ R_E`;
   `tensorIdx_ceil_smul_mem`: in particular `p ^ ⌈𝔡_2⌉ · (R_E)^∼ ⊆ R_E`, and
   `tensorIdx_ceil_smul_mem_left`: `p ^ ⌈𝔡_1⌉ · (R_E)^∼ ⊆ R_E` (exchanging the factors).
   `tensorIdx_coord_isOpen_isCompact`: in the coordinates of `Module.finBasis`, `R_E` and
   `(R_E)^∼` are open and compact (`R_E` is a subgroup containing the open set
   `p ^ k · (R_E)^∼`). `tensorIdx_relIndex_ne_zero`: `(R_E)^∼ / R_E` is finite.
2. *Measure and log-volume.* `tensorIdx_measure_eq_relIndex` (general): for subgroups `H ≤ N`
   with `N / H` finite, `μ N = [N : H] · μ H` for a translation invariant measure.
   `tensorIdx_measure`: `R_E` has positive finite Haar measure and
   `μ((R_E)^∼) = [(R_E)^∼ : R_E] · μ(R_E)`. `tensorIdx_muLog_eq`: **the index formula**
   `μ^log(R_E) = −log [(R_E)^∼ : R_E] / D`. `tensorIdx_muLog_nonpos`: `μ^log(R_E) ≤ 0`, the
   inequality `μ^log(R_I) ≤ μ^log((R_I)^∼) = 0` of page 14 for `|I| = 2`.
   `tensorIdx_muLog_ge_of_pow`, `tensorIdx_muLog_bounds`, `tensorIdx_muLog_bounds_left`:
   `−⌈𝔡_i⌉ log p ≤ μ^log(R_E)` and `[(R_E)^∼ : R_E] ≤ p ^ (⌈𝔡_i⌉ · D)` for `i = 1, 2`.
3. *Normalization.* `tensorIdx_isIntegralElem_iff`: `z` is integral over `R_E` if and only if
   `z ∈ (R_E)^∼`. `tensorIdx_exists_pow_smul_mem_ring`: every `z` is `r / p ^ n` with
   `r ∈ R_E`. `tensorIdx_isFractionRing`: `K₁ ⊗[ℚ_p] K₂` is the total ring of fractions of `R_E`
   (`IsFractionRing`). Together: `(R_E)^∼` is the normalization of `R_E` in its ring of
   fractions, the definition of page 9.
4. *Equality case and an example.* `tensorIdx_eq_of_ramificationIdx_eq_one` (and `_left`): if
   `K₂` (or `K₁`) has ramification index `1`, then `R_E = (R_E)^∼`; `tensorIdx_muLog_eq_zero_of_eq`:
   then the index is `1` and `μ^log(R_E) = 0`. `tensorIdxEx_ne`, `tensorIdxEx_muLog_neg`: for
   `K₁ = K₂ = K` with `[K : ℚ_p] = 2` and `π ∈ K`, `π ^ 2 = p` (every prime `p`),
   `p⁻¹ (π ⊗ π)` is integral but not in `R_E`, so `[(R_E)^∼ : R_E] ≥ 2` and `μ^log(R_E) < 0`;
   `tensorIdxEx_exists`: such `K` exists (`ℚ_p[X] / (X ^ 2 − p)`).

## Not proved

* The sharp bound `μ^log(R_E) ≥ −𝔡_2 log p` without the ceiling: it would follow from
  `(1 ⊗ δ) · (R_E)^∼ ⊆ R_E` (`tensorDiff_mul_mem_packetIntegers`) and the scaling of Haar measure
  by the multiplication by `1 ⊗ δ`, whose modulus is `‖N_{K₂/ℚ_p}(δ)‖ ^ [K₁ : ℚ_p]`; Haar scaling
  by an element of a tensor product (a determinant formula over `ℚ_p`) is not available here.
* The exact index in the example (it is `p` for `p` odd by a computation of the ring of integers
  of `K ⊗ K ≅ K × K`); only the lower bound `2` is proved.
* More than two factors, and the identification of `K₁ ⊗[ℤ_p] K₂` with `K₁ ⊗[ℚ_p] K₂` for more
  than two factors.
* The additivity of page 14, `μ^log(log_p(R_I^×)) = ∑_i μ^log(log_p(R_i^×)) + μ^log(R_I)`, is out
  of scope here. For two factors it would need: that the image `L` of
  `log_p(R₁^×) ⊗_{ℤ_p} log_p(R₂^×)` in `K₁ ⊗ K₂` is a lattice and the index formula
  relating the generalized index of `L` relative to `R_E` to those of `L_i = log_p(R_i^×)`
  relative to `R_i`; that is, the multiplicativity of generalized indices under tensor products
  of `ℤ_p`-lattices, `[R₁ ⊗ R₂ : L₁ ⊗ L₂] = [R₁ : L₁] ^ (dim K₂) · [R₂ : L₂] ^ (dim K₁)` (true by
  elementary divisors, not formalized), together with the identification of the image of
  `L₁ ⊗_{ℤ_p} L₂` with the lattice spanned by the `x ⊗ y`, `x ∈ L₁`, `y ∈ L₂`.
-/

open MeasureTheory Measure IUT.Prerequisites.PadicVolume
open scoped Pointwise

namespace IUT.PaperIV.LocalFields

/-! ## Measure of a subgroup of finite relative index -/

section RelIndex

variable {V : Type*} [AddGroup V]

/-- The coset `q` of `H` in `N`, translated back into `V`: `x` lies in `out(q) + H` if and only if
`x ∈ N` and the class of `x` in `N / H` is `q`. -/
theorem tensorIdx_mem_coset_iff {H N : AddSubgroup V} (hHN : H ≤ N)
    (q : ↥N ⧸ H.addSubgroupOf N) (x : V) :
    x ∈ ((Quotient.out q : N) : V) +ᵥ (H : Set V) ↔
      ∃ hx : x ∈ N, (QuotientAddGroup.mk (⟨x, hx⟩ : N) : ↥N ⧸ H.addSubgroupOf N) = q := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    have hxN : ((Quotient.out q : N) : V) + h ∈ N := N.add_mem (Quotient.out q).2 (hHN hh)
    refine ⟨hxN, ?_⟩
    conv_rhs => rw [← QuotientAddGroup.out_eq' q]
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    have e : ((-(⟨((Quotient.out q : N) : V) +ᵥ h, hxN⟩ : N) + Quotient.out q : N) : V) = -h := by
      simp [vadd_eq_add]
    rw [e]
    exact H.neg_mem hh
  · rintro ⟨hx, hq⟩
    have h1 : (QuotientAddGroup.mk (Quotient.out q) : ↥N ⧸ H.addSubgroupOf N) =
        QuotientAddGroup.mk (⟨x, hx⟩ : N) := (QuotientAddGroup.out_eq' q).trans hq.symm
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
    refine ⟨-((Quotient.out q : N) : V) + x, by simpa using h1, ?_⟩
    simp [vadd_eq_add]

/-- **Measure of a subgroup of finite relative index**: for subgroups `H ≤ N` of `V` with `N / H`
finite, `H` measurable and `μ` invariant under translations, `μ N = [N : H] · μ H`. `N` is the
disjoint union of the `[N : H]` translates of `H` by representatives of `N / H`. -/
theorem tensorIdx_measure_eq_relIndex [MeasurableSpace V] [MeasurableAdd V] (μ : Measure V)
    [μ.IsAddLeftInvariant] {H N : AddSubgroup V} (hHN : H ≤ N)
    [Finite (↥N ⧸ H.addSubgroupOf N)] (hH : MeasurableSet (H : Set V)) :
    μ (N : Set V) = (H.relIndex N : ENNReal) * μ (H : Set V) := by
  classical
  have := Fintype.ofFinite (↥N ⧸ H.addSubgroupOf N)
  have hU : (N : Set V) =
      ⋃ q : ↥N ⧸ H.addSubgroupOf N, ((Quotient.out q : N) : V) +ᵥ (H : Set V) := by
    ext x
    simp only [Set.mem_iUnion, tensorIdx_mem_coset_iff hHN]
    exact ⟨fun hx => ⟨_, hx, rfl⟩, fun ⟨_, hx, _⟩ => hx⟩
  have hD : Pairwise (Function.onFun Disjoint
      fun q : ↥N ⧸ H.addSubgroupOf N => ((Quotient.out q : N) : V) +ᵥ (H : Set V)) := by
    intro q q' hqq'
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    rw [tensorIdx_mem_coset_iff hHN] at hx hx'
    obtain ⟨_, rfl⟩ := hx
    obtain ⟨_, h'⟩ := hx'
    exact hqq' h'
  have hM : ∀ q : ↥N ⧸ H.addSubgroupOf N,
      MeasurableSet (((Quotient.out q : N) : V) +ᵥ (H : Set V)) :=
    fun q => hH.const_vadd _
  rw [hU, measure_iUnion hD hM]
  simp only [measure_vadd, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]

/-- **An open subgroup of a compact subgroup has finite index**: for subgroups `H ≤ N` of a
topological group `V` with `H` open and `N` compact, `N / H` is finite. -/
theorem tensorIdx_finite_quotient [TopologicalSpace V] [IsTopologicalAddGroup V]
    {H N : AddSubgroup V} (hHN : H ≤ N) (hH : IsOpen (H : Set V))
    (hN : IsCompact (N : Set V)) : Finite (↥N ⧸ H.addSubgroupOf N) := by
  classical
  obtain ⟨t, ht⟩ := hN.elim_finite_subcover
    (fun q : ↥N ⧸ H.addSubgroupOf N => ((Quotient.out q : N) : V) +ᵥ (H : Set V))
    (fun q => hH.vadd _)
    (fun x hx => Set.mem_iUnion.2 ⟨_, (tensorIdx_mem_coset_iff hHN _ x).2 ⟨hx, rfl⟩⟩)
  have hall : ∀ q : ↥N ⧸ H.addSubgroupOf N, q ∈ t := by
    intro q
    have hx := ht (Quotient.out q).2
    simp only [Set.mem_iUnion] at hx
    obtain ⟨q', hq', hx⟩ := hx
    obtain ⟨_, h⟩ := (tensorIdx_mem_coset_iff hHN q' _).1 hx
    rw [Subtype.coe_eta, QuotientAddGroup.out_eq'] at h
    exact h ▸ hq'
  exact Finite.of_injective (fun q => (⟨q, hall q⟩ : t)) fun a b h => congrArg Subtype.val h

end RelIndex

/-! ## The rings `R_E` and `(R_E)^∼` -/

section Rings

variable (p : ℕ) [hp : Fact p.Prime]

/-- `1` is integral over `ℤ_p`. -/
theorem tensorIdx_integral_one {A : Type*} [CommRing A] [Algebra ℚ_[p] A] :
    padicVolIntegral p (1 : A) := by
  unfold padicVolIntegral
  rw [← RingHom.map_one ((algebraMap ℚ_[p] A).comp (algebraMap ℤ_[p] ℚ_[p]))]
  exact RingHom.isIntegralElem_map _

/-- The image of an element of `ℤ_p` is integral over `ℤ_p`. -/
theorem tensorIdx_integral_algebraMap {A : Type*} [CommRing A] [Algebra ℚ_[p] A] (c : ℤ_[p]) :
    padicVolIntegral p (algebraMap ℚ_[p] A (c : ℚ_[p])) :=
  RingHom.isIntegralElem_map ((algebraMap ℚ_[p] A).comp (algebraMap ℤ_[p] ℚ_[p])) (x := c)

variable (K₁ K₂ : Type*) [Field K₁] [Field K₂] [Algebra ℚ_[p] K₁] [Algebra ℚ_[p] K₂]

/-- The pure tensors `x ⊗ y` with `x`, `y` integral over `ℤ_p`, a multiplicative submonoid of
`K₁ ⊗[ℚ_p] K₂`; its additive span is `R_E = padicPacketIntegers`. -/
noncomputable def tensorIdxPureMonoid : Submonoid (TensorProduct ℚ_[p] K₁ K₂) where
  carrier := {z | ∃ x y, padicVolIntegral p x ∧ padicVolIntegral p y ∧
    z = TensorProduct.tmul ℚ_[p] x y}
  one_mem' := ⟨1, 1, tensorIdx_integral_one p, tensorIdx_integral_one p, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨x, y, hx, hy, rfl⟩ ⟨x', y', hx', hy', rfl⟩
    exact ⟨x * x', y * y', RingHom.IsIntegralElem.mul _ hx hx',
      RingHom.IsIntegralElem.mul _ hy hy', Algebra.TensorProduct.tmul_mul_tmul _ _ _ _⟩

/-- **`R_E = R₁ ⊗_{ℤ_p} R₂` as a subring of `K₁ ⊗[ℚ_p] K₂`**: the additive span of the `x ⊗ y`
with `x`, `y` integral over `ℤ_p`. Its carrier is `padicPacketIntegers`
(`tensorIdxRing_coe`). -/
noncomputable def tensorIdxRing : Subring (TensorProduct ℚ_[p] K₁ K₂) where
  toSubsemiring := (tensorIdxPureMonoid p K₁ K₂).subsemiringClosure
  neg_mem' {z} hz := by
    have hz' : z ∈ AddSubmonoid.closure
        ((tensorIdxPureMonoid p K₁ K₂ : Set (TensorProduct ℚ_[p] K₁ K₂))) := by
      rw [← SetLike.mem_coe, ← Submonoid.subsemiringClosure_coe]
      exact hz
    show -z ∈ (tensorIdxPureMonoid p K₁ K₂).subsemiringClosure
    rw [← SetLike.mem_coe, Submonoid.subsemiringClosure_coe, SetLike.mem_coe]
    clear hz
    induction hz' using AddSubmonoid.closure_induction with
    | mem w hw =>
      obtain ⟨x, y, hx, hy, rfl⟩ := hw
      exact AddSubmonoid.subset_closure ⟨-x, y, RingHom.IsIntegralElem.neg _ hx, hy,
        (TensorProduct.neg_tmul x y).symm⟩
    | zero => rw [neg_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [neg_add]; exact add_mem ha hb

/-- The carrier of `tensorIdxRing` is `padicPacketIntegers`. -/
theorem tensorIdxRing_coe :
    (tensorIdxRing p K₁ K₂ : Set (TensorProduct ℚ_[p] K₁ K₂)) = padicPacketIntegers p K₁ K₂ :=
  Submonoid.subsemiringClosure_coe _

/-- **`(R_E)^∼` as a subring of `K₁ ⊗[ℚ_p] K₂`**: the elements integral over `ℤ_p`. Its
carrier is `padicPacketNormalization`. -/
noncomputable def tensorIdxNormRing : Subring (TensorProduct ℚ_[p] K₁ K₂) where
  carrier := padicPacketNormalization p K₁ K₂
  mul_mem' ha hb := RingHom.IsIntegralElem.mul _ ha hb
  one_mem' := tensorIdx_integral_one p
  add_mem' ha hb := RingHom.IsIntegralElem.add _ ha hb
  zero_mem' := by
    show padicVolIntegral p (0 : TensorProduct ℚ_[p] K₁ K₂)
    unfold padicVolIntegral
    rw [← RingHom.map_zero ((algebraMap ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).comp
      (algebraMap ℤ_[p] ℚ_[p]))]
    exact RingHom.isIntegralElem_map _
  neg_mem' ha := RingHom.IsIntegralElem.neg _ ha

/-- The carrier of `tensorIdxNormRing` is `padicPacketNormalization`. -/
theorem tensorIdxNormRing_coe :
    (tensorIdxNormRing p K₁ K₂ : Set (TensorProduct ℚ_[p] K₁ K₂)) =
      padicPacketNormalization p K₁ K₂ := rfl

/-- `R_E ≤ (R_E)^∼` as subrings. -/
theorem tensorIdxRing_le : tensorIdxRing p K₁ K₂ ≤ tensorIdxNormRing p K₁ K₂ := by
  intro z hz
  rw [← SetLike.mem_coe, tensorIdxRing_coe] at hz
  exact padicPacketIntegers_subset p K₁ K₂ hz

/-- The image of `ℤ_p` lies in `R_E`. -/
theorem tensorIdx_algebraMap_mem (c : ℤ_[p]) :
    algebraMap ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂) (c : ℚ_[p]) ∈ tensorIdxRing p K₁ K₂ := by
  rw [← SetLike.mem_coe, tensorIdxRing_coe, Algebra.TensorProduct.algebraMap_apply]
  exact AddSubmonoid.subset_closure ⟨_, 1, tensorIdx_integral_algebraMap p c,
    tensorIdx_integral_one p, rfl⟩

/-- **`R_E` is a `ℤ_p`-submodule**: `c • z ∈ R_E` for `c ∈ ℤ_p` (acting through `ℚ_p`) and
`z ∈ R_E`. -/
theorem tensorIdx_smul_mem (c : ℤ_[p]) {z : TensorProduct ℚ_[p] K₁ K₂}
    (hz : z ∈ tensorIdxRing p K₁ K₂) : (c : ℚ_[p]) • z ∈ tensorIdxRing p K₁ K₂ := by
  rw [Algebra.smul_def]
  exact mul_mem (tensorIdx_algebraMap_mem p K₁ K₂ c) hz

end Rings

/-! ## `p ^ k · (R_E)^∼ ⊆ R_E` from the different of the second factor -/

section Different

variable (p : ℕ) [hp : Fact p.Prime] (K₁ K₂ : Type*) [Field K₁] [Field K₂] [Algebra ℚ_[p] K₁]
  [Algebra ℚ_[p] K₂]

/-- **`p ^ k` lies in the different** of `R₂ = integralClosure ℤ_[p] K₂` over `ℤ_p` as soon as
`k · e ≥ n`, where `n = differentExponent` is the exponent of the prime `P` over `p` in the
different and `e` its ramification index; that is, as soon as `k ≥ 𝔡_2 = n / e`. -/
theorem tensorIdx_pow_mem_differentIdeal [FiniteDimensional ℚ_[p] K₂] [Algebra ℤ_[p] K₂]
    [IsScalarTower ℤ_[p] ℚ_[p] K₂] (P : Ideal (integralClosure ℤ_[p] K₂)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] {k : ℕ}
    (hk : letI := isDedekindDomain_ringOfIntegers_padic p K₂
      letI := isTorsionFree_ringOfIntegers_padic p K₂
      differentExponent ℤ_[p] (integralClosure ℤ_[p] K₂) P ≤ k * P.ramificationIdx ℤ_[p]) :
    letI := isDedekindDomain_ringOfIntegers_padic p K₂
    letI := isTorsionFree_ringOfIntegers_padic p K₂
    ((p : integralClosure ℤ_[p] K₂)) ^ k ∈ differentIdeal ℤ_[p] (integralClosure ℤ_[p] K₂) := by
  let := isDedekindDomain_ringOfIntegers_padic p K₂
  let := isTorsionFree_ringOfIntegers_padic p K₂
  have := padicBridge_isLocalRing p K₂
  have := padicBridge_isDiscreteValuationRing p K₂
  obtain ⟨ϖ, hirr, hPϖ, hpe, -⟩ := padicBridge_uniformizer p K₂ P
  have hD := differentIdeal_ne_bot_of_isIntegralClosure ℤ_[p] ℚ_[p] K₂
    (integralClosure ℤ_[p] K₂)
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hD hirr
  have hP0 : P ≠ ⊥ := by
    rw [hPϖ, Ne, Ideal.span_singleton_eq_bot]
    exact hirr.ne_zero
  have hexp : differentExponent ℤ_[p] (integralClosure ℤ_[p] K₂) P = n := by
    unfold differentExponent
    rw [hn, ← Ideal.span_singleton_pow, ← hPϖ,
      multiplicity_pow_self_of_prime (Ideal.prime_of_isPrime hP0 inferInstance)]
  have hk' : n ≤ P.ramificationIdx ℤ_[p] * k := by
    rw [← hexp, mul_comm]
    exact hk
  have h1 : ((p : integralClosure ℤ_[p] K₂)) ^ k ∈
      (Ideal.span {((p : ℕ) : integralClosure ℤ_[p] K₂)}) ^ k :=
    Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) k
  rw [hpe, ← pow_mul, Ideal.span_singleton_pow] at h1
  rw [hn]
  exact Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ hk') h1

/-- **`p ^ k · (R_E)^∼ ⊆ R_E` for `k ≥ 𝔡_2`** (IUT IV Proposition 1.1, page 9, for two factors,
with `p ^ (𝔡_{I*})` replaced by the power `p ^ k` of `p` with `k · e ≥ n`): for `z ∈ (R_E)^∼`,
`p ^ k • z ∈ R_E`. From `tensorDiff_mul_mem_packetIntegers` with `δ = p ^ k`. -/
theorem tensorIdx_pow_smul_mem [FiniteDimensional ℚ_[p] K₂] [Algebra ℤ_[p] K₂]
    [IsScalarTower ℤ_[p] ℚ_[p] K₂] (P : Ideal (integralClosure ℤ_[p] K₂)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] {k : ℕ}
    (hk : letI := isDedekindDomain_ringOfIntegers_padic p K₂
      letI := isTorsionFree_ringOfIntegers_padic p K₂
      differentExponent ℤ_[p] (integralClosure ℤ_[p] K₂) P ≤ k * P.ramificationIdx ℤ_[p])
    {z : TensorProduct ℚ_[p] K₁ K₂} (hz : z ∈ tensorIdxNormRing p K₁ K₂) :
    ((p : ℚ_[p]) ^ k) • z ∈ tensorIdxRing p K₁ K₂ := by
  have h := tensorDiff_mul_mem_packetIntegers p K₁ K₂
    (tensorIdx_pow_mem_differentIdeal p K₂ P hk) hz
  rw [← SetLike.mem_coe, tensorIdxRing_coe]
  convert h using 1
  have e : (((p : integralClosure ℤ_[p] K₂) ^ k : integralClosure ℤ_[p] K₂) : K₂) =
      algebraMap ℚ_[p] K₂ ((p : ℚ_[p]) ^ k) := by simp
  rw [e, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, smul_mul_assoc,
    ← Algebra.TensorProduct.one_def, one_mul]

/-- **The exponent `⌈𝔡_2⌉`**: `p ^ ⌈𝔡_2⌉ · (R_E)^∼ ⊆ R_E`, with `𝔡_2 = differentOrder` the order of
the different of `R₂` at the prime `P` over `p` (page 9). -/
theorem tensorIdx_ceil_smul_mem [FiniteDimensional ℚ_[p] K₂] [Algebra ℤ_[p] K₂]
    [IsScalarTower ℤ_[p] ℚ_[p] K₂] (P : Ideal (integralClosure ℤ_[p] K₂)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    {z : TensorProduct ℚ_[p] K₁ K₂} (hz : z ∈ tensorIdxNormRing p K₁ K₂) :
    letI := isDedekindDomain_ringOfIntegers_padic p K₂
    letI := isTorsionFree_ringOfIntegers_padic p K₂
    ((p : ℚ_[p]) ^ ⌈differentOrder ℤ_[p] (integralClosure ℤ_[p] K₂) P⌉₊) • z ∈
      tensorIdxRing p K₁ K₂ := by
  let := isDedekindDomain_ringOfIntegers_padic p K₂
  let := isTorsionFree_ringOfIntegers_padic p K₂
  refine tensorIdx_pow_smul_mem p K₁ K₂ P ?_ hz
  have he : (0 : ℝ) < P.ramificationIdx ℤ_[p] := by
    exact_mod_cast ramificationIdx_pos_of_liesOver (IsDiscreteValuationRing.not_a_field ℤ_[p]) P
  have h := Nat.le_ceil (differentOrder ℤ_[p] (integralClosure ℤ_[p] K₂) P)
  unfold differentOrder at h ⊢
  rw [div_le_iff₀ he] at h
  exact_mod_cast h

/-- **Some power of `p` maps `(R_E)^∼` into `R_E`**, for any finite extension `K₂` of `ℚ_p` (no
`ℤ_p`-algebra structure on `K₂` is assumed; one is built from `ℤ_p → ℚ_p`). -/
theorem tensorIdx_exists_pow_smul_mem [FiniteDimensional ℚ_[p] K₂] :
    ∃ k : ℕ, ∀ z ∈ tensorIdxNormRing p K₁ K₂, ((p : ℚ_[p]) ^ k) • z ∈ tensorIdxRing p K₁ K₂ := by
  let _ : Algebra ℤ_[p] K₂ := ((algebraMap ℚ_[p] K₂).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra
  have : IsScalarTower ℤ_[p] ℚ_[p] K₂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := padicBridge_isLocalRing p K₂
  have := padicBridge_maximalIdeal_liesOver p K₂
  exact ⟨_, fun z hz => tensorIdx_ceil_smul_mem p K₁ K₂ (IsLocalRing.maximalIdeal _) hz⟩

end Different

/-! ## `R_E` in coordinates: open, compact, of finite index, and its log-volume -/

section Measure

variable (p : ℕ) [hp : Fact p.Prime] (K₁ K₂ : Type*) [Field K₁] [Field K₂] [Algebra ℚ_[p] K₁]
  [Algebra ℚ_[p] K₂] [FiniteDimensional ℚ_[p] K₁] [FiniteDimensional ℚ_[p] K₂]

/-- The image of an additive subgroup of `K₁ ⊗[ℚ_p] K₂` in the coordinates of `Module.finBasis`
(the coordinates in which `padicPacketMuLog` is computed). -/
noncomputable def tensorIdxCoordMap (S : AddSubgroup (TensorProduct ℚ_[p] K₁ K₂)) :
    AddSubgroup (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) → ℚ_[p]) :=
  S.map (Module.finBasis ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).equivFun.toAddEquiv.toAddMonoidHom

theorem tensorIdxCoordMap_coe (S : AddSubgroup (TensorProduct ℚ_[p] K₁ K₂)) :
    (tensorIdxCoordMap p K₁ K₂ S : Set _) =
      (Module.finBasis ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).equivFun '' S := by
  rw [tensorIdxCoordMap, AddSubgroup.coe_map]
  rfl

/-- The coordinate map preserves relative indices. -/
theorem tensorIdxCoordMap_relIndex (H N : AddSubgroup (TensorProduct ℚ_[p] K₁ K₂)) :
    (tensorIdxCoordMap p K₁ K₂ H).relIndex (tensorIdxCoordMap p K₁ K₂ N) = H.relIndex N :=
  AddSubgroup.relIndex_map_map_of_injective H N
    (Module.finBasis ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).equivFun.toAddEquiv.injective

/-- **`R_E` is open and compact** in the coordinates of `Module.finBasis` of `K₁ ⊗[ℚ_p] K₂` (the
coordinates of `padicPacketMuLog`), and so is `(R_E)^∼`. `R_E` is a subgroup containing the
open set `p ^ k · (R_E)^∼`, hence open and closed, and it lies in the compact `(R_E)^∼`. -/
theorem tensorIdx_coord_isOpen_isCompact :
    IsOpen ((tensorIdxCoordMap p K₁ K₂ (tensorIdxRing p K₁ K₂).toAddSubgroup :
        Set (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) → ℚ_[p]))) ∧
      IsCompact ((tensorIdxCoordMap p K₁ K₂ (tensorIdxRing p K₁ K₂).toAddSubgroup :
        Set (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) → ℚ_[p]))) ∧
      IsOpen ((tensorIdxCoordMap p K₁ K₂ (tensorIdxNormRing p K₁ K₂).toAddSubgroup :
        Set (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) → ℚ_[p]))) ∧
      IsCompact ((tensorIdxCoordMap p K₁ K₂ (tensorIdxNormRing p K₁ K₂).toAddSubgroup :
        Set (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) → ℚ_[p]))) := by
  have := volBridge_tensor_formallyUnramified p K₁ K₂
  obtain ⟨hK, hO⟩ := packet_normalization_isCompact_isOpen p (TensorProduct ℚ_[p] K₁ K₂)
  obtain ⟨k, hk⟩ := tensorIdx_exists_pow_smul_mem p K₁ K₂
  set c := (Module.finBasis ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).equivFun
  have hN : (tensorIdxCoordMap p K₁ K₂ (tensorIdxNormRing p K₁ K₂).toAddSubgroup :
      Set (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) → ℚ_[p])) =
      c '' packetNormalizationSet p (TensorProduct ℚ_[p] K₁ K₂) := tensorIdxCoordMap_coe p K₁ K₂ _
  have hsub : ((p : ℚ_[p]) ^ k) • (c '' packetNormalizationSet p (TensorProduct ℚ_[p] K₁ K₂)) ⊆
      (tensorIdxCoordMap p K₁ K₂ (tensorIdxRing p K₁ K₂).toAddSubgroup : Set _) := by
    rw [tensorIdxCoordMap_coe, ← padicVol_image_smul p c]
    refine Set.image_mono ?_
    rintro _ ⟨z, hz, rfl⟩
    exact hk z hz
  have hp0 : ((p : ℚ_[p]) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hopen := hO.smul₀ hp0
  have h0 : (0 : Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) → ℚ_[p]) ∈
      ((p : ℚ_[p]) ^ k) • (c '' packetNormalizationSet p (TensorProduct ℚ_[p] K₁ K₂)) :=
    ⟨0, ⟨0, packet_zero_mem_normalization p _, map_zero c⟩, smul_zero _⟩
  have hHo : IsOpen ((tensorIdxCoordMap p K₁ K₂ (tensorIdxRing p K₁ K₂).toAddSubgroup :
      Set (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) → ℚ_[p]))) :=
    AddSubgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hopen.mem_nhds h0) hsub)
  have hHc := AddSubgroup.isClosed_of_isOpen _ hHo
  have hle : (tensorIdxCoordMap p K₁ K₂ (tensorIdxRing p K₁ K₂).toAddSubgroup : Set _) ⊆
      c '' packetNormalizationSet p (TensorProduct ℚ_[p] K₁ K₂) := by
    rw [tensorIdxCoordMap_coe]
    exact Set.image_mono (tensorIdxRing_le p K₁ K₂)
  exact ⟨hHo, hK.of_isClosed_subset hHc hle, hN ▸ hO, hN ▸ hK⟩

/-- **`(R_E)^∼ / R_E` is finite**: the relative index `[(R_E)^∼ : R_E]` is nonzero. -/
theorem tensorIdx_relIndex_ne_zero :
    (tensorIdxRing p K₁ K₂).toAddSubgroup.relIndex
      (tensorIdxNormRing p K₁ K₂).toAddSubgroup ≠ 0 := by
  obtain ⟨hHo, -, -, hNc⟩ := tensorIdx_coord_isOpen_isCompact p K₁ K₂
  have hle : tensorIdxCoordMap p K₁ K₂ (tensorIdxRing p K₁ K₂).toAddSubgroup ≤
      tensorIdxCoordMap p K₁ K₂ (tensorIdxNormRing p K₁ K₂).toAddSubgroup :=
    AddSubgroup.map_mono (tensorIdxRing_le p K₁ K₂)
  have := tensorIdx_finite_quotient hle hHo hNc
  rw [← tensorIdxCoordMap_relIndex]
  exact Nat.card_pos.ne'

variable [MeasurableSpace (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) → ℚ_[p])]
  [BorelSpace (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) → ℚ_[p])]
  (μ : Measure (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) → ℚ_[p]))
  [μ.IsAddHaarMeasure]

/-- **Positive finite measure and the index formula for Haar measure**: in coordinates,
`R_E` has positive finite Haar measure and `μ((R_E)^∼) = [(R_E)^∼ : R_E] · μ(R_E)`. -/
theorem tensorIdx_measure :
    μ ((Module.finBasis ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).equivFun ''
        padicPacketIntegers p K₁ K₂) ≠ 0 ∧
      μ ((Module.finBasis ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).equivFun ''
        padicPacketIntegers p K₁ K₂) ≠ ⊤ ∧
      μ ((Module.finBasis ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).equivFun ''
        padicPacketNormalization p K₁ K₂) =
        ((tensorIdxRing p K₁ K₂).toAddSubgroup.relIndex
          (tensorIdxNormRing p K₁ K₂).toAddSubgroup : ENNReal) *
        μ ((Module.finBasis ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).equivFun ''
          padicPacketIntegers p K₁ K₂) := by
  obtain ⟨hHo, hHc, -, hNc⟩ := tensorIdx_coord_isOpen_isCompact p K₁ K₂
  have hle : tensorIdxCoordMap p K₁ K₂ (tensorIdxRing p K₁ K₂).toAddSubgroup ≤
      tensorIdxCoordMap p K₁ K₂ (tensorIdxNormRing p K₁ K₂).toAddSubgroup :=
    AddSubgroup.map_mono (tensorIdxRing_le p K₁ K₂)
  have := tensorIdx_finite_quotient hle hHo hNc
  have h := tensorIdx_measure_eq_relIndex μ hle hHo.measurableSet
  rw [tensorIdxCoordMap_relIndex, tensorIdxCoordMap_coe, tensorIdxCoordMap_coe] at h
  rw [tensorIdxCoordMap_coe] at hHo hHc
  have hc : ((tensorIdxRing p K₁ K₂).toAddSubgroup : Set (TensorProduct ℚ_[p] K₁ K₂)) =
      padicPacketIntegers p K₁ K₂ := tensorIdxRing_coe p K₁ K₂
  rw [hc] at h hHo hHc
  refine ⟨hHo.measure_ne_zero μ ⟨0, 0, ?_, map_zero _⟩, hHc.measure_lt_top.ne, h⟩
  rw [← hc]
  exact zero_mem _

/-- **The index formula for the log-volume**: normalized so that `μ^log((R_E)^∼) = 0` (the
normalization of IUT IV Proposition 1.4 (i), page 13),
`μ^log(R_E) = −log [(R_E)^∼ : R_E] / dim_{ℚ_p}(K₁ ⊗ K₂)`. -/
theorem tensorIdx_muLog_eq :
    padicPacketMuLog p (TensorProduct ℚ_[p] K₁ K₂) μ (padicPacketNormalization p K₁ K₂)
        (padicPacketIntegers p K₁ K₂) =
      -Real.log ((tensorIdxRing p K₁ K₂).toAddSubgroup.relIndex
          (tensorIdxNormRing p K₁ K₂).toAddSubgroup) /
        Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂) := by
  obtain ⟨h0, h1, h⟩ := tensorIdx_measure p K₁ K₂ μ
  have hn := tensorIdx_relIndex_ne_zero p K₁ K₂
  unfold padicPacketMuLog padicMuLog
  rw [h, ENNReal.toReal_mul, Module.finrank_fin_fun, ENNReal.toReal_natCast]
  have ha := ENNReal.toReal_pos h0 h1
  have hn' : (0 : ℝ) < ((tensorIdxRing p K₁ K₂).toAddSubgroup.relIndex
      (tensorIdxNormRing p K₁ K₂).toAddSubgroup : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [div_mul_cancel_right₀ ha.ne', Real.log_inv]

/-- **`μ^log(R_E) ≤ 0 = μ^log((R_E)^∼)`**, the inequality used on IUT IV page 14 (for two
factors). -/
theorem tensorIdx_muLog_nonpos :
    padicPacketMuLog p (TensorProduct ℚ_[p] K₁ K₂) μ (padicPacketNormalization p K₁ K₂)
        (padicPacketIntegers p K₁ K₂) ≤ 0 := by
  rw [tensorIdx_muLog_eq]
  have hn := tensorIdx_relIndex_ne_zero p K₁ K₂
  have : 0 ≤ Real.log ((tensorIdxRing p K₁ K₂).toAddSubgroup.relIndex
      (tensorIdxNormRing p K₁ K₂).toAddSubgroup) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _)

/-- **Lower bound from an inclusion `p ^ k · (R_E)^∼ ⊆ R_E`**: `μ^log(R_E) ≥ −k log p`, and
`[(R_E)^∼ : R_E] ≤ p ^ (k · dim (K₁ ⊗ K₂))`. -/
theorem tensorIdx_muLog_ge_of_pow {k : ℕ}
    (hk : ∀ z ∈ tensorIdxNormRing p K₁ K₂, ((p : ℚ_[p]) ^ k) • z ∈ tensorIdxRing p K₁ K₂) :
    -(k * Real.log p) ≤ padicPacketMuLog p (TensorProduct ℚ_[p] K₁ K₂) μ
        (padicPacketNormalization p K₁ K₂) (padicPacketIntegers p K₁ K₂) ∧
      (tensorIdxRing p K₁ K₂).toAddSubgroup.relIndex (tensorIdxNormRing p K₁ K₂).toAddSubgroup ≤
        p ^ (k * Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) := by
  have := volBridge_tensor_formallyUnramified p K₁ K₂
  have hD0 : 0 < Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂) := by
    rw [padicVol_finrank_tensor p K₁ K₂]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos
  have : Nontrivial (TensorProduct ℚ_[p] K₁ K₂) := Module.nontrivial_of_finrank_pos hD0
  obtain ⟨hN0, hN1, -, hNn⟩ := packet_muLog_normalization p (TensorProduct ℚ_[p] K₁ K₂) μ
  obtain ⟨hR0, hR1, -⟩ := tensorIdx_measure p K₁ K₂ μ
  obtain ⟨-, hO⟩ := packet_normalization_isCompact_isOpen p (TensorProduct ℚ_[p] K₁ K₂)
  set c := (Module.finBasis ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).equivFun
  have hp0 : ((p : ℚ_[p]) ^ (k : ℤ)) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hsub : c '' (((p : ℚ_[p]) ^ (k : ℤ)) • packetNormalizationSet p
      (TensorProduct ℚ_[p] K₁ K₂)) ⊆ c '' padicPacketIntegers p K₁ K₂ := by
    refine Set.image_mono ?_
    rintro _ ⟨z, hz, rfl⟩
    rw [← tensorIdxRing_coe, zpow_natCast]
    exact hk z hz
  have hA0 : μ (c '' (((p : ℚ_[p]) ^ (k : ℤ)) • packetNormalizationSet p
      (TensorProduct ℚ_[p] K₁ K₂))) ≠ 0 := by
    rw [padicVol_image_smul p c]
    exact (hO.smul₀ hp0).measure_ne_zero μ
      ⟨0, 0, ⟨0, packet_zero_mem_normalization p _, map_zero c⟩, smul_zero _⟩
  have hmono := padicMuLog_mono p μ hsub hN0 hN1 hA0 hR1
  have h1 : -(k * Real.log p) ≤ padicPacketMuLog p (TensorProduct ℚ_[p] K₁ K₂) μ
      (padicPacketNormalization p K₁ K₂) (padicPacketIntegers p K₁ K₂) := by
    have := hNn k
    unfold padicPacketMuLog at this ⊢
    push_cast at this
    rw [← this]
    exact hmono
  refine ⟨h1, ?_⟩
  rw [tensorIdx_muLog_eq] at h1
  have hD : (0 : ℝ) < Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂) := by
    rw [padicVol_finrank_tensor p K₁ K₂]
    exact_mod_cast Nat.mul_pos Module.finrank_pos Module.finrank_pos
  have hn := tensorIdx_relIndex_ne_zero p K₁ K₂
  have hlog : Real.log ((tensorIdxRing p K₁ K₂).toAddSubgroup.relIndex
      (tensorIdxNormRing p K₁ K₂).toAddSubgroup) ≤
      Real.log ((p : ℝ) ^ (k * Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂))) := by
    rw [Real.log_pow]
    rw [le_div_iff₀ hD] at h1
    push_cast
    nlinarith
  have hpos : (0 : ℝ) < ((tensorIdxRing p K₁ K₂).toAddSubgroup.relIndex
      (tensorIdxNormRing p K₁ K₂).toAddSubgroup : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have := (Real.log_le_log_iff hpos (pow_pos (by exact_mod_cast hp.out.pos) _)).1 hlog
  exact_mod_cast this

end Measure

/-! ## `(R_E)^∼` is the normalization of `R_E` in its total ring of fractions -/

section Normalization

variable (p : ℕ) [hp : Fact p.Prime] (K₁ K₂ : Type*) [Field K₁] [Field K₂] [Algebra ℚ_[p] K₁]
  [Algebra ℚ_[p] K₂]

/-- **Integral over `R_E` if and only if integral over `ℤ_p`**: an element `z` of
`K₁ ⊗[ℚ_p] K₂` is a root of a monic polynomial with coefficients in `R_E` if and only if it lies
in `(R_E)^∼`. So `(R_E)^∼` is the integral closure of `R_E` in `K₁ ⊗[ℚ_p] K₂`. -/
theorem tensorIdx_isIntegralElem_iff (z : TensorProduct ℚ_[p] K₁ K₂) :
    (tensorIdxRing p K₁ K₂).subtype.IsIntegralElem z ↔ z ∈ tensorIdxNormRing p K₁ K₂ := by
  constructor
  · intro hz
    let _ : Algebra ℤ_[p] (TensorProduct ℚ_[p] K₁ K₂) :=
      Algebra.compHom (TensorProduct ℚ_[p] K₁ K₂) (algebraMap ℤ_[p] ℚ_[p])
    have hR : tensorIdxRing p K₁ K₂ ≤
        (integralClosure ℤ_[p] (TensorProduct ℚ_[p] K₁ K₂)).toSubring :=
      fun x hx => tensorIdxRing_le p K₁ K₂ hx
    obtain ⟨P, hP, h0⟩ := hz
    have hint : IsIntegral (integralClosure ℤ_[p] (TensorProduct ℚ_[p] K₁ K₂)) z :=
      ⟨P.map (Subring.inclusion hR), hP.map _, by rw [Polynomial.eval₂_map]; exact h0⟩
    exact isIntegral_trans (R := ℤ_[p]) z hint
  · intro hz
    obtain ⟨P, hP, h0⟩ := hz
    let ψ : ℤ_[p] →+* tensorIdxRing p K₁ K₂ :=
      ((algebraMap ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)).comp (algebraMap ℤ_[p] ℚ_[p])).codRestrict
        (tensorIdxRing p K₁ K₂) fun c => tensorIdx_algebraMap_mem p K₁ K₂ c
    exact ⟨P.map ψ, hP.map _, by rw [Polynomial.eval₂_map]; exact h0⟩

variable [FiniteDimensional ℚ_[p] K₁] [FiniteDimensional ℚ_[p] K₂]

/-- **Every element is `r / p ^ n` with `r ∈ R_E`**: for every `z` of `K₁ ⊗[ℚ_p] K₂` some
`p ^ n • z` lies in `R_E`. -/
theorem tensorIdx_exists_pow_smul_mem_ring (z : TensorProduct ℚ_[p] K₁ K₂) :
    ∃ n : ℕ, ((p : ℚ_[p]) ^ n) • z ∈ tensorIdxRing p K₁ K₂ := by
  have := volBridge_tensor_formallyUnramified p K₁ K₂
  obtain ⟨n, hn⟩ := packet_exists_pow_smul_mem p (TensorProduct ℚ_[p] K₁ K₂) z
  obtain ⟨k, hk⟩ := tensorIdx_exists_pow_smul_mem p K₁ K₂
  refine ⟨k + n, ?_⟩
  rw [pow_add, mul_smul]
  exact hk _ hn

omit [FiniteDimensional ℚ_[p] K₁] [FiniteDimensional ℚ_[p] K₂] in
/-- `p ^ n` (the image of the natural number) lies in `R_E` and is a unit of `K₁ ⊗ K₂`. -/
theorem tensorIdx_natCast_pow_mem (n : ℕ) :
    ((p : TensorProduct ℚ_[p] K₁ K₂)) ^ n ∈ tensorIdxRing p K₁ K₂ :=
  pow_mem (natCast_mem _ p) n

/-- **`K₁ ⊗[ℚ_p] K₂` is the total ring of fractions of `R_E`**: `IsFractionRing R_E (K₁ ⊗ K₂)`.
Nonzerodivisors of `R_E` are nonzerodivisors of `K₁ ⊗ K₂` (multiply by a power of `p`), hence
units (multiplication by them is an injective `ℚ_p`-linear endomorphism of a finite-dimensional
space); every element is `r / p ^ n`. With `tensorIdx_isIntegralElem_iff`, `(R_E)^∼` is the
normalization of `R_E` in its ring of fractions, the definition of page 9. -/
theorem tensorIdx_isFractionRing :
    IsFractionRing (tensorIdxRing p K₁ K₂) (TensorProduct ℚ_[p] K₁ K₂) := by
  have hpn : ∀ n : ℕ, ((p : ℚ_[p]) ^ n) ≠ 0 := fun n =>
    pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hsmul : ∀ (n : ℕ) (w : TensorProduct ℚ_[p] K₁ K₂),
      ((p : ℚ_[p]) ^ n) • w = ((p : TensorProduct ℚ_[p] K₁ K₂)) ^ n * w := by
    intro n w
    rw [Algebra.smul_def, map_pow, map_natCast]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨r, hr⟩
    have hinj : Function.Injective (LinearMap.mulLeft ℚ_[p] (r : TensorProduct ℚ_[p] K₁ K₂)) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro w hw
      obtain ⟨n, hn⟩ := tensorIdx_exists_pow_smul_mem_ring p K₁ K₂ w
      have h0 : r * ⟨_, hn⟩ = 0 := by
        apply Subtype.ext
        simp only [Subring.coe_mul, Subring.coe_zero]
        rw [mul_smul_comm]
        simp only [LinearMap.mulLeft_apply] at hw
        rw [hw, smul_zero]
      have h1 := (mem_nonZeroDivisors_iff.1 hr).1 _ h0
      have h2 : ((p : ℚ_[p]) ^ n) • w = 0 := congrArg Subtype.val h1
      exact (smul_eq_zero.1 h2).resolve_left (hpn n)
    obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective.1 hinj) 1
    exact isUnit_iff_exists_inv.2 ⟨w, hw⟩
  · intro z
    obtain ⟨n, hn⟩ := tensorIdx_exists_pow_smul_mem_ring p K₁ K₂ z
    have hd : (⟨_, tensorIdx_natCast_pow_mem p K₁ K₂ n⟩ : tensorIdxRing p K₁ K₂) ∈
        nonZeroDivisors (tensorIdxRing p K₁ K₂) := by
      rw [mem_nonZeroDivisors_iff]
      constructor
      · intro x hx
        have h := congrArg Subtype.val hx
        simp only [Subring.coe_mul, Subring.coe_zero, ← hsmul] at h
        exact Subtype.ext ((smul_eq_zero.1 h).resolve_left (hpn n))
      · intro x hx
        have h := congrArg Subtype.val hx
        simp only [Subring.coe_mul, Subring.coe_zero, mul_comm (x : TensorProduct ℚ_[p] K₁ K₂),
          ← hsmul] at h
        exact Subtype.ext ((smul_eq_zero.1 h).resolve_left (hpn n))
    refine ⟨(⟨_, hn⟩, ⟨_, hd⟩), ?_⟩
    show z * ((p : TensorProduct ℚ_[p] K₁ K₂)) ^ n = ((p : ℚ_[p]) ^ n) • z
    rw [hsmul, mul_comm]
  · intro x y h
    exact ⟨1, by rw [Subtype.ext (h : (x : TensorProduct ℚ_[p] K₁ K₂) = y)]⟩

end Normalization

/-! ## The equality case and the second factor -/

section Equality

variable (p : ℕ) [hp : Fact p.Prime] (K₁ K₂ : Type*) [Field K₁] [Field K₂] [Algebra ℚ_[p] K₁]
  [Algebra ℚ_[p] K₂]

/-- **`R_E = (R_E)^∼` when `K₂` is unramified over `ℚ_p`**: if the prime `P` of
`R₂ = integralClosure ℤ_[p] K₂` over `p` has ramification index `1`, the different of `R₂` is
trivial (`differentExponent = e − 1 = 0`, the tame case of Proposition 1.3 (i)), and
`p ^ 0 · (R_E)^∼ ⊆ R_E`. -/
theorem tensorIdx_eq_of_ramificationIdx_eq_one [FiniteDimensional ℚ_[p] K₂] [Algebra ℤ_[p] K₂]
    [IsScalarTower ℤ_[p] ℚ_[p] K₂] (P : Ideal (integralClosure ℤ_[p] K₂)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] (he : P.ramificationIdx ℤ_[p] = 1) :
    tensorIdxRing p K₁ K₂ = tensorIdxNormRing p K₁ K₂ := by
  refine le_antisymm (tensorIdxRing_le p K₁ K₂) fun z hz => ?_
  have hd := differentExponent_eq_of_not_dvd_ramificationIdx_padic p K₂ P
    (by rw [he]; exact hp.out.not_dvd_one)
  have h := tensorIdx_pow_smul_mem p K₁ K₂ P (k := 0) (by rw [hd, he]) hz
  simpa using h

/-- `comm : K₂ ⊗ K₁ → K₁ ⊗ K₂` maps `R_E` of `(K₂, K₁)` into `R_E` of `(K₁, K₂)`. -/
theorem tensorIdx_comm_mem {z : TensorProduct ℚ_[p] K₂ K₁} (hz : z ∈ tensorIdxRing p K₂ K₁) :
    Algebra.TensorProduct.comm ℚ_[p] K₂ K₁ z ∈ tensorIdxRing p K₁ K₂ := by
  rw [← SetLike.mem_coe, tensorIdxRing_coe] at hz ⊢
  unfold padicPacketIntegers at hz ⊢
  rw [SetLike.mem_coe] at hz ⊢
  induction hz using AddSubmonoid.closure_induction with
  | mem w hw =>
    obtain ⟨x, y, hx, hy, rfl⟩ := hw
    exact AddSubmonoid.subset_closure ⟨y, x, hy, hx, by simp⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb

/-- Exchanging the factors twice is the identity. -/
theorem tensorIdx_comm_comm (w : TensorProduct ℚ_[p] K₁ K₂) :
    Algebra.TensorProduct.comm ℚ_[p] K₂ K₁ (Algebra.TensorProduct.comm ℚ_[p] K₁ K₂ w) = w := by
  induction w using TensorProduct.inductionOn with
  | tmul x y => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- **`p ^ ⌈𝔡_1⌉ · (R_E)^∼ ⊆ R_E`**, the inclusion of Proposition 1.1 with `* = 2`, `I* = {1}`:
the different of the first factor, by exchanging the factors. -/
theorem tensorIdx_ceil_smul_mem_left [FiniteDimensional ℚ_[p] K₁] [Algebra ℤ_[p] K₁]
    [IsScalarTower ℤ_[p] ℚ_[p] K₁] (P : Ideal (integralClosure ℤ_[p] K₁)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    {z : TensorProduct ℚ_[p] K₁ K₂} (hz : z ∈ tensorIdxNormRing p K₁ K₂) :
    letI := isDedekindDomain_ringOfIntegers_padic p K₁
    letI := isTorsionFree_ringOfIntegers_padic p K₁
    ((p : ℚ_[p]) ^ ⌈differentOrder ℤ_[p] (integralClosure ℤ_[p] K₁) P⌉₊) • z ∈
      tensorIdxRing p K₁ K₂ := by
  have h1 : Algebra.TensorProduct.comm ℚ_[p] K₁ K₂ z ∈ tensorIdxNormRing p K₂ K₁ :=
    padicVolIntegral_map p (Algebra.TensorProduct.comm ℚ_[p] K₁ K₂).toAlgHom hz
  have h2 := tensorIdx_comm_mem p K₁ K₂ (tensorIdx_ceil_smul_mem p K₂ K₁ P h1)
  rwa [map_smul, tensorIdx_comm_comm] at h2

/-- **`R_E = (R_E)^∼` when `K₁` is unramified over `ℚ_p`**, by exchanging the factors. -/
theorem tensorIdx_eq_of_ramificationIdx_eq_one_left [FiniteDimensional ℚ_[p] K₁]
    [Algebra ℤ_[p] K₁] [IsScalarTower ℤ_[p] ℚ_[p] K₁] (P : Ideal (integralClosure ℤ_[p] K₁))
    [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (he : P.ramificationIdx ℤ_[p] = 1) :
    tensorIdxRing p K₁ K₂ = tensorIdxNormRing p K₁ K₂ := by
  refine le_antisymm (tensorIdxRing_le p K₁ K₂) fun z hz => ?_
  have h1 : Algebra.TensorProduct.comm ℚ_[p] K₁ K₂ z ∈ tensorIdxNormRing p K₂ K₁ :=
    padicVolIntegral_map p (Algebra.TensorProduct.comm ℚ_[p] K₁ K₂).toAlgHom hz
  rw [← tensorIdx_eq_of_ramificationIdx_eq_one p K₂ K₁ P he] at h1
  have h2 := tensorIdx_comm_mem p K₁ K₂ h1
  rwa [tensorIdx_comm_comm] at h2

end Equality

/-! ## The bounds with the orders of the differents -/

section Bounds

variable (p : ℕ) [hp : Fact p.Prime] (K₁ K₂ : Type*) [Field K₁] [Field K₂] [Algebra ℚ_[p] K₁]
  [Algebra ℚ_[p] K₂] [FiniteDimensional ℚ_[p] K₁] [FiniteDimensional ℚ_[p] K₂]
  [MeasurableSpace (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) → ℚ_[p])]
  [BorelSpace (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) → ℚ_[p])]
  (μ : Measure (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) → ℚ_[p]))
  [μ.IsAddHaarMeasure]

/-- **`−⌈𝔡_2⌉ log p ≤ μ^log(R_E) ≤ 0`**, and `[(R_E)^∼ : R_E] ≤ p ^ (⌈𝔡_2⌉ · dim (K₁ ⊗ K₂))`,
with `𝔡_2` the order of the different of `R₂` at the prime `P` over `p`. -/
theorem tensorIdx_muLog_bounds [Algebra ℤ_[p] K₂] [IsScalarTower ℤ_[p] ℚ_[p] K₂]
    (P : Ideal (integralClosure ℤ_[p] K₂)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    letI := isDedekindDomain_ringOfIntegers_padic p K₂
    letI := isTorsionFree_ringOfIntegers_padic p K₂;
    -((⌈differentOrder ℤ_[p] (integralClosure ℤ_[p] K₂) P⌉₊ : ℝ) * Real.log p) ≤
        padicPacketMuLog p (TensorProduct ℚ_[p] K₁ K₂) μ (padicPacketNormalization p K₁ K₂)
          (padicPacketIntegers p K₁ K₂) ∧
      padicPacketMuLog p (TensorProduct ℚ_[p] K₁ K₂) μ (padicPacketNormalization p K₁ K₂)
          (padicPacketIntegers p K₁ K₂) ≤ 0 ∧
      (tensorIdxRing p K₁ K₂).toAddSubgroup.relIndex (tensorIdxNormRing p K₁ K₂).toAddSubgroup ≤
        p ^ (⌈differentOrder ℤ_[p] (integralClosure ℤ_[p] K₂) P⌉₊ *
          Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) := by
  let := isDedekindDomain_ringOfIntegers_padic p K₂
  let := isTorsionFree_ringOfIntegers_padic p K₂
  obtain ⟨h1, h2⟩ := tensorIdx_muLog_ge_of_pow p K₁ K₂ μ
    (fun z hz => tensorIdx_ceil_smul_mem p K₁ K₂ P hz)
  exact ⟨h1, tensorIdx_muLog_nonpos p K₁ K₂ μ, h2⟩

/-- **The same with the first factor**: `−⌈𝔡_1⌉ log p ≤ μ^log(R_E)` and
`[(R_E)^∼ : R_E] ≤ p ^ (⌈𝔡_1⌉ · dim (K₁ ⊗ K₂))`. -/
theorem tensorIdx_muLog_bounds_left [Algebra ℤ_[p] K₁] [IsScalarTower ℤ_[p] ℚ_[p] K₁]
    (P : Ideal (integralClosure ℤ_[p] K₁)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    letI := isDedekindDomain_ringOfIntegers_padic p K₁
    letI := isTorsionFree_ringOfIntegers_padic p K₁;
    -((⌈differentOrder ℤ_[p] (integralClosure ℤ_[p] K₁) P⌉₊ : ℝ) * Real.log p) ≤
        padicPacketMuLog p (TensorProduct ℚ_[p] K₁ K₂) μ (padicPacketNormalization p K₁ K₂)
          (padicPacketIntegers p K₁ K₂) ∧
      (tensorIdxRing p K₁ K₂).toAddSubgroup.relIndex (tensorIdxNormRing p K₁ K₂).toAddSubgroup ≤
        p ^ (⌈differentOrder ℤ_[p] (integralClosure ℤ_[p] K₁) P⌉₊ *
          Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) := by
  let := isDedekindDomain_ringOfIntegers_padic p K₁
  let := isTorsionFree_ringOfIntegers_padic p K₁
  exact tensorIdx_muLog_ge_of_pow p K₁ K₂ μ
    (fun z hz => tensorIdx_ceil_smul_mem_left p K₁ K₂ P hz)

omit [BorelSpace (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K₁ K₂)) → ℚ_[p])]
  [μ.IsAddHaarMeasure] in
/-- **The equality case for the log-volume**: if `R_E = (R_E)^∼` (for example when one factor is
unramified, `tensorIdx_eq_of_ramificationIdx_eq_one`), the index is `1` and `μ^log(R_E) = 0`. -/
theorem tensorIdx_muLog_eq_zero_of_eq (h : tensorIdxRing p K₁ K₂ = tensorIdxNormRing p K₁ K₂) :
    (tensorIdxRing p K₁ K₂).toAddSubgroup.relIndex (tensorIdxNormRing p K₁ K₂).toAddSubgroup = 1 ∧
      padicPacketMuLog p (TensorProduct ℚ_[p] K₁ K₂) μ (padicPacketNormalization p K₁ K₂)
        (padicPacketIntegers p K₁ K₂) = 0 := by
  refine ⟨by rw [h]; exact AddSubgroup.relIndex_self _, ?_⟩
  rw [← tensorIdxRing_coe, h, tensorIdxNormRing_coe]
  exact padicPacketMuLog_self p μ _

end Bounds

/-! ## A ramified example: `K₁ = K₂ = K` with `[K : ℚ_p] = 2` and `π ^ 2 = p` -/

section Example

variable (p : ℕ) [hp : Fact p.Prime]

/-- `p` has no square root in `ℚ_p`. -/
theorem tensorIdxEx_not_sq (x : ℚ_[p]) : x ^ 2 ≠ (p : ℚ_[p]) := by
  intro hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hx
    exact hp.out.ne_zero (by exact_mod_cast hx.symm)
  have h := congrArg norm hx
  rw [norm_pow, Padic.norm_eq_zpow_neg_valuation hx0, Padic.norm_p, ← zpow_natCast,
    ← zpow_mul, ← zpow_neg_one] at h
  have := zpow_right_injective₀ (by exact_mod_cast hp.out.pos : (0 : ℝ) < p)
    (by exact_mod_cast hp.out.one_lt.ne' : (p : ℝ) ≠ 1) h
  omega

variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

/-- **The `π`-coordinate of an integral element is integral**: if `π ^ 2 = p` in `K` and
`a + b π` (with `a`, `b ∈ ℚ_p`) is integral over `ℤ_p`, then `‖b‖ ≤ 1`. For the spectral norm,
`‖a‖ ∈ p ^ ℤ` and `‖b π‖ ∈ p ^ (ℤ + 1/2)` differ unless both vanish, so
`‖a + b π‖ = max ‖a‖ ‖b π‖ ≥ ‖b‖ p ^ (−1/2)`. -/
theorem tensorIdxEx_coeff_le_one {π : K} (hπ : π ^ 2 = algebraMap ℚ_[p] K p) {a b : ℚ_[p]}
    (h : padicVolIntegral p (algebraMap ℚ_[p] K a + algebraMap ℚ_[p] K b * π)) : ‖b‖ ≤ 1 := by
  rw [volBridge_padicVolIntegral_iff] at h
  let _ := spectralNorm.normedField ℚ_[p] K
  let _ := spectralNorm.normedAlgebra ℚ_[p] K
  have : IsUltrametricDist K := extLog_isUltrametricDist p
  change ‖algebraMap ℚ_[p] K a + algebraMap ℚ_[p] K b * π‖ ≤ 1 at h
  have hP : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hP1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hπn : ‖π‖ ^ 2 = (p : ℝ) ^ (-1 : ℤ) := by
    rw [← norm_pow, hπ, norm_algebraMap', Padic.norm_p, zpow_neg_one]
  by_contra hb
  rw [not_le] at hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hb
    linarith
  have hbv := Padic.norm_eq_zpow_neg_valuation hb0
  have hbn : ‖algebraMap ℚ_[p] K b * π‖ ^ 2 = (p : ℝ) ^ (-b.valuation * 2 + -1) := by
    rw [norm_mul, mul_pow, norm_algebraMap', hπn, hbv, ← zpow_natCast, ← zpow_mul,
      ← zpow_add₀ hP.ne']
    norm_num
  have hv : 1 ≤ -b.valuation := by
    by_contra hv
    rw [not_le] at hv
    have : ‖b‖ ≤ 1 := by
      rw [hbv]
      exact zpow_le_one_of_nonpos₀ hP1.le (by omega)
    linarith
  have hne : ‖algebraMap ℚ_[p] K a‖ ≠ ‖algebraMap ℚ_[p] K b * π‖ := by
    intro he
    have h2 : ‖algebraMap ℚ_[p] K a‖ ^ 2 = ‖algebraMap ℚ_[p] K b * π‖ ^ 2 := by rw [he]
    rw [hbn, norm_algebraMap'] at h2
    by_cases ha0 : a = 0
    · rw [ha0, norm_zero, zero_pow two_ne_zero] at h2
      exact (zpow_pos hP _).ne' h2.symm
    · rw [Padic.norm_eq_zpow_neg_valuation ha0, ← zpow_natCast, ← zpow_mul] at h2
      have := zpow_right_injective₀ hP hP1.ne' h2
      omega
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne] at h
  have h2 : ‖algebraMap ℚ_[p] K b * π‖ ^ 2 ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) ((le_max_right _ _).trans h)
  rw [hbn] at h2
  have h3 : (1 : ℝ) < (p : ℝ) ^ (-b.valuation * 2 + -1) := one_lt_zpow₀ hP1 (by omega)
  linarith

variable (hK : Module.finrank ℚ_[p] K = 2) {π : K} (hπ : π ^ 2 = algebraMap ℚ_[p] K p)
include hK hπ

/-- `1, π` is a `ℚ_p`-basis of `K`. -/
noncomputable def tensorIdxExBasis : Module.Basis (Fin 2) ℚ_[p] K :=
  basisOfLinearIndependentOfCardEqFinrank
    (LinearIndependent.pair_iff.2 fun s t hst => by
      by_cases ht : t = 0
      · subst ht
        rw [zero_smul, add_zero, smul_eq_zero] at hst
        exact ⟨hst.resolve_right one_ne_zero, rfl⟩
      · exfalso
        have hπ' : π = algebraMap ℚ_[p] K (-s / t) := by
          rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
          rw [map_div₀, map_neg, eq_div_iff ((map_ne_zero _).2 ht), mul_comm]
          exact (eq_neg_of_add_eq_zero_right hst)
        rw [hπ', ← map_pow] at hπ
        exact tensorIdxEx_not_sq p _ ((algebraMap ℚ_[p] K).injective hπ))
    (by rw [Fintype.card_fin, hK])

theorem tensorIdxExBasis_apply (i : Fin 2) :
    tensorIdxExBasis p hK hπ i = ![1, π] i := by
  simp [tensorIdxExBasis]

/-- The `π`-coordinate functional `a + b π ↦ b`. -/
noncomputable def tensorIdxExCoord : K →ₗ[ℚ_[p]] ℚ_[p] := (tensorIdxExBasis p hK hπ).coord 1

/-- The coordinate of an integral element is in `ℤ_p`. -/
theorem tensorIdxExCoord_le_one {x : K} (hx : padicVolIntegral p x) :
    ‖tensorIdxExCoord p hK hπ x‖ ≤ 1 := by
  set B := tensorIdxExBasis p hK hπ
  have hx' : x = algebraMap ℚ_[p] K (B.repr x 0) + algebraMap ℚ_[p] K (B.repr x 1) * π := by
    conv_lhs => rw [← B.sum_repr x]
    rw [Fin.sum_univ_two, tensorIdxExBasis_apply, tensorIdxExBasis_apply, Algebra.smul_def,
      Algebra.smul_def]
    simp
  rw [hx'] at hx
  exact tensorIdxEx_coeff_le_one p hπ hx

omit [FiniteDimensional ℚ_[p] K] hK in
/-- `u = p⁻¹ (π ⊗ π)` satisfies `u * u = 1`. -/
theorem tensorIdxEx_unit_mul_self :
    ((p : ℚ_[p])⁻¹ • TensorProduct.tmul ℚ_[p] π π) *
        ((p : ℚ_[p])⁻¹ • TensorProduct.tmul ℚ_[p] π π) = (1 : TensorProduct ℚ_[p] K K) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hππ : π * π = algebraMap ℚ_[p] K p := by rw [← sq, hπ]
  rw [smul_mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, hππ,
    Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul_smul, smul_smul,
    ← Algebra.TensorProduct.one_def]
  rw [show (p : ℚ_[p])⁻¹ * (p : ℚ_[p])⁻¹ * ((p : ℚ_[p]) * (p : ℚ_[p])) = 1 by field_simp,
    one_smul]

omit [FiniteDimensional ℚ_[p] K] in
omit hK in
/-- `u = p⁻¹ (π ⊗ π)` lies in `(R_E)^∼`: it is a root of `X ^ 2 − 1`. -/
theorem tensorIdxEx_unit_mem :
    (p : ℚ_[p])⁻¹ • TensorProduct.tmul ℚ_[p] π π ∈ tensorIdxNormRing p K K := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 two_ne_zero, ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, map_one, sq,
    tensorIdxEx_unit_mul_self p hπ, sub_self]

/-- The functional `x ⊗ y ↦ b(x) b(y)` on `K ⊗ K`, with `b` the `π`-coordinate. -/
noncomputable def tensorIdxExForm : TensorProduct ℚ_[p] K K →ₗ[ℚ_[p]] ℚ_[p] :=
  TensorProduct.lift ((LinearMap.mul ℚ_[p] ℚ_[p]).compl₁₂ (tensorIdxExCoord p hK hπ)
    (tensorIdxExCoord p hK hπ))

theorem tensorIdxExForm_tmul (x y : K) :
    tensorIdxExForm p hK hπ (TensorProduct.tmul ℚ_[p] x y) =
      tensorIdxExCoord p hK hπ x * tensorIdxExCoord p hK hπ y := by
  simp [tensorIdxExForm]

/-- The functional is `ℤ_p`-valued on `R_E`. -/
theorem tensorIdxExForm_le_one {z : TensorProduct ℚ_[p] K K}
    (hz : z ∈ padicPacketIntegers p K K) : ‖tensorIdxExForm p hK hπ z‖ ≤ 1 := by
  unfold padicPacketIntegers at hz
  rw [SetLike.mem_coe] at hz
  induction hz using AddSubmonoid.closure_induction with
  | mem w hw =>
    obtain ⟨x, y, hx, hy, rfl⟩ := hw
    rw [tensorIdxExForm_tmul, norm_mul]
    exact (mul_le_mul (tensorIdxExCoord_le_one p hK hπ hx) (tensorIdxExCoord_le_one p hK hπ hy)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add]
    exact (Padic.nonarchimedean _ _).trans (max_le ha hb)

theorem tensorIdxExCoord_pi : tensorIdxExCoord p hK hπ π = 1 := by
  have h : tensorIdxExBasis p hK hπ 1 = π := by rw [tensorIdxExBasis_apply]; rfl
  have h1 := (tensorIdxExBasis p hK hπ).repr_self 1
  rw [h] at h1
  rw [tensorIdxExCoord, Module.Basis.coord_apply, h1, Finsupp.single_eq_same]

/-- **`R_E ≠ (R_E)^∼` for `K₁ = K₂ = K`, `[K : ℚ_p] = 2`, `π ^ 2 = p`** (any prime `p`):
`u = p⁻¹ (π ⊗ π)` is integral (`u ^ 2 = 1`) but the functional `x ⊗ y ↦ b(x) b(y)`, which is
`ℤ_p`-valued on `R_E`, takes the value `p⁻¹` at `u`. -/
theorem tensorIdxEx_ne : tensorIdxRing p K K ≠ tensorIdxNormRing p K K := by
  intro h
  have hu := tensorIdxEx_unit_mem p hπ
  rw [← h, ← SetLike.mem_coe, tensorIdxRing_coe] at hu
  have h1 := tensorIdxExForm_le_one p hK hπ hu
  rw [map_smul, tensorIdxExForm_tmul, tensorIdxExCoord_pi, mul_one, smul_eq_mul, mul_one,
    norm_inv, Padic.norm_p, inv_inv] at h1
  have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  linarith

/-- **In the example the index is at least `2` and `μ^log(R_E) < 0`.** -/
theorem tensorIdxEx_muLog_neg
    [MeasurableSpace (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K K)) → ℚ_[p])]
    [BorelSpace (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K K)) → ℚ_[p])]
    (μ : Measure (Fin (Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K K)) → ℚ_[p]))
    [μ.IsAddHaarMeasure] :
    2 ≤ (tensorIdxRing p K K).toAddSubgroup.relIndex (tensorIdxNormRing p K K).toAddSubgroup ∧
      padicPacketMuLog p (TensorProduct ℚ_[p] K K) μ (padicPacketNormalization p K K)
        (padicPacketIntegers p K K) < 0 := by
  have hn0 := tensorIdx_relIndex_ne_zero p K K
  have hn1 : (tensorIdxRing p K K).toAddSubgroup.relIndex
      (tensorIdxNormRing p K K).toAddSubgroup ≠ 1 := by
    rw [Ne, AddSubgroup.relIndex_eq_one]
    intro hle
    exact tensorIdxEx_ne p hK hπ (le_antisymm (tensorIdxRing_le p K K) fun z hz => hle hz)
  have h2 : 2 ≤ (tensorIdxRing p K K).toAddSubgroup.relIndex
      (tensorIdxNormRing p K K).toAddSubgroup := by omega
  refine ⟨h2, ?_⟩
  rw [tensorIdx_muLog_eq]
  have hD : (0 : ℝ) < Module.finrank ℚ_[p] (TensorProduct ℚ_[p] K K) := by
    rw [padicVol_finrank_tensor p K K, hK]
    norm_num
  have hlog : 0 < Real.log ((tensorIdxRing p K K).toAddSubgroup.relIndex
      (tensorIdxNormRing p K K).toAddSubgroup) :=
    Real.log_pos (by exact_mod_cast h2)
  exact div_neg_of_neg_of_pos (by linarith) hD

end Example

/-- **The example exists**: there is a field `K`, finite-dimensional of degree `2` over `ℚ_p`,
with an element `π` such that `π ^ 2 = p` (namely `ℚ_p[X] / (X ^ 2 − p)`; `X ^ 2 − p` is
irreducible since `p` is not a square in `ℚ_p`). So the hypotheses of `tensorIdxEx_ne` and
`tensorIdxEx_muLog_neg` are satisfiable. -/
theorem tensorIdxEx_exists (p : ℕ) [hp : Fact p.Prime] :
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ_[p] K) (_ : FiniteDimensional ℚ_[p] K),
      Module.finrank ℚ_[p] K = 2 ∧ ∃ π : K, π ^ 2 = algebraMap ℚ_[p] K p := by
  have hdeg : (Polynomial.X ^ 2 - Polynomial.C (p : ℚ_[p])).natDegree = 2 :=
    Polynomial.natDegree_X_pow_sub_C _
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C (p : ℚ_[p])) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [hdeg]
      decide
    · intro x hx
      rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C, sub_eq_zero] at hx
      exact tensorIdxEx_not_sq p x hx
  have : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (p : ℚ_[p]))) := ⟨hirr⟩
  have hne : Polynomial.X ^ 2 - Polynomial.C (p : ℚ_[p]) ≠ 0 := hirr.ne_zero
  refine ⟨AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (p : ℚ_[p])), inferInstance, inferInstance,
    (AdjoinRoot.powerBasis hne).finite, ?_, AdjoinRoot.root _, ?_⟩
  · rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  · have h := AdjoinRoot.eval₂_root (Polynomial.X ^ 2 - Polynomial.C (p : ℚ_[p]))
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero] at h
    rw [h, AdjoinRoot.algebraMap_eq]

end IUT.PaperIV.LocalFields
