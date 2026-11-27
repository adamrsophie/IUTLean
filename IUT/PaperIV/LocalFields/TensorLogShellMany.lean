import IUT.PaperIV.LocalFields.TensorDifferentMany
import IUT.PaperIV.LocalFields.TensorLogShell
import IUT.PaperIV.Theorem1_10.StepsIVtoVII

/-!
# Log-shells of packets with any finite number of factors (IUT IV, Propositions 1.2 and 1.4)

Source: IUT IV, Proposition 1.2 (page 10) with its proof (page 11), Proposition 1.4 (page 13)
with its proof (pages 13 and 14), and Step (vi) of the proof of Theorem 1.10 (page 29, with the
setting of pages 28 and 30). Pages read for this file: 10, 11, 13, 14, 28, 29 and 30. Pages
checked against rendered images: 10, 11, 13, 14, 28, 29 and 30.

For finite extensions `K_i`, `i ∈ I`, of `ℚ_p` (abstract fields, `I` any finite type), the packet
is `⊗_{i ∈ I} K_i` over `ℚ_p` (`PiTensorProduct`), `R_I` is `tdManyIntegers` and `(R_I)^∼` is
`packetNormalizationSet` (the elements integral over `ℤ_p`). This file defines

* `tlsmLattice`: `log_p(R_I^×) = ⊗_i log_p(R_i^×)`, read as the `ℤ_p`-span of the pure tensors
  `⊗_i log_p(u_i)` in the packet;
* `tlsmShift`: `p ^ λ · (R_I)^∼`, represented as `(⊗_i x_i) · (R_I)^∼` with
  `∏_i ‖x_i‖ = p ^ (−λ)` (spectral norms);
* `tlsmDiffSum`, `tlsmASum`, `tlsmBSum`: `𝔡_I`, `a_I`, `b_I`.

and proves, for every finite `I`: Proposition 1.2 (ii) (`tlsm_prop1_2_ii`, `tlsm_prop1_2_ii_zero`),
(iii) (`tlsm_prop1_2_iii`, `tlsm_prop1_2_iii_zero`) and (iv) (`tlsm_prop1_2_iv`); the span of
`log_p(R_I^×)` over `ℚ_p` is the packet (`tlsm_span_lattice`); Proposition 1.4 (i)
(`tlsm_prop1_4_i`) and (iv) (`tlsm_prop1_4_iv`); and Step (vi) of Theorem 1.10 for every `j`
(`IUT.PaperIV.Theorem1_10.tlsm_stepVI`).

The key new step is `tlsm_tprod_mem_normalization`: a pure tensor `⊗_i x_i` with
`∏_i ‖x_i‖ ≤ 1` is integral over `ℤ_p`, although single factors may have norm larger than one.
The chain of the first display of the proof of Proposition 1.2 (ii) uses Proposition 1.1 for
any number of factors (`tdMany_order_mul_mem_integers`) and Proposition 1.2 (i) on each factor.

Not covered here: identity (A) of page 14 and the index of a tensor product of `n` lattices,
hence the first inequality of Proposition 1.4 (iii) for `n` factors (these three are proved in
`IUT.PaperIV.LocalFields.TensorAdditivityMany`: `tam_muLog_logLattice`, `tam_relIndex`,
`tam_prop1_4_iii_first`); Proposition 1.4 (ii); the
injectivity of `⊗_{ℤ_p} log_p(R_i^×)` into the packet (the lattice is taken as its image); and the
identification of these statements, for a two-element `I`, with the binary `tensorLog_…`
theorems.
-/

open MeasureTheory IUT.Prerequisites.PadicVolume
open scoped Pointwise

namespace IUT.PaperIV.LocalFields

/-! ## Elementary helpers -/

section Helpers

/-- `∏_{i ∈ s} a ^ (n i) = a ^ (∑_{i ∈ s} n i)` in a field, for `a ≠ 0`. -/
theorem tlsm_prod_zpow {κ F : Type*} [Field F] {a : F} (ha : a ≠ 0) (s : Finset κ)
    (n : κ → ℤ) : ∏ i ∈ s, a ^ n i = a ^ ∑ i ∈ s, n i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ ha]

variable (p : ℕ) [hp : Fact p.Prime] (L : Type*) [Field L] [Algebra ℚ_[p] L]
  [FiniteDimensional ℚ_[p] L]

/-- The spectral norm is multiplicative. -/
theorem tlsm_sn_mul (x y : L) :
    spectralNorm ℚ_[p] L (x * y) = spectralNorm ℚ_[p] L x * spectralNorm ℚ_[p] L y := by
  let _ := spectralNorm.normedField ℚ_[p] L
  exact norm_mul x y

/-- The spectral norm of a quotient. -/
theorem tlsm_sn_div (x y : L) :
    spectralNorm ℚ_[p] L (x / y) = spectralNorm ℚ_[p] L x / spectralNorm ℚ_[p] L y := by
  let _ := spectralNorm.normedField ℚ_[p] L
  exact norm_div x y

/-- The spectral norm of a power. -/
theorem tlsm_sn_pow (x : L) (n : ℕ) :
    spectralNorm ℚ_[p] L (x ^ n) = spectralNorm ℚ_[p] L x ^ n := by
  let _ := spectralNorm.normedField ℚ_[p] L
  exact norm_pow x n

/-- The spectral norm of `1`. -/
theorem tlsm_sn_one : spectralNorm ℚ_[p] L 1 = 1 := by
  let _ := spectralNorm.normedField ℚ_[p] L
  exact (norm_one : ‖(1 : L)‖ = 1)

/-- The spectral norm of `0`. -/
theorem tlsm_sn_zero : spectralNorm ℚ_[p] L 0 = 0 := by
  let _ := spectralNorm.normedField ℚ_[p] L
  exact (norm_zero : ‖(0 : L)‖ = 0)

/-- The spectral norm of a nonzero element is positive. -/
theorem tlsm_sn_pos {x : L} (hx : x ≠ 0) : 0 < spectralNorm ℚ_[p] L x := by
  let _ := spectralNorm.normedField ℚ_[p] L
  exact norm_pos_iff.2 hx

/-- The spectral norm is nonnegative. -/
theorem tlsm_sn_nonneg (x : L) : 0 ≤ spectralNorm ℚ_[p] L x := by
  let _ := spectralNorm.normedField ℚ_[p] L
  exact norm_nonneg x

/-- The spectral norm of `p ^ k · x`. -/
theorem tlsm_sn_zpow_smul (k : ℤ) (x : L) :
    spectralNorm ℚ_[p] L (((p : ℚ_[p]) ^ k) • x) =
      (p : ℝ) ^ (-(k : ℝ)) * spectralNorm ℚ_[p] L x :=
  tensorLog_norm_p_zpow_smul p L k x

/-- An element of spectral norm at most one is integral over `ℤ_p`. -/
theorem tlsm_integral_of_sn_le_one {x : L} (hx : spectralNorm ℚ_[p] L x ≤ 1) :
    padicVolIntegral p x := by
  let _ : Algebra ℤ_[p] L := ((algebraMap ℚ_[p] L).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra
  have : IsScalarTower ℤ_[p] ℚ_[p] L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (padicBridge_norm_le_one_iff_isIntegral p L x).1 hx

end Helpers

/-! ## Finite étale `ℚ_p`-algebras: closure properties of `(R_E)^∼` -/

section Etale

variable (p : ℕ) [hp : Fact p.Prime] {W : Type*} [CommRing W] [Algebra ℚ_[p] W]

/-- `(R_E)^∼` is closed under multiplication. -/
theorem tlsm_mul_mem {z w : W} (hz : z ∈ packetNormalizationSet p W)
    (hw : w ∈ packetNormalizationSet p W) : z * w ∈ packetNormalizationSet p W :=
  RingHom.IsIntegralElem.mul _ hz hw

/-- `(R_E)^∼` is closed under addition. -/
theorem tlsm_add_mem {z w : W} (hz : z ∈ packetNormalizationSet p W)
    (hw : w ∈ packetNormalizationSet p W) : z + w ∈ packetNormalizationSet p W :=
  RingHom.IsIntegralElem.add _ hz hw

/-- `(R_E)^∼` is a `ℤ_p`-module. -/
theorem tlsm_smul_mem (a : ℤ_[p]) {w : W} (hw : w ∈ packetNormalizationSet p W) :
    (a : ℚ_[p]) • w ∈ packetNormalizationSet p W := by
  set φ := (algebraMap ℚ_[p] W).comp (algebraMap ℤ_[p] ℚ_[p])
  have h1 : (a : ℚ_[p]) • w = φ a * w := by
    rw [Algebra.smul_def]
    rfl
  show φ.IsIntegralElem _
  rw [h1]
  exact RingHom.IsIntegralElem.mul φ φ.isIntegralElem_map hw

end Etale

/-! ## Pure tensors in `(R_I)^∼` and the sets `p ^ λ · (R_I)^∼` -/

section Pure

variable (p : ℕ) [hp : Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] (K : ι → Type)
  [∀ i, Field (K i)] [∀ i, Algebra ℚ_[p] (K i)] [∀ i, FiniteDimensional ℚ_[p] (K i)]

omit [DecidableEq ι] in
/-- **A pure tensor `⊗_i x_i` with `∏_i ‖x_i‖ ≤ 1` lies in `(R_I)^∼`**, although single factors
may have norm larger than one: a power of `⊗_i x_i` is `p ^ m · (⊗_i u_i)` with `m ≥ 0` and every
`‖u_i‖ = 1`, and an element with an integral power is integral. -/
theorem tlsm_tprod_mem_normalization {x : ∀ i, K i}
    (h : ∏ i, spectralNorm ℚ_[p] (K i) (x i) ≤ 1) :
    PiTensorProduct.tprod ℚ_[p] x ∈ packetNormalizationSet p (PiTensorProduct ℚ_[p] K) := by
  by_cases hx : ∃ i, x i = 0
  · obtain ⟨i, hi⟩ := hx
    rw [(PiTensorProduct.tprod ℚ_[p]).map_coord_zero i hi]
    exact packet_zero_mem_normalization p _
  push Not at hx
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpq : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have he : ∀ i, ∃ e : ℕ, 0 < e ∧ ∃ k : ℤ, spectralNorm ℚ_[p] (K i) (x i) ^ e = (p : ℝ) ^ k :=
    fun i => by
      let _ : Algebra ℤ_[p] (K i) :=
        ((algebraMap ℚ_[p] (K i)).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra
      have : IsScalarTower ℤ_[p] ℚ_[p] (K i) := IsScalarTower.of_algebraMap_eq fun _ => rfl
      exact tensorLog_norm_pow_eq_zpow p (K i) (hx i)
  choose e he k hk using he
  set N : ℕ := ∏ i, e i with hN
  have hN0 : 0 < N := Finset.prod_pos fun i _ => he i
  have hdvd : ∀ i, ∃ q : ℕ, N = e i * q := fun i => Finset.dvd_prod_of_mem e (Finset.mem_univ i)
  choose q hq using hdvd
  set m : ι → ℤ := fun i => k i * q i with hm
  have hxN : ∀ i, spectralNorm ℚ_[p] (K i) (x i ^ N) = (p : ℝ) ^ m i := by
    intro i
    rw [tlsm_sn_pow, hq i, pow_mul, hk i, ← zpow_natCast, ← zpow_mul]
  set u : ∀ i, K i := fun i => ((p : ℚ_[p]) ^ m i) • x i ^ N with hu
  have hu1 : ∀ i, spectralNorm ℚ_[p] (K i) (u i) = 1 := by
    intro i
    show spectralNorm ℚ_[p] (K i) (((p : ℚ_[p]) ^ m i) • x i ^ N) = 1
    rw [tlsm_sn_zpow_smul, hxN, ← Real.rpow_intCast, ← Real.rpow_add hp0, neg_add_cancel,
      Real.rpow_zero]
  have hxu : ∀ i, x i ^ N = ((p : ℚ_[p]) ^ (-m i)) • u i := by
    intro i
    show _ = _ • (((p : ℚ_[p]) ^ m i) • x i ^ N)
    rw [smul_smul, ← zpow_add₀ hpq, neg_add_cancel, zpow_zero, one_smul]
  have htp : PiTensorProduct.tprod ℚ_[p] x ^ N =
      (∏ i, (p : ℚ_[p]) ^ (-m i)) • PiTensorProduct.tprod ℚ_[p] u := by
    have h1 : PiTensorProduct.tprod ℚ_[p] x ^ N = PiTensorProduct.tprod ℚ_[p] (x ^ N) :=
      (map_pow (PiTensorProduct.tprodMonoidHom ℚ_[p] (A := K)) x N).symm
    have h2 : x ^ N = fun i => ((p : ℚ_[p]) ^ (-m i)) • u i :=
      funext fun i => by rw [Pi.pow_apply, hxu i]
    rw [h1, h2, MultilinearMap.map_smul_univ]
    rfl
  have hsum : 0 ≤ ∑ i, -m i := by
    have h3 : (∏ i, spectralNorm ℚ_[p] (K i) (x i)) ^ N = (p : ℝ) ^ (∑ i, (m i : ℝ)) := by
      rw [← Finset.prod_pow, Real.rpow_sum_of_pos hp0]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← tlsm_sn_pow, hxN, Real.rpow_intCast]
    have h4 : (∏ i, spectralNorm ℚ_[p] (K i) (x i)) ^ N ≤ 1 :=
      pow_le_one₀ (Finset.prod_nonneg fun i _ => tlsm_sn_nonneg p (K i) _) h
    rw [h3] at h4
    have h5 : ∑ i, (m i : ℝ) ≤ 0 := by
      by_contra hc
      exact absurd h4 (not_le.2 (Real.one_lt_rpow hp1 (lt_of_not_ge hc)))
    have h6 : ∑ i, m i ≤ 0 := by exact_mod_cast h5
    rw [Finset.sum_neg_distrib]
    omega
  have hint : padicVolIntegral p (PiTensorProduct.tprod ℚ_[p] x ^ N) := by
    rw [htp, tlsm_prod_zpow hpq]
    obtain ⟨M, hM⟩ := Int.eq_ofNat_of_zero_le hsum
    rw [hM, zpow_natCast]
    exact packet_pow_smul_mem_normalization p _ (tdMany_tprod_integral p K fun i =>
      tlsm_integral_of_sn_le_one p (K i) (hu1 i).le) M
  let _ : Algebra ℤ_[p] (PiTensorProduct ℚ_[p] K) :=
    Algebra.compHom _ (algebraMap ℤ_[p] ℚ_[p])
  exact IsIntegral.of_pow (R := ℤ_[p]) hN0 hint

/-- **`p ^ λ · (R_I)^∼`** of IUT IV pages 10 and 11 for any finite number of factors, represented
by a pure tensor `⊗_i x_i` with `∏_i ‖x_i‖ = p ^ (−λ)`: the set `(⊗_i x_i) · (R_I)^∼`. By
`tlsmShift_subset` it depends only on `∏_i ‖x_i‖`; for `λ ∈ (1 / e_i) ℤ` the page's
`p ^ λ · (R_I)^∼` is `tlsmShift` of the family with `x_i = p ^ λ` and `x_j = 1` for `j ≠ i`. -/
noncomputable def tlsmShift (x : ∀ i, K i) : Set (PiTensorProduct ℚ_[p] K) :=
  (fun z => PiTensorProduct.tprod ℚ_[p] x * z) '' packetNormalizationSet p (PiTensorProduct ℚ_[p] K)

omit [DecidableEq ι] in
/-- **Monotonicity and independence of the choices**: if `∏_i ‖x_i‖ ≤ ∏_i ‖x'_i‖` with every
`x'_i` nonzero, then `(⊗_i x_i) · (R_I)^∼ ⊆ (⊗_i x'_i) · (R_I)^∼`. -/
theorem tlsmShift_subset {x x' : ∀ i, K i} (hx' : ∀ i, x' i ≠ 0)
    (h : ∏ i, spectralNorm ℚ_[p] (K i) (x i) ≤ ∏ i, spectralNorm ℚ_[p] (K i) (x' i)) :
    tlsmShift p K x ⊆ tlsmShift p K x' := by
  rintro _ ⟨z, hz, rfl⟩
  have hpos : 0 < ∏ i, spectralNorm ℚ_[p] (K i) (x' i) :=
    Finset.prod_pos fun i _ => tlsm_sn_pos p (K i) (hx' i)
  refine ⟨PiTensorProduct.tprod ℚ_[p] (fun i => x i / x' i) * z,
    tlsm_mul_mem p (tlsm_tprod_mem_normalization p K ?_) hz, ?_⟩
  · simp only [tlsm_sn_div]
    rw [Finset.prod_div_distrib, div_le_one hpos]
    exact h
  · show PiTensorProduct.tprod ℚ_[p] x' * (PiTensorProduct.tprod ℚ_[p] (fun i => x i / x' i) * z) =
      PiTensorProduct.tprod ℚ_[p] x * z
    rw [← mul_assoc, PiTensorProduct.tprod_mul_tprod]
    congr 2
    funext i
    exact mul_div_cancel₀ (x i) (hx' i)

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℚ_[p] (K i)] in
/-- `p ^ 0 · (R_I)^∼ = (R_I)^∼`. -/
theorem tlsmShift_one :
    tlsmShift p K 1 = packetNormalizationSet p (PiTensorProduct ℚ_[p] K) := by
  unfold tlsmShift
  rw [← PiTensorProduct.one_def]
  simp

omit [Fintype ι] [∀ i, FiniteDimensional ℚ_[p] (K i)] in
/-- A scalar of `ℚ_p` moves into the factor `s`: `c · (⊗_i x_i) = ⊗_i x'_i` with
`x'_s = c · x_s` and `x'_i = x_i` otherwise. -/
theorem tlsm_tprod_update_smul (s : ι) (c : ℚ_[p]) (x : ∀ i, K i) :
    PiTensorProduct.tprod ℚ_[p] (Function.update x s (c • x s)) =
      c • PiTensorProduct.tprod ℚ_[p] x := by
  rw [(PiTensorProduct.tprod ℚ_[p]).map_update_smul x s c (x s), Function.update_eq_self]
  rfl

omit [Fintype ι] [∀ i, FiniteDimensional ℚ_[p] (K i)] in
/-- Scalars of `ℚ_p` move into the factor `s`: `c · ((⊗_i x_i) · (R_I)^∼) =
(⊗_i x'_i) · (R_I)^∼`, with `x'_s = c · x_s`. -/
theorem tlsmShift_smul (s : ι) (c : ℚ_[p]) (x : ∀ i, K i) :
    c • tlsmShift p K x = tlsmShift p K (Function.update x s (c • x s)) := by
  unfold tlsmShift
  rw [← Set.image_smul, Set.image_image]
  congr 1
  funext z
  rw [tlsm_tprod_update_smul, smul_mul_assoc]

omit [∀ i, FiniteDimensional ℚ_[p] (K i)] in
/-- The norm product after changing the factor `s`: if `‖y‖ = c · ‖x_s‖`, then
`∏_i ‖x'_i‖ = c · ∏_i ‖x_i‖` for `x'_s = y`, `x'_i = x_i` otherwise. -/
theorem tlsm_prod_update (s : ι) (x : ∀ i, K i) (y : K s) (c : ℝ)
    (hy : spectralNorm ℚ_[p] (K s) y = c * spectralNorm ℚ_[p] (K s) (x s)) :
    ∏ i, spectralNorm ℚ_[p] (K i) (Function.update x s y i) =
      c * ∏ i, spectralNorm ℚ_[p] (K i) (x i) := by
  have h1 : (fun i => spectralNorm ℚ_[p] (K i) (Function.update x s y i)) =
      Function.update (fun i => spectralNorm ℚ_[p] (K i) (x i)) s (spectralNorm ℚ_[p] (K s) y) :=
    funext fun i => Function.apply_update (fun i => spectralNorm ℚ_[p] (K i)) x s y i
  rw [show (∏ i, spectralNorm ℚ_[p] (K i) (Function.update x s y i)) =
      ∏ i, Function.update (fun i => spectralNorm ℚ_[p] (K i) (x i)) s
        (spectralNorm ℚ_[p] (K s) y) i from congrArg (fun f => ∏ i, f i) h1,
    Finset.prod_update_of_mem (Finset.mem_univ s), Finset.sdiff_singleton_eq_erase, hy,
    ← Finset.mul_prod_erase Finset.univ (fun i => spectralNorm ℚ_[p] (K i) (x i))
      (Finset.mem_univ s)]
  ring

end Pure

/-! ## The lattice `log_p(R_I^×)` and Proposition 1.2 (ii) to (iv) -/

section Lattice

variable (p : ℕ) [hp : Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] (K : ι → Type)
  [∀ i, Field (K i)] [∀ i, Algebra ℚ_[p] (K i)] [∀ i, FiniteDimensional ℚ_[p] (K i)]
  [∀ i, Algebra ℤ_[p] (K i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (K i)]

/-- **`log_p(R_I^×) = ⊗_{i ∈ I} log_p(R_i^×)`** (IUT IV page 10) for any finite number of factors,
as its image in the packet `⊗_i K_i` over `ℚ_p`: the additive span of the `a · (⊗_i x_i)` with
`a ∈ ℤ_p` and every `x_i ∈ log_p(R_i^×)` (that is, the `ℤ_p`-span of the pure tensors of
logarithms of units). -/
noncomputable def tlsmLattice : Set (PiTensorProduct ℚ_[p] K) :=
  ((AddSubmonoid.closure {w | ∃ (a : ℤ_[p]) (x : ∀ i, K i),
      (∀ i, x i ∈ tensorLogUnits p (K i)) ∧ w = (a : ℚ_[p]) • PiTensorProduct.tprod ℚ_[p] x} :
    AddSubmonoid (PiTensorProduct ℚ_[p] K)) : Set (PiTensorProduct ℚ_[p] K))

variable (P : ∀ i, Ideal (integralClosure ℤ_[p] (K i))) [∀ i, (P i).IsPrime]
  [∀ i, (P i).LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]

/-- `𝔡_I = ∑_{i ∈ I} 𝔡_i`, with `𝔡_i = differentOrder` at `P_i` (`tensorLogDiffOrder`). -/
noncomputable def tlsmDiffSum : ℝ := ∑ i, tensorLogDiffOrder p (K i) (P i)

/-- `a_I = ∑_{i ∈ I} a_i`, with `a_i = Proposition1_2.a p e_i`. -/
noncomputable def tlsmASum : ℝ := ∑ i, Proposition1_2.a p ((P i).ramificationIdx ℤ_[p])

/-- `b_I = ∑_{i ∈ I} b_i`, with `b_i = Proposition1_2.b p e_i`. -/
noncomputable def tlsmBSum : ℝ := ∑ i, Proposition1_2.b p ((P i).ramificationIdx ℤ_[p])

/-- **The first display of the proof of Proposition 1.2 (ii)** (page 11), for any finite
number of factors: for `u_i` with `ord(u_i) = a_i` and `⊗_i x_i` with
`∏_i ‖x_i‖ ≤ p ^ (−(𝔡_I + a_I))`, `(⊗_i x_i) · (R_I)^∼ ⊆ (⊗_i u_i) · R_I`, the image of
`⊗_i p ^ (a_i) · R_i`. The proof uses Proposition 1.1 (`tdMany_order_mul_mem_integers`, with
any index `s` as the page's `*`) and `𝔡_s ≥ 0`. -/
theorem tlsm_shift_subset_integers (s : ι) {u x : ∀ i, K i}
    (hu : ∀ i, spectralNorm ℚ_[p] (K i) (u i) =
      (p : ℝ) ^ (-Proposition1_2.a p ((P i).ramificationIdx ℤ_[p])))
    (h : ∏ i, spectralNorm ℚ_[p] (K i) (x i) ≤
      (p : ℝ) ^ (-(tlsmDiffSum p K P + tlsmASum p K P))) :
    tlsmShift p K x ⊆
      (fun w => PiTensorProduct.tprod ℚ_[p] u * w) '' tdManyIntegers p K := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hd : ∀ i, ∃ d : K i, d ≠ 0 ∧
      spectralNorm ℚ_[p] (K i) d = (p : ℝ) ^ (-tensorLogDiffOrder p (K i) (P i)) := by
    intro i
    let _ := isDedekindDomain_ringOfIntegers_padic p (K i)
    let _ := isTorsionFree_ringOfIntegers_padic p (K i)
    obtain ⟨d, hd0, hd⟩ := padicBridge_exists_norm_eq_rpow p (K i) (P i)
      (-((differentExponent ℤ_[p] (integralClosure ℤ_[p] (K i)) (P i) : ℕ) : ℤ))
    refine ⟨d, hd0, ?_⟩
    have hd' : spectralNorm ℚ_[p] (K i) d = _ := hd
    rw [hd']
    congr 1
    unfold tensorLogDiffOrder differentOrder
    push_cast
    ring
  choose d hd0 hd using hd
  have hδs : Function.update d s 1 s = 1 := Function.update_self s 1 d
  have hδ0 : ∀ i, Function.update d s 1 i ≠ 0 := by
    intro i
    by_cases hi : i = s
    · subst hi
      rw [hδs]
      exact one_ne_zero
    · rw [Function.update_of_ne hi]
      exact hd0 i
  have hu0 : ∀ i, u i ≠ 0 := by
    intro i h0
    have h1 := hu i
    rw [h0, tlsm_sn_zero] at h1
    exact (Real.rpow_pos_of_pos hp0 _).ne' h1.symm
  have hU : ∏ i, spectralNorm ℚ_[p] (K i) (u i) = (p : ℝ) ^ (-tlsmASum p K P) := by
    rw [Finset.prod_congr rfl fun i _ => hu i, ← Real.rpow_sum_of_pos hp0, tlsmASum,
      Finset.sum_neg_distrib]
  have hD : (p : ℝ) ^ (-tlsmDiffSum p K P) ≤
      ∏ i, spectralNorm ℚ_[p] (K i) (Function.update d s 1 i) := by
    rw [tlsmDiffSum, ← Finset.sum_neg_distrib, Real.rpow_sum_of_pos hp0]
    refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
    by_cases hi : i = s
    · subst hi
      rw [hδs, tlsm_sn_one]
      exact Real.rpow_le_one_of_one_le_of_nonpos hp1
        (neg_nonpos.2 (tensorLogDiffOrder_nonneg p (K i) (P i)))
    · rw [Function.update_of_ne hi, hd i]
  have hUpos : 0 < ∏ i, spectralNorm ℚ_[p] (K i) (u i) :=
    Finset.prod_pos fun i _ => tlsm_sn_pos p (K i) (hu0 i)
  have hDpos : 0 < ∏ i, spectralNorm ℚ_[p] (K i) (Function.update d s 1 i) :=
    Finset.prod_pos fun i _ => tlsm_sn_pos p (K i) (hδ0 i)
  have hy : ∏ i, spectralNorm ℚ_[p] (K i) (x i / (u i * Function.update d s 1 i)) ≤ 1 := by
    simp only [tlsm_sn_div, tlsm_sn_mul]
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, div_le_one (mul_pos hUpos hDpos)]
    refine h.trans ?_
    rw [neg_add, Real.rpow_add hp0, mul_comm, hU]
    exact mul_le_mul_of_nonneg_left hD (Real.rpow_pos_of_pos hp0 _).le
  have hδ : ∀ i, i ≠ s → (letI := isDedekindDomain_ringOfIntegers_padic p (K i);
      letI := isTorsionFree_ringOfIntegers_padic p (K i);
      letI := spectralNorm.normedField ℚ_[p] (K i);
      ‖Function.update d s 1 i‖ =
        (p : ℝ) ^ (-differentOrder ℤ_[p] (integralClosure ℤ_[p] (K i)) (P i))) := by
    intro i hi
    show spectralNorm ℚ_[p] (K i) (Function.update d s 1 i) =
      (p : ℝ) ^ (-tensorLogDiffOrder p (K i) (P i))
    rw [Function.update_of_ne hi]
    exact hd i
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨PiTensorProduct.tprod ℚ_[p] (Function.update d s 1) *
      (PiTensorProduct.tprod ℚ_[p] (fun i => x i / (u i * Function.update d s 1 i)) * z),
    tdMany_order_mul_mem_integers p K s P _ hδs hδ
      (tlsm_mul_mem p (tlsm_tprod_mem_normalization p K hy) hz), ?_⟩
  show PiTensorProduct.tprod ℚ_[p] u * (PiTensorProduct.tprod ℚ_[p] (Function.update d s 1) *
      (PiTensorProduct.tprod ℚ_[p] (fun i => x i / (u i * Function.update d s 1 i)) * z)) =
    PiTensorProduct.tprod ℚ_[p] x * z
  rw [← mul_assoc, ← mul_assoc, PiTensorProduct.tprod_mul_tprod, PiTensorProduct.tprod_mul_tprod]
  congr 2
  funext i
  exact mul_div_cancel₀ (x i) (mul_ne_zero (hu0 i) (hδ0 i))

omit [Fintype ι] [DecidableEq ι] in
/-- **`⊗_i p ^ (a_i) · R_i ⊆ log_p(R_I^×)`** for any finite number of factors: for `u_i` with
`ord(u_i) = a_i`, the image `(⊗_i u_i) · R_I` lies in `log_p(R_I^×)`, by Proposition 1.2 (i) on
each factor. -/
theorem tlsm_mul_integers_subset_lattice {u : ∀ i, K i}
    (hu : ∀ i, spectralNorm ℚ_[p] (K i) (u i) =
      (p : ℝ) ^ (-Proposition1_2.a p ((P i).ramificationIdx ℤ_[p]))) :
    (fun w => PiTensorProduct.tprod ℚ_[p] u * w) '' tdManyIntegers p K ⊆ tlsmLattice p K := by
  have hS : ∀ i, Set.range (fun r : integralClosure ℤ_[p] (K i) => u i * (r : K i)) ⊆
      tensorLogUnits p (K i) := by
    intro i
    obtain ⟨-, ⟨z, hz⟩, H⟩ := padicBridge_extLogUnit_image_fractionalIdeal p (K i) (P i)
    exact (H (u i) z (hu i) hz).1
  rintro _ ⟨w, hw, rfl⟩
  unfold tdManyIntegers at hw
  rw [SetLike.mem_coe] at hw
  unfold tlsmLattice
  rw [SetLike.mem_coe]
  induction hw using AddSubmonoid.closure_induction with
  | mem w hw =>
    obtain ⟨y, hy, rfl⟩ := hw
    refine AddSubmonoid.subset_closure ⟨1, u * y, fun i => hS i
      ⟨⟨y i, (tensorDiff_padicVolIntegral_iff p (K i) _).1 (hy i)⟩, rfl⟩, ?_⟩
    beta_reduce
    rw [PiTensorProduct.tprod_mul_tprod]
    simp
  | zero =>
    beta_reduce
    rw [mul_zero]
    exact zero_mem _
  | add a b _ _ ha hb =>
    beta_reduce at ha hb ⊢
    rw [mul_add]
    exact add_mem ha hb

omit [DecidableEq ι] in
/-- **`log_p(R_I^×) ⊆ p ^ (−b_I) · (R_I)^∼`** for any finite number of factors (the last inclusion
of the first display of Proposition 1.2 (ii), page 10): for `z_i` with `ord(z_i) = −b_i`, every
element of `log_p(R_I^×)` is `(⊗_i z_i) · w` with `w ∈ (R_I)^∼`, by Proposition 1.2 (i) on each
factor. -/
theorem tlsm_lattice_subset_shift {z : ∀ i, K i}
    (hz : ∀ i, spectralNorm ℚ_[p] (K i) (z i) =
      (p : ℝ) ^ Proposition1_2.b p ((P i).ramificationIdx ℤ_[p])) :
    tlsmLattice p K ⊆ tlsmShift p K z := by
  have hT : ∀ i, tensorLogUnits p (K i) ⊆
      Set.range (fun r : integralClosure ℤ_[p] (K i) => z i * (r : K i)) := by
    intro i
    obtain ⟨⟨y, hy⟩, -, H⟩ := padicBridge_extLogUnit_image_fractionalIdeal p (K i) (P i)
    exact (H y (z i) hy (hz i)).2
  intro w hw
  unfold tlsmLattice at hw
  rw [SetLike.mem_coe] at hw
  induction hw using AddSubmonoid.closure_induction with
  | mem w hw =>
    obtain ⟨a, x, hx, rfl⟩ := hw
    have hr : ∀ i, ∃ r : integralClosure ℤ_[p] (K i), z i * (r : K i) = x i :=
      fun i => hT i (hx i)
    choose r hr using hr
    refine ⟨(a : ℚ_[p]) • PiTensorProduct.tprod ℚ_[p] (fun i => (r i : K i)),
      tlsm_smul_mem p a (tdMany_tprod_integral p K fun i =>
        (tensorDiff_padicVolIntegral_iff p (K i) _).2 (r i).2), ?_⟩
    show PiTensorProduct.tprod ℚ_[p] z *
        ((a : ℚ_[p]) • PiTensorProduct.tprod ℚ_[p] (fun i => (r i : K i))) =
      (a : ℚ_[p]) • PiTensorProduct.tprod ℚ_[p] x
    rw [mul_smul_comm, PiTensorProduct.tprod_mul_tprod]
    congr 2
    funext i
    exact hr i
  | zero => exact ⟨0, packet_zero_mem_normalization p _, mul_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨n, hn, rfl⟩ := ha
    obtain ⟨n', hn', rfl⟩ := hb
    exact ⟨n + n', tlsm_add_mem p hn hn', mul_add _ _ _⟩

/-- **`p ^ (𝔡_I + a_I) · (R_I)^∼ ⊆ log_p(R_I^×)`** for any finite number of factors (page 11, from
the first display and Proposition 1.2 (i)): every `(⊗_i x_i) · (R_I)^∼` with
`∏_i ‖x_i‖ ≤ p ^ (−(𝔡_I + a_I))` lies in `log_p(R_I^×)`. -/
theorem tlsm_shift_subset_lattice (s : ι) {x : ∀ i, K i}
    (h : ∏ i, spectralNorm ℚ_[p] (K i) (x i) ≤
      (p : ℝ) ^ (-(tlsmDiffSum p K P + tlsmASum p K P))) :
    tlsmShift p K x ⊆ tlsmLattice p K := by
  have hu : ∀ i, ∃ u : K i, spectralNorm ℚ_[p] (K i) u =
      (p : ℝ) ^ (-Proposition1_2.a p ((P i).ramificationIdx ℤ_[p])) := by
    intro i
    obtain ⟨⟨u, hu⟩, -, -⟩ := padicBridge_extLogUnit_image_fractionalIdeal p (K i) (P i)
    exact ⟨u, hu⟩
  choose u hu using hu
  exact (tlsm_shift_subset_integers p K P s hu h).trans (tlsm_mul_integers_subset_lattice p K P hu)

omit [Fintype ι] [DecidableEq ι] in
/-- Representatives `z_i` of `p ^ (−b_i)`: elements with `‖z_i‖ = p ^ (b_i)`. -/
theorem tlsm_exists_b :
    ∃ z : ∀ i, K i, ∀ i, spectralNorm ℚ_[p] (K i) (z i) =
      (p : ℝ) ^ Proposition1_2.b p ((P i).ramificationIdx ℤ_[p]) := by
  have hz : ∀ i, ∃ z : K i, spectralNorm ℚ_[p] (K i) z =
      (p : ℝ) ^ Proposition1_2.b p ((P i).ramificationIdx ℤ_[p]) := by
    intro i
    obtain ⟨-, ⟨z, hz⟩, -⟩ := padicBridge_extLogUnit_image_fractionalIdeal p (K i) (P i)
    exact ⟨z, hz⟩
  choose z hz using hz
  exact ⟨z, hz⟩

omit [DecidableEq ι] [∀ i, FiniteDimensional ℚ_[p] (K i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (K i)]
  [∀ i, (P i).IsPrime] [∀ i, (P i).LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] in
/-- `∏_i ‖z_i‖ = p ^ (b_I)` for representatives of `p ^ (−b_i)`. -/
theorem tlsm_prod_b {z : ∀ i, K i}
    (hz : ∀ i, spectralNorm ℚ_[p] (K i) (z i) =
      (p : ℝ) ^ Proposition1_2.b p ((P i).ramificationIdx ℤ_[p])) :
    ∏ i, spectralNorm ℚ_[p] (K i) (z i) = (p : ℝ) ^ tlsmBSum p K P := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  rw [Finset.prod_congr rfl fun i _ => hz i, ← Real.rpow_sum_of_pos hp0, tlsmBSum]

/-- **IUT IV Proposition 1.2 (ii) for any finite number of factors** (page 10, proof on page 11).
Let `φ` be a `ℚ_p`-linear automorphism of the packet `⊗_i K_i` (the `ℚ_p`-span of
`log_p(R_I^×)`, `tlsm_span_lattice`) mapping `log_p(R_I^×)` onto itself. For every real `λ`,
every `⊗_i t_i` with `∏_i ‖t_i‖ = p ^ (−λ)` (for `λ ∈ (1 / e_i) ℤ` this is `p ^ λ` taken in the
factor `i`) and every `z_i` with `ord(z_i) = −b_i`:
`φ(p ^ λ · (R_I)^∼) ⊆ p ^ ⌊λ − 𝔡_I − a_I⌋ · log_p(R_I^×) ⊆
p ^ ⌊λ − 𝔡_I − a_I⌋ · (p ^ (−b_I) · (R_I)^∼)`. The index set is nonempty (the page has
`|I| ≥ 2`). -/
theorem tlsm_prop1_2_ii [Nonempty ι]
    (φ : PiTensorProduct ℚ_[p] K ≃ₗ[ℚ_[p]] PiTensorProduct ℚ_[p] K)
    (hφ : φ '' tlsmLattice p K = tlsmLattice p K) (lam : ℝ) {t : ∀ i, K i}
    (ht : ∏ i, spectralNorm ℚ_[p] (K i) (t i) = (p : ℝ) ^ (-lam)) {z : ∀ i, K i}
    (hz : ∀ i, spectralNorm ℚ_[p] (K i) (z i) =
      (p : ℝ) ^ Proposition1_2.b p ((P i).ramificationIdx ℤ_[p])) :
    φ '' tlsmShift p K t ⊆
        ((p : ℚ_[p]) ^ ⌊lam - tlsmDiffSum p K P - tlsmASum p K P⌋) • tlsmLattice p K ∧
      ((p : ℚ_[p]) ^ ⌊lam - tlsmDiffSum p K P - tlsmASum p K P⌋) • tlsmLattice p K ⊆
        ((p : ℚ_[p]) ^ ⌊lam - tlsmDiffSum p K P - tlsmASum p K P⌋) • tlsmShift p K z := by
  obtain ⟨s⟩ := ‹Nonempty ι›
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hpq : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set k := ⌊lam - tlsmDiffSum p K P - tlsmASum p K P⌋ with hk
  have hkle : (k : ℝ) ≤ lam - tlsmDiffSum p K P - tlsmASum p K P := Int.floor_le _
  have hS : tlsmShift p K (Function.update t s (((p : ℚ_[p]) ^ (-k)) • t s)) ⊆
      tlsmLattice p K := by
    refine tlsm_shift_subset_lattice p K P s ?_
    rw [tlsm_prod_update p K s t _ _ (tlsm_sn_zpow_smul p (K s) (-k) (t s)), ht,
      ← Real.rpow_add hp0]
    apply Real.rpow_le_rpow_of_exponent_le hp1
    push_cast
    linarith
  have heq : tlsmShift p K t =
      ((p : ℚ_[p]) ^ k) • tlsmShift p K (Function.update t s (((p : ℚ_[p]) ^ (-k)) • t s)) := by
    rw [tlsmShift_smul p K s, Function.update_idem, Function.update_self, smul_smul,
      ← zpow_add₀ hpq, add_neg_cancel, zpow_zero, one_smul, Function.update_eq_self]
  refine ⟨?_, Set.smul_set_mono (tlsm_lattice_subset_shift p K P hz)⟩
  rw [heq, padicVol_image_smul p φ]
  have h := Set.smul_set_mono (a := (p : ℚ_[p]) ^ k) (Set.image_mono (f := φ) hS)
  rwa [hφ] at h

/-- **IUT IV Proposition 1.2 (ii), "in particular"**, for any finite number of factors
(page 10), `λ = 0`: `φ((R_I)^∼) ⊆ p ^ (−⌈𝔡_I + a_I⌉) · log_p(R_I^×) ⊆
p ^ (−⌈𝔡_I + a_I⌉) · (p ^ (−b_I) · (R_I)^∼)`. -/
theorem tlsm_prop1_2_ii_zero [Nonempty ι]
    (φ : PiTensorProduct ℚ_[p] K ≃ₗ[ℚ_[p]] PiTensorProduct ℚ_[p] K)
    (hφ : φ '' tlsmLattice p K = tlsmLattice p K) {z : ∀ i, K i}
    (hz : ∀ i, spectralNorm ℚ_[p] (K i) (z i) =
      (p : ℝ) ^ Proposition1_2.b p ((P i).ramificationIdx ℤ_[p])) :
    φ '' packetNormalizationSet p (PiTensorProduct ℚ_[p] K) ⊆
        ((p : ℚ_[p]) ^ (-⌈tlsmDiffSum p K P + tlsmASum p K P⌉)) • tlsmLattice p K ∧
      ((p : ℚ_[p]) ^ (-⌈tlsmDiffSum p K P + tlsmASum p K P⌉)) • tlsmLattice p K ⊆
        ((p : ℚ_[p]) ^ (-⌈tlsmDiffSum p K P + tlsmASum p K P⌉)) • tlsmShift p K z := by
  have h := tlsm_prop1_2_ii p K P φ hφ 0 (t := 1)
    (by simp only [Pi.one_apply, tlsm_sn_one, Finset.prod_const_one, neg_zero, Real.rpow_zero])
    hz
  rwa [tlsmShift_one, zero_sub, ← neg_add', Int.floor_neg] at h

/-- **IUT IV Proposition 1.2 (iii) for any finite number of factors** (page 11): if `p > 2` and
`e_i ≤ p − 2` for all `i ∈ I`, then `φ(p ^ λ · (R_I)^∼) ⊆ p ^ (λ − 𝔡_I − 1) · (R_I)^∼` for every
real `λ`, every `⊗_i t_i` with `∏_i ‖t_i‖ = p ^ (−λ)`, and every representative `⊗_i w_i` of
`p ^ (λ − 𝔡_I − 1)`. -/
theorem tlsm_prop1_2_iii [Nonempty ι] (hp2 : 2 < p)
    (he : ∀ i, (P i).ramificationIdx ℤ_[p] ≤ p - 2)
    (φ : PiTensorProduct ℚ_[p] K ≃ₗ[ℚ_[p]] PiTensorProduct ℚ_[p] K)
    (hφ : φ '' tlsmLattice p K = tlsmLattice p K) (lam : ℝ) {t : ∀ i, K i}
    (ht : ∏ i, spectralNorm ℚ_[p] (K i) (t i) = (p : ℝ) ^ (-lam)) {w : ∀ i, K i}
    (hw : ∏ i, spectralNorm ℚ_[p] (K i) (w i) =
      (p : ℝ) ^ (-(lam - tlsmDiffSum p K P - 1))) :
    φ '' tlsmShift p K t ⊆ tlsmShift p K w := by
  obtain ⟨s⟩ := ‹Nonempty ι›
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  obtain ⟨z, hz⟩ := tlsm_exists_b p K P
  have hii := tlsm_prop1_2_ii p K P φ hφ lam ht hz
  have h := hii.1.trans hii.2
  rw [tlsmShift_smul p K s] at h
  have hwpos : 0 < ∏ i, spectralNorm ℚ_[p] (K i) (w i) := hw ▸ Real.rpow_pos_of_pos hp0 _
  have hw0 : ∀ i, w i ≠ 0 := by
    intro i h0
    have h1 : ∏ i, spectralNorm ℚ_[p] (K i) (w i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h0, tlsm_sn_zero])
    linarith
  refine h.trans (tlsmShift_subset p K hw0 ?_)
  rw [tlsm_prod_update p K s z _ _ (tlsm_sn_zpow_smul p (K s) _ (z s)), tlsm_prod_b p K P hz, hw,
    ← Real.rpow_add hp0]
  apply Real.rpow_le_rpow_of_exponent_le hp1
  have hab : tlsmASum p K P = -tlsmBSum p K P := by
    rw [tlsmASum, tlsmBSum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h2 := Proposition1_2.a_b_of_le hp2 (tensorLog_one_le_ramificationIdx p (K i) (P i)) (he i)
    rw [h2.1, h2.2, neg_neg]
  have hf := Proposition1_2.iii_floor (lam - tlsmDiffSum p K P) (tlsmASum p K P)
    (tlsmBSum p K P) hab
  linarith

/-- **IUT IV Proposition 1.2 (iii), "in particular"**, for any finite number of factors
(page 11): under the same hypotheses, `φ((R_I)^∼) ⊆ p ^ (−𝔡_I − 1) · (R_I)^∼`. -/
theorem tlsm_prop1_2_iii_zero [Nonempty ι] (hp2 : 2 < p)
    (he : ∀ i, (P i).ramificationIdx ℤ_[p] ≤ p - 2)
    (φ : PiTensorProduct ℚ_[p] K ≃ₗ[ℚ_[p]] PiTensorProduct ℚ_[p] K)
    (hφ : φ '' tlsmLattice p K = tlsmLattice p K) {w : ∀ i, K i}
    (hw : ∏ i, spectralNorm ℚ_[p] (K i) (w i) = (p : ℝ) ^ (tlsmDiffSum p K P + 1)) :
    φ '' packetNormalizationSet p (PiTensorProduct ℚ_[p] K) ⊆ tlsmShift p K w := by
  rw [← tlsmShift_one]
  refine tlsm_prop1_2_iii p K P hp2 he φ hφ 0
    (by simp only [Pi.one_apply, tlsm_sn_one, Finset.prod_const_one, neg_zero, Real.rpow_zero]) ?_
  rw [hw]
  congr 1
  ring

omit [DecidableEq ι] in
/-- `𝔡_I = 0`, `a_I = |I|` and `b_I = −|I|` when `p > 2` and every `e_i = 1`. -/
theorem tlsm_sums_of_e_one (hp2 : 2 < p) (he : ∀ i, (P i).ramificationIdx ℤ_[p] = 1) :
    tlsmDiffSum p K P = 0 ∧ tlsmASum p K P = Fintype.card ι ∧
      tlsmBSum p K P = -(Fintype.card ι : ℝ) := by
  have hnd : ¬ p ∣ 1 := fun h => (Nat.le_of_dvd one_pos h).not_gt hp.out.one_lt
  have hab := Proposition1_2.a_b_of_e_one hp2
  refine ⟨Finset.sum_eq_zero fun i _ => ?_, ?_, ?_⟩
  · have h := differentOrder_eq_of_not_dvd_ramificationIdx_padic p (K i) (P i)
      (by rw [he i]; exact hnd)
    unfold tensorLogDiffOrder
    rw [h, he i]
    norm_num
  · rw [tlsmASum, Finset.sum_congr rfl fun i _ => by rw [he i, hab.1]]
    simp
  · rw [tlsmBSum, Finset.sum_congr rfl fun i _ => by rw [he i, hab.2]]
    simp

/-- **IUT IV Proposition 1.2 (iv) for any finite number of factors** (page 11): if `p > 2` and
`e_i = 1` for all `i ∈ I`, then `φ((R_I)^∼) ⊆ (R_I)^∼`. Here `𝔡_I = 0` (Proposition 1.3 (i),
equality case, `differentOrder_eq_of_not_dvd_ramificationIdx_padic`) and `a_I = −b_I = |I|`. -/
theorem tlsm_prop1_2_iv [Nonempty ι] (hp2 : 2 < p) (he : ∀ i, (P i).ramificationIdx ℤ_[p] = 1)
    (φ : PiTensorProduct ℚ_[p] K ≃ₗ[ℚ_[p]] PiTensorProduct ℚ_[p] K)
    (hφ : φ '' tlsmLattice p K = tlsmLattice p K) :
    φ '' packetNormalizationSet p (PiTensorProduct ℚ_[p] K) ⊆
      packetNormalizationSet p (PiTensorProduct ℚ_[p] K) := by
  obtain ⟨s⟩ := ‹Nonempty ι›
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  obtain ⟨hD, hA, hB⟩ := tlsm_sums_of_e_one p K P hp2 he
  obtain ⟨z, hz⟩ := tlsm_exists_b p K P
  have hii := tlsm_prop1_2_ii_zero p K P φ hφ hz
  have h := hii.1.trans hii.2
  rw [tlsmShift_smul p K s] at h
  refine h.trans ((tlsmShift_subset p K (x' := 1) (fun _ => one_ne_zero) ?_).trans
    (tlsmShift_one p K).subset)
  rw [tlsm_prod_update p K s z _ _ (tlsm_sn_zpow_smul p (K s) _ (z s)), tlsm_prod_b p K P hz,
    ← Real.rpow_add hp0, hD, hA, hB]
  simp only [Pi.one_apply, tlsm_sn_one, Finset.prod_const_one, zero_add, Int.ceil_natCast]
  rw [show (-(((-(Fintype.card ι : ℤ) : ℤ)) : ℝ) + -(Fintype.card ι : ℝ)) = 0 by push_cast; ring,
    Real.rpow_zero]

include P in
/-- **`log_p(R_I^×) ⊗ ℚ_p = ⊗_i K_i`** for any finite number of factors: the `ℚ_p`-span of
`log_p(R_I^×)` is the whole packet, so the automorphisms `φ` of Proposition 1.2 are `ℚ_p`-linear
automorphisms of `⊗_i K_i`. -/
theorem tlsm_span_lattice [Nonempty ι] :
    Submodule.span ℚ_[p] (tlsmLattice p K) = ⊤ := by
  obtain ⟨s⟩ := ‹Nonempty ι›
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hpq : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  obtain ⟨M, hM⟩ := exists_nat_ge (tlsmDiffSum p K P + tlsmASum p K P)
  have hsub : ((p : ℚ_[p]) ^ (M : ℤ)) • packetNormalizationSet p (PiTensorProduct ℚ_[p] K) ⊆
      tlsmLattice p K := by
    rw [← tlsmShift_one, tlsmShift_smul p K s]
    refine tlsm_shift_subset_lattice p K P s ?_
    rw [tlsm_prod_update p K s 1 _ _ (tlsm_sn_zpow_smul p (K s) _ _)]
    simp only [Pi.one_apply, tlsm_sn_one, Finset.prod_const_one, mul_one]
    apply Real.rpow_le_rpow_of_exponent_le hp1
    push_cast
    linarith
  have hspan := (packet_normalization_lattice_tensor p K).2.2
  rw [eq_top_iff, ← hspan, Submodule.span_le]
  intro n hn
  have hmem : ((p : ℚ_[p]) ^ (M : ℤ)) • n ∈ tlsmLattice p K :=
    hsub (Set.smul_mem_smul_set hn)
  have hn' : n = ((p : ℚ_[p]) ^ (M : ℤ))⁻¹ • (((p : ℚ_[p]) ^ (M : ℤ)) • n) := by
    rw [smul_smul, inv_mul_cancel₀ (zpow_ne_zero _ hpq), one_smul]
  rw [SetLike.mem_coe, hn']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end Lattice

/-! ## Proposition 1.4 (i) and (iv), and Step (vi) of Theorem 1.10 -/

section Volume

variable (p : ℕ) [hp : Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] (K : ι → Type)
  [∀ i, Field (K i)] [∀ i, Algebra ℚ_[p] (K i)] [∀ i, FiniteDimensional ℚ_[p] (K i)]
  [MeasurableSpace (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] K)) → ℚ_[p])]
  [BorelSpace (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] K)) → ℚ_[p])]
  (μ : Measure (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] K)) → ℚ_[p]))
  [μ.IsAddHaarMeasure]

omit [DecidableEq ι] in
/-- **IUT IV Proposition 1.4 (i) for any finite number of factors** (page 13): the log-volume
normalized at `(R_I)^∼` has `μ^log((R_I)^∼) = 0` and `μ^log(p · (R_I)^∼) = −log(p)`. -/
theorem tlsm_prop1_4_i :
    padicPacketMuLog p (PiTensorProduct ℚ_[p] K) μ
        (packetNormalizationSet p (PiTensorProduct ℚ_[p] K))
        (packetNormalizationSet p (PiTensorProduct ℚ_[p] K)) = 0 ∧
      padicPacketMuLog p (PiTensorProduct ℚ_[p] K) μ
        (packetNormalizationSet p (PiTensorProduct ℚ_[p] K))
        ((p : ℚ_[p]) • packetNormalizationSet p (PiTensorProduct ℚ_[p] K)) =
        -Real.log p := by
  obtain ⟨-, -, -, -, hself, hsmul⟩ := packet_muLog_normalization_tensor p K μ
  refine ⟨hself, ?_⟩
  have h := hsmul 1
  rw [zpow_one] at h
  rw [h]
  push_cast
  ring

omit [DecidableEq ι] in
/-- Every subset of `(R_I)^∼` has `μ^log ≤ 0`. -/
theorem tlsm_muLog_le_zero {A : Set (PiTensorProduct ℚ_[p] K)}
    (hA : A ⊆ packetNormalizationSet p (PiTensorProduct ℚ_[p] K)) :
    padicPacketMuLog p (PiTensorProduct ℚ_[p] K) μ
      (packetNormalizationSet p (PiTensorProduct ℚ_[p] K)) A ≤ 0 := by
  obtain ⟨-, -, h0, hfin, -, -⟩ := packet_muLog_normalization_tensor p K μ
  exact IUT.PaperIV.Theorem1_10.stepsVI_muLog_le_zero_of_subset μ h0 hfin hA

variable [∀ i, Algebra ℤ_[p] (K i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (K i)]
  (P : ∀ i, Ideal (integralClosure ℤ_[p] (K i))) [∀ i, (P i).IsPrime]
  [∀ i, (P i).LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]

/-- **IUT IV Proposition 1.4 (iv) for any finite number of factors** (page 13): if `p > 2` and
`e_i = 1` for all `i ∈ I`, then `φ((R_I)^∼) ⊆ (R_I)^∼`, so `μ^log(φ((R_I)^∼)) ≤ 0`, and
`μ^log((R_I)^∼) = 0`. -/
theorem tlsm_prop1_4_iv [Nonempty ι] (hp2 : 2 < p)
    (he : ∀ i, (P i).ramificationIdx ℤ_[p] = 1)
    (φ : PiTensorProduct ℚ_[p] K ≃ₗ[ℚ_[p]] PiTensorProduct ℚ_[p] K)
    (hφ : φ '' tlsmLattice p K = tlsmLattice p K) :
    φ '' packetNormalizationSet p (PiTensorProduct ℚ_[p] K) ⊆
        packetNormalizationSet p (PiTensorProduct ℚ_[p] K) ∧
      padicPacketMuLog p (PiTensorProduct ℚ_[p] K) μ
        (packetNormalizationSet p (PiTensorProduct ℚ_[p] K))
        (φ '' packetNormalizationSet p (PiTensorProduct ℚ_[p] K)) ≤ 0 ∧
      padicPacketMuLog p (PiTensorProduct ℚ_[p] K) μ
        (packetNormalizationSet p (PiTensorProduct ℚ_[p] K))
        (packetNormalizationSet p (PiTensorProduct ℚ_[p] K)) = 0 := by
  have hsub := tlsm_prop1_2_iv p K P hp2 he φ hφ
  exact ⟨hsub, tlsm_muLog_le_zero p K μ hsub, (tlsm_prop1_4_i p K μ).1⟩

end Volume

end IUT.PaperIV.LocalFields

namespace IUT.PaperIV.Theorem1_10

open IUT.PaperIV.LocalFields

/-- **Step (vi) of Theorem 1.10 for every `j`** (IUT IV page 29). Let `K_i`, `i ∈ Fin (j + 1)`,
be finite extensions of `ℚ_p` with `p > 2` and every ramification index `e_i = 1` (the hypotheses
of Proposition 1.4 (iv)), and let `φ` be a `ℚ_p`-linear automorphism of the packet `⊗_i K_i`
preserving `log_p(R_I^×)`. Then `φ((R_I)^∼) ⊆ (R_I)^∼` and
`μ^log(φ((R_I)^∼)) ≤ 0 = μ^log((R_I)^∼)`. Moreover the union of the images `φ((R_I)^∼)` over all
such `φ` is `(R_I)^∼` (the identity is one of them). -/
theorem tlsm_stepVI {p : ℕ} [hp : Fact p.Prime] (j : ℕ) (K : Fin (j + 1) → Type)
    [∀ i, Field (K i)] [∀ i, Algebra ℚ_[p] (K i)] [∀ i, FiniteDimensional ℚ_[p] (K i)]
    [∀ i, Algebra ℤ_[p] (K i)] [∀ i, IsScalarTower ℤ_[p] ℚ_[p] (K i)]
    [MeasurableSpace (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] K)) → ℚ_[p])]
    [BorelSpace (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] K)) → ℚ_[p])]
    (μ : Measure (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] K)) → ℚ_[p]))
    [μ.IsAddHaarMeasure]
    (P : ∀ i, Ideal (integralClosure ℤ_[p] (K i))) [∀ i, (P i).IsPrime]
    [∀ i, (P i).LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]
    (hp2 : 2 < p) (he : ∀ i, (P i).ramificationIdx ℤ_[p] = 1) :
    (∀ φ : PiTensorProduct ℚ_[p] K ≃ₗ[ℚ_[p]] PiTensorProduct ℚ_[p] K,
      φ '' tlsmLattice p K = tlsmLattice p K →
        φ '' packetNormalizationSet p (PiTensorProduct ℚ_[p] K) ⊆
            packetNormalizationSet p (PiTensorProduct ℚ_[p] K) ∧
          padicPacketMuLog p (PiTensorProduct ℚ_[p] K) μ
            (packetNormalizationSet p (PiTensorProduct ℚ_[p] K))
            (φ '' packetNormalizationSet p (PiTensorProduct ℚ_[p] K)) ≤ 0) ∧
      (⋃ φ : {φ : PiTensorProduct ℚ_[p] K ≃ₗ[ℚ_[p]] PiTensorProduct ℚ_[p] K //
          φ '' tlsmLattice p K = tlsmLattice p K},
        (φ : PiTensorProduct ℚ_[p] K ≃ₗ[ℚ_[p]] PiTensorProduct ℚ_[p] K) ''
          packetNormalizationSet p (PiTensorProduct ℚ_[p] K))
        = packetNormalizationSet p (PiTensorProduct ℚ_[p] K) := by
  refine ⟨fun φ hφ => ?_, ?_⟩
  · obtain ⟨h1, h2, -⟩ := tlsm_prop1_4_iv p K μ P hp2 he φ hφ
    exact ⟨h1, h2⟩
  · apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun φ => (tlsm_prop1_4_iv p K μ P hp2 he φ.1 φ.2).1
    · intro x hx
      refine Set.mem_iUnion.2 ⟨⟨LinearEquiv.refl ℚ_[p] _, by
        rw [show ⇑(LinearEquiv.refl ℚ_[p] (PiTensorProduct ℚ_[p] K)) = id from rfl,
          Set.image_id]⟩, ?_⟩
      exact ⟨x, hx, rfl⟩

end IUT.PaperIV.Theorem1_10
