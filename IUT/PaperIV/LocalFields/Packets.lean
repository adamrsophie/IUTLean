import IUT.PaperIV.LocalFields.VolumeBridge

/-!
# Tensor packets of finitely many finite extensions of `ℚ_p` and their normalized log-volume

Sources: Mochizuki, *Inter-universal Teichmüller Theory IV*, Proposition 1.1 (page 9),
Proposition 1.2 (page 10), Proposition 1.4 (pages 13 and 14); *Inter-universal Teichmüller
Theory III*, the parts of Proposition 3.1 and Remark 3.1.1 on pages 93 to 96, Proposition 3.9 (i)
(pages 115 and 116). Pages read for this file: IUT IV pages 9, 10, 13 and 14; IUT III pages 93,
94, 95, 96, 115 and 116. Pages checked against rendered images: the same. Displays relied on:
* IUT IV page 9: `R_E = ⊗_{i ∈ E} R_i`, "where the tensor product is over `ℤ_p`", and `(−)^∼`
  "the normalization of the [reduced] ring in parentheses in its ring of fractions";
* IUT IV page 10: `log_p(R_E^×) = ⊗_{i ∈ E} log_p(R_i^×)`, again over `ℤ_p`;
* IUT IV page 13, Proposition 1.4 (i): tensor products of finitely many finite extensions of
  `ℚ_p` over `ℤ_p` "decompose, naturally, as direct sums of finitely many finite extensions of
  `ℚ_p`", and the log-volume on them is "defined on compact open subsets of such tensor products,
  valued in `ℝ`, and normalized so that `μ^log((R_E)^∼) = 0`, `μ^log(p · (R_E)^∼) = −log(p)`, for
  any nonempty set `E ⊆ I`". No weights of the direct summands are printed;
* IUT IV page 14, the first line of the computation proving (iii):
  `μ^log(p ^ ⌊λ − 𝔡_I − a_I⌋ · log_p(R_I^×)) ≤ (−λ + 𝔡_I + a_I + 1) · log(p) + μ^log(log_p(R_I^×))`,
  and the next line, which writes `μ^log(log_p(R_I^×))` as
  `∑_{i ∈ I} μ^log(log_p(R_i^×)) + μ^log(R_I)`: an unweighted sum over the tensor factors;
* IUT III page 115, Proposition 3.9 (i): the log-volume on each direct summand `p_v`-adic field,
  "together with the discussion of normalized weights in Remark 3.1.1, (ii), (iii), (iv)", with
  the integral structures of log-volume zero and "multiplication of an element of `𝔐(−)` by `p_v`
  corresponds to adding the quantity `−log(p_v)`" (the packet-normalization). The weights of
  Remark 3.1.1 (ii), page 94, are built from the global degrees `[K_v : (F_mod)_v]` and
  `[(F_mod)_w : ℚ_{v_ℚ}]`; they have no meaning for an abstract packet of local fields and are
  not formalized here.

## The objects

`K : ι → Type` is a finite family of finite extensions of `ℚ_[p]`, and the packet is Mathlib's
`PiTensorProduct ℚ_[p] K` (written `⊗_i K_i` below), not an iterated binary tensor product. The
pages take the tensor product over `ℤ_p`; the packet here is the tensor product over `ℚ_p`, and the
two are identified only for two factors (`packet_tensor_zp_bijective`). Most
statements are proved for any finite-dimensional commutative `ℚ_p`-algebra `W` that is formally
unramified over `ℚ_p` (a finite étale `ℚ_p`-algebra) and then hold for the packet by
`packet_formallyUnramified`. `(R_E)^∼` is `packetNormalizationSet p W`, the elements of `W`
integral over `ℤ_p`; for `W = K₁ ⊗[ℚ_p] K₂` it is `padicPacketNormalization`
(`packetNormalizationSet_tensor`). `μ^log` on `W` is the existing `padicPacketMuLog`, the
logarithm of a Haar measure on the coordinate space of `Module.finBasis` divided by `dim W` and
normalized at a set `Λ`; on a summand `A_j` it is the same construction with `dim A_j`.

## What is proved

1. *Structure.* `packet_formallyUnramified`: `⊗_i K_i` is formally unramified over `ℚ_p` (two
   lifts agree on every `K_i` because `K_i` is separable, hence on the tensor product).
   `packet_isReduced`, `packet_equiv_pi`: it is reduced and isomorphic, as a `ℚ_p`-algebra, to a
   finite product of finite separable extensions of `ℚ_p`. `packet_finrank`:
   `dim ⊗_i K_i = ∏_i dim K_i`.
2. *The normalization `(R_E)^∼`.* `packet_normalization_eq_preimage`: under any `ℚ_p`-algebra
   isomorphism `e : W ≃ Π_j A_j`, `(R_E)^∼` is the preimage of the product of the sets of
   integral elements of the `A_j` (for fields, their rings of integers, the closed unit balls of
   the spectral norms, `volBridge_padicVolIntegral_iff`). `packet_normalization_isCompact_isOpen`:
   compact and open in coordinates. `packet_muLog_normalization`: positive finite Haar measure,
   `μ^log((R_E)^∼) = 0` and `μ^log(p ^ n · (R_E)^∼) = −n log p` for every `n ∈ ℤ`; this is
   Proposition 1.4 (i) for every finite `E`, on the tensor product over `ℚ_p`
   (`packet_muLog_normalization_tensor` on the packet).
3. *Lattice.* `packet_normalization_lattice`: with `ℤ_p` acting through `ℚ_p`, `(R_E)^∼` is the
   integral closure of `ℤ_p` in `W`, a finitely generated `ℤ_p`-module, and spans `W` over `ℚ_p`.
4. *Tensor product over `ℤ_p` and over `ℚ_p`.* `packet_tensor_zp_bijective`: for `K₁`, `K₂`
   with compatible `ℤ_p`- and `ℚ_p`-algebra structures, the natural map
   `K₁ ⊗[ℤ_p] K₂ → K₁ ⊗[ℚ_p] K₂`, `x ⊗ y ↦ x ⊗ y`, is bijective (`ℚ_p` is the fraction field of
   `ℤ_p`). `packet_integers_span`: the image `padicPacketIntegers` of `R₁ ⊗[ℤ_p] R₂` spans
   `K₁ ⊗[ℚ_p] K₂` over `ℚ_p`.
5. *Direct summands.* `packet_muLog_pi_region`: for a region that is a product `Π_j S_j` of sets
   of positive finite measure in the summands of a decomposition `e : W ≃ Π_j A_j` into fields,
   `μ^log(Π_j S_j) = ∑_j ([A_j : ℚ_p] / dim W) · μ^log_j(S_j)`, with `μ^log_j` normalized at the
   integral elements of `A_j`. The weights `[A_j : ℚ_p] / dim W` are derived from the
   normalization by the dimension, not printed on the pages read. `packet_muLog_transport`
   computes `μ^log` in any linear coordinates.
6. *The step of page 14.* `packet_muLog_floor_smul_le`: for `A` of positive finite measure and
   real `x`, `μ^log(p ^ ⌊x⌋ · A) ≤ (−x + 1) log p + μ^log(A)`. With `x = λ − 𝔡_I − a_I` and
   `A = log_p(R_I^×)` this is the first inequality of the computation on page 14, provided
   `log_p(R_I^×)` has positive finite measure, which is not proved here.

## Not proved

* For more than two factors, that the tensor product over `ℤ_p` of the pages equals
  `PiTensorProduct ℚ_[p] K`; and `R_E = ⊗_{i ∈ E} R_i` itself for more than two factors, here.
  The tensor product over `ℤ_p` maps injectively onto `R_E` for any finite number of factors in
  `PacketIdentifications.lean` (`packetId_map_injective`, `packetId_range_eq`).
* The second line of the computation on page 14, `μ^log(log_p(R_I^×)) = ∑_i μ^log(log_p(R_i^×)) +
  μ^log(R_I)`, an additivity over the tensor factors (not over the direct summands), for more
  than two factors, here. For two factors it is proved in `TensorAdditivity.lean`
  (`tensorAdd_muLog_logLattice`), and for any finite number of factors in
  `TensorAdditivityMany.lean` (`tam_muLog_logLattice`).
* That `R_E` has positive Haar measure for more than two factors; for two factors it is proved,
  with the step `μ^log(R_I) ≤ μ^log((R_I)^∼) = 0` of page 14, in `TensorIndex.lean`
  (`tensorIdx_muLog_nonpos`).
* That `(R_E)^∼` is the normalization of `R_E` in its ring of fractions; here it is the integral
  closure of `ℤ_p` in the packet. For two factors it is proved in `TensorIndex.lean`
  (`tensorIdx_isFractionRing`), and for any finite number of factors in
  `PacketIdentifications.lean` (`packetId_isLocalization`, `packetId_isIntegralElem_iff`).
* The weighted log-volumes of IUT III Proposition 3.9 (i) with the normalized weights of
  Remark 3.1.1 (ii), which depend on global data. They are defined, with the weights as inputs,
  on direct product regions in `IUT/PaperIII/Corollary312/WeightedPacket.lean`.
* IUT IV Proposition 1.4 (iii), (iv) for more than two factors, here (two factors:
  `TensorLogShell.lean`, `TensorAdditivity.lean`; 1.4 (ii): `UnitVolume.lean`). For any finite
  number of factors, (iv) and the first inequality of (iii) are proved in
  `TensorLogShellMany.lean` and `TensorAdditivityMany.lean`. Proposition 1.1 is proved for two
  factors in `TensorDifferent.lean` and `TensorIndex.lean`, its inclusions for any finite number
  of factors in `TensorDifferentMany.lean`, and on the tensor product over `ℤ_p` in
  `PacketIdentifications.lean`.
-/

open MeasureTheory Measure IUT.Prerequisites.PadicVolume
open scoped Pointwise

namespace IUT.PaperIV.LocalFields

/-! ## Finite étale `ℚ_p`-algebras -/

section Etale

universe u

variable (p : ℕ) [hp : Fact p.Prime] (W : Type u) [CommRing W] [Algebra ℚ_[p] W]

/-- `(R_E)^∼` in a commutative `ℚ_p`-algebra `W`: the elements integral over `ℤ_p`. -/
def packetNormalizationSet : Set W := {z | padicVolIntegral p z}

/-- For two factors, `packetNormalizationSet` is `padicPacketNormalization`. -/
theorem packetNormalizationSet_tensor (K₁ K₂ : Type*) [Field K₁] [Field K₂]
    [Algebra ℚ_[p] K₁] [Algebra ℚ_[p] K₂] :
    packetNormalizationSet p (TensorProduct ℚ_[p] K₁ K₂) = padicPacketNormalization p K₁ K₂ :=
  rfl

/-- **`(R_E)^∼` in the coordinates of a decomposition**: for every `ℚ_p`-algebra isomorphism
`e : W ≃ Π_j A_j` onto a finite product, `(R_E)^∼` is the preimage of the product of the sets of
elements of the `A_j` integral over `ℤ_p`. -/
theorem packet_normalization_eq_preimage {J : Type*} [Fintype J] (A : J → Type*)
    [∀ j, CommRing (A j)] [∀ j, Algebra ℚ_[p] (A j)] (e : W ≃ₐ[ℚ_[p]] Π j, A j) :
    packetNormalizationSet p W =
      e ⁻¹' Set.univ.pi (fun j => packetNormalizationSet p (A j)) := by
  ext z
  simp only [Set.mem_preimage, Set.mem_univ_pi]
  constructor
  · intro hz
    exact (volBridge_padicVolIntegral_pi p A (e z)).1 (padicVolIntegral_map p e.toAlgHom hz)
  · intro h
    have h1 := padicVolIntegral_map p e.symm.toAlgHom ((volBridge_padicVolIntegral_pi p A _).2 h)
    have h2 : (e.symm.toAlgHom : _ → _) (e z) = z := e.symm_apply_apply z
    rw [h2] at h1
    exact h1

/-- The image form of `packet_normalization_eq_preimage`: `e((R_E)^∼) = Π_j (integral
elements of A_j)`. -/
theorem packet_normalization_image {J : Type*} [Fintype J] (A : J → Type*)
    [∀ j, CommRing (A j)] [∀ j, Algebra ℚ_[p] (A j)] (e : W ≃ₐ[ℚ_[p]] Π j, A j) :
    e '' packetNormalizationSet p W = Set.univ.pi (fun j => packetNormalizationSet p (A j)) := by
  rw [packet_normalization_eq_preimage p W A e]
  exact Set.image_preimage_eq _ e.surjective

/-- `0 ∈ (R_E)^∼`. -/
theorem packet_zero_mem_normalization : (0 : W) ∈ packetNormalizationSet p W := by
  show padicVolIntegral p (0 : W)
  unfold padicVolIntegral
  rw [← RingHom.map_zero ((algebraMap ℚ_[p] W).comp (algebraMap ℤ_[p] ℚ_[p]))]
  exact RingHom.isIntegralElem_map _

/-- `(R_E)^∼` is stable under multiplication by `p ^ k`, `k ∈ ℕ`. -/
theorem packet_pow_smul_mem_normalization {z : W} (hz : z ∈ packetNormalizationSet p W)
    (k : ℕ) : ((p : ℚ_[p]) ^ k) • z ∈ packetNormalizationSet p W := by
  set φ := (algebraMap ℚ_[p] W).comp (algebraMap ℤ_[p] ℚ_[p])
  have h1 : ((p : ℚ_[p]) ^ k) • z = φ ((p : ℤ_[p]) ^ k) * z := by
    rw [Algebra.smul_def]
    simp [φ]
  show φ.IsIntegralElem _
  rw [h1]
  exact RingHom.IsIntegralElem.mul φ (φ.isIntegralElem_map) hz

/-- For a finite extension `A` of `ℚ_p`, every `x` has a multiple `p ^ n · x` integral over
`ℤ_p`. -/
theorem packet_field_exists_pow_smul (A : Type*) [Field A] [Algebra ℚ_[p] A]
    [FiniteDimensional ℚ_[p] A] (x : A) :
    ∃ n : ℕ, ((p : ℚ_[p]) ^ n) • x ∈ packetNormalizationSet p A := by
  let _ := spectralNorm.normedField ℚ_[p] A
  let _ := spectralNorm.normedAlgebra ℚ_[p] A
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖x‖ hp1
  refine ⟨n, (volBridge_padicVolIntegral_iff p A _).2 ?_⟩
  show ‖((p : ℚ_[p]) ^ n) • x‖ ≤ 1
  rw [norm_smul, norm_pow, Padic.norm_p, inv_pow]
  have hpn : (0 : ℝ) < (p : ℝ) ^ n := by positivity
  rw [inv_mul_le_one₀ hpn]
  exact hn.le

variable [FiniteDimensional ℚ_[p] W]

/-- **A formally unramified finite `ℚ_p`-algebra is reduced.** -/
theorem packet_isReduced_of_unramified [Algebra.FormallyUnramified ℚ_[p] W] : IsReduced W :=
  Algebra.FormallyUnramified.isReduced_of_field ℚ_[p] _

/-- **A formally unramified finite `ℚ_p`-algebra is a finite product of finite separable
extensions of `ℚ_p`.** -/
theorem packet_equiv_pi_of_unramified [Algebra.FormallyUnramified ℚ_[p] W] :
    ∃ (J : Type u) (_ : Fintype J) (A : J → Type u) (_ : ∀ j, Field (A j))
      (_ : ∀ j, Algebra ℚ_[p] (A j)) (_ : W ≃ₐ[ℚ_[p]] Π j, A j),
      ∀ j, Algebra.IsSeparable ℚ_[p] (A j) ∧ FiniteDimensional ℚ_[p] (A j) := by
  have hE : Algebra.FormallyEtale ℚ_[p] W :=
    Algebra.FormallyEtale.iff_formallyUnramified_of_field.mpr ‹_›
  obtain ⟨J, hJ, A, hF, hA, e, hs⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod ℚ_[p] _).mp hE
  classical
  refine ⟨J, Fintype.ofFinite J, A, hF, hA, e, fun j => ⟨hs j, ?_⟩⟩
  refine Module.Finite.of_surjective ((Pi.evalAlgHom ℚ_[p] A j).comp e.toAlgHom).toLinearMap ?_
  intro y
  exact ⟨e.symm (Pi.single j y), by simp⟩

/-- **Every element has a multiple `p ^ n · z` in `(R_E)^∼`**, for `W` formally unramified. -/
theorem packet_exists_pow_smul_mem [Algebra.FormallyUnramified ℚ_[p] W] (z : W) :
    ∃ n : ℕ, ((p : ℚ_[p]) ^ n) • z ∈ packetNormalizationSet p W := by
  obtain ⟨J, _, A, _, _, e, hA⟩ := packet_equiv_pi_of_unramified p W
  have : ∀ j, FiniteDimensional ℚ_[p] (A j) := fun j => (hA j).2
  choose n hn using fun j => packet_field_exists_pow_smul p (A j) (e z j)
  refine ⟨∑ j, n j, ?_⟩
  rw [packet_normalization_eq_preimage p W A e]
  simp only [Set.mem_preimage, Set.mem_univ_pi, map_smul, Pi.smul_apply]
  intro j
  have hle : n j ≤ ∑ k, n k := Finset.single_le_sum (fun k _ => Nat.zero_le (n k))
    (Finset.mem_univ j)
  have h := packet_pow_smul_mem_normalization p (A j) (hn j) (∑ k, n k - n j)
  rwa [smul_smul, ← pow_add, Nat.sub_add_cancel hle] at h

/-- **`(R_E)^∼` is compact and open** in the coordinates of `Module.finBasis`, for `W` formally
unramified (for example a packet of any finite number of factors). -/
theorem packet_normalization_isCompact_isOpen [Algebra.FormallyUnramified ℚ_[p] W] :
    IsCompact ((Module.finBasis ℚ_[p] W).equivFun '' packetNormalizationSet p W) ∧
      IsOpen ((Module.finBasis ℚ_[p] W).equivFun '' packetNormalizationSet p W) := by
  obtain ⟨J, _, A, _, _, e, hA⟩ := packet_equiv_pi_of_unramified p W
  have : ∀ j, FiniteDimensional ℚ_[p] (A j) := fun j => (hA j).2
  let _ : ∀ j, NormedField (A j) := fun j => spectralNorm.normedField ℚ_[p] (A j)
  let _ : ∀ j, NormedAlgebra ℚ_[p] (A j) := fun j => spectralNorm.normedAlgebra ℚ_[p] (A j)
  set c := (Module.finBasis ℚ_[p] W).equivFun
  let Φ := (c.symm.trans e.toLinearEquiv).toContinuousLinearEquiv
  have hΦ : ∀ t, Φ t = e (c.symm t) := fun t => rfl
  have hS : c '' packetNormalizationSet p W =
      Φ ⁻¹' Set.univ.pi (fun j => {y : A j | ‖y‖ ≤ 1}) := by
    ext t
    rw [LinearEquiv.image_eq_preimage_symm, Set.mem_preimage, Set.mem_preimage,
      packet_normalization_eq_preimage p W A e, Set.mem_preimage, hΦ]
    simp only [Set.mem_univ_pi]
    exact forall_congr' fun j => volBridge_padicVolIntegral_iff p (A j) _
  rw [hS]
  have hB := fun j => padicVol_unitBall_isOpen_isCompact p (K := A j)
  exact ⟨Φ.toHomeomorph.isCompact_preimage.mpr (isCompact_univ_pi fun j => (hB j).2),
    (isOpen_set_pi Set.finite_univ fun j _ => (hB j).1).preimage Φ.continuous⟩

/-- **IUT IV Proposition 1.4 (i) for a formally unramified finite `ℚ_p`-algebra** (page 13):
for every additive Haar measure on the coordinate space, `(R_E)^∼` has positive finite measure,
`μ^log((R_E)^∼) = 0`, and `μ^log(p ^ n · (R_E)^∼) = −n log p` for every `n ∈ ℤ` (the case
`n = 1` is the printed normalization). -/
theorem packet_muLog_normalization [Algebra.FormallyUnramified ℚ_[p] W] [Nontrivial W]
    [MeasurableSpace (Fin (Module.finrank ℚ_[p] W) → ℚ_[p])]
    [BorelSpace (Fin (Module.finrank ℚ_[p] W) → ℚ_[p])]
    (μ : Measure (Fin (Module.finrank ℚ_[p] W) → ℚ_[p])) [μ.IsAddHaarMeasure] :
    μ ((Module.finBasis ℚ_[p] W).equivFun '' packetNormalizationSet p W) ≠ 0 ∧
      μ ((Module.finBasis ℚ_[p] W).equivFun '' packetNormalizationSet p W) ≠ ⊤ ∧
      padicPacketMuLog p W μ (packetNormalizationSet p W) (packetNormalizationSet p W) = 0 ∧
      ∀ n : ℤ, padicPacketMuLog p W μ (packetNormalizationSet p W)
        (((p : ℚ_[p]) ^ n) • packetNormalizationSet p W) = -(n * Real.log p) := by
  obtain ⟨hK, hO⟩ := packet_normalization_isCompact_isOpen p W
  have hne : μ ((Module.finBasis ℚ_[p] W).equivFun '' packetNormalizationSet p W) ≠ 0 :=
    hO.measure_ne_zero μ ⟨_, Set.mem_image_of_mem _ (packet_zero_mem_normalization p W)⟩
  have hfin := hK.measure_lt_top (μ := μ) |>.ne
  have hD : 0 < Module.finrank ℚ_[p] W := Module.finrank_pos
  refine ⟨hne, hfin, padicPacketMuLog_self p μ _, fun n => ?_⟩
  rw [padicPacketMuLog_p_zpow_smul p μ hD hne hfin hne hfin n, padicPacketMuLog_self]
  ring

/-- **`(R_E)^∼` is a lattice**: letting `ℤ_p` act on `W` through `ℚ_p`, `(R_E)^∼` is the integral
closure of `ℤ_p` in `W`, it is a finitely generated `ℤ_p`-module, and it spans `W` over `ℚ_p`. -/
theorem packet_normalization_lattice [Algebra.FormallyUnramified ℚ_[p] W] :
    letI : Algebra ℤ_[p] W := Algebra.compHom W (algebraMap ℤ_[p] ℚ_[p])
    ((integralClosure ℤ_[p] W : Subalgebra ℤ_[p] W) : Set W) = packetNormalizationSet p W ∧
      (Subalgebra.toSubmodule (integralClosure ℤ_[p] W)).FG ∧
      Submodule.span ℚ_[p] (packetNormalizationSet p W) = ⊤ := by
  let _ : Algebra ℤ_[p] W := Algebra.compHom W (algebraMap ℤ_[p] ℚ_[p])
  have hcl : ((integralClosure ℤ_[p] W : Subalgebra ℤ_[p] W) : Set W) =
      packetNormalizationSet p W := rfl
  refine ⟨hcl, ?_, ?_⟩
  · -- `(R_E)^∼` lies in `p ^ (−m)` times the `ℤ_p`-span of a basis.
    set b := Module.finBasis ℚ_[p] W
    set c := b.equivFun
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Fin _ → ℚ_[p])).1
      (packet_normalization_isCompact_isOpen p W).1.isBounded
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt r hp1
    have hp0 : (p : ℚ_[p]) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
    set T : Submodule ℤ_[p] W :=
      Submodule.span ℤ_[p] (Set.range fun j => ((p : ℚ_[p]) ^ m)⁻¹ • b j)
    refine Submodule.FG.of_le
      (Submodule.fg_span (Set.finite_range fun j => ((p : ℚ_[p]) ^ m)⁻¹ • b j)) ?_
    intro z hz
    have hzN : z ∈ packetNormalizationSet p W := hz
    have hcz : ‖c z‖ ≤ r := by
      have := hr (Set.mem_image_of_mem c hzN)
      simpa using this
    rw [← b.sum_equivFun z]
    refine Submodule.sum_mem _ fun j _ => ?_
    have hj : ‖(p : ℚ_[p]) ^ m * c z j‖ ≤ 1 := by
      rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
      have hpn : (0 : ℝ) < (p : ℝ) ^ m := by positivity
      rw [inv_mul_le_one₀ hpn]
      exact ((norm_le_pi_norm (c z) j).trans hcz).trans hm.le
    set u : ℤ_[p] := ⟨(p : ℚ_[p]) ^ m * c z j, hj⟩
    have hu : c z j • b j = u • (((p : ℚ_[p]) ^ m)⁻¹ • b j) := by
      show _ = ((p : ℚ_[p]) ^ m * c z j) • (((p : ℚ_[p]) ^ m)⁻¹ • b j)
      rw [smul_smul, mul_comm, ← mul_assoc, inv_mul_cancel₀ hp0, one_mul]
    rw [hu]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [eq_top_iff]
    intro z _
    obtain ⟨n, hn⟩ := packet_exists_pow_smul_mem p W z
    have hp0 : (p : ℚ_[p]) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
    have hz : z = ((p : ℚ_[p]) ^ n)⁻¹ • (((p : ℚ_[p]) ^ n) • z) := by
      rw [smul_smul, inv_mul_cancel₀ hp0, one_smul]
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hn)

end Etale

/-! ## Log-volume in other coordinates and on product regions -/

section Regions

universe u

variable (p : ℕ) [hp : Fact p.Prime] (W : Type u) [CommRing W] [Algebra ℚ_[p] W]
  [FiniteDimensional ℚ_[p] W] [MeasurableSpace (Fin (Module.finrank ℚ_[p] W) → ℚ_[p])]
  [BorelSpace (Fin (Module.finrank ℚ_[p] W) → ℚ_[p])]
  (μ : Measure (Fin (Module.finrank ℚ_[p] W) → ℚ_[p])) [μ.IsAddHaarMeasure]

/-- **`μ^log` in any linear coordinates**: for a linear isomorphism `G` from `W` onto a
finite-dimensional normed `ℚ_p`-vector space `V` with an additive Haar measure `ν`,
`padicPacketMuLog` on `W` is `padicMuLog` on `V` of the images. -/
theorem packet_muLog_transport {V : Type*} [NormedAddCommGroup V] [NormedSpace ℚ_[p] V]
    [FiniteDimensional ℚ_[p] V] [MeasurableSpace V] [BorelSpace V] (ν : Measure V)
    [ν.IsAddHaarMeasure] (G : W ≃ₗ[ℚ_[p]] V) (Λ X : Set W) :
    padicPacketMuLog p W μ Λ X = padicMuLog p ν (G '' Λ) (G '' X) := by
  set c := (Module.finBasis ℚ_[p] W).equivFun
  let h : (Fin (Module.finrank ℚ_[p] W) → ℚ_[p]) ≃L[ℚ_[p]] V :=
    (c.symm.trans G).toContinuousLinearEquiv
  have hH : (Measure.map h μ).IsAddHaarMeasure := h.isAddHaarMeasure_map μ
  rw [padicMuLog_haar_indep p (Measure.map h μ) ν]
  have key : ∀ S : Set W, Measure.map h μ (G '' S) = μ (c '' S) := by
    intro S
    rw [show (Measure.map h μ) (G '' S) =
        (Measure.map h.toHomeomorph.toMeasurableEquiv μ) (G '' S) from rfl,
      MeasurableEquiv.map_apply]
    congr 1
    rw [LinearEquiv.image_eq_preimage_symm, LinearEquiv.image_eq_preimage_symm,
      ← Set.preimage_comp]
    congr 1
    funext t
    simp [h]
  have hd : Module.finrank ℚ_[p] V = Module.finrank ℚ_[p] (Fin (Module.finrank ℚ_[p] W) → ℚ_[p]) :=
    h.toLinearEquiv.finrank_eq.symm
  unfold padicPacketMuLog padicMuLog
  rw [key, key, hd]

/-- **Additivity over the direct summands on product regions**: let `e : W ≃ Π_j A_j` be a
decomposition into finite extensions `A_j` of `ℚ_p`, `ν_j` additive Haar measures on the
coordinate spaces of the `A_j`, and `S_j ⊆ A_j` sets of positive finite measure. Then the region
`e⁻¹(Π_j S_j)` has `μ^log = ∑_j ([A_j : ℚ_p] / dim W) · μ^log_j(S_j)`, where `μ^log` is normalized
at `(R_E)^∼` and `μ^log_j` at the integral elements of `A_j`. -/
theorem packet_muLog_pi_region {J : Type*} [Fintype J] (A : J → Type*) [∀ j, Field (A j)]
    [∀ j, Algebra ℚ_[p] (A j)] [∀ j, FiniteDimensional ℚ_[p] (A j)]
    (e : W ≃ₐ[ℚ_[p]] Π j, A j)
    [∀ j, MeasurableSpace (Fin (Module.finrank ℚ_[p] (A j)) → ℚ_[p])]
    [∀ j, BorelSpace (Fin (Module.finrank ℚ_[p] (A j)) → ℚ_[p])]
    (ν : ∀ j, Measure (Fin (Module.finrank ℚ_[p] (A j)) → ℚ_[p]))
    [∀ j, (ν j).IsAddHaarMeasure] (S : ∀ j, Set (A j))
    (hS0 : ∀ j, ν j ((Module.finBasis ℚ_[p] (A j)).equivFun '' S j) ≠ 0)
    (hS : ∀ j, ν j ((Module.finBasis ℚ_[p] (A j)).equivFun '' S j) ≠ ⊤) :
    padicPacketMuLog p W μ (packetNormalizationSet p W) (e ⁻¹' Set.univ.pi S) =
      ∑ j, ((Module.finrank ℚ_[p] (A j) : ℝ) / Module.finrank ℚ_[p] W) *
        padicPacketMuLog p (A j) (ν j) (packetNormalizationSet p (A j)) (S j) := by
  set c := fun j => (Module.finBasis ℚ_[p] (A j)).equivFun
  let G : W ≃ₗ[ℚ_[p]] Π j, (Fin (Module.finrank ℚ_[p] (A j)) → ℚ_[p]) :=
    e.toLinearEquiv.trans (LinearEquiv.piCongrRight c)
  have hreg : ∀ T : ∀ j, Set (A j),
      G '' (e ⁻¹' Set.univ.pi T) = Set.univ.pi (fun j => c j '' T j) := by
    intro T
    ext t
    rw [LinearEquiv.image_eq_preimage_symm, Set.mem_preimage, Set.mem_preimage, Set.mem_univ_pi,
      Set.mem_univ_pi]
    refine forall_congr' fun j => ?_
    rw [LinearEquiv.image_eq_preimage_symm, Set.mem_preimage]
    simp [G]
  rw [packet_muLog_transport p W μ (Measure.pi ν) G, packet_normalization_eq_preimage p W A e,
    hreg, hreg]
  have hW : Module.finrank ℚ_[p] W =
      Module.finrank ℚ_[p] (Π j, (Fin (Module.finrank ℚ_[p] (A j)) → ℚ_[p])) := G.finrank_eq
  have : ∀ j, Algebra.FormallyUnramified ℚ_[p] (A j) := fun j =>
    Algebra.FormallyUnramified.of_isSeparable _ _
  have hN := fun j => packet_muLog_normalization p (A j) (ν j)
  unfold padicPacketMuLog padicMuLog
  rw [Measure.pi_pi, Measure.pi_pi, ENNReal.toReal_prod, ENNReal.toReal_prod,
    ← Finset.prod_div_distrib, Real.log_prod, Finset.sum_div, hW]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hd : (Module.finrank ℚ_[p] (Fin (Module.finrank ℚ_[p] (A j)) → ℚ_[p]) : ℝ) ≠ 0 := by
      rw [Module.finrank_fin_fun]
      exact_mod_cast (Module.finrank_pos (R := ℚ_[p]) (M := A j)).ne'
    rw [Module.finrank_fin_fun] at hd ⊢
    field_simp
    rfl
  · intro j _
    have h1 := ENNReal.toReal_pos (hS0 j) (hS j)
    have h2 := ENNReal.toReal_pos (hN j).1 (hN j).2.1
    positivity

/-- **The first inequality of the computation on IUT IV page 14**: for `A` and `Λ` of positive
finite measure and real `x`, `μ^log(p ^ ⌊x⌋ · A) ≤ (−x + 1) log p + μ^log(A)`. With
`x = λ − 𝔡_I − a_I` and `A = log_p(R_I^×)` it is the printed step. -/
theorem packet_muLog_floor_smul_le (hD : 0 < Module.finrank ℚ_[p] W) {Λ A : Set W}
    (hΛ0 : μ ((Module.finBasis ℚ_[p] W).equivFun '' Λ) ≠ 0)
    (hΛ : μ ((Module.finBasis ℚ_[p] W).equivFun '' Λ) ≠ ⊤)
    (hA0 : μ ((Module.finBasis ℚ_[p] W).equivFun '' A) ≠ 0)
    (hA : μ ((Module.finBasis ℚ_[p] W).equivFun '' A) ≠ ⊤) (x : ℝ) :
    padicPacketMuLog p W μ Λ (((p : ℚ_[p]) ^ ⌊x⌋) • A) ≤
      (-x + 1) * Real.log p + padicPacketMuLog p W μ Λ A := by
  rw [padicPacketMuLog_p_zpow_smul p μ hD hΛ0 hΛ hA0 hA]
  have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.out.one_lt)
  have h := mul_le_mul_of_nonneg_right (Int.sub_one_lt_floor x).le hlog.le
  linarith

end Regions

/-! ## Tensor packets of finitely many factors -/

section Packet

variable (p : ℕ) [hp : Fact p.Prime] {ι : Type} (K : ι → Type) [∀ i, Field (K i)]
  [∀ i, Algebra ℚ_[p] (K i)] [∀ i, FiniteDimensional ℚ_[p] (K i)]

/-- **A packet `⊗_i K_i` over `ℚ_p` is formally unramified over `ℚ_p`**: two lifts of a map to a
square-zero extension agree on each factor `K_i` (separable, hence formally unramified), hence
on the tensor product. -/
theorem packet_formallyUnramified [Finite ι] :
    Algebra.FormallyUnramified ℚ_[p] (PiTensorProduct ℚ_[p] K) := by
  classical
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro B _ _ I hI f g hfg
  apply PiTensorProduct.algHom_ext
  intro i
  have : Algebra.FormallyUnramified ℚ_[p] (K i) := Algebra.FormallyUnramified.of_isSeparable _ _
  apply Algebra.FormallyUnramified.comp_injective I hI
  rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, hfg]

/-- **`⊗_i K_i` is reduced.** -/
theorem packet_isReduced [Finite ι] : IsReduced (PiTensorProduct ℚ_[p] K) := by
  have := packet_formallyUnramified p K
  exact packet_isReduced_of_unramified p _

/-- **`⊗_i K_i` is a finite product of finite separable extensions of `ℚ_p`** (the decomposition
"as direct sums of finitely many finite extensions of `ℚ_p`" of IUT IV page 13). -/
theorem packet_equiv_pi [Finite ι] :
    ∃ (J : Type) (_ : Fintype J) (A : J → Type) (_ : ∀ j, Field (A j))
      (_ : ∀ j, Algebra ℚ_[p] (A j)) (_ : PiTensorProduct ℚ_[p] K ≃ₐ[ℚ_[p]] Π j, A j),
      ∀ j, Algebra.IsSeparable ℚ_[p] (A j) ∧ FiniteDimensional ℚ_[p] (A j) := by
  have := packet_formallyUnramified p K
  exact packet_equiv_pi_of_unramified p _

/-- **The dimension of a packet**: `dim ⊗_i K_i = ∏_i dim K_i`. -/
theorem packet_finrank [Fintype ι] :
    Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] K) = ∏ i, Module.finrank ℚ_[p] (K i) := by
  classical
  rw [Module.finrank_eq_card_basis (Basis.piTensorProduct fun i => Module.finBasis ℚ_[p] (K i)),
    Fintype.card_pi]
  simp

/-- A packet is nonzero. -/
theorem packet_nontrivial [Fintype ι] : Nontrivial (PiTensorProduct ℚ_[p] K) := by
  apply Module.nontrivial_of_finrank_pos (R := ℚ_[p])
  rw [packet_finrank p K]
  exact Finset.prod_pos fun i _ => Module.finrank_pos

/-- **IUT IV Proposition 1.4 (i) for a packet of any finite number of factors** (page 13), on
`(R_E)^∼` itself: it is compact and open in coordinates, has positive finite measure for every
additive Haar measure, `μ^log((R_E)^∼) = 0` and `μ^log(p ^ n · (R_E)^∼) = −n log p`. -/
theorem packet_muLog_normalization_tensor [Fintype ι]
    [MeasurableSpace (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] K)) → ℚ_[p])]
    [BorelSpace (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] K)) → ℚ_[p])]
    (μ : Measure (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] K)) → ℚ_[p]))
    [μ.IsAddHaarMeasure] :
    IsCompact ((Module.finBasis ℚ_[p] (PiTensorProduct ℚ_[p] K)).equivFun ''
        packetNormalizationSet p (PiTensorProduct ℚ_[p] K)) ∧
      IsOpen ((Module.finBasis ℚ_[p] (PiTensorProduct ℚ_[p] K)).equivFun ''
        packetNormalizationSet p (PiTensorProduct ℚ_[p] K)) ∧
      μ ((Module.finBasis ℚ_[p] (PiTensorProduct ℚ_[p] K)).equivFun ''
        packetNormalizationSet p (PiTensorProduct ℚ_[p] K)) ≠ 0 ∧
      μ ((Module.finBasis ℚ_[p] (PiTensorProduct ℚ_[p] K)).equivFun ''
        packetNormalizationSet p (PiTensorProduct ℚ_[p] K)) ≠ ⊤ ∧
      padicPacketMuLog p (PiTensorProduct ℚ_[p] K) μ
        (packetNormalizationSet p (PiTensorProduct ℚ_[p] K))
        (packetNormalizationSet p (PiTensorProduct ℚ_[p] K)) = 0 ∧
      ∀ n : ℤ, padicPacketMuLog p (PiTensorProduct ℚ_[p] K) μ
        (packetNormalizationSet p (PiTensorProduct ℚ_[p] K))
        (((p : ℚ_[p]) ^ n) • packetNormalizationSet p (PiTensorProduct ℚ_[p] K)) =
          -(n * Real.log p) := by
  have := packet_formallyUnramified p K
  have := packet_nontrivial p K
  obtain ⟨hK, hO⟩ := packet_normalization_isCompact_isOpen p (PiTensorProduct ℚ_[p] K)
  exact ⟨hK, hO, packet_muLog_normalization p _ μ⟩

/-- **`(R_E)^∼` of a packet is a lattice**: with `ℤ_p` acting through `ℚ_p`, it is the integral
closure of `ℤ_p` in `⊗_i K_i`, a finitely generated `ℤ_p`-module, and it spans `⊗_i K_i` over
`ℚ_p`. -/
theorem packet_normalization_lattice_tensor [Fintype ι] :
    letI : Algebra ℤ_[p] (PiTensorProduct ℚ_[p] K) :=
      Algebra.compHom _ (algebraMap ℤ_[p] ℚ_[p])
    ((integralClosure ℤ_[p] (PiTensorProduct ℚ_[p] K) :
        Subalgebra ℤ_[p] (PiTensorProduct ℚ_[p] K)) : Set (PiTensorProduct ℚ_[p] K)) =
        packetNormalizationSet p (PiTensorProduct ℚ_[p] K) ∧
      (Subalgebra.toSubmodule (integralClosure ℤ_[p] (PiTensorProduct ℚ_[p] K))).FG ∧
      Submodule.span ℚ_[p] (packetNormalizationSet p (PiTensorProduct ℚ_[p] K)) = ⊤ := by
  have := packet_formallyUnramified p K
  exact packet_normalization_lattice p _

end Packet

/-! ## Two factors: the tensor product over `ℤ_p` -/

section TwoFactors

variable (p : ℕ) [hp : Fact p.Prime] (K₁ K₂ : Type*) [Field K₁] [Field K₂] [Algebra ℚ_[p] K₁]
  [Algebra ℚ_[p] K₂]

/-- **`K₁ ⊗[ℤ_p] K₂ = K₁ ⊗[ℚ_p] K₂`**: for `ℚ_p`-algebras `K₁`, `K₂` with compatible
`ℤ_p`-algebra structures, the natural map `x ⊗ y ↦ x ⊗ y` from the tensor product over `ℤ_p`
(the one of IUT IV pages 9 and 13) to the tensor product over `ℚ_p` is bijective, because `ℚ_p`
is the fraction field of `ℤ_p`. -/
theorem packet_tensor_zp_bijective [Algebra ℤ_[p] K₁] [Algebra ℤ_[p] K₂]
    [IsScalarTower ℤ_[p] ℚ_[p] K₁] [IsScalarTower ℤ_[p] ℚ_[p] K₂] :
    Function.Bijective (Algebra.TensorProduct.mapOfCompatibleSMul ℚ_[p] ℤ_[p] ℤ_[p] K₁ K₂) := by
  have := IsLocalization.tensorProduct_compatibleSMul (nonZeroDivisors ℤ_[p]) (A := ℚ_[p]) K₁ K₂
  exact (Algebra.TensorProduct.equivOfCompatibleSMul ℚ_[p] ℤ_[p] ℤ_[p] K₁ K₂).bijective

/-- **The image of `R₁ ⊗[ℤ_p] R₂` spans the packet**: `padicPacketIntegers`, the additive span of
the `x ⊗ y` with `x`, `y` integral over `ℤ_p`, spans `K₁ ⊗[ℚ_p] K₂` over `ℚ_p`. -/
theorem packet_integers_span [FiniteDimensional ℚ_[p] K₁] [FiniteDimensional ℚ_[p] K₂] :
    Submodule.span ℚ_[p] (padicPacketIntegers p K₁ K₂) = ⊤ := by
  rw [eq_top_iff, ← TensorProduct.span_tmul_eq_top]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨x, y, rfl⟩
  obtain ⟨n, hn⟩ := packet_field_exists_pow_smul p K₁ x
  obtain ⟨m, hm⟩ := packet_field_exists_pow_smul p K₂ y
  have hp0 : ∀ k : ℕ, (p : ℚ_[p]) ^ k ≠ 0 := fun k =>
    pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hxy : TensorProduct.tmul ℚ_[p] x y = (((p : ℚ_[p]) ^ n)⁻¹ * ((p : ℚ_[p]) ^ m)⁻¹) •
      TensorProduct.tmul ℚ_[p] (((p : ℚ_[p]) ^ n) • x) (((p : ℚ_[p]) ^ m) • y) := by
    rw [TensorProduct.smul_tmul_smul, smul_smul]
    have h1 : ((p : ℚ_[p]) ^ n)⁻¹ * ((p : ℚ_[p]) ^ m)⁻¹ *
        ((p : ℚ_[p]) ^ n * (p : ℚ_[p]) ^ m) = 1 := by
      rw [← mul_inv, inv_mul_cancel₀ (mul_ne_zero (hp0 n) (hp0 m))]
    rw [h1, one_smul]
  rw [SetLike.mem_coe, hxy]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact AddSubmonoid.subset_closure ⟨_, _, hn, hm, rfl⟩

end TwoFactors

end IUT.PaperIV.LocalFields
