import IUT.Audit.TensorOrderIndexMany
import IUT.PaperIV.LocalFields.LocalDiscriminant

/-!
# The normalized log-volume of `R_I` against the allowance of Proposition 1.1, `n` factors

Sources: Mochizuki, *Inter-universal Teichmüller Theory IV*, Proposition 1.1 (page 9) and
Proposition 1.4 (i) (page 13). Pages read for this file: 9 and 13; both were checked against
rendered images. Displays relied on:
* page 9: `𝔡_i` is the order `ord` (with `ord(p) = 1`) of a generator of the different of `R_i`
  over `ℤ_p`, `𝔡_{I*} = Σ_{i ∈ I, i ≠ *} 𝔡_i`, and `p ^ (𝔡_{I*}) · (R_I)^∼ ⊆ R_I ⊆ (R_I)^∼`;
* page 13, Proposition 1.4 (i): log-volumes are normalized "by dividing by the degree of the
  finite extension", with `μ^log((R_E)^∼) = 0` and `μ^log(p · (R_E)^∼) = −log(p)`.
Also: C. Zeng, "An Integral-Structure Inflation in the Hull Operation of IUT Corollary 3.12",
hexagon 2610.00646, version 1, Theorem 5.1 (read from its TeX source; no page render).

Setting: `K/ℚ_p` finite Galois of degree `d`, `n = card ι` copies of `K`, the library's packet
`⊗_{i ∈ ι} K` with `R_I = tdManyIntegers` and `(R_I)^∼ = packetNormalizationSet`, and
`𝔡 = differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P` for a prime `P` over `p`. For the
repeated field the allowance of Proposition 1.1 is `𝔡_{I*} = (n − 1) · 𝔡`.

Proved:
* `tOrdAllow_muLog`: `μ^log(R_I) = −((n − 1)/2) · 𝔡 · log p` (from `tOrdMany_muLog` and
  `locDisc_valuation_discr`, `v_p(disc b) = d · 𝔡`).
* `tOrdAllow_compare`: on the same objects, the two inclusions of Proposition 1.1 as the library
  states them (`tdMany_proposition1_1`: multiplication by `⊗δ`, `δ_i` of order `𝔡`, maps
  `(R_I)^∼` into `R_I`, and `R_I ⊆ (R_I)^∼`), the exact value, the bound
  `−(n − 1) · 𝔡 · log p ≤ μ^log(R_I)`, and `μ^log(R_I) = (1/2) · (−(n − 1) · 𝔡 · log p)`.
* `tOrdAllow_muLog_sum`, `tOrdAllow_muLog_avg`: for `n = j + 1` factors, `j = 1, …, J`,
  `Σ_j μ^log(R_{I_j}) = −(J (J + 1)/4) · 𝔡 · log p` and the average is
  `−((J + 1)/4) · 𝔡 · log p`.

Not proved: the bound `−(n − 1) · 𝔡 · log p ≤ μ^log(R_I)` is obtained from the exact value
(as `𝔡 ≥ 0` and `log p > 0`), not from the inclusion `⊗δ · (R_I)^∼ ⊆ R_I` through the
log-volume. That route needs the scaling of a Haar measure on `⊗_{i ∈ ι} K` under
multiplication by `⊗δ`, that is, the `p`-adic absolute value of the determinant of that
multiplication (the norm of `⊗δ` from the tensor algebra to `ℚ_p`), which is not formalized
here.
-/

namespace IUT.Audit.TensorOrderIndexAllowance

open IUT.PaperIV.LocalFields IUT.Audit.TensorOrderIndex IUT.Audit.TensorOrderIndexMany
  IUT.Prerequisites.PadicVolume MeasureTheory

variable {p : ℕ} [hp : Fact p.Prime] (K : Type) [Field K] [Algebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]

/-- **`μ^log(R_I)` for `n` factors in terms of the different** (`K/ℚ_p` Galois): with the
normalization of IUT IV Proposition 1.4 (i) (page 13), `μ^log(R_I) = −((n − 1)/2) · 𝔡 · log p`,
where `𝔡 = differentOrder ℤ_[p] R P` is the order of the different of
`R = integralClosure ℤ_[p] K`, normalized by `ord(p) = 1`. -/
theorem tOrdAllow_muLog [IsGalois ℚ_[p] K] {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [MeasurableSpace (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] (fun _ : ι => K))) →
      ℚ_[p])]
    [BorelSpace (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] (fun _ : ι => K))) → ℚ_[p])]
    (μ : Measure (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] (fun _ : ι => K))) → ℚ_[p]))
    [μ.IsAddHaarMeasure] (P : Ideal (integralClosure ℤ_[p] K)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    letI := isDedekindDomain_ringOfIntegers_padic p K
    letI := isTorsionFree_ringOfIntegers_padic p K
    padicPacketMuLog p (PiTensorProduct ℚ_[p] (fun _ : ι => K)) μ
        (packetNormalizationSet p (PiTensorProduct ℚ_[p] (fun _ : ι => K)))
        (tdManyIntegers p (fun _ : ι => K)) =
      -(((Fintype.card ι - 1 : ℕ) : ℝ) / 2) *
        (differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P * Real.log p) := by
  let := isDedekindDomain_ringOfIntegers_padic p K
  let := isTorsionFree_ringOfIntegers_padic p K
  obtain ⟨m, b, hb⟩ := tOrdIdx_exists_integralBasis (p := p) K
  rw [tOrdMany_muLog p K μ b hb, locDisc_valuation_discr P b hb]
  have hd : (0 : ℝ) < Module.finrank ℚ_[p] K := by exact_mod_cast Module.finrank_pos
  field_simp

/-- **The exact value against the allowance of Proposition 1.1, `n` factors** (`K/ℚ_p`
Galois, `n = card ι ≥ 2` copies of `K`, distinguished factor `s`). On the library's packet:
* the two inclusions of IUT IV Proposition 1.1 (page 9) as `tdMany_proposition1_1` states
  them for the repeated field: for `δ` with `δ_s = 1` and `δ_i` of spectral norm `p ^ (−𝔡)`
  for `i ≠ s`, multiplication by `⊗δ` maps `(R_I)^∼` into `R_I`; and `R_I ⊆ (R_I)^∼`
  (the allowance is `𝔡_{I*} = (n − 1) · 𝔡`);
* the exact value `μ^log(R_I) = −((n − 1)/2) · 𝔡 · log p`;
* the bound `−(n − 1) · 𝔡 · log p ≤ μ^log(R_I)`, the log-volume counterpart of the allowance;
* the relation `μ^log(R_I) = (1/2) · (−(n − 1) · 𝔡 · log p)`.
The bound is derived from the exact value, not from the inclusion (see the module docstring). -/
theorem tOrdAllow_compare [IsGalois ℚ_[p] K] {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι)
    (hI : 2 ≤ Fintype.card ι)
    [MeasurableSpace (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] (fun _ : ι => K))) →
      ℚ_[p])]
    [BorelSpace (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] (fun _ : ι => K))) → ℚ_[p])]
    (μ : Measure (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] (fun _ : ι => K))) → ℚ_[p]))
    [μ.IsAddHaarMeasure] (P : Ideal (integralClosure ℤ_[p] K)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] :
    letI := isDedekindDomain_ringOfIntegers_padic p K
    letI := isTorsionFree_ringOfIntegers_padic p K
    (∀ δ : ι → K, δ s = 1 →
      (∀ i, i ≠ s → (letI := spectralNorm.normedField ℚ_[p] K;
        ‖δ i‖ = (p : ℝ) ^ (-differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P))) →
      ∀ z ∈ packetNormalizationSet p (PiTensorProduct ℚ_[p] (fun _ : ι => K)),
        PiTensorProduct.tprod ℚ_[p] δ * z ∈ tdManyIntegers p (fun _ : ι => K)) ∧
    tdManyIntegers p (fun _ : ι => K) ⊆
      packetNormalizationSet p (PiTensorProduct ℚ_[p] (fun _ : ι => K)) ∧
    padicPacketMuLog p (PiTensorProduct ℚ_[p] (fun _ : ι => K)) μ
        (packetNormalizationSet p (PiTensorProduct ℚ_[p] (fun _ : ι => K)))
        (tdManyIntegers p (fun _ : ι => K)) =
      -(((Fintype.card ι - 1 : ℕ) : ℝ) / 2) *
        (differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P * Real.log p) ∧
    -(((Fintype.card ι - 1 : ℕ) : ℝ) *
        (differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P * Real.log p)) ≤
      padicPacketMuLog p (PiTensorProduct ℚ_[p] (fun _ : ι => K)) μ
        (packetNormalizationSet p (PiTensorProduct ℚ_[p] (fun _ : ι => K)))
        (tdManyIntegers p (fun _ : ι => K)) ∧
    padicPacketMuLog p (PiTensorProduct ℚ_[p] (fun _ : ι => K)) μ
        (packetNormalizationSet p (PiTensorProduct ℚ_[p] (fun _ : ι => K)))
        (tdManyIntegers p (fun _ : ι => K)) =
      (1 / 2) * -(((Fintype.card ι - 1 : ℕ) : ℝ) *
        (differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P * Real.log p)) := by
  let := isDedekindDomain_ringOfIntegers_padic p K
  let := isTorsionFree_ringOfIntegers_padic p K
  have : Nonempty ι := ⟨s⟩
  have hP := tdMany_proposition1_1 p (fun _ : ι => K) s hI (fun _ => P)
  have hval := tOrdAllow_muLog K μ P
  have h0 : 0 ≤ differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hl : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.out.one_lt)
  have hx := mul_nonneg h0 hl.le
  have hn : (0 : ℝ) ≤ ((Fintype.card ι - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hnx := mul_nonneg hn hx
  refine ⟨hP.1, hP.2.1, hval, ?_, ?_⟩
  · rw [hval]
    nlinarith
  · rw [hval]
    ring

/-- **The sum over `n = j + 1` factors, `j = 1, …, J`** (`K/ℚ_p` Galois): for a family of Haar
measures `μ j` on the coordinates of the packets `⊗_{Fin (j + 1)} K`,
`Σ_{j=1}^{J} μ^log(R_{I_j}) = −(J (J + 1)/4) · 𝔡 · log p`. -/
theorem tOrdAllow_muLog_sum [IsGalois ℚ_[p] K]
    [∀ j : ℕ, MeasurableSpace
      (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] (fun _ : Fin (j + 1) => K))) → ℚ_[p])]
    [∀ j : ℕ, BorelSpace
      (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] (fun _ : Fin (j + 1) => K))) → ℚ_[p])]
    (μ : ∀ j : ℕ, Measure
      (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] (fun _ : Fin (j + 1) => K))) → ℚ_[p]))
    [∀ j, (μ j).IsAddHaarMeasure] (P : Ideal (integralClosure ℤ_[p] K)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] (J : ℕ) :
    letI := isDedekindDomain_ringOfIntegers_padic p K
    letI := isTorsionFree_ringOfIntegers_padic p K
    ∑ j ∈ Finset.Icc 1 J,
        padicPacketMuLog p (PiTensorProduct ℚ_[p] (fun _ : Fin (j + 1) => K)) (μ j)
          (packetNormalizationSet p (PiTensorProduct ℚ_[p] (fun _ : Fin (j + 1) => K)))
          (tdManyIntegers p (fun _ : Fin (j + 1) => K)) =
      -((J : ℝ) * (J + 1) / 4) *
        (differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P * Real.log p) := by
  let := isDedekindDomain_ringOfIntegers_padic p K
  let := isTorsionFree_ringOfIntegers_padic p K
  rw [Finset.sum_congr rfl fun j _ => tOrdAllow_muLog K (μ j) P]
  simp only [Fintype.card_fin, Nat.add_sub_cancel]
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

/-- **The average over `n = j + 1` factors, `j = 1, …, J`** (`K/ℚ_p` Galois, `J ≥ 1`):
`(1/J) · Σ_{j=1}^{J} μ^log(R_{I_j}) = −((J + 1)/4) · 𝔡 · log p`. -/
theorem tOrdAllow_muLog_avg [IsGalois ℚ_[p] K]
    [∀ j : ℕ, MeasurableSpace
      (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] (fun _ : Fin (j + 1) => K))) → ℚ_[p])]
    [∀ j : ℕ, BorelSpace
      (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] (fun _ : Fin (j + 1) => K))) → ℚ_[p])]
    (μ : ∀ j : ℕ, Measure
      (Fin (Module.finrank ℚ_[p] (PiTensorProduct ℚ_[p] (fun _ : Fin (j + 1) => K))) → ℚ_[p]))
    [∀ j, (μ j).IsAddHaarMeasure] (P : Ideal (integralClosure ℤ_[p] K)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] {J : ℕ} (hJ : J ≠ 0) :
    letI := isDedekindDomain_ringOfIntegers_padic p K
    letI := isTorsionFree_ringOfIntegers_padic p K
    (1 / (J : ℝ)) * ∑ j ∈ Finset.Icc 1 J,
        padicPacketMuLog p (PiTensorProduct ℚ_[p] (fun _ : Fin (j + 1) => K)) (μ j)
          (packetNormalizationSet p (PiTensorProduct ℚ_[p] (fun _ : Fin (j + 1) => K)))
          (tdManyIntegers p (fun _ : Fin (j + 1) => K)) =
      -(((J : ℝ) + 1) / 4) *
        (differentOrder ℤ_[p] (integralClosure ℤ_[p] K) P * Real.log p) := by
  let := isDedekindDomain_ringOfIntegers_padic p K
  let := isTorsionFree_ringOfIntegers_padic p K
  rw [tOrdAllow_muLog_sum K μ P J]
  have : (J : ℝ) ≠ 0 := by exact_mod_cast hJ
  field_simp

end IUT.Audit.TensorOrderIndexAllowance
