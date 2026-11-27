import IUT.Applications.FermatDifferent

/-!
# The different of a Galois extension, and the log-different bound for the Fermat cover

Sources: Mochizuki, *Arithmetic Elliptic Curves in General Position* ([GenEll]), Proposition 1.7
and its proof (pages 9 and 10) and its use in the proof of Theorem 2.1 (page 12); V. Dimitrov,
*Effectivity in Mochizuki's work on the abc-conjecture* (arXiv 1601.03572), page 9. Pages read for
this file: [GenEll] pages 9, 10 and 12; arXiv 1601.03572 page 9. Pages checked against rendered
images: all of these.

**What this file is.** It continues `IUT.Applications.FermatDifferent`, where the inequality
`log-diff_L ≤ log-diff_K + log-cond_K(x) + c(n)` for the field `L = K(u, v)` of a lifted point of
the Fermat cover (`u^n = x`, `v^n = 1 - x`) was proved assuming the classical bound for the
different. Here the assumption is removed, by a weaker but sufficient bound for the different that
is proved through a Galois extension. The page 12 inequality of [GenEll],
`log-diff_Y ≲ log-diff_X + log-cond_D`, is obtained there from Proposition 1.7 (i); this file
proves an instance of it for the Fermat cover (a choice made here, as in
`IUT.Applications.FermatCover`), not Proposition 1.7.

**What this file proves.**
1. The different of a Galois extension is stable under the Galois group
   (`fermatGal_smul_mem_differentIdeal`, through the trace dual of `𝓞_L`), so all primes over a
   prime have the same exponent in it (`fermatGal_multiplicity_eq_of_under_eq`, with Mathlib's
   transitivity of the Galois group on primes).
2. For `L/K` Galois and `P` over `𝔭`: `v_P(𝔇_{L/K}) ≤ e_P - 1 + v_P([L : K])`
   (`fermatGal_multiplicity_lt`, stated as `v_P(𝔇) < e_P (v_𝔭([L : K]) + 1)`). The proof is the
   trace of `𝔭^{-s}`: if `𝔭^s 𝓞_L ∣ 𝔇_{L/K}` then `[L : K]·𝔭^{-s} ⊆ 𝓞_K`. For any `K ⊆ L ⊆ M`
   with `M/K` Galois, the tower formula for the different gives
   `v_P(𝔇_{L/K}) ≤ e_P - 1 + v_P([M : K])` (`fermatGal_multiplicity_lt_of_tower`).
3. For `L = K(u, v)` inside a Galois `M`:
   `log-diff_L ≤ log-diff_K + log-cond_K(x) + log n + log [M : K]` (`fermatGal_logDiffNF_le`);
   with `M = K(ζ_n, u, v)`, Galois of degree at most `n³` (`fermatGal_galois_field_exists`), this
   is `fermatGal_lift_logDiffNF_le`: `log-diff_L ≤ log-diff_K + log-cond_K(x) + 4 log n`, without
   any assumption. The constant `c(n) = 4 log n` is explicit; [GenEll] page 12 prints none.

**Not proved here.** The classical bound `v_P(𝔇_{L/K}) ≤ e_P - 1 + v_P(e_P)`, which
`IUT.FermatDifferent.fermatDiff_classicalDifferentBoundStatement` asks for, is not reached here
(it is proved in `IUT.DifferentBridge`, `diffBr_classical_bound`): the
bound proved here has `v_P([M : K])` in place of `v_P(e_P)`, and `e_P` may be much smaller than
`[M : K]` at primes over `p` dividing `[M : K]`. `IUT.DifferentBridge` reaches `v_P(e_P)` through
inertia fields. Proposition 1.7 of [GenEll] itself is not proved either.
-/

open NumberField IsDedekindDomain nonZeroDivisors
open IUT.VojtaNumberField IUT.PaperIV.DegreePullback IUT.FermatDifferent

namespace IUT.FermatDifferentGalois

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- Membership in the relative different through the trace dual: `b ∈ 𝔇_{L/K}` exactly when
`b` lies in `1 / (𝓞_L)^∨`, where `(𝓞_L)^∨` is the dual of `𝓞_L` for the trace form of `L/K`
(Mathlib's `coeSubmodule_differentIdeal`). -/
theorem fermatGal_mem_differentIdeal_iff (b : 𝓞 L) :
    b ∈ differentIdeal (𝓞 K) (𝓞 L) ↔
      algebraMap (𝓞 L) L b ∈ (1 : Submodule (𝓞 L) L) / Submodule.traceDual (𝓞 K) K 1 := by
  rw [← coeSubmodule_differentIdeal (𝓞 K) K, IsLocalization.mem_coeSubmodule]
  constructor
  · intro h
    exact ⟨b, h, rfl⟩
  · rintro ⟨y, hy, hyb⟩
    rwa [← IsFractionRing.injective (𝓞 L) L hyb]

/-- **The different is stable under the automorphisms of `L/K`.** For `σ ∈ Aut(L/K)` and
`b ∈ 𝔇_{L/K}`, `σ(b) ∈ 𝔇_{L/K}`: the trace dual of `𝓞_L` is `σ`-stable because
`Tr_{L/K}(σ(z)) = Tr_{L/K}(z)` and `σ(𝓞_L) = 𝓞_L`. -/
theorem fermatGal_smul_mem_differentIdeal (σ : L ≃ₐ[K] L) {b : 𝓞 L}
    (hb : b ∈ differentIdeal (𝓞 K) (𝓞 L)) : σ • b ∈ differentIdeal (𝓞 K) (𝓞 L) := by
  have hcoe : ∀ (τ : L ≃ₐ[K] L) (c : 𝓞 L),
      algebraMap (𝓞 L) L (τ • c) = τ (algebraMap (𝓞 L) L c) := fun τ c => by
    rw [algebraMap.smul', AlgEquiv.smul_def]
  rw [fermatGal_mem_differentIdeal_iff] at hb ⊢
  rw [Submodule.mem_div_iff_forall_mul_mem] at hb ⊢
  intro y hy
  have hy' : σ.symm y ∈ Submodule.traceDual (𝓞 K) K (1 : Submodule (𝓞 L) L) := by
    rw [Submodule.mem_traceDual] at hy ⊢
    intro a ha
    obtain ⟨a', rfl⟩ := Submodule.mem_one.mp ha
    have h := hy (algebraMap (𝓞 L) L (σ • a')) (Submodule.mem_one.mpr ⟨_, rfl⟩)
    rw [Algebra.traceForm_apply] at h ⊢
    rw [← Algebra.trace_eq_of_algEquiv σ, map_mul, AlgEquiv.apply_symm_apply, ← hcoe]
    exact h
  obtain ⟨c, hc⟩ := Submodule.mem_one.mp (hb _ hy')
  refine Submodule.mem_one.mpr ⟨σ • c, ?_⟩
  rw [hcoe, hc, hcoe, map_mul, AlgEquiv.apply_symm_apply]

/-- `𝔇_{L/K} ⊆ σ(𝔇_{L/K})` for every `σ ∈ Aut(L/K)` (hence equality, applying `σ⁻¹`). -/
theorem fermatGal_differentIdeal_le_map (σ : L ≃ₐ[K] L) :
    differentIdeal (𝓞 K) (𝓞 L) ≤
      (differentIdeal (𝓞 K) (𝓞 L)).map (MulSemiringAction.toRingHom _ (𝓞 L) σ) := by
  intro b hb
  have h := Ideal.mem_map_of_mem (MulSemiringAction.toRingHom _ (𝓞 L) σ)
    (fermatGal_smul_mem_differentIdeal σ⁻¹ hb)
  rwa [MulSemiringAction.toRingHom_apply, smul_inv_smul] at h

/-- **In a Galois extension, divisibility of the different by a prime power does not depend
on the prime over a given prime.** For `L/K` Galois and primes `P`, `Q` of `𝓞_L` over the same
prime of `𝓞_K`: `P^k ∣ 𝔇_{L/K}` implies `Q^k ∣ 𝔇_{L/K}` (with Mathlib's transitivity of the
Galois group on the primes over a prime, `Ideal.exists_smul_eq_of_isGaloisGroup`). -/
theorem fermatGal_pow_dvd_of_under_eq [IsGalois K L] (P Q : Ideal (𝓞 L)) [P.IsPrime]
    [Q.IsPrime] (h : P.under (𝓞 K) = Q.under (𝓞 K)) (k : ℕ)
    (hP : P ^ k ∣ differentIdeal (𝓞 K) (𝓞 L)) : Q ^ k ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  have := IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  have : P.LiesOver (P.under (𝓞 K)) := ⟨rfl⟩
  have : Q.LiesOver (P.under (𝓞 K)) := ⟨h⟩
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (P.under (𝓞 K)) P Q (L ≃ₐ[K] L)
  rw [Ideal.pointwise_smul_def] at hσ
  rw [Ideal.dvd_iff_le] at hP ⊢
  rw [← hσ, ← Ideal.map_pow]
  exact (fermatGal_differentIdeal_le_map σ).trans (Ideal.map_mono hP)


/-- **In a Galois extension all primes over a given prime have the same exponent in the
different.** -/
theorem fermatGal_multiplicity_eq_of_under_eq [IsGalois K L] (P Q : Ideal (𝓞 L)) [P.IsPrime]
    [Q.IsPrime] (h : P.under (𝓞 K) = Q.under (𝓞 K)) :
    multiplicity P (differentIdeal (𝓞 K) (𝓞 L)) = multiplicity Q (differentIdeal (𝓞 K) (𝓞 L)) := by
  have hD0 : differentIdeal (𝓞 K) (𝓞 L) ≠ ⊥ := differentIdeal_ne_bot
  have hfin : ∀ R : Ideal (𝓞 L), R.IsPrime → FiniteMultiplicity R (differentIdeal (𝓞 K) (𝓞 L)) :=
    fun R hR => FiniteMultiplicity.of_not_isUnit (fun hu => hR.ne_top (Ideal.isUnit_iff.mp hu)) hD0
  apply le_antisymm
  · exact (hfin Q ‹_›).le_multiplicity_of_pow_dvd
      (fermatGal_pow_dvd_of_under_eq P Q h _ (pow_multiplicity_dvd _ _))
  · exact (hfin P ‹_›).le_multiplicity_of_pow_dvd
      (fermatGal_pow_dvd_of_under_eq Q P h.symm _ (pow_multiplicity_dvd _ _))

/-- **The trace step.** If `𝔞 𝓞_L ∣ 𝔇_{L/K}` for a nonzero ideal `𝔞` of `𝓞_K`, then
`𝔞 ∣ [L : K]·𝓞_K`. Indeed `𝔇_{L/K} ⊆ 𝔞𝓞_L` gives `Tr_{L/K}((𝔞𝓞_L)⁻¹) ⊆ 𝓞_K` (Mathlib's
`differentialIdeal_le_iff`); for `z ∈ 𝔞⁻¹` this reads `[L : K]·z = Tr_{L/K}(z) ∈ 𝓞_K`, so
`[L : K]·𝔞⁻¹ ⊆ 𝓞_K`. -/
theorem fermatGal_dvd_span_finrank_of_map_dvd (a : Ideal (𝓞 K)) (ha : a ≠ ⊥)
    (h : a.map (algebraMap (𝓞 K) (𝓞 L)) ∣ differentIdeal (𝓞 K) (𝓞 L)) :
    a ∣ Ideal.span {((Module.finrank K L : ℕ) : 𝓞 K)} := by
  rw [Ideal.dvd_iff_le] at h
  have hmap0 : a.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot ha
  have H := (differentialIdeal_le_iff (A := 𝓞 K) (K := K) (L := L) hmap0).mp h
  have ha0 : (a : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr ha
  have hz : ∀ z ∈ ((a : FractionalIdeal (𝓞 K)⁰ K))⁻¹,
      algebraMap (𝓞 K) K ((Module.finrank K L : ℕ) : 𝓞 K) * z ∈
        (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    intro z hz
    have h1 : algebraMap K L z ∈
        ((a.map (algebraMap (𝓞 K) (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L))⁻¹ := by
      rw [← FractionalIdeal.extendedHom_coeIdeal_eq_map (K := K) L (𝓞 L) a, ← map_inv₀,
        ← FractionalIdeal.mem_coeToSubmodule, FractionalIdeal.coeToSubmodule_extendedHom_eq_span]
      exact Submodule.subset_span ⟨z, hz, rfl⟩
    have h2 := H (Submodule.mem_map_of_mem h1)
    rw [LinearMap.restrictScalars_apply, Algebra.trace_algebraMap, Submodule.mem_one] at h2
    obtain ⟨c, hc⟩ := h2
    rw [FractionalIdeal.mem_one_iff]
    exact ⟨c, by rw [hc, nsmul_eq_mul, map_natCast]⟩
  have hle : ((Ideal.span {((Module.finrank K L : ℕ) : 𝓞 K)} : Ideal (𝓞 K)) :
      FractionalIdeal (𝓞 K)⁰ K) * ((a : FractionalIdeal (𝓞 K)⁰ K))⁻¹ ≤ 1 := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_le_iff]
    exact hz
  have hle' : ((Ideal.span {((Module.finrank K L : ℕ) : 𝓞 K)} : Ideal (𝓞 K)) :
      FractionalIdeal (𝓞 K)⁰ K) ≤ a := by
    calc _ = ((Ideal.span {((Module.finrank K L : ℕ) : 𝓞 K)} : Ideal (𝓞 K)) :
          FractionalIdeal (𝓞 K)⁰ K) * ((a : FractionalIdeal (𝓞 K)⁰ K))⁻¹ * a := by
          rw [mul_assoc, inv_mul_cancel₀ ha0, mul_one]
      _ ≤ 1 * a := mul_le_mul_left hle _
      _ = a := one_mul _
  rw [Ideal.dvd_iff_le]
  exact (FractionalIdeal.coeIdeal_le_coeIdeal K).mp hle'

/-- In a Galois extension, if `P^(e_P s) ∣ 𝔇_{L/K}` for one prime `P` over `𝔭`, then
`𝔭^s 𝓞_L ∣ 𝔇_{L/K}` (every prime over `𝔭` has the same ramification index and, by
`fermatGal_pow_dvd_of_under_eq`, the same divisibility). -/
theorem fermatGal_map_pow_dvd [IsGalois K L] (w : HeightOneSpectrum (𝓞 L)) (s : ℕ)
    (hw : w.asIdeal ^ (w.asIdeal.ramificationIdx (𝓞 K) * s) ∣ differentIdeal (𝓞 K) (𝓞 L)) :
    ((HeightOneSpectrum.under (𝓞 K) w).asIdeal ^ s).map (algebraMap (𝓞 K) (𝓞 L)) ∣
      differentIdeal (𝓞 K) (𝓞 L) := by
  set p := (HeightOneSpectrum.under (𝓞 K) w).asIdeal with hp
  have hpm : p.IsMaximal := (HeightOneSpectrum.under (𝓞 K) w).isMaximal
  have hpS : p.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot (HeightOneSpectrum.under (𝓞 K) w).ne_bot
  have hD0 : differentIdeal (𝓞 K) (𝓞 L) ≠ ⊥ := differentIdeal_ne_bot
  refine fermatDiff_dvd_of_multiplicity_le
    (by rw [Ideal.map_pow]; exact pow_ne_zero _ hpS) hD0 fun q => ?_
  have hqprime : Prime q.asIdeal := Ideal.prime_of_isPrime q.ne_bot q.isPrime
  rw [Ideal.map_pow, multiplicity_pow hqprime]
  by_cases hq : q.asIdeal.under (𝓞 K) = p
  · have : q.asIdeal.LiesOver p := ⟨hq.symm⟩
    have hwq : w.asIdeal.under (𝓞 K) = q.asIdeal.under (𝓞 K) := by
      rw [hq]; rfl
    have he : q.asIdeal.ramificationIdx (𝓞 K) = w.asIdeal.ramificationIdx (𝓞 K) := by
      have := IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
      have : w.asIdeal.LiesOver p := ⟨rfl⟩
      exact Ideal.ramificationIdx_eq_of_isGaloisGroup p q.asIdeal w.asIdeal (L ≃ₐ[K] L)
    rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity p q.asIdeal hpS, he,
      mul_comm]
    have hqk := fermatGal_pow_dvd_of_under_eq w.asIdeal q.asIdeal hwq _ hw
    have hfin : FiniteMultiplicity q.asIdeal (differentIdeal (𝓞 K) (𝓞 L)) :=
      FiniteMultiplicity.of_not_isUnit
        (fun hu' => q.isPrime.ne_top (Ideal.isUnit_iff.mp hu')) hD0
    exact hfin.le_multiplicity_of_pow_dvd hqk
  · have hnd : ¬ q.asIdeal ∣ p.map (algebraMap (𝓞 K) (𝓞 L)) := by
      intro hd
      apply hq
      rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap] at hd
      exact (hpm.eq_of_le (Ideal.comap_isPrime _ q.asIdeal).ne_top hd).symm
    rw [multiplicity_eq_zero_of_not_dvd hnd, mul_zero]
    exact Nat.zero_le _

/-- **The bound for the different of a Galois extension.** For `L/K` Galois and a prime `P`
of `𝓞_L` over `𝔭`: `v_P(𝔇_{L/K}) < e_P·(v_𝔭([L : K]) + 1)`, that is
`v_P(𝔇_{L/K}) ≤ e_P - 1 + v_P([L : K])`. Proof: with `s = ⌊v_P(𝔇)/e_P⌋`,
`fermatGal_map_pow_dvd` gives `𝔭^s 𝓞_L ∣ 𝔇_{L/K}`, and the trace step gives `s ≤ v_𝔭([L : K])`. -/
theorem fermatGal_multiplicity_lt [IsGalois K L] (w : HeightOneSpectrum (𝓞 L)) :
    multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 L)) <
      w.asIdeal.ramificationIdx (𝓞 K) *
        (multiplicity (HeightOneSpectrum.under (𝓞 K) w).asIdeal
          (Ideal.span {((Module.finrank K L : ℕ) : 𝓞 K)}) + 1) := by
  set p := (HeightOneSpectrum.under (𝓞 K) w).asIdeal with hp
  set d := multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 L)) with hd
  set e := w.asIdeal.ramificationIdx (𝓞 K) with he
  have he0 : 0 < e := by
    have : w.asIdeal.LiesOver p := ⟨rfl⟩
    exact Ideal.ramificationIdx_pos_of_isDedekindDomain' w.asIdeal
      (HeightOneSpectrum.under (𝓞 K) w).ne_bot
  have hw : w.asIdeal ^ (e * (d / e)) ∣ differentIdeal (𝓞 K) (𝓞 L) :=
    (pow_dvd_pow _ (Nat.mul_div_le d e)).trans (pow_multiplicity_dvd _ _)
  have hps := fermatGal_dvd_span_finrank_of_map_dvd (L := L) (p ^ (d / e))
    (pow_ne_zero _ (HeightOneSpectrum.under (𝓞 K) w).ne_bot) (fermatGal_map_pow_dvd w _ hw)
  have hN0 : Ideal.span {((Module.finrank K L : ℕ) : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast Module.finrank_pos.ne'
  have hfin : FiniteMultiplicity p (Ideal.span {((Module.finrank K L : ℕ) : 𝓞 K)}) :=
    FiniteMultiplicity.of_not_isUnit
      (fun hu' => (HeightOneSpectrum.under (𝓞 K) w).isPrime.ne_top (Ideal.isUnit_iff.mp hu'))
      hN0
  have hs := hfin.le_multiplicity_of_pow_dvd hps
  calc d < e * (d / e + 1) := Nat.lt_mul_div_succ d he0
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.add_le_add_right hs 1)


/-- **The bound for any extension inside a Galois one.** For number fields `K ⊆ L ⊆ M` with
`M/K` Galois and a prime `P` of `𝓞_L` over `𝔭`:
`v_P(𝔇_{L/K}) < e_P·(v_𝔭([M : K]) + 1)`, that is `v_P(𝔇_{L/K}) ≤ e_P - 1 + v_P([M : K])`.
Proof: for a prime `Q` of `𝓞_M` over `P`, `𝔇_{M/K} = 𝔇_{M/L}·𝔇_{L/K}𝓞_M` gives
`e(Q|P)·v_P(𝔇_{L/K}) ≤ v_Q(𝔇_{M/K})`, and `e(Q|𝔭) = e(Q|P)·e_P`
(Mathlib's `Ideal.ramificationIdx_tower`); then `fermatGal_multiplicity_lt` for `M/K`. -/
theorem fermatGal_multiplicity_lt_of_tower {M : Type*} [Field M] [NumberField M] [Algebra L M]
    [Algebra K M] [IsScalarTower K L M] [IsGalois K M] (w : HeightOneSpectrum (𝓞 L)) :
    multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 L)) <
      w.asIdeal.ramificationIdx (𝓞 K) *
        (multiplicity (HeightOneSpectrum.under (𝓞 K) w).asIdeal
          (Ideal.span {((Module.finrank K M : ℕ) : 𝓞 K)}) + 1) := by
  let _ : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 M)) := FractionRing.liftAlgebra _ _
  have : w.asIdeal.IsMaximal := w.isMaximal
  obtain ⟨Q, hQm, hQl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 M) w.asIdeal
  have hu : Q.under (𝓞 L) = w.asIdeal := hQl.over.symm
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply w.ne_bot
    rw [← hu]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  let Q' : HeightOneSpectrum (𝓞 M) := ⟨Q, hQm.isPrime, hQ0⟩
  set v := multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 L))
  set e := w.asIdeal.ramificationIdx (𝓞 K)
  set E := Q.ramificationIdx (𝓞 L)
  set m := multiplicity (HeightOneSpectrum.under (𝓞 K) w).asIdeal
    (Ideal.span {((Module.finrank K M : ℕ) : 𝓞 K)})
  have htow : Q.ramificationIdx (𝓞 K) = e * E :=
    Ideal.ramificationIdx_tower (r := Q) (q := w.asIdeal)
  have hE0 : 0 < E := Ideal.ramificationIdx_pos_of_isDedekindDomain' Q w.ne_bot
  have hund : (HeightOneSpectrum.under (𝓞 K) Q').asIdeal =
      (HeightOneSpectrum.under (𝓞 K) w).asIdeal := by
    simp only [HeightOneSpectrum.under_asIdeal]
    rw [← hu, Ideal.under_under]
  have hgal := fermatGal_multiplicity_lt (K := K) (L := M) Q'
  rw [hund] at hgal
  change multiplicity Q _ < Q.ramificationIdx (𝓞 K) * (m + 1) at hgal
  have hQE : Q ^ E ∣ w.asIdeal.map (algebraMap (𝓞 L) (𝓞 M)) := by
    have h := fermatDiff_pow_ramificationIdx_dvd_map (K := L) (L := M) Q'
    simp only [HeightOneSpectrum.under_asIdeal] at h
    rwa [hu] at h
  have hdvd : Q ^ (E * v) ∣ differentIdeal (𝓞 K) (𝓞 M) := by
    rw [pow_mul, differentIdeal_eq_differentIdeal_mul_differentIdeal (𝓞 K) (𝓞 L) (𝓞 M)]
    refine Dvd.dvd.mul_left ?_ _
    refine (pow_dvd_pow_of_dvd hQE v).trans ?_
    rw [← Ideal.map_pow, Ideal.dvd_iff_le]
    exact Ideal.map_mono (Ideal.le_of_dvd (pow_multiplicity_dvd _ _))
  have hfin : FiniteMultiplicity Q (differentIdeal (𝓞 K) (𝓞 M)) :=
    FiniteMultiplicity.of_not_isUnit (fun hu' => hQm.ne_top (Ideal.isUnit_iff.mp hu'))
      differentIdeal_ne_bot
  have h1 := hfin.le_multiplicity_of_pow_dvd hdvd
  rw [htow] at hgal
  have h2 : E * v < E * (e * (m + 1)) := by
    calc E * v ≤ _ := h1
      _ < e * E * (m + 1) := hgal
      _ = E * (e * (m + 1)) := by ring
  exact Nat.lt_of_mul_lt_mul_left h2


/-- **The log-different bound for the field of the lifted point, from a Galois extension.**
Let `K ⊆ L ⊆ M` be number fields with `M/K` Galois, `x ∈ K \ {0, 1}`, `n ≥ 1`, and
`L = K(u, v)` with `u^n = x`, `v^n = 1 - x`. Then
`log-diff_L ≤ log-diff_K + log-cond_K(x) + log n + log [M : K]`. -/
theorem fermatGal_logDiffNF_le {K L M : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [Field M] [NumberField M] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] [IsGalois K M] {x : K} (hx0 : x ≠ 0) (hx1 : x ≠ 1) {n : ℕ} (hn : 0 < n)
    {u v : L}
    (hu : u ^ n = algebraMap K L x) (hv : v ^ n = 1 - algebraMap K L x)
    (hgen : IntermediateField.adjoin K {u, v} = ⊤) :
    logDiffNF L ≤ logDiffNF K + logCondNF K x + Real.log n +
      Real.log (Module.finrank K M) := by
  classical
  set m := Module.finrank K L with hm
  set N := Module.finrank K M with hN
  set S := (degPb_meetsBoundaryAt_finite hx0 hx1).toFinset with hS
  set R : Ideal (𝓞 K) := ∏ v ∈ S, v.asIdeal with hR
  set J : Ideal (𝓞 L) := Ideal.span {((n : ℕ) : 𝓞 L)} * Ideal.span {((N : ℕ) : 𝓞 L)} *
    R.map (algebraMap (𝓞 K) (𝓞 L)) with hJ
  set D := differentIdeal (𝓞 K) (𝓞 L) with hD
  have hD0 : D ≠ ⊥ := differentIdeal_ne_bot
  have hspan0 : ∀ k : ℕ, k ≠ 0 → Ideal.span {((k : ℕ) : 𝓞 L)} ≠ ⊥ := fun k hk => by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hk
  have hR0 : R ≠ ⊥ := by
    rw [hR, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    exact fun v _ => v.ne_bot
  have hRmap0 : R.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hR0
  have hJ0 : J ≠ ⊥ := by
    rw [hJ, ← Ideal.zero_eq_bot]
    exact mul_ne_zero (mul_ne_zero (hspan0 n hn.ne') (hspan0 N Module.finrank_pos.ne'))
      hRmap0
  -- the different divides `J`
  have hdvd : D ∣ J := by
    refine fermatDiff_dvd_of_multiplicity_le hD0 hJ0 fun w => ?_
    by_cases hw : w.asIdeal ∣ D
    · set vv := HeightOneSpectrum.under (𝓞 K) w
      set e := w.asIdeal.ramificationIdx (𝓞 K)
      set mm := multiplicity vv.asIdeal (Ideal.span {((N : ℕ) : 𝓞 K)})
      have hb : multiplicity w.asIdeal D < e * (mm + 1) :=
        fermatGal_multiplicity_lt_of_tower (M := M) w
      have hwe : w.asIdeal ^ e ∣ vv.asIdeal.map (algebraMap (𝓞 K) (𝓞 L)) :=
        fermatDiff_pow_ramificationIdx_dvd_map w
      have hwk : w.asIdeal ^ (e * mm) ∣ Ideal.span {((N : ℕ) : 𝓞 L)} := by
        rw [pow_mul]
        refine (pow_dvd_pow_of_dvd hwe mm).trans ?_
        rw [← Ideal.map_pow, Ideal.dvd_iff_le, ← map_natCast (algebraMap (𝓞 K) (𝓞 L)),
          ← Set.image_singleton, ← Ideal.map_span]
        exact Ideal.map_mono (Ideal.le_of_dvd (pow_multiplicity_dvd _ _))
      have hcases := fermatDiff_dvd_differentIdeal_imp hu hv hgen w hw
      have hpow : w.asIdeal ^ (e + e * mm) ∣ J := by
        rw [pow_add]
        rcases hcases with hnv | hmeet
        · have hwn : w.asIdeal ^ e ∣ Ideal.span {((n : ℕ) : 𝓞 L)} := by
            refine hwe.trans ?_
            rw [Ideal.dvd_iff_le, ← map_natCast (algebraMap (𝓞 K) (𝓞 L)), ← Set.image_singleton,
              ← Ideal.map_span]
            exact Ideal.map_mono ((Ideal.span_singleton_le_iff_mem _).mpr hnv)
          rw [hJ]
          exact Dvd.dvd.mul_right (mul_dvd_mul hwn hwk) _
        · have hvS : vv ∈ S := (Set.Finite.mem_toFinset _).mpr hmeet
          have hwR : w.asIdeal ^ e ∣ R.map (algebraMap (𝓞 K) (𝓞 L)) := by
            refine hwe.trans ?_
            rw [Ideal.dvd_iff_le]
            exact Ideal.map_mono (Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hvS))
          rw [hJ, mul_assoc, mul_comm (w.asIdeal ^ e)]
          exact Dvd.dvd.mul_left (mul_dvd_mul hwk hwR) _
      have hfin : FiniteMultiplicity w.asIdeal J :=
        FiniteMultiplicity.of_not_isUnit
          (fun hu' => w.isPrime.ne_top (Ideal.isUnit_iff.mp hu')) hJ0
      have := hfin.le_multiplicity_of_pow_dvd hpow
      refine (hb.trans_le ?_).le
      rw [Nat.mul_succ, add_comm]
      exact this
    · rw [multiplicity_eq_zero_of_not_dvd hw]
      exact Nat.zero_le _
  -- norms
  have hDpos : 0 < Ideal.absNorm D :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD0)
  have hJpos : 0 < Ideal.absNorm J :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ0)
  have hnorm : Ideal.absNorm D ≤ Ideal.absNorm J := Nat.le_of_dvd hJpos (map_dvd _ hdvd)
  have hJnorm : Ideal.absNorm J = n ^ Module.finrank ℚ L * N ^ Module.finrank ℚ L *
      (∏ v ∈ S, Ideal.absNorm v.asIdeal) ^ m := by
    rw [hJ, map_mul, map_mul, Ideal.absNorm_span_natCast, Ideal.absNorm_span_natCast,
      Ideal.absNorm_algebraMap, degPb_finrank_int (K := K) L, hR, map_prod,
      RingOfIntegers.rank]
  have hvpos : ∀ v ∈ S, (0 : ℝ) < Ideal.absNorm v.asIdeal := fun v _ => by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Module.finrank_pos
  have hlogJ : Real.log (Ideal.absNorm J) = Module.finrank ℚ L * Real.log n +
      Module.finrank ℚ L * Real.log N +
        m * ∑ v ∈ S, Real.log (Ideal.absNorm v.asIdeal) := by
    rw [hJnorm, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow,
      Nat.cast_prod, Real.log_mul, Real.log_mul, Real.log_pow, Real.log_pow, Real.log_pow,
      Real.log_prod]
    · exact fun v hv => (hvpos v hv).ne'
    · exact (pow_pos hnpos _).ne'
    · exact (pow_pos hNpos _).ne'
    · exact (mul_pos (pow_pos hnpos _) (pow_pos hNpos _)).ne'
    · exact (pow_pos (Finset.prod_pos hvpos) _).ne'
  have hlog : Real.log (Ideal.absNorm D) ≤ Real.log (Ideal.absNorm J) :=
    Real.log_le_log (by exact_mod_cast hDpos) (by exact_mod_cast hnorm)
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hKL : (0 : ℝ) < m := by exact_mod_cast Module.finrank_pos
  have htow : (Module.finrank ℚ K : ℝ) * m = Module.finrank ℚ L := by
    exact_mod_cast Module.finrank_mul_finrank ℚ K L
  rw [degPb_logDiffNF_tower (K := K) L, fermatDiff_logCondNF_eq_sum hx0 hx1]
  set T := ∑ v ∈ S, Real.log (Ideal.absNorm v.asIdeal)
  have key : Real.log (Ideal.absNorm D) / Module.finrank ℚ L ≤
      T / Module.finrank ℚ K + Real.log n + Real.log N := by
    rw [div_le_iff₀ (by rw [← htow]; exact mul_pos hK hKL)]
    calc Real.log (Ideal.absNorm D) ≤ Real.log (Ideal.absNorm J) := hlog
      _ = _ := by
        rw [hlogJ, ← htow]
        field_simp
        ring
      _ ≤ _ := le_rfl
  linarith


universe uK

/-- **A Galois field containing the lifted points.** For `x ∈ K \ {0, 1}` and `n ≥ 1`, the field
`M = K(ζ_n, u, v)` (`ζ_n` a primitive `n`-th root of unity, `u^n = x`, `v^n = 1 - x`) is Galois
over `K`, as the splitting field of `(X^n - 1)(X^n - x)(X^n - (1 - x))`, and
`[M : K] ≤ n³`. -/
theorem fermatGal_galois_field_exists {K : Type uK} [Field K] [NumberField K] {x : K}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) {n : ℕ} (hn : 0 < n) :
    ∃ (M : Type uK) (_ : Field M) (_ : NumberField M) (_ : Algebra K M) (_ : IsGalois K M),
      Module.finrank K M ≤ n ^ 3 ∧ ∃ u v : M, u ^ n = algebraMap K M x ∧
        v ^ n = algebraMap K M (1 - x) := by
  have : NeZero n := NeZero.of_pos hn
  set A := AlgebraicClosure K
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot A n
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K A x) hn
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K A (1 - x)) hn
  have hζ1 : ζ ^ n = algebraMap K A 1 := by rw [hζ.pow_eq_one, map_one]
  set M := IntermediateField.adjoin K {ζ, u, v} with hM
  have hζM : ζ ∈ M := IntermediateField.subset_adjoin K _ (Set.mem_insert _ _)
  have huM : u ∈ M := IntermediateField.subset_adjoin K _
    (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hvM : v ∈ M := IntermediateField.subset_adjoin K _
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hu
    exact hx0 ((map_eq_zero _).mp hu.symm)
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hv
    exact sub_ne_zero.mpr (Ne.symm hx1) ((map_eq_zero _).mp hv.symm)
  have hint : ∀ y ∈ ({ζ, u, v} : Set A), IsIntegral K y := by
    intro y hy
    rcases hy with rfl | rfl | rfl
    · exact IUT.FermatCover.fermatCover_isIntegral_root hn hζ1
    · exact IUT.FermatCover.fermatCover_isIntegral_root hn hu
    · exact IUT.FermatCover.fermatCover_isIntegral_root hn hv
  have : FiniteDimensional K M := IntermediateField.finiteDimensional_adjoin hint
  have : NumberField M := NumberField.of_module_finite K M
  -- `M` is the splitting field of `(X^n - 1)(X^n - x)(X^n - (1 - x))`
  set f : Polynomial K := (Polynomial.X ^ n - Polynomial.C 1) *
    (Polynomial.X ^ n - Polynomial.C x) * (Polynomial.X ^ n - Polynomial.C (1 - x)) with hf
  have hf0 : f ≠ 0 := mul_ne_zero (mul_ne_zero (Polynomial.X_pow_sub_C_ne_zero hn 1)
    (Polynomial.X_pow_sub_C_ne_zero hn x)) (Polynomial.X_pow_sub_C_ne_zero hn (1 - x))
  have haeval : ∀ r : A, Polynomial.aeval r f =
      (r ^ n - algebraMap K A 1) * (r ^ n - algebraMap K A x) *
        (r ^ n - algebraMap K A (1 - x)) := fun r => by
    simp only [hf, map_mul, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
  have hmem : ∀ w r : A, w ∈ M → w ≠ 0 → r ^ n = w ^ n → r ∈ M := by
    intro w r hwM hw0 h
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := r / w)
      (by rw [div_pow, h, div_self (pow_ne_zero _ hw0)])
    have hr : r = w * ζ ^ i := by rw [hi, mul_div_cancel₀ _ hw0]
    rw [hr]
    exact M.mul_mem hwM (pow_mem hζM i)
  have hroots : IntermediateField.adjoin K (f.rootSet A) = M := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro r hr
      rw [Polynomial.mem_rootSet, haeval] at hr
      rcases mul_eq_zero.mp hr.2 with h | h
      · rcases mul_eq_zero.mp h with h | h
        · have h1 : r ^ n = 1 ^ n := by
            rw [one_pow, ← map_one (algebraMap K A)]
            exact sub_eq_zero.mp h
          exact hmem 1 r M.one_mem one_ne_zero h1
        · exact hmem u r huM hu0 (by rw [hu]; exact sub_eq_zero.mp h)
      · exact hmem v r hvM hv0 (by rw [hv]; exact sub_eq_zero.mp h)
    · rw [hM, IntermediateField.adjoin_le_iff]
      have hr : ∀ r : A, Polynomial.aeval r f = 0 → r ∈ IntermediateField.adjoin K (f.rootSet A) :=
        fun r h => IntermediateField.subset_adjoin K _ (Polynomial.mem_rootSet.mpr ⟨hf0, h⟩)
      intro y hy
      rcases hy with rfl | rfl | rfl
      · exact hr _ (by rw [haeval, hζ1, sub_self, zero_mul, zero_mul])
      · exact hr _ (by rw [haeval, hu, sub_self, mul_zero, zero_mul])
      · exact hr _ (by rw [haeval, hv, sub_self, mul_zero])
  have hspl : f.IsSplittingField K M := by
    rw [← hroots]
    exact IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have : Normal K M := Normal.of_isSplittingField f
  have hgal : IsGalois K M := isGalois_iff.mpr ⟨inferInstance, this⟩
  -- the degree
  have hdeg : Module.finrank K M ≤ n ^ 3 := by
    have hMsup : M = IntermediateField.adjoin K {ζ} ⊔
        (IntermediateField.adjoin K {u} ⊔ IntermediateField.adjoin K {v}) := by
      rw [hM, Set.insert_eq, IntermediateField.adjoin_union, Set.insert_eq,
        IntermediateField.adjoin_union]
    rw [hMsup]
    calc _ ≤ _ := IntermediateField.finrank_sup_le _ _
      _ ≤ n * n ^ 2 := Nat.mul_le_mul
          (IUT.FermatCover.fermatCover_finrank_adjoin_root_le hn hζ1)
          (IUT.FermatCover.fermatCover_finrank_adjoin_le hn hu hv)
      _ = n ^ 3 := by ring
  refine ⟨M, inferInstance, inferInstance, inferInstance, hgal, hdeg, ⟨u, huM⟩, ⟨v, hvM⟩,
    ?_, ?_⟩
  · apply Subtype.ext
    simpa using hu
  · apply Subtype.ext
    simpa using hv


/-- **The bound of [GenEll] page 12 for the Fermat cover, unconditionally, with
`c(n) = 4 log n`.** For a number field `K`, `x ∈ K \ {0, 1}` and `n ≥ 1` there are a number field
`L ⊇ K` with `[L : K] ≤ n²` and `u, v ∈ L` with `u^n = x`, `v^n = 1 - x`, `L = K(u, v)`, such that
`log-diff_L ≤ log-diff_K + log-cond_K(x) + 4 log n`. -/
theorem fermatGal_lift_logDiffNF_le {K : Type uK} [Field K] [NumberField K] {x : K}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) {n : ℕ} (hn : 0 < n) :
    ∃ (L : Type uK) (_ : Field L) (_ : NumberField L) (_ : Algebra K L),
      Module.finrank K L ≤ n ^ 2 ∧
        ∃ u v : L, u ^ n = algebraMap K L x ∧ v ^ n = 1 - algebraMap K L x ∧
          IntermediateField.adjoin K {u, v} = ⊤ ∧
          logDiffNF L ≤ logDiffNF K + logCondNF K x + 4 * Real.log n := by
  obtain ⟨M, _, _, _, _, hdegM, u, v, hu, hv⟩ := fermatGal_galois_field_exists hx0 hx1 hn
  set L : IntermediateField K M := IntermediateField.adjoin K {u, v} with hL
  have : NumberField L := NumberField.of_module_finite K L
  have huL : u ∈ L := IntermediateField.subset_adjoin K _ (Set.mem_insert u {v})
  have hvL : v ∈ L := IntermediateField.subset_adjoin K _ (Set.mem_insert_of_mem u rfl)
  have hdegL : Module.finrank K L ≤ n ^ 2 := by
    have hLsup : L = IntermediateField.adjoin K {u} ⊔ IntermediateField.adjoin K {v} := by
      rw [hL, Set.insert_eq, IntermediateField.adjoin_union]
    rw [hLsup]
    exact IUT.FermatCover.fermatCover_finrank_adjoin_le hn hu hv
  have hu' : (⟨u, huL⟩ : L) ^ n = algebraMap K L x := by
    apply Subtype.ext
    simpa using hu
  have hv' : (⟨v, hvL⟩ : L) ^ n = 1 - algebraMap K L x := by
    apply Subtype.ext
    simpa [map_sub] using hv
  have hgen : IntermediateField.adjoin K {(⟨u, huL⟩ : L), ⟨v, hvL⟩} = ⊤ := by
    apply IntermediateField.lift_injective L
    rw [IntermediateField.lift_adjoin, IntermediateField.lift_top, Set.image_insert_eq,
      Set.image_singleton]
  refine ⟨L, inferInstance, inferInstance, inferInstance, hdegL, _, _, hu', hv', hgen, ?_⟩
  have h := fermatGal_logDiffNF_le (M := M) hx0 hx1 hn hu' hv' hgen
  have hlog : Real.log (Module.finrank K M) ≤ 3 * Real.log n := by
    rw [show (3 : ℝ) * Real.log n = ((3 : ℕ) : ℝ) * Real.log n by norm_num, ← Real.log_pow]
    exact Real.log_le_log (by exact_mod_cast Module.finrank_pos) (by exact_mod_cast hdegM)
  linarith

end IUT.FermatDifferentGalois
