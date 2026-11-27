import IUT.Applications.FermatDifferentGalois

/-!
# The classical bound for the different of number fields, through inertia fields

Sources: Mochizuki, *Arithmetic Elliptic Curves in General Position* ([GenEll]), Proposition 1.7
and its proof (pages 9 and 10), which rest on "the elementary theory of differents", and the use of
Proposition 1.7 (i) in the proof of Theorem 2.1 (page 12, `log-diff_Y ≲ log-diff_X + log-cond_D`).
Pages read for this file: [GenEll] pages 9, 10 and 12. Pages checked against rendered images:
[GenEll] pages 9, 10 and 12. The bound proved
here is a classical theorem of algebraic number theory; it is not printed in [GenEll] or in the
IUT papers, and no page of them is formalized here.

**What this file is.** `IUT.FermatDifferent` states the classical upper bound for the different,
`v_P(𝔇_{L/K}) ≤ e_P - 1 + v_P(e_P)` for number fields `K ⊆ L` and a prime `P` of `𝓞_L` with
ramification index `e_P` over `𝓞_K` (`fermatDiff_classicalDifferentBoundStatement`, where
`v_P(e_P)` is the multiplicity of `P` in `e_P·𝓞_L`), and uses it as an assumption;
`IUT.FermatDifferentGalois` proves the weaker `v_P(𝔇_{L/K}) ≤ e_P - 1 + v_P([M : K])` for `L`
inside a Galois `M/K`. This file proves the classical bound itself, without completions, by the
decomposition of the problem along inertia fields (Mathlib's `Ideal.inertia`, `IsGaloisGroup`,
`Ideal.card_inertia_eq_ramificationIdxIn`).

**What this file proves.**
1. The trace bound for a prime alone over its base (`diffBr_multiplicity_lt_of_unique`): if `P`
   is the only prime of `𝓞_E` over `𝔭`, then `v_P(𝔇_{E/F}) < e_P·(v_𝔭([E : F]) + 1)`.
2. The inertia field (`diffBr_inertia_facts`): for `M/F` Galois, `Q` a prime of `𝓞_M` and `E` its
   inertia field, `Q ∩ 𝓞_E` is unramified over `𝓞_F`, `e(Q | Q ∩ 𝓞_E) = [M : E]`, and `Q` is the
   only prime over `Q ∩ 𝓞_E`. Mathlib v4.36.0 has these facts for the decomposition field only.
3. The Galois case (`diffBr_multiplicity_le_of_isGalois`): for `M/K` Galois,
   `v_P(𝔇_{M/K}) ≤ e_P - 1 + v_P(e_P)`. With `T` the inertia field, `𝔇_{M/K} = 𝔇_{M/T}·𝔇_{T/K}𝓞_M`,
   `P` does not divide the second factor, and item 1 applies to `M/T`, of degree `e_P`.
4. The general case (`diffBr_classical_bound`, and `diffBr_statement`, which is
   `fermatDiff_classicalDifferentBoundStatement`). For `K ⊆ L ⊆ M` with `M/K` Galois
   (`diffBr_multiplicity_le_of_tower`; `M` is the normal closure of `L/K` in an algebraic closure
   of `L`) and `Q` over `P`: let `T` be the inertia field of `Q` in `M/K` and `E` that in `M/L`.
   Then `T ⊆ E`, `Q ∩ 𝓞_E` is unramified over `P`, `Q ∩ 𝓞_T` is unramified over `𝓞_K`, and
   `Q ∩ 𝓞_E` is the only prime of `𝓞_E` over `Q ∩ 𝓞_T`, with ramification index `[E : T] = e_P`.
   So `v_P(𝔇_{L/K}) ≤ v_{Q ∩ 𝓞_E}(𝔇_{E/K}) = v_{Q ∩ 𝓞_E}(𝔇_{E/T})`, and item 1 for `E/T` gives the
   bound (`diffBr_bound_of_inertia_towers`).
5. The two theorems of `IUT.FermatDifferent` that assumed the classical bound, without the
   assumption (`diffBr_fermat_logDiffNF_le`, `diffBr_fermat_lift_logDiffNF_le`). Their constants
   (`log n + log([L : K]!)`, and `log n + log((n²)!)` uniformly) are not smaller than those of
   `IUT.FermatDifferentGalois`: the uniform constant there is `4 log n`, and for `M` the Galois
   closure of `L/K` the classical fact that `[M : K]` divides `[L : K]!` (not proved here) makes
   `log n + log [M : K]` at most `log n + log([L : K]!)`.

**Not proved.**
* Proposition 1.7 of [GenEll] and any statement of the papers. The claim printed in the proof of
  Proposition 1.7 (i) on page 10 (for finite Galois extensions `L/K` of finite extensions of `ℚ_p`
  of bounded degree, the different contains `p^n·𝒪_L` with `n` depending only on `p` and the
  degree) is local, and the bound proved here concerns number fields; no global analog of the
  claim is stated or proved here.
* The comparison of the global different with the differents of the completions: not needed for
  the bound above. Mathlib v4.36.0 has no lemma relating `differentIdeal` with localization or
  with `IsDedekindDomain.HeightOneSpectrum.adicCompletion`.
-/

open NumberField IsDedekindDomain Pointwise
open IUT.VojtaNumberField IUT.FermatDifferent IUT.FermatDifferentGalois

namespace IUT.DifferentBridge

/-- If `P` is the only prime of `𝓞_E` over `𝔭 = P ∩ 𝓞_F` and `P^(e_P s) ∣ 𝔇_{E/F}`, then
`𝔭^s 𝓞_E ∣ 𝔇_{E/F}` (here `𝔭𝓞_E = P^{e_P}`). -/
theorem diffBr_map_pow_dvd_of_unique {F E : Type*} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (w : HeightOneSpectrum (𝓞 E))
    (huniq : ∀ q : HeightOneSpectrum (𝓞 E),
      q.asIdeal.under (𝓞 F) = w.asIdeal.under (𝓞 F) → q = w) (s : ℕ)
    (hw : w.asIdeal ^ (w.asIdeal.ramificationIdx (𝓞 F) * s) ∣ differentIdeal (𝓞 F) (𝓞 E)) :
    ((HeightOneSpectrum.under (𝓞 F) w).asIdeal ^ s).map (algebraMap (𝓞 F) (𝓞 E)) ∣
      differentIdeal (𝓞 F) (𝓞 E) := by
  set p := (HeightOneSpectrum.under (𝓞 F) w).asIdeal with hp
  have hpm : p.IsMaximal := (HeightOneSpectrum.under (𝓞 F) w).isMaximal
  have hpS : p.map (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot (HeightOneSpectrum.under (𝓞 F) w).ne_bot
  have hD0 : differentIdeal (𝓞 F) (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  refine fermatDiff_dvd_of_multiplicity_le
    (by rw [Ideal.map_pow]; exact pow_ne_zero _ hpS) hD0 fun q => ?_
  have hqprime : Prime q.asIdeal := Ideal.prime_of_isPrime q.ne_bot q.isPrime
  rw [Ideal.map_pow, multiplicity_pow hqprime]
  by_cases hq : q.asIdeal.under (𝓞 F) = p
  · rw [huniq q hq]
    have : w.asIdeal.LiesOver p := ⟨rfl⟩
    rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity p w.asIdeal hpS, mul_comm]
    have hfin : FiniteMultiplicity w.asIdeal (differentIdeal (𝓞 F) (𝓞 E)) :=
      FiniteMultiplicity.of_not_isUnit
        (fun hu' => w.isPrime.ne_top (Ideal.isUnit_iff.mp hu')) hD0
    exact hfin.le_multiplicity_of_pow_dvd hw
  · have hnd : ¬ q.asIdeal ∣ p.map (algebraMap (𝓞 F) (𝓞 E)) := by
      intro hd
      apply hq
      rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap] at hd
      exact (hpm.eq_of_le (Ideal.comap_isPrime _ q.asIdeal).ne_top hd).symm
    rw [multiplicity_eq_zero_of_not_dvd hnd, mul_zero]
    exact Nat.zero_le _

/-- **The trace bound at a prime that is alone over its base.** If `P` is the only prime of
`𝓞_E` over `𝔭 = P ∩ 𝓞_F`, then `v_P(𝔇_{E/F}) < e_P·(v_𝔭([E : F]) + 1)`. The proof is that of
the Galois case `IUT.FermatDifferentGalois.fermatGal_multiplicity_lt`, with the uniqueness of `P`
in place of the Galois action: for `s = ⌊v_P(𝔇)/e_P⌋`, `𝔭^s 𝓞_E ∣ 𝔇_{E/F}`, and the trace step
`IUT.FermatDifferentGalois.fermatGal_dvd_span_finrank_of_map_dvd` gives `s ≤ v_𝔭([E : F])`. -/
theorem diffBr_multiplicity_lt_of_unique {F E : Type*} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (w : HeightOneSpectrum (𝓞 E))
    (huniq : ∀ q : HeightOneSpectrum (𝓞 E),
      q.asIdeal.under (𝓞 F) = w.asIdeal.under (𝓞 F) → q = w) :
    multiplicity w.asIdeal (differentIdeal (𝓞 F) (𝓞 E)) <
      w.asIdeal.ramificationIdx (𝓞 F) *
        (multiplicity (HeightOneSpectrum.under (𝓞 F) w).asIdeal
          (Ideal.span {((Module.finrank F E : ℕ) : 𝓞 F)}) + 1) := by
  set p := (HeightOneSpectrum.under (𝓞 F) w).asIdeal with hp
  set d := multiplicity w.asIdeal (differentIdeal (𝓞 F) (𝓞 E)) with hd
  set e := w.asIdeal.ramificationIdx (𝓞 F) with he
  have he0 : 0 < e := by
    have : w.asIdeal.LiesOver p := ⟨rfl⟩
    exact Ideal.ramificationIdx_pos_of_isDedekindDomain' w.asIdeal
      (HeightOneSpectrum.under (𝓞 F) w).ne_bot
  have hw : w.asIdeal ^ (e * (d / e)) ∣ differentIdeal (𝓞 F) (𝓞 E) :=
    (pow_dvd_pow _ (Nat.mul_div_le d e)).trans (pow_multiplicity_dvd _ _)
  have hps := fermatGal_dvd_span_finrank_of_map_dvd (L := E) (p ^ (d / e))
    (pow_ne_zero _ (HeightOneSpectrum.under (𝓞 F) w).ne_bot)
    (diffBr_map_pow_dvd_of_unique w huniq _ hw)
  have hN0 : Ideal.span {((Module.finrank F E : ℕ) : 𝓞 F)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast Module.finrank_pos.ne'
  have hfin : FiniteMultiplicity p (Ideal.span {((Module.finrank F E : ℕ) : 𝓞 F)}) :=
    FiniteMultiplicity.of_not_isUnit
      (fun hu' => (HeightOneSpectrum.under (𝓞 F) w).isPrime.ne_top (Ideal.isUnit_iff.mp hu'))
      hN0
  have hs := hfin.le_multiplicity_of_pow_dvd hps
  calc d < e * (d / e + 1) := Nat.lt_mul_div_succ d he0
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.add_le_add_right hs 1)

/-- For `n ≠ 0` and a prime `P` of `𝓞_E` over `𝔭` of `𝓞_F`: `v_P(n·𝓞_E) = e_P·v_𝔭(n·𝓞_F)`
(Mathlib's `Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul`). -/
theorem diffBr_multiplicity_span_natCast {F E : Type*} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (w : HeightOneSpectrum (𝓞 E)) {n : ℕ} (hn : n ≠ 0) :
    multiplicity w.asIdeal (Ideal.span {((n : ℕ) : 𝓞 E)}) =
      w.asIdeal.ramificationIdx (𝓞 F) *
        multiplicity (HeightOneSpectrum.under (𝓞 F) w).asIdeal
          (Ideal.span {((n : ℕ) : 𝓞 F)}) := by
  set v := HeightOneSpectrum.under (𝓞 F) w
  have : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have hI : Ideal.span {((n : ℕ) : 𝓞 F)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hn
  have hIE : Ideal.span {((n : ℕ) : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hn
  have hmap : (Ideal.span {((n : ℕ) : 𝓞 F)}).map (algebraMap (𝓞 F) (𝓞 E)) =
      Ideal.span {((n : ℕ) : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have h := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul
    (R := 𝓞 F) (S := 𝓞 E) hI
    (Ideal.prime_of_isPrime v.ne_bot v.isPrime).irreducible
    (Ideal.prime_of_isPrime w.ne_bot w.isPrime).irreducible w.ne_bot
  rw [hmap, Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot] at h
  have hfinE : FiniteMultiplicity w.asIdeal (Ideal.span {((n : ℕ) : 𝓞 E)}) :=
    FiniteMultiplicity.of_not_isUnit
      (fun hu' => w.isPrime.ne_top (Ideal.isUnit_iff.mp hu')) hIE
  have hfinF : FiniteMultiplicity v.asIdeal (Ideal.span {((n : ℕ) : 𝓞 F)}) :=
    FiniteMultiplicity.of_not_isUnit
      (fun hu' => v.isPrime.ne_top (Ideal.isUnit_iff.mp hu')) hI
  rw [hfinE.emultiplicity_eq_multiplicity, hfinF.emultiplicity_eq_multiplicity] at h
  exact_mod_cast h

/-- A prime of `𝓞_T` with ramification index `1` over `𝓞_K` does not divide `𝔇_{T/K}`
(Mathlib's `dvd_differentIdeal_iff` and `Ideal.ramificationIdx_eq_one_iff`; the residue fields
are finite, hence perfect). -/
theorem diffBr_not_dvd_of_ramificationIdx_eq_one {K T : Type*} [Field K] [NumberField K]
    [Field T] [NumberField T] [Algebra K T] (q : HeightOneSpectrum (𝓞 T))
    (h : q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    ¬ q.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 T) := by
  let _ : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 T)) := FractionRing.liftAlgebra _ _
  rw [dvd_differentIdeal_iff, not_not]
  exact (Ideal.ramificationIdx_eq_one_iff).mp h

/-- **The bound through an intermediate field.** Let `K ⊆ T ⊆ E` be number fields and `w` a
prime of `𝓞_E`. Suppose that `w ∩ 𝓞_T` is unramified over `𝓞_K`, that `w` is the only prime of
`𝓞_E` over `w ∩ 𝓞_T`, and that `e(w | w ∩ 𝓞_T) = [E : T]`. Then
`v_w(𝔇_{E/K}) ≤ e_w - 1 + v_w(e_w)`, with `e_w` the ramification index of `w` over `𝓞_K`. Proof:
`𝔇_{E/K} = 𝔇_{E/T}·𝔇_{T/K}𝓞_E` and `w` does not divide the second factor; `e_w = e(w | w ∩ 𝓞_T)`
by the tower formula; then `diffBr_multiplicity_lt_of_unique` for `E/T` and
`v_w(e·𝓞_E) = e·v_{w ∩ 𝓞_T}(e·𝓞_T)`. -/
theorem diffBr_bound_of_inertia_tower {K T E : Type*} [Field K] [NumberField K] [Field T]
    [NumberField T] [Field E] [NumberField E] [Algebra K T] [Algebra T E] [Algebra K E]
    [IsScalarTower K T E] (w : HeightOneSpectrum (𝓞 E))
    (hT : (HeightOneSpectrum.under (𝓞 T) w).asIdeal.ramificationIdx (𝓞 K) = 1)
    (huniq : ∀ q : HeightOneSpectrum (𝓞 E),
      q.asIdeal.under (𝓞 T) = w.asIdeal.under (𝓞 T) → q = w)
    (hdeg : w.asIdeal.ramificationIdx (𝓞 T) = Module.finrank T E) :
    multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 E)) ≤
      w.asIdeal.ramificationIdx (𝓞 K) - 1 +
        multiplicity w.asIdeal
          (Ideal.span {((w.asIdeal.ramificationIdx (𝓞 K) : ℕ) : 𝓞 E)}) := by
  let _ : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 E)) := FractionRing.liftAlgebra _ _
  set q := HeightOneSpectrum.under (𝓞 T) w with hqdef
  have htow : w.asIdeal.ramificationIdx (𝓞 K) =
      q.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.ramificationIdx (𝓞 T) := by
    have : w.asIdeal.LiesOver q.asIdeal := ⟨rfl⟩
    exact Ideal.ramificationIdx_tower (r := w.asIdeal) (q := q.asIdeal)
  have he : w.asIdeal.ramificationIdx (𝓞 K) = w.asIdeal.ramificationIdx (𝓞 T) := by
    rw [htow, hT, one_mul]
  have hqnd := diffBr_not_dvd_of_ramificationIdx_eq_one (K := K) q hT
  have hwnd : ¬ w.asIdeal ∣ (differentIdeal (𝓞 K) (𝓞 T)).map (algebraMap (𝓞 T) (𝓞 E)) := by
    intro h
    apply hqnd
    rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap] at h
    rw [Ideal.dvd_iff_le]
    exact h
  have hwp : Prime w.asIdeal := Ideal.prime_of_isPrime w.ne_bot w.isPrime
  have hD0 : differentIdeal (𝓞 K) (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  have hmul : multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 E)) =
      multiplicity w.asIdeal (differentIdeal (𝓞 T) (𝓞 E)) := by
    have hfin : FiniteMultiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 E)) :=
      FiniteMultiplicity.of_not_isUnit
        (fun hu' => w.isPrime.ne_top (Ideal.isUnit_iff.mp hu')) hD0
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal (𝓞 K) (𝓞 T) (𝓞 E)] at hfin ⊢
    rw [multiplicity_mul hwp hfin, multiplicity_eq_zero_of_not_dvd hwnd, add_zero]
  have hcore := diffBr_multiplicity_lt_of_unique (F := T) (E := E) w huniq
  rw [← hdeg] at hcore
  have he0 : w.asIdeal.ramificationIdx (𝓞 T) ≠ 0 := by
    have : w.asIdeal.LiesOver q.asIdeal := ⟨rfl⟩
    exact (Ideal.ramificationIdx_pos_of_isDedekindDomain' w.asIdeal q.ne_bot).ne'
  have hspan := diffBr_multiplicity_span_natCast (F := T) w he0
  rw [he, hmul, hspan]
  set e := w.asIdeal.ramificationIdx (𝓞 T)
  set m := multiplicity (HeightOneSpectrum.under (𝓞 T) w).asIdeal
    (Ideal.span {((e : ℕ) : 𝓞 T)})
  set d := multiplicity w.asIdeal (differentIdeal (𝓞 T) (𝓞 E))
  have h2 : e * (m + 1) = e * m + e := by ring
  omega

/-- **The inertia field.** Let `M/F` be a Galois extension of number fields, `Q` a prime of
`𝓞_M`, and `E` an intermediate field such that `M/E` is Galois with group the inertia group
`I(Q) ⊆ Gal(M/F)` (an inertia field of `Q`). Then `Q ∩ 𝓞_E` is unramified over `𝓞_F`,
`e(Q | Q ∩ 𝓞_E) = [M : E]`, and `Q` is the only prime of `𝓞_M` over `Q ∩ 𝓞_E`. Proof: Mathlib's
`Ideal.card_inertia_eq_ramificationIdxIn`, once for `Gal(M/F)` over `𝓞_F` and once for `I(Q)`
acting on `𝓞_M` over `𝓞_E` (where the inertia group of `Q` is all of `I(Q)`), gives
`e(Q | Q ∩ 𝓞_E) = |I(Q)| = e(Q | Q ∩ 𝓞_F)`, so the tower formula gives
`e(Q ∩ 𝓞_E | Q ∩ 𝓞_F) = 1`; `|I(Q)| = [M : E]`; and `I(Q)` acts transitively on the primes over
`Q ∩ 𝓞_E` while fixing `Q`. Mathlib proves the corresponding facts for the decomposition field
only (`IsDecompositionField.ramificationIdx_eq`). -/
theorem diffBr_inertia_facts {F E M : Type*} [Field F] [NumberField F] [Field E]
    [NumberField E] [Field M] [NumberField M] [Algebra F E] [Algebra E M] [Algebra F M]
    [IsScalarTower F E M] [IsGalois F M] (Q : HeightOneSpectrum (𝓞 M))
    [IsGaloisGroup (Ideal.inertia (M ≃ₐ[F] M) Q.asIdeal) E M] :
    (HeightOneSpectrum.under (𝓞 E) Q).asIdeal.ramificationIdx (𝓞 F) = 1 ∧
      Q.asIdeal.ramificationIdx (𝓞 E) = Module.finrank E M ∧
      ∀ Q' : HeightOneSpectrum (𝓞 M),
        Q'.asIdeal.under (𝓞 E) = Q.asIdeal.under (𝓞 E) → Q' = Q := by
  let G := M ≃ₐ[F] M
  let I := Ideal.inertia G Q.asIdeal
  have : IsGaloisGroup G (𝓞 F) (𝓞 M) := IsGaloisGroup.of_isFractionRing G (𝓞 F) (𝓞 M) F M
  have : IsGaloisGroup I (𝓞 E) (𝓞 M) := IsGaloisGroup.of_isFractionRing I (𝓞 E) (𝓞 M) E M
  set p := Q.asIdeal.under (𝓞 F) with hp
  set q := HeightOneSpectrum.under (𝓞 E) Q with hq
  have : Q.asIdeal.LiesOver p := ⟨rfl⟩
  have : Q.asIdeal.LiesOver q.asIdeal := ⟨rfl⟩
  have h1 : Nat.card I = Q.asIdeal.ramificationIdx (𝓞 F) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn p Q.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx p Q.asIdeal G]
  have h2 : Nat.card (Q.asIdeal.inertia I) = Q.asIdeal.ramificationIdx (𝓞 E) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn q.asIdeal Q.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx q.asIdeal Q.asIdeal I]
  have htop : Q.asIdeal.inertia I = ⊤ := by
    ext σ
    simp only [Subgroup.mem_top, iff_true, Ideal.mem_inertia]
    intro x
    exact Ideal.mem_inertia.mp σ.2 x
  have hcardI : Nat.card I = Q.asIdeal.ramificationIdx (𝓞 E) := by
    rw [← h2, htop, Subgroup.card_top]
  have hpos : 0 < Q.asIdeal.ramificationIdx (𝓞 E) :=
    Ideal.ramificationIdx_pos_of_isDedekindDomain' Q.asIdeal q.ne_bot
  refine ⟨?_, ?_, ?_⟩
  · have htow : Q.asIdeal.ramificationIdx (𝓞 F) =
        q.asIdeal.ramificationIdx (𝓞 F) * Q.asIdeal.ramificationIdx (𝓞 E) :=
      Ideal.ramificationIdx_tower (r := Q.asIdeal) (q := q.asIdeal)
    rw [← h1, hcardI] at htow
    nlinarith
  · rw [← hcardI, IsGaloisGroup.card_eq_finrank I E M]
  · intro Q' hQ'
    have : Q'.asIdeal.LiesOver q.asIdeal := ⟨hQ'.symm⟩
    obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup q.asIdeal Q.asIdeal Q'.asIdeal I
    have hst := Ideal.inertia_le_stabilizer Q.asIdeal σ.2
    rw [MulAction.mem_stabilizer_iff] at hst
    apply HeightOneSpectrum.ext
    rw [← hσ]
    exact hst

/-- For number fields `T ⊆ E ⊆ M` and a prime `Q` of `𝓞_M`: if `Q` is the only prime of `𝓞_M`
over `Q ∩ 𝓞_T`, then `Q ∩ 𝓞_E` is the only prime of `𝓞_E` over `Q ∩ 𝓞_T` (every prime of `𝓞_E`
lies under a prime of `𝓞_M`). -/
theorem diffBr_unique_mid {T E M : Type*} [Field T] [NumberField T] [Field E] [NumberField E]
    [Field M] [NumberField M] [Algebra T E] [Algebra E M] [Algebra T M] [IsScalarTower T E M]
    (Q : HeightOneSpectrum (𝓞 M))
    (huniq : ∀ Q' : HeightOneSpectrum (𝓞 M),
      Q'.asIdeal.under (𝓞 T) = Q.asIdeal.under (𝓞 T) → Q' = Q) :
    ∀ q : HeightOneSpectrum (𝓞 E),
      q.asIdeal.under (𝓞 T) = (HeightOneSpectrum.under (𝓞 E) Q).asIdeal.under (𝓞 T) →
        q = HeightOneSpectrum.under (𝓞 E) Q := by
  intro q hq
  have : q.asIdeal.IsMaximal := q.isMaximal
  obtain ⟨Q', hQ'm, hQ'l⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 M) q.asIdeal
  have hu : Q'.under (𝓞 E) = q.asIdeal := hQ'l.over.symm
  have hQ'0 : Q' ≠ ⊥ := by
    rintro rfl
    apply q.ne_bot
    rw [← hu]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  have key := huniq ⟨Q', hQ'm.isPrime, hQ'0⟩ (by
    change Q'.under (𝓞 T) = Q.asIdeal.under (𝓞 T)
    rw [← Ideal.under_under (B := 𝓞 E) Q', hu, hq, HeightOneSpectrum.under_asIdeal,
      Ideal.under_under])
  apply HeightOneSpectrum.ext
  rw [← hu, HeightOneSpectrum.under_asIdeal]
  have := congrArg HeightOneSpectrum.asIdeal key
  rw [← this]

/-- For number fields `T ⊆ E ⊆ M` and a prime `Q` of `𝓞_M`: if `e(Q | Q ∩ 𝓞_T) = [M : T]`, then
`e(Q ∩ 𝓞_E | Q ∩ 𝓞_T) = [E : T]` (in `e(Q | Q ∩ 𝓞_T) = e(Q ∩ 𝓞_E | Q ∩ 𝓞_T)·e(Q | Q ∩ 𝓞_E)` each
factor is at most the corresponding degree). -/
theorem diffBr_ramificationIdx_mid {T E M : Type*} [Field T] [NumberField T] [Field E]
    [NumberField E] [Field M] [NumberField M] [Algebra T E] [Algebra E M] [Algebra T M]
    [IsScalarTower T E M] (Q : HeightOneSpectrum (𝓞 M))
    (hdeg : Q.asIdeal.ramificationIdx (𝓞 T) = Module.finrank T M) :
    (HeightOneSpectrum.under (𝓞 E) Q).asIdeal.ramificationIdx (𝓞 T) = Module.finrank T E := by
  set P := HeightOneSpectrum.under (𝓞 E) Q
  have htow : Q.asIdeal.ramificationIdx (𝓞 T) =
      P.asIdeal.ramificationIdx (𝓞 T) * Q.asIdeal.ramificationIdx (𝓞 E) := by
    have : Q.asIdeal.LiesOver P.asIdeal := ⟨rfl⟩
    exact Ideal.ramificationIdx_tower (r := Q.asIdeal) (q := P.asIdeal)
  have h1 := fermatDiff_ramificationIdx_le_finrank (K := T) (L := E) P
  have h2 := fermatDiff_ramificationIdx_le_finrank (K := E) (L := M) Q
  have hmul := Module.finrank_mul_finrank T E M
  have hpos : 0 < Module.finrank E M := Module.finrank_pos
  rw [hdeg, ← hmul] at htow
  by_contra hne
  have hlt : P.asIdeal.ramificationIdx (𝓞 T) < Module.finrank T E := lt_of_le_of_ne h1 hne
  have h3 : P.asIdeal.ramificationIdx (𝓞 T) * Q.asIdeal.ramificationIdx (𝓞 E) <
      Module.finrank T E * Module.finrank E M :=
    calc _ ≤ P.asIdeal.ramificationIdx (𝓞 T) * Module.finrank E M := Nat.mul_le_mul_left _ h2
      _ < _ := Nat.mul_lt_mul_of_pos_right hlt hpos
  omega

/-- **The reduction to an intermediate field.** Let `K ⊆ L ⊆ E` and `K ⊆ T ⊆ E` be number
fields, `w` a prime of `𝓞_E` and `P = w ∩ 𝓞_L`. If `w` is unramified over `P` and `T ⊆ E`
satisfies the hypotheses of `diffBr_bound_of_inertia_tower` at `w`, then
`v_P(𝔇_{L/K}) ≤ e_P - 1 + v_P(e_P)`. Proof: `P^v ∣ 𝔇_{L/K}` gives
`w^v ∣ 𝔇_{L/K}𝓞_E ∣ 𝔇_{E/K}`; `e_w = e_P` and `v_w(e·𝓞_E) = v_P(e·𝓞_L)` because `e(w | P) = 1`. -/
theorem diffBr_bound_of_inertia_towers {K L T E : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Field T] [NumberField T] [Field E] [NumberField E] [Algebra K L]
    [Algebra K T] [Algebra L E] [Algebra T E] [Algebra K E] [IsScalarTower K L E]
    [IsScalarTower K T E] (w : HeightOneSpectrum (𝓞 E))
    (hL : w.asIdeal.ramificationIdx (𝓞 L) = 1)
    (hT : (HeightOneSpectrum.under (𝓞 T) w).asIdeal.ramificationIdx (𝓞 K) = 1)
    (huniq : ∀ q : HeightOneSpectrum (𝓞 E),
      q.asIdeal.under (𝓞 T) = w.asIdeal.under (𝓞 T) → q = w)
    (hdeg : w.asIdeal.ramificationIdx (𝓞 T) = Module.finrank T E) :
    multiplicity (HeightOneSpectrum.under (𝓞 L) w).asIdeal (differentIdeal (𝓞 K) (𝓞 L)) ≤
      (HeightOneSpectrum.under (𝓞 L) w).asIdeal.ramificationIdx (𝓞 K) - 1 +
        multiplicity (HeightOneSpectrum.under (𝓞 L) w).asIdeal
          (Ideal.span {(((HeightOneSpectrum.under (𝓞 L) w).asIdeal.ramificationIdx (𝓞 K) : ℕ) :
            𝓞 L)}) := by
  let _ : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 E)) := FractionRing.liftAlgebra _ _
  set P := HeightOneSpectrum.under (𝓞 L) w with hPdef
  have h1 := diffBr_bound_of_inertia_tower (K := K) (T := T) w hT huniq hdeg
  have htow : w.asIdeal.ramificationIdx (𝓞 K) =
      P.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.ramificationIdx (𝓞 L) := by
    have : w.asIdeal.LiesOver P.asIdeal := ⟨rfl⟩
    exact Ideal.ramificationIdx_tower (r := w.asIdeal) (q := P.asIdeal)
  rw [hL, mul_one] at htow
  rw [htow] at h1
  have he0 : P.asIdeal.ramificationIdx (𝓞 K) ≠ 0 := by
    have : P.asIdeal.LiesOver (HeightOneSpectrum.under (𝓞 K) P).asIdeal := ⟨rfl⟩
    exact (Ideal.ramificationIdx_pos_of_isDedekindDomain' P.asIdeal
      (HeightOneSpectrum.under (𝓞 K) P).ne_bot).ne'
  rw [diffBr_multiplicity_span_natCast (F := L) w he0, hL, one_mul] at h1
  refine le_trans ?_ h1
  have hD0 : differentIdeal (𝓞 K) (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  have hfin : FiniteMultiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 E)) :=
    FiniteMultiplicity.of_not_isUnit
      (fun hu' => w.isPrime.ne_top (Ideal.isUnit_iff.mp hu')) hD0
  refine hfin.le_multiplicity_of_pow_dvd ?_
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal (𝓞 K) (𝓞 L) (𝓞 E)]
  refine Dvd.dvd.mul_left ?_ _
  have hwP : w.asIdeal ∣ P.asIdeal.map (algebraMap (𝓞 L) (𝓞 E)) := by
    rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
    exact le_rfl
  refine (pow_dvd_pow_of_dvd hwP _).trans ?_
  rw [← Ideal.map_pow, Ideal.dvd_iff_le]
  exact Ideal.map_mono (Ideal.le_of_dvd (pow_multiplicity_dvd _ _))

/-- **The sharp bound for a Galois extension.** For a Galois extension `M/K` of number fields
and a prime `P` of `𝓞_M` with ramification index `e_P` over `𝓞_K`:
`v_P(𝔇_{M/K}) ≤ e_P - 1 + v_P(e_P)`. Proof: with `T` the inertia field of `P`, `P ∩ 𝓞_T` is
unramified over `𝓞_K` and `M/T` has degree `e_P` with `P` alone over `P ∩ 𝓞_T`
(`diffBr_inertia_facts`); then `diffBr_bound_of_inertia_tower`. -/
theorem diffBr_multiplicity_le_of_isGalois {K M : Type*} [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [IsGalois K M] (w : HeightOneSpectrum (𝓞 M)) :
    multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 M)) ≤
      w.asIdeal.ramificationIdx (𝓞 K) - 1 +
        multiplicity w.asIdeal
          (Ideal.span {((w.asIdeal.ramificationIdx (𝓞 K) : ℕ) : 𝓞 M)}) := by
  let T : IntermediateField K M :=
    FixedPoints.intermediateField (Ideal.inertia (M ≃ₐ[K] M) w.asIdeal)
  obtain ⟨hT, hdeg, huniq⟩ := diffBr_inertia_facts (F := K) (E := T) (M := M) w
  exact diffBr_bound_of_inertia_tower (K := K) (T := T) w hT huniq hdeg


/-- **The bound for a subextension of a Galois extension.** For number fields `K ⊆ L ⊆ M` with
`M/K` Galois and a prime `P` of `𝓞_L`: `v_P(𝔇_{L/K}) ≤ e_P - 1 + v_P(e_P)`. Proof: take a prime
`Q` of `𝓞_M` over `P`, `T` the inertia field of `Q` in `M/K` and `E` that in `M/L`. An element
of `M` fixed by the inertia group of `Q` over `K` is fixed by the inertia group of `Q` over `L`
(a subgroup of it), so `T ⊆ E`. By `diffBr_inertia_facts`, `Q ∩ 𝓞_E` is unramified over `P`
and `Q ∩ 𝓞_T` over `𝓞_K`, `Q` is alone over `Q ∩ 𝓞_T` with `e(Q | Q ∩ 𝓞_T) = [M : T]`, hence
(`diffBr_unique_mid`, `diffBr_ramificationIdx_mid`) `Q ∩ 𝓞_E` is alone over `Q ∩ 𝓞_T` with
`e = [E : T]`; then `diffBr_bound_of_inertia_towers`. -/
theorem diffBr_multiplicity_le_of_tower {K L M : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Field M] [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] [IsGalois K M] (P : HeightOneSpectrum (𝓞 L)) :
    multiplicity P.asIdeal (differentIdeal (𝓞 K) (𝓞 L)) ≤
      P.asIdeal.ramificationIdx (𝓞 K) - 1 +
        multiplicity P.asIdeal
          (Ideal.span {((P.asIdeal.ramificationIdx (𝓞 K) : ℕ) : 𝓞 L)}) := by
  have : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  have : P.asIdeal.IsMaximal := P.isMaximal
  obtain ⟨Q, hQm, hQl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 M) P.asIdeal
  have hu : Q.under (𝓞 L) = P.asIdeal := hQl.over.symm
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply P.ne_bot
    rw [← hu]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  let Q' : HeightOneSpectrum (𝓞 M) := ⟨Q, hQm.isPrime, hQ0⟩
  let T : IntermediateField K M :=
    FixedPoints.intermediateField (Ideal.inertia (M ≃ₐ[K] M) Q)
  let E : IntermediateField L M :=
    FixedPoints.intermediateField (Ideal.inertia (M ≃ₐ[L] M) Q)
  have hTE : ∀ x : M, x ∈ T → x ∈ E := by
    intro x hx
    rw [FixedPoints.mem_intermediateField_iff] at hx ⊢
    intro τ
    have hτ : (τ : M ≃ₐ[L] M).restrictScalars K ∈ Ideal.inertia (M ≃ₐ[K] M) Q := by
      rw [Ideal.mem_inertia]
      intro y
      exact Ideal.mem_inertia.mp τ.2 y
    exact hx ⟨_, hτ⟩
  let _ : Algebra T E := RingHom.toAlgebra
    { toFun := fun x => ⟨(x : M), hTE _ x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have : IsScalarTower T E M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower K T E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨hT, hdegT, huniqT⟩ := diffBr_inertia_facts (F := K) (E := T) (M := M) Q'
  obtain ⟨hLE, -, -⟩ := diffBr_inertia_facts (F := L) (E := E) (M := M) Q'
  have huniqE := diffBr_unique_mid (T := T) (E := E) Q' huniqT
  have hdegE := diffBr_ramificationIdx_mid (T := T) (E := E) Q' hdegT
  set w := HeightOneSpectrum.under (𝓞 E) Q' with hw
  have hwT : HeightOneSpectrum.under (𝓞 T) w = HeightOneSpectrum.under (𝓞 T) Q' := by
    apply HeightOneSpectrum.ext
    simp only [hw, HeightOneSpectrum.under_asIdeal, Ideal.under_under]
  have hwL : HeightOneSpectrum.under (𝓞 L) w = P := by
    apply HeightOneSpectrum.ext
    simp only [hw, HeightOneSpectrum.under_asIdeal, Ideal.under_under]
    exact hu
  have h := diffBr_bound_of_inertia_towers (K := K) (L := L) (T := T) (E := E) w hLE
    (by rw [hwT]; exact hT) huniqE hdegE
  rwa [hwL] at h

/-- **The classical bound for the different of number fields.** For number fields `K ⊆ L` and
a prime `P` of `𝓞_L` with ramification index `e_P` over `𝓞_K`:
`v_P(𝔇_{L/K}) ≤ e_P - 1 + v_P(e_P)`, with `v_P(e_P)` the multiplicity of `P` in `e_P·𝓞_L`. The
Galois overfield is the normal closure of `L/K` in an algebraic closure of `L`. -/
theorem diffBr_classical_bound {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (P : HeightOneSpectrum (𝓞 L)) :
    multiplicity P.asIdeal (differentIdeal (𝓞 K) (𝓞 L)) ≤
      P.asIdeal.ramificationIdx (𝓞 K) - 1 +
        multiplicity P.asIdeal
          (Ideal.span {((P.asIdeal.ramificationIdx (𝓞 K) : ℕ) : 𝓞 L)}) := by
  have : NumberField (IntermediateField.normalClosure K L (AlgebraicClosure L)) :=
    NumberField.of_module_finite K _
  have : IsGalois K (IntermediateField.normalClosure K L (AlgebraicClosure L)) :=
    IsGalois.normalClosure_of_isSeparable K L (AlgebraicClosure L)
  exact diffBr_multiplicity_le_of_tower (K := K) (L := L)
    (M := IntermediateField.normalClosure K L (AlgebraicClosure L)) P

/-- `IUT.FermatDifferent.fermatDiff_classicalDifferentBoundStatement` holds. -/
theorem diffBr_statement : fermatDiff_classicalDifferentBoundStatement :=
  fun _ _ _ _ _ _ _ w => diffBr_classical_bound w

/-! ## The two Fermat bounds without assumption -/

/-- **The log-different bound for the field of a lifted point of the Fermat cover, from the
classical bound.** `IUT.FermatDifferent.fermatDiff_logDiffNF_le_of_bound` with its assumption
discharged by `diffBr_classical_bound`: for `L = K(u, v)`, `u^n = x`, `v^n = 1 - x`, `x ∉ {0, 1}`,
`log-diff_L ≤ log-diff_K + log-cond_K(x) + log n + log([L : K]!)`. -/
theorem diffBr_fermat_logDiffNF_le {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] {x : K} (hx0 : x ≠ 0) (hx1 : x ≠ 1) {n : ℕ} (hn : 0 < n)
    {u v : L} (hu : u ^ n = algebraMap K L x) (hv : v ^ n = 1 - algebraMap K L x)
    (hgen : IntermediateField.adjoin K {u, v} = ⊤) :
    logDiffNF L ≤ logDiffNF K + logCondNF K x + Real.log n +
      Real.log (Module.finrank K L).factorial :=
  fermatDiff_logDiffNF_le_of_bound (fun _ _ _ _ _ _ _ w => diffBr_classical_bound w)
    hx0 hx1 hn hu hv hgen

/-- **The existence form.** `IUT.FermatDifferent.fermatDiff_lift_logDiffNF_le_of_bound` with its
assumption discharged: there are `L ⊇ K` with `[L : K] ≤ n²` and `u, v ∈ L`, `u^n = x`,
`v^n = 1 - x`, `L = K(u, v)`, with
`log-diff_L ≤ log-diff_K + log-cond_K(x) + log n + log((n²)!)`. The uniform constant
`log n + log((n²)!)` is larger than the `4 log n` of
`IUT.FermatDifferentGalois.fermatGal_lift_logDiffNF_le`. -/
theorem diffBr_fermat_lift_logDiffNF_le {K : Type} [Field K] [NumberField K] {x : K}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) {n : ℕ} (hn : 0 < n) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L),
      Module.finrank K L ≤ n ^ 2 ∧
        ∃ u v : L, u ^ n = algebraMap K L x ∧ v ^ n = 1 - algebraMap K L x ∧
          IntermediateField.adjoin K {u, v} = ⊤ ∧
          logDiffNF L ≤ logDiffNF K + logCondNF K x + Real.log n +
            Real.log (n ^ 2).factorial :=
  fermatDiff_lift_logDiffNF_le_of_bound (fun _ _ _ _ _ _ _ w => diffBr_classical_bound w)
    hx0 hx1 hn

end IUT.DifferentBridge
