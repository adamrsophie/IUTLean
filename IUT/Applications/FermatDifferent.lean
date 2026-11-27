import IUT.Applications.FermatCover

/-!
# The relative different of the Fermat cover: unramified primes and the log-different bound

Sources: Mochizuki, *Arithmetic Elliptic Curves in General Position* ([GenEll]),
Proposition 1.7 and its proof (pages 9 and 10) and its use in the proof of Theorem 2.1
(page 12); V. Dimitrov, *Effectivity in Mochizuki's work on the abc-conjecture*
(arXiv 1601.03572), the beginning of §5 (page 9). Pages read for this file: [GenEll] pages 9,
10 and 12; arXiv 1601.03572 page 9. Pages checked against rendered images: all of these.

**What this file is.** It continues `IUT.Applications.FermatCover`, which lifts a point
`x ∈ K \ {0, 1}` of `ℙ¹ \ {0, 1, ∞}` along the Fermat cover `π_n : C_n → ℙ¹` to a point
`(u, v)`, `u^n = x`, `v^n = 1 - x`, over a number field `L = K(u, v)` with `[L : K] ≤ n²`. Here the
relative different `𝔇_{L/K}` (Mathlib's `differentIdeal (𝓞 K) (𝓞 L)`) is studied, toward the
inequality that page 12 of [GenEll] takes from Proposition 1.7 (i),
`log-diff_Y ≲ log-diff_X + log-cond_D` on `U_Y(ℚ̄)^{≤ d'}`, in the form it takes for this
cover: `log-diff_L ≤ log-diff_K + log-cond_K(x) + c(n)`. It is not a formalization of
Proposition 1.7 of [GenEll], which concerns arbitrary finite coverings of arithmetic surfaces,
nor of any statement of the papers; the Fermat cover is an instance chosen here (as in
`IUT.Applications.FermatCover`).

**What the pages print that bears on this.**
* [GenEll] page 9, Proposition 1.7 (i): for `φ : Y → Z` with the conditions (a) to (d) (in
  particular `φ_ℚ` étale over `U_Z`, ramification index dividing `e` over `D`),
  `log-cond_E - log-cond_D ≲ log-diff_Y - log-diff_Z ≲ (1 - 1/e)·log-cond_E` on `U_Y(ℚ̄)`.
* [GenEll] page 10, proof of (i): outside a finite set `Σ` of primes the covering is tamely
  ramified, and "the prime-to-`Σ` portion" of the inequality "follows immediately from the
  elementary theory of differents"; over `Σ` it suffices that the different of a finite Galois
  extension `L/K` of `p`-adic fields of bounded degree contains `p^n·𝒪_L` for an `n` depending
  on `p` and the degree only, which the page verifies through Kummer extensions.
* [GenEll] page 12: Proposition 1.7 (i) is applied to conclude
  `log-diff_Y ≲ log-diff_X + log-cond_D` on `U_Y(ℚ̄)^{≤ d'}`.
* arXiv 1601.03572 page 9: the ramification divisor of `π_n` is `(n - 1)·π_n^{-1}{0, 1, ∞}`, and
  the maps `f_i` there are unramified outside `f_i^{-1}{0, 1, ∞}`.

**What this file proves.** `K ⊆ L` are number fields.
1. The Kummer criterion, element form (`fermatDiff_not_dvd_differentIdeal`): if `L = K(θ)`,
   `θ^n = c` with `c ∈ 𝓞_K`, and the prime `P` of `𝓞_L` lies over a prime `𝔭` of `𝓞_K` with
   `n ∉ 𝔭` and `c ∉ 𝔭`, then `P ∤ 𝔇_{L/K}`, so `P` is unramified
   (`fermatDiff_isUnramifiedAt_of_not_dvd`, through Mathlib's `not_dvd_differentIdeal_iff`). The
   proof: the minimal polynomial `g` of `θ` over `𝓞_K` divides `X^n - c`, so `g'(θ)` divides
   `n·θ^(n-1)`; `g'(θ)` lies in the different (Mathlib's `aeval_derivative_mem_differentIdeal`).
   For `a ∈ K` a unit at `𝔭` (valuation `1`) and `L = K(a^{1/n})`:
   `fermatDiff_not_dvd_differentIdeal_of_valuation`.
2. Transfer to the field of the lifted point (`fermatDiff_not_dvd_differentIdeal_of_reduces`): if
   `L = K(u, v)` with `u^n = x`, `v^n = 1 - x`, then every prime of `𝓞_L` over a prime `𝔭` of `𝓞_K`
   with `n ∉ 𝔭` at which `x` reduces away from `{0, 1, ∞}` does not divide `𝔇_{L/K}`. The proof
   goes through the tower `K ⊆ K(u) ⊆ L` (`fermatDiff_not_dvd_differentIdeal_tower`, Mathlib's
   transitivity `differentIdeal_eq_differentIdeal_mul_differentIdeal`), with the integral
   generators `b·u`, `b·v` where `x = a/b`, `a, b, a - b ∉ 𝔭`. With
   `fermatDiff_point_exists` (such an `L` with `[L : K] ≤ n²` and `L = K(u, v)` exists) this gives
   `fermatDiff_lift_unramified`. Equivalently (`fermatDiff_dvd_differentIdeal_imp`): a prime of
   `𝓞_L` dividing `𝔇_{L/K}` lies over a prime containing `n` or over a prime where `x` meets
   `{0, 1, ∞}`. This is the arithmetic counterpart of "unramified outside `π_n^{-1}{0, 1, ∞}`"
   (arXiv 1601.03572 page 9) and the unramified part of "the prime-to-`Σ` portion" of [GenEll]
   page 10, with `Σ` taken here (a choice, not printed) to be the primes dividing `n`; the other
   part of that portion, the tame equality at the primes where `x` meets the boundary, is not
   proved (the classical bound used in item 3 gives an upper bound there, not the value).
3. The bound, from one classical statement. `fermatDiff_logDiffNF_le_of_bound`:
   assuming `fermatDiff_classicalDifferentBoundStatement` (for all number fields `K ⊆ L` in
   `Type` and every prime `P` of `𝓞_L`, `v_P(𝔇_{L/K}) ≤ e_P - 1 + v_P(e_P)`, the classical upper
   bound for the different), for
   `L = K(u, v)` as above and `x ∉ {0, 1}`,
   `log-diff_L ≤ log-diff_K + log-cond_K(x) + log n + log([L : K]!)`, with `logDiffNF`, `logCondNF`
   of `IUT.VojtaNumberField`. Since `[L : K] ≤ n²`, this is the bound with
   `c(n) = log n + log((n²)!)` (`fermatDiff_lift_logDiffNF_le_of_bound`). The proof: `𝔇_{L/K}`
   divides `n·[L : K]!·∏_{𝔭 ∈ S} 𝔭` extended to `𝓞_L`, `S` the primes where `x` meets the
   boundary (item 2 for the primes outside `S` and not containing `n`, the classical bound with
   `e_P ∣ [L : K]!` for the others); then the norm, and Mathlib's
   `|d_L| = N(𝔇_{L/K})·|d_K|^{[L : K]}` through `IUT.PaperIV.DegreePullback.degPb_logDiffNF_tower`.
   The constant is not the paper's (none is printed); it is explicit and depends on `n` only.

**Not proved.**
* The classical bound `v_P(𝔇_{L/K}) ≤ e_P - 1 + v_P(e_P)` for number fields
  (`fermatDiff_classicalDifferentBoundStatement`, a definition, the hypothesis of the theorems of
  item 3), here; it is proved without completions in `IUT.DifferentBridge`
  (`diffBr_classical_bound`, and `diffBr_statement` for the definition), so the bound of item 3
  holds without hypothesis (`IUT.DifferentBridge.diffBr_fermat_logDiffNF_le`). The tame half,
  `v_P(𝔇) = e_P - 1` when the residue
  characteristic does not divide `e_P`, follows the pattern of
  `IUT.PaperIV.LocalFields.differentExponent_eq_of_not_dvd_ramificationIdx_padic` (trace of
  `B ⧸ P^e` equal to `e` times the residue trace) but with a non-principal `P` and the
  Chinese remainder decomposition of `B ⧸ 𝔭B`; it is not formalized here either.
* Proposition 1.7 (i) of [GenEll] itself (finite coverings of arithmetic surfaces, and the
  lower bound `log-cond_E - log-cond_D ≲ log-diff_Y - log-diff_Z`), and any statement of the
  papers.
-/

open NumberField IsDedekindDomain
open IUT.VojtaNumberField IUT.PaperIV.DegreePullback

namespace IUT.FermatDifferent

/-! ## The Kummer criterion -/

/-- **The Kummer criterion for the different, element form.** Let `L = K(θ)` with `θ^n = c`,
`c ∈ 𝓞_K`, and let `P` be a prime of `𝓞_L` such that neither `n` nor `c` lies in the prime
`P ∩ 𝓞_K`. Then `P` does not divide the relative different `𝔇_{L/K}`. -/
theorem fermatDiff_not_dvd_differentIdeal {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] {n : ℕ} (θ₀ : L) (c : 𝓞 K)
    (hθ₀ : θ₀ ^ n = algebraMap K L c) (hgen₀ : IntermediateField.adjoin K {θ₀} = ⊤)
    (P : Ideal (𝓞 L)) [P.IsPrime] (hn : (n : 𝓞 K) ∉ P.comap (algebraMap (𝓞 K) (𝓞 L)))
    (hc : c ∉ P.comap (algebraMap (𝓞 K) (𝓞 L))) :
    ¬ P ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (by simp)
  have hint₀ : IsIntegral ℤ θ₀ := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hn0) ?_
    rw [hθ₀]
    exact (RingOfIntegers.isIntegral_coe c).map (IsScalarTower.toAlgHom ℤ K L)
  set θ : 𝓞 L := ⟨θ₀, hint₀⟩ with hθdef
  have hθ : θ ^ n = algebraMap (𝓞 K) (𝓞 L) c := by
    apply RingOfIntegers.ext
    rw [show ((θ ^ n : 𝓞 L) : L) = θ₀ ^ n from rfl]
    exact hθ₀
  have hgen : Algebra.adjoin K {algebraMap (𝓞 L) L θ} = ⊤ := by
    rw [← IntermediateField.adjoin_eq_top_iff]
    exact hgen₀
  have hint : IsIntegral (𝓞 K) θ := Algebra.IsIntegral.isIntegral θ
  have hroot : Polynomial.aeval θ
      (Polynomial.X ^ n - Polynomial.C c : Polynomial (𝓞 K)) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hθ, sub_self]
  obtain ⟨h, hh⟩ := minpoly.isIntegrallyClosed_dvd hint hroot
  have hder : Polynomial.aeval θ
      (Polynomial.derivative (Polynomial.X ^ n - Polynomial.C c : Polynomial (𝓞 K))) =
      Polynomial.aeval θ (Polynomial.derivative (minpoly (𝓞 K) θ)) * Polynomial.aeval θ h := by
    rw [hh, Polynomial.derivative_mul, map_add, map_mul, map_mul, minpoly.aeval, zero_mul,
      add_zero]
  have hmem := aeval_derivative_mem_differentIdeal (𝓞 K) K L θ hgen
  have hmem' : (n : 𝓞 L) * θ ^ (n - 1) ∈ differentIdeal (𝓞 K) (𝓞 L) := by
    have := Ideal.mul_mem_right (Polynomial.aeval θ h) _ hmem
    rw [← hder] at this
    simpa only [Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_C, sub_zero, map_mul, map_natCast, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C] using this
  intro hdvd
  have hP := Ideal.le_of_dvd hdvd hmem'
  rcases Ideal.IsPrime.mem_or_mem ‹_› hP with h1 | h1
  · apply hn
    rw [Ideal.mem_comap, map_natCast]
    exact h1
  · have hθP : θ ∈ P := Ideal.IsPrime.mem_of_pow_mem ‹_› _ h1
    apply hc
    rw [Ideal.mem_comap, ← hθ]
    exact Ideal.pow_mem_of_mem _ hθP _ (Nat.pos_of_ne_zero hn0)

/-- A prime of `𝓞_L` that does not divide `𝔇_{L/K}` is unramified over `𝓞_K` (Mathlib's
`not_dvd_differentIdeal_iff`). -/
theorem fermatDiff_isUnramifiedAt_of_not_dvd {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] (P : Ideal (𝓞 L)) [P.IsPrime]
    (h : ¬ P ∣ differentIdeal (𝓞 K) (𝓞 L)) : Algebra.IsUnramifiedAt (𝓞 K) P := by
  let _ : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) := FractionRing.liftAlgebra _ _
  exact not_dvd_differentIdeal_iff.mp h

/-- **The different in a tower.** For number fields `K ⊆ F ⊆ L` and a prime `P` of `𝓞_L`: if
`P ∩ 𝓞_F` does not divide `𝔇_{F/K}` and `P` does not divide `𝔇_{L/F}`, then `P` does not divide
`𝔇_{L/K} = 𝔇_{L/F}·𝔇_{F/K}𝓞_L`. -/
theorem fermatDiff_not_dvd_differentIdeal_tower {K F L : Type*} [Field K] [NumberField K]
    [Field F] [NumberField F] [Field L] [NumberField L] [Algebra K F] [Algebra F L]
    [Algebra K L] [IsScalarTower K F L] (P : Ideal (𝓞 L)) [P.IsPrime]
    (h1 : ¬ P.comap (algebraMap (𝓞 F) (𝓞 L)) ∣ differentIdeal (𝓞 K) (𝓞 F))
    (h2 : ¬ P ∣ differentIdeal (𝓞 F) (𝓞 L)) :
    ¬ P ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  let _ : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) := FractionRing.liftAlgebra _ _
  intro hdvd
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    rw [← Ideal.zero_eq_bot, zero_dvd_iff] at hdvd
    exact differentIdeal_ne_bot hdvd
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal (𝓞 K) (𝓞 F) (𝓞 L)] at hdvd
  rcases (Ideal.prime_of_isPrime hPbot ‹_›).dvd_or_dvd hdvd with h | h
  · exact h2 h
  · apply h1
    rw [Ideal.dvd_iff_le] at h ⊢
    exact Ideal.map_le_iff_le_comap.mp h

/-- `K(c·θ) = K(θ)` for `c ∈ K` nonzero. -/
theorem fermatDiff_adjoin_smul_eq {K L : Type*} [Field K] [Field L] [Algebra K L] {c : K}
    (hc : c ≠ 0) (θ : L) :
    IntermediateField.adjoin K {algebraMap K L c * θ} = IntermediateField.adjoin K {θ} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact mul_mem (IntermediateField.algebraMap_mem _ c)
      (IntermediateField.mem_adjoin_simple_self K θ)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have hmem := mul_mem
      (IntermediateField.algebraMap_mem (IntermediateField.adjoin K {algebraMap K L c * θ}) c⁻¹)
      (IntermediateField.mem_adjoin_simple_self K (algebraMap K L c * θ))
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul] at hmem

/-- **The Kummer criterion for `X^n - a`** (item 1 in the form of a unit `a`): let `L = K(u)`
with `u^n = a ∈ K`, and let `w` be a prime of `𝓞_L` over the prime `𝔭` of `𝓞_K`. If `n ∉ 𝔭` and
`a` is a unit at `𝔭` (its `𝔭`-adic valuation is `1`), then `w` does not divide `𝔇_{L/K}`, so `w`
is unramified over `𝓞_K`. Writing `a = c/d` with `c, d ∈ 𝓞_K \ 𝔭`, the integral generator `d·u`
has `(d·u)^n = d^(n-1)·c ∉ 𝔭`. -/
theorem fermatDiff_not_dvd_differentIdeal_of_valuation {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] {a : K} {n : ℕ} {u : L}
    (hu : u ^ n = algebraMap K L a) (hgen : IntermediateField.adjoin K {u} = ⊤)
    (w : HeightOneSpectrum (𝓞 L))
    (hn : (n : 𝓞 K) ∉ (HeightOneSpectrum.under (𝓞 K) w).asIdeal)
    (ha : (HeightOneSpectrum.under (𝓞 K) w).valuation K a = 1) :
    ¬ w.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  set vv := HeightOneSpectrum.under (𝓞 K) w
  obtain ⟨c, d, hcd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer vv a ha.le
  have hd : (d : 𝓞 K) ∉ vv.asIdeal := d.prop
  have vd := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K) vv).mpr hd
  have hc : c ∉ vv.asIdeal := by
    rw [← HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K) vv, ← hcd, map_mul, ha, vd,
      one_mul]
  have hpp : vv.asIdeal.IsPrime := vv.isPrime
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (by simp)
  have hd0 : algebraMap (𝓞 K) K (d : 𝓞 K) ≠ 0 := by
    intro h
    apply hd
    rw [show (d : 𝓞 K) = 0 from RingOfIntegers.ext h]
    exact vv.asIdeal.zero_mem
  have hdc : (d : 𝓞 K) ^ (n - 1) * c ∉ vv.asIdeal := hpp.mul_mem_iff_mem_or_mem.not.mpr
    (not_or.mpr ⟨fun h => hd (hpp.mem_of_pow_mem _ h), hc⟩)
  refine fermatDiff_not_dvd_differentIdeal (algebraMap K L (algebraMap (𝓞 K) K (d : 𝓞 K)) * u)
    ((d : 𝓞 K) ^ (n - 1) * c) ?_ ?_ w.asIdeal hn hdc
  · rw [mul_pow, hu, ← map_pow, ← map_mul]
    congr 1
    change (algebraMap (𝓞 K) K (d : 𝓞 K)) ^ n * a =
      algebraMap (𝓞 K) K ((d : 𝓞 K) ^ (n - 1) * c)
    rw [map_mul, map_pow, ← hcd]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring
  · rw [fermatDiff_adjoin_smul_eq hd0, hgen]

/-! ## The field of the lifted point -/

/-- **The field of a point of the Fermat curve is unramified at the good primes.** Let
`L = K(u, v)` with `u^n = x` and `v^n = 1 - x` (`x ∈ K`), and let `w` be a prime of `𝓞_L` over
the prime `𝔭` of `𝓞_K`. If `n ∉ 𝔭` and `x` reduces modulo `𝔭` to a point of
`ℙ¹ \ {0, 1, ∞}` (`ReducesAwayFromBoundary`), then `w` does not divide `𝔇_{L/K}`. -/
theorem fermatDiff_not_dvd_differentIdeal_of_reduces {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] {x : K} {n : ℕ} {u v : L}
    (hu : u ^ n = algebraMap K L x) (hv : v ^ n = 1 - algebraMap K L x)
    (hgen : IntermediateField.adjoin K {u, v} = ⊤) (w : HeightOneSpectrum (𝓞 L))
    (hn : (n : 𝓞 K) ∉ (HeightOneSpectrum.under (𝓞 K) w).asIdeal)
    (hx : ReducesAwayFromBoundary K (HeightOneSpectrum.under (𝓞 K) w) x) :
    ¬ w.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  obtain ⟨a, b, ha, hb, hab, hxb⟩ := hx
  rw [HeightOneSpectrum.under_asIdeal] at ha hb hab hn
  set p := w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) with hp
  have hpp : p.IsPrime := Ideal.comap_isPrime _ _
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (by simp)
  have hb0 : (b : K) ≠ 0 := by
    intro h
    apply hb
    rw [show b = 0 from RingOfIntegers.ext h]
    exact p.zero_mem
  have : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  set F : IntermediateField K L := IntermediateField.adjoin K {u} with hF
  have : NumberField F := NumberField.of_module_finite K F
  set g : F := IntermediateField.AdjoinSimple.gen K u with hg
  have hgF : IntermediateField.adjoin K {g} = ⊤ := by
    apply IntermediateField.lift_injective F
    rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]
    rfl
  have h1 : ¬ w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L)) ∣ differentIdeal (𝓞 K) (𝓞 F) := by
    have hcomap :
        (w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L))).comap (algebraMap (𝓞 K) (𝓞 F)) = p := by
      rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    have hc1 : b ^ (n - 1) * a ∉ p := hpp.mul_mem_iff_mem_or_mem.not.mpr
      (not_or.mpr ⟨fun h => hb (hpp.mem_of_pow_mem _ h), ha⟩)
    have hn' : (n : 𝓞 K) ∉ p := hn
    refine fermatDiff_not_dvd_differentIdeal (algebraMap K F b * g) (b ^ (n - 1) * a) ?_ ?_ _
      (by rw [hcomap]; exact hn') (by rw [hcomap]; exact hc1)
    · apply (algebraMap F L).injective
      rw [map_pow, map_mul, ← IsScalarTower.algebraMap_apply K F L, hg,
        IntermediateField.AdjoinSimple.algebraMap_gen, ← IsScalarTower.algebraMap_apply K F L,
        mul_pow, hu, ← map_pow, ← map_mul]
      congr 1
      change (algebraMap (𝓞 K) K b) ^ n * x = algebraMap (𝓞 K) K (b ^ (n - 1) * a)
      rw [map_mul, map_pow, ← hxb]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      ring
    · rw [fermatDiff_adjoin_smul_eq hb0, hgF]
  have h2 : ¬ w.asIdeal ∣ differentIdeal (𝓞 F) (𝓞 L) := by
    have hvF : IntermediateField.adjoin F {v} = ⊤ := by
      rw [← IntermediateField.restrictScalars_eq_top_iff (K := K), hF,
        IntermediateField.adjoin_adjoin_left, ← Set.insert_eq, hgen]
    have hbF : algebraMap K F b ≠ 0 := (map_ne_zero _).mpr hb0
    have hd : b ^ (n - 1) * (b - a) ∉ p := hpp.mul_mem_iff_mem_or_mem.not.mpr
      (not_or.mpr ⟨fun h => hb (hpp.mem_of_pow_mem _ h),
        fun h => hab (by rw [← neg_sub]; exact p.neg_mem h)⟩)
    refine fermatDiff_not_dvd_differentIdeal (K := F) (n := n) (algebraMap K L b * v)
      (algebraMap (𝓞 K) (𝓞 F) (b ^ (n - 1) * (b - a))) ?_ ?_ w.asIdeal ?_ ?_
    · rw [show ((algebraMap (𝓞 K) (𝓞 F) (b ^ (n - 1) * (b - a)) : 𝓞 F) : F) =
          algebraMap K F (b ^ (n - 1) * (b - a) : 𝓞 K) from rfl,
        ← IsScalarTower.algebraMap_apply K F L, mul_pow, hv, ← map_pow,
        ← map_one (algebraMap K L), ← map_sub, ← map_mul]
      congr 1
      change (algebraMap (𝓞 K) K b) ^ n * (1 - x) =
        algebraMap (𝓞 K) K (b ^ (n - 1) * (b - a))
      rw [map_mul, map_pow, map_sub, ← hxb]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      ring
    · rw [IsScalarTower.algebraMap_apply K F L, fermatDiff_adjoin_smul_eq hbF, hvF]
    · rw [Ideal.mem_comap, map_natCast]
      rw [Ideal.mem_comap, map_natCast] at hn
      exact hn
    · intro h
      apply hd
      rw [hp, Ideal.mem_comap, IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 F) (𝓞 L)]
      exact h
  exact fermatDiff_not_dvd_differentIdeal_tower w.asIdeal h1 h2

/-- **The support of the different of the field of the lifted point.** For `L = K(u, v)` with
`u^n = x`, `v^n = 1 - x`: a prime `w` of `𝓞_L` dividing `𝔇_{L/K}` lies over a prime of `𝓞_K`
that contains `n` or at which `x` meets `{0, 1, ∞}`. -/
theorem fermatDiff_dvd_differentIdeal_imp {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] {x : K} {n : ℕ} {u v : L}
    (hu : u ^ n = algebraMap K L x) (hv : v ^ n = 1 - algebraMap K L x)
    (hgen : IntermediateField.adjoin K {u, v} = ⊤) (w : HeightOneSpectrum (𝓞 L))
    (hw : w.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 L)) :
    (n : 𝓞 K) ∈ (HeightOneSpectrum.under (𝓞 K) w).asIdeal ∨
      MeetsBoundaryAt K (HeightOneSpectrum.under (𝓞 K) w) x := by
  by_contra hc
  rw [not_or] at hc
  exact fermatDiff_not_dvd_differentIdeal_of_reduces hu hv hgen w hc.1 (not_not.mp hc.2) hw

universe uK

/-- **The lifted point, with the field it generates** (a refinement of
`IUT.FermatCover.fermatCover_point_exists` that also records `L = K(u, v)`): for a number field
`K`, `x ∈ K` and `n ≥ 1` there are a number field `L ⊇ K` with `[L : K] ≤ n²` and `u, v ∈ L` with
`u^n = x`, `v^n = 1 - x` and `L = K(u, v)`. -/
theorem fermatDiff_point_exists {K : Type uK} [Field K] [NumberField K] (x : K) {n : ℕ}
    (hn : 0 < n) :
    ∃ (L : Type uK) (_ : Field L) (_ : NumberField L) (_ : Algebra K L),
      Module.finrank K L ≤ n ^ 2 ∧
        ∃ u v : L, u ^ n = algebraMap K L x ∧ v ^ n = 1 - algebraMap K L x ∧
          IntermediateField.adjoin K {u, v} = ⊤ := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) x) hn
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) (1 - x)) hn
  set M := IntermediateField.adjoin K {u, v} with hM
  have hMsup : M = IntermediateField.adjoin K {u} ⊔ IntermediateField.adjoin K {v} := by
    rw [hM, Set.insert_eq, IntermediateField.adjoin_union]
  have := IntermediateField.finiteDimensional_adjoin_pair
    (IUT.FermatCover.fermatCover_isIntegral_root hn hu)
    (IUT.FermatCover.fermatCover_isIntegral_root hn hv)
  have : NumberField M := NumberField.of_module_finite K M
  have huM : u ∈ M := IntermediateField.subset_adjoin K _ (Set.mem_insert u {v})
  have hvM : v ∈ M := IntermediateField.subset_adjoin K _ (Set.mem_insert_of_mem u rfl)
  refine ⟨M, inferInstance, inferInstance, inferInstance, ?_, ⟨u, huM⟩, ⟨v, hvM⟩, ?_, ?_, ?_⟩
  · rw [hMsup]
    exact IUT.FermatCover.fermatCover_finrank_adjoin_le hn hu hv
  · apply Subtype.ext
    simpa using hu
  · apply Subtype.ext
    simpa using hv
  · apply IntermediateField.lift_injective M
    rw [IntermediateField.lift_adjoin, IntermediateField.lift_top, Set.image_insert_eq,
      Set.image_singleton]

/-- **The lift is unramified at the good primes** (items 1 and 2 together): for a number field
`K`, `x ∈ K` and `n ≥ 1` there are a number field `L ⊇ K` with `[L : K] ≤ n²` and `u, v ∈ L`,
`u^n = x`, `v^n = 1 - x`, `L = K(u, v)`, such that every prime `w` of `𝓞_L` over a prime `𝔭` of
`𝓞_K` with `n ∉ 𝔭`, at which `x` reduces away from `{0, 1, ∞}`, is unramified over `𝓞_K`. -/
theorem fermatDiff_lift_unramified {K : Type uK} [Field K] [NumberField K] (x : K) {n : ℕ}
    (hn : 0 < n) :
    ∃ (L : Type uK) (_ : Field L) (_ : NumberField L) (_ : Algebra K L),
      Module.finrank K L ≤ n ^ 2 ∧
        ∃ u v : L, u ^ n = algebraMap K L x ∧ v ^ n = 1 - algebraMap K L x ∧
          IntermediateField.adjoin K {u, v} = ⊤ ∧
          ∀ w : HeightOneSpectrum (𝓞 L),
            (n : 𝓞 K) ∉ (HeightOneSpectrum.under (𝓞 K) w).asIdeal →
            ReducesAwayFromBoundary K (HeightOneSpectrum.under (𝓞 K) w) x →
            Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := by
  obtain ⟨L, _, _, _, hdeg, u, v, hu, hv, hgen⟩ := fermatDiff_point_exists x hn
  exact ⟨L, inferInstance, inferInstance, inferInstance, hdeg, u, v, hu, hv, hgen,
    fun w hnw hxw => fermatDiff_isUnramifiedAt_of_not_dvd w.asIdeal
      (fermatDiff_not_dvd_differentIdeal_of_reduces hu hv hgen w hnw hxw)⟩

/-! ## The log-different bound, from the classical bound for the different -/

/-- **The classical upper bound for the different, for number fields, as a proposition** (proved
in `IUT.DifferentBridge.diffBr_statement`). For number fields `K ⊆ L` and every prime `P` of
`𝓞_L`, with ramification index
`e_P` over `𝓞_K`: `v_P(𝔇_{L/K}) ≤ e_P - 1 + v_P(e_P)`, where `v_P` is the multiplicity of `P`
(in `𝔇_{L/K}`, and in the principal ideal `(e_P)` of `𝓞_L`). This is a classical theorem of
algebraic number theory (the local bound `v_P(𝔇_{L_P/K_𝔭}) ≤ e - 1 + v_P(e)` together with the
equality of the global and local exponents of the different); it is not a statement of
[GenEll] or of IUT. The local bound over `ℚ_p` is
`IUT.PaperIV.LocalFields.diffBound_exponent_le`; this global form is proved in
`IUT.DifferentBridge.diffBr_statement`. The fields range over `Type`. -/
def fermatDiff_classicalDifferentBoundStatement : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)),
    multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 L)) ≤
      w.asIdeal.ramificationIdx (𝓞 K) - 1 +
        multiplicity w.asIdeal (Ideal.span {((w.asIdeal.ramificationIdx (𝓞 K) : ℕ) : 𝓞 L)})

/-- Divisibility of nonzero ideals of `𝓞_L` from the multiplicities at all primes. -/
theorem fermatDiff_dvd_of_multiplicity_le {L : Type*} [Field L] [NumberField L]
    {I J : Ideal (𝓞 L)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (h : ∀ w : HeightOneSpectrum (𝓞 L), multiplicity w.asIdeal I ≤ multiplicity w.asIdeal J) :
    I ∣ J := by
  rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hI hJ,
    Multiset.le_iff_count]
  intro P
  by_cases hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I
  · have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor P hP
    have hprime : Prime P := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
    have hPbot : P ≠ ⊥ := hprime.ne_zero
    have hPp : P.IsPrime := (Ideal.prime_iff_isPrime hPbot).mp hprime
    have h1 := UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors hirr (b := I)
    have h2 := UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors hirr (b := J)
    rw [normalize_eq] at h1 h2
    rw [← h1, ← h2]
    exact h { asIdeal := P, isPrime := hPp, ne_bot := hPbot }
  · rw [Multiset.count_eq_zero.mpr hP]
    exact Nat.zero_le _

/-- The ramification index of a prime of `𝓞_L` over `𝓞_K` is at most `[L : K]`
(`∑ e(w|v) f(w|v) = [L : K]`). -/
theorem fermatDiff_ramificationIdx_le_finrank {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal.ramificationIdx (𝓞 K) ≤ Module.finrank K L := by
  classical
  set v := HeightOneSpectrum.under (𝓞 K) w
  have : v.asIdeal.IsMaximal := v.isMaximal
  have hlies : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  let q : v.asIdeal.primesOver (𝓞 L) := ⟨w.asIdeal, w.isPrime, hlies⟩
  have hsum := Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 L)
  rw [degPb_finrank_int (K := K) L] at hsum
  have hle : q.1.ramificationIdx (𝓞 K) * q.1.inertiaDeg (𝓞 K) ≤ Module.finrank K L := by
    rw [← hsum]
    exact Finset.single_le_sum
      (f := fun q : v.asIdeal.primesOver (𝓞 L) => q.1.ramificationIdx (𝓞 K) * q.1.inertiaDeg (𝓞 K))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
  have hf : 0 < q.1.inertiaDeg (𝓞 K) := Ideal.inertiaDeg_pos q.1 (𝓞 K)
  calc w.asIdeal.ramificationIdx (𝓞 K) = q.1.ramificationIdx (𝓞 K) := rfl
    _ ≤ q.1.ramificationIdx (𝓞 K) * q.1.inertiaDeg (𝓞 K) := Nat.le_mul_of_pos_right _ hf
    _ ≤ Module.finrank K L := hle

/-- `w ^ e(w|v)` divides the extension of `v` to `𝓞_L`, for `v` the prime below `w`. -/
theorem fermatDiff_pow_ramificationIdx_dvd_map {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal ^ w.asIdeal.ramificationIdx (𝓞 K) ∣
      (HeightOneSpectrum.under (𝓞 K) w).asIdeal.map (algebraMap (𝓞 K) (𝓞 L)) := by
  set v := HeightOneSpectrum.under (𝓞 K) w
  have : v.asIdeal.IsMaximal := v.isMaximal
  have : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have hpS : v.asIdeal.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot v.ne_bot
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity v.asIdeal w.asIdeal hpS]
  exact pow_multiplicity_dvd _ _

/-- The log-conductor as a finite sum: for `x ∉ {0, 1}`,
`log-cond_K(x) = (1/[K : ℚ]) ∑_{𝔭 ∈ S} log N𝔭`, `S` the finite set of primes at which `x` meets
`{0, 1, ∞}`. -/
theorem fermatDiff_logCondNF_eq_sum {K : Type*} [Field K] [NumberField K] {x : K}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    logCondNF K x = (∑ v ∈ (degPb_meetsBoundaryAt_finite hx0 hx1).toFinset,
      Real.log (Ideal.absNorm v.asIdeal)) / Module.finrank ℚ K := by
  classical
  set S := (degPb_meetsBoundaryAt_finite hx0 hx1).toFinset
  unfold logCondNF
  congr 1
  rw [finsum_eq_sum_of_support_subset _ (s := S) fun v hv => ?_]
  · refine Finset.sum_congr rfl fun v hv => ?_
    have hm : MeetsBoundaryAt K v x := (Set.Finite.mem_toFinset _).mp hv
    rw [ite_eq_left hm, degPb_card_quot]
  · rw [Function.mem_support] at hv
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    by_contra hm
    exact hv (ite_eq_right hm)

/-- **The log-different bound for the field of the lifted point, from the classical bound for
the different.** Assume `fermatDiff_classicalDifferentBoundStatement`. Let `K ⊆ L` be number
fields (in `Type`), `x ∈ K \ {0, 1}`, `n ≥ 1`, and `L = K(u, v)` with `u^n = x`, `v^n = 1 - x`.
Then `log-diff_L ≤ log-diff_K + log-cond_K(x) + log n + log([L : K]!)`. -/
theorem fermatDiff_logDiffNF_le_of_bound (hB : fermatDiff_classicalDifferentBoundStatement)
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {x : K} (hx0 : x ≠ 0) (hx1 : x ≠ 1) {n : ℕ} (hn : 0 < n) {u v : L}
    (hu : u ^ n = algebraMap K L x) (hv : v ^ n = 1 - algebraMap K L x)
    (hgen : IntermediateField.adjoin K {u, v} = ⊤) :
    logDiffNF L ≤ logDiffNF K + logCondNF K x + Real.log n +
      Real.log (Module.finrank K L).factorial := by
  classical
  set m := Module.finrank K L with hm
  set N := m.factorial with hN
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
    exact mul_ne_zero (mul_ne_zero (hspan0 n hn.ne') (hspan0 N (Nat.factorial_ne_zero m)))
      hRmap0
  -- the different divides `J`
  have hdvd : D ∣ J := by
    refine fermatDiff_dvd_of_multiplicity_le hD0 hJ0 fun w => ?_
    by_cases hw : w.asIdeal ∣ D
    · set vv := HeightOneSpectrum.under (𝓞 K) w
      set e := w.asIdeal.ramificationIdx (𝓞 K)
      set k := multiplicity w.asIdeal (Ideal.span {((e : ℕ) : 𝓞 L)})
      have hb : multiplicity w.asIdeal D ≤ e - 1 + k := hB K L w
      have he0 : 0 < e := by
        have : w.asIdeal.LiesOver vv.asIdeal := ⟨rfl⟩
        exact Ideal.ramificationIdx_pos_of_isDedekindDomain' w.asIdeal vv.ne_bot
      have hele : e ≤ m := fermatDiff_ramificationIdx_le_finrank w
      have hwe : w.asIdeal ^ e ∣ vv.asIdeal.map (algebraMap (𝓞 K) (𝓞 L)) :=
        fermatDiff_pow_ramificationIdx_dvd_map w
      have hwk : w.asIdeal ^ k ∣ Ideal.span {((N : ℕ) : 𝓞 L)} := by
        refine (pow_multiplicity_dvd _ _).trans ?_
        rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_span_singleton]
        exact Nat.cast_dvd_cast (Nat.dvd_factorial he0 hele)
      have hcases := fermatDiff_dvd_differentIdeal_imp hu hv hgen w hw
      have hpow : w.asIdeal ^ (e + k) ∣ J := by
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
      omega
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
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.factorial_pos m
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

/-- **The bound of [GenEll] page 12 for the Fermat cover, with `c(n) = log n + log((n²)!)`,
from the classical bound for the different.** Assume
`fermatDiff_classicalDifferentBoundStatement`. For a number field `K` (in `Type`), `x ∈ K \ {0, 1}`
and `n ≥ 1` there are a number field `L ⊇ K` with `[L : K] ≤ n²` and `u, v ∈ L` with `u^n = x`,
`v^n = 1 - x`, `L = K(u, v)`, such that
`log-diff_L ≤ log-diff_K + log-cond_K(x) + log n + log((n²)!)`. -/
theorem fermatDiff_lift_logDiffNF_le_of_bound (hB : fermatDiff_classicalDifferentBoundStatement)
    {K : Type} [Field K] [NumberField K] {x : K} (hx0 : x ≠ 0) (hx1 : x ≠ 1) {n : ℕ}
    (hn : 0 < n) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L),
      Module.finrank K L ≤ n ^ 2 ∧
        ∃ u v : L, u ^ n = algebraMap K L x ∧ v ^ n = 1 - algebraMap K L x ∧
          IntermediateField.adjoin K {u, v} = ⊤ ∧
          logDiffNF L ≤ logDiffNF K + logCondNF K x + Real.log n +
            Real.log (n ^ 2).factorial := by
  obtain ⟨L, _, _, _, hdeg, u, v, hu, hv, hgen⟩ := fermatDiff_point_exists x hn
  refine ⟨L, inferInstance, inferInstance, inferInstance, hdeg, u, v, hu, hv, hgen, ?_⟩
  have h := fermatDiff_logDiffNF_le_of_bound hB hx0 hx1 hn hu hv hgen
  have hfac : Real.log (Module.finrank K L).factorial ≤ Real.log (n ^ 2).factorial :=
    Real.log_le_log (by exact_mod_cast Nat.factorial_pos _)
      (by exact_mod_cast Nat.factorial_le hdeg)
  linarith

end IUT.FermatDifferent
