import IUT.PaperIV.DegreePullback

/-!
# The height, log-different and log-conductor under extension of the number field

Sources: Mochizuki, *Arithmetic Elliptic Curves in General Position* ([GenEll]), §1: page 4
(the normalized degree, its invariance under finite extension for arithmetic line bundles, and
the definition of `ht_𝓜(x)` on `X(ℚ̄)`), Definition 1.2 (page 5) and Definition 1.5 (i), (iii),
(iv) (page 8: minimal field of definition, log-different, log-conductor); Mochizuki,
*Inter-universal Teichmüller Theory IV*, Definition 1.9 (i) (page 22). Pages read for this file:
[GenEll] pages 3, 4, 5 and 8; IUT IV page 22. Pages checked against rendered images: all of
these.

**What the pages print.** [GenEll] page 4: with `deg_F = (1/[F : ℚ]) deg_F` (normalized), "for
any finite extension `K` of `F`, it follows that `deg_K(𝓛|_{Spec 𝒪_K}) = deg_F(𝓛)`" for arithmetic
line bundles on `Spec 𝒪_F`; "In particular, ... for any `x ∈ X(ℚ̄)` ... it makes sense to define
`ht_𝓜(x) = deg_F(x_F^* 𝓜)`, where `x_F : Spec(𝒪_F) → X` is any morphism that gives rise to
`x`." So the height does not depend on the number field `F` through which the point is read.
Definition 1.2 (i) (page 5) names this function `ht_𝓜 : X(ℚ̄) → ℝ`. Definition 1.5 (iii), (iv)
(page 8), by contrast, define `log-diff_X(x)` and `log-cond_D(x)` only for `x ∈ X(F)` with `F` "a
minimal field of definition of `x`" (Definition 1.5 (i)): the pages do not assert that these
two functions are unchanged when `x` is read in a larger field. For the log-different this fails
(item 2 below); for the log-conductor item 3 below gives the exact change. IUT IV page 22
(Definition 1.9 (i)) prints the invariance `deg(𝔞|_K) = deg(𝔞)` of the normalized degree of
arithmetic divisors, proved in `IUT.PaperIV.DegreePullback` as `degPb_normalizedDeg_pullback`.

**What this file proves**, for the functions `heightNF`, `logDiffNF`, `logCondNF` of
`IUT.Applications.VojtaNumberField` on the line minus `{0, 1, ∞}`.

1. Height (`htExt_heightNF_algebraMap`): for number fields `K ⊆ L` and `y ∈ K`,
   `heightNF L y = heightNF K y`. The proof writes Mathlib's `Height.logHeight₁ y` (the sum of
   `mult(v) log⁺ |y|_v` over the infinite places and of `log⁺ |y|_v` over the finite places) as
   the degree `deg_K` of an effective arithmetic divisor `htExtPoleDiv y` (the polar divisor of
   `y`: coefficient `max(0, -ord_v(y))` at a finite place, `[K_v : ℝ] log⁺ |y|_v` at an
   archimedean place), shows that its pull-back to `L` along `degPbPullback` is the polar divisor
   of `y` in `L` (`htExt_pullback_poleDiv`), and applies `degPb_degF_pullback`. This is the
   invariance of [GenEll] page 4 for the Weil height on `ℙ¹`. It extends the case `K = ℚ` of
   `IUT.VojtaNumberField.heightNF_algebraMap_rat`; `htExt_heightNF_ringHom` gives the same for
   any ring homomorphism `K →+* L`, in particular for isomorphisms of number fields.
2. Log-different: `htExt_logDiffNF_le` (`log-diff_K ≤ log-diff_L`, from the tower formula
   `degPb_logDiffNF_tower`) and `htExt_logDiffNF_rat_lt_cyclotomicThree` (`log-diff_ℚ = 0 <
   (1/2) log 3 = log-diff_{ℚ(ζ₃)}`): it is not invariant.
3. Log-conductor: for `y ∈ K \ {0, 1}` and the finite set `S` of primes of `K` at which `y` meets
   `{0, 1, ∞}`, the identity `htExt_finrank_mul_logCondNF_sub`:
   `[L : ℚ] (log-cond_K(y) - log-cond_L(y)) = Σ_{v ∈ S} Σ_{w | v} (e(w|v) - 1) log q_w`.
   Hence `log-cond_L(y) ≤ log-cond_K(y)` (`htExt_logCondNF_algebraMap_le`), with equality when
   `L/K` is unramified at the primes of `L` where `y` meets the boundary
   (`htExt_logCondNF_algebraMap_eq_of_unramified`). The sum `log-diff + log-cond` does not
   decrease (`IUT.PaperIV.DegreePullback.degPb_logDiffNF_add_logCondNF_le`).
4. Reading on the minimal field: for `x` in a number field `L`, with `ℚ(x)` the intermediate
   field `IntermediateField.adjoin ℚ {x}` and `g` its generator, `g` generates `ℚ(x)`
   (`htExt_adjoin_gen_eq_top`), `heightNF ℚ(x) g = heightNF L x` (`htExt_heightNF_adjoin`),
   and an inequality `ht ≤ (1 + ε)(log-diff + log-cond) + C` at `g` in `ℚ(x)` gives the same
   inequality at `x` in `L` (`htExt_ineq_algebraMap`, `htExt_ineq_of_adjoin`).
5. The registered statement `VojtaLineMinusThreePointsDegreeAtMost d` already reads each point
   on its minimal field (its hypothesis `IntermediateField.adjoin ℚ {x} = ⊤`). The theorem
   `htExt_degreeAtMost_iff_anyField` proves it equivalent, with the same constant, to
   `htExtDegreeAtMostAnyFieldStatement d`, in which the point `x` is read in any number field
   `F` of degree at most `d` containing it, with `log-diff` and `log-cond` evaluated at `F`. That
   form is an open family of statements of this project, not a statement of the papers; neither
   form is proved here.
6. Nonvacuity: `y = 1/3` has normalized height `log 3` in `ℚ` and in the quadratic field
   `ℚ(ζ₃) = ℚ(√-3)` (Mathlib's `CyclotomicField 3 ℚ`), `htExt_heightNF_oneThird`.

**Not proved.**

* The identification of `heightNF` with the height `ht_{ω_P(C)}` of [GenEll] page 4 attached to
  an arithmetic line bundle (see `IUT.Applications.VojtaNumberField`); only the Weil height is
  treated.
* An example where the log-conductor strictly drops (a point whose conductor contains a prime
  that ramifies in `L`); only the identity, the inequality and the unramified equality are proved.
* Equality of `log-diff + log-cond` along an extension unramified at every prime (it would need
  the relative different to be the unit ideal).
* Statements for the compactly bounded subsets of `IUT.Applications.CompactlyBounded`: the
  analogous equivalence for `cbDegreeAtMostStatement` would also need that membership `cbMem` of
  `x` does not depend on the field in which it is read (every embedding of `L` restricts to an
  embedding of `ℚ(x)` and every embedding of `ℚ(x)` extends to `L`). The extension of embeddings
  into `ℂ` and into `ℚ̄_p` is not formalized here.
-/

namespace IUT.HeightExtension

open NumberField IsDedekindDomain
open scoped Classical
open IUT.PaperIV IUT.PaperIV.DegreePullback IUT.VojtaNumberField

/-! ## The polar divisor and the height -/

section Height

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
  [Algebra K L]

/-- The coefficients of the polar divisor of `y`: `max(0, -ord_v(y))` at a finite place `v` and
`[K_v : ℝ]·log⁺ |y|_v` at an archimedean place `v`, with `[K_v : ℝ] = InfinitePlace.mult v`. -/
noncomputable def htExtPoleCoeff (y : K) : Valuations K → ℝ
  | .inl v => max 0 (-(degPbOrd v y : ℝ))
  | .inr w => (w.mult : ℝ) * Real.posLog (w y)

theorem htExtPoleCoeff_support_finite {y : K} (hy : y ≠ 0) :
    (Function.support (htExtPoleCoeff y)).Finite := by
  refine (((degPbOrd_finite hy).image Sum.inl).union
    (Set.finite_range (Sum.inr : InfinitePlace K → Valuations K))).subset ?_
  rintro (v | w) hv
  · refine Or.inl ⟨v, ?_, rfl⟩
    rw [Function.mem_support] at hv
    intro h0
    apply hv
    have h0' : (degPbOrd v y : ℝ) = 0 := by exact_mod_cast h0
    simp [htExtPoleCoeff, h0']
  · exact Or.inr ⟨w, rfl⟩

/-- **The polar divisor of `y ∈ K^×`**, an effective arithmetic divisor whose degree `deg_K` is
`Height.logHeight₁ y` (`htExt_degF_poleDiv`). -/
noncomputable def htExtPoleDiv (y : Kˣ) : ADiv K :=
  Finsupp.ofSupportFinite (htExtPoleCoeff (y : K)) (htExtPoleCoeff_support_finite y.ne_zero)

/-- At a finite place, `log⁺ |y|_v = log q_v · max(0, -ord_v(y))`. -/
theorem htExt_posLog_finitePlace {y : K} (hy : y ≠ 0) (v : HeightOneSpectrum (𝓞 K)) :
    Real.posLog (FinitePlace.mk v y) =
      Real.log (Ideal.absNorm v.asIdeal) * max 0 (-(degPbOrd v y : ℝ)) := by
  rw [Real.posLog_apply, degPb_log_finitePlace hy,
    mul_max_of_nonneg _ _ (Real.log_natCast_nonneg _), mul_zero]
  congr 1
  ring

/-- **The degree of the polar divisor is the height**: `deg_K(htExtPoleDiv y) =
Height.logHeight₁ y`, Mathlib's unnormalized logarithmic height on the number field `K`. -/
theorem htExt_degF_poleDiv (y : Kˣ) : degF (htExtPoleDiv y) = Height.logHeight₁ (y : K) := by
  have hy : (y : K) ≠ 0 := y.ne_zero
  set T := (degPbOrd_finite hy).toFinset
  have hsupp : (htExtPoleDiv y).support ⊆ T.disjSum Finset.univ := by
    intro t ht
    rw [Finsupp.mem_support_iff] at ht
    rcases t with v | w
    · rw [Finset.inl_mem_disjSum, Set.Finite.mem_toFinset]
      intro h0
      apply ht
      have h0' : (degPbOrd v (y : K) : ℝ) = 0 := by exact_mod_cast h0
      simp [htExtPoleDiv, htExtPoleCoeff, h0']
    · exact Finset.inr_mem_disjSum.mpr (Finset.mem_univ _)
  rw [degF_apply, Finsupp.sum_of_support_subset _ hsupp _ (fun _ _ => mul_zero _),
    Finset.sum_disjSum, NumberField.logHeight₁_eq]
  simp only [htExtPoleDiv, Finsupp.ofSupportFinite_coe, htExtPoleCoeff, degWeight, one_mul]
  have hfp : ∑ᶠ w : FinitePlace K, Real.posLog (w (y : K)) =
      ∑ᶠ v : HeightOneSpectrum (𝓞 K), Real.posLog (FinitePlace.mk v (y : K)) := by
    rw [← finsum_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    rfl
  have hsub : Function.support (fun v : HeightOneSpectrum (𝓞 K) =>
      Real.posLog (FinitePlace.mk v (y : K))) ⊆ ↑T := by
    intro v hv
    rw [Function.mem_support, htExt_posLog_finitePlace hy] at hv
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    intro h0
    apply hv
    have h0' : (degPbOrd v (y : K) : ℝ) = 0 := by exact_mod_cast h0
    simp [h0']
  rw [hfp, finsum_eq_sum_of_support_subset _ hsub, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun v _ => (htExt_posLog_finitePlace hy v).symm

/-- **The pull-back of the polar divisor is the polar divisor**: `(htExtPoleDiv y)|_L =
htExtPoleDiv y` with `y` viewed in `L`. At a finite place `w | v`, `e(w|v)·max(0, -ord_v(y)) =
max(0, -ord_w(y))`; at an archimedean place `w | v`, `[L_w : K_v]·[K_v : ℝ]·log⁺ |y|_v =
[L_w : ℝ]·log⁺ |y|_w`. -/
theorem htExt_pullback_poleDiv (y : Kˣ) :
    degPbPullback L (htExtPoleDiv y) =
      htExtPoleDiv (Units.map (algebraMap K L).toMonoidHom y) := by
  ext t
  rcases t with w | w
  · rw [degPbPullback_apply_inl]
    simp only [htExtPoleDiv, Finsupp.ofSupportFinite_coe, htExtPoleCoeff, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
    rw [degPb_ord_algebraMap]
    push_cast
    rw [mul_max_of_nonneg _ _ (Nat.cast_nonneg _), mul_zero, mul_neg]
  · rw [degPbPullback_apply_inr]
    simp only [htExtPoleDiv, Finsupp.ofSupportFinite_coe, htExtPoleCoeff, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
    rw [InfinitePlace.comap_apply, ← degPb_mult_mul_inertiaDeg (K := K) L w]
    push_cast
    ring

/-- `Height.logHeight₁` computed in `L` is `[L : K]` times its value in `K`. -/
theorem htExt_logHeight₁_algebraMap (y : K) :
    Height.logHeight₁ (algebraMap K L y) = Module.finrank K L * Height.logHeight₁ y := by
  by_cases hy : y = 0
  · subst hy
    rw [map_zero, Height.logHeight₁_zero, Height.logHeight₁_zero, mul_zero]
  · set u := Units.mk0 y hy
    have h2 := htExt_degF_poleDiv (Units.map (algebraMap K L).toMonoidHom u)
    rw [← htExt_pullback_poleDiv L u, degPb_degF_pullback, htExt_degF_poleDiv] at h2
    exact h2.symm

/-- **The normalized height does not depend on the number field** ([GenEll] page 4: `ht(x)` may
be computed through any morphism `Spec 𝒪_F → X` giving rise to `x`): for number fields `K ⊆ L`
and `y ∈ K`, `heightNF L y = heightNF K y`. -/
theorem htExt_heightNF_algebraMap (y : K) :
    heightNF L (algebraMap K L y) = heightNF K y := by
  have hK : (0 : ℝ) < Module.finrank ℚ K := IUT.VojtaNumberField.finrank_pos_real K
  have hKL : (0 : ℝ) < Module.finrank K L := by exact_mod_cast Module.finrank_pos
  have htow : (Module.finrank ℚ K : ℝ) * Module.finrank K L = Module.finrank ℚ L := by
    exact_mod_cast Module.finrank_mul_finrank ℚ K L
  rw [heightNF, heightNF, htExt_logHeight₁_algebraMap, ← htow]
  field_simp

omit [Algebra K L] in
/-- **The normalized height is invariant under every ring homomorphism of number fields**, in
particular under isomorphisms: `heightNF L (f y) = heightNF K y` for `f : K →+* L`. -/
theorem htExt_heightNF_ringHom (f : K →+* L) (y : K) : heightNF L (f y) = heightNF K y := by
  let _ : Algebra K L := f.toAlgebra
  exact htExt_heightNF_algebraMap L y

end Height

/-! ## The log-different -/

section LogDiff

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
  [Algebra K L]

/-- **The log-different does not decrease under extension**: `log-diff_K ≤ log-diff_L`, from
the tower formula `log-diff_L = log-diff_K + (1/[L : ℚ]) log N(𝔇_{L/K})`. -/
theorem htExt_logDiffNF_le : logDiffNF K ≤ logDiffNF L := by
  rw [degPb_logDiffNF_tower (K := K) L]
  have : 0 ≤ Real.log (Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L))) / Module.finrank ℚ L :=
    div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  linarith

/-- **The log-different is not invariant under extension**: `log-diff_ℚ = 0`, while for the
quadratic field `ℚ(ζ₃)` (Mathlib's `CyclotomicField 3 ℚ`) `log-diff = (1/2) log 3 > 0`. -/
theorem htExt_logDiffNF_rat_lt_cyclotomicThree :
    logDiffNF ℚ < logDiffNF (CyclotomicField 3 ℚ) := by
  have : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  rw [logDiffNF_rat, logDiffNF_cyclotomicThree]
  have : 0 < Real.log 3 := Real.log_pos (by norm_num)
  linarith

end LogDiff

/-! ## The log-conductor -/

section LogCond

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
  [Algebra K L]

/-- The log-conductor as a finite sum: if `S` is exactly the set of primes of `𝓞 K` at which
`y` meets `{0, 1, ∞}`, then `log-cond_K(y) = (1/[K : ℚ]) Σ_{v ∈ S} log q_v`. -/
theorem htExt_logCondNF_eq_sum (S : Finset (HeightOneSpectrum (𝓞 K))) {y : K}
    (hS : ∀ v, v ∈ S ↔ MeetsBoundaryAt K v y) :
    logCondNF K y = (∑ v ∈ S, Real.log (Ideal.absNorm v.asIdeal)) / Module.finrank ℚ K := by
  unfold logCondNF
  congr 1
  rw [finsum_eq_sum_of_support_subset _ (s := S) ?_]
  · refine Finset.sum_congr rfl fun v hv => ?_
    rw [ite_eq_left ((hS v).mp hv), degPb_card_quot]
  · intro v hv
    rw [Function.mem_support] at hv
    rw [Finset.mem_coe, hS]
    by_contra h
    exact hv (ite_eq_right h)

/-- The log-conductor of `y ∈ K` read in `L`, as a finite sum over the primes of `𝓞 L` above
`S`: `log-cond_L(y) = (1/[L : ℚ]) Σ_{v ∈ S} Σ_{w | v} log q_w`. -/
theorem htExt_logCondNF_algebraMap_eq_sum (S : Finset (HeightOneSpectrum (𝓞 K))) {y : K}
    (hS : ∀ v, v ∈ S ↔ MeetsBoundaryAt K v y) :
    logCondNF L (algebraMap K L y) =
      (∑ v ∈ S, ∑ q : v.asIdeal.primesOver (𝓞 L), Real.log (Ideal.absNorm q.1)) /
        Module.finrank ℚ L := by
  unfold logCondNF
  congr 1
  set T := S.biUnion fun v => Finset.univ.image (degPbPrimeOf L v)
  have hsub : Function.support (fun w : HeightOneSpectrum (𝓞 L) =>
      if MeetsBoundaryAt L w (algebraMap K L y) then Real.log (Nat.card (𝓞 L ⧸ w.asIdeal))
      else 0) ⊆ ↑T := by
    intro w hw
    rw [Function.mem_support] at hw
    have hm : MeetsBoundaryAt L w (algebraMap K L y) := by
      by_contra h
      exact hw (ite_eq_right h)
    have hv : HeightOneSpectrum.under (𝓞 K) w ∈ S :=
      (hS _).mpr ((degPb_meetsBoundaryAt_iff L w y).mp hm)
    rw [Finset.coe_biUnion]
    refine Set.mem_iUnion₂.mpr ⟨_, hv, ?_⟩
    rw [Finset.coe_image]
    exact ⟨⟨w.asIdeal, w.isPrime, ⟨rfl⟩⟩, Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩
  rw [finsum_eq_sum_of_support_subset _ hsub, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun v hv => ?_
    rw [Finset.sum_image fun q _ q' _ h => degPb_primeOf_injective L v h]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hm : MeetsBoundaryAt L (degPbPrimeOf L v q) (algebraMap K L y) := by
      rw [degPb_meetsBoundaryAt_iff, degPb_under_primeOf]
      exact (hS v).mp hv
    rw [ite_eq_left hm, degPb_card_quot]
    rfl
  · intro v _ v' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro w hw hw'
    rw [Finset.mem_image] at hw hw'
    obtain ⟨q, -, rfl⟩ := hw
    obtain ⟨q', -, hq'⟩ := hw'
    apply hne
    rw [← degPb_under_primeOf L v q, ← degPb_under_primeOf L v' q', hq']

/-- **The change of the log-conductor under extension**: if `S` is the set of primes of `𝓞 K`
at which `y` meets `{0, 1, ∞}`, then
`[L : ℚ]·(log-cond_K(y) - log-cond_L(y)) = Σ_{v ∈ S} Σ_{w | v} (e(w|v) - 1)·log q_w`. -/
theorem htExt_finrank_mul_logCondNF_sub (S : Finset (HeightOneSpectrum (𝓞 K))) {y : K}
    (hS : ∀ v, v ∈ S ↔ MeetsBoundaryAt K v y) :
    (Module.finrank ℚ L : ℝ) * (logCondNF K y - logCondNF L (algebraMap K L y)) =
      ∑ v ∈ S, ∑ q : v.asIdeal.primesOver (𝓞 L),
        ((q.1.ramificationIdx (𝓞 K) : ℝ) - 1) * Real.log (Ideal.absNorm q.1) := by
  have hK : (0 : ℝ) < Module.finrank ℚ K := IUT.VojtaNumberField.finrank_pos_real K
  have hL : (0 : ℝ) < Module.finrank ℚ L := IUT.VojtaNumberField.finrank_pos_real L
  have htow : (Module.finrank ℚ K : ℝ) * Module.finrank K L = Module.finrank ℚ L := by
    exact_mod_cast Module.finrank_mul_finrank ℚ K L
  have hfib : (Module.finrank K L : ℝ) * ∑ v ∈ S, Real.log (Ideal.absNorm v.asIdeal) =
      ∑ v ∈ S, ∑ q : v.asIdeal.primesOver (𝓞 L),
        (q.1.ramificationIdx (𝓞 K) : ℝ) * Real.log (Ideal.absNorm q.1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => (degPb_sum_ramificationIdx_log L v).symm
  have hsplit : ∑ v ∈ S, ∑ q : v.asIdeal.primesOver (𝓞 L),
        ((q.1.ramificationIdx (𝓞 K) : ℝ) - 1) * Real.log (Ideal.absNorm q.1) =
      ∑ v ∈ S, ∑ q : v.asIdeal.primesOver (𝓞 L),
        (q.1.ramificationIdx (𝓞 K) : ℝ) * Real.log (Ideal.absNorm q.1) -
      ∑ v ∈ S, ∑ q : v.asIdeal.primesOver (𝓞 L), Real.log (Ideal.absNorm q.1) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [htExt_logCondNF_eq_sum S hS, htExt_logCondNF_algebraMap_eq_sum L S hS, hsplit, ← hfib,
    ← htow]
  have hKL : (0 : ℝ) < Module.finrank K L := by exact_mod_cast Module.finrank_pos
  field_simp

/-- The finite set of primes at which a point `y ∉ {0, 1}` meets `{0, 1, ∞}`. -/
noncomputable def htExtConductorSet {y : K} (hy0 : y ≠ 0) (hy1 : y ≠ 1) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (degPb_meetsBoundaryAt_finite hy0 hy1).toFinset

theorem htExt_mem_conductorSet {y : K} (hy0 : y ≠ 0) (hy1 : y ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) : v ∈ htExtConductorSet hy0 hy1 ↔ MeetsBoundaryAt K v y := by
  rw [htExtConductorSet, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

/-- **The log-conductor does not increase under extension**: for `y ∈ K \ {0, 1}`,
`log-cond_L(y) ≤ log-cond_K(y)`. The reduced conductor loses `(e(w|v) - 1) log q_w` at each
ramified prime `w` over the conductor. -/
theorem htExt_logCondNF_algebraMap_le {y : K} (hy0 : y ≠ 0) (hy1 : y ≠ 1) :
    logCondNF L (algebraMap K L y) ≤ logCondNF K y := by
  have h := htExt_finrank_mul_logCondNF_sub L (htExtConductorSet hy0 hy1)
    (htExt_mem_conductorSet hy0 hy1)
  have hL : (0 : ℝ) < Module.finrank ℚ L := IUT.VojtaNumberField.finrank_pos_real L
  have hnn : 0 ≤ ∑ v ∈ htExtConductorSet hy0 hy1, ∑ q : v.asIdeal.primesOver (𝓞 L),
      ((q.1.ramificationIdx (𝓞 K) : ℝ) - 1) * Real.log (Ideal.absNorm q.1) := by
    refine Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun q _ => ?_
    have := q.2.1
    have := q.2.2
    have he := Ideal.ramificationIdx_pos_of_isDedekindDomain' q.1 v.ne_bot
    have he' : (1 : ℝ) ≤ q.1.ramificationIdx (𝓞 K) := by exact_mod_cast he
    exact mul_nonneg (by linarith) (Real.log_natCast_nonneg _)
  rw [← h] at hnn
  have := (mul_nonneg_iff_of_pos_left hL).mp hnn
  linarith

/-- **The log-conductor is invariant under extensions unramified at the conductor**: for
`y ∈ K \ {0, 1}`, if every prime `w` of `𝓞 L` at which `y` meets `{0, 1, ∞}` is unramified over
`K` (`e(w|v) = 1`), then `log-cond_L(y) = log-cond_K(y)`. -/
theorem htExt_logCondNF_algebraMap_eq_of_unramified {y : K} (hy0 : y ≠ 0) (hy1 : y ≠ 1)
    (hun : ∀ w : HeightOneSpectrum (𝓞 L), MeetsBoundaryAt L w (algebraMap K L y) →
      w.asIdeal.ramificationIdx (𝓞 K) = 1) :
    logCondNF L (algebraMap K L y) = logCondNF K y := by
  have h := htExt_finrank_mul_logCondNF_sub L (htExtConductorSet hy0 hy1)
    (htExt_mem_conductorSet hy0 hy1)
  have hL : (0 : ℝ) < Module.finrank ℚ L := IUT.VojtaNumberField.finrank_pos_real L
  have hzero : ∑ v ∈ htExtConductorSet hy0 hy1, ∑ q : v.asIdeal.primesOver (𝓞 L),
      ((q.1.ramificationIdx (𝓞 K) : ℝ) - 1) * Real.log (Ideal.absNorm q.1) = 0 := by
    refine Finset.sum_eq_zero fun v hv => Finset.sum_eq_zero fun q _ => ?_
    have hm : MeetsBoundaryAt L (degPbPrimeOf L v q) (algebraMap K L y) := by
      rw [degPb_meetsBoundaryAt_iff, degPb_under_primeOf]
      exact (htExt_mem_conductorSet hy0 hy1 v).mp hv
    have he : q.1.ramificationIdx (𝓞 K) = 1 := hun _ hm
    rw [he]
    simp
  rw [hzero, mul_eq_zero] at h
  rcases h with h | h
  · exact absurd h hL.ne'
  · linarith

end LogCond

/-! ## Reading a point on its minimal field -/

section MinimalField

/-- **The inequality transfers to larger fields.** For number fields `K ⊆ L`, `y ∈ K \ {0, 1}`
and `1 + ε ≥ 0`: if `ht(y) ≤ (1 + ε)(log-diff + log-cond)(y) + C` with `y` read in `K`, then the
same holds with `y` read in `L`. The height is unchanged (`htExt_heightNF_algebraMap`) and
`log-diff + log-cond` does not decrease (`degPb_logDiffNF_add_logCondNF_le`). -/
theorem htExt_ineq_algebraMap {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L]
    [NumberField L] [Algebra K L] {y : K} (hy0 : y ≠ 0) (hy1 : y ≠ 1) {ε C : ℝ}
    (hε : 0 ≤ 1 + ε) (h : heightNF K y ≤ (1 + ε) * (logDiffNF K + logCondNF K y) + C) :
    heightNF L (algebraMap K L y) ≤
      (1 + ε) * (logDiffNF L + logCondNF L (algebraMap K L y)) + C := by
  rw [htExt_heightNF_algebraMap]
  have := mul_le_mul_of_nonneg_left (degPb_logDiffNF_add_logCondNF_le L hy0 hy1) hε
  linarith

variable {L : Type*} [Field L] [NumberField L]

/-- The generator `x` of `ℚ(x) ⊆ L` generates `ℚ(x)` as a field: `ℚ(x)` is the minimal field of
definition of `x` ([GenEll] Definition 1.5 (i)). -/
theorem htExt_adjoin_gen_eq_top (x : L) :
    IntermediateField.adjoin ℚ {IntermediateField.AdjoinSimple.gen ℚ x} = ⊤ :=
  IntermediateField.lift_injective _ (by
    rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]
    rfl)

/-- **The height of `x` read in `L` equals its height read in its minimal field `ℚ(x)`.** -/
theorem htExt_heightNF_adjoin (x : L) :
    heightNF (IntermediateField.adjoin ℚ {x}) (IntermediateField.AdjoinSimple.gen ℚ x) =
      heightNF L x := by
  have h := htExt_heightNF_algebraMap L (IntermediateField.AdjoinSimple.gen ℚ x)
  rw [IntermediateField.AdjoinSimple.algebraMap_gen] at h
  exact h.symm

theorem htExt_gen_ne_zero {x : L} (hx0 : x ≠ 0) :
    IntermediateField.AdjoinSimple.gen ℚ x ≠ 0 := fun h => hx0 (by
  rw [← IntermediateField.AdjoinSimple.algebraMap_gen ℚ x, h, map_zero])

theorem htExt_gen_ne_one {x : L} (hx1 : x ≠ 1) :
    IntermediateField.AdjoinSimple.gen ℚ x ≠ 1 := fun h => hx1 (by
  rw [← IntermediateField.AdjoinSimple.algebraMap_gen ℚ x, h, map_one])

/-- **The inequality read on the minimal field implies the inequality read in `L`**: for
`x ∈ L \ {0, 1}` and `1 + ε ≥ 0`, if `ht ≤ (1 + ε)(log-diff + log-cond) + C` holds at the
generator of `ℚ(x)`, it holds at `x` in `L`. -/
theorem htExt_ineq_of_adjoin {x : L} (hx0 : x ≠ 0) (hx1 : x ≠ 1) {ε C : ℝ} (hε : 0 ≤ 1 + ε)
    (h : heightNF (IntermediateField.adjoin ℚ {x}) (IntermediateField.AdjoinSimple.gen ℚ x) ≤
      (1 + ε) * (logDiffNF (IntermediateField.adjoin ℚ {x}) +
        logCondNF (IntermediateField.adjoin ℚ {x}) (IntermediateField.AdjoinSimple.gen ℚ x)) +
        C) :
    heightNF L x ≤ (1 + ε) * (logDiffNF L + logCondNF L x) + C := by
  have h2 := htExt_ineq_algebraMap L (htExt_gen_ne_zero hx0) (htExt_gen_ne_one hx1) hε h
  rwa [IntermediateField.AdjoinSimple.algebraMap_gen] at h2

/-- The degree of `ℚ(x)` is at most the degree of `L`. -/
theorem htExt_finrank_adjoin_le (x : L) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) ≤ Module.finrank ℚ L := by
  rw [← Module.finrank_mul_finrank ℚ (IntermediateField.adjoin ℚ {x}) L]
  exact Nat.le_mul_of_pos_right _ Module.finrank_pos

end MinimalField

/-- **An open family of statements of this project, not a theorem and not a statement of the
papers**: the inequality of `VojtaLineMinusThreePointsDegreeAtMost d` with each point `x` read in
an arbitrary number field `F` of degree at most `d` containing it, and `log-diff`, `log-cond`
evaluated at `F` instead of at the minimal field of definition of `x`. It is equivalent to
`VojtaLineMinusThreePointsDegreeAtMost d` (`htExt_degreeAtMost_iff_anyField`). -/
def htExtDegreeAtMostAnyFieldStatement (d : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ (F : Type) [Field F] [NumberField F] (x : F),
    Module.finrank ℚ F ≤ d → x ≠ 0 → x ≠ 1 →
      heightNF F x ≤ (1 + ε) * (logDiffNF F + logCondNF F x) + C

/-- **The registered statement, which reads each point on its minimal field, is equivalent to the
statement reading each point in any number field of degree at most `d` containing it**, with the
same constants. One direction restricts to fields generated by the point; the other passes from
`F` to `ℚ(x) ⊆ F`, of degree at most `[F : ℚ] ≤ d`, by `htExt_ineq_of_adjoin`. Neither side is
proved. -/
theorem htExt_degreeAtMost_iff_anyField (d : ℕ) :
    VojtaLineMinusThreePointsDegreeAtMost d ↔ htExtDegreeAtMostAnyFieldStatement d := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC⟩ := h ε hε
    refine ⟨C, fun F _ _ x hdeg hx0 hx1 => ?_⟩
    exact htExt_ineq_of_adjoin hx0 hx1 (by linarith)
      (hC (IntermediateField.adjoin ℚ {x}) (IntermediateField.AdjoinSimple.gen ℚ x)
        (htExt_adjoin_gen_eq_top x) ((htExt_finrank_adjoin_le x).trans hdeg)
        (htExt_gen_ne_zero hx0) (htExt_gen_ne_one hx1))
  · intro h ε hε
    obtain ⟨C, hC⟩ := h ε hε
    exact ⟨C, fun F _ _ x _ hdeg hx0 hx1 => hC F x hdeg hx0 hx1⟩

/-! ## Example: `1/3` in `ℚ` and in `ℚ(ζ₃)` -/

/-- **Nonvacuity.** `ℚ(ζ₃) = ℚ(√-3)` (Mathlib's `CyclotomicField 3 ℚ`) is a quadratic field, and
the point `1/3` has the same normalized height `log 3` in `ℚ` and in `ℚ(ζ₃)`. -/
theorem htExt_heightNF_oneThird :
    Module.finrank ℚ (CyclotomicField 3 ℚ) = 2 ∧
      heightNF ℚ (1 / 3) = Real.log 3 ∧
      heightNF (CyclotomicField 3 ℚ) (algebraMap ℚ (CyclotomicField 3 ℚ) (1 / 3)) =
        Real.log 3 := by
  have : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  have hQ : heightNF ℚ (1 / 3) = Real.log 3 := by
    rw [heightNF_rat, Rat.logHeight₁_eq_log_max]
    have hn : (1 / 3 : ℚ).num = 1 := by norm_num
    have hd : (1 / 3 : ℚ).den = 3 := by norm_num
    rw [hn, hd]
    norm_num
  exact ⟨finrank_cyclotomicThree _, hQ, (htExt_heightNF_algebraMap _ _).trans hQ⟩

end IUT.HeightExtension
