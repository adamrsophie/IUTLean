import IUT.PaperIV.Definition1_9
import IUT.Applications.VojtaNumberField

/-!
# IUT IV, Definition 1.9 (i): pull-back of arithmetic divisors and invariance of the
# normalized degree

Sources: Mochizuki, *Inter-universal Teichmüller Theory IV*, Definition 1.9 (pages 21 and 22),
the definitions of `log(𝔡^{F□})` and `log(𝔣^{F□})` in the statement of Theorem 1.10 (pages 22
and 23) and Step (ii) of the proof of Theorem 1.10 (page 24); Mochizuki, *Arithmetic Elliptic
Curves in General Position* ([GenEll]), §1 (pages 3 and 4: arithmetic divisors, principal
arithmetic divisors, the degree `deg_F`, the normalized degree and its invariance under finite
extension for arithmetic line bundles), Definition 1.5 (page 8), Propositions 1.6 and 1.7 with
the proof of 1.7 (pages 9 and 10). Pages read for this file: IUT IV pages 21 to 24; [GenEll]
pages 3, 4, 8, 9 and 10. Pages checked against rendered images: all of these.

## The conventions, and which sentences fix them

* IUT IV page 21: the degree `deg_F` sends a nonarchimedean `v` to `log(q_v)` and an archimedean
  `v` to `1`; page 22: `deg = deg_F/[F : ℚ]`, and "Thus, for any finite extension `K` of `F`, we
  have `deg(𝔞|_K) = deg(𝔞)`", where `deg(𝔞|_K)` is the normalized degree of "the pull-back
  `𝔞|_K ∈ ADiv_ℝ(K)` [defined in the evident fashion] of `𝔞` to `K`". The page prints no formula
  for the pull-back and no principal divisor.
* [GenEll] page 4 prints the principal arithmetic divisor
  `ADiv(f) = ∑_{v non} ord_v(f)·v - ∑_{v arc} [F_v : ℝ]·log(|f|_v)·v`, the same degree map (weight
  `1` at every archimedean place), and the isomorphism `ADiv(F)/APrc(F) ≅ APic(Spec 𝒪_F)`, under
  which it states `deg_K(𝓛|_{Spec 𝒪_K}) = deg_F(𝓛)` (normalized) for arithmetic line bundles.
  This display fixes the archimedean coefficient convention: the factor `[F_v : ℝ]` sits in the
  coefficient, not in the weight. With it the degree of a principal divisor is zero
  (`degPb_degF_principal`); no coefficient convention at complex places has to be invented.
* The pull-back of divisors is not printed on either page. This file defines it as the
  pull-back that matches the pull-back of arithmetic line bundles: at a finite place `w | v` the
  coefficient is multiplied by the ramification index `e(w|v)`, and at an archimedean place
  `w | v` by the local degree `[L_w : K_v]` (`1` or `2`; `2` exactly for a complex `w` over a real
  `v`). This choice is derived, not quoted. Two checks that it is the evident one:
  `degPb_pullback_principal` proves that it sends the principal divisor of `x ∈ K^×` to the
  principal divisor of `x` in `L` (both as printed on [GenEll] page 4), and the coefficient
  formulas `degPbPullback_apply_inl`, `degPbPullback_apply_inr` state it place by place. The
  identification with the pull-back of arithmetic line bundles through `ADiv/APrc ≅ APic` is not
  formalized. [GenEll] takes integer coefficients at finite places; IUT IV takes real ones; the
  definitions here use real coefficients throughout.

## What is proved

* `degPbPullback` (an additive map `ADiv(K) → ADiv(L)`), with the coefficient formulas.
* `degPb_degF_pullback`: `deg_L(𝔞|_L) = [L : K]·deg_K(𝔞)`, from
  `∑_{w | v} e(w|v) f(w|v) = [L : K]` and `q_w = q_v^{f(w|v)}` at finite places and from
  `∑_{w | v} [L_w : K_v] = [L : K]` at archimedean places (Mathlib's
  `Ideal.sum_ramification_inertia_eq_finrank`, `Ideal.absNorm_pow_inertiaDeg`,
  `InfinitePlace.sum_inertiaDeg_eq_finrank`). These are the content; the definition does not
  build them in.
* `degPb_normalizedDeg_pullback`: **the invariance `deg(𝔞|_L) = deg(𝔞)` of Definition 1.9 (i)**.
* `degPbPrincipal`, `degPb_degF_principal`: the principal divisor of [GenEll] page 4 has degree
  zero (Mathlib's product formula `NumberField.prod_abs_eq_one`), and `degPb_pullback_principal`.
* `degPb_logDiffNF_tower`: `log-diff_L = log-diff_K + (1/[L : ℚ])·log N(𝔇_{L/K})`, with
  `logDiffNF` of `IUT.VojtaNumberField` (Mathlib's
  `natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow`).
* `degPb_logDiff_add_cond_le`: for a finite set `S` of primes of `K` and the reduced divisor of `L`
  supported on the primes over `S`, `log-diff_K + log-cond_K ≤ log-diff_L + log-cond_L`
  (normalized degrees). This is the shape of the first inequality of Step (ii) on page 24,
  `log(𝔡^{F_tpd}) + log(𝔣^{F_tpd}) ≤ log(𝔡^F) + log(𝔣^F)`, where the conductor `𝔣` of page 23 is
  the reduced divisor with the support of `𝔮`, and the support of `𝔮` over `F` is the set of
  places over the support over `F_tpd`. The paper derives the inequality from Proposition 1.3 (i);
  here the input is Mathlib's bound `w^{e(w|v) - 1} ∣ 𝔇_{L/K}`.
* `degPb_meetsBoundaryAt_finite`, `degPb_meetsBoundaryAt_iff`,
  `degPb_logDiffNF_add_logCondNF_le`: for `y ∈ K` off the boundary (`y ≠ 0`, `y ≠ 1`), the
  conductor is finite and `log-diff_K + log-cond_K(y) ≤ log-diff_L + log-cond_L(y)` with
  `logCondNF` of `IUT.VojtaNumberField` (the conductor of a point of `ℙ¹ \ {0, 1, ∞}`).

## Not proved

* The invariance `deg_{E|K}(𝔞|_K) = deg_E(𝔞)` of Definition 1.9 (ii).
* The isomorphism `ADiv/APrc ≅ APic` of [GenEll] page 4 and the pull-back of arithmetic line
  bundles.
* The inequality of Step (ii) for the paper's own objects: the divisor `𝔮` of `q`-parameters of
  the elliptic curve and the fields `F_tpd ⊆ F` of Theorem 1.10 are not defined here; only the
  inequality for an arbitrary reduced conductor pulled back from the smaller field is proved.
  The second inequality of Step (ii) (the bound by `log(2^{11}·3^3·5^2)`) and the bounds on
  `log(𝔡^K)` are not treated.
* [GenEll] Proposition 1.7 (log-conductor and log-different along a finite covering of curves)
  is a different statement; it is not formalized.
-/

namespace IUT.PaperIV.DegreePullback

open NumberField IsDedekindDomain
open scoped Classical

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
  [Algebra K L]

/-! ## The pull-back -/

/-- The height one prime of `𝓞 L` given by a prime ideal of `𝓞 L` lying over the prime `v` of
`𝓞 K`. -/
def degPbPrimeOf (v : HeightOneSpectrum (𝓞 K)) (q : v.asIdeal.primesOver (𝓞 L)) :
    HeightOneSpectrum (𝓞 L) where
  asIdeal := q.1
  isPrime := q.2.1
  ne_bot := by
    have := q.2.2
    exact Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot q.1

/-- The pull-back to `L` of the arithmetic divisor `1 · v` of `K`: at a finite place `v` the sum
of `e(w|v) · w` over the primes `w` of `𝓞 L` over `v`; at an archimedean place `v` the sum of
`[L_w : K_v] · w` over the archimedean places `w` of `L` over `v`, where `[L_w : K_v]` is
Mathlib's `InfinitePlace.inertiaDeg`, the degree of the completion `L_w` over `K_v`. -/
noncomputable def degPbSingle : Valuations K → ADiv L
  | .inl v => ∑ q : v.asIdeal.primesOver (𝓞 L),
      Finsupp.single (.inl (degPbPrimeOf L v q)) (q.1.ramificationIdx (𝓞 K) : ℝ)
  | .inr v => ∑ w ∈ (v.placesOver L).toFinset, Finsupp.single (.inr w) (v.inertiaDeg w : ℝ)

/-- The pull-back `𝔞 ↦ 𝔞|_L` of arithmetic divisors along `K ⊆ L`, extended additively from
`degPbSingle`. Its coefficients are computed in `degPbPullback_apply_inl` and
`degPbPullback_apply_inr`. -/
noncomputable def degPbPullback : ADiv K →+ ADiv L :=
  Finsupp.liftAddHom fun v => (smulAddHom ℝ (ADiv L)).flip (degPbSingle L v)

theorem degPbPullback_single (v : Valuations K) (c : ℝ) :
    degPbPullback L (Finsupp.single v c) = c • degPbSingle L v := by
  simp [degPbPullback]

/-! ## The coefficients of the pull-back -/

theorem degPbSingle_inl_apply_inl (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) :
    degPbSingle L (.inl v) (.inl w) =
      if v = HeightOneSpectrum.under (𝓞 K) w then (w.asIdeal.ramificationIdx (𝓞 K) : ℝ)
      else 0 := by
  simp only [degPbSingle, Finsupp.finsetSum_apply, Finsupp.single_apply, Sum.inl.injEq]
  split_ifs with h
  · have hw : w.asIdeal ∈ v.asIdeal.primesOver (𝓞 L) :=
      ⟨w.isPrime, (Ideal.liesOver_iff _ _).mpr (by rw [h]; rfl)⟩
    rw [Finset.sum_eq_single ⟨w.asIdeal, hw⟩]
    · exact ite_eq_left rfl
    · intro q _ hq
      refine ite_eq_right_of_eq_false _ _ (eq_false ?_)
      intro hqw
      apply hq
      apply Subtype.ext
      exact congrArg HeightOneSpectrum.asIdeal hqw
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · refine Finset.sum_eq_zero fun q _ => ite_eq_right_of_eq_false _ _ (eq_false ?_)
    intro hqw
    apply h
    have := q.2.2
    ext1
    rw [HeightOneSpectrum.under_asIdeal, ← hqw]
    exact Ideal.over_def q.1 v.asIdeal

theorem degPbSingle_inr_apply_inl (v : InfinitePlace K) (w : HeightOneSpectrum (𝓞 L)) :
    degPbSingle L (.inr v) (.inl w) = 0 := by
  simp [degPbSingle, Finsupp.finsetSum_apply]

theorem degPbSingle_inl_apply_inr (v : HeightOneSpectrum (𝓞 K)) (w : InfinitePlace L) :
    degPbSingle L (.inl v) (.inr w) = 0 := by
  simp [degPbSingle, Finsupp.finsetSum_apply]

omit [NumberField K] [NumberField L] in
theorem degPb_liesOver_iff (v : InfinitePlace K) (w : InfinitePlace L) :
    w.LiesOver v ↔ v = w.comap (algebraMap K L) := by
  constructor
  · intro h
    exact (InfinitePlace.LiesOver.comap_eq w v).symm
  · rintro rfl
    exact ⟨rfl⟩

theorem degPbSingle_inr_apply_inr (v : InfinitePlace K) (w : InfinitePlace L) :
    degPbSingle L (.inr v) (.inr w) =
      if v = w.comap (algebraMap K L) then (v.inertiaDeg w : ℝ) else 0 := by
  simp only [degPbSingle, Finsupp.finsetSum_apply, Finsupp.single_apply, Sum.inr.injEq]
  rw [Finset.sum_ite_eq']
  have hm : w ∈ (v.placesOver L).toFinset ↔ v = w.comap (algebraMap K L) := by
    rw [Set.mem_toFinset]
    exact degPb_liesOver_iff L v w
  exact if_congr hm rfl rfl

/-- **The coefficient of the pull-back at a finite place.** For a prime `w` of `𝓞 L` over the
prime `v = w ∩ 𝓞 K`, the coefficient of `𝔞|_L` at `w` is `e(w|v)` times the coefficient of `𝔞`
at `v`. -/
theorem degPbPullback_apply_inl (a : ADiv K) (w : HeightOneSpectrum (𝓞 L)) :
    degPbPullback L a (.inl w) =
      (w.asIdeal.ramificationIdx (𝓞 K) : ℝ) * a (.inl (HeightOneSpectrum.under (𝓞 K) w)) := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [map_add, ha, hb, mul_add]
  | single v c =>
    rw [degPbPullback_single, Finsupp.smul_apply, smul_eq_mul]
    cases v with
    | inl v =>
      rw [degPbSingle_inl_apply_inl, Finsupp.single_apply]
      by_cases h : v = HeightOneSpectrum.under (𝓞 K) w
      · subst h
        rw [ite_eq_left rfl, ite_eq_left rfl]
        ring
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h),
          ite_eq_right_of_eq_false _ _ (eq_false fun h' => h (Sum.inl_injective h'))]
        ring
    | inr v =>
      rw [degPbSingle_inr_apply_inl, Finsupp.single_apply,
        ite_eq_right_of_eq_false _ _ (eq_false Sum.inr_ne_inl)]
      ring

/-- **The coefficient of the pull-back at an archimedean place.** For an archimedean place `w`
of `L` over the place `v` of `K` below it, the coefficient of `𝔞|_L` at `w` is `[L_w : K_v]`
times the coefficient of `𝔞` at `v`. -/
theorem degPbPullback_apply_inr (a : ADiv K) (w : InfinitePlace L) :
    degPbPullback L a (.inr w) =
      ((w.comap (algebraMap K L)).inertiaDeg w : ℝ) * a (.inr (w.comap (algebraMap K L))) := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [map_add, ha, hb, mul_add]
  | single v c =>
    rw [degPbPullback_single, Finsupp.smul_apply, smul_eq_mul]
    cases v with
    | inl v =>
      rw [degPbSingle_inl_apply_inr, Finsupp.single_apply,
        ite_eq_right_of_eq_false _ _ (eq_false Sum.inl_ne_inr)]
      ring
    | inr v =>
      rw [degPbSingle_inr_apply_inr, Finsupp.single_apply]
      by_cases h : v = w.comap (algebraMap K L)
      · subst h
        rw [ite_eq_left rfl, ite_eq_left rfl]
        ring
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h),
          ite_eq_right_of_eq_false _ _ (eq_false fun h' => h (Sum.inr_injective h'))]
        ring

/-! ## Invariance of the normalized degree -/

theorem degPb_degF_smul {F : Type*} [Field F] [NumberField F] (c : ℝ) (x : ADiv F) :
    degF (c • x) = c * degF x := by
  rw [degF_apply, degF_apply, Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => ?_
  simp only [smul_eq_mul]
  ring

theorem degPb_finrank_int : Module.finrank (𝓞 K) (𝓞 L) = Module.finrank K L := by
  rw [IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L]

/-- The degrees of the places of `L` over a finite place `v` of `K`, weighted by the
ramification indices, add up to `[L : K]·log q_v`: `∑_{w | v} e(w|v)·log q_w = [L : K]·log q_v`,
from `∑_{w | v} e(w|v) f(w|v) = [L : K]` and `q_w = q_v^{f(w|v)}`. -/
theorem degPb_degF_single_inl (v : HeightOneSpectrum (𝓞 K)) :
    degF (degPbSingle L (.inl v)) = Module.finrank K L * degWeight (.inl v : Valuations K) := by
  have : v.asIdeal.IsMaximal := v.isMaximal
  simp only [degPbSingle, map_sum, degF_single, degWeight]
  have hterm : ∀ q : v.asIdeal.primesOver (𝓞 L),
      Real.log (Ideal.absNorm (degPbPrimeOf L v q).asIdeal) *
        (q.1.ramificationIdx (𝓞 K) : ℝ) =
      Real.log (Ideal.absNorm v.asIdeal) *
        ((q.1.ramificationIdx (𝓞 K) * q.1.inertiaDeg (𝓞 K) : ℕ) : ℝ) := by
    intro q
    have := q.2.1
    have := q.2.2
    have h := Ideal.absNorm_pow_inertiaDeg v.asIdeal q.1
    simp only [degPbPrimeOf]
    rw [← h, Nat.cast_pow, Real.log_pow]
    push_cast; ring
  rw [Finset.sum_congr rfl fun q _ => hterm q, ← Finset.mul_sum, ← Nat.cast_sum,
    Ideal.sum_ramification_inertia_eq_finrank, degPb_finrank_int]
  ring

/-- The local degrees `[L_w : K_v]` over an archimedean place `v` of `K` add up to `[L : K]`. -/
theorem degPb_degF_single_inr (v : InfinitePlace K) :
    degF (degPbSingle L (.inr v)) = Module.finrank K L * degWeight (.inr v : Valuations K) := by
  simp only [degPbSingle, map_sum, degF_single, degWeight, one_mul, mul_one]
  rw [← Nat.cast_sum]
  congr 1
  convert InfinitePlace.sum_inertiaDeg_eq_finrank K L v

/-- `deg_L(𝔞|_L) = [L : K]·deg_K(𝔞)`. -/
theorem degPb_degF_pullback (a : ADiv K) :
    degF (degPbPullback L a) = Module.finrank K L * degF a := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [map_add, ha, hb, mul_add]
  | single v c =>
    rw [degPbPullback_single, degPb_degF_smul, degF_single]
    cases v with
    | inl v => rw [degPb_degF_single_inl]; ring
    | inr v => rw [degPb_degF_single_inr]; ring

/-- **Invariance of the normalized degree under pull-back** (IUT IV, Definition 1.9 (i),
page 22): `deg(𝔞|_L) = deg(𝔞)`. -/
theorem degPb_normalizedDeg_pullback (a : ADiv K) :
    normalizedDeg (degPbPullback L a) = normalizedDeg a := by
  have hKL : (0 : ℝ) < Module.finrank K L := by exact_mod_cast Module.finrank_pos
  have htow : (Module.finrank ℚ K : ℝ) * Module.finrank K L = Module.finrank ℚ L := by
    exact_mod_cast Module.finrank_mul_finrank ℚ K L
  rw [normalizedDeg, normalizedDeg, degPb_degF_pullback, ← htow]
  field_simp

/-! ## Log-different and log-conductor under field extension -/

open IUT.VojtaNumberField

/-- The fiber identity behind the invariance at a finite place, in the form used below:
`∑_{w | v} e(w|v)·log q_w = [L : K]·log q_v`. -/
theorem degPb_sum_ramificationIdx_log (v : HeightOneSpectrum (𝓞 K)) :
    ∑ q : v.asIdeal.primesOver (𝓞 L),
        (q.1.ramificationIdx (𝓞 K) : ℝ) * Real.log (Ideal.absNorm q.1) =
      Module.finrank K L * Real.log (Ideal.absNorm v.asIdeal) := by
  have h := degPb_degF_single_inl L v
  simp only [degPbSingle, map_sum, degF_single, degWeight, degPbPrimeOf] at h
  rw [← h]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- **The transitivity formula for the log-different**: `log-diff_L = log-diff_K +
(1/[L : ℚ])·log N(𝔇_{L/K})`, where `𝔇_{L/K}` is the relative different ideal of `𝓞 L` over
`𝓞 K`. From Mathlib's `|d_L| = N(𝔇_{L/K})·|d_K|^{[L : K]}`. -/
theorem degPb_logDiffNF_tower :
    logDiffNF L = logDiffNF K +
      Real.log (Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L))) / Module.finrank ℚ L := by
  have hd := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  have hcK : ((discr K).natAbs : ℝ) = |(discr K : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hcL : ((discr L).natAbs : ℝ) = |(discr L : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hdK : (0 : ℝ) < |(discr K : ℝ)| := by
    rw [← hcK]; exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero K)
  have hrel : (0 : ℝ) < Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr differentIdeal_ne_bot)
  have hlog : Real.log |(discr L : ℝ)| =
      Real.log (Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L))) +
        Module.finrank K L * Real.log |(discr K : ℝ)| := by
    rw [← hcL, hd, Nat.cast_mul, Nat.cast_pow, hcK, Real.log_mul hrel.ne'
      (pow_pos hdK _).ne', Real.log_pow]
  have hKL : (0 : ℝ) < Module.finrank K L := by exact_mod_cast Module.finrank_pos
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have htow : (Module.finrank ℚ K : ℝ) * Module.finrank K L = Module.finrank ℚ L := by
    exact_mod_cast Module.finrank_mul_finrank ℚ K L
  rw [logDiffNF_eq, logDiffNF_eq, hlog, ← htow]
  field_simp
  ring

/-- For the primes `w` of `𝓞 L` over the primes of a finite set `S` of primes of `𝓞 K`,
`∑ (e(w|v) - 1)·log q_w ≤ log N(𝔇_{L/K})`: the ideal `∏ w^{e(w|v) - 1}` divides the relative
different. -/
theorem degPb_sum_ramification_sub_one_le (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∑ v ∈ S, ∑ q : v.asIdeal.primesOver (𝓞 L),
        ((q.1.ramificationIdx (𝓞 K) : ℝ) - 1) * Real.log (Ideal.absNorm q.1) ≤
      Real.log (Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L))) := by
  classical
  set D := differentIdeal (𝓞 K) (𝓞 L)
  let ι := Σ v : HeightOneSpectrum (𝓞 K), v.asIdeal.primesOver (𝓞 L)
  let s : Finset ι := S.sigma fun _ => Finset.univ
  let f : ι → Ideal (𝓞 L) := fun i => i.2.1
  let n : ι → ℕ := fun i => i.2.1.ramificationIdx (𝓞 K) - 1
  have hprime : ∀ i ∈ s, Prime (f i) := fun i _ =>
    Ideal.prime_of_isPrime (degPbPrimeOf L i.1 i.2).ne_bot i.2.2.1
  have hinj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i ≠ f j := by
    rintro ⟨v, q⟩ - ⟨v', q'⟩ - hne heq
    apply hne
    have hq := q.2.2
    have hq' := q'.2.2
    simp only [f] at heq
    have hvv : v = v' := by
      ext1
      rw [Ideal.over_def q.1 v.asIdeal, Ideal.over_def q'.1 v'.asIdeal, heq]
    subst hvv
    have : q = q' := Subtype.ext heq
    subst this
    rfl
  have hdvd : ∀ i ∈ s, f i ^ n i ∣ D := by
    rintro ⟨v, q⟩ -
    have : v.asIdeal.IsMaximal := v.isMaximal
    have := q.2.1
    have := q.2.2
    have hpS : v.asIdeal.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ :=
      Ideal.map_ne_bot_of_ne_bot v.ne_bot
    have h : q.1 ^ (q.1.ramificationIdx (𝓞 K)) ∣ v.asIdeal.map (algebraMap (𝓞 K) (𝓞 L)) := by
      rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity v.asIdeal q.1 hpS]
      exact pow_multiplicity_dvd _ _
    exact pow_sub_one_dvd_differentIdeal_aux (𝓞 K) K L q.1 v.ne_bot h
  have hcop : (s : Set ι).Pairwise (Function.onFun IsCoprime fun i => f i ^ n i) := by
    intro i hi j hj hij
    have := (degPbPrimeOf L i.1 i.2).isMaximal
    have := (degPbPrimeOf L j.1 j.2).isMaximal
    exact (Ideal.isCoprime_of_isMaximal (hinj i hi j hj hij)).pow
  have hJ : (∏ i ∈ s, f i ^ n i) ∣ D := Finset.prod_dvd_of_coprime hcop hdvd
  have hD0 : D ≠ ⊥ := differentIdeal_ne_bot
  have hnorm : Ideal.absNorm (∏ i ∈ s, f i ^ n i) ≤ Ideal.absNorm D :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD0))
      (map_dvd Ideal.absNorm hJ)
  have hpos : ∀ i ∈ s, (0 : ℝ) < Ideal.absNorm (f i) := fun i hi => by
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (hprime i hi).ne_zero)
  have hlogprod : Real.log (Ideal.absNorm (∏ i ∈ s, f i ^ n i)) =
      ∑ i ∈ s, (n i : ℝ) * Real.log (Ideal.absNorm (f i)) := by
    rw [map_prod, Nat.cast_prod, Real.log_prod (fun i hi => ?_)]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_pow, Nat.cast_pow, Real.log_pow]
    · rw [map_pow, Nat.cast_pow]; exact (pow_pos (hpos i hi) _).ne'
  have hsum : ∑ v ∈ S, ∑ q : v.asIdeal.primesOver (𝓞 L),
      ((q.1.ramificationIdx (𝓞 K) : ℝ) - 1) * Real.log (Ideal.absNorm q.1) =
      ∑ i ∈ s, (n i : ℝ) * Real.log (Ideal.absNorm (f i)) := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun q _ => ?_
    have := q.2.1
    have := q.2.2
    have he := Ideal.ramificationIdx_pos_of_isDedekindDomain' q.1 v.ne_bot
    simp only [n, f]
    rw [Nat.cast_sub he, Nat.cast_one]
  rw [hsum, ← hlogprod]
  have hP0 : (0 : ℝ) < Ideal.absNorm (∏ i ∈ s, f i ^ n i) := by
    have hJ0 : (∏ i ∈ s, f i ^ n i) ≠ ⊥ := by
      rw [← Submodule.zero_eq_bot]
      exact Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hprime i hi).ne_zero
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ0)
  exact Real.log_le_log hP0 (by exact_mod_cast hnorm)

/-- **Monotonicity of log-different plus log-conductor, for a conductor pulled back from `K`.**
For a finite set `S` of primes of `𝓞 K`, with normalized degree `(1/[K : ℚ])∑_{v ∈ S} log q_v`,
and the reduced divisor of `L` supported on the primes over `S`, with normalized degree
`(1/[L : ℚ])∑_{v ∈ S} ∑_{w | v} log q_w`: `log-diff_K + log-cond_K ≤ log-diff_L + log-cond_L`.
The relative different `𝔇_{L/K}`, which is divisible by `w^{e(w|v) - 1}`, compensates the loss
`∑ (e(w|v) - 1)·log q_w` of the reduced conductor. -/
theorem degPb_logDiff_add_cond_le (S : Finset (HeightOneSpectrum (𝓞 K))) :
    logDiffNF K + (∑ v ∈ S, Real.log (Ideal.absNorm v.asIdeal)) / Module.finrank ℚ K ≤
      logDiffNF L + (∑ v ∈ S, ∑ q : v.asIdeal.primesOver (𝓞 L),
        Real.log (Ideal.absNorm q.1)) / Module.finrank ℚ L := by
  have hKL : (0 : ℝ) < Module.finrank K L := by exact_mod_cast Module.finrank_pos
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have htow : (Module.finrank ℚ K : ℝ) * Module.finrank K L = Module.finrank ℚ L := by
    exact_mod_cast Module.finrank_mul_finrank ℚ K L
  have hfib : (Module.finrank K L : ℝ) * ∑ v ∈ S, Real.log (Ideal.absNorm v.asIdeal) =
      ∑ v ∈ S, ∑ q : v.asIdeal.primesOver (𝓞 L),
        (q.1.ramificationIdx (𝓞 K) : ℝ) * Real.log (Ideal.absNorm q.1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => (degPb_sum_ramificationIdx_log L v).symm
  have hb := degPb_sum_ramification_sub_one_le L S
  have hsplit : ∑ v ∈ S, ∑ q : v.asIdeal.primesOver (𝓞 L),
        (q.1.ramificationIdx (𝓞 K) : ℝ) * Real.log (Ideal.absNorm q.1) =
      ∑ v ∈ S, ∑ q : v.asIdeal.primesOver (𝓞 L),
        ((q.1.ramificationIdx (𝓞 K) : ℝ) - 1) * Real.log (Ideal.absNorm q.1) +
      ∑ v ∈ S, ∑ q : v.asIdeal.primesOver (𝓞 L), Real.log (Ideal.absNorm q.1) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [degPb_logDiffNF_tower (K := K) L, ← htow]
  set A := ∑ v ∈ S, Real.log (Ideal.absNorm v.asIdeal)
  set B := ∑ v ∈ S, ∑ q : v.asIdeal.primesOver (𝓞 L), Real.log (Ideal.absNorm q.1)
  set C := ∑ v ∈ S, ∑ q : v.asIdeal.primesOver (𝓞 L),
        ((q.1.ramificationIdx (𝓞 K) : ℝ) - 1) * Real.log (Ideal.absNorm q.1)
  set R := Real.log (Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)))
  have key : (Module.finrank K L : ℝ) * A ≤ R + B := by linarith
  have hA : A / Module.finrank ℚ K =
      Module.finrank K L * A / (Module.finrank ℚ K * Module.finrank K L) := by
    field_simp
  have h2 : (Module.finrank K L : ℝ) * A / (Module.finrank ℚ K * Module.finrank K L) ≤
      (R + B) / (Module.finrank ℚ K * Module.finrank K L) :=
    div_le_div_of_nonneg_right key (mul_pos hK hKL).le
  rw [add_div] at h2
  linarith

/-! ## The log-conductor of a point of `ℙ¹ \ {0, 1, ∞}` under field extension -/

omit [NumberField K] [NumberField L] in
/-- The prime of `𝓞 K` below `degPbPrimeOf L v q` is `v`. -/
theorem degPb_under_primeOf (v : HeightOneSpectrum (𝓞 K)) (q : v.asIdeal.primesOver (𝓞 L)) :
    HeightOneSpectrum.under (𝓞 K) (degPbPrimeOf L v q) = v := by
  have := q.2.2
  ext1
  rw [HeightOneSpectrum.under_asIdeal]
  exact (Ideal.over_def q.1 v.asIdeal).symm

omit [NumberField K] [NumberField L] in
theorem degPb_primeOf_injective (v : HeightOneSpectrum (𝓞 K)) :
    Function.Injective (degPbPrimeOf L v) := fun _ _ h =>
  Subtype.ext (congrArg HeightOneSpectrum.asIdeal h)

/-- A valuation of `ℤᵐ⁰` whose `n`-th power is `1`, for `n ≠ 0`, is `1`. -/
theorem degPb_pow_eq_one_iff {a : WithZero (Multiplicative ℤ)} {n : ℕ} (hn : n ≠ 0) :
    a ^ n = 1 ↔ a = 1 := by
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (pow_lt_one₀ zero_le hlt hn).ne h
    · exact (one_lt_pow₀ hgt hn).ne' h
  · rintro rfl
    exact one_pow n

/-- **The conductor pulls back.** A point `y ∈ K` of `ℙ¹` meets `{0, 1, ∞}` at a prime `w` of
`𝓞 L` exactly when it meets it at the prime of `𝓞 K` below `w`: the valuations satisfy
`v_w(y) = e(w|v)·v_v(y)`. -/
theorem degPb_meetsBoundaryAt_iff (w : HeightOneSpectrum (𝓞 L)) (y : K) :
    MeetsBoundaryAt L w (algebraMap K L y) ↔
      MeetsBoundaryAt K (HeightOneSpectrum.under (𝓞 K) w) y := by
  set v := HeightOneSpectrum.under (𝓞 K) w
  have : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have he : w.asIdeal.ramificationIdx (𝓞 K) ≠ 0 :=
    (Ideal.ramificationIdx_pos_of_isDedekindDomain' w.asIdeal v.ne_bot).ne'
  have key : ∀ x : K, w.valuation L (algebraMap K L x) = 1 ↔ v.valuation K x = 1 := by
    intro x
    rw [← HeightOneSpectrum.valuation_liesOver L v w x, degPb_pow_eq_one_iff he]
  rw [meetsBoundaryAt_iff_valuation, meetsBoundaryAt_iff_valuation,
    show algebraMap K L y - 1 = algebraMap K L (y - 1) by rw [map_sub, map_one],
    Ne, Ne, Ne, Ne, key, key]

theorem degPb_card_quot {F : Type*} [Field F] [NumberField F] (I : Ideal (𝓞 F)) :
    (Nat.card (𝓞 F ⧸ I) : ℝ) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

/-- For `x ≠ 0`, `v(x) ≠ 1` for only finitely many primes `v` of `𝓞 K`. -/
theorem degPb_valuation_ne_one_finite {x : K} (hx : x ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | v.valuation K x ≠ 1}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 K) x).union
    (HeightOneSpectrum.Support.finite (𝓞 K) x⁻¹)).subset ?_
  intro v hne
  have hx0 : v.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine Or.inr ?_
    show 1 < v.valuation K x⁻¹
    rw [map_inv₀]
    exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr hx0, hlt⟩
  · exact Or.inl hgt

/-- **The conductor of a point of `ℙ¹ \ {0, 1, ∞}` is finite**: for `y ∉ {0, 1}` only finitely
many primes of `𝓞 K` meet the boundary at `y`. -/
theorem degPb_meetsBoundaryAt_finite {y : K} (hy0 : y ≠ 0) (hy1 : y ≠ 1) :
    {v : HeightOneSpectrum (𝓞 K) | MeetsBoundaryAt K v y}.Finite := by
  refine ((degPb_valuation_ne_one_finite hy0).union
    (degPb_valuation_ne_one_finite (sub_ne_zero.mpr hy1))).subset ?_
  intro v hv
  exact (meetsBoundaryAt_iff_valuation K v y).mp hv

/-- **Monotonicity of `log-diff + log-cond` for a point of `ℙ¹ \ {0, 1, ∞}`.** For a finite
extension `L` of `K` and `y ∈ K` off the boundary (`y ≠ 0`, `y ≠ 1`; `y ≠ ∞` holds since
`y ∈ K`): `log-diff_K + log-cond_K(y) ≤ log-diff_L + log-cond_L(y)`, in the normalization of
`IUT.VojtaNumberField` (both evaluated at the field given, not at the minimal field of
definition of `y`). The hypotheses make the conductor finite
(`degPb_meetsBoundaryAt_finite`), so both log-conductors are finite sums. -/
theorem degPb_logDiffNF_add_logCondNF_le {y : K} (hy0 : y ≠ 0) (hy1 : y ≠ 1) :
    logDiffNF K + logCondNF K y ≤ logDiffNF L + logCondNF L (algebraMap K L y) := by
  set gK : HeightOneSpectrum (𝓞 K) → ℝ := fun v =>
    if MeetsBoundaryAt K v y then Real.log (Nat.card (𝓞 K ⧸ v.asIdeal)) else 0 with hgK
  set gL : HeightOneSpectrum (𝓞 L) → ℝ := fun w =>
    if MeetsBoundaryAt L w (algebraMap K L y) then Real.log (Nat.card (𝓞 L ⧸ w.asIdeal))
    else 0 with hgL
  have hK : logCondNF K y = (∑ᶠ v, gK v) / Module.finrank ℚ K := rfl
  have hL : logCondNF L (algebraMap K L y) = (∑ᶠ w, gL w) / Module.finrank ℚ L := rfl
  have hfin : (Function.support gK).Finite := by
    refine (degPb_meetsBoundaryAt_finite hy0 hy1).subset fun v hv => ?_
    by_contra h
    exact hv (by simp only [gK, show ¬MeetsBoundaryAt K v y from h, ↓reduceIte])
  set S := hfin.toFinset
  have hmeet : ∀ v ∈ S, MeetsBoundaryAt K v y := by
    intro v hv
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hv
    by_contra h
    exact hv (by simp only [gK, h, ↓reduceIte])
  have hKsum : ∑ᶠ v, gK v = ∑ v ∈ S, Real.log (Ideal.absNorm v.asIdeal) := by
    rw [finsum_eq_sum_of_support_subset gK (s := S) fun v hv => hfin.mem_toFinset.mpr hv]
    refine Finset.sum_congr rfl fun v hv => ?_
    simp only [gK, ite_eq_left (hmeet v hv), degPb_card_quot]
  set T := S.biUnion fun v => Finset.univ.image (degPbPrimeOf L v)
  have hsub : Function.support gL ⊆ ↑T := by
    intro w hw
    rw [Function.mem_support] at hw
    have hm : MeetsBoundaryAt L w (algebraMap K L y) := by
      by_contra h
      exact hw (by simp only [gL, h, ↓reduceIte])
    have hv : HeightOneSpectrum.under (𝓞 K) w ∈ S := by
      rw [Set.Finite.mem_toFinset, Function.mem_support]
      simp only [gK, ite_eq_left ((degPb_meetsBoundaryAt_iff L w y).mp hm), degPb_card_quot]
      exact (Real.log_pos (by exact_mod_cast
        HeightOneSpectrum.one_lt_absNorm (HeightOneSpectrum.under (𝓞 K) w))).ne'
    rw [Finset.coe_biUnion]
    refine Set.mem_iUnion₂.mpr ⟨_, hv, ?_⟩
    rw [Finset.coe_image]
    refine ⟨⟨w.asIdeal, w.isPrime, ⟨rfl⟩⟩, Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩
  have hLsum : ∑ᶠ w, gL w =
      ∑ v ∈ S, ∑ q : v.asIdeal.primesOver (𝓞 L), Real.log (Ideal.absNorm q.1) := by
    rw [finsum_eq_sum_of_support_subset gL hsub, Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun v hv => ?_
      rw [Finset.sum_image fun q _ q' _ h => degPb_primeOf_injective L v h]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hm : MeetsBoundaryAt L (degPbPrimeOf L v q) (algebraMap K L y) := by
        rw [degPb_meetsBoundaryAt_iff, degPb_under_primeOf]
        exact hmeet v hv
      simp only [gL, ite_eq_left hm, degPb_card_quot]
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
  rw [hK, hL, hKsum, hLsum]
  exact degPb_logDiff_add_cond_le L S

/-! ## Principal arithmetic divisors and the product formula -/

/-- `ord_v(x)`, the order of `x ∈ K` at the prime `v` of `𝓞 K`, normalized so that a generator
of the maximal ideal of the localization at `v` has order `1`. Mathlib's `v`-adic valuation of
`x` is `exp(-ord_v(x))`, so `ord_v(x) = -log(v(x))` with `WithZero.log`. -/
noncomputable def degPbOrd (v : HeightOneSpectrum (𝓞 K)) (x : K) : ℤ :=
  -WithZero.log (v.valuation K x)

/-- For `x ≠ 0`, `ord_v(x) ≠ 0` for only finitely many `v`. -/
theorem degPbOrd_finite {x : K} (hx : x ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | degPbOrd v x ≠ 0}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 K) x).union
    (HeightOneSpectrum.Support.finite (𝓞 K) x⁻¹)).subset ?_
  intro v hv
  have hx0 : v.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have hne : v.valuation K x ≠ 1 := by
    intro h
    apply hv
    simp [degPbOrd, h]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine Or.inr ?_
    show 1 < v.valuation K x⁻¹
    rw [map_inv₀]
    exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr hx0, hlt⟩
  · exact Or.inl hgt

/-- The coefficients of the principal arithmetic divisor of `x`: `ord_v(x)` at a finite place
and `-[K_v : ℝ]·log|x|_v` at an archimedean place `v`, with `[K_v : ℝ] = InfinitePlace.mult v`. -/
noncomputable def degPbPrincipalCoeff (x : K) : Valuations K → ℝ
  | .inl v => (degPbOrd v x : ℝ)
  | .inr w => -((w.mult : ℝ) * Real.log (w x))

theorem degPbPrincipalCoeff_support_finite {x : K} (hx : x ≠ 0) :
    (Function.support (degPbPrincipalCoeff x)).Finite := by
  refine (((degPbOrd_finite hx).image Sum.inl).union
    (Set.finite_range (Sum.inr : InfinitePlace K → Valuations K))).subset ?_
  rintro (v | w) hv
  · refine Or.inl ⟨v, ?_, rfl⟩
    rw [Function.mem_support] at hv
    intro h0
    apply hv
    simp only [degPbPrincipalCoeff]
    exact_mod_cast h0
  · exact Or.inr ⟨w, rfl⟩

/-- **The principal arithmetic divisor** of `x ∈ K^×`, as printed in [GenEll], page 4:
`ADiv(x) = ∑_{v finite} ord_v(x)·v - ∑_{v archimedean} [K_v : ℝ]·log(|x|_v)·v`. -/
noncomputable def degPbPrincipal (x : Kˣ) : ADiv K :=
  Finsupp.ofSupportFinite (degPbPrincipalCoeff (x : K))
    (degPbPrincipalCoeff_support_finite x.ne_zero)

/-- The `v`-adic absolute value of `x ≠ 0` (the finite place attached to `v`) is
`q_v^{-ord_v(x)}`, so its logarithm is `-ord_v(x)·log q_v`. -/
theorem degPb_log_finitePlace {x : K} (hx : x ≠ 0) (v : HeightOneSpectrum (𝓞 K)) :
    Real.log (FinitePlace.mk v x) = -(degPbOrd v x : ℝ) * Real.log (Ideal.absNorm v.asIdeal) := by
  have hx0 : v.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding',
    WithZeroMulInt.toNNReal_neg_apply _ hx0, NNReal.coe_zpow, NNReal.coe_natCast, Real.log_zpow,
    degPbOrd, Int.cast_neg, neg_neg]

theorem degPb_finitePlace_pos {x : K} (hx : x ≠ 0) (v : HeightOneSpectrum (𝓞 K)) :
    0 < FinitePlace.mk v x := by
  have hx0 : v.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have hN : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    have h := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
    exact_mod_cast h
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding',
    WithZeroMulInt.toNNReal_neg_apply _ hx0, NNReal.coe_zpow, NNReal.coe_natCast]
  exact zpow_pos hN _

/-- **The degree of a principal arithmetic divisor is zero** (the product formula), in the
convention of [GenEll] page 4: weight `log q_v` at a finite place, weight `1` at an
archimedean place, coefficient `-[K_v : ℝ]·log|x|_v` at an archimedean place. -/
theorem degPb_degF_principal (x : Kˣ) : degF (degPbPrincipal x) = 0 := by
  have hx : (x : K) ≠ 0 := x.ne_zero
  set T := (degPbOrd_finite hx).toFinset
  have hsupp : (degPbPrincipal x).support ⊆ T.disjSum Finset.univ := by
    intro t ht
    rw [Finsupp.mem_support_iff] at ht
    rcases t with v | w
    · rw [Finset.inl_mem_disjSum, Set.Finite.mem_toFinset]
      intro h0
      apply ht
      simp only [degPbPrincipal, Finsupp.ofSupportFinite_coe, degPbPrincipalCoeff]
      exact_mod_cast h0
    · exact Finset.inr_mem_disjSum.mpr (Finset.mem_univ _)
  rw [degF_apply, Finsupp.sum_of_support_subset _ hsupp _ (fun _ _ => mul_zero _),
    Finset.sum_disjSum]
  simp only [degPbPrincipal, Finsupp.ofSupportFinite_coe, degPbPrincipalCoeff, degWeight,
    one_mul]
  -- the finite part
  have hfin : ∑ v ∈ T, Real.log (Ideal.absNorm v.asIdeal) * (degPbOrd v (x : K) : ℝ) =
      -Real.log (∏ᶠ w : FinitePlace K, w x) := by
    have hfp : ∏ᶠ w : FinitePlace K, w x =
        ∏ᶠ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v (x : K) := by
      rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
      rfl
    have hsub : Function.support (fun v : HeightOneSpectrum (𝓞 K) =>
        Real.log (FinitePlace.mk v (x : K))) ⊆ ↑T := by
      intro v hv
      rw [Function.mem_support, degPb_log_finitePlace hx] at hv
      rw [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      intro h0
      apply hv
      rw [h0]
      simp
    rw [hfp, Real.log_finprod (degPb_finitePlace_pos hx),
      finsum_eq_sum_of_support_subset _ hsub, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [degPb_log_finitePlace hx]
    ring
  -- the archimedean part
  have hpf := prod_abs_eq_one hx
  have hP : ∏ᶠ w : FinitePlace K, w (x : K) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hpf
    exact zero_ne_one hpf
  have hI : ∏ w : InfinitePlace K, w (x : K) ^ w.mult ≠ 0 := by
    intro h
    rw [h, zero_mul] at hpf
    exact zero_ne_one hpf
  have hlog := congrArg Real.log hpf
  rw [Real.log_one, Real.log_mul hI hP,
    Real.log_prod (fun w _ => pow_ne_zero _ (InfinitePlace.pos_iff.mpr hx).ne')] at hlog
  simp only [Real.log_pow] at hlog
  rw [hfin, Finset.sum_neg_distrib]
  linarith

/-! ## The pull-back of a principal divisor is principal -/

/-- `ord_w(x) = e(w|v)·ord_v(x)` for `x ∈ K` and a prime `w` of `𝓞 L` over `v`. -/
theorem degPb_ord_algebraMap (w : HeightOneSpectrum (𝓞 L)) (x : K) :
    degPbOrd w (algebraMap K L x) =
      w.asIdeal.ramificationIdx (𝓞 K) * degPbOrd (HeightOneSpectrum.under (𝓞 K) w) x := by
  have : w.asIdeal.LiesOver (HeightOneSpectrum.under (𝓞 K) w).asIdeal := ⟨rfl⟩
  rw [degPbOrd, degPbOrd,
    ← HeightOneSpectrum.valuation_liesOver L (HeightOneSpectrum.under (𝓞 K) w) w x,
    WithZero.log_pow, nsmul_eq_mul]
  ring

omit [NumberField K] [NumberField L] in
/-- `[K_v : ℝ]·[L_w : K_v] = [L_w : ℝ]` for an archimedean place `w` of `L` over `v`. -/
theorem degPb_mult_mul_inertiaDeg (w : InfinitePlace L) :
    (w.comap (algebraMap K L)).mult * (w.comap (algebraMap K L)).inertiaDeg w = w.mult := by
  have hw : w.LiesOver (w.comap (algebraMap K L)) := ⟨rfl⟩
  rcases w.isUnramified_or_isRamified K with h | h
  · rw [InfinitePlace.inertiaDeg_eq_one ⟨hw, h⟩, mul_one, h.eq]
  · rw [InfinitePlace.inertiaDeg_eq_two ⟨hw, h⟩, h.isReal.mult_eq_one,
      h.isComplex.mult_eq_two]

/-- **The pull-back of a principal divisor is the principal divisor of the image**:
`ADiv(x)|_L = ADiv(x)` for `x ∈ K^×` viewed in `L^×`. This checks the multipliers of
`degPbPullback` against the principal divisors of [GenEll] page 4, independently of the
degree. -/
theorem degPb_pullback_principal (x : Kˣ) :
    degPbPullback L (degPbPrincipal x) =
      degPbPrincipal (Units.map (algebraMap K L).toMonoidHom x) := by
  ext t
  rcases t with w | w
  · rw [degPbPullback_apply_inl]
    simp only [degPbPrincipal, Finsupp.ofSupportFinite_coe, degPbPrincipalCoeff, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
    rw [degPb_ord_algebraMap]
    push_cast
    ring
  · rw [degPbPullback_apply_inr]
    simp only [degPbPrincipal, Finsupp.ofSupportFinite_coe, degPbPrincipalCoeff, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
    rw [InfinitePlace.comap_apply, ← degPb_mult_mul_inertiaDeg (K := K) L w]
    push_cast
    ring

end IUT.PaperIV.DegreePullback
