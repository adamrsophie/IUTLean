import IUT.PaperIV.LegendreFrey

/-!
# Reduction of the Frey curve of a triple at the odd primes

Sources.

* Mochizuki, *Inter-universal Teichmüller Theory IV*, Corollary 2.2 and the beginning of its
  proof (pages 41 to 43). Page 41 regards `X = ℙ¹_ℚ` minus `{0, 1, ∞}` as the `λ`-line of the
  Legendre form `y² = x(x - 1)(x - λ)`, and Corollary 2.2 (i) introduces `log(q^∀)` and
  `log(q^{∤2})`, the normalized degrees of the arithmetic divisors cut out by the `q`-parameters
  of an elliptic curve over a number field at all nonarchimedean primes, respectively at those
  not dividing `2`. Page 42 uses that `E_F` has stable reduction at every nonarchimedean prime of
  `F`, and condition (C2) and page 43 use `log-cond_D(x_E)` and `log(f^{F_tpd})`.
* Silverman's standard facts on minimal models and reduction types, as encoded in Mathlib's
  `Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean`.

Pages read for this file: IUT IV pages 41 to 43. Pages checked against rendered images: IUT IV
pages 41 to 43.

**What is and is not taken from the paper.** The pages read do not mention a triple, the Frey
curve, its reduction at odd primes, or the relation `v(q) = -v(j)`. They use the `q`-parameters
and the conductor of curves over number fields. This file checks the classical arithmetic that
lies behind these invariants for the rational points of the `λ`-line coming from coprime
triples `a + b = c`, through the Frey curve `y² = x(x - a)(x + b)` (a quadratic twist of the
Legendre curve, `IUT.LegendreFrey.freyCurve_variableChange_legendre`). The Legendre model at
`λ` itself is not treated here: minimality, the reduction type and the discriminant change
under a quadratic twist (a twist ramified at an odd prime turns multiplicative into additive
reduction), and only the `j`-invariant is shared by the two curves.

**What this file proves.** Let `a + b = c` be positive and coprime, `p` an odd prime, and `W`
the Frey model `IUT.LegendreFrey.freyCurve a b` base changed from `ℤ` to `ℚ_[p]`. Valuations
are those of Mathlib's reduction API for the discrete valuation ring `ℤ_[p]`, with values in
`ℤᵐ⁰` (multiplicative: the additive valuation `n` corresponds to `exp (-n)`).

1. A general minimality criterion over any discrete valuation ring: an integral Weierstrass
   equation whose `Δ` or `c₄` is a unit is minimal (`freyRed_isMinimal_of_val`); two minimal
   equations related by a change of variables have discriminants of equal valuation
   (`freyRed_val_Δ_eq_of_isMinimal`).
2. `W` is integral and minimal at `p` (`freyRedModel_isMinimal`).
3. `HasGoodReduction ℤ_[p] W ↔ ¬ p ∣ abc` and `HasMultiplicativeReduction ℤ_[p] W ↔ p ∣ abc`;
   the reduction is never additive.
4. `v(Δ) = exp (-2 v_p(abc))`, also for every minimal model of `W`, and, when `p ∣ abc`,
   `v(j) = exp (2 v_p(abc))`, that is `v_p(j) = -2 v_p(abc)`. Here `v_p` is Mathlib's
   `multiplicity p` on natural numbers (equal to `padicValNat p` by `Nat.padicValNat_def`).
5. The set of odd primes at which `W` has multiplicative reduction is the set of odd prime
   factors of `abc`, and twice the product of these primes is `Challenge.rad (abc)` (`abc` is
   always even).
6. At `p = 2`: `W` over `ℤ_[2]` has neither good nor multiplicative reduction in Mathlib's sense
   (both `Δ` and `c₄` are divisible by `16`), and for the triple `3 + 16 = 19` the model is not
   minimal at `2` (an explicit change of variables with `u = 2` keeps it integral).

**Not proved.**

* The relation `v(q) = -v(j)` between the Tate parameter and the `j`-invariant at a prime of
  multiplicative reduction: it needs Tate uniformization, and Mathlib has no Tate curve and no
  `q`-parameter.
* The conductor exponent: Mathlib defines no conductor of an elliptic curve. Item 5 is stated
  with `HasMultiplicativeReduction` and `Challenge.rad` instead; the statement "the conductor
  exponent at an odd prime of multiplicative reduction is `1`" is not formalized.
* The minimal model, the minimal discriminant and the reduction type at `2` for a general
  triple; only the single non-minimal example above is proved.
* Anything over a number field other than `ℚ`, the stable reduction of `E_F` over `F`, and every
  assertion of Corollary 2.2.
-/

namespace IUT.FreyReduction

open WeierstrassCurve IUT.LegendreFrey

/-! ## A minimality criterion over a discrete valuation ring -/

section Criterion

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The valuation of an integral Weierstrass equation transformed by a change of variables that
keeps it integral is at most `1` on `c₄` and `Δ`. -/
private theorem freyRed_val_le_one_of_integral (W : WeierstrassCurve K) [IsIntegral R W] :
    (IsDiscreteValuationRing.maximalIdeal R).valuation K W.c₄ ≤ 1 ∧
      (IsDiscreteValuationRing.maximalIdeal R).valuation K W.Δ ≤ 1 := by
  refine ⟨?_, ?_⟩
  · rw [← integralModel_c₄_eq R W]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _
  · rw [← integralModel_Δ_eq R W]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _

/-- **Minimality criterion.** Over the fraction field `K` of a discrete valuation ring `R`, an
integral Weierstrass equation whose discriminant or whose `c₄` has valuation `1` (is a unit of
`R`) is minimal in the sense of `WeierstrassCurve.IsMinimal`. If `v(c₄) = 1`, a change of
variables with `u` of positive valuation would make `c₄' = u⁻⁴ c₄` non-integral; if `v(Δ) = 1`,
no integral model has a discriminant of larger multiplicative valuation. -/
theorem freyRed_isMinimal_of_val (W : WeierstrassCurve K) [IsIntegral R W]
    (h : (IsDiscreteValuationRing.maximalIdeal R).valuation K W.Δ = 1 ∨
      (IsDiscreteValuationRing.maximalIdeal R).valuation K W.c₄ = 1) :
    IsMinimal R W := by
  refine ⟨⟨by show IsIntegral R ((1 : VariableChange K) • W); rw [one_smul]; infer_instance,
    ?_⟩⟩
  intro C hC _
  have := hC
  show valuation_Δ_aux R (C • W) ≤ valuation_Δ_aux R ((1 : VariableChange K) • W)
  rw [← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral, one_smul,
    valuation_Δ_aux_eq_of_isIntegral]
  rcases h with hΔ | hc
  · rw [hΔ]
    exact (freyRed_val_le_one_of_integral (R := R) (C • W)).2
  · have h4 := (freyRed_val_le_one_of_integral (R := R) (C • W)).1
    rw [variableChange_c₄, map_mul, hc, mul_one, map_pow,
      pow_le_one_iff (by norm_num : (4 : ℕ) ≠ 0)] at h4
    rw [variableChange_Δ, map_mul, map_pow]
    exact mul_le_of_le_one_left zero_le (pow_le_one' h4 12)

/-- Two minimal Weierstrass equations related by a change of variables have discriminants of
the same valuation. -/
theorem freyRed_val_Δ_eq_of_isMinimal (W : WeierstrassCurve K) (C : VariableChange K)
    [hW : IsMinimal R W] [hCW : IsMinimal R (C • W)] :
    (IsDiscreteValuationRing.maximalIdeal R).valuation K (C • W).Δ =
      (IsDiscreteValuationRing.maximalIdeal R).valuation K W.Δ := by
  have key : ∀ (W' : WeierstrassCurve K) (C' : VariableChange K) [IsMinimal R W']
      [IsIntegral R (C' • W')],
      (IsDiscreteValuationRing.maximalIdeal R).valuation K (C' • W').Δ ≤
        (IsDiscreteValuationRing.maximalIdeal R).valuation K W'.Δ := by
    intro W' C' hW' hC'
    have hmax := hW'.val_Δ_maximal
    have hle : valuation_Δ_aux R (C' • W') ≤ valuation_Δ_aux R ((1 : VariableChange K) • W') := by
      rcases le_total (valuation_Δ_aux R (C' • W'))
        (valuation_Δ_aux R ((1 : VariableChange K) • W')) with h | h
      · exact h
      · exact hmax.2 hC' h
    rw [← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral, one_smul,
      valuation_Δ_aux_eq_of_isIntegral] at hle
    exact hle
  have : IsIntegral R (C⁻¹ • C • W) := by rw [inv_smul_smul]; infer_instance
  refine le_antisymm (key W C) ?_
  have := key (C • W) C⁻¹
  rwa [inv_smul_smul] at this

end Criterion

/-! ## The `p`-adic valuation on natural numbers -/

section Padic

variable {p : ℕ} [hp : Fact p.Prime]

/-- The valuation of `ℚ_[p]` used by Mathlib's reduction API for the discrete valuation ring
`ℤ_[p]`: the adic valuation of its maximal ideal, with values in `ℤᵐ⁰`. -/
noncomputable abbrev freyRedVal (p : ℕ) [Fact p.Prime] :
    Valuation ℚ_[p] (WithZero (Multiplicative ℤ)) :=
  (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation ℚ_[p]

/-- A natural number has valuation `1` in `ℚ_[p]` exactly when `p` does not divide it. -/
theorem freyRedVal_natCast_eq_one_iff (n : ℕ) : freyRedVal p (n : ℚ_[p]) = 1 ↔ ¬ p ∣ n := by
  rw [← map_natCast (algebraMap ℤ_[p] ℚ_[p]),
    IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
  show (n : ℤ_[p]) ∉ IsLocalRing.maximalIdeal ℤ_[p] ↔ _
  rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_natCast_lt_one_iff]

/-- The prime `p` is a uniformizer: its valuation is `exp (-1)`. -/
theorem freyRedVal_p : freyRedVal p (p : ℚ_[p]) = WithZero.exp (-1 : ℤ) := by
  rw [← map_natCast (algebraMap ℤ_[p] ℚ_[p]),
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _
    (by exact_mod_cast hp.out.ne_zero) PadicInt.maximalIdeal_eq_span_p

/-- The valuation of a nonzero natural number in `ℚ_[p]` is `exp (-v_p(n))`. -/
theorem freyRedVal_natCast (n : ℕ) (hn : n ≠ 0) :
    freyRedVal p (n : ℚ_[p]) = WithZero.exp (-(multiplicity p n : ℤ)) := by
  have e := Nat.ordProj_mul_ordCompl_eq_self n p
  have hm : ¬ p ∣ n / p ^ n.factorization p := Nat.not_dvd_ordCompl hp.out hn
  conv_lhs => rw [← e]
  rw [Nat.cast_mul, map_mul, (freyRedVal_natCast_eq_one_iff _).mpr hm, mul_one,
    Nat.cast_pow, map_pow, freyRedVal_p, Nat.factorization_def n hp.out, ← WithZero.exp_nsmul]
  congr 1
  simp

end Padic

/-! ## The Frey model over `ℚ_[p]` -/

section Frey

variable {p : ℕ} [hp : Fact p.Prime]

/-- The Frey curve `y² = x(x - a)(x + b)` of a pair of natural numbers, as the base change to
`ℚ_[p]` of the integral model `IUT.LegendreFrey.freyCurve (a : ℤ) b` over `ℤ`. -/
noncomputable def freyRedModel (p : ℕ) [Fact p.Prime] (a b : ℕ) : WeierstrassCurve ℚ_[p] :=
  (freyCurve (a : ℤ) b).map (Int.castRingHom ℚ_[p])

/-- The Frey model over `ℚ_[p]` is integral over `ℤ_[p]`: it is the base change of the Frey
model over `ℤ_[p]`. -/
theorem freyRedModel_isIntegral (a b : ℕ) : IsIntegral ℤ_[p] (freyRedModel p a b) :=
  ⟨⟨(freyCurve (a : ℤ) b).map (Int.castRingHom ℤ_[p]), by
    rw [freyRedModel, baseChange, map_map]
    congr 1⟩⟩

/-- The discriminant of the Frey model is the natural number `16 (abc)²`. -/
theorem freyRedModel_Δ {a b c : ℕ} (h : a + b = c) :
    (freyRedModel p a b).Δ = ((16 * (a * b * c) ^ 2 : ℕ) : ℚ_[p]) := by
  subst h
  rw [freyRedModel, map_Δ, freyCurve_disc, eq_intCast]
  push_cast
  ring

/-- The invariant `c₄` of the Frey model is the natural number `16 (a² + ab + b²)`. -/
theorem freyRedModel_c₄ (a b : ℕ) :
    (freyRedModel p a b).c₄ = ((16 * (a ^ 2 + a * b + b ^ 2) : ℕ) : ℚ_[p]) := by
  rw [freyRedModel, map_c₄, freyCurve_c4, eq_intCast]
  push_cast
  ring

/-- An odd prime divides `16 m` exactly when it divides `m`. -/
private theorem freyRed_dvd_sixteen_mul_iff (hp2 : p ≠ 2) (m : ℕ) : p ∣ 16 * m ↔ p ∣ m := by
  refine ⟨fun hd => ?_, fun hd => hd.mul_left _⟩
  rcases (Nat.Prime.dvd_mul hp.out).mp hd with h16 | hm
  · have : p ∣ 2 ^ 4 := by simpa using h16
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp
      (hp.out.dvd_of_dvd_pow this)) hp2
  · exact hm

/-- At an odd prime, the discriminant of the Frey model has valuation `1` exactly when `p` does
not divide `abc`. -/
theorem freyRedModel_val_Δ_eq_one_iff {a b c : ℕ} (h : a + b = c) (hp2 : p ≠ 2) :
    freyRedVal p (freyRedModel p a b).Δ = 1 ↔ ¬ p ∣ a * b * c := by
  rw [freyRedModel_Δ h, freyRedVal_natCast_eq_one_iff, freyRed_dvd_sixteen_mul_iff hp2]
  exact not_congr ⟨hp.out.dvd_of_dvd_pow, fun hd => dvd_pow hd two_ne_zero⟩

/-- For a coprime pair, at an odd prime dividing `abc`, the invariant `c₄` of the Frey model is a
unit of `ℤ_[p]`. -/
theorem freyRedModel_val_c₄_eq_one {a b c : ℕ} (hab : a.Coprime b) (h : a + b = c)
    (hp2 : p ≠ 2) (hd : p ∣ a * b * c) : freyRedVal p (freyRedModel p a b).c₄ = 1 := by
  rw [freyRedModel_c₄, freyRedVal_natCast_eq_one_iff, freyRed_dvd_sixteen_mul_iff hp2]
  intro hN
  subst h
  have := Nat.dvd_gcd hN hd
  rw [freyNorm_coprime hab] at this
  exact hp.out.one_lt.ne' (Nat.dvd_one.mp this)

/-- **Minimality at odd primes.** For a coprime pair `a + b = c` and an odd prime `p`, the Frey
model is a minimal Weierstrass equation over `ℤ_[p]`: if `p ∤ abc` its discriminant is a unit;
if `p ∣ abc` its `c₄` is a unit. -/
theorem freyRedModel_isMinimal {a b c : ℕ} (hab : a.Coprime b) (h : a + b = c)
    (hp2 : p ≠ 2) : IsMinimal ℤ_[p] (freyRedModel p a b) := by
  have := freyRedModel_isIntegral (p := p) a b
  refine freyRed_isMinimal_of_val _ ?_
  by_cases hd : p ∣ a * b * c
  · exact Or.inr (freyRedModel_val_c₄_eq_one hab h hp2 hd)
  · exact Or.inl ((freyRedModel_val_Δ_eq_one_iff h hp2).mpr hd)

/-- **Good reduction.** For a coprime pair `a + b = c` and an odd prime `p`, the Frey model has
good reduction at `p` (in the sense of `WeierstrassCurve.HasGoodReduction`) exactly when `p`
does not divide `abc`. -/
theorem freyRedModel_hasGoodReduction_iff {a b c : ℕ} (hab : a.Coprime b) (h : a + b = c)
    (hp2 : p ≠ 2) : HasGoodReduction ℤ_[p] (freyRedModel p a b) ↔ ¬ p ∣ a * b * c := by
  rw [hasGoodReduction_iff, ← freyRedModel_val_Δ_eq_one_iff h hp2]
  exact and_iff_right (freyRedModel_isMinimal hab h hp2)

/-- **Multiplicative reduction.** For a coprime pair `a + b = c` and an odd prime `p`, the Frey
model has multiplicative reduction at `p` (in the sense of
`WeierstrassCurve.HasMultiplicativeReduction`) exactly when `p` divides `abc`. -/
theorem freyRedModel_hasMultiplicativeReduction_iff {a b c : ℕ} (hab : a.Coprime b)
    (h : a + b = c) (hp2 : p ≠ 2) :
    HasMultiplicativeReduction ℤ_[p] (freyRedModel p a b) ↔ p ∣ a * b * c := by
  rw [hasMultiplicativeReduction_iff]
  have := freyRedModel_isIntegral (p := p) a b
  have hle := (freyRed_val_le_one_of_integral (R := ℤ_[p]) (freyRedModel p a b)).2
  constructor
  · rintro ⟨-, hlt, -⟩
    by_contra hd
    exact hlt.ne ((freyRedModel_val_Δ_eq_one_iff h hp2).mpr hd)
  · intro hd
    refine ⟨freyRedModel_isMinimal hab h hp2, lt_of_le_of_ne hle fun he => ?_,
      freyRedModel_val_c₄_eq_one hab h hp2 hd⟩
    exact (freyRedModel_val_Δ_eq_one_iff h hp2).mp he hd

/-- The reduction of the Frey model at an odd prime is never additive. -/
theorem freyRedModel_not_hasAdditiveReduction {a b c : ℕ} (hab : a.Coprime b)
    (h : a + b = c) (hp2 : p ≠ 2) : ¬ HasAdditiveReduction ℤ_[p] (freyRedModel p a b) := by
  intro hA
  by_cases hd : p ∣ a * b * c
  · exact HasAdditiveReduction.not_hasMultiplicativeReduction (R := ℤ_[p]) hA
      ((freyRedModel_hasMultiplicativeReduction_iff hab h hp2).mpr hd)
  · exact HasGoodReduction.not_hasAdditiveReduction (R := ℤ_[p])
      ((freyRedModel_hasGoodReduction_iff hab h hp2).mpr hd) hA

/-- **Valuation of the discriminant.** For positive `a`, `b` with `a + b = c` and an odd prime
`p`, the discriminant of the Frey model has valuation `exp (-2 v_p(abc))`: additively,
`v_p(Δ) = 2 v_p(abc)`. -/
theorem freyRedModel_val_Δ {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a + b = c)
    (hp2 : p ≠ 2) :
    freyRedVal p (freyRedModel p a b).Δ =
      WithZero.exp (-(2 * multiplicity p (a * b * c) : ℤ)) := by
  have hc : 0 < c := by omega
  have habc : a * b * c ≠ 0 := by positivity
  rw [freyRedModel_Δ h, freyRedVal_natCast _ (by positivity),
    Nat.multiplicity_mul (by norm_num) (by positivity), Nat.multiplicity_pow,
    multiplicity_eq_zero_of_not_dvd (fun hd => ?_)]
  · push_cast; ring_nf
  · have : p ∣ 2 ^ 4 := by simpa using hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp
      (hp.out.dvd_of_dvd_pow this))

/-- **Valuation of the minimal discriminant.** For a coprime pair of positive numbers
`a + b = c` and an odd prime `p`, every minimal Weierstrass equation over `ℤ_[p]` isomorphic to
the Frey model (by a change of variables over `ℚ_[p]`) has discriminant of valuation
`exp (-2 v_p(abc))`. -/
theorem freyRedModel_val_minimal_Δ {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : a + b = c) (hp2 : p ≠ 2) (C : VariableChange ℚ_[p])
    [IsMinimal ℤ_[p] (C • freyRedModel p a b)] :
    freyRedVal p (C • freyRedModel p a b).Δ =
      WithZero.exp (-(2 * multiplicity p (a * b * c) : ℤ)) := by
  have := freyRedModel_isMinimal (p := p) hab h hp2
  rw [freyRed_val_Δ_eq_of_isMinimal (R := ℤ_[p]), freyRedModel_val_Δ ha hb h hp2]

/-- For positive `a`, `b`, the Frey model over `ℚ_[p]` is an elliptic curve. -/
theorem freyRedModel_isElliptic {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (freyRedModel p a b).IsElliptic := by
  rw [isElliptic_iff, freyRedModel_Δ rfl, isUnit_iff_ne_zero, Nat.cast_ne_zero]
  positivity

/-- **Valuation of `j`.** For a coprime pair of positive numbers `a + b = c` and an odd prime `p`
dividing `abc`, the `j`-invariant of the Frey model has valuation `exp (2 v_p(abc))`:
additively, `v_p(j) = -2 v_p(abc)`. (The ellipticity instance is supplied by
`freyRedModel_isElliptic`.) -/
theorem freyRedModel_val_j {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : a + b = c) (hp2 : p ≠ 2) (hd : p ∣ a * b * c) [(freyRedModel p a b).IsElliptic] :
    freyRedVal p (freyRedModel p a b).j =
      WithZero.exp ((2 * multiplicity p (a * b * c) : ℕ) : ℤ) := by
  rw [j_eq, map_mul, map_inv₀, map_pow, freyRedModel_val_c₄_eq_one hab h hp2 hd, one_pow,
    mul_one, freyRedModel_val_Δ ha hb h hp2, ← WithZero.exp_neg, neg_neg]
  push_cast
  rfl

end Frey

/-! ## The odd primes of multiplicative reduction and the radical -/

section Radical

/-- The prime `p` is odd and the Frey model of `(a, b)` has multiplicative reduction at `p`, in
the sense of `WeierstrassCurve.HasMultiplicativeReduction` over `ℤ_[p]`. -/
def freyRedOddMultPrime (a b p : ℕ) : Prop :=
  ∃ hp : p.Prime, p ≠ 2 ∧
    letI : Fact p.Prime := ⟨hp⟩
    HasMultiplicativeReduction ℤ_[p] (freyRedModel p a b)

/-- For a coprime pair of positive numbers `a + b = c`, the odd primes of multiplicative
reduction of the Frey model are the odd prime factors of `abc`. -/
theorem freyRedOddMultPrime_iff {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : a + b = c) (p : ℕ) :
    freyRedOddMultPrime a b p ↔ p ∈ (a * b * c).primeFactors ∧ p ≠ 2 := by
  have hc : 0 < c := by omega
  have habc : a * b * c ≠ 0 := by positivity
  rw [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hp2, hM⟩
    have : Fact p.Prime := ⟨hp⟩
    exact ⟨⟨hp, (freyRedModel_hasMultiplicativeReduction_iff hab h hp2).mp hM, habc⟩, hp2⟩
  · rintro ⟨⟨hp, hd, -⟩, hp2⟩
    have : Fact p.Prime := ⟨hp⟩
    exact ⟨hp, hp2, (freyRedModel_hasMultiplicativeReduction_iff hab h hp2).mpr hd⟩

/-- For a coprime pair `a + b = c`, the product `abc` is even. -/
theorem freyRed_two_dvd {a b c : ℕ} (h : a + b = c) : 2 ∣ a * b * c := by
  subst h
  rcases Nat.even_or_odd a with ha | ha
  · exact (ha.two_dvd.mul_right _).mul_right _
  rcases Nat.even_or_odd b with hb | hb
  · exact (hb.two_dvd.mul_left _).mul_right _
  · exact (ha.add_odd hb).two_dvd.mul_left _

/-- **The odd part of the radical.** For a coprime pair of positive numbers `a + b = c`, the set
of odd primes at which the Frey model has multiplicative reduction is the set of odd prime
factors of `abc`, and twice the product of these primes is `rad(abc)`. -/
theorem freyRed_oddMultPrimes_rad {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : a + b = c) :
    {p | freyRedOddMultPrime a b p} = ↑((a * b * c).primeFactors.erase 2) ∧
      2 * ∏ p ∈ (a * b * c).primeFactors.erase 2, p = Challenge.rad (a * b * c) := by
  have hc : 0 < c := by omega
  have habc : a * b * c ≠ 0 := by positivity
  refine ⟨?_, ?_⟩
  · ext p
    simp only [Set.mem_ofPred_eq, Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe,
      Set.mem_singleton_iff, freyRedOddMultPrime_iff ha hb hab h]
  · rw [Challenge.rad]
    exact Finset.mul_prod_erase _ (fun p => p)
      (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, freyRed_two_dvd h, habc⟩)

end Radical

/-! ## The prime `2` -/

section Two

/-- At the prime `2`, the Frey model (an integral equation over `ℤ_[2]`, minimal or not) is
neither of good nor of multiplicative reduction in the sense of Mathlib: both `Δ = 16(abc)²` and
`c₄ = 16(a² + ab + b²)` lie in the maximal ideal. -/
theorem freyRedModel_two_not_good_not_mult {a b c : ℕ} (h : a + b = c) :
    ¬ HasGoodReduction ℤ_[2] (freyRedModel 2 a b) ∧
      ¬ HasMultiplicativeReduction ℤ_[2] (freyRedModel 2 a b) := by
  refine ⟨fun hG => ?_, fun hM => ?_⟩
  · have := hG.goodReduction
    rw [freyRedModel_Δ h] at this
    exact ((freyRedVal_natCast_eq_one_iff (p := 2) _).mp this) (dvd_mul_of_dvd_left (by norm_num) _)
  · have := hM.multiplicativeReduction
    rw [freyRedModel_c₄] at this
    exact ((freyRedVal_natCast_eq_one_iff (p := 2) _).mp this) (dvd_mul_of_dvd_left (by norm_num) _)

/-- **The model is not minimal at `2` in general.** For the coprime triple `3 + 16 = 19`, the
Frey model `y² = x(x - 3)(x + 16)` is not a minimal Weierstrass equation over `ℤ_[2]`: the
change of variables `x = 4x'`, `y = 8y' + 4x'` (`u = 2`, `r = t = 0`, `s = 1`) carries it to the
integral equation `y'² + x'y' = x'³ + 3x'² - 3x'`, whose discriminant is `2⁻¹²Δ`. -/
theorem freyRedModel_two_not_isMinimal : ¬ IsMinimal ℤ_[2] (freyRedModel 2 3 16) := by
  intro hmin
  set C : VariableChange ℚ_[2] := ⟨Units.mk0 2 two_ne_zero, 0, 1, 0⟩ with hCdef
  have hC : C • freyRedModel 2 3 16 =
      (⟨1, 3, 0, -3, 0⟩ : WeierstrassCurve ℤ).map (Int.castRingHom ℚ_[2]) := by
    ext <;> simp [hCdef, variableChange_def, freyRedModel, freyCurve, map] <;> norm_num
  have hI : IsIntegral ℤ_[2] (C • freyRedModel 2 3 16) :=
    ⟨⟨(⟨1, 3, 0, -3, 0⟩ : WeierstrassCurve ℤ).map (Int.castRingHom ℤ_[2]), by
      rw [hC, baseChange, map_map]
      congr 1⟩⟩
  have := freyRedModel_isIntegral (p := 2) 3 16
  have hv : freyRedVal 2 (freyRedModel 2 3 16).Δ =
      WithZero.exp (-(multiplicity 2 (16 * (3 * 16 * 19) ^ 2) : ℤ)) := by
    rw [freyRedModel_Δ (by norm_num : 3 + 16 = 19)]
    exact freyRedVal_natCast _ (by norm_num)
  have hu : freyRedVal 2 ((C.u⁻¹ : ℚ_[2]ˣ) : ℚ_[2]) = WithZero.exp 1 := by
    simp only [hCdef, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀]
    rw [show (2 : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) by norm_num, freyRedVal_p]
    rfl
  have hΔC : freyRedVal 2 (C • freyRedModel 2 3 16).Δ =
      WithZero.exp (12 + -(multiplicity 2 (16 * (3 * 16 * 19) ^ 2) : ℤ)) := by
    rw [variableChange_Δ, map_mul, map_pow, hu, hv, WithZero.exp_add, ← WithZero.exp_nsmul]
    norm_num
  have hle : valuation_Δ_aux ℤ_[2] ((1 : VariableChange ℚ_[2]) • freyRedModel 2 3 16) ≤
      valuation_Δ_aux ℤ_[2] (C • freyRedModel 2 3 16) := by
    rw [one_smul, ← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral,
      valuation_Δ_aux_eq_of_isIntegral]
    change freyRedVal 2 _ ≤ freyRedVal 2 _
    rw [hΔC, hv, WithZero.exp_le_exp]
    omega
  have hge := hmin.val_Δ_maximal.2 hI hle
  change valuation_Δ_aux ℤ_[2] (C • freyRedModel 2 3 16) ≤
      valuation_Δ_aux ℤ_[2] ((1 : VariableChange ℚ_[2]) • freyRedModel 2 3 16) at hge
  rw [one_smul, ← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral,
    valuation_Δ_aux_eq_of_isIntegral] at hge
  change freyRedVal 2 _ ≤ freyRedVal 2 _ at hge
  rw [hΔC, hv, WithZero.exp_le_exp] at hge
  omega

end Two

end IUT.FreyReduction
