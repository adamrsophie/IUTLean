import IUT.Applications.ABCSpecialization

/-!
# The Legendre curve, the Frey curve of a triple, and the `j`-invariant on the `λ`-line

Sources.

* Mochizuki, *Inter-universal Teichmüller Theory IV*: Proposition 1.8 (vi) (statement on
  page 19, proof on pages 20 and 21), which descends an elliptic curve with rational 2-torsion
  to a curve in Legendre form after a possibly trivial quadratic twist; Theorem 1.10 (page 22),
  which uses the model in Legendre form over the tripodal field; Corollary 2.2 (page 41), which
  regards `X = ℙ¹_ℚ` minus `{0, 1, ∞}` as the `λ`-line of the Legendre form
  `y² = x(x - 1)(x - λ)` with its classifying morphism to the moduli stack of elliptic curves;
  the proof of Corollary 2.2 (i) (page 43), which uses that the pullback to `X` of the divisor
  at infinity of the compactified moduli stack has degree 6 to get the equality of bounded
  discrepancy classes `(1/6)·ht_∞ ≈ ht_{ω_X(D)}`, and the proof of Corollary 2.2 (ii)
  (page 43), which excludes the points with one of "four possibilities for the `j`-invariant";
  Corollary 2.3 and its proof (pages 54 and 55).
* Mochizuki, Fesenko, Hoshi, Minamide, Porowski, *Explicit estimates in inter-universal
  Teichmüller theory*, Proposition 2.1 (page 21), which lists these four values:
  `2¹⁴·31³·5⁻³`, `2²·73³·3⁻⁴`, `2⁶·3³ = 1728` and `0`.

Pages read for this file: IUT IV pages 16 to 22, 41 to 43, 45, 54 to 56; Explicit estimates
page 21. Pages checked against rendered images: IUT IV pages 18 to 22, 41 to 43, 45, 54 to 56;
Explicit estimates page 21.

**What is and is not taken from the papers.** IUT IV does not print the formula for the
`j`-invariant of the Legendre form, does not use the `S₃`-symmetry of the `λ`-line on the pages
read (page 41 introduces the `λ`-line without it), and does not attach a point of the `λ`-line
to an abc triple: the proof of Corollary 2.3 (pages 54 and 55) reduces to [GenEll], Theorem 2.1,
and works with arbitrary points of a compactly bounded subset. The formulas below are computed
here from Mathlib's definitions of `WeierstrassCurve.Δ`, `WeierstrassCurve.c₄` and
`WeierstrassCurve.j`, not transcribed. For a triple `a + b = c` this file uses the point
`λ = a / c` of `IUT.ABCSpecialization` (the point used there to compare Corollary 2.3 with the
abc conjecture); the Frey curve `y² = x(x - a)(x + b)` is the quadratic twist by `a` of the
Legendre curve at `λ = -b / a = 1 - c / a`, which lies in the same `S₃`-orbit as `a / c`, so
both normalizations give the same `j`-invariant (`legendreJ_neg_div_eq`).

**What this file proves.**

1. `legendreCurve t` is `y² = x(x - 1)(x - t)` as a `WeierstrassCurve`; `Δ = 16 t²(t - 1)²`,
   `c₄ = 16(t² - t + 1)`; over a field with `2 ≠ 0` it is elliptic exactly when `t ≠ 0, 1`,
   and then its `j` is `legendreJ t = 2⁸(t² - t + 1)³ / (t²(t - 1)²)`.
2. `legendreJ` is invariant under `t ↦ 1 - t` and `t ↦ t⁻¹` for every `t` (with Lean's
   convention `x / 0 = 0` at `t = 0, 1`), hence on the orbit
   `{t, 1 - t, t⁻¹, (1 - t)⁻¹, (t - 1)/t, t/(t - 1)}`.
3. `freyCurve a b` is `y² = x(x - a)(x + b)`; `Δ = 16 a²b²(a + b)²`, `c₄ = 16(a² + ab + b²)`,
   `j = 2⁸(a² + ab + b²)³ / (a²b²(a + b)²) = legendreJ (a / (a + b))`; a change of variables
   with `u² = a` carries it to `legendreCurve (-b / a)`.
4. For positive coprime natural numbers `a + b = c`, with `N = a² + ab + b²`: `N` is odd and
   coprime to `abc`; the rational number `j = legendreJ (a / c)` has denominator dividing
   `(abc)²` and divisible by `(abc)² / 2⁸`, its numerator is divisible by `N³` and divides
   `2⁸N³`, and an odd prime divides its denominator exactly when it divides `abc`. For the
   integral Frey model over `ℤ`, an odd prime divides `Δ` exactly when it divides `abc`, and
   then it does not divide `c₄`. The statement fails at `2`: the triple `1 + 1 = 2` gives
   `j = 1728`.
5. The four special values: `j = 1728` exactly at `t ∈ {-1, 2, 1/2}`; `j = 2²·73³·3⁻⁴` exactly
   at `t ∈ {9, -8, 9/8, -1/8, 8/9, 1/9}` (the triple `1 + 8 = 9` gives this value);
   `j = 2¹⁴·31³·5⁻³` exactly at the roots of three quadratics with discriminant `5·55²`, none
   rational; `j = 0` exactly at the roots of `t² - t + 1`, none rational. Each statement assumes
   `t ≠ 0, 1` and characteristic zero.
6. Height comparison for triples: `6 h(λ) - log(64/27) ≤ h(j(λ)) ≤ 6 h(λ) + 8 log 2` for
   `λ = a / c`, with `h = Height.logHeight₁`. This is an explicit form, on the points of
   triples, of the degree-6 comparison behind `(1/6)·ht_∞ ≈ ht_{ω_X(D)}` (page 43); the
   identification of `ht_∞` and `ht_{ω_X(D)}` with these Weil heights is not formalized. A
   uniform form over number fields is in `IUT/Applications/HeightComparison.lean`.

**What Mathlib has and lacks.** Mathlib has `WeierstrassCurve` with `b₂ … b₈`, `c₄`, `c₆`,
`Δ`, `IsElliptic`, `j`, variable changes and their action, models with given `j` (`ofJ`), the
isomorphism of curves with equal `j` over a separably closed field, and, over the fraction
field of a discrete valuation ring, integral and minimal models with `HasGoodReduction`,
`HasMultiplicativeReduction`, `HasAdditiveReduction` and `HasSplitMultiplicativeReduction`.
It lacks Tate curves, `q`-parameters, conductors and semistable reduction after extension.
Minimality of the Frey model at odd primes, its multiplicative reduction at the odd primes
dividing `abc` and the valuation of `j` there are proved in `IUT/PaperIV/FreyReduction.lean`,
from the arithmetic of `Δ` and `c₄` of item 4; the relation `v(q) = -v(j)` needs Tate curves
and is not proved.
-/

namespace IUT.LegendreFrey

open WeierstrassCurve

/-! ## The two Weierstrass curves -/

section Curves

variable {R : Type*} [CommRing R]

/-- The Legendre curve `y² = x(x - 1)(x - t) = x³ - (1 + t)x² + t x` as a Weierstrass curve. -/
def legendreCurve (t : R) : WeierstrassCurve R :=
  ⟨0, -(1 + t), 0, t, 0⟩

/-- The discriminant of the Legendre curve is `16 t²(t - 1)²`. -/
theorem legendreCurve_disc (t : R) : (legendreCurve t).Δ = 16 * t ^ 2 * (t - 1) ^ 2 := by
  simp only [legendreCurve, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]; ring

/-- The invariant `c₄` of the Legendre curve is `16(t² - t + 1)`. -/
theorem legendreCurve_c4 (t : R) : (legendreCurve t).c₄ = 16 * (t ^ 2 - t + 1) := by
  simp only [legendreCurve, WeierstrassCurve.c₄, b₂, b₄]; ring

/-- The Frey curve `y² = x(x - a)(x + b) = x³ + (b - a)x² - ab x` of a pair `a`, `b`. -/
def freyCurve (a b : R) : WeierstrassCurve R :=
  ⟨0, b - a, 0, -(a * b), 0⟩

/-- The discriminant of the Frey curve is `16 a²b²(a + b)²`. -/
theorem freyCurve_disc (a b : R) :
    (freyCurve a b).Δ = 16 * a ^ 2 * b ^ 2 * (a + b) ^ 2 := by
  simp only [freyCurve, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]; ring

/-- The invariant `c₄` of the Frey curve is `16(a² + ab + b²)`. -/
theorem freyCurve_c4 (a b : R) : (freyCurve a b).c₄ = 16 * (a ^ 2 + a * b + b ^ 2) := by
  simp only [freyCurve, WeierstrassCurve.c₄, b₂, b₄]; ring

end Curves

/-! ## Over a field: ellipticity and the `j`-invariant -/

section Field

variable {K : Type*} [Field K]

private theorem sixteen_ne_zero_of_two (h2 : (2 : K) ≠ 0) : (16 : K) ≠ 0 := by
  have : (16 : K) = 2 ^ 4 := by norm_num
  rw [this]; exact pow_ne_zero _ h2

/-- Over a field with `2 ≠ 0`, the Legendre curve is elliptic exactly when `t ≠ 0` and
`t ≠ 1`. -/
theorem legendreCurve_isElliptic_iff (h2 : (2 : K) ≠ 0) (t : K) :
    (legendreCurve t).IsElliptic ↔ t ≠ 0 ∧ t ≠ 1 := by
  rw [isElliptic_iff, legendreCurve_disc, isUnit_iff_ne_zero]
  simp [sixteen_ne_zero_of_two h2, sub_eq_zero]

/-- Over a field with `2 ≠ 0`, the Frey curve is elliptic exactly when `a`, `b` and `a + b` are
nonzero. -/
theorem freyCurve_isElliptic_iff (h2 : (2 : K) ≠ 0) (a b : K) :
    (freyCurve a b).IsElliptic ↔ a ≠ 0 ∧ b ≠ 0 ∧ a + b ≠ 0 := by
  rw [isElliptic_iff, freyCurve_disc, isUnit_iff_ne_zero]
  simp [sixteen_ne_zero_of_two h2, and_assoc]

/-- The `j`-function of the `λ`-line, `2⁸(t² - t + 1)³ / (t²(t - 1)²)`. With Lean's convention
`x / 0 = 0` its value at `t = 0` and `t = 1` is `0`; it is the `j`-invariant of the Legendre
curve only for `t ≠ 0, 1` (`legendreCurve_jInv`). -/
noncomputable def legendreJ (t : K) : K :=
  2 ^ 8 * (t ^ 2 - t + 1) ^ 3 / (t ^ 2 * (t - 1) ^ 2)

/-- The `j`-invariant of the Legendre curve, when it is elliptic, is `legendreJ t`. -/
theorem legendreCurve_jInv (t : K) [(legendreCurve t).IsElliptic] :
    (legendreCurve t).j = legendreJ t := by
  have h := (legendreCurve t).isUnit_Δ.ne_zero
  rw [legendreCurve_disc] at h
  rw [j_eq, legendreCurve_disc, legendreCurve_c4, legendreJ]
  have h16 : (16 : K) ≠ 0 := fun h0 => h (by rw [h0]; ring)
  have ht : t ≠ 0 := fun h0 => h (by rw [h0]; ring)
  have ht1 : t - 1 ≠ 0 := fun h0 => h (by rw [h0]; ring)
  field_simp
  ring

/-- The `j`-invariant of the Frey curve, when it is elliptic, is
`2⁸(a² + ab + b²)³ / (a²b²(a + b)²)`. -/
theorem freyCurve_jInv (a b : K) [(freyCurve a b).IsElliptic] :
    (freyCurve a b).j = 2 ^ 8 * (a ^ 2 + a * b + b ^ 2) ^ 3 / (a ^ 2 * b ^ 2 * (a + b) ^ 2) := by
  have h := (freyCurve a b).isUnit_Δ.ne_zero
  rw [freyCurve_disc] at h
  rw [j_eq, freyCurve_disc, freyCurve_c4]
  have h16 : (16 : K) ≠ 0 := fun h0 => h (by rw [h0]; ring)
  have ha : a ≠ 0 := fun h0 => h (by rw [h0]; ring)
  have hb : b ≠ 0 := fun h0 => h (by rw [h0]; ring)
  have hab : a + b ≠ 0 := fun h0 => h (by rw [h0]; ring)
  field_simp
  ring

/-- Invariance of the `j`-function under `t ↦ 1 - t`, for every `t`. -/
theorem legendreJ_one_sub (t : K) : legendreJ (1 - t) = legendreJ t := by
  unfold legendreJ
  congr 1 <;> ring

/-- Invariance of the `j`-function under `t ↦ t⁻¹`, for every `t`. -/
theorem legendreJ_inv (t : K) : legendreJ t⁻¹ = legendreJ t := by
  unfold legendreJ
  rcases eq_or_ne t 0 with rfl | h0
  · simp
  rcases eq_or_ne t 1 with rfl | h1
  · simp
  have h1' : t - 1 ≠ 0 := sub_ne_zero.mpr h1
  rw [div_eq_div_iff (by simp [h0, h1, inv_eq_zero, sub_eq_zero, inv_eq_one]) (by simp [h0, h1'])]
  field_simp
  ring

/-- Invariance of the `j`-function on the orbit of `t` under the group generated by
`t ↦ 1 - t` and `t ↦ t⁻¹`: the three remaining elements `(1 - t)⁻¹`, `(t - 1)/t` and
`t/(t - 1)`. -/
theorem legendreJ_orbit (t : K) (h0 : t ≠ 0) :
    legendreJ (1 - t)⁻¹ = legendreJ t ∧ legendreJ ((t - 1) / t) = legendreJ t ∧
      legendreJ (t / (t - 1)) = legendreJ t := by
  refine ⟨by rw [legendreJ_inv, legendreJ_one_sub], ?_, ?_⟩
  · have : (t - 1) / t = 1 - t⁻¹ := by field_simp
    rw [this, legendreJ_one_sub, legendreJ_inv]
  · rcases eq_or_ne t 1 with rfl | h1
    · simp [legendreJ]
    have h1' : t - 1 ≠ 0 := sub_ne_zero.mpr h1
    have : t / (t - 1) = 1 - (1 - t)⁻¹ := by
      have h1'' : 1 - t ≠ 0 := fun h => h1' (by linear_combination -h)
      field_simp
      ring
    rw [this, legendreJ_one_sub, legendreJ_inv, legendreJ_one_sub]

/-- The value of the `j`-function at the point `a / (a + b)` of a pair. -/
theorem legendreJ_div_add (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) :
    legendreJ (a / (a + b)) =
      2 ^ 8 * (a ^ 2 + a * b + b ^ 2) ^ 3 / (a ^ 2 * b ^ 2 * (a + b) ^ 2) := by
  unfold legendreJ
  have h1 : a / (a + b) - 1 = -b / (a + b) := by field_simp; ring
  rw [h1, div_eq_div_iff (by simp [ha, hb, hab]) (by simp [ha, hb, hab])]
  field_simp
  ring

/-- The two normalizations `-b / a` and `a / (a + b)` of a pair give the same value of the
`j`-function: `-b / a = 1 - (a + b) / a` and `(a + b) / a = (a / (a + b))⁻¹`. -/
theorem legendreJ_neg_div_eq (a b : K) (ha : a ≠ 0) :
    legendreJ (-b / a) = legendreJ (a / (a + b)) := by
  have : -b / a = 1 - (a / (a + b))⁻¹ := by
    rw [inv_div]; field_simp; ring
  rw [this, legendreJ_one_sub, legendreJ_inv]

/-- The `j`-invariant of an elliptic Frey curve is the value of the `j`-function at
`a / (a + b)`, and also at `-b / a`. -/
theorem freyCurve_jInv_eq_legendreJ (a b : K) [h : (freyCurve a b).IsElliptic] :
    (freyCurve a b).j = legendreJ (a / (a + b)) ∧ (freyCurve a b).j = legendreJ (-b / a) := by
  have hΔ := (freyCurve a b).isUnit_Δ.ne_zero
  rw [freyCurve_disc] at hΔ
  have ha : a ≠ 0 := fun h0 => hΔ (by rw [h0]; ring)
  have hb : b ≠ 0 := fun h0 => hΔ (by rw [h0]; ring)
  have hab : a + b ≠ 0 := fun h0 => hΔ (by rw [h0]; ring)
  rw [legendreJ_neg_div_eq a b ha, freyCurve_jInv, legendreJ_div_add a b ha hb hab]
  exact ⟨rfl, rfl⟩

/-- The Frey curve is the quadratic twist by `a` of the Legendre curve at `-b / a`: if
`u² = a`, the change of variables `(x, y) ↦ (u² x', u³ y')` carries `freyCurve a b` to
`legendreCurve (-b / a)`. -/
theorem freyCurve_variableChange_legendre (a b u : K) (hu : u ≠ 0) (h : u ^ 2 = a) :
    (⟨Units.mk0 u hu, 0, 0, 0⟩ : VariableChange K) • freyCurve a b = legendreCurve (-b / a) := by
  subst h
  ext <;> simp [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, freyCurve, legendreCurve] <;> field_simp
  ring

end Field

/-! ## Arithmetic of the `j`-invariant of a coprime triple -/

section Triple

/-- For coprime natural numbers `a`, `b`, the number `a² + ab + b²` is coprime to
`a b (a + b)`. -/
theorem freyNorm_coprime {a b : ℕ} (hab : a.Coprime b) :
    (a ^ 2 + a * b + b ^ 2).Coprime (a * b * (a + b)) := by
  rw [← Nat.isCoprime_iff_coprime]
  have h : IsCoprime (a : ℤ) b := Nat.isCoprime_iff_coprime.mpr hab
  push_cast
  refine IsCoprime.mul_right (IsCoprime.mul_right ?_ ?_) ?_
  · have := (h.symm.pow_left (m := 2)).add_mul_left_left ((a : ℤ) + b)
    convert this using 1; ring
  · have := (h.pow_left (m := 2)).add_mul_left_left ((a : ℤ) + b)
    convert this using 1; ring
  · have h1 : IsCoprime (a : ℤ) (a + b) := by
      have := h.add_mul_left_right 1; convert this using 1; ring
    have h2 : IsCoprime (b : ℤ) (a + b) := by
      have := h.symm.add_mul_left_right 1; convert this using 1; ring
    have := (IsCoprime.mul_left h1 h2).neg_left.add_mul_left_left ((a : ℤ) + b)
    convert this using 1; ring

/-- For coprime natural numbers `a`, `b`, the number `a² + ab + b²` is odd. -/
theorem freyNorm_odd {a b : ℕ} (hab : a.Coprime b) : Odd (a ^ 2 + a * b + b ^ 2) := by
  rw [Nat.odd_iff]
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb
  · exfalso
    have := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero ha) (Nat.dvd_of_mod_eq_zero hb)
    rw [hab] at this
    omega
  all_goals simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, ha, hb]

variable {a b c : ℕ}

/-- For a triple `a + b = c` of positive numbers, the `j`-function at `a / c` is
`2⁸(a² + ab + b²)³ / (abc)²`. -/
theorem legendreJ_triple_eq (ha : 0 < a) (hb : 0 < b) (h : a + b = c) :
    legendreJ ((a : ℚ) / c) =
      ((2 ^ 8 * (a ^ 2 + a * b + b ^ 2) ^ 3 : ℕ) : ℚ) / ((a * b * c) ^ 2 : ℕ) := by
  subst h
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hab' : (a : ℚ) + b ≠ 0 := by positivity
  push_cast
  rw [legendreJ_div_add _ _ ha' hb' hab']
  ring

/-- The numerator and denominator of the `j`-invariant of a coprime triple, up to a common
factor `k`: `(abc)² = den · k` and `|num| · k = 2⁸(a² + ab + b²)³`, with `k ∣ 2⁸`. -/
theorem legendreJ_triple_num_den (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : a + b = c) :
    ∃ k : ℕ, k ∣ 2 ^ 8 ∧ (a * b * c) ^ 2 = (legendreJ ((a : ℚ) / c)).den * k ∧
      (legendreJ ((a : ℚ) / c)).num.natAbs * k = 2 ^ 8 * (a ^ 2 + a * b + b ^ 2) ^ 3 := by
  set m : ℕ := 2 ^ 8 * (a ^ 2 + a * b + b ^ 2) ^ 3 with hm
  set n : ℕ := (a * b * c) ^ 2 with hn
  have hc : 0 < c := by omega
  have hn0 : (n : ℤ) ≠ 0 := by
    have : 0 < n := by positivity
    exact_mod_cast this.ne'
  obtain ⟨k, hk1, hk2⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den (m : ℤ) hn0
  have hq : legendreJ ((a : ℚ) / c) = ((m : ℤ) : ℚ) / ((n : ℤ) : ℚ) := by
    rw [legendreJ_triple_eq ha hb h, hm, hn, Int.cast_natCast, Int.cast_natCast]
  rw [← hq] at hk1 hk2
  have e1 : m = k.natAbs * (legendreJ ((a : ℚ) / c)).num.natAbs := by
    have := congrArg Int.natAbs hk1; rwa [Int.natAbs_mul, Int.natAbs_natCast] at this
  have e2 : n = k.natAbs * (legendreJ ((a : ℚ) / c)).den := by
    have := congrArg Int.natAbs hk2; rwa [Int.natAbs_mul, Int.natAbs_natCast,
      Int.natAbs_natCast] at this
  refine ⟨k.natAbs, ?_, by rw [e2]; ring, by rw [e1]; ring⟩
  have hcop : (k.natAbs).Coprime ((a ^ 2 + a * b + b ^ 2) ^ 3) := by
    have hN : ((a ^ 2 + a * b + b ^ 2) ^ 3).Coprime n := by
      rw [hn, ← h]
      exact ((freyNorm_coprime hab).pow 3 2)
    exact (hN.coprime_dvd_right ⟨_, by rw [e2]⟩).symm
  exact hcop.dvd_of_dvd_mul_right ⟨_, by rw [hm] at e1; rw [e1]⟩

/-- The denominator of the `j`-invariant of a coprime triple divides `(abc)²`. -/
theorem legendreJ_triple_den_dvd (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : a + b = c) : (legendreJ ((a : ℚ) / c)).den ∣ (a * b * c) ^ 2 := by
  obtain ⟨k, -, e, -⟩ := legendreJ_triple_num_den ha hb hab h
  exact ⟨k, e⟩

/-- The denominator of the `j`-invariant of a coprime triple is at least `(abc)² / 2⁸`:
`(abc)²` divides `2⁸ · den`. -/
theorem legendreJ_triple_sq_dvd (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : a + b = c) : (a * b * c) ^ 2 ∣ 2 ^ 8 * (legendreJ ((a : ℚ) / c)).den := by
  obtain ⟨k, hk, e, -⟩ := legendreJ_triple_num_den ha hb hab h
  rw [e, mul_comm (2 ^ 8)]
  exact Nat.mul_dvd_mul_left _ hk

/-- The numerator of the `j`-invariant of a coprime triple is divisible by `(a² + ab + b²)³`
and divides `2⁸(a² + ab + b²)³`. -/
theorem legendreJ_triple_num (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (h : a + b = c) :
    (a ^ 2 + a * b + b ^ 2) ^ 3 ∣ (legendreJ ((a : ℚ) / c)).num.natAbs ∧
      (legendreJ ((a : ℚ) / c)).num.natAbs ∣ 2 ^ 8 * (a ^ 2 + a * b + b ^ 2) ^ 3 := by
  obtain ⟨k, hk, e, e'⟩ := legendreJ_triple_num_den ha hb hab h
  refine ⟨?_, ⟨k, e'.symm⟩⟩
  have hcop : ((a ^ 2 + a * b + b ^ 2) ^ 3).Coprime k := by
    have hN : ((a ^ 2 + a * b + b ^ 2) ^ 3).Coprime ((a * b * c) ^ 2) := by
      rw [← h]; exact (freyNorm_coprime hab).pow 3 2
    exact hN.coprime_dvd_right ⟨_, by rw [e]; ring⟩
  exact hcop.dvd_of_dvd_mul_right ⟨2 ^ 8, by rw [e']; ring⟩

/-- An odd prime divides the denominator of the `j`-invariant of a coprime triple exactly when
it divides `abc`. -/
theorem legendreJ_triple_prime_dvd_den_iff (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : a + b = c) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p ∣ (legendreJ ((a : ℚ) / c)).den ↔ p ∣ a * b * c := by
  constructor
  · intro hd
    exact hp.dvd_of_dvd_pow (hd.trans (legendreJ_triple_den_dvd ha hb hab h))
  · intro hd
    have := (dvd_pow hd two_ne_zero).trans (legendreJ_triple_sq_dvd ha hb hab h)
    rcases (Nat.Prime.dvd_mul hp).mp this with h2 | h2
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow h2)) hp2
    · exact h2

/-- For the integral Frey model over `ℤ` of a coprime pair of natural numbers, an odd prime
divides the discriminant exactly when it divides `ab(a + b)`. -/
theorem freyCurve_prime_dvd_disc_iff {a b : ℕ} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (p : ℤ) ∣ (freyCurve (a : ℤ) b).Δ ↔ p ∣ a * b * (a + b) := by
  have e : (freyCurve (a : ℤ) b).Δ = ((16 * (a * b * (a + b)) ^ 2 : ℕ) : ℤ) := by
    rw [freyCurve_disc]; push_cast; ring
  rw [e, Int.natCast_dvd_natCast]
  constructor
  · intro hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h16 | h2
    · exfalso
      have : p ∣ 2 ^ 4 := by simpa using h16
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this))
    · exact hp.dvd_of_dvd_pow h2
  · intro hd
    exact Dvd.dvd.mul_left (dvd_pow hd two_ne_zero) _

/-- For the integral Frey model over `ℤ` of a coprime pair of natural numbers, an odd prime
dividing `ab(a + b)` does not divide `c₄`. -/
theorem freyCurve_prime_not_dvd_c4 {a b : ℕ} (hab : a.Coprime b) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hd : p ∣ a * b * (a + b)) : ¬ (p : ℤ) ∣ (freyCurve (a : ℤ) b).c₄ := by
  have e : (freyCurve (a : ℤ) b).c₄ = ((16 * (a ^ 2 + a * b + b ^ 2) : ℕ) : ℤ) := by
    rw [freyCurve_c4]; push_cast; ring
  rw [e, Int.natCast_dvd_natCast]
  intro h4
  rcases (Nat.Prime.dvd_mul hp).mp h4 with h16 | hN
  · have : p ∣ 2 ^ 4 := by simpa using h16
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this))
  · have := Nat.dvd_gcd hN hd
    rw [freyNorm_coprime hab] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-! ## Heights -/

/-- **Upper height bound.** For a coprime triple `a + b = c` of positive numbers and
`λ = a / c`, `h(j(λ)) ≤ 6 h(λ) + 8 log 2`, with `h = Height.logHeight₁`. -/
theorem logHeight₁_legendreJ_triple_le (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : a + b = c) :
    Height.logHeight₁ (legendreJ ((a : ℚ) / c)) ≤
      6 * Height.logHeight₁ ((a : ℚ) / c) + 8 * Real.log 2 := by
  obtain ⟨k, hk, e, e'⟩ := legendreJ_triple_num_den ha hb hab h
  rw [IUT.ABCSpecialization.logHeight₁_of_triple ha hb hab h, Rat.logHeight₁_eq_log_max]
  set q := legendreJ ((a : ℚ) / c)
  have hk0 : 0 < k := Nat.pos_of_dvd_of_pos hk (by norm_num)
  have hN : a ^ 2 + a * b + b ^ 2 ≤ c ^ 2 := by rw [← h]; nlinarith
  have habc : a * b * c ≤ c ^ 3 := by
    have : a * b ≤ c * c := Nat.mul_le_mul (by omega) (by omega)
    calc a * b * c ≤ c * c * c := Nat.mul_le_mul_right _ this
      _ = c ^ 3 := by ring
  have hnum : q.num.natAbs ≤ 2 ^ 8 * c ^ 6 := by
    calc q.num.natAbs ≤ q.num.natAbs * k := Nat.le_mul_of_pos_right _ hk0
      _ = 2 ^ 8 * (a ^ 2 + a * b + b ^ 2) ^ 3 := e'
      _ ≤ 2 ^ 8 * (c ^ 2) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN 3)
      _ = 2 ^ 8 * c ^ 6 := by ring
  have hden : q.den ≤ 2 ^ 8 * c ^ 6 := by
    calc q.den ≤ q.den * k := Nat.le_mul_of_pos_right _ hk0
      _ = (a * b * c) ^ 2 := e.symm
      _ ≤ (c ^ 3) ^ 2 := Nat.pow_le_pow_left habc 2
      _ ≤ 2 ^ 8 * c ^ 6 := by rw [← pow_mul]; exact Nat.le_mul_of_pos_left _ (by norm_num)
  have hmax : ((max q.num.natAbs q.den : ℕ) : ℝ) ≤ 2 ^ 8 * (c : ℝ) ^ 6 := by
    exact_mod_cast max_le hnum hden
  have hpos : (0 : ℝ) < ((max q.num.natAbs q.den : ℕ) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le q.pos (le_max_right _ _)
  have hc : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  calc Real.log ((max q.num.natAbs q.den : ℕ) : ℝ) ≤ Real.log (2 ^ 8 * (c : ℝ) ^ 6) :=
        Real.log_le_log hpos hmax
    _ = 6 * Real.log c + 8 * Real.log 2 := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
        push_cast; ring

/-- **Lower height bound.** For a coprime triple `a + b = c` of positive numbers and
`λ = a / c`, `6 h(λ) - log(64/27) ≤ h(j(λ))`, with `h = Height.logHeight₁`. -/
theorem le_logHeight₁_legendreJ_triple (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : a + b = c) :
    6 * Height.logHeight₁ ((a : ℚ) / c) - Real.log (64 / 27) ≤
      Height.logHeight₁ (legendreJ ((a : ℚ) / c)) := by
  obtain ⟨hdiv, -⟩ := legendreJ_triple_num ha hb hab h
  rw [IUT.ABCSpecialization.logHeight₁_of_triple ha hb hab h, Rat.logHeight₁_eq_log_max]
  set q := legendreJ ((a : ℚ) / c)
  have hN0 : 0 < a ^ 2 + a * b + b ^ 2 := by positivity
  have hnum0 : q.num.natAbs ≠ 0 := by
    intro h0
    have hq0 : q ≠ 0 := by
      show legendreJ ((a : ℚ) / c) ≠ 0
      rw [legendreJ_triple_eq ha hb h]
      have : 0 < (a * b * c) ^ 2 := by have : 0 < c := by omega
                                       positivity
      positivity
    exact hq0 (Rat.num_eq_zero.mp (Int.natAbs_eq_zero.mp h0))
  have hle : (a ^ 2 + a * b + b ^ 2) ^ 3 ≤ q.num.natAbs := Nat.le_of_dvd (by omega) hdiv
  have h4 : 3 * c ^ 2 ≤ 4 * (a ^ 2 + a * b + b ^ 2) := by
    rw [← h]; nlinarith [sq_nonneg ((a : ℤ) - b)]
  have h27 : 27 * c ^ 6 ≤ 64 * q.num.natAbs := by
    have := Nat.pow_le_pow_left h4 3
    calc 27 * c ^ 6 = (3 * c ^ 2) ^ 3 := by ring
      _ ≤ (4 * (a ^ 2 + a * b + b ^ 2)) ^ 3 := this
      _ = 64 * (a ^ 2 + a * b + b ^ 2) ^ 3 := by ring
      _ ≤ 64 * q.num.natAbs := Nat.mul_le_mul_left _ hle
  have hmax : 27 * (c : ℝ) ^ 6 ≤ 64 * ((max q.num.natAbs q.den : ℕ) : ℝ) := by
    have : 27 * c ^ 6 ≤ 64 * max q.num.natAbs q.den :=
      h27.trans (Nat.mul_le_mul_left _ (le_max_left _ _))
    exact_mod_cast this
  have hc : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  have hpos : (0 : ℝ) < ((max q.num.natAbs q.den : ℕ) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le q.pos (le_max_right _ _)
  have hlog := Real.log_le_log (by positivity) hmax
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num) hpos.ne',
    Real.log_pow] at hlog
  rw [Real.log_div (by norm_num) (by norm_num)]
  push_cast at hlog ⊢
  linarith

end Triple

/-! ## The four special values -/

section SpecialValues

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
private theorem legendreJ_eq_iff_aux (t j₀ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) :
    legendreJ t = j₀ ↔ 2 ^ 8 * (t ^ 2 - t + 1) ^ 3 - j₀ * (t ^ 2 * (t - 1) ^ 2) = 0 := by
  have h1' : t - 1 ≠ 0 := sub_ne_zero.mpr h1
  unfold legendreJ
  rw [div_eq_iff (by positivity), sub_eq_zero]

/-- `j = 2⁶·3³ = 1728` exactly at `t ∈ {-1, 2, 1/2}` (for `t ≠ 0, 1`). -/
theorem legendreJ_eq_1728_iff (t : K) (h0 : t ≠ 0) (h1 : t ≠ 1) :
    legendreJ t = 2 ^ 6 * 3 ^ 3 ↔ t = -1 ∨ t = 2 ∨ t = 1 / 2 := by
  rw [legendreJ_eq_iff_aux t _ h0 h1]
  have e : 2 ^ 8 * (t ^ 2 - t + 1) ^ 3 - 2 ^ 6 * 3 ^ 3 * (t ^ 2 * (t - 1) ^ 2) =
      64 * ((t + 1) * (t - 2) * (2 * t - 1)) ^ 2 := by ring
  rw [e]
  simp only [mul_eq_zero, pow_eq_zero_iff two_ne_zero, OfNat.ofNat_ne_zero, false_or,
    add_eq_zero_iff_eq_neg, sub_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by field_simp; linear_combination h))
  · rintro (h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (by rw [h]; ring)

/-- `j = 2²·73³·3⁻⁴` exactly at `t ∈ {9, -8, 9/8, -1/8, 8/9, 1/9}` (for `t ≠ 0, 1`). -/
theorem legendreJ_eq_73_iff (t : K) (h0 : t ≠ 0) (h1 : t ≠ 1) :
    legendreJ t = 2 ^ 2 * 73 ^ 3 / 3 ^ 4 ↔
      t = 9 ∨ t = -8 ∨ t = 9 / 8 ∨ t = -1 / 8 ∨ t = 8 / 9 ∨ t = 1 / 9 := by
  rw [legendreJ_eq_iff_aux t _ h0 h1]
  have e : 2 ^ 8 * (t ^ 2 - t + 1) ^ 3 - 2 ^ 2 * 73 ^ 3 / 3 ^ 4 * (t ^ 2 * (t - 1) ^ 2) =
      4 / 81 * ((t - 9) * (t + 8) * (8 * t - 9) * (8 * t + 1) * (9 * t - 8) * (9 * t - 1)) := by
    ring
  rw [e]
  simp only [mul_eq_zero, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_self, false_or]
  constructor
  · rintro (((((h | h) | h) | h) | h) | h)
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (Or.inl (by linear_combination h))
    · exact Or.inr (Or.inr (Or.inl (by field_simp; linear_combination h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by field_simp; linear_combination h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by field_simp; linear_combination h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by field_simp; linear_combination h)))))
  · rintro (h | h | h | h | h | h) <;> subst h <;> norm_num

/-- `j = 2¹⁴·31³·5⁻³` exactly at the roots of `t² - 125t + 125`, `t² + 123t + 1` and
`125t² - 125t + 1` (for `t ≠ 0, 1`). -/
theorem legendreJ_eq_31_iff (t : K) (h0 : t ≠ 0) (h1 : t ≠ 1) :
    legendreJ t = 2 ^ 14 * 31 ^ 3 / 5 ^ 3 ↔
      t ^ 2 - 125 * t + 125 = 0 ∨ t ^ 2 + 123 * t + 1 = 0 ∨ 125 * t ^ 2 - 125 * t + 1 = 0 := by
  rw [legendreJ_eq_iff_aux t _ h0 h1]
  have e : 2 ^ 8 * (t ^ 2 - t + 1) ^ 3 - 2 ^ 14 * 31 ^ 3 / 5 ^ 3 * (t ^ 2 * (t - 1) ^ 2) =
      256 / 125 * ((t ^ 2 - 125 * t + 125) * (t ^ 2 + 123 * t + 1) *
        (125 * t ^ 2 - 125 * t + 1)) := by
    ring
  rw [e]
  simp only [mul_eq_zero, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_self, false_or, or_assoc]

/-- `j = 0` exactly at the roots of `t² - t + 1` (for `t ≠ 0, 1`). -/
theorem legendreJ_eq_zero_iff (t : K) (h0 : t ≠ 0) (h1 : t ≠ 1) :
    legendreJ t = 0 ↔ t ^ 2 - t + 1 = 0 := by
  rw [legendreJ_eq_iff_aux t _ h0 h1]
  simp

/-- No rational number squares to `5`. -/
theorem rat_sq_ne_five (s : ℚ) : s ^ 2 ≠ 5 := by
  intro h
  have : IsSquare (5 : ℚ) := ⟨s, by rw [← h]; ring⟩
  rw [show (5 : ℚ) = ((5 : ℕ) : ℚ) by norm_num, Rat.isSquare_natCast_iff] at this
  obtain ⟨r, hr⟩ := this
  have : r ≤ 2 := by nlinarith
  interval_cases r <;> omega

/-- No rational `t ≠ 0, 1` has `j = 2¹⁴·31³·5⁻³`: each of the three quadratics has
discriminant `5·55²`. -/
theorem legendreJ_ne_31_rat (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) :
    legendreJ t ≠ 2 ^ 14 * 31 ^ 3 / 5 ^ 3 := by
  rw [Ne, legendreJ_eq_31_iff t h0 h1]
  rintro (h | h | h)
  · exact rat_sq_ne_five ((2 * t - 125) / 55) (by linear_combination 4 / 3025 * h)
  · exact rat_sq_ne_five ((2 * t + 123) / 55) (by linear_combination 4 / 3025 * h)
  · exact rat_sq_ne_five ((250 * t - 125) / 55) (by linear_combination 500 / 3025 * h)

/-- No rational `t ≠ 0, 1` has `j = 0`, since `t² - t + 1 > 0`. -/
theorem legendreJ_ne_zero_rat (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) : legendreJ t ≠ 0 := by
  rw [Ne, legendreJ_eq_zero_iff t h0 h1]
  nlinarith [sq_nonneg (2 * t - 1)]

/-- The triple `1 + 8 = 9`, at `λ = 1/9`, gives the special value `2²·73³·3⁻⁴`. -/
theorem legendreJ_one_ninth : legendreJ (1 / 9 : ℚ) = 2 ^ 2 * 73 ^ 3 / 3 ^ 4 := by
  norm_num [legendreJ]

/-- The triple `1 + 1 = 2`, at `λ = 1/2`, gives the special value `1728`. -/
theorem legendreJ_one_half : legendreJ (1 / 2 : ℚ) = 2 ^ 6 * 3 ^ 3 := by
  norm_num [legendreJ]

end SpecialValues

end IUT.LegendreFrey
