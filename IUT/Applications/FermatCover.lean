import IUT.Applications.HeightExtension

/-!
# Lifting points of the line minus three points to Fermat curves

Sources: Mochizuki, *Arithmetic Elliptic Curves in General Position* ([GenEll]), Theorem 2.1 and
the proof of (ii) ⟹ (i), pages 11 to 13; V. Dimitrov, *Effectivity in Mochizuki's work on the
abc-conjecture* (arXiv 1601.03572), the Theorem on page 3 and the beginning of §5 on page 9.
Pages read for this file: [GenEll] pages 11, 12 and 13; arXiv 1601.03572 pages 3 and 9. Pages
checked against rendered images: all of these.

**What this file is.** It is not a formalization of [GenEll] Theorem 2.1 or of any part of its
proof, and it proves no statement of the papers. It proves the elementary algebraic steps that
occur when a point `x` of `U_P = ℙ¹ \ {0, 1, ∞}` is lifted along the Fermat cover
`π_n : C_n → ℙ¹`, `[X : Y : Z] ↦ [X^n : Z^n]`, of degree `n²` (arXiv 1601.03572, page 9), the
cover through which that paper carries out the reduction of the bounded degree statement for
`(ℙ¹, {0, 1, ∞})` to compactly bounded subsets. In the affine chart `Z = 1` a point of `C_n` over
`x` is a pair `(u, v)` with `u^n = x` and `v^n = 1 - x`. The Fermat cover is one instance of the
covering `U_Y → U_X` of [GenEll] page 11 (finite étale over `U_P`, ramified with index `e = n`
over each point of `{0, 1, ∞}`), with `deg(Y/X) = n²`; the choice of this instance is made here,
not on the pages of [GenEll]. The functions are those of `IUT.Applications.VojtaNumberField`:
`heightNF` (Weil height normalized by the degree), `logDiffNF`, `logCondNF`.

**What the pages print that bears on these steps.**
* [GenEll] page 12: `d' = d · deg(Y/X)`, and "every point of `U_X(ℚ̄)^{≤ d}` clearly lifts to a
  point of `U_Y(ℚ̄)^{≤ d'}`"; Proposition 1.7 (i) is applied to give
  `log-diff_Y ≲ log-diff_X + log-cond_D` on `U_Y(ℚ̄)^{≤ d'}`.
* [GenEll] page 13: Proposition 1.7 (i) with `e = 1` gives
  `log-diff_P + log-cond_C ≲ log-diff_X + log-cond_E` on `Ξ`.
* arXiv 1601.03572 page 9: `deg π_n = n²`; the ramification divisor of `π_n` is
  `(n - 1) π_n^{-1}{0, 1, ∞} = (1 - 1/n) π_n^*([0] + [1] + [∞])`; for `P ∈ ℙ¹(ℚ̄) \ {0, 1, ∞}`
  with `[ℚ(P) : ℚ] ≤ d` one chooses `Q ∈ π_n^{-1}(P)`; displays (7) and (8) express heights on
  `C_n` attached to the ramification divisor and the canonical class through `h(π(Q))` and
  `h(P)`.

**What this file proves.** Let `K` be a number field, `x ∈ K`, `n ≥ 1`.
1. Degree (`fermatCover_point_exists`): there are a number field `L ⊇ K` with `[L : K] ≤ n²`,
   hence `[L : ℚ] ≤ n² [K : ℚ]`, and `u, v ∈ L` with `u^n = x`, `v^n = 1 - x`, so that
   `u^n + v^n = 1`. The field is `K(u) ⊔ K(v)` inside an algebraic closure of `K`; the bound comes
   from `fermatCover_finrank_adjoin_le`, valid in any field extension. For the Fermat cover this
   is the lifting sentence of [GenEll] page 12 with `deg(Y/X) = n²`.
2. Height (`fermatCover_heightNF_root`): for any number field `L ⊇ K` and `u ∈ L` with
   `u^n = x`, `heightNF L u = heightNF K x / n`. It uses Mathlib's `Height.logHeight₁_pow` and the
   invariance `IUT.HeightExtension.htExt_heightNF_algebraMap`. In the same way the second
   coordinate satisfies `heightNF L v = heightNF K (1 - x) / n`.
3. Log-conductor and log-different, as far as the library's definitions reach.
   * `fermatCover_meetsBoundaryAt_of_pow`, `fermatCover_logCondNF_le_pow`: a point `y` of a number
     field meets `{0, 1, ∞}` at a prime only if `y^n` does; hence
     `log-cond(y) ≤ log-cond(y^n)` when `y^n ∉ {0, 1}`.
   * `fermatCover_logCondNF_root_le`, `fermatCover_logCondNF_second_le`: for `x ∉ {0, 1}`,
     `log-cond_L(u) ≤ log-cond_K(x)` and `log-cond_L(v) ≤ log-cond_K(x)`.
   * `fermatCover_lift` collects items 1 to 3 with the existing inequalities
     `log-diff_K ≤ log-diff_L` (`IUT.HeightExtension.htExt_logDiffNF_le`) and
     `log-diff_K + log-cond_K(x) ≤ log-diff_L + log-cond_L(x)`
     (`IUT.PaperIV.DegreePullback.degPb_logDiffNF_add_logCondNF_le`). The latter is, for this
     cover and with the point `x` read in `L`, the direction of the inequality used on page 13.

None of these is a statement of the papers; they are elementary facts about the lifted point.

**Not proved.**
* The upper bound that page 12 takes from Proposition 1.7 (i), in the form it would take here:
  `log-diff_L ≤ log-diff_K + log-cond_K(x) + c(n)` for `L = K(u, v)` and a constant `c(n)`
  depending on `n` only, here. It is proved in `IUT.FermatDifferentGalois` with
  `c(n) = 4 log n` (`fermatGal_lift_logDiffNF_le`), from the unramifiedness of `L/K` at the
  primes not dividing `n` at which `x` reduces away from `{0, 1, ∞}`
  (`IUT.FermatDifferent.fermatDiff_not_dvd_differentIdeal_of_reduces`). The bound
  `v_w(𝔇_{L/K}) ≤ e_w - 1 + v_w(e_w)` for the global different is
  `IUT.DifferentBridge.diffBr_classical_bound`.
* The heights on `C_n` of displays (7) and (8) of arXiv 1601.03572 page 9 (heights attached to
  presented Cartier divisors on a curve); curves, their divisors and their heights are not
  defined in the library. Only the coordinate heights `h(u)`, `h(v)` are treated.
* The remaining input of the reduction, the noncritical Belyi map step ([GenEll] page 12: a
  noncritical Belyi map `φ : X → P` from [Mzk1] Theorem 2.5, unramified over `U_P` and sending the
  points of the limit tuples `Ξ_v` into `U_P(ℚ̄_v)`; arXiv 1601.03572 page 9: the maps
  `f_1 = π, …, f_m : C_n → ℙ¹` of its Proposition 2.1). It is not stated as a Lean proposition:
  curves over number fields other than the projective line, morphisms between them, ramification
  of such morphisms and the noncritical condition have no definition in the library.
* Any statement of the papers, and in particular [GenEll] Theorem 2.1 (ii) ⟹ (i).
-/

universe uK

namespace IUT.FermatCover

open NumberField
open IUT.VojtaNumberField IUT.HeightExtension IUT.PaperIV.DegreePullback

/-! ## The degree of the field of a lifted point -/

section Degree

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

/-- An `n`-th root `u` of an element `a` of `K` (`n ≥ 1`) is integral over `K`. -/
theorem fermatCover_isIntegral_root {n : ℕ} (hn : 0 < n) {u : E} {a : K}
    (hu : u ^ n = algebraMap K E a) : IsIntegral K u := by
  refine ⟨Polynomial.X ^ n - Polynomial.C a, Polynomial.monic_X_pow_sub_C a hn.ne', ?_⟩
  rw [← Polynomial.aeval_def, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hu,
    sub_self]

/-- **The field generated by an `n`-th root has degree at most `n`**: if `u^n = a` with
`a ∈ K` and `n ≥ 1`, then `[K(u) : K] ≤ n`, since the minimal polynomial of `u` divides
`X^n - a`. -/
theorem fermatCover_finrank_adjoin_root_le {n : ℕ} (hn : 0 < n) {u : E} {a : K}
    (hu : u ^ n = algebraMap K E a) :
    Module.finrank K (IntermediateField.adjoin K {u}) ≤ n := by
  have hint := fermatCover_isIntegral_root hn hu
  have hp : (Polynomial.X ^ n - Polynomial.C a : Polynomial K) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero hn a
  have hroot : Polynomial.aeval u (Polynomial.X ^ n - Polynomial.C a) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hu, sub_self]
  rw [IntermediateField.adjoin.finrank hint]
  calc (minpoly K u).natDegree
      ≤ (Polynomial.X ^ n - Polynomial.C a : Polynomial K).natDegree :=
        Polynomial.natDegree_le_of_dvd (minpoly.dvd K u hroot) hp
    _ = n := Polynomial.natDegree_X_pow_sub_C a

/-- **The field of a point of the Fermat curve has degree at most `n²`**: if `u^n = a` and
`v^n = b` with `a, b ∈ K` and `n ≥ 1`, then `[K(u) ⊔ K(v) : K] ≤ n²`. -/
theorem fermatCover_finrank_adjoin_le {n : ℕ} (hn : 0 < n) {u v : E} {a b : K}
    (hu : u ^ n = algebraMap K E a) (hv : v ^ n = algebraMap K E b) :
    Module.finrank K
      ↥(IntermediateField.adjoin K {u} ⊔ IntermediateField.adjoin K {v}) ≤ n ^ 2 := by
  have := IntermediateField.adjoin.finiteDimensional (fermatCover_isIntegral_root hn hu)
  have := IntermediateField.adjoin.finiteDimensional (fermatCover_isIntegral_root hn hv)
  calc Module.finrank K
        ↥(IntermediateField.adjoin K {u} ⊔ IntermediateField.adjoin K {v})
      ≤ Module.finrank K (IntermediateField.adjoin K {u}) *
          Module.finrank K (IntermediateField.adjoin K {v}) :=
        IntermediateField.finrank_sup_le _ _
    _ ≤ n * n := Nat.mul_le_mul (fermatCover_finrank_adjoin_root_le hn hu)
          (fermatCover_finrank_adjoin_root_le hn hv)
    _ = n ^ 2 := (sq n).symm

/-- **Every point of the affine line lifts to the Fermat curve over a field of degree at most
`n²`** (the lifting sentence of [GenEll] page 12 for the Fermat cover of arXiv 1601.03572
page 9, of degree `n²`): for a number field `K`, `x ∈ K` and `n ≥ 1` there are a number field
`L` with `K → L`, `[L : K] ≤ n²`, and `u, v ∈ L` with `u^n = x` and `v^n = 1 - x`. -/
theorem fermatCover_point_exists {K : Type uK} [Field K] [NumberField K] (x : K) {n : ℕ}
    (hn : 0 < n) :
    ∃ (L : Type uK) (_ : Field L) (_ : NumberField L) (_ : Algebra K L),
      Module.finrank K L ≤ n ^ 2 ∧
        ∃ u v : L, u ^ n = algebraMap K L x ∧ v ^ n = 1 - algebraMap K L x := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) x) hn
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) (1 - x)) hn
  set M := IntermediateField.adjoin K {u} ⊔ IntermediateField.adjoin K {v}
  have := IntermediateField.adjoin.finiteDimensional (fermatCover_isIntegral_root hn hu)
  have := IntermediateField.adjoin.finiteDimensional (fermatCover_isIntegral_root hn hv)
  have : NumberField M := NumberField.of_module_finite K M
  have huM : u ∈ M :=
    le_sup_left (a := IntermediateField.adjoin K {u})
      (IntermediateField.mem_adjoin_simple_self K u)
  have hvM : v ∈ M :=
    le_sup_right (b := IntermediateField.adjoin K {v})
      (IntermediateField.mem_adjoin_simple_self K v)
  refine ⟨M, inferInstance, inferInstance, inferInstance, fermatCover_finrank_adjoin_le hn hu hv,
    ⟨u, huM⟩, ⟨v, hvM⟩, ?_, ?_⟩
  · apply Subtype.ext
    simpa using hu
  · apply Subtype.ext
    simpa using hv

end Degree

/-! ## The height of the lifted point -/

section Height

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- `heightNF` of an `n`-th power is `n` times `heightNF`. -/
theorem fermatCover_heightNF_pow (y : L) (n : ℕ) : heightNF L (y ^ n) = n * heightNF L y := by
  rw [heightNF, heightNF, Height.logHeight₁_pow]
  ring

/-- **The height of an `n`-th root**: for number fields `K ⊆ L`, `x ∈ K`, `n ≥ 1` and `u ∈ L`
with `u^n = x`, `ht(u) = ht(x) / n`. -/
theorem fermatCover_heightNF_root (x : K) {n : ℕ} (hn : 0 < n) {u : L}
    (hu : u ^ n = algebraMap K L x) : heightNF L u = heightNF K x / n := by
  have h := fermatCover_heightNF_pow u n
  rw [hu, htExt_heightNF_algebraMap] at h
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [h]
  field_simp

end Height

/-! ## The log-conductor of the lifted point -/

section Conductor

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]

/-- **A point meets `{0, 1, ∞}` at a prime only if its `n`-th power does** (`n ≥ 1`). If `y^n`
and `y^n - 1` are units at `w`, then so is `y` (its valuation is a root of `1` in an ordered
group), and so is `y - 1`, a factor of `y^n - 1 = (y - 1)(1 + y + ⋯ + y^{n-1})` whose
cofactor is integral at `w`. -/
theorem fermatCover_meetsBoundaryAt_of_pow {n : ℕ} (hn : 0 < n)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) {y : L}
    (h : MeetsBoundaryAt L w y) : MeetsBoundaryAt L w (y ^ n) := by
  rw [meetsBoundaryAt_iff_valuation] at h ⊢
  by_contra hc
  simp only [not_or, ne_eq, not_not] at hc
  obtain ⟨hpow, hpow1⟩ := hc
  have hy : w.valuation L y = 1 := by
    rw [map_pow] at hpow
    exact (pow_eq_one_iff.mp hpow).resolve_right hn.ne'
  have hfac : y ^ n - 1 = (∑ i ∈ Finset.range n, y ^ i) * (y - 1) := (geom_sum_mul y n).symm
  have hsum : w.valuation L (∑ i ∈ Finset.range n, y ^ i) ≤ 1 :=
    Valuation.map_sum_le _ fun i _ => by rw [map_pow, hy, one_pow]
  have hsub : w.valuation L (y - 1) ≤ 1 :=
    Valuation.map_sub_le _ hy.le (by rw [map_one])
  have hprod : w.valuation L (∑ i ∈ Finset.range n, y ^ i) * w.valuation L (y - 1) = 1 := by
    rw [← map_mul, ← hfac, hpow1]
  have hy1 : w.valuation L (y - 1) = 1 := by
    refine le_antisymm hsub (not_lt.mp fun hlt => ?_)
    have : w.valuation L (∑ i ∈ Finset.range n, y ^ i) * w.valuation L (y - 1) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left' hsum) hlt
    rw [hprod] at this
    exact lt_irrefl _ this
  rcases h with h | h
  · exact h hy
  · exact h hy1

open Classical in
/-- **The log-conductor of a point is at most that of its `n`-th power** (`n ≥ 1`), when the
power lies in `U = ℙ¹ \ {0, 1, ∞}`. -/
theorem fermatCover_logCondNF_le_pow {n : ℕ} (hn : 0 < n) {y : L} (h0 : y ^ n ≠ 0)
    (h1 : y ^ n ≠ 1) : logCondNF L y ≤ logCondNF L (y ^ n) := by
  unfold logCondNF
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  have hfin := degPb_meetsBoundaryAt_finite h0 h1
  refine finsum_le_finsum ?_ ?_ (fun w => ?_)
  · refine hfin.subset fun w hw => ?_
    rw [Function.mem_support] at hw
    by_contra hm
    exact hw (ite_eq_right fun h => hm (fermatCover_meetsBoundaryAt_of_pow hn w h))
  · refine hfin.subset fun w hw => ?_
    rw [Function.mem_support] at hw
    by_contra hm
    exact hw (ite_eq_right hm)
  · by_cases hw : MeetsBoundaryAt L w y
    · rw [ite_eq_left hw, ite_eq_left (fermatCover_meetsBoundaryAt_of_pow hn w hw)]
    · rw [ite_eq_right hw]
      split_ifs
      · exact Real.log_natCast_nonneg _
      · exact le_rfl

variable [Algebra K L]

/-- **The log-conductor of the first coordinate**: for `x ∈ K \ {0, 1}`, `n ≥ 1` and `u ∈ L`
with `u^n = x`, `log-cond_L(u) ≤ log-cond_K(x)`. -/
theorem fermatCover_logCondNF_root_le {x : K} (hx0 : x ≠ 0) (hx1 : x ≠ 1) {n : ℕ} (hn : 0 < n)
    {u : L} (hu : u ^ n = algebraMap K L x) : logCondNF L u ≤ logCondNF K x := by
  have h0 : u ^ n ≠ 0 := by
    rw [hu]; exact (map_ne_zero (algebraMap K L)).mpr hx0
  have h1 : u ^ n ≠ 1 := by
    rw [hu, ← map_one (algebraMap K L)]
    exact fun h => hx1 ((algebraMap K L).injective h)
  calc logCondNF L u ≤ logCondNF L (u ^ n) := fermatCover_logCondNF_le_pow hn h0 h1
    _ = logCondNF L (algebraMap K L x) := by rw [hu]
    _ ≤ logCondNF K x := htExt_logCondNF_algebraMap_le L hx0 hx1

/-- **The log-conductor of the second coordinate**: for `x ∈ K \ {0, 1}`, `n ≥ 1` and `v ∈ L`
with `v^n = 1 - x`, `log-cond_L(v) ≤ log-cond_K(x)`. -/
theorem fermatCover_logCondNF_second_le {x : K} (hx0 : x ≠ 0) (hx1 : x ≠ 1) {n : ℕ}
    (hn : 0 < n) {v : L} (hv : v ^ n = 1 - algebraMap K L x) :
    logCondNF L v ≤ logCondNF K x := by
  have hv' : v ^ n = algebraMap K L (1 - x) := by rw [map_sub, map_one]; exact hv
  have h0 : (1 - x) ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have h1 : (1 - x) ≠ 1 := by
    intro h; apply hx0; linear_combination -h
  calc logCondNF L v ≤ logCondNF K (1 - x) := fermatCover_logCondNF_root_le h0 h1 hn hv'
    _ = logCondNF K x := logCondNF_one_sub x

end Conductor

/-! ## The lifted point -/

/-- **The lift of a point of `ℙ¹ \ {0, 1, ∞}` to the Fermat curve `C_n`** (arXiv 1601.03572,
page 9, with the lifting sentence of [GenEll] page 12). For a number field `K`, `x ∈ K \ {0, 1}`
and `n ≥ 1` there are a number field `L ⊇ K` and `u, v ∈ L` such that:
`[L : K] ≤ n²` and `[L : ℚ] ≤ n² [K : ℚ]`; `u^n = x`, `v^n = 1 - x`, `u^n + v^n = 1`; `u` and `v`
lie in `U(L)`; `ht(u) = ht(x) / n` and `ht(v) = ht(1 - x) / n`; `log-cond_L(u)` and
`log-cond_L(v)` are at most `log-cond_K(x)`; `log-diff_K ≤ log-diff_L`; and
`log-diff_K + log-cond_K(x) ≤ log-diff_L + log-cond_L(x)`. -/
theorem fermatCover_lift {K : Type uK} [Field K] [NumberField K] {x : K} (hx0 : x ≠ 0)
    (hx1 : x ≠ 1) {n : ℕ} (hn : 0 < n) :
    ∃ (L : Type uK) (_ : Field L) (_ : NumberField L) (_ : Algebra K L),
      Module.finrank K L ≤ n ^ 2 ∧ Module.finrank ℚ L ≤ n ^ 2 * Module.finrank ℚ K ∧
        ∃ u v : L, u ^ n = algebraMap K L x ∧ v ^ n = 1 - algebraMap K L x ∧
          u ^ n + v ^ n = 1 ∧ u ≠ 0 ∧ u ≠ 1 ∧ v ≠ 0 ∧ v ≠ 1 ∧
          heightNF L u = heightNF K x / n ∧ heightNF L v = heightNF K (1 - x) / n ∧
          logCondNF L u ≤ logCondNF K x ∧ logCondNF L v ≤ logCondNF K x ∧
          logDiffNF K ≤ logDiffNF L ∧
          logDiffNF K + logCondNF K x ≤ logDiffNF L + logCondNF L (algebraMap K L x) := by
  obtain ⟨L, _, _, _, hdeg, u, v, hu, hv⟩ := fermatCover_point_exists x hn
  have hinj := (algebraMap K L).injective
  have hv' : v ^ n = algebraMap K L (1 - x) := by rw [map_sub, map_one]; exact hv
  have hxL0 : algebraMap K L x ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hx0
  have hxL1 : algebraMap K L x ≠ 1 := by
    rw [← map_one (algebraMap K L)]; exact fun h => hx1 (hinj h)
  have htow : Module.finrank ℚ K * Module.finrank K L = Module.finrank ℚ L :=
    Module.finrank_mul_finrank ℚ K L
  refine ⟨L, inferInstance, inferInstance, inferInstance, hdeg, ?_, u, v, hu, hv, ?_, ?_, ?_, ?_,
    ?_, fermatCover_heightNF_root x hn hu, fermatCover_heightNF_root (1 - x) hn hv',
    fermatCover_logCondNF_root_le hx0 hx1 hn hu, fermatCover_logCondNF_second_le hx0 hx1 hn hv,
    htExt_logDiffNF_le L, degPb_logDiffNF_add_logCondNF_le L hx0 hx1⟩
  · rw [← htow, mul_comm]
    exact Nat.mul_le_mul_right _ hdeg
  · rw [hu, hv]; ring
  · rintro rfl
    rw [zero_pow hn.ne'] at hu
    exact hxL0 hu.symm
  · rintro rfl
    rw [one_pow] at hu
    exact hxL1 hu.symm
  · rintro rfl
    rw [zero_pow hn.ne'] at hv
    exact hxL1 (sub_eq_zero.mp hv.symm).symm
  · rintro rfl
    rw [one_pow] at hv
    exact hxL0 (by linear_combination hv)

end IUT.FermatCover
