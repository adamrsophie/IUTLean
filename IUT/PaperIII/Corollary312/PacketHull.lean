import IUT.PaperIV.LocalFields.VolumeBridge
import IUT.Applications.DupuyHilado

/-!
# IUT III, Remark 3.9.5 (i), (ii): the holomorphic hull on a finite product of `p`-adic fields

Source: Mochizuki, *Inter-universal Teichmüller Theory III*, Remark 3.9.5 (i), (ii), page 127
(the remark begins at the foot of page 126; (iii) and (iv) follow on page 128). Pages read for
this file: 126, 127 and 128. Pages checked against rendered images: 126, 127 and 128.

## What the page says

Remark 3.9.5 (i), page 127, in the situation of Proposition 3.9 (i): let `U ⊆ ℐ^ℚ(−)` be a
subset that contains a relatively compact subset whose log-volume is finite (that is, `> −∞`).
If `U` is relatively compact, its holomorphic hull is "the smallest subset of the form
`λ · 𝒪`" that contains `U`, where `𝒪` is the integral structure and `λ ∈ ℐ^ℚ(−)` is an element
each of whose components, relative to the decomposition of `ℐ^ℚ(−)` as a direct sum of fields,
is nonzero. If `U` is not relatively compact, its holomorphic hull is `ℐ^ℚ(−)` itself. "One
verifies immediately that the holomorphic hull is well-defined [under the conditions stated]."
Remark 3.9.5 (ii) writes `ℙ` for the direct product regions, `ℍ = {H ⊊ ℐ^ℚ(−) | H is a hull}`
(proper subsets), observes `ℍ ⊆ ℙ`, and characterizes the map `φ : ℙ → ℍ` by (P1), (P2), (P3)
(`IUT.PaperIII.Remark3_9_5.IsHullMap`).

## What this file is and is not

**This file does not treat tensor packets.** It works on a finite product `V = Π s, L s` of
normed fields in place of the direct sum of fields of the page; the isomorphism of a tensor
packet with such a product (`IUT.PaperIV.LocalFields.volBridge_tensor_equiv_pi` for two
factors) is not applied here, and the archimedean case is not treated. The integral structure
is `𝒪 = {x | ∀ s, ‖x s‖ ≤ 1}` (`pktHullIntegers`), the product of the closed unit balls; for a
finite extension of `ℚ_p` with its spectral norm the closed unit ball is the ring of integers
(`pktHullIntegers_eq_pi_integralClosure`).

* `pktHullPrincipal c = c • 𝒪` for `c : Π s, (L s)ˣ` (the sets `λ · 𝒪`), equal to the box
  `{x | ∀ s, ‖x s‖ ≤ ‖c s‖}` (`pktHull_mem_principal`); `pktHullForms` is the family of them.
* `pktHull U` is `⋂ {H ∈ pktHullForms | U ⊆ H}` when `closure U` is compact, and `univ`
  otherwise. Where the page's smallest set exists, it is this intersection; the definition
  does not presuppose that it exists.
* *Existence of the smallest set* (`pktHull_isLeast`): under a discreteness hypothesis on the
  value group (`pktHullDiscrete`, proved for every finite extension of `ℚ_p` with its spectral
  norm in `pktHullDiscrete_spectral` and for `ℚ_p` in `pktHullDiscrete_padic`), for every
  relatively compact `U` none of whose coordinate projections is zero
  (`pktHullNondeg`), `pktHull U` is the least set of the form `λ · 𝒪` containing `U`, with
  `λ_s` a point of the projection of `U` of largest norm (`pktHull_eq_principal`). The page's
  condition (a relatively compact subset of finite log-volume) implies the nondegeneracy:
  a set of positive product measure is not contained in a coordinate hyperplane
  (`pktHullNondeg_of_measure`). For finite extensions of `ℚ_p` with Haar measure the two
  together give `pktHull_isLeast_spectral`.
* *Excluded cases.* For `U` that is not relatively compact, `pktHull U = univ`, by definition,
  as on the page; in particular for every unbounded `U` (`pktHull_of_not_isBounded`), and
  relatively compact is the same as bounded for finite extensions of `ℚ_p`
  (`pktHull_relCompact_iff`). For a bounded `U` with a zero coordinate projection, which the
  page's condition excludes, there may be no smallest set: for `U = {0}` there is none
  (`pktHull_not_exists_isLeast_zero`). The value of `pktHull` there is a convention.
* *Properties* (for all subsets, unless stated): `U ⊆ pktHull U` (`pktHull_extensive`),
  monotone (`pktHull_mono`), idempotent for proper discretely valued factors
  (`pktHull_idem`), and
  `pktHull (g • U) = g • pktHull U` for every unit `g` of `V`, that is, every element of the
  product of the groups `L_s^×` (`pktHull_smul`). With `𝓟` the relatively compact sets with
  nonzero projections and `𝓗 = pktHullForms`, `pktHull` satisfies `IsHullMap 𝓟 𝓗`
  (`pktHull_isHullMap`). On all subsets it does not, because `pktHull univ = univ` is not of
  the form `λ · 𝒪`, in accordance with `H ⊊ ℐ^ℚ(−)` on page 127
  (`pktHull_not_isHullMap_univ`). The paper's `ℙ` (direct product regions, Remark 3.1.1 (iii))
  is not modeled; the domain `𝓟` here is a choice.
* *Log-volume* (`pktHull_muLog_principal`): for finite extensions `L_s` of `ℚ_p` of degrees
  `d_s`, any Haar measures `μ_s` and the product measure, the normalized log-volume
  `padicMuLog` (normalized at `𝒪`, divided by `D = Σ d_s`) is
  `μ^log(λ · 𝒪) = (Σ_s d_s log ‖λ_s‖) / D`, a weighted sum with weights `d_s / D` that come from
  `Measure.pi` and the scaling law `μ_s(y • A) = ‖y‖ ^ d_s μ_s(A)`. Hence the log-volume of a
  hull (`pktHull_muLog_hull`). These are the Haar weights of the whole product, not the
  normalized weights of IUT III Remark 3.1.1 (ii); in the reading of `WeightedPacket.lean`,
  `wPkt_weight_eq_haar_iff` shows that the two weight systems coincide for every tuple of places
  if and only if `[K_v : (F_mod)_v]` is the same at all places over `p` (for nonempty label and
  place sets and positive degrees).
* *Comparison with the coordinatewise hull* `IUT.Applications.DupuyHilado.dhHull` (polydisc of
  the coordinate suprema of norms). On relatively compact sets they agree for discretely valued
  factors (`pktHull_eq_dhHull`), whether or not a projection is zero. On `ℚ_p × ℤ_p ⊆ ℚ_p²`
  they differ (`pktHull_dhHull_padic_test`): the page's definition gives `ℚ_p²` (the set is not
  relatively compact), the polydisc construction gives `ℚ_p × ℤ_p` itself (radii `∞` and `1`).
  This is a difference between two definitions on an unbounded set.
* *Unions.* `⋃ i, pktHull (U i) ⊆ pktHull (⋃ i, U i)` (`pktHull_iUnion_subset`); the inclusion
  is strict for `U₀ = {(1, p)}`, `U₁ = {(p, 1)}` in `ℚ_p²`, where `(1, 1)` lies in the hull of
  the union and in neither hull (`pktHull_union_strict_padic`). This matters because
  Corollary 3.12 takes the hull of the union of the possible images.

## Interpretation choices

1. *Relatively compact* is `IsCompact (closure U)` in the product topology.
2. *Finite log-volume.* The page asks for a relatively compact subset of finite log-volume. Here
   it is read as a subset of positive (outer) product Haar measure; only its consequence, that
   no coordinate projection of `U` is zero, is used, and the theorems are stated under that
   weaker hypothesis where possible.
3. *The domain of `φ`.* (P1) to (P3) are checked on `𝓟` above, not on the paper's direct
   product regions.

## Not proved

* Nothing about tensor packets, `ℐ^ℚ(−)` itself, log-shells, or the archimedean places.
* Remark 3.9.5 (iii), (iv) (the sets `Φ(P)`, `Ξ(P)` of page 128).
-/

namespace IUT.PaperIII.Corollary312

open MeasureTheory Set IUT.PaperIII.Remark3_9_5 IUT.Applications.DupuyHilado
  IUT.Prerequisites.PadicVolume IUT.PaperIV.LocalFields
open scoped Pointwise

/-! ## Discretely valued normed fields -/

section Discrete

/-- The value group of a normed field `K` is discrete: there is `ϖ` with `0 < ‖ϖ‖ < 1` such that
every nonzero `x` has `‖x‖ = ‖ϖ‖ ^ k` for an integer `k`. For a finite extension of `ℚ_p` with
its spectral norm this is `pktHullDiscrete_spectral`. -/
def pktHullDiscrete (K : Type*) [NormedField K] : Prop :=
  ∃ ϖ : K, 0 < ‖ϖ‖ ∧ ‖ϖ‖ < 1 ∧ ∀ x : K, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖ϖ‖ ^ k

variable {K : Type*} [NormedField K]

/-- Elements of arbitrarily small nonzero norm. -/
theorem pktHull_exists_small (hK : pktHullDiscrete K) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : K, c ≠ 0 ∧ ‖c‖ < ε := by
  obtain ⟨ϖ, h0, h1, -⟩ := hK
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε h1
  exact ⟨ϖ ^ n, pow_ne_zero n (norm_pos_iff.mp h0), by rwa [norm_pow]⟩

/-- Elements of arbitrarily large norm. -/
theorem pktHull_exists_large (hK : pktHullDiscrete K) (B : ℝ) :
    ∃ c : K, c ≠ 0 ∧ B ≤ ‖c‖ := by
  obtain ⟨c, hc0, hc⟩ := pktHull_exists_small hK (inv_pos.mpr (by positivity : (0 : ℝ) < |B| + 1))
  refine ⟨c⁻¹, inv_ne_zero hc0, ?_⟩
  have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  rw [norm_inv]
  calc B ≤ |B| + 1 := (le_abs_self B).trans (le_add_of_nonneg_right zero_le_one)
    _ ≤ ‖c‖⁻¹ := by
      rw [le_inv_comm₀ (by positivity) hpos]
      exact hc.le

/-- **The largest norm is attained** on a set `S` of a discretely valued field whose norms are
bounded and which contains a nonzero element. -/
theorem pktHull_exists_max (hK : pktHullDiscrete K) {S : Set K} {B : ℝ}
    (hB : ∀ y ∈ S, ‖y‖ ≤ B) {x₀ : K} (hx₀ : x₀ ∈ S) (h0 : x₀ ≠ 0) :
    ∃ x ∈ S, x ≠ 0 ∧ ∀ y ∈ S, ‖y‖ ≤ ‖x‖ := by
  classical
  obtain ⟨ϖ, hr0, hr1, hval⟩ := hK
  have hBpos : 0 < B := (norm_pos_iff.mpr h0).trans_le (hB x₀ hx₀)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hBpos) hr1
  have hbdd : ∃ b : ℤ, ∀ k : ℤ, (∃ y ∈ S, y ≠ 0 ∧ ‖y‖ = ‖ϖ‖ ^ k) → b ≤ k := by
    refine ⟨-(n : ℤ), ?_⟩
    rintro k ⟨y, hy, -, hyk⟩
    have h1 : ‖ϖ‖ ^ k < ‖ϖ‖ ^ (-(n : ℤ)) := by
      rw [zpow_neg, zpow_natCast, ← hyk]
      calc ‖y‖ ≤ B := hB y hy
        _ < (‖ϖ‖ ^ n)⁻¹ := by
          rw [lt_inv_comm₀ hBpos (pow_pos hr0 n)]
          exact hn
    exact ((zpow_lt_zpow_iff_right_of_lt_one₀ hr0 hr1).mp h1).le
  obtain ⟨k₀, hk₀⟩ := hval x₀ h0
  obtain ⟨lb, ⟨x, hx, hx0, hxk⟩, hmin⟩ :=
    Int.exists_least_of_bdd hbdd ⟨k₀, x₀, hx₀, h0, hk₀⟩
  refine ⟨x, hx, hx0, fun y hy => ?_⟩
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [norm_zero]; exact norm_nonneg _
  obtain ⟨k, hk⟩ := hval y hy0
  rw [hk, hxk]
  exact zpow_le_zpow_right_of_le_one₀ hr0 hr1.le (hmin k ⟨y, hy, hy0, hk⟩)

end Discrete

/-! ## Principal product sets and the hull -/

section Generic

variable {ι : Type*} [Fintype ι] {L : ι → Type*} [∀ s, NormedField (L s)]

/-- The integral structure `𝒪 = Π s, 𝒪_{L_s}`, modeled as the product of the closed unit
balls. -/
def pktHullIntegers : Set (∀ s, L s) := {x | ∀ s, ‖x s‖ ≤ 1}

/-- The set `λ · 𝒪` of Remark 3.9.5 (i), page 127, for `λ` with every component nonzero (an
element of `Π s, L_s^×`). -/
def pktHullPrincipal (c : ∀ s, (L s)ˣ) : Set (∀ s, L s) :=
  (fun s => ((c s : (L s)ˣ) : L s)) • pktHullIntegers

/-- The family of the sets `λ · 𝒪`, the candidate hulls. -/
def pktHullForms : Set (Set (∀ s, L s)) := Set.range (pktHullPrincipal (L := L))

/-- No coordinate projection of `U` is zero. -/
def pktHullNondeg (U : Set (∀ s, L s)) : Prop := ∀ s, ∃ x ∈ U, x s ≠ 0

open Classical in
/-- **The holomorphic hull** of Remark 3.9.5 (i), page 127: for relatively compact `U`, the
intersection of the sets `λ · 𝒪` containing `U` (the smallest one when it exists,
`pktHull_isLeast`); for `U` not relatively compact, the whole space. -/
noncomputable def pktHull (U : Set (∀ s, L s)) : Set (∀ s, L s) :=
  if IsCompact (closure U) then ⋂₀ {H | H ∈ pktHullForms ∧ U ⊆ H} else Set.univ

omit [Fintype ι] in
/-- `λ · 𝒪` is the box `{x | ∀ s, ‖x s‖ ≤ ‖λ_s‖}`. -/
theorem pktHull_mem_principal {c : ∀ s, (L s)ˣ} {x : ∀ s, L s} :
    x ∈ pktHullPrincipal c ↔ ∀ s, ‖x s‖ ≤ ‖((c s : (L s)ˣ) : L s)‖ := by
  simp only [pktHullPrincipal, pktHullIntegers, Set.mem_smul_set, Set.mem_ofPred_eq,
    smul_eq_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩ s
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hy s)
  · intro hx
    refine ⟨fun s => (((c s)⁻¹ : (L s)ˣ) : L s) * x s, fun s => ?_, ?_⟩
    · rw [norm_mul, Units.val_inv_eq_inv_val, norm_inv,
        inv_mul_le_iff₀ (norm_pos_iff.mpr (c s).ne_zero), mul_one]
      exact hx s
    · funext s
      simp

omit [Fintype ι] in
/-- `𝒪` itself is of the form `λ · 𝒪`, with `λ = 1`. -/
theorem pktHullPrincipal_one : pktHullPrincipal (1 : ∀ s, (L s)ˣ) = pktHullIntegers := by
  ext x
  simp [pktHull_mem_principal, pktHullIntegers]

omit [Fintype ι] in
/-- `λ · 𝒪` as a product of closed balls. -/
theorem pktHullPrincipal_eq_pi (c : ∀ s, (L s)ˣ) :
    pktHullPrincipal c = Set.univ.pi (fun s => Metric.closedBall (0 : L s) ‖(c s : L s)‖) := by
  ext x
  simp [pktHull_mem_principal, Metric.mem_closedBall, dist_zero_right]

omit [Fintype ι] in
/-- The hull of a relatively compact set is the intersection of the sets `λ · 𝒪` containing
it. -/
theorem pktHull_of_relCompact {U : Set (∀ s, L s)} (h : IsCompact (closure U)) :
    pktHull U = ⋂₀ {H | H ∈ pktHullForms ∧ U ⊆ H} := by
  simp only [pktHull, h, ↓reduceIte]

omit [Fintype ι] in
/-- The hull of a set that is not relatively compact is the whole space. -/
theorem pktHull_of_not_relCompact {U : Set (∀ s, L s)} (h : ¬ IsCompact (closure U)) :
    pktHull U = Set.univ := by
  simp only [pktHull, h, ↓reduceIte]

/-- A relatively compact set is bounded. -/
theorem pktHull_isBounded_of_relCompact {U : Set (∀ s, L s)} (h : IsCompact (closure U)) :
    Bornology.IsBounded U :=
  h.isBounded.subset subset_closure

/-- **Unbounded sets**: the hull is the whole space, as on page 127 for sets that are not
relatively compact. -/
theorem pktHull_of_not_isBounded {U : Set (∀ s, L s)} (h : ¬ Bornology.IsBounded U) :
    pktHull U = Set.univ :=
  pktHull_of_not_relCompact fun hc => h (pktHull_isBounded_of_relCompact hc)

/-- For proper factors (for example finite extensions of `ℚ_p`), relatively compact is the same
as bounded. -/
theorem pktHull_relCompact_iff [∀ s, ProperSpace (L s)] {U : Set (∀ s, L s)} :
    IsCompact (closure U) ↔ Bornology.IsBounded U :=
  ⟨pktHull_isBounded_of_relCompact, fun h => h.isCompact_closure⟩

omit [Fintype ι] in
/-- `U ⊆ pktHull U`, property (P2). -/
theorem pktHull_extensive (U : Set (∀ s, L s)) : U ⊆ pktHull U := by
  by_cases h : IsCompact (closure U)
  · rw [pktHull_of_relCompact h]
    exact Set.subset_sInter fun H hH => hH.2
  · rw [pktHull_of_not_relCompact h]
    exact Set.subset_univ U

omit [Fintype ι] in
/-- The hull is monotone, on all subsets (property (P3)). -/
theorem pktHull_mono {U U' : Set (∀ s, L s)} (h : U ⊆ U') : pktHull U ⊆ pktHull U' := by
  by_cases h' : IsCompact (closure U')
  · have hU : IsCompact (closure U) := h'.of_isClosed_subset isClosed_closure (closure_mono h)
    rw [pktHull_of_relCompact hU, pktHull_of_relCompact h']
    exact Set.sInter_subset_sInter fun H hH => ⟨hH.1, h.trans hH.2⟩
  · rw [pktHull_of_not_relCompact h']
    exact Set.subset_univ _

omit [Fintype ι] in
/-- The hull of the whole space is the whole space. -/
theorem pktHull_univ : pktHull (Set.univ : Set (∀ s, L s)) = Set.univ :=
  Set.eq_univ_of_univ_subset (pktHull_extensive _)

variable (hd : ∀ s, pktHullDiscrete (L s))
include hd

/-- A bounded set lies in some `λ · 𝒪`. -/
theorem pktHull_exists_form_superset {U : Set (∀ s, L s)} (hU : Bornology.IsBounded U) :
    ∃ c : ∀ s, (L s)ˣ, U ⊆ pktHullPrincipal c := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hU
  choose b hb0 hbC using fun s => pktHull_exists_large (hd s) C
  refine ⟨fun s => Units.mk0 (b s) (hb0 s), fun x hx => pktHull_mem_principal.mpr fun s => ?_⟩
  exact ((norm_le_pi_norm x s).trans (hC x hx)).trans (hbC s)

/-- **Coordinatewise description of the intersection** of the sets `λ · 𝒪` containing a
bounded `U`: `y` lies in it exactly when, for every `s`, `‖y_s‖ ≤ ‖c‖` for every nonzero `c`
of `L_s` with `‖x_s‖ ≤ ‖c‖` on `U`. -/
theorem pktHull_mem_sInter_iff {U : Set (∀ s, L s)} (hU : Bornology.IsBounded U)
    (y : ∀ s, L s) :
    y ∈ ⋂₀ {H | H ∈ pktHullForms ∧ U ⊆ H} ↔
      ∀ s, ∀ c : L s, c ≠ 0 → (∀ x ∈ U, ‖x s‖ ≤ ‖c‖) → ‖y s‖ ≤ ‖c‖ := by
  classical
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hU
  choose b hb0 hbC using fun s => pktHull_exists_large (hd s) C
  constructor
  · intro hy s c hc hcU
    let l : ∀ t, (L t)ˣ := Function.update (fun t => Units.mk0 (b t) (hb0 t)) s (Units.mk0 c hc)
    have hmem : pktHullPrincipal l ∈ {H | H ∈ pktHullForms ∧ U ⊆ H} := by
      refine ⟨⟨l, rfl⟩, fun x hx => pktHull_mem_principal.mpr fun t => ?_⟩
      rcases eq_or_ne t s with rfl | hts
      · simp only [l, Function.update_self, Units.val_mk0]
        exact hcU x hx
      · simp only [l, Function.update_of_ne hts, Units.val_mk0]
        exact ((norm_le_pi_norm x t).trans (hC x hx)).trans (hbC t)
    have := pktHull_mem_principal.mp (hy _ hmem) s
    simpa [l] using this
  · rintro hy H ⟨⟨c, rfl⟩, hUH⟩
    exact pktHull_mem_principal.mpr fun s =>
      hy s _ (c s).ne_zero fun x hx => pktHull_mem_principal.mp (hUH hx) s

/-- For each `s`, a bounded `U` with nonzero `s`-th projection has a point whose `s`-th
coordinate has the largest norm. -/
theorem pktHull_exists_coord_max {U : Set (∀ s, L s)} (hU : Bornology.IsBounded U)
    (hn : pktHullNondeg U) (s : ι) :
    ∃ x ∈ U, x s ≠ 0 ∧ ∀ y ∈ U, ‖y s‖ ≤ ‖x s‖ := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hU
  obtain ⟨x₀, hx₀, h0⟩ := hn s
  obtain ⟨m, ⟨x, hx, rfl⟩, hm0, hmax⟩ := pktHull_exists_max (hd s)
    (S := (fun x => x s) '' U) (B := C)
    (by rintro _ ⟨x, hx, rfl⟩; exact (norm_le_pi_norm x s).trans (hC x hx)) ⟨x₀, hx₀, rfl⟩ h0
  exact ⟨x, hx, hm0, fun y hy => hmax _ ⟨y, hy, rfl⟩⟩

/-- **The hull is `λ · 𝒪` with `λ_s` a point of largest norm of the `s`-th projection**, for
relatively compact `U` with nonzero projections. -/
theorem pktHull_eq_principal {U : Set (∀ s, L s)} (hU : IsCompact (closure U))
    (hn : pktHullNondeg U) :
    ∃ c : ∀ s, (L s)ˣ, pktHull U = pktHullPrincipal c ∧
      ∀ s, ∃ x ∈ U, ((c s : (L s)ˣ) : L s) = x s ∧ ∀ y ∈ U, ‖y s‖ ≤ ‖x s‖ := by
  have hb := pktHull_isBounded_of_relCompact hU
  choose xs hxs hxs0 hxsmax using pktHull_exists_coord_max hd hb hn
  refine ⟨fun s => Units.mk0 (xs s s) (hxs0 s), ?_, fun s => ⟨xs s, hxs s, rfl, hxsmax s⟩⟩
  ext y
  rw [pktHull_of_relCompact hU, pktHull_mem_sInter_iff hd hb, pktHull_mem_principal]
  constructor
  · intro h s
    exact h s _ (hxs0 s) (hxsmax s)
  · intro h s c _ hcU
    exact (h s).trans (hcU _ (hxs s))

/-- **Remark 3.9.5 (i), page 127: the hull is the smallest set of the form `λ · 𝒪` containing
`U`**, for relatively compact `U` none of whose coordinate projections is zero, over
discretely valued fields. -/
theorem pktHull_isLeast {U : Set (∀ s, L s)} (hU : IsCompact (closure U))
    (hn : pktHullNondeg U) :
    IsLeast {H | U ⊆ H ∧ H ∈ pktHullForms} (pktHull U) := by
  obtain ⟨c, hc, -⟩ := pktHull_eq_principal hd hU hn
  refine ⟨⟨pktHull_extensive U, c, hc.symm⟩, ?_⟩
  rintro H ⟨hUH, hH⟩
  rw [pktHull_of_relCompact hU]
  exact Set.sInter_subset_of_mem ⟨hH, hUH⟩

omit [Fintype ι] in
/-- **A degenerate set has no smallest `λ · 𝒪`**: for `U = {0}` (a coordinate projection is
zero; the page's condition of a subset of finite log-volume excludes it) no set of the form
`λ · 𝒪` containing `U` is smallest. -/
theorem pktHull_not_exists_isLeast_zero [Nonempty ι] :
    ¬ ∃ H, IsLeast {H | ({0} : Set (∀ s, L s)) ⊆ H ∧ H ∈ pktHullForms} H := by
  classical
  rintro ⟨_, ⟨-, c, rfl⟩, hleast⟩
  obtain ⟨s₀⟩ := (inferInstance : Nonempty ι)
  obtain ⟨d, hd0, hdc⟩ := pktHull_exists_small (hd s₀) (norm_pos_iff.mpr (c s₀).ne_zero)
  let c' : ∀ t, (L t)ˣ := Function.update c s₀ (Units.mk0 d hd0)
  have hmem : pktHullPrincipal c' ∈ {H | ({0} : Set (∀ s, L s)) ⊆ H ∧ H ∈ pktHullForms} := by
    refine ⟨?_, c', rfl⟩
    rintro _ rfl
    exact pktHull_mem_principal.mpr fun t => by simp
  have hc : (fun t => ((c t : (L t)ˣ) : L t)) ∈ pktHullPrincipal c :=
    pktHull_mem_principal.mpr fun t => le_rfl
  have := pktHull_mem_principal.mp (hleast hmem hc) s₀
  simp only [c', Function.update_self, Units.val_mk0] at this
  exact absurd (this.trans_lt hdc) (lt_irrefl _)

/-- **Agreement with the coordinatewise hull** of `IUT.Applications.DupuyHilado`: on relatively
compact sets, over discretely valued fields, `pktHull U` is the polydisc of the coordinate
suprema of norms, whether or not a projection is zero. -/
theorem pktHull_eq_dhHull {U : Set (∀ s, L s)} (hU : IsCompact (closure U)) :
    pktHull U = dhHull U := by
  have hb := pktHull_isBounded_of_relCompact hU
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
  ext y
  rw [pktHull_of_relCompact hU, pktHull_mem_sInter_iff hd hb]
  simp only [dhHull, dhPolydisc, Set.mem_ofPred_eq]
  refine forall_congr' fun s => ?_
  by_cases hs : ∃ x ∈ U, x s ≠ 0
  · obtain ⟨x₀, hx₀, h0⟩ := hs
    obtain ⟨m, ⟨xm, hxm, rfl⟩, hm0, hmax⟩ := pktHull_exists_max (hd s)
      (S := (fun x => x s) '' U) (B := C)
      (by rintro _ ⟨x, hx, rfl⟩; exact (norm_le_pi_norm x s).trans (hC x hx)) ⟨x₀, hx₀, rfl⟩ h0
    have hR : dhPolyRadius U s = ENNReal.ofReal ‖xm s‖ := by
      apply le_antisymm
      · exact iSup₂_le fun x hx => ENNReal.ofReal_le_ofReal (hmax _ ⟨x, hx, rfl⟩)
      · exact le_iSup₂ (f := fun x (_ : x ∈ U) => ENNReal.ofReal ‖x s‖) xm hxm
    rw [hR, ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)]
    constructor
    · intro h
      exact h _ hm0 fun x hx => hmax _ ⟨x, hx, rfl⟩
    · intro h c _ hcU
      exact h.trans (hcU _ hxm)
  · push Not at hs
    have hR : dhPolyRadius U s = 0 := by
      refine le_antisymm (iSup₂_le fun x hx => ?_) bot_le
      rw [hs x hx, norm_zero, ENNReal.ofReal_zero]
    rw [hR, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero]
    constructor
    · intro h
      by_contra hy
      have hy0 : y s ≠ 0 := fun h0 => hy (by rw [h0, norm_zero])
      obtain ⟨c, hc0, hc⟩ := pktHull_exists_small (hd s) (norm_pos_iff.mpr hy0)
      have := h c hc0 fun x hx => by rw [hs x hx, norm_zero]; exact norm_nonneg _
      exact absurd (this.trans_lt hc) (lt_irrefl _)
    · intro h c _ _
      exact h.trans (norm_nonneg _)

/-- **Hulls of singletons**: `pktHull {v}` is the box of radii `‖v_s‖` (a zero coordinate gives
radius `0`, although then no smallest `λ · 𝒪` exists). -/
theorem pktHull_singleton (v : ∀ s, L s) :
    pktHull {v} = {y | ∀ s, ‖y s‖ ≤ ‖v s‖} := by
  have hU : IsCompact (closure ({v} : Set (∀ s, L s))) := by
    rw [closure_singleton]; exact isCompact_singleton
  ext y
  rw [pktHull_of_relCompact hU, pktHull_mem_sInter_iff hd Bornology.isBounded_singleton,
    Set.mem_ofPred_eq]
  refine forall_congr' fun s => ⟨fun h => ?_, fun h c _ hc => h.trans (hc v rfl)⟩
  rcases eq_or_ne (v s) 0 with h0 | h0
  · rw [h0, norm_zero]
    by_contra hy
    have hy0 : 0 < ‖y s‖ := lt_of_not_ge hy
    obtain ⟨c, hc0, hc⟩ := pktHull_exists_small (hd s) hy0
    have := h c hc0 fun x hx => by rw [hx, h0, norm_zero]; exact norm_nonneg _
    exact absurd (this.trans_lt hc) (lt_irrefl _)
  · exact h (v s) h0 fun x hx => by rw [hx]

omit hd [Fintype ι] in
/-- **Hull of a union**: it contains the union of the hulls (by monotonicity). -/
theorem pktHull_iUnion_subset {κ : Type*} (U : κ → Set (∀ s, L s)) :
    ⋃ i, pktHull (U i) ⊆ pktHull (⋃ i, U i) :=
  Set.iUnion_subset fun i => pktHull_mono (Set.subset_iUnion U i)

/-! ### Equivariance under units -/

omit [Fintype ι] hd in
/-- The coordinates of the inverse of a unit of `V`. -/
theorem pktHull_units_inv_apply (g : (∀ s, L s)ˣ) (s : ι) :
    ((g⁻¹ : (∀ s, L s)ˣ) : ∀ s, L s) s = ((g : ∀ s, L s) s)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  have := congrFun g.mul_inv s
  simpa using this

omit [Fintype ι] hd in
/-- The coordinates of a unit of `V` are nonzero. -/
theorem pktHull_units_apply_ne_zero (g : (∀ s, L s)ˣ) (s : ι) : (g : ∀ s, L s) s ≠ 0 := by
  intro h
  have := congrFun g.mul_inv s
  simp [h] at this

omit hd [Fintype ι] in
/-- A unit of `V` maps the sets `λ · 𝒪` to sets of the same form. -/
theorem pktHull_smul_mem_forms (g : (∀ s, L s)ˣ) {H : Set (∀ s, L s)} (hH : H ∈ pktHullForms) :
    g • H ∈ pktHullForms := by
  obtain ⟨c, rfl⟩ := hH
  refine ⟨fun s => Units.mk0 ((g : ∀ s, L s) s * c s)
    (mul_ne_zero (pktHull_units_apply_ne_zero g s) (c s).ne_zero), ?_⟩
  ext x
  rw [pktHull_mem_principal, Set.mem_smul_set_iff_inv_smul_mem, pktHull_mem_principal]
  refine forall_congr' fun s => ?_
  have hg := pktHull_units_apply_ne_zero g s
  simp only [Units.smul_def, smul_eq_mul, Pi.mul_apply, Units.val_mk0, norm_mul,
    pktHull_units_inv_apply, norm_inv]
  rw [inv_mul_le_iff₀ (norm_pos_iff.mpr hg)]

omit hd [Fintype ι] in
/-- **Equivariance** (all subsets): `pktHull (g • U) = g • pktHull U` for every unit `g` of
`V = Π s, L s`, that is, every element of the product of the groups `L_s^×`. -/
theorem pktHull_smul (g : (∀ s, L s)ˣ) (U : Set (∀ s, L s)) :
    pktHull (g • U) = g • pktHull U := by
  have hcl : closure (g • U) = g • closure U := closure_smul g U
  have hcomp : IsCompact (closure (g • U)) ↔ IsCompact (closure U) := by
    rw [hcl]
    refine ⟨fun h => ?_, fun h => h.smul g⟩
    have := h.smul g⁻¹
    rwa [inv_smul_smul] at this
  by_cases hU : IsCompact (closure U)
  · rw [pktHull_of_relCompact (hcomp.mpr hU), pktHull_of_relCompact hU]
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [Set.mem_sInter, Set.mem_ofPred_eq, and_imp]
    constructor
    · intro hx H hH hUH
      have := hx (g • H) (pktHull_smul_mem_forms g hH) (Set.smul_set_mono hUH)
      rwa [Set.mem_smul_set_iff_inv_smul_mem] at this
    · intro hx H' hH' hUH'
      have h1 : g⁻¹ • H' ∈ pktHullForms := pktHull_smul_mem_forms g⁻¹ hH'
      have h2 : U ⊆ g⁻¹ • H' := fun x hx => by
        rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
        exact hUH' (Set.smul_mem_smul_set hx)
      have := hx _ h1 h2
      rwa [Set.smul_mem_smul_set_iff] at this
  · rw [pktHull_of_not_relCompact (fun h => hU (hcomp.mp h)), pktHull_of_not_relCompact hU,
      Set.smul_set_univ]

/-! ### Idempotence and the conditions (P1) to (P3) -/

omit hd [Fintype ι] in
/-- For proper factors, a set of the form `λ · 𝒪` is compact. -/
theorem pktHull_isCompact_principal [∀ s, ProperSpace (L s)] (c : ∀ s, (L s)ˣ) :
    IsCompact (pktHullPrincipal c) := by
  rw [pktHullPrincipal_eq_pi]
  exact isCompact_univ_pi fun s => isCompact_closedBall _ _

omit hd [Fintype ι] in
/-- For proper factors, the hull of `U` lies in every `λ · 𝒪` that contains `U`. -/
theorem pktHull_subset_of_form [∀ s, ProperSpace (L s)] {U H : Set (∀ s, L s)}
    (hH : H ∈ pktHullForms) (hUH : U ⊆ H) : pktHull U ⊆ H := by
  obtain ⟨c, rfl⟩ := hH
  have hc := pktHull_isCompact_principal c
  have hU : IsCompact (closure U) :=
    hc.of_isClosed_subset isClosed_closure (closure_minimal hUH hc.isClosed)
  rw [pktHull_of_relCompact hU]
  exact Set.sInter_subset_of_mem ⟨⟨c, rfl⟩, hUH⟩

/-- **Idempotence** (all subsets, proper factors): `pktHull (pktHull U) = pktHull U`. -/
theorem pktHull_idem [∀ s, ProperSpace (L s)] (U : Set (∀ s, L s)) :
    pktHull (pktHull U) = pktHull U := by
  by_cases hU : IsCompact (closure U)
  · obtain ⟨c, hc⟩ := pktHull_exists_form_superset hd (pktHull_isBounded_of_relCompact hU)
    have hsub := pktHull_subset_of_form ⟨c, rfl⟩ hc
    have hcU : IsCompact (closure (pktHull U)) :=
      (pktHull_isCompact_principal c).of_isClosed_subset isClosed_closure
        (closure_minimal hsub (pktHull_isCompact_principal c).isClosed)
    rw [pktHull_of_relCompact hcU]
    conv_rhs => rw [pktHull_of_relCompact hU]
    congr 1
    ext H
    simp only [Set.mem_ofPred_eq]
    refine and_congr_right fun hH => ⟨fun h => (pktHull_extensive U).trans h, fun h => ?_⟩
    exact pktHull_subset_of_form hH h
  · rw [pktHull_of_not_relCompact hU, pktHull_univ]

/-- The domain on which (P1) to (P3) are checked: relatively compact sets with nonzero
coordinate projections. A choice; the paper's `ℙ` is the set of direct product regions. -/
def pktHullDomain : Set (Set (∀ s, L s)) := {U | IsCompact (closure U) ∧ pktHullNondeg U}

/-- **Remark 3.9.5 (ii), page 127, for this hull**: with `𝓗` the sets `λ · 𝒪` and `𝓟` the
relatively compact sets with nonzero projections, `pktHull` maps `𝓟` into `𝓗` and satisfies
(P1), (P2), (P3), and `𝓗 ⊆ 𝓟`; proper, discretely valued factors. -/
theorem pktHull_isHullMap [∀ s, ProperSpace (L s)] :
    IsHullMap (pktHullDomain (L := L)) pktHullForms pktHull where
  hull_sub := by
    rintro _ ⟨c, rfl⟩
    refine ⟨?_, fun s => ⟨fun t => c t, pktHull_mem_principal.mpr fun t => le_rfl,
      (c s).ne_zero⟩⟩
    rw [(pktHull_isCompact_principal c).isClosed.closure_eq]
    exact pktHull_isCompact_principal c
  maps_to U hU := (pktHull_isLeast hd hU.1 hU.2).1.2
  P1 H hH := Set.Subset.antisymm (pktHull_subset_of_form hH le_rfl) (pktHull_extensive H)
  P2 U _ := pktHull_extensive U
  P3 _ _ _ _ h := pktHull_mono h

omit [Fintype ι] in
/-- **On all subsets (P1) to (P3) fail**: `univ` would have to be mapped to a set of the form
`λ · 𝒪`, but `pktHull univ = univ` is not of that form. Page 127 requires hulls to be proper
subsets (`H ⊊ ℐ^ℚ(−)`). -/
theorem pktHull_not_isHullMap_univ [Nonempty ι] :
    ¬ IsHullMap (Set.univ : Set (Set (∀ s, L s))) pktHullForms pktHull := by
  classical
  intro h
  obtain ⟨c, hc⟩ := h.maps_to Set.univ (Set.mem_univ _)
  rw [pktHull_univ] at hc
  obtain ⟨s₀⟩ := (inferInstance : Nonempty ι)
  obtain ⟨b, -, hb⟩ := pktHull_exists_large (hd s₀) (‖(c s₀ : L s₀)‖ + 1)
  have hmem : (Pi.single s₀ b : ∀ s, L s) ∈ pktHullPrincipal c := hc ▸ Set.mem_univ _
  have := pktHull_mem_principal.mp hmem s₀
  rw [Pi.single_eq_same] at this
  linarith

end Generic

/-! ## Measure: nondegeneracy and the log-volume of `λ · 𝒪` -/

section Measure

variable {ι : Type*} [Fintype ι] {L : ι → Type*} [∀ s, NormedField (L s)]
  [∀ s, MeasurableSpace (L s)]

/-- **Positive measure implies nonzero projections**: if the product of measures with no mass
at `0` gives `U` positive (outer) measure, then no coordinate projection of `U` is zero. -/
theorem pktHullNondeg_of_measure (μ : ∀ s, Measure (L s)) [∀ s, SigmaFinite (μ s)]
    (h0 : ∀ s, μ s {0} = 0) {U : Set (∀ s, L s)} (hU : Measure.pi μ U ≠ 0) :
    pktHullNondeg U := by
  classical
  intro s
  by_contra hcon
  push Not at hcon
  apply hU
  have hsub : U ⊆ Set.univ.pi
      (Function.update (fun t => (Set.univ : Set (L t))) s ({0} : Set (L s))) := by
    intro x hx t _
    rcases eq_or_ne t s with rfl | hts
    · simp [hcon x hx]
    · simp [Function.update_of_ne hts]
  refine measure_mono_null hsub ?_
  rw [Measure.pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [h0 s])

/-- **Haar measure of `λ · 𝒪`**: under the scaling law `μ_s(y • A) = ‖y‖ ^ d_s μ_s(A)`, the
product measure of `λ · 𝒪` is `∏_s ‖λ_s‖ ^ d_s μ_s(𝒪_s)`. -/
theorem pktHull_measure_principal (d : ι → ℕ) (μ : ∀ s, Measure (L s))
    [∀ s, SigmaFinite (μ s)]
    (hsc : ∀ s (y : L s), y ≠ 0 → ∀ A : Set (L s),
      μ s (y • A) = ((‖y‖₊ ^ d s : NNReal) : ENNReal) * μ s A)
    (c : ∀ s, (L s)ˣ) :
    Measure.pi μ (pktHullPrincipal c) =
      ∏ s, ((‖(c s : L s)‖₊ ^ d s : NNReal) : ENNReal) * μ s {y | ‖y‖ ≤ 1} := by
  have hpi : pktHullPrincipal c =
      Set.univ.pi (fun s => ((c s : (L s)ˣ) : L s) • {y : L s | ‖y‖ ≤ 1}) := by
    ext x
    rw [pktHull_mem_principal, Set.mem_univ_pi]
    refine forall_congr' fun s => ?_
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (c s).ne_zero, Set.mem_ofPred_eq, smul_eq_mul,
      norm_mul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.mpr (c s).ne_zero), mul_one]
  rw [hpi, Measure.pi_pi]
  exact Finset.prod_congr rfl fun s _ => hsc s _ (c s).ne_zero _

end Measure

/-! ## Finite extensions of `ℚ_p` with the spectral norm -/

section Spectral

variable (p : ℕ) [hp : Fact p.Prime]

/-- **`ℚ_p` is discretely valued**, with `ϖ = p`. -/
theorem pktHullDiscrete_padic : pktHullDiscrete ℚ_[p] := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  refine ⟨(p : ℚ_[p]), ?_, ?_, fun x hx => ⟨x.valuation, ?_⟩⟩
  · rw [Padic.norm_p]; positivity
  · rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ hp1
  · rw [Padic.norm_p, Padic.norm_eq_zpow_neg_valuation hx, inv_zpow']

/-- **A finite extension of `ℚ_p` with its spectral norm is discretely valued** (from the
uniformizer of `IUT.PaperIV.LocalFields.padicBridge_uniformizer`). -/
theorem pktHullDiscrete_spectral (K : Type*) [Field K] [Algebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] :
    letI := spectralNorm.normedField ℚ_[p] K
    pktHullDiscrete K := by
  let := spectralNorm.normedField ℚ_[p] K
  have := padicBridge_isLocalRing p K
  have := padicBridge_maximalIdeal_liesOver p K
  obtain ⟨ϖ, -, -, -, h0, h1, -, hval, -⟩ :=
    padicBridge_uniformizer p K (IsLocalRing.maximalIdeal (integralClosure ℤ_[p] K))
  exact ⟨ϖ, h0, h1, hval⟩

/-- For a finite extension with its spectral norm and any Haar measure, `{0}` is a null set. -/
theorem pktHull_haar_singleton_zero (K : Type*) [Field K] [Algebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] :
    letI := spectralNorm.normedField ℚ_[p] K
    letI := spectralNorm.normedAlgebra ℚ_[p] K
    letI : MeasurableSpace K := borel K
    ∀ (μ : Measure K) [μ.IsAddHaarMeasure], μ {0} = 0 := by
  let := spectralNorm.normedField ℚ_[p] K
  let := spectralNorm.normedAlgebra ℚ_[p] K
  let _ : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  have : ProperSpace K := FiniteDimensional.proper ℚ_[p] K
  intro μ _
  obtain ⟨ϖ, h0, h1, -⟩ := pktHullDiscrete_spectral p K
  have hϖ : ϖ ≠ 0 := norm_pos_iff.mp h0
  have hsc := volBridge_measure_smul p K hϖ {0} μ
  rw [Set.smul_set_singleton, smul_zero] at hsc
  have htop : μ {0} ≠ ⊤ := (isCompact_singleton.measure_lt_top).ne
  have hd : 0 < Module.finrank ℚ_[p] K := Module.finrank_pos
  have hr : ‖ϖ‖ ^ Module.finrank ℚ_[p] K < 1 := pow_lt_one₀ (norm_nonneg _) h1 hd.ne'
  have hreal : (μ {0}).toReal = ‖ϖ‖ ^ Module.finrank ℚ_[p] K * (μ {0}).toReal := by
    conv_lhs => rw [hsc]
    rw [ENNReal.toReal_mul]
    simp
  have hz : (μ {0}).toReal = 0 := by
    have hnn := ENNReal.toReal_nonneg (a := μ {0})
    nlinarith
  rcases (ENNReal.toReal_eq_zero_iff _).mp hz with h | h
  · exact h
  · exact absurd h htop

variable {ι : Type*} [Fintype ι] (L : ι → Type*) [∀ s, Field (L s)] [∀ s, Algebra ℚ_[p] (L s)]
  [∀ s, FiniteDimensional ℚ_[p] (L s)] [∀ s, Algebra ℤ_[p] (L s)]
  [∀ s, IsScalarTower ℤ_[p] ℚ_[p] (L s)]

omit [Fintype ι] in
/-- The integral structure `𝒪 = Π s, 𝒪_{L_s}` is the product of the rings of integers
`integralClosure ℤ_p L_s`. -/
theorem pktHullIntegers_eq_pi_integralClosure :
    letI : ∀ s, NormedField (L s) := fun s => spectralNorm.normedField ℚ_[p] (L s)
    (pktHullIntegers : Set (∀ s, L s)) =
      Set.univ.pi (fun s => ((integralClosure ℤ_[p] (L s) : Subalgebra ℤ_[p] (L s)) :
        Set (L s))) := by
  let _ : ∀ s, NormedField (L s) := fun s => spectralNorm.normedField ℚ_[p] (L s)
  ext x
  simp only [pktHullIntegers, Set.mem_ofPred_eq, Set.mem_univ_pi]
  exact forall_congr' fun s => (padicBridge_mem_integralClosure_iff p (L s) (x s)).symm

/-- **Remark 3.9.5 (i), page 127, for a finite product of finite extensions of `ℚ_p`**: for every
additive Haar measure on each factor and every relatively compact `U` containing a subset of
positive product measure, `pktHull U` is the smallest set of the form `λ · 𝒪` containing `U`. -/
theorem pktHull_isLeast_spectral :
    letI : ∀ s, NormedField (L s) := fun s => spectralNorm.normedField ℚ_[p] (L s)
    letI : ∀ s, NormedAlgebra ℚ_[p] (L s) := fun s => spectralNorm.normedAlgebra ℚ_[p] (L s)
    letI : ∀ s, MeasurableSpace (L s) := fun s => borel (L s)
    ∀ (μ : ∀ s, Measure (L s)) [∀ s, (μ s).IsAddHaarMeasure] (U : Set (∀ s, L s)),
      IsCompact (closure U) → (∃ K ⊆ U, Measure.pi μ K ≠ 0) →
      IsLeast {H | U ⊆ H ∧ H ∈ pktHullForms} (pktHull U) := by
  let _ : ∀ s, NormedField (L s) := fun s => spectralNorm.normedField ℚ_[p] (L s)
  let _ : ∀ s, NormedAlgebra ℚ_[p] (L s) := fun s => spectralNorm.normedAlgebra ℚ_[p] (L s)
  let _ : ∀ s, MeasurableSpace (L s) := fun s => borel (L s)
  have _ : ∀ s, BorelSpace (L s) := fun s => ⟨rfl⟩
  have _ : ∀ s, ProperSpace (L s) := fun s => FiniteDimensional.proper ℚ_[p] (L s)
  intro μ _ U hU ⟨K, hKU, hK⟩
  have hn : pktHullNondeg K :=
    pktHullNondeg_of_measure μ (fun s => pktHull_haar_singleton_zero p (L s) (μ s)) hK
  exact pktHull_isLeast (fun s => pktHullDiscrete_spectral p (L s)) hU
    fun s => let ⟨x, hx, h⟩ := hn s; ⟨x, hKU hx, h⟩

/-- **(P1) to (P3) for finite extensions of `ℚ_p`**, on relatively compact sets with nonzero
projections. -/
theorem pktHull_isHullMap_spectral :
    letI : ∀ s, NormedField (L s) := fun s => spectralNorm.normedField ℚ_[p] (L s)
    IsHullMap (pktHullDomain (L := L)) pktHullForms pktHull := by
  let _ : ∀ s, NormedField (L s) := fun s => spectralNorm.normedField ℚ_[p] (L s)
  let _ : ∀ s, NormedAlgebra ℚ_[p] (L s) := fun s => spectralNorm.normedAlgebra ℚ_[p] (L s)
  have _ : ∀ s, ProperSpace (L s) := fun s => FiniteDimensional.proper ℚ_[p] (L s)
  exact pktHull_isHullMap (fun s => pktHullDiscrete_spectral p (L s))

/-- **Log-volume of `λ · 𝒪`**: for finite extensions `L_s` of `ℚ_p` of degrees `d_s`, Haar
measures `μ_s` and the product measure on `V = Π s, L s` (of dimension `D = Σ d_s`), the
normalized log-volume `padicMuLog` normalized at `𝒪` is
`μ^log(λ · 𝒪) = (Σ_s d_s log ‖λ_s‖) / D`: the average of the `log ‖λ_s‖` with weights
`d_s / D`. -/
theorem pktHull_muLog_principal :
    letI : ∀ s, NormedField (L s) := fun s => spectralNorm.normedField ℚ_[p] (L s)
    letI : ∀ s, NormedAlgebra ℚ_[p] (L s) := fun s => spectralNorm.normedAlgebra ℚ_[p] (L s)
    letI : ∀ s, MeasurableSpace (L s) := fun s => borel (L s)
    ∀ (μ : ∀ s, Measure (L s)) [∀ s, (μ s).IsAddHaarMeasure] (c : ∀ s, (L s)ˣ),
      padicMuLog p (Measure.pi μ) pktHullIntegers (pktHullPrincipal c) =
        (∑ s, (Module.finrank ℚ_[p] (L s) : ℝ) * Real.log ‖((c s : (L s)ˣ) : L s)‖) /
          ∑ s, (Module.finrank ℚ_[p] (L s) : ℝ) := by
  let _ : ∀ s, NormedField (L s) := fun s => spectralNorm.normedField ℚ_[p] (L s)
  let _ : ∀ s, NormedAlgebra ℚ_[p] (L s) := fun s => spectralNorm.normedAlgebra ℚ_[p] (L s)
  let _ : ∀ s, MeasurableSpace (L s) := fun s => borel (L s)
  have _ : ∀ s, BorelSpace (L s) := fun s => ⟨rfl⟩
  have _ : ∀ s, ProperSpace (L s) := fun s => FiniteDimensional.proper ℚ_[p] (L s)
  intro μ _ c
  have hsc : ∀ s (y : L s), y ≠ 0 → ∀ A : Set (L s),
      μ s (y • A) = ((‖y‖₊ ^ Module.finrank ℚ_[p] (L s) : NNReal) : ENNReal) * μ s A :=
    fun s y hy A => volBridge_measure_smul p (L s) hy A (μ s)
  have hball : ∀ s, μ s {y : L s | ‖y‖ ≤ 1} ≠ 0 ∧ μ s {y : L s | ‖y‖ ≤ 1} ≠ ⊤ := by
    intro s
    obtain ⟨h0, h1, -⟩ := volBridge_muLog_integralClosure p (L s) (μ s)
    rw [padicBridge_integralClosure_eq_unitBall p (L s)] at h0 h1
    exact ⟨h0, h1⟩
  have hO := pktHull_measure_principal (fun s => Module.finrank ℚ_[p] (L s)) μ hsc 1
  rw [pktHullPrincipal_one] at hO
  have hC := pktHull_measure_principal (fun s => Module.finrank ℚ_[p] (L s)) μ hsc c
  unfold padicMuLog
  rw [hO, hC, Module.finrank_pi_fintype, Nat.cast_sum]
  simp only [Units.val_one, Pi.one_apply, nnNorm_one, one_pow, ENNReal.coe_one, one_mul]
  rw [ENNReal.toReal_prod, ENNReal.toReal_prod, ← Finset.prod_div_distrib]
  congr 1
  have hterm : ∀ s, (((‖(c s : L s)‖₊ ^ Module.finrank ℚ_[p] (L s) : NNReal) : ENNReal) *
      μ s {y : L s | ‖y‖ ≤ 1}).toReal / (μ s {y : L s | ‖y‖ ≤ 1}).toReal =
      ‖(c s : L s)‖ ^ Module.finrank ℚ_[p] (L s) := by
    intro s
    have hpos := ENNReal.toReal_pos (hball s).1 (hball s).2
    rw [ENNReal.toReal_mul, mul_div_assoc, div_self hpos.ne', mul_one]
    simp
  simp_rw [hterm]
  rw [Real.log_prod fun s _ => pow_ne_zero _ (norm_pos_iff.mpr (c s).ne_zero).ne']
  simp_rw [Real.log_pow]

/-- **Log-volume of the hull**: for relatively compact `U` with nonzero projections, with
`x_s ∈ U` a point whose `s`-th coordinate has the largest norm,
`μ^log(pktHull U) = (Σ_s d_s log ‖(x_s)_s‖) / D`. -/
theorem pktHull_muLog_hull :
    letI : ∀ s, NormedField (L s) := fun s => spectralNorm.normedField ℚ_[p] (L s)
    letI : ∀ s, NormedAlgebra ℚ_[p] (L s) := fun s => spectralNorm.normedAlgebra ℚ_[p] (L s)
    letI : ∀ s, MeasurableSpace (L s) := fun s => borel (L s)
    ∀ (μ : ∀ s, Measure (L s)) [∀ s, (μ s).IsAddHaarMeasure] (U : Set (∀ s, L s)),
      IsCompact (closure U) → pktHullNondeg U →
      ∃ x : ι → ∀ s, L s, (∀ s, x s ∈ U ∧ ∀ y ∈ U, ‖y s‖ ≤ ‖x s s‖) ∧
        padicMuLog p (Measure.pi μ) pktHullIntegers (pktHull U) =
          (∑ s, (Module.finrank ℚ_[p] (L s) : ℝ) * Real.log ‖x s s‖) /
            ∑ s, (Module.finrank ℚ_[p] (L s) : ℝ) := by
  let _ : ∀ s, NormedField (L s) := fun s => spectralNorm.normedField ℚ_[p] (L s)
  let _ : ∀ s, NormedAlgebra ℚ_[p] (L s) := fun s => spectralNorm.normedAlgebra ℚ_[p] (L s)
  let _ : ∀ s, MeasurableSpace (L s) := fun s => borel (L s)
  intro μ _ U hU hn
  obtain ⟨c, hc, hmax⟩ := pktHull_eq_principal (fun s => pktHullDiscrete_spectral p (L s)) hU hn
  choose x hx hcx hxmax using hmax
  refine ⟨x, fun s => ⟨hx s, hxmax s⟩, ?_⟩
  rw [hc, pktHull_muLog_principal p L μ c]
  simp_rw [hcx]

end Spectral

/-! ## Tests on `ℚ_p²` -/

section Test

variable (p : ℕ) [hp : Fact p.Prime]

/-- **`ℚ_p × ℤ_p` in `ℚ_p²`: the two definitions differ.** For `U = {x | ‖x₁‖ ≤ 1}`, the hull
of page 127 is the whole space `ℚ_p²`, because `U` is not relatively compact; the polydisc hull
`dhHull` of the coordinate suprema of norms has radii `∞` and `1` and is `U` itself, which is
not the whole space. A difference between two definitions on an unbounded set. -/
theorem pktHull_dhHull_padic_test :
    let U : Set (Fin 2 → ℚ_[p]) := {x | ‖x 1‖ ≤ 1}
    pktHull (L := fun _ : Fin 2 => ℚ_[p]) U = Set.univ ∧
      dhPolyRadius (X := fun _ : Fin 2 => ℚ_[p]) U 0 = ⊤ ∧
      dhPolyRadius (X := fun _ : Fin 2 => ℚ_[p]) U 1 = 1 ∧
      dhHull (X := fun _ : Fin 2 => ℚ_[p]) U = U ∧ U ≠ Set.univ := by
  intro U
  have hd := pktHullDiscrete_padic p
  have hR1 : dhPolyRadius (X := fun _ : Fin 2 => ℚ_[p]) U 1 = 1 := by
    apply le_antisymm
    · exact iSup₂_le fun x hx => ENNReal.ofReal_le_one.mpr hx
    · have hx : (Pi.single 1 1 : Fin 2 → ℚ_[p]) ∈ U := by simp [U]
      calc (1 : ENNReal) = ENNReal.ofReal ‖(Pi.single 1 1 : Fin 2 → ℚ_[p]) 1‖ := by simp
        _ ≤ _ := le_iSup₂ (f := fun x (_ : x ∈ U) => ENNReal.ofReal ‖x 1‖) _ hx
  refine ⟨?_, ?_, hR1, ?_, ?_⟩
  · apply pktHull_of_not_isBounded
    intro hb
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
    obtain ⟨b, -, hbC⟩ := pktHull_exists_large hd (C + 1)
    have hx : (Pi.single 0 b : Fin 2 → ℚ_[p]) ∈ U := by simp [U]
    have := (norm_le_pi_norm (Pi.single 0 b : Fin 2 → ℚ_[p]) 0).trans (hC _ hx)
    rw [Pi.single_eq_same] at this
    linarith
  · refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
    obtain ⟨b, -, hbr⟩ := pktHull_exists_large hd (r : ℝ)
    have hx : (Pi.single 0 b : Fin 2 → ℚ_[p]) ∈ U := by simp [U]
    calc (r : ENNReal) = ENNReal.ofReal (r : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
      _ ≤ ENNReal.ofReal ‖(Pi.single 0 b : Fin 2 → ℚ_[p]) 0‖ := by
          rw [Pi.single_eq_same]; exact ENNReal.ofReal_le_ofReal hbr
      _ ≤ _ := le_iSup₂ (f := fun x (_ : x ∈ U) => ENNReal.ofReal ‖x 0‖) _ hx
  · refine Set.Subset.antisymm (fun y hy => ?_) (dh_subset_hull U)
    have := hy 1
    rw [hR1] at this
    exact ENNReal.ofReal_le_one.mp this
  · intro h
    have hx : (Pi.single 1 (p : ℚ_[p])⁻¹ : Fin 2 → ℚ_[p]) ∈ U := h ▸ Set.mem_univ _
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    simp only [U, Set.mem_ofPred_eq, Pi.single_eq_same, norm_inv, Padic.norm_p, inv_inv] at hx
    linarith

/-- **The hull of a union can be strictly larger than the union of the hulls**: in `ℚ_p²`, for
`v = (1, p)` and `w = (p, 1)`, the point `(1, 1)` lies in `pktHull ({v} ∪ {w})` but in neither
`pktHull {v}` nor `pktHull {w}`. -/
theorem pktHull_union_strict_padic :
    let v : Fin 2 → ℚ_[p] := ![1, (p : ℚ_[p])]
    let w : Fin 2 → ℚ_[p] := ![(p : ℚ_[p]), 1]
    (fun _ => 1 : Fin 2 → ℚ_[p]) ∈ pktHull (L := fun _ : Fin 2 => ℚ_[p]) ({v} ∪ {w}) ∧
      (fun _ => 1 : Fin 2 → ℚ_[p]) ∉ pktHull (L := fun _ : Fin 2 => ℚ_[p]) {v} ∧
      (fun _ => 1 : Fin 2 → ℚ_[p]) ∉ pktHull (L := fun _ : Fin 2 => ℚ_[p]) {w} := by
  intro v w
  have hd : ∀ _ : Fin 2, pktHullDiscrete ℚ_[p] := fun _ => pktHullDiscrete_padic p
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  refine ⟨?_, ?_, ?_⟩
  · have hU : IsCompact (closure ({v} ∪ {w} : Set (Fin 2 → ℚ_[p]))) := by
      rw [closure_union, closure_singleton, closure_singleton]
      exact isCompact_singleton.union isCompact_singleton
    rw [pktHull_of_relCompact hU, pktHull_mem_sInter_iff hd (pktHull_isBounded_of_relCompact hU)]
    intro s c _ hc
    fin_cases s
    · simpa [v] using hc v (Or.inl rfl)
    · simpa [w] using hc w (Or.inr rfl)
  · rw [pktHull_singleton hd]
    intro h
    have := h 1
    simp [v, Padic.norm_p] at this
    linarith
  · rw [pktHull_singleton hd]
    intro h
    have := h 0
    simp [w, Padic.norm_p] at this
    linarith

end Test

end IUT.PaperIII.Corollary312
