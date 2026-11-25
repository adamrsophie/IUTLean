import Mathlib

/-!
# IUT II: the label sets `|𝔽_l|`, `𝔽_l^⋇` and the exponents `j²` of the theta values

Sources, all read for this file, with every formula below checked against a rendered page:

* Mochizuki, *Inter-universal Teichmüller Theory I*, page 3 (rendered): the definitions
  `l^⋇ = (l − 1)/2` and `𝔽_l^⋇ = 𝔽_l^× / {±1}`.
* *Inter-universal Teichmüller Theory II*, page 3 (rendered): `j ∈ {0, 1, …, l^⋇}` is uniquely
  determined by its image in `|𝔽_l| = 𝔽_l / {±1} = {0} ∪ 𝔽_l^⋇`.
* IUT II, Remark 2.5.1 (i), page 72 (rendered): the theta value attached to `j ∈ |𝔽_l|` is
  `qq_v^{j²}` with `j ∈ {0, 1, …, l^⋇}` the representative of `j`. Here `qq_v` (a `q` with a
  double underline in the paper) is not the Tate parameter `q_v` of `E_v`: by IUT I, Example
  3.2 (iv), page 71 (rendered), `qq_v = q_v^{1/2l}`, a chosen `2l`-th root determined up to a
  `μ_{2l}`-multiple. Relative to the Tate parameter the theta value is `q_v^{j²/(2l)}`. The
  exponents treated in this file are the `j²` attached to `qq_v`.
* IUT II, Proposition 4.1 (iv), page 122, and Remark 4.5.4, page 136 (both rendered): the
  Gaussian monoid carries the exponent vector `(…, j² · log(p_v), …)` indexed by `j ∈ 𝔽_l^⋇`,
  with `j` read as a natural number in `{1, …, l^⋇}`.
* IUT II, Remark 4.7.3 (iii), page 145 (rendered): the volume at each `j ∈ 𝔽_l^⋇` gets
  weight `1/l^⋇`.
* IUT II, Remark 2.6.3 (ii), pages 79 and 80 (rendered): the quantity
  `‖Γ′‖ = |Γ′|⁻¹ · ∑_{j ∈ 𝔽_l^⋇} min_{j ∈ j ∩ Γ′} j²` and claim (d) about it.

## What this file is and is not

**This file is not a formalization of any theorem about theta functions or Gaussian monoids.**
It checks elementary facts about the labels and the exponents that these constructions use:

1. `|𝔽_l|` (defined as the quotient of `ZMod l` by `x ∼ ±x`) is in bijection with
   `{0, 1, …, l^⋇}` for odd `l` (page 3 of IUT II), so it has `l^⋇ + 1` elements and
   `l^⋇` nonzero elements.
2. `𝔽_l^⋇ = 𝔽_l^× / {±1}` (IUT I, page 3) has `l^⋇` elements for an odd prime `l`.
3. `24 · ∑_{j=1}^{l^⋇} j² = l (l² − 1)` and the `1/l^⋇`-weighted average of the exponents
   `j²` equals `l (l + 1) / 12`. **Neither formula appears in the pages read**; they are
   elementary arithmetic about the exponent vector of pages 122, 136, 145.
4. Remark 2.6.3: for a finite connected subgraph `Γ′ ≠ {0}` of the line graph containing `0`,
   i.e. a vertex set `[−a, b] ⊆ ℤ` with `max(a, b) ≥ 1`, the file computes `|Γ′| = min(max(a,b), l^⋇)` and
   `‖Γ′‖ = (n + 1)(2n + 1)/6` with `n = |Γ′|`, so `‖Γ′‖` is a function of `|Γ′|`, strictly
   increasing in it, monotone in `max(a,b)`, and maximal (value `l (l + 1)/12`) exactly when
   `max(a,b) ≥ l^⋇`. The paper calls this "easily verified"; the file verifies it.

Interpretation choices (recorded in `data/curated/iut2.json`, record `IUT2.Rem2_6_3`):

* The paper assumes `l ≥ 5` prime. Facts 1, 3, 4 are proved for every odd `l ≥ 3`; fact 2 for
  every odd prime.
* An element of `𝔽_l^⋇` is represented by its unique representative `c ∈ {1, …, l^⋇}`
  (justified by fact 1); its fiber in `ℤ` is `{k | k ≡ c or k ≡ −c mod l}`.
* "Min over the empty set is zero" and "`|Γ′|` is the number of classes `c ∈ 𝔽_l^⋇` hit by
  `Γ′`" are taken literally from page 79. Nonzero vertices divisible by `l` map to `0 ∉ 𝔽_l^⋇`
  and are not counted.
* Page 80 (d) says "monotone increasing [but not strictly increasing!] function of `|Γ′|` …
  constant for `|Γ′| ≥ l^⋇`". Since `|Γ′| ≤ l^⋇` by definition, the literal reading gives a
  strictly increasing function (`gammaNormValue_strictMono`); the parenthetical and the
  constancy match the reading in terms of the radius `max(a,b)`
  (`gammaNorm_eq_max_iff`, `gammaNorm_mono_radius`, `gammaNorm_le_max`). Both are proved; neither is imposed.
* Infinite `Γ′` (Remark 2.6.3 (iii)) is not treated.
-/

namespace IUT.PaperII.Labels

open Finset

/-! ## The label sets -/

/-- `l^⋇ = (l − 1)/2` (IUT I, page 3). -/
def lstar (l : ℕ) : ℕ := (l - 1) / 2

/-- The relation `x ∼ y ⟺ x = y ∨ x = −y` on `𝔽_l = ZMod l`, whose quotient is `|𝔽_l|`. -/
def pmSetoid (l : ℕ) : Setoid (ZMod l) where
  r x y := x = y ∨ x = -y
  iseqv := by
    refine ⟨fun x => Or.inl rfl, ?_, ?_⟩
    · rintro x y (h | h)
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h, neg_neg])
    · rintro x y z (h | h) (h' | h')
      · exact Or.inl (h.trans h')
      · exact Or.inr (h.trans h')
      · exact Or.inr (by rw [h, h'])
      · exact Or.inl (by rw [h, h', neg_neg])

/-- `|𝔽_l| = 𝔽_l / {±1}` (IUT II, page 3). -/
def AbsLabel (l : ℕ) : Type := Quotient (pmSetoid l)

/-- The class in `|𝔽_l|` of `j ∈ {0, 1, …, l^⋇}`. -/
def labelRep (l : ℕ) (j : Fin (lstar l + 1)) : AbsLabel l :=
  Quotient.mk (pmSetoid l) ((j : ℕ) : ZMod l)

/-- If `l ∣ x` and `|x| < l` then `x = 0`; the basic step used throughout. -/
private lemma eq_zero_of_dvd_of_lt {l : ℕ} {x : ℤ} (h : (l : ℤ) ∣ x) (hx : |x| < l) : x = 0 :=
  Int.eq_zero_of_abs_lt_dvd h hx

/-- IUT II, page 3: for odd `l`, every class in `|𝔽_l|` has exactly one representative in
`{0, 1, …, l^⋇}`. -/
theorem labelRep_bijective {l : ℕ} (hl : Odd l) : Function.Bijective (labelRep l) := by
  obtain ⟨k, rfl⟩ := hl
  have hk : lstar (2 * k + 1) = k := by simp [lstar]
  constructor
  · intro i j hij
    have hi : (i : ℕ) ≤ k := by have := i.2; omega
    have hj : (j : ℕ) ≤ k := by have := j.2; omega
    have h := Quotient.exact hij
    apply Fin.ext
    rcases h with h | h
    · have h' : (((i : ℕ) : ℤ) : ZMod (2 * k + 1)) = (((j : ℕ) : ℤ) : ZMod (2 * k + 1)) := by
        exact_mod_cast h
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h'
      have := eq_zero_of_dvd_of_lt h' (by rw [abs_lt]; push_cast; omega)
      omega
    · have h' : (((i : ℕ) : ℤ) : ZMod (2 * k + 1)) = ((-((j : ℕ) : ℤ) : ℤ) : ZMod (2 * k + 1)) := by
        push_cast; exact h
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h'
      have := eq_zero_of_dvd_of_lt h' (by rw [abs_lt]; push_cast; omega)
      omega
  · intro x
    induction x using Quotient.inductionOn with
    | h y =>
      have hv := ZMod.val_lt y
      by_cases hy : y.val ≤ k
      · refine ⟨⟨y.val, by rw [hk]; omega⟩, ?_⟩
        apply Quotient.sound
        exact Or.inl (by simp)
      · refine ⟨⟨2 * k + 1 - y.val, by rw [hk]; omega⟩, ?_⟩
        apply Quotient.sound
        right
        have : ((2 * k + 1 - y.val : ℕ) : ZMod (2 * k + 1)) = -((y.val : ℕ) : ZMod (2 * k + 1)) := by
          rw [Nat.cast_sub hv.le, ZMod.natCast_self, zero_sub]
        simp [this]

/-- `|𝔽_l|` has `l^⋇ + 1` elements for odd `l`. -/
theorem card_absLabel {l : ℕ} (hl : Odd l) : Nat.card (AbsLabel l) = lstar l + 1 := by
  rw [← Nat.card_eq_of_bijective _ (labelRep_bijective hl), Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- The zero label `0 ∈ |𝔽_l|`. -/
def zeroLabel (l : ℕ) : AbsLabel l := Quotient.mk (pmSetoid l) 0

/-- The decomposition `|𝔽_l| = {0} ∪ 𝔽_l^⋇` at the level of cardinalities: for odd `l` there are
exactly `l^⋇` nonzero labels. -/
theorem card_nonzero_absLabel {l : ℕ} (hl : Odd l) :
    Nat.card {x : AbsLabel l // x ≠ zeroLabel l} = lstar l := by
  have hb := labelRep_bijective hl
  have h0 : labelRep l 0 = zeroLabel l := by
    unfold labelRep zeroLabel; congr 1; simp
  let e : {j : Fin (lstar l + 1) // j ≠ 0} ≃ {x : AbsLabel l // x ≠ zeroLabel l} :=
    (Equiv.ofBijective _ hb).subtypeEquiv (fun j => by
      simp only [Equiv.ofBijective_apply, ← h0]
      exact hb.1.ne_iff.symm)
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_fin, Fintype.card_unique]
  simp

/-- `𝔽_l^⋇ = 𝔽_l^× / {±1}` (IUT I, page 3), with `{±1}` the subgroup generated by `−1`. -/
abbrev FlStar (l : ℕ) : Type := (ZMod l)ˣ ⧸ Subgroup.zpowers (-1 : (ZMod l)ˣ)

/-- For an odd prime `l`, `𝔽_l^⋇` has `l^⋇ = (l − 1)/2` elements. -/
theorem card_flStar {l : ℕ} [hp : Fact l.Prime] (hl : l ≠ 2) : Nat.card (FlStar l) = lstar l := by
  have hord : orderOf (-1 : (ZMod l)ˣ) = 2 := by
    rw [← orderOf_units, Units.val_neg, Units.val_one, orderOf_neg_one, ZMod.ringChar_zmod_n,
      ite_eq_right_iff.mpr (fun h => absurd h hl)]
  have h := (Subgroup.zpowers (-1 : (ZMod l)ˣ)).index_mul_card
  rw [Nat.card_zpowers, hord, Nat.card_eq_fintype_card (α := (ZMod l)ˣ), ZMod.card_units] at h
  rw [lstar, ← h]
  simp [Subgroup.index]

/-! ## The exponents `j²`, `j = 1, …, l^⋇` -/

/-- `6 · ∑_{j=1}^{n} j² = n (n + 1) (2n + 1)`. -/
theorem six_mul_sum_sq (n : ℕ) : 6 * ∑ j ∈ Icc 1 n, j ^ 2 = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    ring

/-- The exponents `j²`, `j = 1, …, l^⋇`, of the Gaussian monoid (IUT II, pages 122, 136)
satisfy `24 · ∑ j² = l (l² − 1)` for odd `l`. Elementary; not stated in the paper. -/
theorem sum_exponents {l : ℕ} (hl : Odd l) :
    24 * ∑ j ∈ Icc 1 (lstar l), j ^ 2 = l * (l ^ 2 - 1) := by
  obtain ⟨k, rfl⟩ := hl
  have hk : lstar (2 * k + 1) = k := by simp [lstar]
  rw [hk, show 24 = 4 * 6 by rfl, mul_assoc, six_mul_sum_sq]
  have : (2 * k + 1) ^ 2 - 1 = 4 * k * (k + 1) := by
    rw [Nat.sub_eq_of_eq_add]; ring
  rw [this]; ring

/-- With weight `1/l^⋇` at each `j ∈ 𝔽_l^⋇` (IUT II, Remark 4.7.3 (iii), page 145), the
weighted total of the exponents `j²` is `l (l + 1)/12`, for odd `l ≥ 3`. Elementary; not stated
in the paper. -/
theorem average_exponents {l : ℕ} (hl : Odd l) (h3 : 3 ≤ l) :
    (∑ j ∈ Icc 1 (lstar l), (j : ℚ) ^ 2) / lstar l = l * (l + 1) / 12 := by
  obtain ⟨k, rfl⟩ := hl
  have hk : lstar (2 * k + 1) = k := by simp [lstar]
  have hk0 : (k : ℚ) ≠ 0 := by norm_cast; omega
  have h6 : (6 : ℚ) * ∑ j ∈ Icc 1 k, (j : ℚ) ^ 2 = k * (k + 1) * (2 * k + 1) := by
    exact_mod_cast six_mul_sum_sq k
  rw [hk, div_eq_iff hk0]
  push_cast
  linear_combination h6 / 6

/-! ## Remark 2.6.3: the quantity `‖Γ′‖` for `Γ′ = [−a, b]` -/

/-- The intersection of `Γ′ = [−a, b]` with the fiber over the class of `c` of the projection
`ℤ → |𝔽_l|`, i.e. the integers `k ∈ [−a, b]` with `k ≡ ±c (mod l)`. -/
def fiberIn (l a b c : ℕ) : Finset ℤ :=
  (Icc (-(a : ℤ)) b).filter fun k => (k : ZMod l) = (c : ZMod l) ∨ (k : ZMod l) = -(c : ZMod l)

/-- `min_{k ∈ S} k²`, with the convention of page 79 that the min over the empty set is `0`. -/
def minSq (S : Finset ℤ) : ℕ :=
  if h : S.Nonempty then (S.image fun k => k.natAbs ^ 2).min' (h.image _) else 0

/-- `|Γ′|`: the number of classes `c ∈ 𝔽_l^⋇` (represented by `c ∈ {1, …, l^⋇}`) that contain a
vertex of `Γ′ = [−a, b]`, i.e. the size of the image in `𝔽_l^⋇` of the nonzero vertices. -/
def gammaCard (l a b : ℕ) : ℕ := ((Icc 1 (lstar l)).filter fun c => (fiberIn l a b c).Nonempty).card

/-- `‖Γ′‖ = |Γ′|⁻¹ · ∑_{c ∈ 𝔽_l^⋇} min_{k ∈ c ∩ Γ′} k²` (IUT II, page 79).

Domain: the paper's formula has a meaning only when `|Γ′| ≥ 1`, that is `Γ′ ≠ {0}`
(`one_le_gammaCard_iff`). For `a = b = 0` Lean's division by zero makes this function return
`0`; that value is a convention of the Lean definition, not a value given on page 79. Every
lemma below that evaluates `gammaNorm` assumes `1 ≤ gammaCard l a b` or `1 ≤ max a b`. -/
def gammaNorm (l a b : ℕ) : ℚ :=
  (∑ c ∈ Icc 1 (lstar l), (minSq (fiberIn l a b c) : ℚ)) / gammaCard l a b

/-- A vertex in the fiber of `c ∈ {1, …, l^⋇}` has absolute value at least `c`. -/
lemma le_natAbs_of_mem_fiber {l c : ℕ} (hl : Odd l) (hc : c ≤ lstar l) {k : ℤ}
    (hk : (k : ZMod l) = (c : ZMod l) ∨ (k : ZMod l) = -(c : ZMod l)) : c ≤ k.natAbs := by
  obtain ⟨m, rfl⟩ := hl
  have hm : lstar (2 * m + 1) = m := by simp [lstar]
  rw [hm] at hc
  by_contra hlt
  push Not at hlt
  have hka : |k| < c := by rw [Int.abs_eq_natAbs]; exact_mod_cast hlt
  rw [abs_lt] at hka
  rcases hk with h | h
  · have h' : (k : ZMod (2 * m + 1)) = (((c : ℤ)) : ZMod (2 * m + 1)) := by exact_mod_cast h
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h'
    have := eq_zero_of_dvd_of_lt h' (by rw [abs_lt]; push_cast; omega)
    omega
  · have h' : (k : ZMod (2 * m + 1)) = ((-(c : ℤ) : ℤ) : ZMod (2 * m + 1)) := by
      push_cast; exact h
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h'
    have := eq_zero_of_dvd_of_lt h' (by rw [abs_lt]; push_cast; omega)
    omega

/-- The fiber of `c ∈ {1, …, l^⋇}` meets `[−a, b]` if and only if `c ≤ max a b`. -/
lemma fiberIn_nonempty_iff {l a b c : ℕ} (hl : Odd l) (hc : c ≤ lstar l) :
    (fiberIn l a b c).Nonempty ↔ c ≤ max a b := by
  constructor
  · rintro ⟨k, hk⟩
    simp only [fiberIn, mem_filter, mem_Icc] at hk
    have := le_natAbs_of_mem_fiber hl hc hk.2
    omega
  · intro h
    rcases le_max_iff.mp h with h | h
    · exact ⟨-(c : ℤ), by simp [fiberIn]; omega⟩
    · exact ⟨(c : ℤ), by simp [fiberIn]; omega⟩

/-- When the fiber of `c ∈ {1, …, l^⋇}` meets `[−a, b]`, the minimum of `k²` over it is `c²`. -/
lemma minSq_fiberIn {l a b c : ℕ} (hl : Odd l) (hc : c ≤ lstar l) (h : c ≤ max a b) :
    minSq (fiberIn l a b c) = c ^ 2 := by
  have hne := (fiberIn_nonempty_iff hl hc).mpr h
  simp only [minSq, hne, ↓reduceDIte]
  apply le_antisymm
  · apply Finset.min'_le
    rw [mem_image]
    rcases le_max_iff.mp h with h' | h'
    · exact ⟨-(c : ℤ), by simp [fiberIn]; omega, by simp⟩
    · exact ⟨(c : ℤ), by simp [fiberIn]; omega, by simp⟩
  · apply Finset.le_min'
    intro y hy
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hy
    simp only [fiberIn, mem_filter] at hk
    exact Nat.pow_le_pow_left (le_natAbs_of_mem_fiber hl hc hk.2) 2

/-- `|Γ′| = min(max(a, b), l^⋇)`. -/
theorem gammaCard_eq {l : ℕ} (hl : Odd l) (a b : ℕ) :
    gammaCard l a b = min (max a b) (lstar l) := by
  rw [gammaCard]
  have : ((Icc 1 (lstar l)).filter fun c => (fiberIn l a b c).Nonempty) =
      Icc 1 (min (max a b) (lstar l)) := by
    ext c
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have := (fiberIn_nonempty_iff hl h2).mp h3
      omega
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, by omega⟩, (fiberIn_nonempty_iff hl (by omega)).mpr (by omega)⟩
  rw [this, Nat.card_Icc]
  omega

/-- `∑_{c ∈ 𝔽_l^⋇} min_{k ∈ c ∩ Γ′} k² = ∑_{c = 1}^{|Γ′|} c²`. -/
theorem sum_minSq_eq {l : ℕ} (hl : Odd l) (a b : ℕ) :
    ∑ c ∈ Icc 1 (lstar l), (minSq (fiberIn l a b c) : ℚ) =
      ∑ c ∈ Icc 1 (gammaCard l a b), (c : ℚ) ^ 2 := by
  rw [gammaCard_eq hl]
  have hsplit : ∀ c ∈ Icc 1 (lstar l), (minSq (fiberIn l a b c) : ℚ) =
      if c ≤ max a b then (c : ℚ) ^ 2 else 0 := by
    intro c hc
    have hc' := (mem_Icc.mp hc).2
    split_ifs with h
    · rw [minSq_fiberIn hl hc' h]; push_cast; ring
    · have : ¬ (fiberIn l a b c).Nonempty := fun h' => h ((fiberIn_nonempty_iff hl hc').mp h')
      simp [minSq, this]
  rw [Finset.sum_congr rfl hsplit, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext c
  simp only [mem_filter, mem_Icc]
  omega

/-- The closed form `g(n) = (n + 1)(2n + 1)/6`. -/
def gammaNormValue (n : ℕ) : ℚ := ((n : ℚ) + 1) * (2 * n + 1) / 6

/-- Remark 2.6.3 (d), first part: `‖Γ′‖` is a function of `|Γ′|` alone, namely
`‖Γ′‖ = (|Γ′| + 1)(2|Γ′| + 1)/6`, whenever `|Γ′| ≥ 1`. -/
theorem gammaNorm_eq {l : ℕ} (hl : Odd l) (a b : ℕ) (hpos : 1 ≤ gammaCard l a b) :
    gammaNorm l a b = gammaNormValue (gammaCard l a b) := by
  rw [gammaNorm, sum_minSq_eq hl, gammaNormValue]
  set n := gammaCard l a b
  have hn : (n : ℚ) ≠ 0 := by norm_cast; omega
  have h6 : (6 : ℚ) * ∑ j ∈ Icc 1 n, (j : ℚ) ^ 2 = n * (n + 1) * (2 * n + 1) := by
    exact_mod_cast six_mul_sum_sq n
  rw [div_eq_iff hn]
  linear_combination h6 / 6

/-- `|Γ′| ≥ 1` exactly when `Γ′ ≠ {0}`, for `l ≥ 3`. -/
theorem one_le_gammaCard_iff {l : ℕ} (hl : Odd l) (h3 : 3 ≤ l) (a b : ℕ) :
    1 ≤ gammaCard l a b ↔ 1 ≤ max a b := by
  have : 1 ≤ lstar l := by unfold lstar; omega
  rw [gammaCard_eq hl]; omega

/-- The literal reading of (d): as a function of `|Γ′|`, the value `‖Γ′‖` is strictly
increasing. Since `|Γ′| ≤ l^⋇`, its maximum is attained at `|Γ′| = l^⋇`. -/
theorem gammaNormValue_strictMono : StrictMono gammaNormValue := by
  intro m n h
  have h' : (m : ℚ) + 1 ≤ n := by exact_mod_cast h
  unfold gammaNormValue
  have hm : (0 : ℚ) ≤ m := by positivity
  nlinarith

/-- `|Γ′| ≤ l^⋇`. -/
theorem gammaCard_le {l : ℕ} (hl : Odd l) (a b : ℕ) : gammaCard l a b ≤ lstar l := by
  rw [gammaCard_eq hl]; exact min_le_right _ _

/-- The maximal value: `g(l^⋇) = l (l + 1)/12` for odd `l`. -/
theorem gammaNormValue_lstar {l : ℕ} (hl : Odd l) :
    gammaNormValue (lstar l) = l * (l + 1) / 12 := by
  obtain ⟨k, rfl⟩ := hl
  have hk : lstar (2 * k + 1) = k := by simp [lstar]
  rw [hk, gammaNormValue]; push_cast; ring

/-- The radius reading of (d): `‖Γ′‖ ≤ l (l + 1)/12` for every `Γ′ = [−a, b] ≠ {0}`. -/
theorem gammaNorm_le_max {l : ℕ} (hl : Odd l) (h3 : 3 ≤ l) (a b : ℕ) (hab : 1 ≤ max a b) :
    gammaNorm l a b ≤ l * (l + 1) / 12 := by
  rw [gammaNorm_eq hl a b ((one_le_gammaCard_iff hl h3 a b).mpr hab), ← gammaNormValue_lstar hl]
  exact gammaNormValue_strictMono.monotone (gammaCard_le hl a b)

/-- The radius reading of (d): the maximum `l (l + 1)/12` is attained exactly when
`max(a, b) ≥ l^⋇`, so `‖Γ′‖` is constant in the radius from `l^⋇` on. -/
theorem gammaNorm_eq_max_iff {l : ℕ} (hl : Odd l) (h3 : 3 ≤ l) (a b : ℕ) (hab : 1 ≤ max a b) :
    gammaNorm l a b = l * (l + 1) / 12 ↔ lstar l ≤ max a b := by
  rw [gammaNorm_eq hl a b ((one_le_gammaCard_iff hl h3 a b).mpr hab), ← gammaNormValue_lstar hl,
    gammaNormValue_strictMono.injective.eq_iff, gammaCard_eq hl]
  omega

/-- The radius reading of (d): `‖Γ′‖` is monotone in the radius `max(a, b)`. -/
theorem gammaNorm_mono_radius {l : ℕ} (hl : Odd l) (h3 : 3 ≤ l) {a b a' b' : ℕ}
    (hab : 1 ≤ max a b) (h : max a b ≤ max a' b') : gammaNorm l a b ≤ gammaNorm l a' b' := by
  rw [gammaNorm_eq hl a b ((one_le_gammaCard_iff hl h3 a b).mpr hab),
    gammaNorm_eq hl a' b' ((one_le_gammaCard_iff hl h3 a' b').mpr (hab.trans h))]
  apply gammaNormValue_strictMono.monotone
  rw [gammaCard_eq hl, gammaCard_eq hl]
  omega

end IUT.PaperII.Labels
