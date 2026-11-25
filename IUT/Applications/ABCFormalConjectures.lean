import IUT.Applications.ABC

/-!
# Comparison with the abc statements of the Formal Conjectures project

Source: the file `FormalConjectures/Wikipedia/ABC.lean` of
<https://github.com/google-deepmind/formal-conjectures>, at commit
`9097e2f90e66d2f6244209cb1c07f7120d17ec53` (2026-11-24). The file is byte-identical to the
version at commit `1646ca16afd6cc7a693d3bdc9f066c4d3cc01a89`, the commit cited by the
`lana-agents/iut` repository. The project is licensed under Apache-2.0
(Copyright 2025 The Formal Conjectures Authors).

That file cannot be imported here (it is a Lean module of a different project, on Lean
`v4.33.1`, and its theorems are stated with `sorry`). This file restates, in the namespace
`IUT.ABC.FormalConjectures`, their definitions `ABC.radical` and `ABC.quality` with the same
bodies, and turns each of their three open theorems into a definition of type `Prop` whose body
is the theorem statement with the arguments `(ε : ℝ) (hε : 0 < ε)` written as
`∀ ε : ℝ, 0 < ε →`; binders, set-builders and coercions are as in their file:

* `abc` (their `ABC.abc`): finiteness of the exceptional triples, with pairwise coprimality
  of the set `{a, b, c}`;
* `ltConstantMul` (their `ABC.abc.variants.lt_constant_mul`): a real constant `K`, with no
  sign condition, and the strict inequality `c < K * rad(abc)^(1 + ε)`;
* `qualityVariant` (their `ABC.abc.variants.quality`): finiteness of the triples of quality
  `q(a, b, c) = log c / log rad(abc)` greater than `1 + ε`.

Each is proved equivalent to `Challenge.ABC`. Nothing here says whether any of them holds.

Remarks on the formulations, all checked by the proofs below.

* Coprimality: for positive `a`, `b` with `a + b = c`, pairwise coprimality of `{a, b, c}` is
  coprimality of `a` and `b` (`IUT.ABC.coprime_iff_pairwise`).
* Constant form: `Challenge.ABC` asks for `0 < K` and the non-strict `≤`; theirs asks for no sign
  and the strict `<`. These are equivalent: the triple `1 + 1 = 2` forces `K > 0` in their form,
  and `K + 1` turns `≤` into `<` because `rad(abc)^(1 + ε) ≥ 1`.
* Quality form: Lean's division gives `x / 0 = 0`, so the quality is `0` when `rad(abc) = 1`.
  For positive `a`, `b` with `a + b = c` this never happens: `c ≥ 2`, so `rad(abc) ≥ 2`
  (`rad(abc) = 1` with `abc ≠ 0` forces `abc = 1`, hence `a = b = c = 1`, and `1 + 1 ≠ 1`).
  When `rad(abc) ≥ 2` the logarithm of the radical is positive, and `q > 1 + ε` is exactly
  `rad(abc)^(1 + ε) < c`. So, for each `ε`, the quality set is the same set as the set of the
  finiteness form (`qualitySet_eq`), and the quality form is exactly equivalent; no strict versus
  non-strict discrepancy arises, since both sets use strict inequalities.

No PDF page of the IUT papers is used in this file.
-/

namespace IUT.ABC.FormalConjectures

open Challenge

/-! ## Restated definitions (bodies as in `FormalConjectures/Wikipedia/ABC.lean`) -/

/-- The radical of `n` denoted is the product of the distinct prime factors of `n`.
(Their `ABC.radical`, same body.) -/
def radical (n : ℕ) : ℕ := n.primeFactors.prod id

/-- Quality `q(a, b, c)` of the triple `(a, b, c)` is defined as
`q(a,b,c) = log (c) / log (rad(abc))`. (Their `ABC.quality`, same body.) -/
noncomputable def quality (a b c : ℕ) : ℝ := (c : ℝ).log / (radical <| a * b * c : ℝ).log

/-- For every positive real number `ε`, there exist only finitely many triples `(a, b, c)` of
coprime positive integers, with `a + b = c`, such that `c > rad(abc)^(1+ε)`.
(Statement of their theorem `ABC.abc`.) -/
def abc : Prop := ∀ ε : ℝ, 0 < ε →
    {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧
    a + b = c ∧ (radical <| a * b * c : ℝ)^(1 + ε) < c}.Finite

/-- For every positive real number ε, there exists a constant `K_ε` such that for all triples
(a, b, c) of coprime positive integers, with a + b = c we have `c < K_ε rad(abc)^(1+ε)`.
(Statement of their theorem `ABC.abc.variants.lt_constant_mul`.) -/
def ltConstantMul : Prop := ∀ ε : ℝ, 0 < ε → ∃ K,
    ∀ (a b c : ℕ), 0 < a → 0 < b → 0 < c → ({a, b, c} : Set ℕ).Pairwise Nat.Coprime →
    a + b = c → c < K * (radical <| a * b * c : ℝ)^(1 + ε)

/-- For every positive real number ε, there exist only finitely many triples `(a, b, c)` of
coprime positive integers with `a + b = c` such that `q(a, b, c) > 1 + ε`.
(Statement of their theorem `ABC.abc.variants.quality`.) -/
def qualityVariant : Prop := ∀ ε : ℝ, 0 < ε →
    {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧
    a + b = c ∧ quality a b c > (1 + ε)}.Finite

/-! ## Comparison lemmas -/

/-- Their radical is the radical of `Challenge.Defs`. -/
theorem radical_eq_rad (n : ℕ) : radical n = rad n := rfl

/-- `rad n ≥ 2` for `n ≥ 2`: some prime divides `n`, hence divides `rad n`. -/
theorem two_le_rad {n : ℕ} (hn : 2 ≤ n) : 2 ≤ rad n := by
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
  have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩
  have hdvd : p ∣ rad n := Finset.dvd_prod_of_mem (fun q => q) hmem
  exact hp.two_le.trans (Nat.le_of_dvd (rad_pos n) hdvd)

/-- For positive `a`, `b` with `a + b = c`, the quality exceeds `1 + ε` exactly when
`rad(abc)^(1 + ε) < c`. -/
theorem quality_gt_iff {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a + b = c) (ε : ℝ) :
    quality a b c > 1 + ε ↔ (rad (a * b * c) : ℝ) ^ (1 + ε) < c := by
  have hc2 : 2 ≤ a * b * c := by
    have : 1 ≤ a * b := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    calc 2 ≤ 1 * c := by omega
      _ ≤ a * b * c := Nat.mul_le_mul_right c this
  have hr2 : (2 : ℝ) ≤ rad (a * b * c) := by exact_mod_cast two_le_rad hc2
  have hr0 : (0 : ℝ) < rad (a * b * c) := by linarith
  have hlogr : 0 < Real.log (rad (a * b * c)) := Real.log_pos (by linarith)
  have hc0 : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  unfold quality
  rw [radical_eq_rad, gt_iff_lt, lt_div_iff₀ hlogr, ← Real.log_rpow hr0,
    Real.log_lt_log_iff (Real.rpow_pos_of_pos hr0 _) hc0]

/-- The set of the finiteness form of Formal Conjectures is the set of `Challenge.ABCFinite`. -/
theorem abcSet_eq (ε : ℝ) :
    {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧
      a + b = c ∧ (radical <| a * b * c : ℝ)^(1 + ε) < c} =
    {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧
      Nat.Coprime t.1 t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧
      ((rad (t.1 * t.2.1 * t.2.2) : ℝ) ^ (1 + ε) < t.2.2)} := by
  ext ⟨a, b, c⟩
  simp only [Set.mem_ofPred_eq, radical_eq_rad]
  constructor
  · rintro ⟨ha, hb, hc, hp, h, hlt⟩
    exact ⟨ha, hb, hc, (coprime_iff_pairwise ha hb h).mpr hp, h, hlt⟩
  · rintro ⟨ha, hb, hc, hab, h, hlt⟩
    exact ⟨ha, hb, hc, (coprime_iff_pairwise ha hb h).mp hab, h, hlt⟩

/-- The set of the quality form is the set of the finiteness form, for every `ε`. -/
theorem qualitySet_eq (ε : ℝ) :
    {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧
      a + b = c ∧ quality a b c > (1 + ε)} =
    {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧
      a + b = c ∧ (radical <| a * b * c : ℝ)^(1 + ε) < c} := by
  ext ⟨a, b, c⟩
  simp only [Set.mem_ofPred_eq, radical_eq_rad]
  constructor
  · rintro ⟨ha, hb, hc, hp, h, hq⟩
    exact ⟨ha, hb, hc, hp, h, (quality_gt_iff ha hb h ε).mp hq⟩
  · rintro ⟨ha, hb, hc, hp, h, hlt⟩
    exact ⟨ha, hb, hc, hp, h, (quality_gt_iff ha hb h ε).mpr hlt⟩

/-! ## Equivalences with `Challenge.ABC` -/

/-- The finiteness form of Formal Conjectures is `Challenge.ABCFinite`. -/
theorem abc_iff_abcFinite : abc ↔ ABCFinite := by
  unfold abc ABCFinite
  exact forall₂_congr fun ε _ => by rw [abcSet_eq]

/-- **The finiteness form of Formal Conjectures (`ABC.abc`) is equivalent to `Challenge.ABC`.** -/
theorem abc_iff_ABC : abc ↔ ABC := abc_iff_abcFinite.trans IUT.ABC.abc_iff_abcFinite.symm

/-- **The quality form of Formal Conjectures (`ABC.abc.variants.quality`) is equivalent to
`Challenge.ABC`.** It defines, for each `ε`, the same set as `ABC.abc`. -/
theorem qualityVariant_iff_ABC : qualityVariant ↔ ABC := by
  refine Iff.trans ?_ abc_iff_ABC
  unfold qualityVariant abc
  exact forall₂_congr fun ε _ => by rw [qualitySet_eq]

/-- **The strict constant form of Formal Conjectures (`ABC.abc.variants.lt_constant_mul`) is
equivalent to `Challenge.ABC`.** -/
theorem ltConstantMul_iff_ABC : ltConstantMul ↔ ABC := by
  constructor
  · intro h ε hε
    obtain ⟨K, hK⟩ := h ε hε
    -- The triple `1 + 1 = 2` forces `K > 0`.
    have hpos : (0 : ℝ) < K := by
      have h2 := hK 1 1 2 (by decide) (by decide) (by decide)
        ((coprime_iff_pairwise (by decide) (by decide) rfl).mp (by decide)) rfl
      have hr := one_le_rad_rpow (1 * 1 * 2) (show (0 : ℝ) ≤ 1 + ε by linarith)
      rw [radical_eq_rad] at h2
      by_contra hK0
      replace hK0 : K ≤ 0 := not_lt.mp hK0
      have : K * (rad (1 * 1 * 2) : ℝ) ^ (1 + ε) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hK0 (by linarith)
      have h2' : ((2 : ℕ) : ℝ) < K * (rad (1 * 1 * 2) : ℝ) ^ (1 + ε) := h2
      norm_num at h2'
      linarith
    refine ⟨K, hpos, fun a b c ha hb hc hab habc => ?_⟩
    have := hK a b c ha hb hc ((coprime_iff_pairwise ha hb habc).mp hab) habc
    rw [radical_eq_rad] at this
    exact this.le
  · intro h ε hε
    obtain ⟨K, _, hK⟩ := h ε hε
    refine ⟨K + 1, fun a b c ha hb hc hp habc => ?_⟩
    have hle := hK a b c ha hb hc ((coprime_iff_pairwise ha hb habc).mpr hp) habc
    have hr := one_le_rad_rpow (a * b * c) (show (0 : ℝ) ≤ 1 + ε by linarith)
    rw [radical_eq_rad]
    calc (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε) := hle
      _ < (K + 1) * (rad (a * b * c) : ℝ) ^ (1 + ε) := by nlinarith

end IUT.ABC.FormalConjectures
