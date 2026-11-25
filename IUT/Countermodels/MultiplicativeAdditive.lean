import Mathlib

/-!
# Countermodels: multiplicative data and additive structure

Source context: Mochizuki, *Inter-universal Teichmüller Theory III*. The passages this file
bears on were read in this session from the extracted text: Definition 1.1 and
Proposition 1.2 (log-links, log-shells; pages 26 to 35), Theorem 3.11 (i), (ii) (pages 153
to 157), and Step (i) of the proof of Corollary 3.12 (page 175), where the
Θ×μ_LGP-link is described as a poly-isomorphism with a "unit portion" and a "value group
portion". No formula of the papers is transcribed here, so no page render was needed.

**None of the statements below is a counterexample to a statement of the IUT papers.** They
refute a simplified abstraction: "a map that respects the multiplicative structure of a field
respects its additive structure", together with variants in which some extra data (a Galois
action, a topology, an order, the unit group) is also respected. In the classification of the
project they are counterexamples to a simplified abstraction. The passages read do not assert
that multiplicative data alone determines the ring; the point of the examples is to show which
extra data does and does not close the gap, so that an argument that relies on such a
reconstruction must name the data it uses.

The positive statement `additive_of_mul_of_translate` shows that very little additive data
suffices: compatibility with the single translation `x ↦ x + 1`.

For the unit group `ℤ_p^×` itself, `padicInt_units_inv_not_ringHom` shows that inversion, a
group automorphism of `ℤ_p^×`, is induced by no ring endomorphism of `ℤ_p`. Power maps
`u ↦ u^k` on `ℤ_p^×` were not attempted.
-/

namespace IUT.Countermodels.MulAdd

/-! ## Inversion: multiplicative, Galois equivariant, continuous, not additive -/

/-- Inversion commutes with every ring automorphism of every field. So equivariance with
respect to a group of field automorphisms (a "Galois action") cannot distinguish inversion,
which is not additive, from the identity. -/
theorem inv_comm_ringEquiv {K : Type*} [Field K] (σ : K ≃+* K) (x : K) :
    σ x⁻¹ = (σ x)⁻¹ :=
  map_inv₀ σ x

/-- On a field in which `2 ≠ 0` and `3 ≠ 0`, inversion agrees with no ring endomorphism on the
nonzero elements: a ring map fixes `2`, while `2⁻¹ = 2` would force `3 = 0`. -/
theorem inv_not_ringHom {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    ¬ ∃ σ : K →+* K, ∀ x : K, x ≠ 0 → σ x = x⁻¹ := by
  rintro ⟨σ, hσ⟩
  have h := hσ 2 h2
  rw [map_ofNat] at h
  have : (2 : K) * 2 = 1 := by
    calc (2 : K) * 2 = 2 * 2⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel₀ h2
  apply h3
  linear_combination this

/-- **Local field countermodel.** On `ℚ_p`, inversion (with `0⁻¹ = 0`) is a bijection that
preserves `0`, `1` and multiplication, commutes with every field automorphism, is continuous on
`ℚ_p^×`, and maps the unit group `{‖x‖ = 1}` onto itself. It is nevertheless induced by no
ring endomorphism, and it does not preserve the absolute value: it sends `p`, of norm `p⁻¹`,
to an element of norm `p`.

So the multiplicative monoid of `ℚ_p` with its topology, its unit group and the action of its
field automorphisms does not determine the additive structure, and an isomorphism that is the
identity on units can still reverse the value group. Bears on: the description of the
Θ×μ_LGP-link as a unit portion together with a value group portion (IUT III, page 175, Step
(i) of the proof of Corollary 3.12) and the fact that log-shells are built from units only
(IUT III, Remark 1.1.1 (i), page 28). The example says nothing about reconstructions from
richer data, such as the absolute Galois group of `ℚ_p` used in the papers. -/
theorem padic_inv_countermodel (p : ℕ) [Fact p.Prime] :
    let f : ℚ_[p] → ℚ_[p] := fun x => x⁻¹
    Function.Bijective f ∧ f 0 = 0 ∧ f 1 = 1 ∧ (∀ x y, f (x * y) = f x * f y) ∧
      (∀ σ : ℚ_[p] ≃+* ℚ_[p], ∀ x, f (σ x) = σ (f x)) ∧ ContinuousOn f {0}ᶜ ∧
      (∀ x : ℚ_[p], ‖x‖ = 1 → ‖f x‖ = 1) ∧ ‖f p‖ ≠ ‖(p : ℚ_[p])‖ ∧
      ¬ ∃ σ : ℚ_[p] →+* ℚ_[p], ∀ x, x ≠ 0 → σ x = f x := by
  intro f
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  refine ⟨?_, inv_zero, inv_one, fun x y => mul_inv x y, fun σ x => (map_inv₀ σ x).symm,
    continuousOn_inv₀, fun x hx => by simp [f, hx], ?_, inv_not_ringHom two_ne_zero three_ne_zero⟩
  · exact Function.Involutive.bijective inv_inv
  · simp only [f, norm_inv, Padic.norm_p, inv_inv]
    intro h
    have : (p : ℝ) * p = 1 := by
      calc (p : ℝ) * p = (p : ℝ) * (p : ℝ)⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ (by linarith)
    nlinarith

/-- **Countermodel on a unit group.** Inversion is a group automorphism of `ℤ_p^×`
(`MulEquiv.inv`), but no ring endomorphism of `ℤ_p` agrees with it on units: a ring map fixes the
unit `1 + p`, while `(1 + p)² = 1` would give `p (p + 2) = 0` in the domain `ℤ_p`. So an
automorphism of the unit group of the ring of integers of a local field need not come from the
ring. -/
theorem padicInt_units_inv_not_ringHom (p : ℕ) [Fact p.Prime] :
    ¬ ∃ σ : ℤ_[p] →+* ℤ_[p], ∀ u : ℤ_[p]ˣ, σ u = ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by
  rintro ⟨σ, hσ⟩
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hn : ‖(1 : ℤ_[p]) + p‖ = 1 := by
    rw [PadicInt.norm_add_eq_max_of_ne, norm_one, PadicInt.norm_p]
    · exact max_eq_left (inv_le_one_of_one_le₀ hp1.le)
    · rw [norm_one, PadicInt.norm_p]
      exact (inv_lt_one_of_one_lt₀ hp1).ne'
  obtain ⟨u, hu⟩ := PadicInt.isUnit_iff.mpr hn
  have h := hσ u
  rw [hu, map_add, map_one, map_natCast] at h
  have h2 : ((1 : ℤ_[p]) + p) * (1 + p) = 1 := by
    calc ((1 : ℤ_[p]) + p) * (1 + p) = (u : ℤ_[p]) * ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by rw [← h, hu]
      _ = 1 := u.mul_inv
  have h3 : (p : ℤ_[p]) * ((p : ℤ_[p]) + 2) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h4)
  · have : ((p + 2 : ℕ) : ℤ_[p]) = 0 := by push_cast; exact h4
    have : (p + 2 : ℕ) = 0 := by exact_mod_cast this
    omega

/-! ## A unit-preserving monoid map that rescales the value group -/

/-- The map `x ↦ x · p^{v(x)}` on `ℚ_p`, where `v` is the `p`-adic valuation. It is the
identity on units and doubles valuations: on `x = p^n u` it gives `p^{2n} u`. -/
noncomputable def squareValue (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) : ℚ_[p] :=
  x * (p : ℚ_[p]) ^ x.valuation

/-- **Countermodel shaped like a unit portion plus a value group portion.** The map
`squareValue p` preserves `0`, `1` and multiplication, is injective, and is the identity on
every element of norm `1` (the units of `ℤ_p`). It doubles the valuation of every nonzero
element. It is not additive.

So a multiplicative map that is the identity on the unit portion and acts on the value group
portion by a homomorphism of value groups (here multiplication by `2`) need not be compatible
with addition. This is a model of the abstraction "identify the units, rescale the value
group"; it is not a model of the Θ×μ_LGP-link, which is a poly-isomorphism of Frobenioid
theoretic prime-strips rather than a map on a field (IUT III, page 175). -/
theorem squareValue_countermodel (p : ℕ) [Fact p.Prime] :
    squareValue p 0 = 0 ∧ squareValue p 1 = 1 ∧
      (∀ x y, squareValue p (x * y) = squareValue p x * squareValue p y) ∧
      Function.Injective (squareValue p) ∧
      (∀ x : ℚ_[p], x ≠ 0 → ‖x‖ = 1 → squareValue p x = x) ∧
      (∀ x : ℚ_[p], x ≠ 0 → (squareValue p x).valuation = 2 * x.valuation) ∧
      ¬ ∀ x y, squareValue p (x + y) = squareValue p x + squareValue p y := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hval : ∀ x : ℚ_[p], x ≠ 0 → (squareValue p x).valuation = 2 * x.valuation := by
    intro x hx
    unfold squareValue
    rw [Padic.valuation_mul hx (zpow_ne_zero _ hp0), Padic.valuation_zpow, Padic.valuation_p]
    ring
  have hunit : ∀ x : ℚ_[p], x ≠ 0 → ‖x‖ = 1 → x.valuation = 0 := by
    intro x hx h1
    rw [Padic.norm_eq_zpow_neg_valuation hx] at h1
    have := (zpow_right_injective₀ (by linarith : (0 : ℝ) < p) hp1.ne') (h1.trans (zpow_zero _).symm)
    omega
  refine ⟨by simp [squareValue], by simp [squareValue], ?_, ?_, ?_, hval, ?_⟩
  · intro x y
    by_cases hx : x = 0
    · simp [squareValue, hx]
    by_cases hy : y = 0
    · simp [squareValue, hy]
    unfold squareValue
    rw [Padic.valuation_mul hx hy, zpow_add₀ hp0]
    ring
  · intro x y hxy
    by_cases hx : x = 0
    · subst hx
      have : y * (p : ℚ_[p]) ^ y.valuation = 0 := by simpa [squareValue] using hxy.symm
      rcases mul_eq_zero.mp this with h | h
      · exact h.symm
      · exact absurd h (zpow_ne_zero _ hp0)
    by_cases hy : y = 0
    · subst hy
      have : x * (p : ℚ_[p]) ^ x.valuation = 0 := by simpa [squareValue] using hxy
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (zpow_ne_zero _ hp0)
    have hv : x.valuation = y.valuation := by
      have := congrArg Padic.valuation hxy
      rw [hval x hx, hval y hy] at this
      omega
    unfold squareValue at hxy
    rw [hv] at hxy
    exact mul_right_cancel₀ (zpow_ne_zero _ hp0) hxy
  · intro x hx h1
    simp [squareValue, hunit x hx h1]
  · intro hadd
    have hnat : ∀ n : ℕ, squareValue p (n : ℚ_[p]) = n := by
      intro n
      induction n with
      | zero => simp [squareValue]
      | succ n ih =>
        push_cast
        rw [hadd, ih]
        simp [squareValue]
    have h := hnat p
    unfold squareValue at h
    rw [Padic.valuation_p, zpow_one] at h
    have : (p : ℚ_[p]) * p = p * 1 := by rw [h, mul_one]
    have h' : (p : ℚ_[p]) = 1 := mul_left_cancel₀ hp0 this
    have : (p : ℕ) = 1 := by exact_mod_cast h'
    exact (Fact.out : p.Prime).one_lt.ne' this

/-! ## An order-preserving, continuous multiplicative automorphism of `ℝ` -/

/-- **Countermodel with order and topology.** Cubing on `ℝ` is a strictly monotone, continuous
bijection that preserves `0`, `1` and multiplication, and it is not additive. The only ring
endomorphism of `ℝ` is the identity (`Real.RingHom.unique`), so cubing is induced by no ring
map. Hence the multiplicative monoid of `ℝ` together with its order and its topology does not
determine the additive structure. -/
theorem real_cube_countermodel :
    let f : ℝ → ℝ := fun x => x ^ 3
    StrictMono f ∧ Continuous f ∧ Function.Bijective f ∧ f 0 = 0 ∧ f 1 = 1 ∧
      (∀ x y, f (x * y) = f x * f y) ∧ ¬ ∃ σ : ℝ →+* ℝ, ∀ x, σ x = f x := by
  intro f
  have hmono : StrictMono f := Odd.strictMono_pow (by decide)
  refine ⟨hmono, continuous_pow 3, ⟨hmono.injective, ?_⟩, by norm_num [f], by norm_num [f],
    fun x y => mul_pow x y 3, ?_⟩
  · intro y
    rcases le_total 0 y with hy | hy
    · exact ⟨y ^ ((3 : ℕ)⁻¹ : ℝ), Real.rpow_inv_natCast_pow hy (by norm_num)⟩
    · refine ⟨-((-y) ^ ((3 : ℕ)⁻¹ : ℝ)), ?_⟩
      show (-((-y) ^ ((3 : ℕ)⁻¹ : ℝ))) ^ 3 = y
      rw [Odd.neg_pow (by decide), Real.rpow_inv_natCast_pow (neg_nonneg.mpr hy) (by norm_num),
        neg_neg]
  · rintro ⟨σ, hσ⟩
    have h := hσ 2
    rw [map_ofNat] at h
    norm_num [f] at h

/-! ## The positive statement: one translation suffices -/

/-- **Positive statement.** On any field, a map that preserves multiplication, sends `0` to `0`,
and commutes with the translation `x ↦ x + 1` is additive (hence a ring endomorphism, since
`f 1 = f 0 + 1 = 1`). For `y ≠ 0`: `f (x + y) = f (y · (x/y + 1)) = f y · (f (x/y) + 1)
= f x + f y`.

So multiplicative data together with even a very small piece of additive data determines the
additive structure. The countermodels above show that this piece cannot be replaced by an
order, a topology, the unit group, or equivariance under field automorphisms. -/
theorem additive_of_mul_of_translate {K : Type*} [Field K] (f : K → K)
    (hmul : ∀ x y, f (x * y) = f x * f y) (h0 : f 0 = 0) (h1 : ∀ x, f (x + 1) = f x + 1) :
    ∀ x y, f (x + y) = f x + f y := by
  intro x y
  by_cases hy : y = 0
  · simp [hy, h0]
  have : x + y = y * (x / y + 1) := by field_simp
  rw [this, hmul, h1, mul_add, mul_one, ← hmul, mul_div_cancel₀ x hy]

end IUT.Countermodels.MulAdd
