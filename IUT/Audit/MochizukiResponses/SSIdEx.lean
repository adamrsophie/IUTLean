import Mathlib

/-!
# Mochizuki's example (SSIdEx): two complex structures on `ℝ²`

Source: S. Mochizuki, *Report on Discussions, Held During the Period March 15 to 20, 2018,
Concerning Inter-universal Teichmüller Theory (IUTch)*, version dated February 2019, item
(SSIdEx), pages 17 to 19. The whole report (45 pages) was read; the formulas of (SSIdEx) were
checked against the rendered pages 17 and 18. (The text extraction drops the slash of the
`≠` in "(φ₁)_ℂ ∘ ι_U ≠ ι_W ∘ φ₂"; the rendered page 18 shows `≠`.)

**Whose argument.** Mochizuki offers (SSIdEx) as an elementary model of the logical structure
of his objection (SSIdFs) to the "id-version" (SSId) of the Θ-link that he attributes to
Scholze and Stix: `V₁ = ℝ e₁` plays the unit group portion, `V₂ = ℝ e₂` the value group
portion, the `U`-structure the q-holomorphic structure, the `W`-structure the Θ-holomorphic
structure.

**The example.** `V = ℝ²`, `e₁ = (1,0)`, `e₂ = (0,1)`, `0 < t < 1`. The `U`-structure is
`i e₁ = e₂, i e₂ = −e₁`; the `W`-structure is `i e₁ = t e₂, i e₂ = −t⁻¹ e₁`. The map
`φ : U → W` is the identity of `V`. `ι_U : U₂ → (U₁)_ℂ` sends `e₂ ↦ i e₁`, and
`ι_W : W₂ → (W₁)_ℂ` sends `t e₂ ↦ i e₁`; they are the restrictions of the `ℂ`-linear
isomorphisms `ζ_U : U → (U₁)_ℂ`, `ζ_W : W → (W₁)_ℂ` that restrict to the identity on `U₁`,
`W₁`.

**Modeling choices.** `(U₁)_ℂ` and `(W₁)_ℂ` are both modeled by `ℂ` with `e₁ ↦ 1`, so that
`ζ_U (x, y) = x + y i` and `ζ_W (x, y) = x + (y / t) i`. This file proves that these are the
`ℂ`-linear maps described in the report, and then checks:

* (≇): there is no isomorphism of the data `(U, U₁, U₂, e₁, e₂, ι_U)` and
  `(W, W₁, W₂, e₁, e₂, ι_W)` when `t ≠ 1` (`not_iso_of_ne_one`);
* (Dilat): in the coordinates `ζ_U, ζ_W`, `φ` becomes `z ↦ a z + b z̄` with
  `b / a = (t − 1)/(t + 1) ≠ 0`, while `(φ₁)_ℂ` is the identity of `ℂ`, with zero
  antiholomorphic part; the maximal dilatation of `φ` is `1/t`.

**What this file does not do.** It checks the example, which is elementary linear algebra.
Whether the id-version (SSId) of the Θ-link stands to the Θ-link of IUT as `[Φ]` stands to
`Φ` here is the analogy Mochizuki asserts; it is not a statement about vector spaces and is not
addressed. This file does not settle the dispute.
-/

namespace IUT.Audit.MochizukiResponses.SSIdEx

open Complex

/-- The real vector space `V = ℝ²`. -/
abbrev V := ℝ × ℝ

/-- `e₁ = (1, 0)`. -/
def e₁ : V := (1, 0)

/-- `e₂ = (0, 1)`. -/
def e₂ : V := (0, 1)

/-- Multiplication by `i` in the `U`-structure: `(x, y) ↦ (−y, x)`. -/
def JU : V →ₗ[ℝ] V where
  toFun v := (-v.2, v.1)
  map_add' _ _ := by ext <;> simp; ring
  map_smul' _ _ := by simp

/-- Multiplication by `i` in the `W`-structure: `(x, y) ↦ (−y/t, t x)`. -/
noncomputable def JW (t : ℝ) : V →ₗ[ℝ] V where
  toFun v := (-(v.2 / t), t * v.1)
  map_add' _ _ := by ext <;> simp <;> ring
  map_smul' _ _ := by ext <;> simp <;> ring

/-- The `U`-structure as stated: `i e₁ = e₂`, `i e₂ = −e₁`. -/
theorem JU_e₁ : JU e₁ = e₂ := by simp [JU, e₁, e₂]
theorem JU_e₂ : JU e₂ = -e₁ := by simp [JU, e₁, e₂]

/-- The `W`-structure as stated: `i e₁ = t e₂`, `i e₂ = −t⁻¹ e₁`. -/
theorem JW_e₁ (t : ℝ) : JW t e₁ = t • e₂ := by simp [JW, e₁, e₂]
theorem JW_e₂ (t : ℝ) : JW t e₂ = -(t⁻¹ • e₁) := by simp [JW, e₁, e₂, div_eq_mul_inv]

/-- Both are complex structures: `J² = −1` (for `W`, when `t ≠ 0`). -/
theorem JU_sq (v : V) : JU (JU v) = -v := by ext <;> simp [JU]

theorem JW_sq {t : ℝ} (ht : t ≠ 0) (v : V) : JW t (JW t v) = -v := by
  ext <;> simp [JW] <;> field_simp

/-- `φ = id_V` is `ℂ`-linear from `U` to `W` only if `t = 1`: the two structures differ. -/
theorem JW_ne_JU {t : ℝ} (ht : t ≠ 1) : JW t ≠ JU := by
  intro h
  have := congrArg (fun f : V →ₗ[ℝ] V => (f e₁).2) h
  simp [JW, JU, e₁] at this
  exact ht this

/-- `ζ_U : U → (U₁)_ℂ`, in the model `(U₁)_ℂ = ℂ`, `e₁ ↦ 1`. -/
noncomputable def ζU (v : V) : ℂ := (v.1 : ℂ) + (v.2 : ℂ) * I

/-- `ζ_W : W → (W₁)_ℂ`, in the model `(W₁)_ℂ = ℂ`, `e₁ ↦ 1`. -/
noncomputable def ζW (t : ℝ) (v : V) : ℂ := (v.1 : ℂ) + ((v.2 / t : ℝ) : ℂ) * I

/-- `ζ_U` is `ℂ`-linear for the `U`-structure. -/
theorem ζU_JU (v : V) : ζU (JU v) = I * ζU v := by
  simp [ζU, JU, Complex.ext_iff]

/-- `ζ_W` is `ℂ`-linear for the `W`-structure. -/
theorem ζW_JW {t : ℝ} (ht : t ≠ 0) (v : V) : ζW t (JW t v) = I * ζW t v := by
  apply Complex.ext <;> simp [ζW, JW]; field_simp

/-- Both restrict to the identity on the first factor: `ζ (e₁) = 1`. -/
theorem ζU_e₁ : ζU e₁ = 1 := by simp [ζU, e₁]
theorem ζW_e₁ (t : ℝ) : ζW t e₁ = 1 := by simp [ζW, e₁]

/-- `ι_U = ζ_U|_{U₂}` maps `e₂ ↦ i e₁`. -/
theorem ιU_e₂ : ζU e₂ = I := by simp [ζU, e₂]

/-- `ι_W = ζ_W|_{W₂}` maps `t e₂ ↦ i e₁`. -/
theorem ιW_te₂ {t : ℝ} (ht : t ≠ 0) : ζW t (t • e₂) = I := by
  simp [ζW, e₂, ht]

/-- **(≇)**: for `t ≠ 1` there is no isomorphism between `(U, U₁, U₂, e₁, e₂, ι_U)` and
`(W, W₁, W₂, e₁, e₂, ι_W)`. An isomorphism consists of a real-linear `ψ : V → V` fixing the
distinguished elements `e₁, e₂` and a `ℂ`-linear `χ : (U₁)_ℂ → (W₁)_ℂ` extending `ψ|_{U₁}`
(so `χ 1 = 1`), compatible with the `ι`'s: `χ (ι_U v) = ι_W (ψ v)` on `U₂`. -/
theorem not_iso_of_ne_one {t : ℝ} (ht : t ≠ 1) :
    ¬ ∃ (ψ : V →ₗ[ℝ] V) (χ : ℂ →ₗ[ℂ] ℂ), ψ e₁ = e₁ ∧ ψ e₂ = e₂ ∧ χ 1 = 1 ∧
      ∀ s : ℝ, χ (ζU (s • e₂)) = ζW t (ψ (s • e₂)) := by
  rintro ⟨ψ, χ, -, h2, hχ, hcomp⟩
  have h := hcomp 1
  rw [one_smul, h2, ιU_e₂] at h
  have hI : χ I = I := by
    have := χ.map_smul I 1
    simpa [hχ] using this
  rw [hI] at h
  have := congrArg Complex.im h
  simp [ζW, e₂] at this
  exact ht (by field_simp at this; linarith)

/-- For `t = 1` the identity is such an isomorphism, so the condition `t ≠ 1` is needed. -/
theorem iso_of_eq_one : ∃ (ψ : V →ₗ[ℝ] V) (χ : ℂ →ₗ[ℂ] ℂ), ψ e₁ = e₁ ∧ ψ e₂ = e₂ ∧ χ 1 = 1 ∧
    ∀ s : ℝ, χ (ζU (s • e₂)) = ζW 1 (ψ (s • e₂)) :=
  ⟨LinearMap.id, LinearMap.id, rfl, rfl, rfl, fun s => by simp [ζU, ζW]⟩

/-- `φ = id_V` read in the coordinates `ζ_U`, `ζ_W`: the map `ℂ → ℂ`,
`x + y i ↦ x + (y / t) i`. -/
noncomputable def φcoord (t : ℝ) (z : ℂ) : ℂ := (z.re : ℂ) + ((z.im / t : ℝ) : ℂ) * I

/-- `φcoord` is indeed `ζ_W ∘ φ ∘ ζ_U⁻¹`. -/
theorem φcoord_ζU (t : ℝ) (v : V) : φcoord t (ζU v) = ζW t v := by
  simp [φcoord, ζU, ζW]

/-- **(Dilat)**, computation: `φcoord z = a z + b z̄` with `a = (1 + t⁻¹)/2`,
`b = (1 − t⁻¹)/2`. -/
theorem φcoord_eq (t : ℝ) (z : ℂ) :
    φcoord t z = (((1 + t⁻¹) / 2 : ℝ) : ℂ) * z + (((1 - t⁻¹) / 2 : ℝ) : ℂ) * (starRingEnd ℂ) z := by
  apply Complex.ext <;> simp [φcoord] <;> ring

/-- The antiholomorphic coefficient `b = (1 − t⁻¹)/2` vanishes only for `t = 1`; so for
`0 < t < 1` the map `φ` is not holomorphic, while `(φ₁)_ℂ = id_ℂ` has `b = 0`. -/
theorem antiholo_ne_zero {t : ℝ} (ht : t ≠ 1) : (1 - t⁻¹) / 2 ≠ 0 := by
  intro h
  apply ht
  have : t⁻¹ = 1 := by linarith
  simpa using this

/-- The Beltrami coefficient `μ = b / a` of `φ` equals `(t − 1)/(t + 1)`. -/
theorem beltrami {t : ℝ} (ht : 0 < t) : ((1 - t⁻¹) / 2) / ((1 + t⁻¹) / 2) = (t - 1) / (t + 1) := by
  field_simp

/-- The maximal dilatation `K = (|a| + |b|)/(|a| − |b|)` of `φ` equals `1/t` for
`0 < t < 1`; it is `1` (conformal) only when `t = 1`. -/
theorem dilatation {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    (|(1 + t⁻¹) / 2| + |(1 - t⁻¹) / 2|) / (|(1 + t⁻¹) / 2| - |(1 - t⁻¹) / 2|) = 1 / t := by
  have hinv : 1 < t⁻¹ := one_lt_inv₀ ht |>.mpr ht1
  rw [abs_of_pos (by linarith), abs_of_neg (by linarith)]
  field_simp
  linear_combination mul_inv_cancel₀ ht.ne'

end IUT.Audit.MochizukiResponses.SSIdEx
