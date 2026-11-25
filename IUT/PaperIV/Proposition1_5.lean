import Mathlib

/-!
# IUT IV, Proposition 1.5: archimedean metric estimates (elementary part)

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Proposition 1.5, pages 14 to 16 of
the April 2020 manuscript, read from the extracted text and from the rendered page 15; the
statements of (i) and (iii) were checked against the render.

Statement (i) of the paper: the isomorphism of topological rings `ℂ ⊗_ℝ ℂ ≅ ℂ ⊕ ℂ` is compatible
with the tensor product metric on the left and the direct sum metric on the right up to a factor
of `2` (the metric on the right is `2` times the metric on the left; lengths differ by `√2`).

This file is not a formalization of Proposition 1.5. Tensor products of metrized real vector
spaces, the primitive automorphisms of (ii), the integral structures `B_I` of (iii) and the
inclusion of (iv) are not formalized. This file checks:

* (i) in coordinates: writing an element of `ℂ ⊗_ℝ ℂ` as
  `x₁₁·(1⊗1) + x_{i1}·(i⊗1) + x_{1i}·(1⊗i) + x_{ii}·(i⊗i)` (an orthonormal basis for the tensor
  product metric), the isomorphism `a⊗b ↦ (a·b, a·b̄)` (`crt`, `crt_pure`) multiplies squared
  lengths by exactly `2` (`crt_normSq`);
* the count in (iii): since `dim_ℝ M_I = (2|V|)^{|I|}` and each copy of `ℂ` has real dimension
  `2`, the number of copies is `2^{|I|-1}·|V|^{|I|}` (`count_iii`).
-/

namespace IUT.PaperIV.Proposition1_5

/-- The isomorphism `ℂ ⊗_ℝ ℂ → ℂ ⊕ ℂ`, `a⊗b ↦ (a·b, a·b̄)`, in the coordinates
`(x₁₁, x_{i1}, x_{1i}, x_{ii})` with respect to the basis `1⊗1, i⊗1, 1⊗i, i⊗i`. -/
noncomputable def crt (x11 xi1 x1i xii : ℝ) : ℂ × ℂ :=
  (⟨x11 - xii, xi1 + x1i⟩, ⟨x11 + xii, xi1 - x1i⟩)

/-- On a pure tensor `a ⊗ b`, whose coordinates are `(a₁b₁, a₂b₁, a₁b₂, a₂b₂)` for
`a = a₁ + a₂·i`, `b = b₁ + b₂·i`, the map `crt` is `(a·b, a·b̄)`. -/
theorem crt_pure (a b : ℂ) :
    crt (a.re * b.re) (a.im * b.re) (a.re * b.im) (a.im * b.im) = (a * b, a * (starRingEnd ℂ) b) := by
  simp only [crt, Prod.mk.injEq]
  constructor <;> apply Complex.ext <;> simp <;> ring

/-- **Proposition 1.5 (i)** in coordinates: the direct sum squared length of `crt x` is `2`
times the tensor product squared length `x₁₁² + x_{i1}² + x_{1i}² + x_{ii}²`. -/
theorem crt_normSq (x11 xi1 x1i xii : ℝ) :
    Complex.normSq (crt x11 xi1 x1i xii).1 + Complex.normSq (crt x11 xi1 x1i xii).2
      = 2 * (x11 ^ 2 + xi1 ^ 2 + x1i ^ 2 + xii ^ 2) := by
  simp only [crt, Complex.normSq_mk]; ring

/-- **The count of Proposition 1.5 (iii).** For `|I| ≥ 1`, `(2|V|)^{|I|} = 2·(2^{|I|-1}·|V|^{|I|})`,
so a real vector space of dimension `(2|V|)^{|I|}` is a direct sum of `2^{|I|-1}·|V|^{|I|}` copies
of `ℂ`. -/
theorem count_iii (n v : ℕ) (hn : 1 ≤ n) : (2 * v) ^ n = 2 * (2 ^ (n - 1) * v ^ n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]; ring

end IUT.PaperIV.Proposition1_5
