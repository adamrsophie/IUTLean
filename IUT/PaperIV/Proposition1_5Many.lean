import Mathlib
import IUT.PaperIV.Proposition1_5Full
import IUT.PaperIV.Theorem1_10.StepsIVtoVII

/-!
# IUT IV, Proposition 1.5 (iii) and (iv): the tensor product of finitely many copies

Source: Mochizuki, *Inter-universal Teichmüller Theory IV*, Proposition 1.5 (archimedean metric
estimates), pages 14 to 16, and Step (vii) of the proof of Theorem 1.10, pages 29 and 30. Pages
read for this file: 14, 15, 16, 29 and 30; all five were checked against rendered images,
including every formula used below.

This file continues `IUT.PaperIV.Proposition1_5Full`, which proves assertions (i) and (ii) on
`ℂ ⊗_ℝ ℂ`. It proves assertions (iii) and (iv) on the objects of page 15, with the readings
listed below, and states Step (vii) of the proof of Theorem 1.10 on the page's `B_I`.

## Objects

* `M = ⊕_{v ∈ V} ℂ_v` is the ring `V → ℂ` with the direct sum metric `tmetDs V`, the sum of the
  standard real inner products `⟪z, w⟫ = Re(w·z̄)` of the components.
* `M_I = ⊗_{i ∈ I} M_i` (`TmetSpace I V`) is Mathlib's `PiTensorProduct` over `ℝ` of copies of
  `M`, with its `ℝ`-algebra structure (the ring structure determined by those of the `ℂ_v`).
* The **tensor product metric** (`tmetForm I V`) is the real bilinear form with
  `⟪⊗ a_i, ⊗ b_i⟫ = ∏_i ⟪a_i, b_i⟫_M`, built here from `PiTensorProduct.piTensorHomMap₂`.
  Mathlib v4.36.0 has an inner product on binary `TensorProduct` only; for `PiTensorProduct` it
  has the projective and injective seminorms, which are other norms. The form is built on
  `PiTensorProduct` directly, not as an iterated binary tensor product, because `I` is an
  arbitrary finite set (an iteration would fix an order of `I`) and because the factor `V → ℂ`
  carries Mathlib's sup norm, not an inner product; no instance is declared. It is symmetric
  (`tmetForm_comm`) and positive definite (`tmetForm_self`: the sum of the squares of the
  coordinates in the product of the bases `{1, √−1}` of the `ℂ_v`, which is orthonormal).
* The **decomposition** (`tmetPhi i₀`, for a chosen `i₀ ∈ I`) is the isomorphism of
  `ℝ`-algebras from `M_I` onto `⊕_{(v, ε)} ℂ` whose `(v, ε)` component is the character
  `⊗ m_i ↦ ∏_i c_{s_i}(m_i(v_i))`; here `v : I → V` chooses a summand of each factor, `ε` is a
  conjugation pattern on `I ∖ {i₀}`, `s` is `ε` extended by `false` at `i₀`, and `c_false = id`,
  `c_true` = complex conjugation. The index set has `2^{|I|-1}·|V|^{|I|}` elements.
* A **decomposition** in general is an isomorphism of `ℝ`-algebras `ψ : M_I ≅ ⊕_{j ∈ J} ℂ`
  for a finite set `J`; its summands are the preimages of the coordinate lines
  (`tmetSummand`), its direct sum metric is `tmetDs J ∘ ψ`, and its direct product of unit
  balls is `ψ⁻¹(tmetBall J)`.
* `B_I` (`tmetIntegral i₀`) is the direct product of the unit balls of the copies of `ℂ`
  (page 15: "given by the direct product of the unit balls of the copies of ℂ that occur in
  the direct sum decomposition of M_I").
* The automorphism of `M_I` induced by primitive automorphisms `f i v` of the summands `ℂ_v` of
  the factors `M_i` (`tmetInduced f`) is the tensor product of the maps of `M` that apply
  `f i v` on `ℂ_v`; the primitive automorphisms are `archPrimitive` of
  `IUT.PaperIV.Proposition1_5Full`.

## Readings of the page

* "The topological ring structure on each `ℂ_v` determines a topological ring structure on
  `M_I`": the topology of `M_I` is read as the one carried over from `⊕ ℂ` by `tmetPhi i₀`
  (the product topology of the copies of `ℂ`); no topology is put on `PiTensorProduct` as an
  instance. A ring isomorphism onto `⊕_{j ∈ J} ℂ` that is continuous for it is `ℝ`-linear
  (`tmetAlgEquivOfContinuous`), so the statements are proved for isomorphisms of `ℝ`-algebras
  and transferred (`tmetProp1_5_iii_topological`).
* "Unique direct sum decomposition" is read as: for any two decompositions, the numbers of
  copies agree, every summand of one is a summand of the other, and the direct sum metrics
  and the products of unit balls agree (`tmetDecomp_unique`); two decompositions differ by a
  permutation of the summands followed by the identity or complex conjugation on each
  (`tmetAlgEquiv_monomial`).
* "Preserved" in (iii): the induced automorphism preserves the tensor product metric, the
  direct sum metric and `B_I`, and maps each summand onto a summand. It does not map each
  summand onto itself: conjugation on one factor exchanges summands, as in (ii).
* In (iv), "the component of `m_i` in each direct summand `ℂ_v` of `M_i` is of length `λ`" is
  read as `‖m_i(v)‖ = λ` for every `v`, and `λ^{|I|}·B_I` as the pointwise dilation of `B_I`.

## Main results

* `tmetForm_comm`, `tmetForm_self`, `tmetForm_self_eq_zero`: the tensor product metric is an
  inner product.
* `tmetPhi`, `tmetIdx_card`, `tmetPhi_ds`: the decomposition into `2^{|I|-1}·|V|^{|I|}` copies
  of `ℂ` and the metric factor `2^{|I|-1}`.
* `tmetDecomp_unique`, `tmetProp1_5_iii_metric`, `tmetIntegral_eq`,
  `tmetProp1_5_iii_topological`: uniqueness; the count and
  the factor `2^{|I|-1}` for every decomposition; `B_I` does not depend on the decomposition.
* `tmetProp1_5_iii_preserved`: preservation under the automorphisms induced by primitive
  automorphisms.
* `tmetProp1_5_iv`: `⊗ m_i ∈ λ^{|I|}·B_I`.
* `tmetStepVII_container_logVolume`: Step (vii) of the proof of Theorem 1.10 on `B_I` (see below).

The case `V` a single point is the decomposition of `⊗_{i ∈ I} ℂ` into `2^{|I|-1}` copies of
`ℂ` with metric factor `2^{|I|-1}`.

## Step (vii) of the proof of Theorem 1.10

Pages 29 and 30 apply Proposition 1.5 (iii), (iv) with `I = 𝕊^±_{j+1}` (so `|I| = j + 1`) and
take `π^{j+1}·B_I` as the container, with upper bound `(j + 1)·log(π)`, using that the
log-volume of `B_I` is `0`. `tmetStepVII_container_logVolume` proves on `M_I`, with `|I|`
in place of `j + 1`:
every tensor product `⊗ m_i` whose components have length at most `π` lies in `π^{|I|}·B_I`;
the container is preserved by the automorphisms induced by primitive automorphisms; and its
log-volume, normalized so that `B_I` has log-volume `0` and divided by the real dimension as
in `stepsVII_logVolume_smul` of `IUT.PaperIV.Theorem1_10.StepsIVtoVII`, is `|I|·log(π)`. The
log-volume is computed with the Lebesgue measure transported by `tmetPhi i₀`. Two parts of
this are readings and not printed statements: the log-shell elements of length at most `π`
(the page says "elements of the log-shells", whose definition is not on pages 29 and 30), and
the normalization by the real dimension (taken from the existing module). On page 30 the
copies `ℂ_v` are the completions `K_v`; this file works with `ℂ_v = ℂ` as in
Proposition 1.5.

## Not proved

* No identification of `tmetForm` for `|I| = 2`, `V` a point, with Mathlib's inner product on
  the binary `ℂ ⊗_ℝ ℂ` of `IUT.PaperIV.Proposition1_5Full` is proved.
* The topology of `M_I` is the one carried over by `tmetPhi i₀` (see Readings); that it agrees
  with a topology defined on `PiTensorProduct` independently of the decomposition is not
  proved.
* The page's proof refers to IUT III, Proposition 3.1 (i), (ii) and Proposition 3.2 (ii) for
  the constructions; the arguments here are direct and do not formalize those statements.
* Step (vii): the Θ-pilot object, its possible images and the indeterminacies (Ind1) to (Ind3)
  are not constructed, so the statement that the container contains the union of possible
  images is not formalized; neither is the normalization of IUT III, Proposition 3.9 (iii)
  that the page cites for "the log-volume of `B_I` is equal to 0".
-/

namespace IUT.PaperIV.Proposition1_5

open Complex ComplexConjugate
open scoped Pointwise

/-! ## The direct sum metric on `⊕_{j ∈ J} ℂ` -/

/-- The direct sum metric on `⊕_{j ∈ J} ℂ` (written `J → ℂ`): the sum over `j` of the standard
real inner products `⟪z, w⟫ = Re(w·z̄)` of the components. For `J = V` it is the metric of the
page's `M = ⊕_{v ∈ V} ℂ_v`. -/
noncomputable def tmetDs (J : Type*) [Fintype J] : (J → ℂ) →ₗ[ℝ] (J → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun a b => ∑ j, inner ℝ (a j) (b j))
    (fun a a' b => by simp [inner_add_left, Finset.sum_add_distrib])
    (fun c a b => by
      simp only [Pi.smul_apply, real_inner_smul_left, smul_eq_mul, Finset.mul_sum])
    (fun a b b' => by simp [inner_add_right, Finset.sum_add_distrib])
    (fun c a b => by
      simp only [Pi.smul_apply, real_inner_smul_right, smul_eq_mul, Finset.mul_sum])

theorem tmetDs_apply (J : Type*) [Fintype J] (a b : J → ℂ) :
    tmetDs J a b = ∑ j, inner ℝ (a j) (b j) := rfl

theorem tmetDs_comm (J : Type*) [Fintype J] (a b : J → ℂ) : tmetDs J a b = tmetDs J b a := by
  simp only [tmetDs_apply]
  exact Finset.sum_congr rfl fun j _ => real_inner_comm _ _

/-! ## The tensor product `M_I` and its tensor product metric -/

/-- The page's `M_I = ⊗_{i ∈ I} M_i`, the tensor product over `ℝ` of copies `M_i = M` of
`M = ⊕_{v ∈ V} ℂ_v` (written `V → ℂ`), as Mathlib's `PiTensorProduct` with its `ℝ`-algebra
structure (componentwise multiplication on each factor). -/
abbrev TmetSpace (I V : Type*) : Type _ := PiTensorProduct ℝ fun _ : I => V → ℂ

variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

/-- The **tensor product metric** on `M_I`: the real bilinear form with
`⟪⊗ a_i, ⊗ b_i⟫ = ∏_i ⟪a_i, b_i⟫_M`, built from `PiTensorProduct.piTensorHomMap₂` and the
multiplication `⊗_{i ∈ I} ℝ ≅ ℝ`. -/
noncomputable def tmetForm (I V : Type*) [Fintype I] [Fintype V] :
    TmetSpace I V →ₗ[ℝ] TmetSpace I V →ₗ[ℝ] ℝ :=
  (PiTensorProduct.piTensorHomMap₂ (PiTensorProduct.tprod ℝ fun _ : I => tmetDs V)).compr₂
    (PiTensorProduct.constantBaseRingEquiv I ℝ).toLinearMap

omit [DecidableEq I] [DecidableEq V] in
theorem tmetForm_tprod (a b : I → V → ℂ) :
    tmetForm I V (PiTensorProduct.tprod ℝ a) (PiTensorProduct.tprod ℝ b) =
      ∏ i, tmetDs V (a i) (b i) := by
  simp [tmetForm]

omit [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] in
/-- Two real bilinear maps on `M_I` that agree on pure tensors are equal. -/
theorem tmetBil_ext {E : Type*} [AddCommGroup E] [Module ℝ E]
    {F G : TmetSpace I V →ₗ[ℝ] TmetSpace I V →ₗ[ℝ] E}
    (h : ∀ a b : I → V → ℂ, F (PiTensorProduct.tprod ℝ a) (PiTensorProduct.tprod ℝ b) =
      G (PiTensorProduct.tprod ℝ a) (PiTensorProduct.tprod ℝ b)) : F = G :=
  PiTensorProduct.ext <| MultilinearMap.ext fun a => by
    simp only [LinearMap.compMultilinearMap_apply]
    exact PiTensorProduct.ext <| MultilinearMap.ext fun b => by
      simp only [LinearMap.compMultilinearMap_apply]; exact h a b

omit [DecidableEq I] [DecidableEq V] in
/-- The tensor product metric is symmetric. -/
theorem tmetForm_comm (x y : TmetSpace I V) : tmetForm I V x y = tmetForm I V y x := by
  have h : tmetForm I V = (tmetForm I V).flip := tmetBil_ext fun a b => by
    rw [LinearMap.flip_apply, tmetForm_tprod, tmetForm_tprod]
    exact Finset.prod_congr rfl fun i _ => tmetDs_comm V _ _
  calc tmetForm I V x y = (tmetForm I V).flip x y := by rw [← h]
    _ = tmetForm I V y x := rfl

/-- A real bilinear form with an orthonormal basis `b` takes the value `∑_p (b.repr x p)²` on
the diagonal. -/
theorem tmetForm_self_of_orthonormal {E κ : Type*} [AddCommGroup E] [Module ℝ E] [Fintype κ]
    [DecidableEq κ] (F : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (b : Module.Basis κ ℝ E)
    (hb : ∀ p q, F (b p) (b q) = if p = q then 1 else 0) (x : E) :
    F x x = ∑ p, (b.repr x p) ^ 2 := by
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hb, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, sq]

/-- The real basis of `M = ⊕_{v ∈ V} ℂ_v` given by `1` and `√−1` in each summand. -/
noncomputable def tmetFactorBasis (V : Type*) [Fintype V] [DecidableEq V] :
    Module.Basis (Σ _ : V, Fin 2) ℝ (V → ℂ) :=
  Pi.basis fun _ : V => Complex.basisOneI

theorem tmetFactorBasis_orthonormal (p q : Σ _ : V, Fin 2) :
    tmetDs V (tmetFactorBasis V p) (tmetFactorBasis V q) = if p = q then 1 else 0 := by
  obtain ⟨v, k⟩ := p
  obtain ⟨v', k'⟩ := q
  simp only [tmetFactorBasis, Pi.basis_apply, tmetDs_apply]
  by_cases hv : v = v'
  · subst hv
    rw [Finset.sum_eq_single v (fun w _ hw => by simp [hw]) (by simp)]
    fin_cases k <;> fin_cases k' <;> simp [Complex.inner]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp [hv]))]
    refine Finset.sum_eq_zero fun w _ => ?_
    by_cases hw : w = v
    · subst hw; simp [hv]
    · simp [hw]

/-- The product basis of `M_I`, orthonormal for the tensor product metric. -/
noncomputable def tmetBasis (I V : Type*) [Fintype I] [Fintype V] [DecidableEq V] :
    Module.Basis (I → Σ _ : V, Fin 2) ℝ (TmetSpace I V) :=
  Basis.piTensorProduct fun _ : I => tmetFactorBasis V

omit [DecidableEq I] in
theorem tmetBasis_orthonormal (p q : I → Σ _ : V, Fin 2) :
    tmetForm I V (tmetBasis I V p) (tmetBasis I V q) = if p = q then 1 else 0 := by
  simp only [tmetBasis, Basis.piTensorProduct_apply, tmetForm_tprod,
    tmetFactorBasis_orthonormal, Fintype.prod_boole, funext_iff]

/-- **The tensor product metric is an inner product**: `⟪x, x⟫ = ∑_p (coordinate)²` in the
orthonormal product basis. -/
theorem tmetForm_self (x : TmetSpace I V) :
    tmetForm I V x x = ∑ p, ((tmetBasis I V).repr x p) ^ 2 :=
  tmetForm_self_of_orthonormal _ _ tmetBasis_orthonormal x

theorem tmetForm_self_nonneg (x : TmetSpace I V) : 0 ≤ tmetForm I V x x := by
  rw [tmetForm_self]; positivity

theorem tmetForm_self_eq_zero {x : TmetSpace I V} (hx : tmetForm I V x x = 0) : x = 0 := by
  rw [tmetForm_self, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)] at hx
  apply (tmetBasis I V).repr.injective
  ext p
  simpa using hx p (Finset.mem_univ p)

/-! ## The characters `M_I → ℂ` -/

/-- The identity of `ℂ` (`false`) or complex conjugation (`true`), as an `ℝ`-algebra map. -/
noncomputable def tmetConj (s : Bool) : ℂ →ₐ[ℝ] ℂ :=
  if s then (conjAe : ℂ →ₐ[ℝ] ℂ) else AlgHom.id ℝ ℂ

theorem tmetConj_apply (s : Bool) (z : ℂ) : tmetConj s z = archConjIf s z := by
  cases s <;> simp [tmetConj, archConjIf]

/-- The multilinear map `(m_i)_i ↦ ∏_i c_{s_i}(m_i(v_i))`, `c_false = id`, `c_true = conj`. -/
noncomputable def tmetCharMulti (v : I → V) (s : I → Bool) :
    (Π _ : I, V → ℂ) →ₘₗ[ℝ] ℂ :=
  (MultilinearMap.mkPiAlgebra ℝ I ℂ).compLinearMap
    fun i => ((tmetConj (s i)).comp (Pi.evalAlgHom ℝ (fun _ : V => ℂ) (v i))).toLinearMap

omit [DecidableEq I] [Fintype V] [DecidableEq V] in
theorem tmetCharMulti_apply (v : I → V) (s : I → Bool) (m : I → V → ℂ) :
    tmetCharMulti v s m = ∏ i, archConjIf (s i) (m i (v i)) := by
  simp [tmetCharMulti, tmetConj_apply]

/-- The `ℝ`-algebra map `χ_{v,s} : M_I → ℂ`, `⊗ m_i ↦ ∏_i c_{s_i}(m_i(v_i))`, for a choice
`v : I → V` of one summand `ℂ_{v_i}` in each factor and a pattern `s : I → Bool` of
conjugations. -/
noncomputable def tmetChar (v : I → V) (s : I → Bool) : TmetSpace I V →ₐ[ℝ] ℂ :=
  PiTensorProduct.liftAlgHom (tmetCharMulti v s)
    (by
      rw [tmetCharMulti_apply]
      exact Finset.prod_eq_one fun i _ => by cases s i <;> simp [archConjIf])
    (fun x y => by
      simp only [tmetCharMulti_apply, Pi.mul_apply, archConjIf_mul, Finset.prod_mul_distrib])

omit [DecidableEq I] [Fintype V] [DecidableEq V] in
theorem tmetChar_tprod (v : I → V) (s : I → Bool) (m : I → V → ℂ) :
    tmetChar v s (PiTensorProduct.tprod ℝ m) = ∏ i, archConjIf (s i) (m i (v i)) := by
  simp [tmetChar, tmetCharMulti_apply]

omit [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] in
/-- Two real linear maps on `M_I` that agree on pure tensors are equal. -/
theorem tmetLin_ext {E : Type*} [AddCommGroup E] [Module ℝ E]
    {F G : TmetSpace I V →ₗ[ℝ] E}
    (h : ∀ a : I → V → ℂ, F (PiTensorProduct.tprod ℝ a) = G (PiTensorProduct.tprod ℝ a)) :
    F = G :=
  PiTensorProduct.ext <| MultilinearMap.ext fun a => by
    simp only [LinearMap.compMultilinearMap_apply]; exact h a

omit [DecidableEq I] [Fintype V] [DecidableEq V] in
/-- Adding a constant `c` to the conjugation pattern conjugates the character by `c_c`. -/
theorem tmetChar_xor_const (v : I → V) (s : I → Bool) (c : Bool) (x : TmetSpace I V) :
    tmetChar v (fun i => xor (s i) c) x = archConjIf c (tmetChar v s x) := by
  have h : (tmetChar v fun i => xor (s i) c).toLinearMap =
      (tmetConj c).toLinearMap ∘ₗ (tmetChar v s).toLinearMap := tmetLin_ext fun a => by
    simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply, tmetChar_tprod, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [tmetConj_apply, archConjIf_conjIf, Bool.xor_comm]
  have := congrArg (fun F : TmetSpace I V →ₗ[ℝ] ℂ => F x) h
  simpa [tmetConj_apply] using this

/-! ## The decomposition of `M_I` into `2^{|I|-1}·|V|^{|I|}` copies of `ℂ` -/

/-- The index set of the summands: a choice `v : I → V` of one summand in each factor and a
conjugation pattern on the factors other than a fixed `i₀`. It has `|V|^{|I|}·2^{|I|-1}`
elements (`tmetIdx_card`). -/
abbrev TmetIdx (I V : Type*) (i₀ : I) : Type _ := (I → V) × ({i // i ≠ i₀} → Bool)

/-- The conjugation pattern on all of `I` that is `false` at `i₀` and `ε` elsewhere. -/
def tmetExt (i₀ : I) (ε : {i // i ≠ i₀} → Bool) (i : I) : Bool :=
  if h : i = i₀ then false else ε ⟨i, h⟩

omit [Fintype I] in
theorem tmetExt_self (i₀ : I) (ε : {i // i ≠ i₀} → Bool) : tmetExt i₀ ε i₀ = false := by
  simp [tmetExt]

omit [Fintype I] in
theorem tmetExt_ne (i₀ : I) (ε : {i // i ≠ i₀} → Bool) (i : {i // i ≠ i₀}) :
    tmetExt i₀ ε i = ε i := by
  simp [tmetExt, i.2]

theorem tmetIdx_card_ne (i₀ : I) : Fintype.card {i // i ≠ i₀} = Fintype.card I - 1 := by
  simp [Fintype.card_subtype_compl]

omit [DecidableEq V] in
/-- `|TmetIdx| = 2^{|I|-1}·|V|^{|I|}`, the number of copies of `ℂ` printed on page 15. -/
theorem tmetIdx_card (i₀ : I) :
    Fintype.card (TmetIdx I V i₀) = 2 ^ (Fintype.card I - 1) * Fintype.card V ^ Fintype.card I := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, tmetIdx_card_ne]
  ring

/-- The `ℝ`-algebra map `M_I → ⊕_{(v, ε)} ℂ` whose components are the characters
`χ_{v, ext ε}`. -/
noncomputable def tmetPhiHom (i₀ : I) : TmetSpace I V →ₐ[ℝ] (TmetIdx I V i₀ → ℂ) :=
  AlgHom.pi fun j => tmetChar j.1 (tmetExt i₀ j.2)

omit [Fintype V] [DecidableEq V] in
theorem tmetPhiHom_apply (i₀ : I) (x : TmetSpace I V) (j : TmetIdx I V i₀) :
    tmetPhiHom i₀ x j = tmetChar j.1 (tmetExt i₀ j.2) x := rfl

theorem tmetSum_bool_conj (z : ℂ) : ∑ b : Bool, archConjIf b z = ((2 * z.re : ℝ) : ℂ) := by
  rw [Fintype.sum_bool]
  show conj z + z = _
  rw [add_comm, Complex.add_conj]

theorem tmetProd_ext (i₀ : I) (ε : {i // i ≠ i₀} → Bool) (f : I → ℂ) :
    ∏ i, archConjIf (tmetExt i₀ ε i) (f i) =
      f i₀ * ∏ i : {i // i ≠ i₀}, archConjIf (ε i) (f i) := by
  rw [Fintype.prod_eq_mul_prod_compl i₀,
    Finset.prod_subtype ({i₀}ᶜ : Finset I) (p := fun i => i ≠ i₀) (by simp)]
  rw [tmetExt_self]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by rw [tmetExt_ne]

theorem tmetSum_ext_prod (i₀ : I) (f : I → ℂ) :
    ∑ ε : {i // i ≠ i₀} → Bool, ∏ i, archConjIf (tmetExt i₀ ε i) (f i) =
      f i₀ * ∏ i : {i // i ≠ i₀}, ((2 * (f i).re : ℝ) : ℂ) := by
  simp_rw [tmetProd_ext, ← Finset.mul_sum, ← tmetSum_bool_conj]
  rw [Fintype.prod_sum]

theorem tmetRe_half (i₀ : I) (f : I → ℂ) :
    (f i₀ * ∏ i : {i // i ≠ i₀}, ((2 * (f i).re : ℝ) : ℂ)).re =
      2 ^ Fintype.card {i // i ≠ i₀} * ∏ i, (f i).re := by
  rw [← Complex.ofReal_prod, Complex.re_mul_ofReal, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.prod_eq_mul_prod_compl i₀ (fun i => (f i).re),
    Finset.prod_subtype ({i₀}ᶜ : Finset I) (p := fun i => i ≠ i₀) (by simp)]
  ring

theorem tmetSum_re (i₀ : I) (f : I → ℂ) :
    (∑ ε : {i // i ≠ i₀} → Bool, ∏ i, archConjIf (tmetExt i₀ ε i) (f i)).re =
      2 ^ Fintype.card {i // i ≠ i₀} * ∏ i, (f i).re := by
  rw [tmetSum_ext_prod, tmetRe_half]

omit [DecidableEq I] [Fintype V] [DecidableEq V] in
theorem tmetChar_inner_tprod (v : I → V) (s : I → Bool) (a b : I → V → ℂ) :
    inner ℝ (tmetChar v s (PiTensorProduct.tprod ℝ a)) (tmetChar v s (PiTensorProduct.tprod ℝ b)) =
      (∏ i, archConjIf (s i) (b i (v i) * conj (a i (v i)))).re := by
  rw [tmetChar_tprod, tmetChar_tprod, Complex.inner, map_prod, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  cases s i <;> simp [archConjIf]

omit [DecidableEq V] in
/-- The metric identity on pure tensors. -/
theorem tmetPhi_ds_tprod (i₀ : I) (a b : I → V → ℂ) :
    tmetDs _ (tmetPhiHom i₀ (PiTensorProduct.tprod ℝ a)) (tmetPhiHom i₀ (PiTensorProduct.tprod ℝ b))
      = 2 ^ Fintype.card {i // i ≠ i₀} *
        tmetForm I V (PiTensorProduct.tprod ℝ a) (PiTensorProduct.tprod ℝ b) := by
  rw [tmetForm_tprod, tmetDs_apply]
  refine (Finset.sum_congr rfl fun j _ => tmetChar_inner_tprod j.1 (tmetExt i₀ j.2) a b).trans ?_
  rw [Fintype.sum_prod_type]
  have hx : ∀ x : I → V, ∑ y : {i // i ≠ i₀} → Bool,
      (∏ i, archConjIf (tmetExt i₀ y i) (b i (x i) * conj (a i (x i)))).re =
        2 ^ Fintype.card {i // i ≠ i₀} * ∏ i, (b i (x i) * conj (a i (x i))).re := fun x => by
    rw [← Complex.re_sum]; exact tmetSum_re i₀ fun i => b i (x i) * conj (a i (x i))
  refine (Finset.sum_congr rfl fun x _ => hx x).trans ?_
  rw [← Finset.mul_sum]
  congr 1
  simp only [tmetDs_apply]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.prod_congr rfl fun i _ => (Complex.inner _ _).symm

omit [DecidableEq V] in
/-- **The metric identity.** The direct sum metric of `Φ x`, `Φ y` is `2^{|I|-1}` times the tensor
product metric of `x`, `y` (with `|I| - 1` written as the number of `i ≠ i₀`). -/
theorem tmetPhiHom_ds (i₀ : I) (x y : TmetSpace I V) :
    tmetDs _ (tmetPhiHom i₀ x) (tmetPhiHom i₀ y) =
      2 ^ Fintype.card {i // i ≠ i₀} * tmetForm I V x y := by
  have h : (tmetDs (TmetIdx I V i₀)).compl₁₂ (tmetPhiHom i₀).toLinearMap
      (tmetPhiHom i₀).toLinearMap = (2 ^ Fintype.card {i // i ≠ i₀} : ℝ) • tmetForm I V :=
    tmetBil_ext fun a b => by simpa using tmetPhi_ds_tprod i₀ a b
  simpa using congrArg (fun F : TmetSpace I V →ₗ[ℝ] TmetSpace I V →ₗ[ℝ] ℝ => F x y) h

theorem tmetPhiHom_injective (i₀ : I) : Function.Injective (tmetPhiHom (V := V) i₀) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply tmetForm_self_eq_zero
  have h := tmetPhiHom_ds i₀ x x
  simp only [hx, map_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (by positivity)

theorem tmetSpace_finrank :
    Module.finrank ℝ (TmetSpace I V) = (Fintype.card V * 2) ^ Fintype.card I := by
  rw [Module.finrank_eq_card_basis (tmetBasis I V)]
  simp [Fintype.card_sigma]

theorem tmetPhiHom_bijective (i₀ : I) : Function.Bijective (tmetPhiHom (V := V) i₀) := by
  have hI : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i₀⟩
  have hdim : Module.finrank ℝ (TmetSpace I V) = Module.finrank ℝ (TmetIdx I V i₀ → ℂ) := by
    rw [tmetSpace_finrank, Module.finrank_pi_fintype]
    simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      tmetIdx_card]
    obtain ⟨n, hn⟩ : ∃ n, Fintype.card I = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hI).symm⟩
    rw [hn, Nat.add_sub_cancel]
    ring
  have hi : Function.Injective (tmetPhiHom (V := V) i₀).toLinearMap := tmetPhiHom_injective i₀
  exact ⟨tmetPhiHom_injective i₀,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi⟩

/-- **The decomposition of `M_I`.** The isomorphism of `ℝ`-algebras
`Φ : M_I ≅ ⊕_{(v, ε) ∈ TmetIdx} ℂ`, `⊗ m_i ↦ (∏_i c_{ext ε i}(m_i(v_i)))_{(v, ε)}`, onto a
direct sum of `2^{|I|-1}·|V|^{|I|}` copies of `ℂ`. -/
noncomputable def tmetPhi (i₀ : I) : TmetSpace I V ≃ₐ[ℝ] (TmetIdx I V i₀ → ℂ) :=
  AlgEquiv.ofBijective (tmetPhiHom i₀) (tmetPhiHom_bijective i₀)

theorem tmetPhi_apply (i₀ : I) (x : TmetSpace I V) (j : TmetIdx I V i₀) :
    tmetPhi i₀ x j = tmetChar j.1 (tmetExt i₀ j.2) x := rfl

/-- **Proposition 1.5 (iii), the metric factor**, for the decomposition `tmetPhi`. -/
theorem tmetPhi_ds (i₀ : I) (x y : TmetSpace I V) :
    tmetDs _ (tmetPhi i₀ x) (tmetPhi i₀ y) = 2 ^ (Fintype.card I - 1) * tmetForm I V x y := by
  rw [← tmetIdx_card_ne i₀]; exact tmetPhiHom_ds i₀ x y


/-! ## Algebra isomorphisms between direct sums of copies of `ℂ` -/

/-- Every `ℝ`-algebra map `⊕_{j ∈ J} ℂ → ℂ` is a coordinate `z ↦ z_k` followed by the identity
or complex conjugation. -/
theorem tmetAlgHom_coord {J : Type*} [Fintype J] [DecidableEq J] (φ : (J → ℂ) →ₐ[ℝ] ℂ) :
    ∃ k : J, ∃ s : Bool, ∀ z, φ z = archConjIf s (z k) := by
  let e : J → J → ℂ := fun k => Pi.single k 1
  have he_idem : ∀ k, e k * e k = e k := fun k => by
    ext j; by_cases hj : j = k <;> simp [e, hj]
  have he_orth : ∀ k k', k ≠ k' → e k * e k' = 0 := fun k k' h => by
    ext j
    by_cases hj : j = k
    · subst hj; simp [e, h]
    · simp [e, hj]
  have he_sum : ∑ k, e k = 1 := by ext j; simp [e, Finset.sum_apply, Pi.single_apply]
  have h01 : ∀ k, φ (e k) = 0 ∨ φ (e k) = 1 := fun k => by
    have h : φ (e k) * (φ (e k) - 1) = 0 := by rw [mul_sub, ← map_mul, he_idem, mul_one, sub_self]
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  obtain ⟨k, hk⟩ : ∃ k, φ (e k) = 1 := by
    by_contra hne
    push Not at hne
    have h0 : ∑ k, φ (e k) = 0 := Finset.sum_eq_zero fun k _ => (h01 k).resolve_right (hne k)
    rw [← map_sum, he_sum, map_one] at h0
    exact one_ne_zero h0
  have hk' : ∀ k', k' ≠ k → φ (e k') = 0 := fun k' h => by
    have := congrArg φ (he_orth k' k h)
    rwa [map_mul, hk, mul_one, map_zero] at this
  let g : ℂ →ₐ[ℝ] ℂ := φ.comp (Pi.constAlgHom ℝ J ℂ)
  have hz : ∀ z : J → ℂ, z = ∑ k', Pi.constAlgHom ℝ J ℂ (z k') * e k' := fun z => by
    ext j; simp [e, Finset.sum_apply, Pi.single_apply]
  have hφ : ∀ z : J → ℂ, φ z = g (z k) := fun z => by
    conv_lhs => rw [hz z]
    rw [map_sum, Finset.sum_eq_single k]
    · rw [map_mul, hk, mul_one]; rfl
    · intro k' _ h; rw [map_mul, hk' k' h, mul_zero]
    · simp
  rcases Complex.real_algHom_eq_id_or_conj g with hg | hg
  · exact ⟨k, false, fun z => by rw [hφ, hg]; simp [archConjIf]⟩
  · exact ⟨k, true, fun z => by rw [hφ, hg]; simp [archConjIf]⟩

/-- The coordinates of an `ℝ`-algebra isomorphism `⊕_{J₁} ℂ ≅ ⊕_{J₂} ℂ`: each output coordinate
is an input coordinate `π j`, possibly conjugated, and `π` is surjective. -/
theorem tmetAlgEquiv_coord {J₁ J₂ : Type*} [Fintype J₁] [DecidableEq J₁] [Fintype J₂]
    [DecidableEq J₂] (θ : (J₁ → ℂ) ≃ₐ[ℝ] (J₂ → ℂ)) :
    ∃ π : J₂ → J₁, ∃ b : J₂ → Bool,
      Function.Surjective π ∧ ∀ z j, θ z j = archConjIf (b j) (z (π j)) := by
  have hc : ∀ j, ∃ k : J₁, ∃ s : Bool, ∀ z, θ z j = archConjIf s (z k) := fun j =>
    tmetAlgHom_coord ((Pi.evalAlgHom ℝ (fun _ : J₂ => ℂ) j).comp (θ : (J₁ → ℂ) →ₐ[ℝ] (J₂ → ℂ)))
  choose π b hπ using hc
  refine ⟨π, b, fun k => ?_, fun z j => hπ j z⟩
  have hne : θ (Pi.single k 1) ≠ 0 := by
    intro h
    have h' := θ.injective (h.trans (map_zero θ).symm)
    simpa using congrFun h' k
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  refine ⟨j, by_contra fun hjk => hj ?_⟩
  rw [hπ, Pi.single_apply, ite_eq_right_of_eq_false _ _ (eq_false hjk)]
  cases b j <;> simp [archConjIf]

/-- A map `T : ⊕_{J₁} ℂ → ⊕_{J₂} ℂ` is **monomial** if it is a bijection `π` of the summands
followed, on each summand, by the identity or complex conjugation and by multiplication by a
complex number of absolute value `1`. -/
def tmetMonomial {J₁ J₂ : Type*} (T : (J₁ → ℂ) → (J₂ → ℂ)) : Prop :=
  ∃ π : J₂ ≃ J₁, ∃ ω : J₂ → ℂ, ∃ b : J₂ → Bool,
    (∀ j, ‖ω j‖ = 1) ∧ ∀ z j, T z j = ω j * archConjIf (b j) (z (π j))

/-- **Uniqueness up to the obvious automorphisms.** Every `ℝ`-algebra isomorphism
`⊕_{J₁} ℂ ≅ ⊕_{J₂} ℂ` is a permutation of the summands followed by the identity or complex
conjugation on each summand (a monomial map with all multipliers `1`); in particular
`|J₁| = |J₂|`. -/
theorem tmetAlgEquiv_monomial {J₁ J₂ : Type*} [Fintype J₁] [DecidableEq J₁] [Fintype J₂]
    [DecidableEq J₂] (θ : (J₁ → ℂ) ≃ₐ[ℝ] (J₂ → ℂ)) :
    (∃ π : J₂ ≃ J₁, ∃ b : J₂ → Bool, ∀ z j, θ z j = archConjIf (b j) (z (π j))) ∧
      tmetMonomial θ ∧ Fintype.card J₁ = Fintype.card J₂ := by
  obtain ⟨π, b, hs, hπ⟩ := tmetAlgEquiv_coord θ
  obtain ⟨π', _, hs', _⟩ := tmetAlgEquiv_coord θ.symm
  have hcard : Fintype.card J₁ = Fintype.card J₂ :=
    le_antisymm (Fintype.card_le_of_surjective π hs) (Fintype.card_le_of_surjective π' hs')
  have hbij : Function.Bijective π :=
    (Fintype.bijective_iff_surjective_and_card π).mpr ⟨hs, hcard.symm⟩
  refine ⟨⟨Equiv.ofBijective π hbij, b, fun z j => hπ z j⟩,
    ⟨Equiv.ofBijective π hbij, fun _ => 1, b, fun _ => by simp, fun z j => by simp [hπ]⟩,
    hcard⟩

theorem tmetNorm_conjIf (s : Bool) (a : ℂ) : ‖archConjIf s a‖ = ‖a‖ := by
  cases s <;> simp [archConjIf]

theorem tmetNorm_unit {ω : ℂ} (hω : ‖ω‖ = 1) (s : Bool) (a : ℂ) :
    ‖ω * archConjIf s a‖ = ‖a‖ := by
  rw [norm_mul, hω, one_mul, tmetNorm_conjIf]

theorem tmetUnit_mul_eq_zero {ω : ℂ} (hω : ‖ω‖ = 1) (s : Bool) (a : ℂ) :
    ω * archConjIf s a = 0 ↔ a = 0 := by
  rw [← norm_eq_zero, tmetNorm_unit hω, norm_eq_zero]

theorem tmetInner_unit {ω : ℂ} (hω : ‖ω‖ = 1) (s : Bool) (a b : ℂ) :
    inner ℝ (ω * archConjIf s a) (ω * archConjIf s b) = inner ℝ a b := by
  have h1 : ω * conj ω = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hω]; simp
  simp only [Complex.inner]
  have h2 : ω * archConjIf s b * conj (ω * archConjIf s a) =
      (ω * conj ω) * (archConjIf s b * conj (archConjIf s a)) := by
    rw [map_mul]; ring
  rw [h2, h1, one_mul]
  cases s <;> simp [archConjIf, mul_re]

/-- A monomial map preserves the direct sum metric. -/
theorem tmetMonomial_ds {J₁ J₂ : Type*} [Fintype J₁] [Fintype J₂]
    {T : (J₁ → ℂ) → (J₂ → ℂ)} (hT : tmetMonomial T) (z w : J₁ → ℂ) :
    tmetDs J₂ (T z) (T w) = tmetDs J₁ z w := by
  obtain ⟨π, ω, b, hω, hT⟩ := hT
  simp only [tmetDs_apply, hT, tmetInner_unit (hω _)]
  exact Equiv.sum_comp π (fun k => inner ℝ (z k) (w k))

/-- The direct product of the closed unit balls of the copies of `ℂ` in `⊕_{j ∈ J} ℂ`. -/
noncomputable def tmetBall (J : Type*) : Set (J → ℂ) :=
  Set.univ.pi fun _ : J => Metric.closedBall (0 : ℂ) 1

theorem tmetMem_ball {J : Type*} {z : J → ℂ} : z ∈ tmetBall J ↔ ∀ j, ‖z j‖ ≤ 1 := by
  simp [tmetBall]

theorem tmetMonomial_ball_iff {J₁ J₂ : Type*} {T : (J₁ → ℂ) → (J₂ → ℂ)} (hT : tmetMonomial T)
    (z : J₁ → ℂ) : T z ∈ tmetBall J₂ ↔ z ∈ tmetBall J₁ := by
  obtain ⟨π, ω, b, hω, hT⟩ := hT
  simp only [tmetMem_ball, hT, tmetNorm_unit (hω _)]
  constructor
  · intro h k; simpa using h (π.symm k)
  · intro h j; exact h _

/-- The summand `ℂ_k` of `⊕_{j ∈ J} ℂ`. -/
def tmetSummand {J : Type*} [DecidableEq J] (k : J) : Set (J → ℂ) := Set.range (Pi.single k)

theorem tmetMem_summand {J : Type*} [DecidableEq J] {z : J → ℂ} {k : J} :
    z ∈ tmetSummand k ↔ ∀ k', k' ≠ k → z k' = 0 := by
  constructor
  · rintro ⟨c, rfl⟩ k' h; simp [h]
  · intro h
    refine ⟨z k, funext fun k' => ?_⟩
    by_cases hk : k' = k
    · subst hk; simp
    · simp [hk, h k' hk]

theorem tmetMonomial_preimage_summand {J₁ J₂ : Type*} [DecidableEq J₁] [DecidableEq J₂]
    {T : (J₁ → ℂ) → (J₂ → ℂ)} (hT : tmetMonomial T) (j : J₂) :
    ∃ k, T ⁻¹' tmetSummand j = tmetSummand k := by
  obtain ⟨π, ω, b, hω, hT⟩ := hT
  refine ⟨π j, Set.ext fun z => ?_⟩
  simp only [Set.mem_preimage, tmetMem_summand, hT, tmetUnit_mul_eq_zero (hω _)]
  constructor
  · intro h k hk
    have := h (π.symm k) (fun e => hk (by rw [← e]; simp))
    rwa [Equiv.apply_symm_apply] at this
  · intro h j' hj'
    exact h _ (fun e => hj' (π.injective e))

theorem tmetMonomial_surjective {J₁ J₂ : Type*} {T : (J₁ → ℂ) → (J₂ → ℂ)}
    (hT : tmetMonomial T) : Function.Surjective T := by
  obtain ⟨π, ω, b, hω, hT⟩ := hT
  intro y
  refine ⟨fun k => archConjIf (b (π.symm k)) ((ω (π.symm k))⁻¹ * y (π.symm k)), funext fun j => ?_⟩
  have hω0 : ω j ≠ 0 := fun h => by simpa [h] using hω j
  rw [hT]
  simp only [Equiv.symm_apply_apply, archConjIf_invol]
  field_simp

/-- A monomial map maps each summand onto a summand. -/
theorem tmetMonomial_image_summand {J₁ J₂ : Type*} [DecidableEq J₁] [DecidableEq J₂]
    {T : (J₁ → ℂ) → (J₂ → ℂ)} (hT : tmetMonomial T) (k : J₁) :
    ∃ k', T '' tmetSummand k = tmetSummand k' := by
  obtain ⟨π, ω, b, hω, hT'⟩ := hT
  obtain ⟨k₀, hk₀⟩ := tmetMonomial_preimage_summand ⟨π, ω, b, hω, hT'⟩ (π.symm k)
  have hk : k₀ = k := by
    obtain ⟨π₂, ω₂, b₂, hω₂, h₂⟩ := (⟨π, ω, b, hω, hT'⟩ : tmetMonomial T)
    -- the summand `ℂ_{k₀}` is nonempty of nonzero elements: compare at `Pi.single k₀ 1`
    have hmem : (Pi.single k₀ 1 : J₁ → ℂ) ∈ T ⁻¹' tmetSummand (π.symm k) := by
      rw [hk₀]; exact ⟨1, rfl⟩
    rw [Set.mem_preimage, tmetMem_summand] at hmem
    by_contra hne
    have := hmem (π.symm k₀) (fun e => hne (by simpa using congrArg π e))
    rw [hT', Equiv.apply_symm_apply, Pi.single_eq_same, tmetUnit_mul_eq_zero (hω _)] at this
    exact one_ne_zero this
  refine ⟨π.symm k, ?_⟩
  rw [← Set.image_preimage_eq (tmetSummand (π.symm k))
    (tmetMonomial_surjective ⟨π, ω, b, hω, hT'⟩), hk₀, hk]

/-! ## Uniqueness of the decomposition of `M_I` -/

omit [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] in
/-- **Uniqueness of the direct sum decomposition (Proposition 1.5 (iii)).** For two
decompositions `ψ₁ : M_I ≅ ⊕_{J₁} ℂ`, `ψ₂ : M_I ≅ ⊕_{J₂} ℂ` (isomorphisms of `ℝ`-algebras):
the numbers of copies agree, every summand of `ψ₂` is a summand of `ψ₁`, the two direct sum
metrics agree, and the two direct products of unit balls agree. -/
theorem tmetDecomp_unique {J₁ J₂ : Type*} [Fintype J₁] [DecidableEq J₁] [Fintype J₂]
    [DecidableEq J₂] (ψ₁ : TmetSpace I V ≃ₐ[ℝ] (J₁ → ℂ)) (ψ₂ : TmetSpace I V ≃ₐ[ℝ] (J₂ → ℂ)) :
    Fintype.card J₁ = Fintype.card J₂ ∧
      (∀ j, ∃ k, ψ₂ ⁻¹' tmetSummand j = ψ₁ ⁻¹' tmetSummand k) ∧
      (∀ x y, tmetDs J₂ (ψ₂ x) (ψ₂ y) = tmetDs J₁ (ψ₁ x) (ψ₁ y)) ∧
      ψ₂ ⁻¹' tmetBall J₂ = ψ₁ ⁻¹' tmetBall J₁ := by
  obtain ⟨-, hmon, hcard⟩ := tmetAlgEquiv_monomial (ψ₁.symm.trans ψ₂)
  have hψ : ∀ x, ψ₂ x = (ψ₁.symm.trans ψ₂) (ψ₁ x) := fun x => by simp
  refine ⟨hcard, fun j => ?_, fun x y => ?_, ?_⟩
  · obtain ⟨k, hk⟩ := tmetMonomial_preimage_summand hmon j
    refine ⟨k, Set.ext fun x => ?_⟩
    change ψ₂ x ∈ tmetSummand j ↔ ψ₁ x ∈ tmetSummand k
    rw [hψ x, ← hk, Set.mem_preimage]
  · rw [hψ x, hψ y]; exact tmetMonomial_ds hmon _ _
  · ext x
    change ψ₂ x ∈ tmetBall J₂ ↔ ψ₁ x ∈ tmetBall J₁
    rw [hψ x]; exact tmetMonomial_ball_iff hmon _

/-- **Proposition 1.5 (iii), the count and the metric factor, for every decomposition.** For
`I` nonempty and every isomorphism of `ℝ`-algebras `ψ : M_I ≅ ⊕_{j ∈ J} ℂ`: `J` has
`2^{|I|-1}·|V|^{|I|}` elements, and the direct sum metric is `2^{|I|-1}` times the tensor
product metric. -/
theorem tmetProp1_5_iii_metric [Nonempty I] {J : Type*} [Fintype J] [DecidableEq J]
    (ψ : TmetSpace I V ≃ₐ[ℝ] (J → ℂ)) :
    Fintype.card J = 2 ^ (Fintype.card I - 1) * Fintype.card V ^ Fintype.card I ∧
      ∀ x y, tmetDs J (ψ x) (ψ y) = 2 ^ (Fintype.card I - 1) * tmetForm I V x y := by
  obtain ⟨i₀⟩ := ‹Nonempty I›
  obtain ⟨hc, -, hds, -⟩ := tmetDecomp_unique (tmetPhi (V := V) i₀) ψ
  exact ⟨by rw [← hc]; exact tmetIdx_card i₀, fun x y => by rw [hds, tmetPhi_ds]⟩

/-- The page's **integral structure** `B_I ⊆ M_I`: the direct product of the unit balls of the
copies of `ℂ` in the decomposition, i.e. the elements all of whose components have length at
most `1`. It is defined with `tmetPhi i₀`; `tmetIntegral_eq` shows that every decomposition
(and every `i₀`) gives the same set. -/
noncomputable def tmetIntegral (i₀ : I) : Set (TmetSpace I V) :=
  tmetPhi i₀ ⁻¹' tmetBall (TmetIdx I V i₀)

theorem tmetMem_integral {i₀ : I} {x : TmetSpace I V} :
    x ∈ tmetIntegral i₀ ↔ ∀ j, ‖tmetPhi i₀ x j‖ ≤ 1 := tmetMem_ball

/-- `B_I` does not depend on the decomposition. -/
theorem tmetIntegral_eq (i₀ : I) {J : Type*} [Fintype J] [DecidableEq J]
    (ψ : TmetSpace I V ≃ₐ[ℝ] (J → ℂ)) : ψ ⁻¹' tmetBall J = tmetIntegral i₀ :=
  (tmetDecomp_unique (tmetPhi i₀) ψ).2.2.2

/-- A ring isomorphism `ψ : M_I ≅ ⊕_{j ∈ J} ℂ` that is continuous for the topology of `M_I`
carried over from `⊕ ℂ` by `tmetPhi i₀` (the product topology of the copies of `ℂ`) is
`ℝ`-linear, hence an isomorphism of `ℝ`-algebras. -/
noncomputable def tmetAlgEquivOfContinuous (i₀ : I) {J : Type*} (ψ : TmetSpace I V ≃+* (J → ℂ))
    (hψ : Continuous fun z => ψ ((tmetPhi i₀).symm z)) : TmetSpace I V ≃ₐ[ℝ] (J → ℂ) :=
  AlgEquiv.ofRingEquiv (f := ψ) fun r => by
    have h := map_real_smul
      (ψ.toAddMonoidHom.comp (tmetPhi i₀).symm.toRingEquiv.toAddMonoidHom) hψ r 1
    change ψ ((tmetPhi i₀).symm (r • 1)) = r • ψ ((tmetPhi i₀).symm 1) at h
    rw [map_smul, map_one, map_one] at h
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    exact h

/-- **Proposition 1.5 (iii) for isomorphisms of topological rings.** For every ring
isomorphism `ψ : M_I ≅ ⊕_{j ∈ J} ℂ` that is continuous for the topology of `M_I` carried over by
`tmetPhi i₀`: `J` has `2^{|I|-1}·|V|^{|I|}` elements, the direct sum metric is `2^{|I|-1}` times
the tensor product metric, and the direct product of the unit balls is `B_I`. -/
theorem tmetProp1_5_iii_topological (i₀ : I) {J : Type*} [Fintype J] [DecidableEq J]
    (ψ : TmetSpace I V ≃+* (J → ℂ)) (hψ : Continuous fun z => ψ ((tmetPhi i₀).symm z)) :
    Fintype.card J = 2 ^ (Fintype.card I - 1) * Fintype.card V ^ Fintype.card I ∧
      (∀ x y, tmetDs J (ψ x) (ψ y) = 2 ^ (Fintype.card I - 1) * tmetForm I V x y) ∧
      ψ ⁻¹' tmetBall J = tmetIntegral i₀ := by
  have : Nonempty I := ⟨i₀⟩
  obtain ⟨h1, h2⟩ := tmetProp1_5_iii_metric (tmetAlgEquivOfContinuous i₀ ψ hψ)
  exact ⟨h1, h2, tmetIntegral_eq i₀ (tmetAlgEquivOfContinuous i₀ ψ hψ)⟩

/-! ## The automorphisms induced by primitive automorphisms -/

/-- The automorphism of `M = ⊕_{v ∈ V} ℂ_v` that applies `g v` on the summand `ℂ_v`. -/
noncomputable def tmetFactorMap (g : V → (ℂ ≃ₗᵢ[ℝ] ℂ)) : (V → ℂ) →ₗ[ℝ] (V → ℂ) :=
  LinearMap.pi fun w => ((g w).toLinearEquiv : ℂ →ₗ[ℝ] ℂ) ∘ₗ LinearMap.proj w

omit [Fintype V] [DecidableEq V] in
theorem tmetFactorMap_apply (g : V → (ℂ ≃ₗᵢ[ℝ] ℂ)) (m : V → ℂ) (w : V) :
    tmetFactorMap g m w = g w (m w) := rfl

/-- The automorphism of `M_I` induced by automorphisms `f i v` of the direct summands `ℂ_v` of
the factors `M_i`: the tensor product over `i` of the maps `tmetFactorMap (f i)`. -/
noncomputable def tmetInduced (f : I → V → (ℂ ≃ₗᵢ[ℝ] ℂ)) : TmetSpace I V →ₗ[ℝ] TmetSpace I V :=
  PiTensorProduct.map fun i => tmetFactorMap (f i)

omit [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] in
theorem tmetInduced_comp (f g : I → V → (ℂ ≃ₗᵢ[ℝ] ℂ)) (x : TmetSpace I V) :
    tmetInduced f (tmetInduced g x) = tmetInduced (fun i w => f i w * g i w) x := by
  have h : tmetInduced f ∘ₗ tmetInduced g = tmetInduced (fun i w => f i w * g i w) :=
    tmetLin_ext fun a => by
      simp only [LinearMap.comp_apply, tmetInduced, PiTensorProduct.map_tprod]
      congr 1
  exact congrArg (fun F : TmetSpace I V →ₗ[ℝ] TmetSpace I V => F x) h

omit [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] in
theorem tmetInduced_one (x : TmetSpace I V) : tmetInduced (fun _ _ => 1) x = x := by
  have h : tmetInduced (I := I) (V := V) (fun _ _ => 1) = LinearMap.id :=
    tmetLin_ext fun a => by
      simp only [tmetInduced, PiTensorProduct.map_tprod, LinearMap.id_apply]
      congr 1
  exact congrArg (fun F : TmetSpace I V →ₗ[ℝ] TmetSpace I V => F x) h

omit [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] in
theorem tmetInduced_inv (f : I → V → (ℂ ≃ₗᵢ[ℝ] ℂ)) (x : TmetSpace I V) :
    tmetInduced f (tmetInduced (fun i w => (f i w)⁻¹) x) = x := by
  rw [tmetInduced_comp]; simp only [mul_inv_cancel]; exact tmetInduced_one x

omit [DecidableEq I] [Fintype V] [DecidableEq V] in
/-- How a character transforms under an induced automorphism, for `f i w = u_{i,w}·c_{t_{i,w}}`. -/
theorem tmetChar_induced (f : I → V → (ℂ ≃ₗᵢ[ℝ] ℂ)) (u : I → V → ℂ) (t : I → V → Bool)
    (hf : ∀ i w z, f i w z = u i w * archConjIf (t i w) z) (v : I → V) (s : I → Bool)
    (x : TmetSpace I V) :
    tmetChar v s (tmetInduced f x) =
      (∏ i, archConjIf (s i) (u i (v i))) * tmetChar v (fun i => xor (s i) (t i (v i))) x := by
  have h : (tmetChar v s).toLinearMap ∘ₗ tmetInduced f =
      LinearMap.mulLeft ℝ (∏ i, archConjIf (s i) (u i (v i))) ∘ₗ
        (tmetChar v fun i => xor (s i) (t i (v i))).toLinearMap := tmetLin_ext fun m => by
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, tmetInduced,
      PiTensorProduct.map_tprod, tmetChar_tprod, LinearMap.mulLeft_apply, tmetFactorMap_apply, hf]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [archConjIf_mul, archConjIf_conjIf]
  exact congrArg (fun F : TmetSpace I V →ₗ[ℝ] ℂ => F x) h

/-- In the coordinates of `tmetPhi i₀`, an automorphism of `M_I` induced by primitive
automorphisms is monomial. -/
theorem tmetInduced_monomial (i₀ : I) (f : I → V → (ℂ ≃ₗᵢ[ℝ] ℂ))
    (hf : ∀ i w, f i w ∈ archPrimitive) :
    tmetMonomial fun z => tmetPhi i₀ (tmetInduced f ((tmetPhi i₀).symm z)) := by
  choose u hu t ht using fun i w => archPrimitive_form (hf i w)
  have hun : ∀ i w, ‖u i w‖ = 1 := fun i w => by
    have h := congrArg norm (hu i w)
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h
  let ρ : TmetIdx I V i₀ → TmetIdx I V i₀ := fun j =>
    (j.1, fun i => xor (xor (j.2 i) (t i (j.1 i))) (t i₀ (j.1 i₀)))
  have hρ : Function.Involutive ρ := by
    rintro ⟨v, ε⟩
    simp only [ρ, Prod.mk.injEq, true_and]
    funext i
    cases ε i <;> cases t i (v i) <;> cases t i₀ (v i₀) <;> rfl
  refine ⟨hρ.toPerm ρ, fun j => ∏ i, archConjIf (tmetExt i₀ j.2 i) (u i (j.1 i)),
    fun j => t i₀ (j.1 i₀), fun j => ?_, fun z j => ?_⟩
  · rw [norm_prod]
    exact Finset.prod_eq_one fun i _ => by rw [tmetNorm_conjIf, hun]
  · obtain ⟨v, ε⟩ := j
    have hz : z (ρ (v, ε)) = tmetChar v (tmetExt i₀ (ρ (v, ε)).2) ((tmetPhi i₀).symm z) := by
      rw [show tmetChar v (tmetExt i₀ (ρ (v, ε)).2) ((tmetPhi i₀).symm z) =
        tmetPhi i₀ ((tmetPhi i₀).symm z) (ρ (v, ε)) from rfl, AlgEquiv.apply_symm_apply]
    have hs : (fun i => xor (tmetExt i₀ ε i) (t i (v i))) =
        fun i => xor (tmetExt i₀ (ρ (v, ε)).2 i) (t i₀ (v i₀)) := by
      funext i
      by_cases hi : i = i₀
      · rw [hi, tmetExt_self, tmetExt_self]
      · simp only [tmetExt, dite_eq_right_of_eq_false (eq_false hi), ρ]
        cases ε ⟨i, hi⟩ <;> cases t i (v i) <;> cases t i₀ (v i₀) <;> rfl
    simp only [Function.Involutive.coe_toPerm]
    rw [hz, tmetPhi_apply, tmetChar_induced f u t ht, ← tmetChar_xor_const, hs]

theorem tmetInduced_mapsTo (i₀ : I) (f : I → V → (ℂ ≃ₗᵢ[ℝ] ℂ))
    (hf : ∀ i w, f i w ∈ archPrimitive) {x : TmetSpace I V} (hx : x ∈ tmetIntegral i₀) :
    tmetInduced f x ∈ tmetIntegral i₀ := by
  have h := (tmetMonomial_ball_iff (tmetInduced_monomial i₀ f hf) (tmetPhi i₀ x)).mpr hx
  simp only [AlgEquiv.symm_apply_apply] at h
  exact h

/-- **Proposition 1.5 (iii), preservation.** Let `f i v` be primitive automorphisms of the
direct summands `ℂ_v` of the factors `M_i`, and `T` the induced automorphism of `M_I`. Then `T`
preserves the tensor product metric, the induced map `Φ ∘ T ∘ Φ⁻¹` of `⊕ ℂ` maps each summand
onto a summand, `T` preserves the direct sum metric, and `T(B_I) = B_I`. -/
theorem tmetProp1_5_iii_preserved (i₀ : I) (f : I → V → (ℂ ≃ₗᵢ[ℝ] ℂ))
    (hf : ∀ i w, f i w ∈ archPrimitive) :
    (∀ x y, tmetForm I V (tmetInduced f x) (tmetInduced f y) = tmetForm I V x y) ∧
      (∀ k, ∃ k', (fun z => tmetPhi i₀ (tmetInduced f ((tmetPhi i₀).symm z))) ''
        tmetSummand k = tmetSummand k') ∧
      (∀ x y, tmetDs _ (tmetPhi i₀ (tmetInduced f x)) (tmetPhi i₀ (tmetInduced f y)) =
        tmetDs _ (tmetPhi i₀ x) (tmetPhi i₀ y)) ∧
      tmetInduced f '' tmetIntegral i₀ = tmetIntegral i₀ := by
  have hmon := tmetInduced_monomial i₀ f hf
  have hT : ∀ x, tmetPhi i₀ (tmetInduced f x) =
      (fun z => tmetPhi i₀ (tmetInduced f ((tmetPhi i₀).symm z))) (tmetPhi i₀ x) :=
    fun x => by simp
  have hds : ∀ x y, tmetDs _ (tmetPhi i₀ (tmetInduced f x)) (tmetPhi i₀ (tmetInduced f y)) =
      tmetDs _ (tmetPhi i₀ x) (tmetPhi i₀ y) := fun x y => by
    rw [hT x, hT y]; exact tmetMonomial_ds hmon _ _
  refine ⟨fun x y => ?_, tmetMonomial_image_summand hmon, hds, ?_⟩
  · have h := hds x y
    rw [tmetPhi_ds, tmetPhi_ds] at h
    exact mul_left_cancel₀ (by positivity) h
  · refine Set.Subset.antisymm ?_ fun y hy => ?_
    · rintro _ ⟨x, hx, rfl⟩; exact tmetInduced_mapsTo i₀ f hf hx
    · exact ⟨_, tmetInduced_mapsTo i₀ (fun i w => (f i w)⁻¹)
        (fun i w => Subgroup.inv_mem _ (hf i w)) hy, tmetInduced_inv f y⟩

/-! ## (iv): tensor products of vectors of a given length -/

/-- If every component of every `m_i` has length at most `r`, then `⊗ m_i ∈ r^{|I|}·B_I`. -/
theorem tmetTprod_mem_of_le (i₀ : I) {r : ℝ} (hr : 0 < r) (m : I → V → ℂ)
    (hm : ∀ i w, ‖m i w‖ ≤ r) :
    PiTensorProduct.tprod ℝ m ∈ r ^ Fintype.card I • tmetIntegral (V := V) i₀ := by
  have hrn : 0 < r ^ Fintype.card I := pow_pos hr _
  refine Set.mem_smul_set.mpr ⟨(r ^ Fintype.card I)⁻¹ • PiTensorProduct.tprod ℝ m, ?_,
    smul_inv_smul₀ hrn.ne' _⟩
  rw [tmetMem_integral]
  intro j
  rw [map_smul, Pi.smul_apply, norm_smul, tmetPhi_apply, tmetChar_tprod, norm_prod,
    Real.norm_of_nonneg (inv_nonneg.mpr hrn.le)]
  have hle : ∏ i, ‖archConjIf (tmetExt i₀ j.2 i) (m i (j.1 i))‖ ≤ r ^ Fintype.card I := by
    calc ∏ i, ‖archConjIf (tmetExt i₀ j.2 i) (m i (j.1 i))‖ ≤ ∏ _i : I, r :=
          by gcongr with i; rw [tmetNorm_conjIf]; exact hm _ _
      _ = r ^ Fintype.card I := by rw [Finset.prod_const, Finset.card_univ]
  calc (r ^ Fintype.card I)⁻¹ * ∏ i, ‖archConjIf (tmetExt i₀ j.2 i) (m i (j.1 i))‖
      ≤ (r ^ Fintype.card I)⁻¹ * r ^ Fintype.card I :=
        mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hrn.le)
    _ = 1 := inv_mul_cancel₀ hrn.ne'

/-- **Proposition 1.5 (iv).** Fix `λ > 0`. If the component of `m_i` in each direct summand
`ℂ_v` of `M_i` has length `λ`, then `⊗_{i ∈ I} m_i ∈ λ^{|I|}·B_I`. -/
theorem tmetProp1_5_iv (i₀ : I) {lam : ℝ} (hlam : 0 < lam) (m : I → V → ℂ)
    (hm : ∀ i w, ‖m i w‖ = lam) :
    PiTensorProduct.tprod ℝ m ∈ lam ^ Fintype.card I • tmetIntegral (V := V) i₀ :=
  tmetTprod_mem_of_le i₀ hlam m fun i w => (hm i w).le


/-! ## Step (vii) of the proof of Theorem 1.10 on `B_I` -/

theorem tmetImage_smul {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] (L : E →ₗ[ℝ] F) (c : ℝ) (s : Set E) : L '' (c • s) = c • L '' s := by
  ext z
  simp only [Set.mem_image, Set.mem_smul_set]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨L y, ⟨y, hy, rfl⟩, (map_smul L c y).symm⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨c • y, ⟨y, hy, rfl⟩, map_smul L c y⟩

theorem tmetBall_volume_ne_zero (J : Type*) [Fintype J] :
    MeasureTheory.volume (tmetBall J) ≠ 0 := by
  have hopen : IsOpen (Set.univ.pi fun _ : J => Metric.ball (0 : ℂ) 1) :=
    isOpen_set_pi Set.finite_univ fun _ _ => Metric.isOpen_ball
  have hpos := hopen.measure_ne_zero MeasureTheory.volume ⟨0, by simp⟩
  exact fun h0 => hpos (MeasureTheory.measure_mono_null
    (Set.pi_mono fun _ _ => Metric.ball_subset_closedBall) h0)

theorem tmetBall_volume_ne_top (J : Type*) [Fintype J] :
    MeasureTheory.volume (tmetBall J) ≠ ⊤ :=
  (isCompact_univ_pi fun _ => isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne

/-- In the coordinates of the decomposition, `B_I` is the direct product of the closed unit balls
of the copies of `ℂ` (the set `stepsVIIUnitBalls` of `IUT.PaperIV.Theorem1_10.StepsIVtoVII`, there
indexed by `Fin N`). -/
theorem tmetPhi_image_integral (i₀ : I) :
    tmetPhi i₀ '' tmetIntegral (V := V) i₀ = tmetBall (TmetIdx I V i₀) :=
  Set.image_preimage_eq _ (tmetPhi i₀).surjective

/-- **Step (vii) of the proof of Theorem 1.10, on the page's `B_I`** (pages 29 and 30, with
`|I|` in place of `j + 1`). For `I`, `V` nonempty: every tensor product `⊗ m_i` whose
components all have length at most `π` lies in the container `π^{|I|}·B_I`; the container is
preserved by every automorphism of `M_I` induced by primitive automorphisms; and its
log-volume, normalized so that `B_I` has log-volume `0` and divided by the real dimension
(computed with the Lebesgue measure transported by `tmetPhi i₀`), is `|I|·log(π)`. -/
theorem tmetStepVII_container_logVolume [Nonempty V] (i₀ : I) :
    (∀ m : I → V → ℂ, (∀ i w, ‖m i w‖ ≤ Real.pi) →
        PiTensorProduct.tprod ℝ m ∈ Real.pi ^ Fintype.card I • tmetIntegral (V := V) i₀) ∧
      (∀ f : I → V → (ℂ ≃ₗᵢ[ℝ] ℂ), (∀ i w, f i w ∈ archPrimitive) →
        tmetInduced f '' (Real.pi ^ Fintype.card I • tmetIntegral (V := V) i₀) =
          Real.pi ^ Fintype.card I • tmetIntegral i₀) ∧
      Real.log ((MeasureTheory.volume
          (tmetPhi i₀ '' (Real.pi ^ Fintype.card I • tmetIntegral (V := V) i₀))).toReal /
          (MeasureTheory.volume (tmetPhi i₀ '' tmetIntegral (V := V) i₀)).toReal) /
          Module.finrank ℝ (TmetIdx I V i₀ → ℂ) = Fintype.card I * Real.log Real.pi := by
  refine ⟨fun m hm => tmetTprod_mem_of_le i₀ Real.pi_pos m hm, fun f hf => ?_, ?_⟩
  · rw [tmetImage_smul, (tmetProp1_5_iii_preserved i₀ f hf).2.2.2]
  · have hsurj := tmetPhi_image_integral (V := V) i₀
    have hsmul : tmetPhi (V := V) i₀ '' (Real.pi ^ Fintype.card I • tmetIntegral i₀) =
        Real.pi ^ Fintype.card I • tmetPhi i₀ '' tmetIntegral i₀ :=
      tmetImage_smul (tmetPhi (V := V) i₀).toLinearEquiv.toLinearMap _ _
    have hd : 0 < Module.finrank ℝ (TmetIdx I V i₀ → ℂ) := Module.finrank_pos
    rw [hsmul, hsurj, IUT.PaperIV.Theorem1_10.stepsVII_logVolume_smul MeasureTheory.volume hd
      (tmetBall_volume_ne_zero _) (tmetBall_volume_ne_top _) (pow_pos Real.pi_pos _),
      Real.log_pow]

end IUT.PaperIV.Proposition1_5
