import IUT.PaperIV.LocalFields.Packets
import IUT.PaperIII.Corollary312.LabelAverage

/-!
# IUT III, Remark 3.1.1 and Proposition 3.9 (i), (ii): weighted log-volumes on tensor packets

Source: Mochizuki, *Inter-universal Teichmüller Theory III*, Remark 3.1.1 (i) to (iv), pages 93
to 97; Proposition 3.9 (i), (ii), pages 115 to 117; Remark 3.9.5 (i), (ii), page 127. Pages read
for this file: 93, 94, 95, 96, 97, 115, 116, 117 and 127. Pages checked against rendered images:
all of them; the displays of page 94 and the normalization sentence of page 115 also at a higher
resolution.

## What the pages print

* Page 94, Remark 3.1.1 (ii). For `v ∈ 𝕍` the log-volume on the portion of `𝔩𝔬𝔤(^α ℱ_v)`
  corresponding to `K_v` is considered "relative to the weight `[K_v : (F_mod)_v]^{-1}`"; for
  direct sums over all `v ∈ 𝕍` over a given `v_ℚ`, "the normalized weight"
  `1 / ([K_v : (F_mod)_v] · (Σ_{𝕍_mod ∋ w | v_ℚ} [(F_mod)_w : ℚ_{v_ℚ}]))`, "normalized so that
  multiplication by `p_{v_ℚ}` affects log-volumes by addition or subtraction [...] of the
  quantity `log(p_{v_ℚ})`". For the tensor product of the `K_{v_α}`, `α ∈ A`, the weight
  `1 / Π_{α ∈ A} [K_{v_α} : (F_mod)_{v_α}]`, and for direct sums over all choices of
  `{v_α}_{α ∈ A}` the normalized weight
  `1 / ((Π_{α ∈ A} [K_{v_α} : (F_mod)_{v_α}]) · {Σ_{{w_α}_{α ∈ A}} (Π_{α ∈ A}
  [(F_mod)_{w_α} : ℚ_{v_ℚ}])})`, "where the sum is over all collections `{w_α}_{α ∈ A}` of
  [not necessarily distinct!] elements `w_α ∈ 𝕍_mod` lying over `v_ℚ`".
* Page 93, Proposition 3.1 (i), (ii), and page 94, Remark 3.1.1 (i): the ind-topological ring
  `𝔩𝔬𝔤(^A ℱ_{v_ℚ})` is an inductive limit of direct sums of fields, and the integral structures
  are copies of `𝒪_{k̄}`.
* Page 95, Remark 3.1.1 (iii): "such weighted sums of log-volumes do not, in general, arise as
  some positive real multiple of the [natural] logarithm of a 'volume' or 'measure' in the
  usual sense of measure theory"; they are clear on a "direct product region" (a direct product
  of compact subsets of positive measure in each of the direct summands), and "may be computed
  for, say, arbitrary Borel sets" by the construction of (iv), with `V = Π_{α ∈ A} 𝕍_{v_ℚ}` and
  (page 96) `N_v = Π_{α ∈ A} [K_{v_α} : (F_mod)_{v_α}]`; "the result of multiplying the
  [natural] logarithm of the '𝓔-weighted measure `μ_𝓔(−)`' of (iv) by a suitable normalization
  factor [i.e., a suitable positive real number] yields the weighted sums of log-volumes".
* Pages 96 and 97, Remark 3.1.1 (iv): `E = Π_{v'} E_{v'}`, `E_{≠v} = Π_{v' ≠ v} E_{v'}`,
  `W = ⨿_{v'} E_{≠v'} × {v'}`, `M_{E*V} ≅ M_W`, `S_E = {Π_{e ∈ E} S} ∩ M_{E*V}`, and for a
  direct product region `S = Π_v S_v`:
  `(1/N_𝓔) · μ^log_𝓔(S) = Σ_{v ∈ V} (1/N_v) · μ^log_v(S_v)`, `N_𝓔 = Π_{v ∈ V} N_v`.
* Page 115, Proposition 3.9 (i): the log-volumes `μ^log_{α,v_ℚ}`, `μ^log_{A,v_ℚ}`,
  `μ^log_{A,α,v}` on nonempty compact open subsets, determined by the `p_{v_ℚ}`-adic log-volume
  on each direct summand field "together with the discussion of normalized weights in Remark
  3.1.1, (ii), (iii), (iv)", such that the integral structures have log-volume zero, and
  "normalized so that multiplication of an element of `𝔐(−)` by `p_v` corresponds to adding
  the quantity `−log(p_v)`": the packet-normalization. Page 116: the archimedean analogue (radial
  log-volumes; multiplication by `e` adds `1 = log(e)`); `μ^log_{A,v_ℚ}` is invariant under
  permutations of `A`; for a procession, the log-volumes are normalized "by taking the
  average, over the various capsules under consideration": the procession-normalization.
  Proposition 3.9 (ii), pages 116 and 117: the same on the mono-analytic log-shells, and the
  average of the packet-normalized log-volumes gives procession-normalized log-volumes.
* Page 127, Remark 3.9.5 (i), (ii): for a subset that contains a relatively compact subset of
  finite log-volume, the holomorphic hull `λ · 𝒪` of the subset, when it is relatively compact, is
  a direct product region (`ℍ ⊆ ℙ`), so its packet-normalized log-volume is a weighted sum of the
  kind computed here; see `PacketHull.lean` for the hull on a product of fields.

## What is formalized

*Weights* (plain inputs `e(v) = [K_v : (F_mod)_v]`, `f(v) = [(F_mod)_v : ℚ_{v_ℚ}]`, a finite set
`V` of places over `v_ℚ`, a finite label set `A`; tuples are `t : A → V`, and `A = Fin (j + 1)`
gives `V^{j+1}`). `wPktWeight` is the normalized weight of page 94 exactly as printed;
`wPktDenom_eq_pow`: its denominator sum is `(Σ_v f(v)) ^ |A|`. `wPkt_weight_dim_sum`:
`Σ_t w_t · dim_t = 1`, with `dim_t = Π_α e(v_α) f(v_α)` the dimension of the summand; the
weights themselves sum to `(Σ_v 1/e(v)) ^ |A| / (Σ_v f(v)) ^ |A|` (`wPkt_weight_sum`), which is
`1/2` for one place with `e = 2`, `f = 1` and one label (`wPkt_weight_sum_example`).

*Real packets.* Fields `F v` (the role of `(F_mod)_v`) and `K v` (the role of `K_v`), finite over
`ℚ_p`, with `K v` a finite extension of `F v`; `e`, `f` are their degrees (`wPktE`, `wPktF`), and
`[K_v : ℚ_p] = e(v) f(v)` is the tower law (`wPkt_finrank_tower`). The summand of `t` is the
packet `⊗_α K_{v_α}` (`PiTensorProduct` over `ℚ_p`). `wPktSummandLogVol` is its unnormalized
log-volume `L_t` (logarithm of a Haar measure, zero on the integral elements; it is `dim_t`
times `padicPacketMuLog`). `wPktLogVol` is the weighted sum `Σ_t w_t · L_t(X_t)` on a direct
product region `Π_t X_t`.
* Tests (`wPkt_logVol_integral`, `wPkt_logVol_zpow_smul`, `wPkt_logVol_integral_zpow`): the
  integral structure has log-volume `0`; multiplying every component by `p ^ n` subtracts
  exactly `n log p`.
* Double division (`wPkt_doubleDivision_zpow_smul`): the page's weights applied to log-volumes
  already divided by the dimension shift by `−n (Σ_t w_t) log p`, which differs from `−n log p`
  in general. So, in general, only the unnormalized `L_t` give the printed normalization with the
  printed weights (the other reading passes when `Σ_t w_t = 1`); the pages do not state which is
  meant.

*Comparison with the Haar normalization of the whole packet* (`scope: model_test` in the
records). For a `ℚ_p`-algebra isomorphism `G` from a finite `ℚ_p`-algebra `W` onto
`Π_t ⊗_α K_{v_α}` (the decomposition of Proposition 3.1 (i); an input here), the log-volume of
`W` normalized by its dimension (`padicPacketMuLog`, as in `Packets.lean`) is
`Σ_t (1/dim W) · L_t(X_t)` with `dim W = (Σ_v e(v) f(v)) ^ |A|` (`wPkt_haar_region`; the general
form for summands that are packets is `wPkt_muLog_pi_region`). In terms of the per-dimension
log-volumes `L_t / dim_t` of `Packets.lean`, the Haar weights are `dim_t / dim W`, the page's are
`w_t · dim_t = Π_α f(v_α) / (Σ_v f(v)) ^ |A|`. The result:
* `wPkt_weight_eq_haar_mul`: `w_t = (1/dim W) · Π_α (ē / e(v_α))`, with
  `ē = Σ_v e(v) f(v) / Σ_v f(v)`.
* `wPkt_weight_eq_haar_iff`: in the reading of this module, for nonempty label and place sets
  and positive degrees, the two normalizations have the same weights for every tuple if and only
  if `[K_v : (F_mod)_v]` is the same at all places over `p`; then the two log-volumes
  agree on every direct product region (`wPkt_logVol_eq_haar_of_const`). In general they differ
  by `Σ_t (w_t − 1/dim W) · L_t(X_t)` (`wPkt_logVol_sub_haar`).
* Both normalizations pass both tests (both weight systems give total `1` against `dim_t`), so the
  tests do not determine the weights. `wPkt_scaled_integral` and `wPkt_coeff_example`: for
  `e = (1, 2)`, `f = (1, 1)`, one label and the region `p · 𝒪` on the first summand, `𝒪` on the
  second, the coefficients of `−log p` are `1/2` (page) and `1/3` (Haar).

*Procession-normalization* (`wPktProcAvg`, `wPktProcLogVol`): the average over a finite
nonempty set `J` of capsules, the capsule `j` with its own label set `L j`, of the
packet-normalized log-volumes; the two tests hold (`wPkt_procLogVol_integral`,
`wPkt_procLogVol_zpow_smul`). The abstract layer is an instance: on real values
`equalWeightAverage` of `Comparison.lean` is `wPktProcAvg` (`wPktProcAvg_eq_equalWeightAverage`),
and `labelAverage` of `LabelAverage.lean` is `wPktProcAvg` over `𝔽_l^⋇`
(`wPktProcAvg_eq_labelAverage`). The abstract layer takes the per-label values as free inputs;
here they are the weighted log-volumes of real packets.

*Remark 3.1.1 (iv)* (`wPktEMeasure`, `wPkt_EMeasure_log`): the `𝓔`-weighted measure, defined on
all subsets of `M_V` through `M_W` (the page's homeomorphism `M_{E*V} ≅ M_W` is used as the
definition of the measure space), and the display of page 97 on direct product regions, for
any finite `V`, nonempty finite `E_v` and σ-finite measures.

*The warning of page 95, made precise in a model* (`scope: model_test`):
`wPkt_warning_forces_equal`, `wPkt_warning_iff`: on `ℝ × ℝ` with Lebesgue measure on each
factor and positive weights `a`, `b`, there are a measure `ν` on `ℝ × ℝ` and `c > 0` with
`c · log ν(S₁ × S₂) = a log vol(S₁) + b log vol(S₂)` for all direct product regions if and only
if `a = b`. The regions used are `[0, 1/4] × [0, 1]`, `[1/2, 3/4] × [0, 1]` and their union
(itself a direct product region), and the same with the factors exchanged. This concerns
measures on the product space itself; the `𝓔`-weighted measure of (iv) lives on `M_W`, and its
logarithm, scaled by `1/N_𝓔`, does give the weighted sum (`wPkt_EMeasure_log`).

## Interpretation choices

1. The places of `𝕍` over `v_ℚ` and of `𝕍_mod` over `v_ℚ` are identified (the natural bijection
   of page 94); `V` stands for both.
2. The log-volume on a summand that the weights multiply is the unnormalized one (natural
   logarithm of a Haar measure, zero on the integral elements). Under this reading the page's
   normalization sentence holds for all degrees (`wPkt_weight_dim_sum`); under the other reading
   (log-volumes divided by the dimension of the summand) it fails in general, though it holds
   when `Σ_t w_t = 1` (`wPkt_doubleDivision_zpow_smul`). The pages do not decide between the two.
3. The summands are the packets `⊗_α K_{v_α}` over `ℚ_p`, not their decompositions into fields;
   the log-volume of a packet is additive over its fields (`packet_muLog_pi_region`), so nothing
   changes on regions that are products over the fields as well.
4. Page 115 writes `p_v` (with `v` underlined) where page 94 writes `p_{v_ℚ}`; both are the
   residue characteristic `p`.

## Not proved

* The decomposition `⊗_α (Π_v K_v) ≅ Π_t ⊗_α K_{v_α}` (Proposition 3.1 (i) for finite levels):
  it is an input `G` of the comparison theorems.
* The inductive limits of Proposition 3.1 (the algebraic closures `k̄`, `𝒪_{k̄}`): only finite
  levels `K_v` are treated.
* Weighted log-volumes of regions that are not direct product regions, other than through the
  `𝓔`-weighted measure; that `μ_𝓔` restricted to direct product regions is the page's choice of
  extension, and the "suitable normalization factor" of page 96 between `(1/N_𝓔) μ^log_𝓔` and the
  normalized weights (it is the constant `1 / Σ_{{w_α}} Π_α [(F_mod)_{w_α} : ℚ_{v_ℚ}]`, which
  the pages do not display).
* Archimedean places: the weights are the same formula (page 94, with `v_ℚ ∈ 𝕍_ℚ^arc`), and the
  arithmetic of `wPktWeight` applies to any positive degrees; the radial log-volume, the
  normalization by `e` of page 116 and the archimedean summands are not formalized.
* Proposition 3.9 (ii) on mono-analytic log-shells, (iii) and (iv); the sizes of the capsules of
  a procession (Proposition 3.4, not read for this file): the label sets `L j` are inputs.
* Nothing here computes either side of Corollary 3.12: all regions are inputs.
-/

namespace IUT.PaperIII.Corollary312

open MeasureTheory IUT.Prerequisites.PadicVolume IUT.PaperIV.LocalFields
open scoped Pointwise

/-! ## The weights of Remark 3.1.1 (ii) -/

section Weights

variable {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]

/-- The sum `Σ_{w : A → V} Π_{α ∈ A} f(w_α)` in the denominator of the normalized weight of
page 94, over all collections `{w_α}_{α ∈ A}` of not necessarily distinct places over `v_ℚ`;
`f(w) = [(F_mod)_w : ℚ_{v_ℚ}]`. -/
def wPktDenom (f : V → ℕ) (A : Type) [Fintype A] [DecidableEq A] : ℕ :=
  ∑ w : A → V, ∏ α, f (w α)

/-- **The normalized weight of page 94** of the tuple `t = {v_α}_{α ∈ A}`:
`1 / ((Π_α [K_{v_α} : (F_mod)_{v_α}]) · Σ_{{w_α}} Π_α [(F_mod)_{w_α} : ℚ_{v_ℚ}])`, with
`e(v) = [K_v : (F_mod)_v]` and `f(v) = [(F_mod)_v : ℚ_{v_ℚ}]`. -/
noncomputable def wPktWeight (e f : V → ℕ) (t : A → V) : ℝ :=
  1 / ((∏ α, (e (t α) : ℝ)) * (wPktDenom f A : ℝ))

/-- The dimension over `ℚ_{v_ℚ}` of the summand `⊗_α K_{v_α}` of the tuple `t`:
`Π_α [K_{v_α} : (F_mod)_{v_α}] · [(F_mod)_{v_α} : ℚ_{v_ℚ}]`. -/
def wPktDim (e f : V → ℕ) (t : A → V) : ℕ :=
  ∏ α, e (t α) * f (t α)

/-- The denominator is a power: `Σ_{w : A → V} Π_α f(w_α) = (Σ_v f(v)) ^ |A|`. -/
theorem wPktDenom_eq_pow (f : V → ℕ) : wPktDenom f A = (∑ v, f v) ^ Fintype.card A := by
  calc wPktDenom f A = ∏ _α : A, ∑ v, f v :=
        (Fintype.prod_sum (fun (_ : A) (v : V) => f v)).symm
    _ = _ := by rw [Finset.prod_const, Finset.card_univ]

theorem wPktDenom_pos [Nonempty V] {f : V → ℕ} (hf : ∀ v, 0 < f v) : 0 < wPktDenom f A := by
  rw [wPktDenom_eq_pow]
  exact pow_pos (Finset.sum_pos (fun v _ => hf v) Finset.univ_nonempty) _

/-- **The weights times the dimensions sum to one**: `Σ_t w_t · dim_t = 1`. This is the
normalization that makes multiplication by `p` subtract exactly `log p` from the weighted sum of
unnormalized log-volumes (`wPkt_logVol_zpow_smul`). -/
theorem wPkt_weight_dim_sum [Nonempty V] {e f : V → ℕ} (he : ∀ v, 0 < e v)
    (hf : ∀ v, 0 < f v) :
    ∑ t : A → V, wPktWeight e f t * (wPktDim e f t : ℝ) = 1 := by
  have hD : (wPktDenom f A : ℝ) ≠ 0 := by exact_mod_cast (wPktDenom_pos (A := A) hf).ne'
  have hE : ∀ t : A → V, (∏ α, (e (t α) : ℝ)) ≠ 0 := fun t =>
    Finset.prod_ne_zero_iff.mpr fun α _ => by exact_mod_cast (he (t α)).ne'
  calc ∑ t : A → V, wPktWeight e f t * (wPktDim e f t : ℝ)
      = ∑ t : A → V, (∏ α, (f (t α) : ℝ)) / (wPktDenom f A : ℝ) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [wPktWeight, wPktDim]
        push_cast
        rw [Finset.prod_mul_distrib]
        field_simp [hE t]
    _ = 1 := by
        rw [← Finset.sum_div, div_eq_one_iff_eq hD, wPktDenom]
        push_cast
        rfl

/-- **The weights alone do not sum to one**: `Σ_t w_t = (Σ_v 1/e(v)) ^ |A| / (Σ_v f(v)) ^ |A|`.
A weighted sum of log-volumes that are already divided by the dimension (the normalization of
`padicPacketMuLog`) shifts under multiplication by `p` by `−(Σ_t w_t) log p`
(`wPkt_doubleDivision_zpow_smul`), which differs from `−log p` in general
(`wPkt_weight_sum_example`). -/
theorem wPkt_weight_sum (e f : V → ℕ) :
    ∑ t : A → V, wPktWeight e f t =
      (∑ v, (e v : ℝ)⁻¹) ^ Fintype.card A / ((∑ v, f v : ℕ) : ℝ) ^ Fintype.card A := by
  have h1 : ∀ t : A → V, wPktWeight e f t =
      (∏ α, (e (t α) : ℝ)⁻¹) / ((∑ v, f v : ℕ) : ℝ) ^ Fintype.card A := by
    intro t
    rw [wPktWeight, wPktDenom_eq_pow, Finset.prod_inv_distrib]
    push_cast
    rw [one_div, mul_inv, div_eq_mul_inv]
  simp only [h1]
  rw [← Finset.sum_div]
  congr 1
  calc ∑ t : A → V, ∏ α, (e (t α) : ℝ)⁻¹ = ∏ _α : A, ∑ v, (e v : ℝ)⁻¹ :=
        (Fintype.prod_sum (fun (_ : A) (v : V) => (e v : ℝ)⁻¹)).symm
    _ = _ := by rw [Finset.prod_const, Finset.card_univ]

/-- **The double-division test, numerically**: one place with `[K_v : (F_mod)_v] = 2`,
`[(F_mod)_v : ℚ_p] = 1`, and one label. The weights sum to `1/2`, not `1`. -/
theorem wPkt_weight_sum_example :
    ∑ t : Unit → Unit, wPktWeight (fun _ => 2) (fun _ => 1) t = 1 / 2 := by
  rw [wPkt_weight_sum]
  norm_num

end Weights

/-! ## Comparison with the Haar normalization on the whole packet -/

section HaarWeights

variable {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]

/-- The coefficient of the unnormalized log-volume of each summand in the log-volume of the
whole packet normalized by its dimension (`packet_muLog_pi_region`, `wPkt_haar_region`):
`1 / dim = 1 / (Σ_v [K_v : (F_mod)_v] · [(F_mod)_v : ℚ_p]) ^ |A|`, the same for every tuple. -/
noncomputable def wPktHaarCoeff (e f : V → ℕ) (A : Type) [Fintype A] : ℝ :=
  1 / ((∑ v, e v * f v : ℕ) : ℝ) ^ Fintype.card A

/-- The dimension of the whole packet: `Σ_t dim_t = (Σ_v e(v) f(v)) ^ |A|`. -/
theorem wPkt_dim_sum (e f : V → ℕ) :
    ∑ t : A → V, wPktDim e f t = (∑ v, e v * f v) ^ Fintype.card A := by
  calc ∑ t : A → V, wPktDim e f t = ∏ _α : A, ∑ v, e v * f v :=
        (Fintype.prod_sum (fun (_ : A) (v : V) => e v * f v)).symm
    _ = _ := by rw [Finset.prod_const, Finset.card_univ]

/-- The `f`-weighted mean `ē = (Σ_v e(v) f(v)) / (Σ_v f(v))` of the local degrees
`[K_v : (F_mod)_v]`. -/
noncomputable def wPktMeanDeg (e f : V → ℕ) : ℝ :=
  ((∑ v, e v * f v : ℕ) : ℝ) / ((∑ v, f v : ℕ) : ℝ)

/-- **The page's weight is the Haar coefficient times an explicit factor**:
`w_t = (1 / dim) · Π_α (ē / [K_{v_α} : (F_mod)_{v_α}])`. -/
theorem wPkt_weight_eq_haar_mul [Nonempty V] {e f : V → ℕ} (he : ∀ v, 0 < e v)
    (hf : ∀ v, 0 < f v) (t : A → V) :
    wPktWeight e f t = wPktHaarCoeff e f A * ∏ α, (wPktMeanDeg e f / (e (t α) : ℝ)) := by
  have hF : ((∑ v, f v : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.sum_pos (fun v _ => hf v) Finset.univ_nonempty).ne'
  have hEF : ((∑ v, e v * f v : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.sum_pos (fun v _ => Nat.mul_pos (he v) (hf v))
      Finset.univ_nonempty).ne'
  have hE : (∏ α, (e (t α) : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun α _ => by exact_mod_cast (he (t α)).ne'
  rw [wPktWeight, wPktHaarCoeff, wPktDenom_eq_pow, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, wPktMeanDeg, div_pow]
  push_cast at hF hEF ⊢
  field_simp

/-- **When the two normalizations agree**: for at least one label (nonempty `A` and `V`, positive
degrees), the page's weights equal the Haar coefficient `1 / dim` for every tuple if and only if
the local degree `[K_v : (F_mod)_v]` is the same at all places over `p`. This compares the two
weight systems in the reading of this module (choice 2 of the module docstring). -/
theorem wPkt_weight_eq_haar_iff [Nonempty V] [Nonempty A] {e f : V → ℕ} (he : ∀ v, 0 < e v)
    (hf : ∀ v, 0 < f v) :
    (∀ t : A → V, wPktWeight e f t = wPktHaarCoeff e f A) ↔ ∀ v v', e v = e v' := by
  have hH : wPktHaarCoeff e f A ≠ 0 := by
    rw [wPktHaarCoeff]
    have : ((∑ v, e v * f v : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.sum_pos (fun v _ => Nat.mul_pos (he v) (hf v))
        Finset.univ_nonempty).ne'
    exact one_div_ne_zero (pow_ne_zero _ this)
  have hmean : ∀ v, wPktMeanDeg e f / (e v : ℝ) = 1 ↔ (e v : ℝ) = wPktMeanDeg e f := by
    intro v
    have : (e v : ℝ) ≠ 0 := by exact_mod_cast (he v).ne'
    rw [div_eq_one_iff_eq this, eq_comm]
  constructor
  · intro h
    have hv : ∀ v, (e v : ℝ) = wPktMeanDeg e f := by
      intro v
      have h1 := h (fun _ => v)
      rw [wPkt_weight_eq_haar_mul he hf, Finset.prod_const, Finset.card_univ] at h1
      have h2 : (wPktMeanDeg e f / (e v : ℝ)) ^ Fintype.card A = 1 := by
        have := mul_left_cancel₀ hH (h1.trans (mul_one _).symm)
        exact this
      have hnn : 0 ≤ wPktMeanDeg e f / (e v : ℝ) := by
        unfold wPktMeanDeg; positivity
      rw [pow_eq_one_iff_of_nonneg hnn Fintype.card_ne_zero] at h2
      exact (hmean v).mp h2
    intro v v'
    exact_mod_cast (hv v).trans (hv v').symm
  · intro h t
    obtain ⟨v₀⟩ := ‹Nonempty V›
    have hc : wPktMeanDeg e f = (e v₀ : ℝ) := by
      have hF : ((∑ v, f v : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.sum_pos (fun v _ => hf v) Finset.univ_nonempty).ne'
      rw [wPktMeanDeg, div_eq_iff hF]
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by rw [h v v₀]
    rw [wPkt_weight_eq_haar_mul he hf]
    have : ∀ α, wPktMeanDeg e f / (e (t α) : ℝ) = 1 := fun α => by
      rw [hc, h (t α) v₀]
      exact div_self (by exact_mod_cast (he v₀).ne')
    simp [this]

end HaarWeights

/-! ## The weighted log-volume on real tensor packets -/

section RealPackets

variable (p : ℕ) [hp : Fact p.Prime] {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
  (F K : V → Type) [∀ v, Field (F v)] [∀ v, Field (K v)] [∀ v, Algebra ℚ_[p] (F v)]
  [∀ v, Algebra ℚ_[p] (K v)] [∀ v, Algebra (F v) (K v)] [∀ v, IsScalarTower ℚ_[p] (F v) (K v)]
  [∀ v, FiniteDimensional ℚ_[p] (F v)] [∀ v, FiniteDimensional (F v) (K v)]
  [∀ v, FiniteDimensional ℚ_[p] (K v)]

/-- `e(v) = [K_v : (F_mod)_v]`, the local degree of the field `K v` over the field `F v`. -/
noncomputable def wPktE (v : V) : ℕ := Module.finrank (F v) (K v)

/-- `f(v) = [(F_mod)_v : ℚ_p]`. -/
noncomputable def wPktF (v : V) : ℕ := Module.finrank ℚ_[p] (F v)

omit [Fintype V] [∀ v, FiniteDimensional ℚ_[p] (K v)] in
/-- The tower law `[K_v : ℚ_p] = [K_v : (F_mod)_v] · [(F_mod)_v : ℚ_p]`. -/
theorem wPkt_finrank_tower (v : V) :
    Module.finrank ℚ_[p] (K v) = wPktE F K v * wPktF p F v := by
  rw [wPktE, wPktF, mul_comm]
  exact (Module.finrank_mul_finrank ℚ_[p] (F v) (K v)).symm

omit [Fintype V] in
theorem wPktE_pos (v : V) : 0 < wPktE F K v := Module.finrank_pos

omit [Fintype V] in
theorem wPktF_pos (v : V) : 0 < wPktF p F v := Module.finrank_pos

/-- The summand `⊗_{α ∈ A} K_{v_α}` of the tuple `t = {v_α}` (tensor product over `ℚ_p`). -/
abbrev wPktSummand (t : A → V) : Type := PiTensorProduct ℚ_[p] (fun α => K (t α))

omit [Fintype V] [DecidableEq A] in
/-- `dim_{ℚ_p} ⊗_α K_{v_α} = Π_α [K_{v_α} : (F_mod)_{v_α}] [(F_mod)_{v_α} : ℚ_p]`. -/
theorem wPkt_summand_finrank (t : A → V) :
    Module.finrank ℚ_[p] (wPktSummand p K t) = wPktDim (wPktE F K) (wPktF p F) t := by
  rw [packet_finrank p (fun α => K (t α)), wPktDim]
  exact Finset.prod_congr rfl fun α _ => wPkt_finrank_tower p F K (t α)

variable [hM : ∀ t : A → V, MeasurableSpace
    (Fin (Module.finrank ℚ_[p] (wPktSummand p K t)) → ℚ_[p])]
  [hB : ∀ t : A → V, BorelSpace (Fin (Module.finrank ℚ_[p] (wPktSummand p K t)) → ℚ_[p])]
  (μ : ∀ t : A → V, Measure (Fin (Module.finrank ℚ_[p] (wPktSummand p K t)) → ℚ_[p]))
  [hμ : ∀ t, (μ t).IsAddHaarMeasure]

/-- The unnormalized log-volume `L_t` on the summand of the tuple `t`: the logarithm of a Haar
measure, normalized so that the integral elements `(R_E)^∼` have log-volume `0` (multiplication
by `p` subtracts `dim_t · log p`). It is `dim_t` times `padicPacketMuLog`, which divides by the
dimension. -/
noncomputable def wPktSummandLogVol (t : A → V) (X : Set (wPktSummand p K t)) : ℝ :=
  (Module.finrank ℚ_[p] (wPktSummand p K t) : ℝ) *
    padicPacketMuLog p (wPktSummand p K t) (μ t) (packetNormalizationSet p _) X

/-- **The packet-normalized log-volume of a direct product region `Π_t X_t`** (Remark 3.1.1 (ii),
(iii); Proposition 3.9 (i)): `Σ_t w_t · L_t(X_t)` with the normalized weights of page 94. -/
noncomputable def wPktLogVol (X : ∀ t : A → V, Set (wPktSummand p K t)) : ℝ :=
  ∑ t, wPktWeight (wPktE F K) (wPktF p F) t * wPktSummandLogVol p K μ t (X t)

omit [∀ v, IsScalarTower ℚ_[p] (F v) (K v)] [∀ v, FiniteDimensional ℚ_[p] (F v)]
  [∀ v, FiniteDimensional (F v) (K v)] hB hμ in
/-- **Test 1**: the integral structure `Π_t (R_E)^∼_t` has packet-normalized log-volume `0`. -/
theorem wPkt_logVol_integral :
    wPktLogVol p F K μ (fun t => packetNormalizationSet p (wPktSummand p K t)) = 0 := by
  simp [wPktLogVol, wPktSummandLogVol, padicPacketMuLog_self]

omit [Fintype V] [DecidableEq A] [∀ v, IsScalarTower ℚ_[p] (F v) (K v)]
  [∀ v, FiniteDimensional ℚ_[p] (F v)] [∀ v, FiniteDimensional (F v) (K v)] in
/-- The integral elements of a summand have positive finite Haar measure, and
`μ^log(p ^ n · (R_E)^∼) = −n log p` (IUT IV Proposition 1.4 (i), `Packets.lean`). -/
theorem wPkt_summand_integral (t : A → V) :
    μ t ((Module.finBasis ℚ_[p] (wPktSummand p K t)).equivFun ''
        packetNormalizationSet p (wPktSummand p K t)) ≠ 0 ∧
      μ t ((Module.finBasis ℚ_[p] (wPktSummand p K t)).equivFun ''
        packetNormalizationSet p (wPktSummand p K t)) ≠ ⊤ ∧
      ∀ n : ℤ, padicPacketMuLog p (wPktSummand p K t) (μ t)
        (packetNormalizationSet p (wPktSummand p K t))
        (((p : ℚ_[p]) ^ n) • packetNormalizationSet p (wPktSummand p K t)) =
          -(n * Real.log p) := by
  have := packet_formallyUnramified p (fun α => K (t α))
  have := packet_nontrivial p (fun α => K (t α))
  obtain ⟨h0, h1, -, h3⟩ := packet_muLog_normalization p (wPktSummand p K t) (μ t)
  exact ⟨h0, h1, h3⟩

omit [Fintype V] [DecidableEq A] in
/-- The scaling law of `L_t`. -/
theorem wPkt_summandLogVol_zpow_smul (t : A → V) {X : Set (wPktSummand p K t)}
    (hX0 : μ t ((Module.finBasis ℚ_[p] (wPktSummand p K t)).equivFun '' X) ≠ 0)
    (hX : μ t ((Module.finBasis ℚ_[p] (wPktSummand p K t)).equivFun '' X) ≠ ⊤) (n : ℤ) :
    wPktSummandLogVol p K μ t (((p : ℚ_[p]) ^ n) • X) =
      wPktSummandLogVol p K μ t X -
        n * Real.log p * (wPktDim (wPktE F K) (wPktF p F) t : ℝ) := by
  have := packet_nontrivial p (fun α => K (t α))
  obtain ⟨h0, h1, -⟩ := wPkt_summand_integral p K μ t
  have hD : 0 < Module.finrank ℚ_[p] (wPktSummand p K t) := Module.finrank_pos
  rw [wPktSummandLogVol, wPktSummandLogVol,
    padicPacketMuLog_p_zpow_smul p (μ t) hD h0 h1 hX0 hX n, wPkt_summand_finrank p F K]
  ring

/-- **Test 2**: multiplying every component of a direct product region (of positive finite
measures) by `p ^ n` subtracts exactly `n · log p` from the packet-normalized log-volume
(Proposition 3.9 (i), page 115, for `n = 1`). -/
theorem wPkt_logVol_zpow_smul [Nonempty V] (X : ∀ t : A → V, Set (wPktSummand p K t))
    (hX0 : ∀ t, μ t ((Module.finBasis ℚ_[p] (wPktSummand p K t)).equivFun '' X t) ≠ 0)
    (hX : ∀ t, μ t ((Module.finBasis ℚ_[p] (wPktSummand p K t)).equivFun '' X t) ≠ ⊤)
    (n : ℤ) :
    wPktLogVol p F K μ (fun t => ((p : ℚ_[p]) ^ n) • X t) =
      wPktLogVol p F K μ X - n * Real.log p := by
  have hsum := wPkt_weight_dim_sum (A := A) (wPktE_pos F K) (wPktF_pos p F)
  simp only [wPktLogVol, wPkt_summandLogVol_zpow_smul p F K μ _ (hX0 _) (hX _), mul_sub,
    Finset.sum_sub_distrib]
  congr 1
  calc ∑ t : A → V, wPktWeight (wPktE F K) (wPktF p F) t *
        (n * Real.log p * (wPktDim (wPktE F K) (wPktF p F) t : ℝ))
      = n * Real.log p * ∑ t : A → V, wPktWeight (wPktE F K) (wPktF p F) t *
          (wPktDim (wPktE F K) (wPktF p F) t : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring
    _ = n * Real.log p := by rw [hsum, mul_one]

/-- **Test 2 on the integral structure**: `Π_t p ^ n · (R_E)^∼_t` has packet-normalized
log-volume `−n log p`; for `n = 1` this is the normalization printed on page 115. -/
theorem wPkt_logVol_integral_zpow [Nonempty V] (n : ℤ) :
    wPktLogVol p F K μ (fun t => ((p : ℚ_[p]) ^ n) •
      packetNormalizationSet p (wPktSummand p K t)) = -(n * Real.log p) := by
  have h := wPkt_summand_integral p K μ
  rw [wPkt_logVol_zpow_smul p F K μ _ (fun t => (h t).1) (fun t => (h t).2.1) n,
    wPkt_logVol_integral]
  ring

omit [∀ v, IsScalarTower ℚ_[p] (F v) (K v)] [∀ v, FiniteDimensional ℚ_[p] (F v)]
  [∀ v, FiniteDimensional (F v) (K v)] in
/-- **The double-division test on real packets**: if the page's weights are applied to the
log-volumes `padicPacketMuLog` that are already divided by the dimension, multiplication by
`p ^ n` shifts the weighted sum by `−n (Σ_t w_t) log p`, and `Σ_t w_t ≠ 1` in general
(`wPkt_weight_sum`, `wPkt_weight_sum_example`). -/
theorem wPkt_doubleDivision_zpow_smul (X : ∀ t : A → V, Set (wPktSummand p K t))
    (hX0 : ∀ t, μ t ((Module.finBasis ℚ_[p] (wPktSummand p K t)).equivFun '' X t) ≠ 0)
    (hX : ∀ t, μ t ((Module.finBasis ℚ_[p] (wPktSummand p K t)).equivFun '' X t) ≠ ⊤)
    (n : ℤ) :
    ∑ t, wPktWeight (wPktE F K) (wPktF p F) t *
        padicPacketMuLog p (wPktSummand p K t) (μ t) (packetNormalizationSet p _)
          (((p : ℚ_[p]) ^ n) • X t) =
      ∑ t, wPktWeight (wPktE F K) (wPktF p F) t *
        padicPacketMuLog p (wPktSummand p K t) (μ t) (packetNormalizationSet p _) (X t) -
        n * Real.log p * ∑ t : A → V, wPktWeight (wPktE F K) (wPktF p F) t := by
  have h : ∀ t, padicPacketMuLog p (wPktSummand p K t) (μ t) (packetNormalizationSet p _)
      (((p : ℚ_[p]) ^ n) • X t) = padicPacketMuLog p (wPktSummand p K t) (μ t)
        (packetNormalizationSet p _) (X t) - n * Real.log p := by
    intro t
    have := packet_nontrivial p (fun α => K (t α))
    obtain ⟨h0, h1, -⟩ := wPkt_summand_integral p K μ t
    exact padicPacketMuLog_p_zpow_smul p (μ t) Module.finrank_pos h0 h1 (hX0 t) (hX t) n
  simp only [h, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun t _ => by ring

end RealPackets

/-! ## The Haar normalization on the whole packet -/

section WholePacket

universe u

variable (p : ℕ) [hp : Fact p.Prime] (W : Type u) [CommRing W] [Algebra ℚ_[p] W]
  [FiniteDimensional ℚ_[p] W] [MeasurableSpace (Fin (Module.finrank ℚ_[p] W) → ℚ_[p])]
  [BorelSpace (Fin (Module.finrank ℚ_[p] W) → ℚ_[p])]
  (ν : Measure (Fin (Module.finrank ℚ_[p] W) → ℚ_[p])) [ν.IsAddHaarMeasure]

/-- **Product regions in a decomposition into formally unramified summands**: for a
`ℚ_p`-algebra isomorphism `G : W ≃ Π_j B_j` onto a finite product of finite formally unramified
`ℚ_p`-algebras (not necessarily fields) and sets `S_j` of positive finite measure,
`μ^log_W(G⁻¹(Π_j S_j)) = Σ_j (dim B_j / dim W) · μ^log_j(S_j)`, each normalized at its integral
elements. This is `packet_muLog_pi_region` with summands that are packets instead of fields. -/
theorem wPkt_muLog_pi_region {J : Type*} [Fintype J] (B : J → Type*) [∀ j, CommRing (B j)]
    [∀ j, Algebra ℚ_[p] (B j)] [∀ j, FiniteDimensional ℚ_[p] (B j)]
    (hU : ∀ j, Algebra.FormallyUnramified ℚ_[p] (B j)) (hN : ∀ j, Nontrivial (B j))
    (G : W ≃ₐ[ℚ_[p]] Π j, B j)
    [∀ j, MeasurableSpace (Fin (Module.finrank ℚ_[p] (B j)) → ℚ_[p])]
    [∀ j, BorelSpace (Fin (Module.finrank ℚ_[p] (B j)) → ℚ_[p])]
    (μ : ∀ j, Measure (Fin (Module.finrank ℚ_[p] (B j)) → ℚ_[p]))
    [∀ j, (μ j).IsAddHaarMeasure] (S : ∀ j, Set (B j))
    (hS0 : ∀ j, μ j ((Module.finBasis ℚ_[p] (B j)).equivFun '' S j) ≠ 0)
    (hS : ∀ j, μ j ((Module.finBasis ℚ_[p] (B j)).equivFun '' S j) ≠ ⊤) :
    padicPacketMuLog p W ν (packetNormalizationSet p W) (G ⁻¹' Set.univ.pi S) =
      ∑ j, ((Module.finrank ℚ_[p] (B j) : ℝ) / Module.finrank ℚ_[p] W) *
        padicPacketMuLog p (B j) (μ j) (packetNormalizationSet p (B j)) (S j) := by
  set c := fun j => (Module.finBasis ℚ_[p] (B j)).equivFun
  let H : W ≃ₗ[ℚ_[p]] Π j, (Fin (Module.finrank ℚ_[p] (B j)) → ℚ_[p]) :=
    G.toLinearEquiv.trans (LinearEquiv.piCongrRight c)
  have hreg : ∀ T : ∀ j, Set (B j),
      H '' (G ⁻¹' Set.univ.pi T) = Set.univ.pi (fun j => c j '' T j) := by
    intro T
    ext t
    rw [LinearEquiv.image_eq_preimage_symm, Set.mem_preimage, Set.mem_preimage, Set.mem_univ_pi,
      Set.mem_univ_pi]
    refine forall_congr' fun j => ?_
    rw [LinearEquiv.image_eq_preimage_symm, Set.mem_preimage]
    simp [H]
  rw [packet_muLog_transport p W ν (Measure.pi μ) H, packet_normalization_eq_preimage p W B G,
    hreg, hreg]
  have hW : Module.finrank ℚ_[p] W =
      Module.finrank ℚ_[p] (Π j, (Fin (Module.finrank ℚ_[p] (B j)) → ℚ_[p])) := H.finrank_eq
  have hNorm : ∀ j, μ j ((Module.finBasis ℚ_[p] (B j)).equivFun ''
      packetNormalizationSet p (B j)) ≠ 0 ∧ μ j ((Module.finBasis ℚ_[p] (B j)).equivFun ''
      packetNormalizationSet p (B j)) ≠ ⊤ := fun j => by
    have := hU j
    have := hN j
    obtain ⟨h0, h1, -⟩ := packet_muLog_normalization p (B j) (μ j)
    exact ⟨h0, h1⟩
  unfold padicPacketMuLog padicMuLog
  rw [Measure.pi_pi, Measure.pi_pi, ENNReal.toReal_prod, ENNReal.toReal_prod,
    ← Finset.prod_div_distrib, Real.log_prod, Finset.sum_div, hW]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hd : (Module.finrank ℚ_[p] (Fin (Module.finrank ℚ_[p] (B j)) → ℚ_[p]) : ℝ) ≠ 0 := by
      have := hN j
      rw [Module.finrank_fin_fun]
      exact_mod_cast (Module.finrank_pos (R := ℚ_[p]) (M := B j)).ne'
    rw [Module.finrank_fin_fun] at hd ⊢
    field_simp
    rfl
  · intro j _
    have h1 := ENNReal.toReal_pos (hS0 j) (hS j)
    have h2 := ENNReal.toReal_pos (hNorm j).1 (hNorm j).2
    positivity

variable {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
  (F K : V → Type) [∀ v, Field (F v)] [∀ v, Field (K v)] [∀ v, Algebra ℚ_[p] (F v)]
  [∀ v, Algebra ℚ_[p] (K v)] [∀ v, Algebra (F v) (K v)] [∀ v, IsScalarTower ℚ_[p] (F v) (K v)]
  [∀ v, FiniteDimensional ℚ_[p] (F v)] [∀ v, FiniteDimensional (F v) (K v)]
  [∀ v, FiniteDimensional ℚ_[p] (K v)]
  [∀ t : A → V, MeasurableSpace (Fin (Module.finrank ℚ_[p] (wPktSummand p K t)) → ℚ_[p])]
  [∀ t : A → V, BorelSpace (Fin (Module.finrank ℚ_[p] (wPktSummand p K t)) → ℚ_[p])]
  (μ : ∀ t : A → V, Measure (Fin (Module.finrank ℚ_[p] (wPktSummand p K t)) → ℚ_[p]))
  [∀ t, (μ t).IsAddHaarMeasure]

/-- **The Haar normalization on the whole packet in terms of the summands**: for a
`ℚ_p`-algebra isomorphism `G` from `W` (the whole packet) onto `Π_t ⊗_α K_{v_α}` (the
decomposition of Proposition 3.1 (i), taken here as an input) and a direct product region
`Π_t X_t`, the log-volume of `W` normalized by its dimension is
`Σ_t (1 / dim W) · L_t(X_t)`, with `dim W = (Σ_v [K_v : ℚ_p]) ^ |A|`. -/
theorem wPkt_haar_region (G : W ≃ₐ[ℚ_[p]] Π t : A → V, wPktSummand p K t)
    (X : ∀ t : A → V, Set (wPktSummand p K t))
    (hX0 : ∀ t, μ t ((Module.finBasis ℚ_[p] (wPktSummand p K t)).equivFun '' X t) ≠ 0)
    (hX : ∀ t, μ t ((Module.finBasis ℚ_[p] (wPktSummand p K t)).equivFun '' X t) ≠ ⊤) :
    padicPacketMuLog p W ν (packetNormalizationSet p W) (G ⁻¹' Set.univ.pi X) =
      ∑ t, wPktHaarCoeff (wPktE F K) (wPktF p F) A * wPktSummandLogVol p K μ t (X t) := by
  rw [wPkt_muLog_pi_region p W ν (fun t => wPktSummand p K t)
    (fun t => packet_formallyUnramified p (fun α => K (t α)))
    (fun t => packet_nontrivial p (fun α => K (t α))) G μ X hX0 hX]
  have hdim : (Module.finrank ℚ_[p] W : ℝ) =
      ((∑ v, wPktE F K v * wPktF p F v : ℕ) : ℝ) ^ Fintype.card A := by
    rw [G.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
    have := wPkt_dim_sum (A := A) (wPktE F K) (wPktF p F)
    simp only [wPkt_summand_finrank p F K]
    rw [this]
    push_cast
    rfl
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [wPktSummandLogVol, wPktHaarCoeff, ← hdim]
  ring

/-- **The page's weighted sum against the Haar normalization**: on a direct product region the
difference is `Σ_t (w_t − 1/dim W) · L_t(X_t)`; when `[K_v : (F_mod)_v]` is the same at all
places the two coincide (`wPkt_weight_eq_haar_iff`). Both sides are taken in the reading of this
module (choice 2 of the module docstring). -/
theorem wPkt_logVol_sub_haar (G : W ≃ₐ[ℚ_[p]] Π t : A → V, wPktSummand p K t)
    (X : ∀ t : A → V, Set (wPktSummand p K t))
    (hX0 : ∀ t, μ t ((Module.finBasis ℚ_[p] (wPktSummand p K t)).equivFun '' X t) ≠ 0)
    (hX : ∀ t, μ t ((Module.finBasis ℚ_[p] (wPktSummand p K t)).equivFun '' X t) ≠ ⊤) :
    wPktLogVol p F K μ X - padicPacketMuLog p W ν (packetNormalizationSet p W)
        (G ⁻¹' Set.univ.pi X) =
      ∑ t, (wPktWeight (wPktE F K) (wPktF p F) t - wPktHaarCoeff (wPktE F K) (wPktF p F) A) *
        wPktSummandLogVol p K μ t (X t) := by
  rw [wPkt_haar_region p W ν F K μ G X hX0 hX, wPktLogVol, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- **Equal local degrees**: if `[K_v : (F_mod)_v]` does not depend on `v`, the
packet-normalized log-volume `wPktLogVol` of a direct product region (the page's weights, in the
reading of this module) equals the log-volume of the whole packet normalized by its dimension. -/
theorem wPkt_logVol_eq_haar_of_const [Nonempty V] (hc : ∀ v v', wPktE F K v = wPktE F K v')
    (G : W ≃ₐ[ℚ_[p]] Π t : A → V, wPktSummand p K t)
    (X : ∀ t : A → V, Set (wPktSummand p K t))
    (hX0 : ∀ t, μ t ((Module.finBasis ℚ_[p] (wPktSummand p K t)).equivFun '' X t) ≠ 0)
    (hX : ∀ t, μ t ((Module.finBasis ℚ_[p] (wPktSummand p K t)).equivFun '' X t) ≠ ⊤) :
    wPktLogVol p F K μ X =
      padicPacketMuLog p W ν (packetNormalizationSet p W) (G ⁻¹' Set.univ.pi X) := by
  rw [← sub_eq_zero, wPkt_logVol_sub_haar p W ν F K μ G X hX0 hX]
  refine Finset.sum_eq_zero fun t _ => ?_
  cases isEmpty_or_nonempty A with
  | inl hA =>
    have h1 : wPktWeight (wPktE F K) (wPktF p F) t =
        wPktHaarCoeff (wPktE F K) (wPktF p F) A := by
      simp [wPktWeight, wPktHaarCoeff, wPktDenom]
    rw [h1, sub_self, zero_mul]
  | inr hA =>
    rw [(wPkt_weight_eq_haar_iff (A := A) (wPktE_pos F K) (wPktF_pos p F)).mpr hc t, sub_self,
      zero_mul]

/-- **The regions `Π_t p ^ {k_t} · (R_E)^∼_t`**: the page's normalization gives
`−log p · Σ_t w_t k_t dim_t` and the Haar normalization `−log p · Σ_t k_t dim_t / dim W`.
Both satisfy the two tests (`k` constant); they differ in general (`wPkt_coeff_example`). -/
theorem wPkt_scaled_integral (k : (A → V) → ℤ) (G : W ≃ₐ[ℚ_[p]] Π t : A → V, wPktSummand p K t) :
    wPktLogVol p F K μ (fun t => ((p : ℚ_[p]) ^ k t) •
        packetNormalizationSet p (wPktSummand p K t)) =
      -(Real.log p * ∑ t, wPktWeight (wPktE F K) (wPktF p F) t * k t *
        (wPktDim (wPktE F K) (wPktF p F) t : ℝ)) ∧
    padicPacketMuLog p W ν (packetNormalizationSet p W) (G ⁻¹' Set.univ.pi (fun t =>
        ((p : ℚ_[p]) ^ k t) • packetNormalizationSet p (wPktSummand p K t))) =
      -(Real.log p * ∑ t, wPktHaarCoeff (wPktE F K) (wPktF p F) A * k t *
        (wPktDim (wPktE F K) (wPktF p F) t : ℝ)) := by
  have hN := wPkt_summand_integral p K μ
  have hL : ∀ t, wPktSummandLogVol p K μ t (((p : ℚ_[p]) ^ k t) •
      packetNormalizationSet p (wPktSummand p K t)) =
      -(Real.log p * k t * (wPktDim (wPktE F K) (wPktF p F) t : ℝ)) := by
    intro t
    rw [wPktSummandLogVol, (hN t).2.2 (k t), wPkt_summand_finrank p F K]
    ring
  have hP : ∀ t, μ t ((Module.finBasis ℚ_[p] (wPktSummand p K t)).equivFun ''
      (((p : ℚ_[p]) ^ k t) • packetNormalizationSet p (wPktSummand p K t))) ≠ 0 ∧
      μ t ((Module.finBasis ℚ_[p] (wPktSummand p K t)).equivFun ''
      (((p : ℚ_[p]) ^ k t) • packetNormalizationSet p (wPktSummand p K t))) ≠ ⊤ := by
    intro t
    have hp0 : ((p : ℚ_[p]) ^ k t) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
    rw [padicVol_image_smul p, padicVol_measure_smul p (μ t) hp0]
    exact ⟨mul_ne_zero (ENNReal.coe_ne_zero.mpr (pow_ne_zero _ (nnNorm_ne_zero_iff.mpr hp0)))
      (hN t).1, ENNReal.mul_ne_top ENNReal.coe_ne_top (hN t).2.1⟩
  constructor
  · simp only [wPktLogVol, hL, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  · rw [wPkt_haar_region p W ν F K μ G _ (fun t => (hP t).1) (fun t => (hP t).2)]
    simp only [hL, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring

end WholePacket

/-- **The two normalizations differ, numerically**: two places over `p` with
`[K_v : (F_mod)_v] = 1, 2` and `[(F_mod)_v : ℚ_p] = 1, 1`, one label, and the region
`p · (R_E)^∼` on the first summand, `(R_E)^∼` on the second (`k = 1, 0`). The coefficient of
`−log p` is `1/2` for the page's weights and `1/3` for the Haar normalization
(`wPkt_scaled_integral`). -/
theorem wPkt_coeff_example :
    ∑ t : Unit → Bool, wPktWeight (fun b : Bool => if b then 2 else 1) (fun _ => 1) t *
        ((if t () then 0 else 1 : ℤ) : ℝ) *
        (wPktDim (fun b : Bool => if b then 2 else 1) (fun _ => 1) t : ℝ) = 1 / 2 ∧
    ∑ t : Unit → Bool, wPktHaarCoeff (fun b : Bool => if b then 2 else 1) (fun _ => 1) Unit *
        ((if t () then 0 else 1 : ℤ) : ℝ) *
        (wPktDim (fun b : Bool => if b then 2 else 1) (fun _ => 1) t : ℝ) = 1 / 3 := by
  have e : ∀ g : (Unit → Bool) → ℝ, ∑ t, g t = g (fun _ => true) + g (fun _ => false) := by
    intro g
    rw [← (Equiv.funUnique Unit Bool).symm.sum_comp, Fintype.sum_bool]
    rfl
  rw [e, e]
  simp [wPktWeight, wPktDenom, wPktDim, wPktHaarCoeff]

/-! ## Procession-normalization: the average over the capsules -/

section Procession

variable {J : Type*} [Fintype J]

/-- The average `(1/|J|) Σ_j v_j` over the capsules of a procession (Proposition 3.9 (i),
page 116: "which we normalize by taking the average, over the various capsules"). -/
noncomputable def wPktProcAvg (v : J → ℝ) : ℝ := (Fintype.card J : ℝ)⁻¹ * ∑ j, v j

theorem wPktProcAvg_const [Nonempty J] (c : ℝ) : wPktProcAvg (fun _ : J => c) = c := by
  have : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [wPktProcAvg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, inv_mul_cancel_left₀ this]

theorem wPktProcAvg_sub [Nonempty J] (v : J → ℝ) (c : ℝ) :
    wPktProcAvg (fun j => v j - c) = wPktProcAvg v - c := by
  have : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [wPktProcAvg, wPktProcAvg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_sub, inv_mul_cancel_left₀ this]

/-- **The abstract layer's average is this one**: on real values, `equalWeightAverage` of
`Comparison.lean` is the procession average. -/
theorem wPktProcAvg_eq_equalWeightAverage (v : J → ℝ) :
    ((wPktProcAvg v : ℝ) : EReal) = equalWeightAverage (fun j => (v j : EReal)) := by
  rw [wPktProcAvg, equalWeightAverage, EReal.coe_mul, EReal.coe_finsetSum]

/-- **The label average of `LabelAverage.lean` is this one** over `𝔽_l^⋇`. -/
theorem wPktProcAvg_eq_labelAverage {l : ℕ} (hl : Odd l) [Fintype (NonzeroLabel l)]
    (v : NonzeroLabel l → ℝ) :
    ((wPktProcAvg v : ℝ) : EReal) = labelAverage l (fun j => (v j : EReal)) := by
  rw [labelAverage_eq_average hl, wPktProcAvg_eq_equalWeightAverage]

variable (p : ℕ) [hp : Fact p.Prime] {V : Type} [Fintype V]
  (F K : V → Type) [∀ v, Field (F v)] [∀ v, Field (K v)] [∀ v, Algebra ℚ_[p] (F v)]
  [∀ v, Algebra ℚ_[p] (K v)] [∀ v, Algebra (F v) (K v)] [∀ v, IsScalarTower ℚ_[p] (F v) (K v)]
  [∀ v, FiniteDimensional ℚ_[p] (F v)] [∀ v, FiniteDimensional (F v) (K v)]
  [∀ v, FiniteDimensional ℚ_[p] (K v)]
  {L : J → Type} [∀ j, Fintype (L j)] [∀ j, DecidableEq (L j)]
  [∀ j (t : L j → V), MeasurableSpace (Fin (Module.finrank ℚ_[p] (wPktSummand p K t)) → ℚ_[p])]
  [∀ j (t : L j → V), BorelSpace (Fin (Module.finrank ℚ_[p] (wPktSummand p K t)) → ℚ_[p])]
  (μ : ∀ j (t : L j → V), Measure (Fin (Module.finrank ℚ_[p] (wPktSummand p K t)) → ℚ_[p]))
  [∀ j t, (μ j t).IsAddHaarMeasure]

/-- **The procession-normalized log-volume** (Proposition 3.9 (i), (ii), page 116): the average
over the capsules `j ∈ J` of the packet-normalized log-volumes, the capsule `j` having label set
`L j`. -/
noncomputable def wPktProcLogVol (X : ∀ j (t : L j → V), Set (wPktSummand p K t)) : ℝ :=
  wPktProcAvg (fun j => wPktLogVol p F K (μ j) (X j))

omit [∀ v, IsScalarTower ℚ_[p] (F v) (K v)] [∀ v, FiniteDimensional ℚ_[p] (F v)]
  [∀ v, FiniteDimensional (F v) (K v)]
  [∀ j (t : L j → V), BorelSpace (Fin (Module.finrank ℚ_[p] (wPktSummand p K t)) → ℚ_[p])]
  [∀ j t, (μ j t).IsAddHaarMeasure] in
/-- **Test 1 for the procession**: the integral structures have procession-normalized
log-volume `0`. -/
theorem wPkt_procLogVol_integral :
    wPktProcLogVol p F K μ (fun _ t => packetNormalizationSet p (wPktSummand p K t)) = 0 := by
  simp only [wPktProcLogVol, wPkt_logVol_integral, wPktProcAvg, Finset.sum_const_zero,
    mul_zero]

/-- **Test 2 for the procession**: multiplying every component of every capsule's region by
`p ^ n` subtracts exactly `n · log p`. -/
theorem wPkt_procLogVol_zpow_smul [Nonempty J] [Nonempty V]
    (X : ∀ j (t : L j → V), Set (wPktSummand p K t))
    (hX0 : ∀ j t, μ j t ((Module.finBasis ℚ_[p] (wPktSummand p K t)).equivFun '' X j t) ≠ 0)
    (hX : ∀ j t, μ j t ((Module.finBasis ℚ_[p] (wPktSummand p K t)).equivFun '' X j t) ≠ ⊤)
    (n : ℤ) :
    wPktProcLogVol p F K μ (fun j t => ((p : ℚ_[p]) ^ n) • X j t) =
      wPktProcLogVol p F K μ X - n * Real.log p := by
  rw [wPktProcLogVol, wPktProcLogVol, ← wPktProcAvg_sub]
  congr 1
  funext j
  exact wPkt_logVol_zpow_smul p F K (μ j) (X j) (hX0 j) (hX j) n

end Procession

/-! ## Remark 3.1.1 (iv): the `𝓔`-weighted measure on direct product regions -/

section EWeighted

variable {V : Type} [Fintype V] [DecidableEq V] (E : V → Type) [∀ v, Fintype (E v)]

/-- `E_{≠v} = Π_{v' ≠ v} E_{v'}`. -/
abbrev wPktENe (v : V) : Type := ∀ v' : {v' : V // v' ≠ v}, E v'

/-- `W = ⨿_{v ∈ V} E_{≠v} × {v}`, as a sigma type over `V`. -/
abbrev wPktWIdx : Type := Σ v : V, wPktENe E v

variable {M : V → Type} [∀ v, MeasurableSpace (M v)] (μ : ∀ v, Measure (M v))
  [∀ v, SigmaFinite (μ v)]

/-- **The `𝓔`-weighted measure of page 97**: `μ_𝓔(S)` is the product measure on
`M_W = Π_{w ∈ W} M_{π(w)}` of the set of `m` such that, for every `e ∈ E`, the point
`(m_{(e_{≠v}, v)})_{v ∈ V}` lies in `S`. Under the homeomorphism `M_{E*V} ≅ M_W` of page 96 this
set is `S_E = {Π_{e ∈ E} S} ∩ M_{E*V}`. -/
noncomputable def wPktEMeasure (S : Set (∀ v, M v)) : ENNReal :=
  Measure.pi (fun w : wPktWIdx E => μ w.1)
    {m | ∀ e : ∀ v, E v, (fun v => m ⟨v, fun v' => e v'⟩) ∈ S}

omit [Fintype V] [∀ v, Fintype (E v)] [∀ v, MeasurableSpace (M v)] [∀ v, SigmaFinite (μ v)] in
/-- For a direct product `S = Π_v S_v` and nonempty `E_v`, the set defining `μ_𝓔(S)` is the
product `Π_{w ∈ W} S_{π(w)}`. -/
theorem wPkt_ESet_pi (hE : ∀ v, Nonempty (E v)) (S : ∀ v, Set (M v)) :
    {m : ∀ w : wPktWIdx E, M w.1 |
        ∀ e : ∀ v, E v, (fun v => m ⟨v, fun v' => e v'⟩) ∈ Set.univ.pi S} =
      Set.univ.pi (fun w : wPktWIdx E => S w.1) := by
  ext m
  simp only [Set.mem_ofPred_eq, Set.mem_univ_pi]
  constructor
  · rintro h ⟨v, x⟩
    let e : ∀ v', E v' := fun v' =>
      if hv : v' = v then Classical.choice (hE v') else x ⟨v', hv⟩
    have hx : (fun v' : {v' : V // v' ≠ v} => e v') = x := by
      funext v'
      simp [e, v'.2]
    have := h e v
    rwa [hx] at this
  · intro h e v
    exact h ⟨v, _⟩

/-- **The display of page 97**: for a direct product region `S = Π_v S_v` with
`0 < μ_v(S_v) < ∞` and nonempty `E_v` of cardinality `N_v`,
`(1/N_𝓔) · log μ_𝓔(S) = Σ_v (1/N_v) · log μ_v(S_v)`, where `N_𝓔 = Π_v N_v`. -/
theorem wPkt_EMeasure_log (hE : ∀ v, Nonempty (E v)) (S : ∀ v, Set (M v))
    (hS0 : ∀ v, μ v (S v) ≠ 0) (hS : ∀ v, μ v (S v) ≠ ⊤) :
    (1 / (∏ v, (Fintype.card (E v) : ℝ))) *
        Real.log (wPktEMeasure E μ (Set.univ.pi S)).toReal =
      ∑ v, (1 / (Fintype.card (E v) : ℝ)) * Real.log (μ v (S v)).toReal := by
  have hN : ∀ v, (Fintype.card (E v) : ℝ) ≠ 0 := fun v => by
    have := hE v
    exact_mod_cast Fintype.card_ne_zero
  have hpos : ∀ v, 0 < (μ v (S v)).toReal := fun v => ENNReal.toReal_pos (hS0 v) (hS v)
  have key : (∏ w : wPktWIdx E, μ w.1 (S w.1)) =
      ∏ v, μ v (S v) ^ Fintype.card (wPktENe E v) := by
    rw [Fintype.prod_sigma]
    exact Finset.prod_congr rfl fun v _ =>
      (Finset.prod_const (s := (Finset.univ : Finset (wPktENe E v))) (μ v (S v))).trans
        (by rw [Finset.card_univ])
  rw [wPktEMeasure, wPkt_ESet_pi E hE S, Measure.pi_pi, key, ENNReal.toReal_prod]
  simp only [ENNReal.toReal_pow]
  rw [Real.log_prod (fun v _ => pow_ne_zero _ (hpos v).ne'), Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Real.log_pow, Fintype.card_pi, Fintype.prod_eq_mul_prod_subtype_ne _ v]
  push_cast
  field_simp [hN v]

end EWeighted

/-! ## The warning of page 95: weighted sums and logarithms of measures (a model) -/

section Warning

open Set

/-- An elementary step: if `x_U = x_P + x_Q` and `c log x_P = c log x_Q = a log(1/4)`,
`c log x_U = a log(1/2)` with `a > 0`, then `a = c`. -/
theorem wPkt_split_forces (a c xP xQ xU : ℝ) (ha : 0 < a) (hxP : 0 ≤ xP) (hxQ : 0 ≤ xQ)
    (hU : xU = xP + xQ) (h1 : c * Real.log xP = a * Real.log (1 / 4))
    (h2 : c * Real.log xQ = a * Real.log (1 / 4)) (h3 : c * Real.log xU = a * Real.log (1 / 2)) :
    a = c := by
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have l4 : Real.log (1 / 4) = -2 * Real.log 2 := by
    rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have l12 : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
  rw [l4] at h1 h2
  rw [l12] at h3
  have hc : c ≠ 0 := by
    rintro rfl
    nlinarith
  have hP0 : xP ≠ 0 := by
    rintro rfl
    rw [Real.log_zero, mul_zero] at h1
    nlinarith [mul_pos ha l2]
  have hQ0 : xQ ≠ 0 := by
    rintro rfl
    rw [Real.log_zero, mul_zero] at h2
    nlinarith [mul_pos ha l2]
  have hPQ : Real.log xP = Real.log xQ := mul_left_cancel₀ hc (h1.trans h2.symm)
  have hxPQ : xP = xQ := Real.log_injOn_pos (lt_of_le_of_ne hxP (Ne.symm hP0))
    (lt_of_le_of_ne hxQ (Ne.symm hQ0)) hPQ
  have hlogU : Real.log xU = Real.log 2 + Real.log xP := by
    rw [hU, ← hxPQ, ← two_mul, Real.log_mul (by norm_num) hP0]
  rw [hlogU, mul_add] at h3
  nlinarith

/-- The three intervals of the model: `P = [0, 1/4]`, `Q = [1/2, 3/4]`, `I = [0, 1]`. -/
theorem wPkt_model_facts :
    IsCompact (Icc (0 : ℝ) (1 / 4)) ∧ IsCompact (Icc (1 / 2 : ℝ) (3 / 4)) ∧
      IsCompact (Icc (0 : ℝ) (1 / 4) ∪ Icc (1 / 2) (3 / 4)) ∧ IsCompact (Icc (0 : ℝ) 1) ∧
      (volume (Icc (0 : ℝ) (1 / 4))).toReal = 1 / 4 ∧
      (volume (Icc (1 / 2 : ℝ) (3 / 4))).toReal = 1 / 4 ∧
      (volume (Icc (0 : ℝ) (1 / 4) ∪ Icc (1 / 2) (3 / 4))).toReal = 1 / 2 ∧
      (volume (Icc (0 : ℝ) 1)).toReal = 1 ∧
      Disjoint (Icc (0 : ℝ) (1 / 4)) (Icc (1 / 2) (3 / 4)) := by
  have hd : Disjoint (Icc (0 : ℝ) (1 / 4)) (Icc (1 / 2) (3 / 4)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    linarith [hx.2, hx'.1]
  refine ⟨isCompact_Icc, isCompact_Icc, isCompact_Icc.union isCompact_Icc, isCompact_Icc,
    by simp [Real.volume_Icc], by norm_num [Real.volume_Icc], ?_, by simp [Real.volume_Icc], hd⟩
  rw [measure_union hd measurableSet_Icc, Real.volume_Icc, Real.volume_Icc,
    ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
  norm_num

/-- **The warning of page 95, in a model**: on `M_1 × M_2 = ℝ × ℝ` with Lebesgue measure on each
factor, let `a, b > 0` be weights. If some measure `ν` on `ℝ × ℝ` and some real `c` satisfy
`c · log ν(S₁ × S₂) = a · log vol(S₁) + b · log vol(S₂)` for all direct product regions
(compact `S₁`, `S₂` of positive measure), then `a = c = b`. So for unequal weights the weighted
sum of log-volumes is not a multiple of the logarithm of any measure on the product. -/
theorem wPkt_warning_forces_equal {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (ν : Measure (ℝ × ℝ))
    (h : ∀ S₁ S₂ : Set ℝ, IsCompact S₁ → IsCompact S₂ → volume S₁ ≠ 0 → volume S₂ ≠ 0 →
      c * Real.log (ν (S₁ ×ˢ S₂)).toReal =
        a * Real.log (volume S₁).toReal + b * Real.log (volume S₂).toReal) :
    a = c ∧ b = c := by
  obtain ⟨cP, cQ, cU, cI, vP, vQ, vU, vI, hd⟩ := wPkt_model_facts
  have ne0 : ∀ {S : Set ℝ}, (volume S).toReal ≠ 0 → volume S ≠ 0 := fun hS h0 => by
    simp [h0] at hS
  have nP := ne0 (by rw [vP]; norm_num)
  have nQ := ne0 (by rw [vQ]; norm_num)
  have nU := ne0 (by rw [vU]; norm_num)
  have nI := ne0 (by rw [vI]; norm_num)
  have fin : ∀ {T : Set (ℝ × ℝ)} {r : ℝ}, r ≠ 0 → c * Real.log (ν T).toReal = r → ν T ≠ ⊤ :=
    fun hr hT htop => hr (by rw [← hT, htop]; simp)
  have ql : Real.log (1 / 4 : ℝ) ≠ 0 := by
    rw [Real.log_ne_zero]; norm_num
  have hl : Real.log (1 / 2 : ℝ) ≠ 0 := by
    rw [Real.log_ne_zero]; norm_num
  constructor
  · have h1 := h _ _ cP cI nP nI
    have h2 := h _ _ cQ cI nQ nI
    have h3 := h _ _ cU cI nU nI
    rw [vP, vI, Real.log_one, mul_zero, add_zero] at h1
    rw [vQ, vI, Real.log_one, mul_zero, add_zero] at h2
    rw [vU, vI, Real.log_one, mul_zero, add_zero] at h3
    have f1 := fin (mul_ne_zero ha.ne' ql) h1
    have f2 := fin (mul_ne_zero ha.ne' ql) h2
    have hU : (ν ((Icc (0 : ℝ) (1 / 4) ∪ Icc (1 / 2) (3 / 4)) ×ˢ Icc 0 1)).toReal =
        (ν (Icc (0 : ℝ) (1 / 4) ×ˢ Icc 0 1)).toReal +
          (ν (Icc (1 / 2 : ℝ) (3 / 4) ×ˢ Icc 0 1)).toReal := by
      rw [Set.union_prod, measure_union (hd.set_prod_left _ _)
        (measurableSet_Icc.prod measurableSet_Icc), ENNReal.toReal_add f1 f2]
    exact wPkt_split_forces a c _ _ _ ha ENNReal.toReal_nonneg ENNReal.toReal_nonneg hU h1 h2 h3
  · have h1 := h _ _ cI cP nI nP
    have h2 := h _ _ cI cQ nI nQ
    have h3 := h _ _ cI cU nI nU
    rw [vP, vI, Real.log_one, mul_zero, zero_add] at h1
    rw [vQ, vI, Real.log_one, mul_zero, zero_add] at h2
    rw [vU, vI, Real.log_one, mul_zero, zero_add] at h3
    have f1 := fin (mul_ne_zero hb.ne' ql) h1
    have f2 := fin (mul_ne_zero hb.ne' ql) h2
    have hU : (ν (Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) (1 / 4) ∪ Icc (1 / 2) (3 / 4)))).toReal =
        (ν (Icc (0 : ℝ) 1 ×ˢ Icc 0 (1 / 4))).toReal +
          (ν (Icc (0 : ℝ) 1 ×ˢ Icc (1 / 2) (3 / 4))).toReal := by
      rw [Set.prod_union, measure_union (hd.set_prod_right _ _)
        (measurableSet_Icc.prod measurableSet_Icc), ENNReal.toReal_add f1 f2]
    exact wPkt_split_forces b c _ _ _ hb ENNReal.toReal_nonneg ENNReal.toReal_nonneg hU h1 h2 h3

/-- **Equal weights do arise from a measure**: with `ν` the product Lebesgue measure and `c = a`,
`a · log ν(S₁ × S₂) = a · log vol(S₁) + a · log vol(S₂)` for all compact `S₁`, `S₂` of positive
measure. -/
theorem wPkt_equal_weights_measure (a : ℝ) (S₁ S₂ : Set ℝ) (h₁ : IsCompact S₁)
    (h₂ : IsCompact S₂) (h₁0 : volume S₁ ≠ 0) (h₂0 : volume S₂ ≠ 0) :
    a * Real.log (volume (S₁ ×ˢ S₂)).toReal =
      a * Real.log (volume S₁).toReal + a * Real.log (volume S₂).toReal := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, ENNReal.toReal_mul,
    Real.log_mul (ENNReal.toReal_pos h₁0 h₁.measure_lt_top.ne).ne'
      (ENNReal.toReal_pos h₂0 h₂.measure_lt_top.ne).ne', mul_add]

/-- **The model statement in both directions**: for positive weights `a`, `b`, a measure `ν` on
`ℝ × ℝ` and a constant `c > 0` with `c · log ν(S₁ × S₂) = a log vol(S₁) + b log vol(S₂)` on all
direct product regions exist if and only if `a = b`. -/
theorem wPkt_warning_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∃ (ν : Measure (ℝ × ℝ)) (c : ℝ), 0 < c ∧
      ∀ S₁ S₂ : Set ℝ, IsCompact S₁ → IsCompact S₂ → volume S₁ ≠ 0 → volume S₂ ≠ 0 →
        c * Real.log (ν (S₁ ×ˢ S₂)).toReal =
          a * Real.log (volume S₁).toReal + b * Real.log (volume S₂).toReal) ↔ a = b := by
  constructor
  · rintro ⟨ν, c, -, h⟩
    obtain ⟨h1, h2⟩ := wPkt_warning_forces_equal ha hb ν h
    rw [h1, h2]
  · rintro rfl
    exact ⟨volume, a, ha, fun S₁ S₂ h₁ h₂ h₁0 h₂0 =>
      wPkt_equal_weights_measure a S₁ S₂ h₁ h₂ h₁0 h₂0⟩

end Warning

end IUT.PaperIII.Corollary312
