import Mathlib

/-!
# IUT III, Remark 3.9.5 (ii): the order-theoretic characterization of the hull map

Source: Mochizuki, *Inter-universal Teichmüller Theory III*, Remark 3.9.5, (i), (ii), pages 126
to 128. Pages 126 to 145 (all of Remark 3.9.5) were read from the extracted text; page 127,
which carries the displays of (i) and (ii), was checked against a rendered image.

## What the paper says

Remark 3.9.5 (i) defines the holomorphic hull of a suitable subset `U` of a tensor packet
`ℐ^ℚ(−)` as the smallest subset of the form `λ · 𝒪` containing `U`. Remark 3.9.5 (ii) writes
`ℙ` for the set of direct product regions and `ℍ ⊆ ℙ` for the set of hulls, and asserts that
forming the hull is a map `φ : ℙ → ℍ` that "may be characterized uniquely" by

* (P1) `φ(H) = H` for every `H ∈ ℍ`;
* (P2) `P ⊆ φ(P)` for every `P ∈ ℙ`;
* (P3) `φ(P₁) ⊆ φ(P₂)` whenever `P₁ ⊆ P₂` in `ℙ`.

It then says that, since any intersection of elements of `ℍ` which is itself of finite
log-volume necessarily determines an element of `ℍ` (the qualifier "of finite log-volume"
applies to the intersection, not to the members intersected), it "follows formally" from
(P1), (P2), (P3) that `φ(P)` is the intersection of all `H ∈ ℍ` containing `P`.

## What this file is and is not

**This file is not a formalization of holomorphic hulls or of Remark 3.9.5.** Tensor packets,
log-shells and direct product regions are not formalized. It checks the order-theoretic part of
Remark 3.9.5 (ii) for arbitrary families `𝓗 ⊆ 𝓟` of subsets of an arbitrary type:

* `IsHullMap.eq_sInter`: (P1), (P2), (P3), together with `ℍ ⊆ ℙ` and `φ(ℙ) ⊆ ℍ` (the two
  other clauses of `IsHullMap`, both stated on page 127), force
  `φ(P) = ⋂ {H ∈ 𝓗 | P ⊆ H}`. The intersection hypothesis quoted by the paper is not needed
  for this formula.
* `IsHullMap.unique`: hence at most one map satisfies (P1), (P2), (P3); this is the paper's
  "characterized uniquely".
* `isHullMap_sInter`: if for each `P ∈ 𝓟` the intersection of the members of `𝓗` containing
  `P` lies in `𝓗`, then that intersection defines a map satisfying (P1), (P2), (P3). This is
  the role of the intersection hypothesis: it gives existence, not the formula.

The paper's closure claim (an intersection of hulls that has finite log-volume is a hull) is
replaced by the plain hypothesis `hcl` of `isHullMap_sInter`: for each `P ∈ 𝓟` the
intersection of the members of `𝓗` containing `P` lies in `𝓗`. That hypothesis is a
statement about the given families only; no log-volume occurs in this file, and the
finite-volume condition of the paper is not modeled.
-/

namespace IUT.PaperIII.Remark3_9_5

variable {X : Type*}

/-- A map `φ` on subsets of `X` satisfies the conditions of Remark 3.9.5 (ii) relative to the
families `𝓟` (playing the role of direct product regions) and `𝓗` (playing the role of hulls):
it sends `𝓟` into `𝓗`, and satisfies (P1), (P2), (P3). -/
structure IsHullMap (𝓟 𝓗 : Set (Set X)) (φ : Set X → Set X) : Prop where
  /-- `ℍ ⊆ ℙ`, as observed in Remark 3.9.5 (ii). -/
  hull_sub : 𝓗 ⊆ 𝓟
  /-- `φ` maps `ℙ` into `ℍ`. -/
  maps_to : ∀ P ∈ 𝓟, φ P ∈ 𝓗
  /-- (P1) `φ(H) = H` for `H ∈ ℍ`. -/
  P1 : ∀ H ∈ 𝓗, φ H = H
  /-- (P2) `P ⊆ φ(P)` for `P ∈ ℙ`. -/
  P2 : ∀ P ∈ 𝓟, P ⊆ φ P
  /-- (P3) `φ` is monotone on `ℙ`. -/
  P3 : ∀ P₁ ∈ 𝓟, ∀ P₂ ∈ 𝓟, P₁ ⊆ P₂ → φ P₁ ⊆ φ P₂

namespace IsHullMap

variable {𝓟 𝓗 : Set (Set X)} {φ : Set X → Set X}

/-- The clauses of `IsHullMap` (`ℍ ⊆ ℙ`, `φ(ℙ) ⊆ ℍ`, (P1), (P2), (P3)) force
`φ(P) = ⋂ {H ∈ ℍ | P ⊆ H}`, with no hypothesis on intersections. -/
theorem eq_sInter (h : IsHullMap 𝓟 𝓗 φ) {P : Set X} (hP : P ∈ 𝓟) :
    φ P = ⋂₀ {H | H ∈ 𝓗 ∧ P ⊆ H} := by
  apply Set.Subset.antisymm
  · refine Set.subset_sInter fun H hH => ?_
    have := h.P3 P hP H (h.hull_sub hH.1) hH.2
    rwa [h.P1 H hH.1] at this
  · exact Set.sInter_subset_of_mem ⟨h.maps_to P hP, h.P2 P hP⟩

/-- At most one map satisfies the conditions of Remark 3.9.5 (ii) on `ℙ`. -/
theorem unique {ψ : Set X → Set X} (hφ : IsHullMap 𝓟 𝓗 φ) (hψ : IsHullMap 𝓟 𝓗 ψ)
    {P : Set X} (hP : P ∈ 𝓟) : φ P = ψ P := by
  rw [hφ.eq_sInter hP, hψ.eq_sInter hP]

end IsHullMap

/-- Existence: if `ℍ ⊆ ℙ` and, for each `P ∈ ℙ`, the intersection of the members of `ℍ`
containing `P` lies in `ℍ`, then `P ↦ ⋂ {H ∈ ℍ | P ⊆ H}` satisfies (P1), (P2), (P3). -/
theorem isHullMap_sInter {𝓟 𝓗 : Set (Set X)} (hsub : 𝓗 ⊆ 𝓟)
    (hcl : ∀ P ∈ 𝓟, ⋂₀ {H | H ∈ 𝓗 ∧ P ⊆ H} ∈ 𝓗) :
    IsHullMap 𝓟 𝓗 (fun P => ⋂₀ {H | H ∈ 𝓗 ∧ P ⊆ H}) where
  hull_sub := hsub
  maps_to := hcl
  P1 _ hH := Set.Subset.antisymm (Set.sInter_subset_of_mem ⟨hH, le_rfl⟩)
    (Set.subset_sInter fun _ hH' => hH'.2)
  P2 _ _ := Set.subset_sInter fun _ hH => hH.2
  P3 _ _ _ _ h12 := Set.sInter_subset_sInter fun _ hH => ⟨hH.1, h12.trans hH.2⟩

end IUT.PaperIII.Remark3_9_5
