import Mathlib

/-!
# Mochizuki's elementary models of the logical structure: (Smm) and the toy model

Sources:
* S. Mochizuki, *Report on Discussions, Held During the Period March 15 to 20, 2018,
  Concerning Inter-universal Teichmüller Theory (IUTch)*, version dated February 2019, item
  (Smm), page 2. The whole report was read; page 2 was checked against the rendered page.
* S. Mochizuki, *Inter-universal Teichmüller Theory III*, May 2020 manuscript, Remark 3.12.2,
  (ii), items (a^toy) to (f^toy), pages 189 to 191. Pages 187 to 195 were read; pages 190 and
  191 were checked against the rendered pages. The report cites these "toy models" in its item
  (LbLV), page 24.

**Whose argument.** Both are Mochizuki's. They are offered as "[very rough!]" models of the
logical structure of the argument of IUT III, Corollary 3.12, Step (xi), and of what he calls
the misunderstanding of Scholze and Stix.

**What is proved.** The arithmetic of the two models: in (Smm), the defining relation
`−2B = −A` and the "theorem" `−2B ≤ −2A + 1` give `A ≤ 1`, while adding `A = B` forces
`A = B = 0`; in the toy model, the incompatibility `−h ≠ −2h` for `h > 0` and the formal step
`−h ∈ ℝ_{≤ −2h + ε} ⟹ h ≤ ε`.

**Observation (assessment of this project).** In both models every nontrivial input is a
hypothesis: the "theorem" `−2B ≤ −2A + 1` in (Smm), and the membership
`−h ∈ ℝ_{≤ −2h + ε}` in (e^toy), which Remark 3.12.2 introduces with "suppose that one
verifies". The corresponding assertions about IUT are IUT III, Theorem 3.11 and Corollary 3.12,
Steps (xi-b) to (xi-f). These models do not test them, and this file does not settle the
dispute.
-/

namespace IUT.Audit.MochizukiResponses.ToyModels

/-- (Smm): from the defining relation `−2B = −A` (the Θ-link) and the "theorem"
`−2B ≤ −2A + 1` (the multiradial representation), `A ≤ 1` (Corollary 3.12). -/
theorem smm_bound {A B : ℝ} (hdef : -2 * B = -A) (hthm : -2 * B ≤ -2 * A + 1) : A ≤ 1 := by
  linarith

/-- (Smm): adding the identification `A = B` to the defining relation forces `A = B = 0`. -/
theorem smm_identify {A B : ℝ} (hdef : -2 * B = -A) (hAB : A = B) : A = 0 ∧ B = 0 := by
  constructor <;> linarith

/-- (Smm): hence `A = B` is incompatible with `A > 0`, the "initial assumption". -/
theorem smm_contradiction {A B : ℝ} (hA : 0 < A) (hdef : -2 * B = -A) : A ≠ B := by
  intro hAB; linarith [(smm_identify hdef hAB).1]

/-- (a^toy): without the labels `q`, `Θ`, the two assignments `∗ ↦ −h` and `∗ ↦ −2h`
contradict each other: `−h ≠ −2h` for `h > 0`. -/
theorem toy_incompatible {h : ℝ} (hh : 0 < h) : -h ≠ -2 * h := by
  intro e; linarith

/-- With the labels kept, both assignments hold simultaneously: a function on the two labels. -/
theorem toy_labeled (h : ℝ) :
    ∃ f : Bool → ℝ, f true = -h ∧ f false = -2 * h := ⟨fun b => if b then -h else -2 * h, rfl, rfl⟩

/-- `ℝ_{≤ c} = {x ∈ ℝ | x ≤ c}`. -/
def leSet (c : ℝ) : Set ℝ := {x | x ≤ c}

/-- (f^toy): if `−h ∈ ℝ_{≤ −2h + ε}` (the hypothesis of (e^toy)), then `h ≤ ε`. -/
theorem toy_bound {h ε : ℝ} (hmem : -h ∈ leSet (-2 * h + ε)) : h ≤ ε := by
  simp only [leSet, Set.mem_ofPred_eq] at hmem; linarith

/-- The analogue in the notation of IUT III, Corollary 3.12, Step (xi-f): the inclusion
`−|log(q)| ∈ ℝ_{≤ −|log(Θ)|}` is the inequality `−|log(q)| ≤ −|log(Θ)|`. -/
theorem stepXIf_formal {negLogQ negLogTheta : ℝ} :
    negLogQ ∈ leSet negLogTheta ↔ negLogQ ≤ negLogTheta := Iff.rfl

end IUT.Audit.MochizukiResponses.ToyModels
