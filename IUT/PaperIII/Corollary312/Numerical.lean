import IUT.PaperIV.Theorem1_10.Arithmetic

/-!
# IUT III, Corollary 3.12: the numerical layer of the statement

Source: Mochizuki, *Inter-universal Teichmüller Theory III*, Corollary 3.12 and its proof,
pages 173 to 186 of the May 2020 manuscript, read in full. The statement was also read from
the rendered pages 173 and 174.

## What this file is and is not

Corollary 3.12 defines two numbers from a collection of initial Θ-data:

* `− |log(Θ)| ∈ ℝ ∪ {+∞}`, the procession-normalized mono-analytic log-volume of the
  holomorphic hull of the union of the possible images of a Θ-pilot object, subject to the
  indeterminacies (Ind1), (Ind2), (Ind3);
* `− |log(q)| ∈ ℝ`, the corresponding log-volume of the image of a q-pilot object, not
  subject to the indeterminacies, with `|log(q)| > 0`.

It asserts that `− |log(Θ)| ∈ ℝ` and `− |log(Θ)| ≥ − |log(q)|`.

This project does not yet construct either number from initial Θ-data: Hodge theaters,
the log-theta-lattice, tensor packets and the multiradial representation are not formalized.
So **this file is not a formalization of Corollary 3.12.** It formalizes only what can be
said about the two numbers once they are given: the shape of the conclusion, the "i.e."
reformulation in the statement, the reduction at the start of the proof, and the purely
numerical content of Steps (xi-d) to (xi-f). The structure below has no field that assumes
any conclusion of the paper.
-/

namespace IUT.PaperIII.Corollary312

/-- The two numbers that the statement of Corollary 3.12 defines, with the two properties
that the statement attributes to them *by definition*: the value set `ℝ ∪ {+∞}` of
`− |log(Θ)|`, and `|log(q)| > 0`. Nothing here is constructed from initial Θ-data. -/
structure PilotLogVolumes where
  /-- `− |log(Θ)| ∈ ℝ ∪ {+∞}`. -/
  negLogTheta : EReal
  /-- The value set in the statement is `ℝ ∪ {+∞}`, so `−∞` is excluded. -/
  negLogTheta_ne_bot : negLogTheta ≠ ⊥
  /-- `|log(q)|`; the paper writes the log-volume as `− |log(q)| ∈ ℝ`. -/
  absLogQ : ℝ
  /-- "`|log(q)| > 0` is easily computed in terms of the various q-parameters". -/
  absLogQ_pos : 0 < absLogQ

variable (v : PilotLogVolumes)

/-- The conclusion of Corollary 3.12: `− |log(Θ)| ∈ ℝ` and `− |log(Θ)| ≥ − |log(q)|`. -/
def Conclusion : Prop :=
  v.negLogTheta ≠ ⊤ ∧ ((-v.absLogQ : ℝ) : EReal) ≤ v.negLogTheta

/-- The reformulation after "i.e." in the statement: `C_Θ ≥ −1` for any real number `C_Θ`
such that `− |log(Θ)| ≤ C_Θ · |log(q)|`. -/
def ConstantForm : Prop :=
  ∀ C : ℝ, v.negLogTheta ≤ ((C * v.absLogQ : ℝ) : EReal) → -1 ≤ C

/-- The conclusion implies the "i.e." form. -/
theorem constantForm_of_conclusion (h : Conclusion v) : ConstantForm v := by
  intro C hC
  have h2 : ((-v.absLogQ : ℝ) : EReal) ≤ ((C * v.absLogQ : ℝ) : EReal) := h.2.trans hC
  have h3 : -v.absLogQ ≤ C * v.absLogQ := EReal.coe_le_coe_iff.mp h2
  have hq := v.absLogQ_pos
  by_contra hlt
  push Not at hlt
  nlinarith

/-- When `− |log(Θ)|` is finite, the "i.e." form implies the inequality. -/
theorem conclusion_of_constantForm (hfin : v.negLogTheta ≠ ⊤) (h : ConstantForm v) :
    Conclusion v := by
  refine ⟨hfin, ?_⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, v.negLogTheta = (θ : EReal) :=
    ⟨v.negLogTheta.toReal, (EReal.coe_toReal hfin v.negLogTheta_ne_bot).symm⟩
  have hq := v.absLogQ_pos
  have hC := h (θ / v.absLogQ) (by rw [hθ, div_mul_cancel₀ _ hq.ne'])
  rw [hθ, EReal.coe_le_coe_iff]
  rw [le_div_iff₀ hq] at hC
  linarith

/-- The "i.e." form alone does not give finiteness: it holds when `− |log(Θ)| = +∞`, because
then no real `C_Θ` satisfies its hypothesis. So the "i.e." of the statement reformulates the
inequality, and the assertion `− |log(Θ)| ∈ ℝ` is a separate claim. -/
theorem constantForm_of_top (h : v.negLogTheta = ⊤) : ConstantForm v := by
  intro C hC
  rw [h] at hC
  exact absurd (top_le_iff.mp hC) (EReal.coe_ne_top _)

/-- With finiteness assumed, the conclusion and the "i.e." form are equivalent. -/
theorem conclusion_iff_constantForm (hfin : v.negLogTheta ≠ ⊤) :
    Conclusion v ↔ ConstantForm v :=
  ⟨constantForm_of_conclusion v, conclusion_of_constantForm v hfin⟩

/-- The reduction at the start of the proof: "we may assume without loss of generality that
`− |log(Θ)| < 0`", because `− |log(Θ)| ≥ 0` gives `− |log(Θ)| ≥ 0 > − |log(q)|`. -/
theorem inequality_of_nonneg (h : 0 ≤ v.negLogTheta) :
    ((-v.absLogQ : ℝ) : EReal) ≤ v.negLogTheta := by
  have : ((-v.absLogQ : ℝ) : EReal) ≤ ((0 : ℝ) : EReal) :=
    EReal.coe_le_coe_iff.mpr (by linarith [v.absLogQ_pos])
  exact this.trans (by simpa using h)

/-- The subset `ℝ_{≤ −|log(Θ)|} = {λ ∈ ℝ | λ ≤ − |log(Θ)|}` of Step (xi-d). -/
def possibleLogVolumes : Set ℝ := {lam | (lam : EReal) ≤ v.negLogTheta}

/-- **Step (xi-f) at the level of numbers.** The proof ends: "The inclusion
`− |log(q)| ∈ ℝ_{≤ −|log(Θ)|}`, hence also the inequality `− |log(q)| ≤ − |log(Θ)|`, then
follows formally."

The second step is indeed formal: the inclusion and the inequality are the same proposition,
by unfolding the definition of the subset. Consequently every bit of mathematical content of
Step (xi) lies in establishing the inclusion, that is, in Steps (xi-a) to (xi-e) and the
first sentence of (xi-f). No formalization that keeps only the two real numbers can express
those steps: stated about numbers alone, the premise of the last step is the conclusion. A
non-circular formalization must model the multiradial representation itself, with the
properties (IPL) and (SHE) of Remark 3.11.1. -/
theorem stepXIf_inclusion_iff_inequality :
    -v.absLogQ ∈ possibleLogVolumes v ↔ ((-v.absLogQ : ℝ) : EReal) ≤ v.negLogTheta :=
  Iff.rfl

/-! ## The link to IUT IV, Theorem 1.10 -/

open IUT.PaperIV.Theorem1_10 in
/-- **Conditional derivation of the final inequality of IUT IV, Theorem 1.10.**

Hypotheses, each a statement about given real numbers:

* `hbound`: `− |log(Θ)| ≤ C_Θ · |log(q)|` for the constant `C_Θ` displayed in Theorem 1.10.
  This is the first assertion of Theorem 1.10 ("one may take the constant `C_Θ` to be ...").
* `hcor`: the conclusion of Corollary 3.12.
* the side conditions `7 ≤ l`, `1 ≤ d`, `0 ≤ D`, `0 ≤ E` that the paper cites.

Conclusion: `(1/6)·log(𝔮) ≤ (1 + 20·d_mod/l)·(log 𝔡 + log 𝔣) + 20·(e*_mod·l + η_prm)`.

The theorem is conditional. It does not show that the objects of the paper satisfy `hbound`
or `hcor`; it shows that nothing else is used in passing from them to the final inequality. -/
theorem thm1_10_final_of_cor312 {l d D E Q : ℝ} (hl : 7 ≤ l) (hd : 1 ≤ d) (hD : 0 ≤ D)
    (hE : 0 ≤ E)
    (hbound : v.negLogTheta ≤ ((constant l d D E Q v.absLogQ * v.absLogQ : ℝ) : EReal))
    (hcor : Conclusion v) :
    1 / 6 * Q ≤ (1 + 20 * d / l) * D + 20 * E :=
  final_inequality hl hd hD hE v.absLogQ_pos (constantForm_of_conclusion v hcor _ hbound)

end IUT.PaperIII.Corollary312
