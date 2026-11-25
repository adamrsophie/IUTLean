import AxiomGateLib
import IUT.Applications.ABCSpecialization

/-!
# Gate control: the rational-point form of the abc conjecture under other names

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`. Files in `GateControls/` mention the word axiom on purpose; the
source scan does not read this folder.

`IUT/Applications/ABCSpecialization.lean` proves `VojtaLineMinusThreePointsRational`
equivalent to `Challenge.ABC`; it is not definitionally equal to any older registered form.
Below, the axiom `heightConductorBound` restates it with its body written out, the theorem
`rationalPointBound` states it as `RationalPointBoundFor Height.logHeight₁`, and
`noVojta` refutes it from a second axiom. The gate must name the form in each case. It also
reports the two axioms (check 2) and the axioms behind the theorems (check 1).

Expected result: the gate rejects this file; among the problems are the lines
`GateControls.heightConductorBound: states IUT.ABCSpecialization.VojtaLineMinusThreePointsRational but is not named abcConjecture`,
`GateControls.rationalPointBound: states IUT.ABCSpecialization.VojtaLineMinusThreePointsRational but is not named abcConjecture` and
`GateControls.noVojta: states the negation of IUT.ABCSpecialization.VojtaLineMinusThreePointsRational but is not named abcConjecture`.
-/

namespace GateControls

/-- The form, restated under a new name as an axiom. -/
axiom heightConductorBound : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℚ, x ≠ 0 → x ≠ 1 →
    Height.logHeight₁ x ≤ (1 + ε) * Real.log (IUT.ABCSpecialization.ratConductor x) + C

/-- The form as the bound for Mathlib's height. -/
theorem rationalPointBound : IUT.ABCSpecialization.RationalPointBoundFor Height.logHeight₁ :=
  heightConductorBound

axiom ex : False

/-- The negation of the form. -/
theorem noVojta : ¬ IUT.ABCSpecialization.VojtaLineMinusThreePointsRational := ex.elim

end GateControls

run_cmd AxiomGate.run AxiomGate.controlConfig
