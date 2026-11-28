import AxiomGateLib

/-!
# Gate control: a resolution is announced and passes

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`.

The real `Challenge.ABC` is not proved, so the path of check 3 that announces a resolution is
exercised on a provable local model: `GateControls.ABCIntModel`, registered for this run as a
closed form through `extraRegistered`. `GateControls.abcConjecture` states it as its whole
statement, with no hypothesis and no axiom. `GateControls/RenamedConjecture.lean` exercises
the same path for `Challenge.ABC` itself through a local axiom, so that its gate run fails for
the axiom; this control shows that a resolution alone does not fail the gate.

Expected result: the gate accepts this file and prints
`!!! RESOLUTION: GateControls.abcConjecture proves GateControls.ABCIntModel; axioms: []`.
-/

namespace GateControls

/-- Local model of a closed form, provable. -/
def ABCIntModel : Prop := (2 : ℕ) + 2 = 4

theorem abcConjecture : ABCIntModel := rfl

end GateControls

run_cmd AxiomGate.run { AxiomGate.controlConfig with
  extraRegistered := [(`GateControls.ABCIntModel, `GateControls.ResolutionModel, true, "form")] }
