import AxiomGateLib

/-!
# Gate control: shadowing names and foreign instances

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`.

Inside `namespace GateControls`, the definition `GateControls.Real.log` makes `Real.log` mean
the local constant, so `log_bound` reads like a statement about the real logarithm but is a
statement about the constant zero function. The instance `fakeLE` puts a relation on `ℝ` under
which every inequality holds. Both change the meaning of later statements without any
construct that the source scan looks for among its keywords.

Expected result: the gate rejects this file with two problems:
`GateControls.Real.log: its suffix Real.log names a constant of a dependency` and
`GateControls.fakeLE: instance of a dependency class on dependency arguments only`.
-/

namespace GateControls

/-- A local constant whose name ends in the name of Mathlib's `Real.log`. -/
noncomputable def Real.log (_ : ℝ) : ℝ := 0

/-- Reads like a bound on the logarithm; `Real.log` is the local constant. -/
theorem log_bound (x : ℝ) : Real.log x ≤ 0 := le_refl 0

/-- An order on `ℝ` under which every inequality holds. -/
def fakeLE : LE ℝ := ⟨fun _ _ => True⟩

attribute [instance] fakeLE

end GateControls

run_cmd AxiomGate.run AxiomGate.controlConfig
