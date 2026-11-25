import AxiomGateLib

/-!
# Gate control: a theorem proved with `sorry`

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`. Files in `GateControls/` mention the words axiom, sorry and
unsafe on purpose; the source scan does not read this folder.

Expected result: the gate rejects this file with exactly one problem, the line
`GateControls.withSorry: depends on [sorryAx]`.
-/

namespace GateControls

theorem withSorry : (2 : Nat) + 2 = 5 := sorry

end GateControls

run_cmd AxiomGate.run AxiomGate.controlConfig
