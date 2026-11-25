import AxiomGateLib

/-!
# Gate control: a theorem proved with `native_decide`

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`. Files in `GateControls/` mention the words axiom, sorry and
unsafe on purpose; the source scan does not read this folder.

`native_decide` proves the statement by compiled evaluation and records that trust in an
auxiliary axiom (on Lean 4.36 `GateControls.byNative._native.native_decide.ax_1_1`). Expected
result: the gate rejects this file with three problems, two about the auxiliary axiom itself
and the line `GateControls.byNative: depends on [GateControls.byNative._native.native_decide.ax_1_1]`.
-/

namespace GateControls

theorem byNative : 2 ^ 10 = 1024 := by native_decide

end GateControls

run_cmd AxiomGate.run AxiomGate.controlConfig
