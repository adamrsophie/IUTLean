import AxiomGateLib
import IUT.Experimental.GateProbe

/-!
# Gate control: an experimental module in the import closure

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`. Files in `GateControls/` mention the words axiom, sorry and
unsafe on purpose; the source scan does not read this folder.

`GateControls/run.sh` compiles `GateControls/GateProbe.lean` as the module
`IUT.Experimental.GateProbe` in a temporary folder. Expected result: the gate rejects this
file with exactly one problem, the line
`module IUT.Experimental.GateProbe is experimental and must not be in the import closure`.
-/

run_cmd AxiomGate.run AxiomGate.controlConfig
