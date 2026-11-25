import AxiomGateLib

/-!
# Gate control: forms of the abc conjecture that the library proves equivalent

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`. Files in `GateControls/` mention the words axiom and sorry on
purpose; the source scan does not read this folder.

`IUT/Applications/ABCFormalConjectures.lean` proves `qualityVariant`, `abc` and
`ltConstantMul` equivalent to `Challenge.ABC`; none of them is definitionally equal to a form
of `Challenge.Defs`. The theorems below prove two of them, and refute the third, from a
locally declared axiom under innocent names. The gate must report each as a statement of a
registered form.

Expected result: the gate rejects this file; among the problems are the lines
`GateControls.qualityBound: states IUT.ABC.FormalConjectures.qualityVariant but is not named
abcConjecture`, `GateControls.finiteTriples: states IUT.ABC.FormalConjectures.abc but is not
named abcConjecture` and `GateControls.noConstant: states the negation of
IUT.ABC.FormalConjectures.ltConstantMul but is not named abcConjecture`.
-/

namespace GateControls

axiom ex : False

theorem qualityBound : IUT.ABC.FormalConjectures.qualityVariant := ex.elim

theorem finiteTriples : IUT.ABC.FormalConjectures.abc := ex.elim

theorem noConstant : ¬ IUT.ABC.FormalConjectures.ltConstantMul := ex.elim

end GateControls

run_cmd AxiomGate.run AxiomGate.controlConfig
