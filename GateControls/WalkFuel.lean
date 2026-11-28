import AxiomGateLib

/-!
# Gate control: an incomplete inspection fails

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`.

The binder walk and the split of `∧` and `↔` of check 3 have a fuel equal to the heartbeat
budget of a statement, which the budget exhausts first. This control lowers the fuel to 4
(through `walkFuel` of the configuration) to see that running out of it is reported as an
incomplete inspection, an error, and not read as "nothing found". Both statements are honest
and pass with the default fuel (`GateControls/DeepConclusionsClean.lean` has the same shapes):
`fiveBinders` has five leading binders and `nestedFive` nests five `∧`.

Expected result: the gate rejects this file with 2 problems:
`GateControls.fiveBinders: inspection by check 3 incomplete: the binder walk ran out of fuel
after 4 binders` and `GateControls.nestedFive: inspection by check 3 incomplete: the split of
∧ and ↔ after 0 binders ran out of fuel`.
-/

namespace GateControls

set_option linter.unusedVariables false in
theorem fiveBinders (n0 n1 n2 n3 n4 : Nat) : n0 + n4 = n4 + n0 := Nat.add_comm _ _

theorem nestedFive : True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (1 = 1))))) :=
  ⟨trivial, trivial, trivial, trivial, trivial, rfl⟩

end GateControls

run_cmd AxiomGate.run { AxiomGate.controlConfig with walkFuel := 4 }
