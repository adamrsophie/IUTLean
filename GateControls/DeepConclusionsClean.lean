import AxiomGateLib

/-!
# Gate control: honest statements with many binders or deep connectives pass

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`.

The counterpart of `GateControls/DeepConclusions.lean`: the same shapes, with conclusions that
mention no registered statement. `manyBinders` has 40 leading binders, more than any fixed
small bound, and `nestedTrue` nests six `∧`. Check 3 walks both completely and finds nothing,
so the gate accepts them; the summary line reports the length of the longest walk and the
depth of the deepest split.

Expected result: the gate accepts this file with `0 matches, 0 undecided, 0 incomplete;
longest binder walk 40 binders, deepest split of ∧ and ↔ 6`.
-/

namespace GateControls

set_option linter.unusedVariables false in
theorem manyBinders (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
    x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 : Nat) :
    x0 + x39 = x39 + x0 :=
  Nat.add_comm _ _

theorem nestedTrue : True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (True ∧ (1 = 1)))))) :=
  ⟨trivial, trivial, trivial, trivial, trivial, trivial, rfl⟩

end GateControls

run_cmd AxiomGate.run AxiomGate.controlConfig
