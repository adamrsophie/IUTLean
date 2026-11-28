import AxiomGateLib

/-!
# Gate control: the name abcConjecture on a statement that is not a resolution

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`.

Check 3 announces a resolution only for a declaration named `abcConjecture` whose whole
statement is a registered closed form or its negation, with no hypothesis. The name is
reserved for that case: every other declaration with that last name component is an error.
Each declaration below carries the name in a namespace of its own:

* `GateControls.abcConjecture` proves `Challenge.ABC` from a hypothesis `False`;
* `GateControls.Refutation.abcConjecture` proves `¬ Challenge.ABC` from a hypothesis `False`;
* `GateControls.Family.abcConjecture` states an instance of an open family, a local provable
  model `GateControls.ExponentModel` registered for this run through `extraRegistered`;
* `GateControls.Conditional.abcConjecture` assumes `Challenge.ABC` to prove it;
* `GateControls.Plain.abcConjecture` states `1 = 1`.

A hypothesis `False` makes any conclusion provable, so none of these may be reported as a
resolution: the runner checks that no line `!!! RESOLUTION` is printed.

Expected result: the gate rejects this file with 5 problems, one per declaration, among them
`GateControls.abcConjecture: named abcConjecture, but its statement has hypotheses or other
parts around Challenge.ABC` and the same line for `GateControls.Refutation.abcConjecture` and
`the negation of Challenge.ABC`.
-/

namespace GateControls

/-- Local model of an open family, provable exactly for `κ > 1`. -/
def ExponentModel (κ : ℝ) : Prop := 1 < κ

theorem abcConjecture (h : False) : Challenge.ABC := h.elim

namespace Refutation

theorem abcConjecture (h : False) : ¬ Challenge.ABC := h.elim

end Refutation

namespace Family

theorem abcConjecture : ExponentModel 24 := by
  show (1 : ℝ) < 24
  norm_num

end Family

namespace Conditional

theorem abcConjecture (h : Challenge.ABC) : Challenge.ABC := h

end Conditional

namespace Plain

theorem abcConjecture : 1 = 1 := rfl

end Plain

end GateControls

run_cmd AxiomGate.run { AxiomGate.controlConfig with
  extraRegistered := [(`GateControls.ExponentModel, `GateControls.NamedConditional, false,
    "family")] }
