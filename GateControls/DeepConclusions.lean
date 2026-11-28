import AxiomGateLib

/-!
# Gate control: a registered statement behind many binders or deep connectives

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`.

Each theorem below concludes `Challenge.ABC` from a hypothesis `False`, which mentions no
registered constant, so check 3 must report it. The conclusion is placed where a walk with a
fixed small bound would not look: behind the hypothesis and 34 further binders
(`deepBinders`), as the innermost conjunct of five nested `∧` (`nestedAnd`), and as the
innermost side of five nested `↔` with `True` (`nestedIff`). The binder walk of check 3 strips
every leading binder, and the split of `∧` and `↔` goes to any depth; only the heartbeat
budget of a statement bounds them, and running out of it is an error.

Expected result: the gate rejects this file with 3 problems, one per theorem:
`GateControls.deepBinders: concludes Challenge.ABC (registered form)`, and the same for
`GateControls.nestedAnd` and `GateControls.nestedIff`.
-/

namespace GateControls

theorem deepBinders (h : False) :
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Challenge.ABC :=
  h.elim

theorem nestedAnd (h : False) :
    True ∧ (True ∧ (True ∧ (True ∧ (True ∧ Challenge.ABC)))) :=
  h.elim

theorem nestedIff (h : False) :
    ((((Challenge.ABC ↔ True) ↔ True) ↔ True) ↔ True) ↔ True :=
  h.elim

end GateControls

run_cmd AxiomGate.run AxiomGate.controlConfig
