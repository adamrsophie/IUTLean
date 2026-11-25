import AxiomGateLib

/-!
# Gate control: a private declaration that shadows a dependency name

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`.

Inside `namespace GateControls`, the private definition `Nat.succ` makes every later
`Nat.succ` of the namespace in this file mean the identity, so `succ_eq` reads like a false
statement about the successor but is proved by `rfl`. In the environment the constant is
stored under the name `_private.<module>.0.GateControls.Nat.succ`, and the private prefix is
itself a generated name component; the gate must compare the user-facing name
`GateControls.Nat.succ`. The private recursive definition `countDown` has generated
auxiliaries (its match and its compiler helper `_unsafe_rec`), whose user-facing names are
generated names; they must not be reported.

Expected result: the gate rejects this file with one problem,
`GateControls.Nat.succ (private): its suffix Nat.succ names a constant of a dependency`.
-/

namespace GateControls

/-- A private constant whose user-facing name ends in the name of core's `Nat.succ`. -/
private def Nat.succ (n : Nat) : Nat := n

/-- Reads like `n + 1 = n`; `Nat.succ` is the private constant. -/
theorem succ_eq (n : Nat) : Nat.succ n = n := rfl

/-- A private recursive definition with generated auxiliaries. -/
private def countDown : Nat → Nat
  | 0 => 0
  | n + 1 => countDown n

theorem countDown_zero : countDown 0 = 0 := rfl

end GateControls

run_cmd AxiomGate.run AxiomGate.controlConfig
