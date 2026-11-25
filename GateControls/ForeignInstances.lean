import AxiomGateLib

/-!
# Gate control: instances on reducible aliases and default instances

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`. The source scan reports every construct below; this file tests
the gate alone.

* `counterInhabited` is registered with the attribute `@[instance]` on the type
  `Inhabited Counter`, where `Counter` is an `abbrev` of `Nat`. The argument head `Counter`
  is a constant of this file, but instance resolution unfolds it, so the instance is one of
  `Inhabited Nat`.
* `realRel` is an instance of `LEAlias ℝ`, where `LEAlias` is an `abbrev` of `LE`: an order on `ℝ`
  under which every inequality holds.
* `Capsule.fintype` has the last name of the one allowlisted library instance
  `IUT.PaperI.Capsule.fintype`, but it is an order on `Rl`, an `abbrev` of `ℝ`, under which
  every inequality holds; the allowlist binds the full name and the class. Its last name
  also meets check 6 (`Finset.fintype` under `open Finset`).
* `natDefault` is registered only with `@[default_instance]`. Lean keeps that registration
  in a registry of its own, not in the instance table.
* `attribute [default_instance 2000] instOfNat` registers a core constant as a default
  instance from this file; after it, `2 - 3 + 1 = 0` elaborates over the integers.

The quoted spelling `@[«instance»]` does not parse in this toolchain, so it is tested only in
the source scan control.

Expected result: the gate rejects this file with six problems,
`GateControls.counterInhabited: instance of a dependency class on dependency arguments only`,
`GateControls.realRel: instance of a dependency class on dependency arguments only`,
`GateControls.Capsule.fintype: instance of a dependency class on dependency arguments only`,
`GateControls.Capsule.fintype: under \`open Finset\` its last component names the constant Finset.fintype`,
`GateControls.natDefault: default instance of Inhabited registered by a checked module` and
`instOfNat: default instance of OfNat registered by a checked module`.
-/

namespace GateControls

/-- A reducible alias of `Nat`. -/
abbrev Counter := Nat

/-- An instance on the alias, registered through the attribute. -/
@[instance] def counterInhabited : Inhabited Counter := ⟨7⟩

/-- A reducible alias of the class `LE`. -/
abbrev LEAlias (α : Type) := LE α

/-- An instance of the alias on `ℝ`. -/
instance realRel : LEAlias ℝ := ⟨fun _ _ => True⟩

/-- A reducible alias of `ℝ`. -/
abbrev Rl := ℝ

/-- An order on the alias, under the last name of the allowlisted library instance. -/
def Capsule.fintype : LE Rl := ⟨fun _ _ => True⟩

attribute [instance] Capsule.fintype

/-- `2 ≤ 1` on the reals, through the alias instance. -/
theorem two_le_one : (2 : ℝ) ≤ 1 := trivial

/-- A default instance that is not an instance. -/
@[default_instance] def natDefault : Inhabited Nat := ⟨5⟩

attribute [default_instance 2000] instOfNat

/-- False for natural numbers; true over the integers that the default instance selects. -/
theorem numerals : 2 - 3 + 1 = 0 := by decide

end GateControls

run_cmd AxiomGate.run AxiomGate.controlConfig
