import AxiomGateLib

/-!
# Gate control: conditional statements and refuted instances pass

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`.

The same local models as `GateControls/OpenStatements.lean` (`ABCIntModel`, registered for
this run as a closed form, `ExponentModel` as an open family, `ZhouModel` as an author
statement, through `extraRegistered`). Each theorem below either assumes
a registered statement (the shape of `abcWithExponent_mono`, `abcWithExponent_of_ABC` and of
a use of an author statement), or proves a negated instance of the family (the shape of
`not_abcWithExponent_of_le_one`), or relates two registered statements by an equivalence.

Expected result: the gate accepts this file.
-/

namespace GateControls

/-- Local model of a closed form. -/
def ABCIntModel : Prop := (2 : ℕ) + 2 = 4

/-- Local model of an open family. -/
def ExponentModel (κ : ℝ) : Prop := 1 < κ

/-- An author statement of this control. -/
def ZhouModel : Prop := ∃ n : ℕ, n = 0

theorem mono {κ κ' : ℝ} (h : κ ≤ κ') : ExponentModel κ → ExponentModel κ' :=
  fun h' => lt_of_lt_of_le h' h

theorem ofInt (_h : ABCIntModel) {κ : ℝ} (hκ : 1 < κ) : ExponentModel κ := hκ

theorem notOne : ¬ ExponentModel 1 := lt_irrefl 1

theorem notLe {κ : ℝ} (hκ : κ ≤ 1) : ¬ ExponentModel κ := not_lt.mpr hκ

theorem fromZhou (_h : ZhouModel) : ExponentModel 24 := by
  show (1 : ℝ) < 24
  norm_num

theorem intIff : ABCIntModel ↔ ∀ ε : ℝ, 0 < ε → ExponentModel (1 + ε) :=
  ⟨fun _ ε hε => by show (1 : ℝ) < 1 + ε; linarith, fun _ => rfl⟩

end GateControls

run_cmd AxiomGate.run { AxiomGate.controlConfig with
  extraRegistered := [
    (`GateControls.ABCIntModel, `GateControls.OpenStatementsClean, true, "form"),
    (`GateControls.ExponentModel, `GateControls.OpenStatementsClean, false, "family"),
    (`GateControls.ZhouModel, `GateControls.OpenStatementsClean, true, "author statement")] }
