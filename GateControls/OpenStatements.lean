import AxiomGateLib

/-!
# Gate control: open statements proved without assuming one

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`.

Check 3 recognizes registered statements by their full names. The gate module imports the
library, so the registered `IUT.ABC.Variants.ABCInt` (a closed form) and
`IUT.ABC.Variants.ABCWithExponent` (an open family) are in scope; their bodies are open. This
file declares provable local models `GateControls.ABCIntModel` (registered for this run as a
closed form, through `extraRegistered`), `GateControls.ExponentModel` (as an open family) and
`GateControls.ZhouModel` (as an author statement). Each theorem below proves one of them
without a hypothesis that mentions a registered statement, packaged in a different way. Three
more theorems conclude the library's `ABCInt` and `ABCWithExponent 24`, and `Challenge.ABC`,
from a hypothesis `False`, which mentions no registered constant; they check that these stay
in the registries of the gate, and that a hypothesis `False` does not exempt a declaration
whose name is not `abcConjecture` (`GateControls/NamedConditional.lean` has the same statement
under that name).

Expected result: the gate rejects this file with 10 problems, one per theorem:
`GateControls.viaAlias: states GateControls.ABCIntModel but is not named abcConjecture`
(the statement is a local alias `Y` of the closed form),
`GateControls.viaBinders`, `GateControls.viaAnd`, `GateControls.viaIff` (the closed form
behind `∀` binders, as a conjunct, as a side of an equivalence with a true statement),
`GateControls.exp24`, `GateControls.expAll` (instances of the family, without and with
binders), `GateControls.zhou` (the author statement), `GateControls.libraryInt`,
`GateControls.libraryExp` (the registered statements of the library) and
`GateControls.conditionalABC` (the abc conjecture itself).
-/

namespace GateControls

/-- Local model of a closed form, provable. -/
def ABCIntModel : Prop := (2 : ℕ) + 2 = 4

/-- Local model of an open family, provable exactly for `κ > 1`. -/
def ExponentModel (κ : ℝ) : Prop := 1 < κ

/-- An author statement of this control, provable. -/
def ZhouModel : Prop := ∃ n : ℕ, n = 0

/-- A local alias of the closed form. -/
def Y : Prop := ABCIntModel

theorem viaAlias : Y := rfl

theorem viaBinders : ∀ n : ℕ, n = n → ABCIntModel := fun _ _ => rfl

theorem viaAnd : 1 = 1 ∧ ABCIntModel := ⟨rfl, rfl⟩

theorem viaIff : ABCIntModel ↔ True := ⟨fun _ => trivial, fun _ => rfl⟩

theorem exp24 : ExponentModel 24 := by
  show (1 : ℝ) < 24
  norm_num

theorem expAll (κ : ℝ) (hκ : 2 ≤ κ) : ExponentModel κ := by
  show (1 : ℝ) < κ
  linarith

theorem zhou : ZhouModel := ⟨0, rfl⟩

/-- The registered closed form of the library, from a hypothesis that mentions no registered
constant. -/
theorem libraryInt (h : False) : IUT.ABC.Variants.ABCInt := h.elim

/-- An instance of the registered family of the library, likewise. -/
theorem libraryExp (h : False) : IUT.ABC.Variants.ABCWithExponent 24 := h.elim

/-- The abc conjecture from a hypothesis that mentions no registered constant. -/
theorem conditionalABC (h : False) : Challenge.ABC := h.elim

end GateControls

run_cmd AxiomGate.run { AxiomGate.controlConfig with
  extraRegistered := [(`GateControls.ABCIntModel, `GateControls.OpenStatements, true, "form"),
    (`GateControls.ExponentModel, `GateControls.OpenStatements, false, "family"),
    (`GateControls.ZhouModel, `GateControls.OpenStatements, true, "author statement")] }
