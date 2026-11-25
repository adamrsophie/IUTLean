import AxiomGateLib

/-!
# Gate control: names that capture trusted, dependency and opened names

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`.

The gate runs with the trusted module `Challenge.Defs` among the checked modules, as in the
library configuration, so that a trusted name counts as a name to protect even though its
module is checked.

* `GateControls.Challenge.ABC` makes `Challenge.ABC` inside the namespace mean `True`, so
  `abc_easy` reads like a proof of the abc conjecture.
* `GateControls.log` makes `log` inside the namespace mean the constant zero function even
  under `open Real`, so `Inner.log_is_nonpos` reads like a bound on the real logarithm.
* `GateControls._aux.Real.log` has a namespace component that starts with `_`; only generated
  last components are skipped, so it is reported like any other name.

Expected result: the gate rejects this file with three problems,
`GateControls.Challenge.ABC: its suffix names the constant Challenge.ABC`,
``GateControls.log: under `open Complex` its last component names the constant Complex.log`` (the gate reports the first opened namespace in its list that has a constant `log`; `Real` would do as well) and
`GateControls._aux.Real.log: its suffix names the constant Real.log`.
-/

namespace GateControls

/-- A local `Challenge.ABC`. -/
def Challenge.ABC : Prop := True

/-- Reads like a proof of the abc conjecture. -/
theorem abc_easy : Challenge.ABC := trivial

/-- A local `log` directly in the namespace. -/
noncomputable def log (_ : ℝ) : ℝ := 0

namespace Inner

open Real

/-- Reads like a bound on `Real.log`; `log` is `GateControls.log`. -/
theorem log_is_nonpos (x : ℝ) : log x ≤ 0 := le_refl 0

end Inner

end GateControls

namespace GateControls._aux

/-- A local `Real.log` below a namespace component that starts with `_`. -/
noncomputable def Real.log (_ : ℝ) : ℝ := 0

end GateControls._aux

run_cmd AxiomGate.run { AxiomGate.controlConfig with modulePred := (· == `Challenge.Defs) }
