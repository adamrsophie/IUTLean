import AxiomGateLib

/-!
# Gate control: the abc conjecture proved from an axiom under another name

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`. Files in `GateControls/` mention the words axiom, sorry and
unsafe on purpose; the source scan does not read this folder.

The real `Challenge.ABC` is not proved, so the statements below are proved from a locally
declared axiom. The gate therefore also reports the axiom and the theorems that use it; the
runner checks for the conjecture lines specifically. `unfolded` writes out the body of
`Challenge.ABC`, so its detection tests definitional equality, not a syntactic match. A
theorem named `abcConjecture` is reported as a resolution, not as a misnamed statement.

Expected result: the gate rejects this file with eleven problems, among them the lines
`GateControls.restated: states Challenge.ABC but is not named abcConjecture`,
`GateControls.unfolded: states Challenge.ABC but is not named abcConjecture`,
`GateControls.viaLog: states Challenge.ABCLog but is not named abcConjecture` and
`GateControls.refuted: states the negation of Challenge.ABCFinite but is not named
abcConjecture`.
-/

namespace GateControls

axiom ex : False

theorem restated : Challenge.ABC := ex.elim

theorem unfolded : ∀ e : ℝ, 0 < e → ∃ K : ℝ, 0 < K ∧ ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z →
    Nat.Coprime x y → x + y = z → (z : ℝ) ≤ K * (Challenge.rad (x * y * z) : ℝ) ^ (1 + e) :=
  ex.elim

theorem viaLog : Challenge.ABCLog := ex.elim

theorem refuted : ¬ Challenge.ABCFinite := ex.elim

theorem abcConjecture : Challenge.ABC := ex.elim

end GateControls

run_cmd AxiomGate.run AxiomGate.controlConfig
