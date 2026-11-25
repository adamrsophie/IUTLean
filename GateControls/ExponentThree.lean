import AxiomGateLib
import IUT.ABC.Variants

/-!
# Gate control: near misses of a registered family fail fast

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`.

Each theorem below concludes a statement close to `IUT.ABC.Variants.ABCWithExponent 3` that is
not an instance of it: the exponent `3` as a natural number (a different power operation),
an extra `+ 0` on the real side (equal only after unfolding the addition of the reals), and a
strict inequality. Each takes the same statement as a hypothesis that does not mention a
registered constant, so the gate must compare the conclusion and find no match. Before the
comparison unfolded only project definitions and compared at the transparency of instances,
such a comparison could unfold the arithmetic of `ℝ` until the heartbeat budget ran out.

Expected result: the gate accepts this file with `0 matches, 0 undecided`.
-/

namespace GateControls

open Challenge

theorem cubeNat (h : ∃ K : ℝ, 0 < K ∧ ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → Nat.Coprime a b →
    a + b = c → (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (3 : ℕ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → Nat.Coprime a b →
    a + b = c → (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (3 : ℕ) := h

theorem cubePlusZero (h : ∃ K : ℝ, 0 < K ∧ ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
    Nat.Coprime a b → a + b = c → (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (3 : ℝ) + 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → Nat.Coprime a b →
    a + b = c → (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (3 : ℝ) + 0 := h

theorem cubeStrict (h : ∃ K : ℝ, 0 < K ∧ ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
    Nat.Coprime a b → a + b = c → (c : ℝ) < K * (rad (a * b * c) : ℝ) ^ (3 : ℝ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → Nat.Coprime a b →
    a + b = c → (c : ℝ) < K * (rad (a * b * c) : ℝ) ^ (3 : ℝ) := h

end GateControls

run_cmd AxiomGate.run AxiomGate.controlConfig
