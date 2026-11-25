import Challenge.Defs

/-!
# Fingerprint dump of `Challenge.Defs`

Helper of `scripts/Controls/fingerprints.py`, not part of the library. Run after building
`Challenge.Defs` with `lake env lean scripts/Controls/Fingerprints.lean`. For every constant
stored in the module `Challenge.Defs`, in sorted order, it prints three lines:

    FP-NAME <name>
    FP-TYPE <structural dump of the elaborated type>
    FP-VALUE <structural dump of the elaborated value, or "none">

The dump is the derived `Repr` of `Lean.Expr`: constructors, names, levels and literals in
full, independent of the pretty printer, of options and of the platform. The script takes the
SHA-256 of each dump.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Challenge.Defs | throwError "Challenge.Defs not imported"
  let names := env.header.moduleData[idx.toNat]!.constNames
  let sorted := names.qsort (fun a b => a.toString < b.toString)
  let mut out := ""
  for n in sorted do
    let s := n.toString
    let some ci := env.find? n | throwError "{s} not found"
    let value := match ci.value? (allowOpaque := true) with
      | some v => (reprStr v).replace "\n" " "
      | none => "none"
    out := out ++ s!"FP-NAME {s}\nFP-TYPE {(reprStr ci.type).replace "\n" " "}\nFP-VALUE {value}\n"
  IO.print out
