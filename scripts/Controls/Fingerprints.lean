import Challenge

/-!
# Fingerprint dump of `Challenge.Defs` and `Challenge`

Helper of `scripts/Controls/fingerprints.py`, not part of the library. Run after
`lake build Challenge` (which compiles the root module `Challenge.lean`; it is not a default
target) with `lake env lean scripts/Controls/Fingerprints.lean`. For every constant stored in
the module `Challenge.Defs` and then in the module `Challenge`, in sorted order, it prints
four lines:

    FP-NAME <name>
    FP-MODULE <module>
    FP-KIND <theorem, or other>
    FP-TYPE <structural dump of the elaborated type>
    FP-VALUE <structural dump of the elaborated value, or "none">

The dump is the derived `Repr` of `Lean.Expr`: constructors, names, levels and literals in
full, independent of the pretty printer, of options and of the platform. The script takes the
SHA-256 of each dump. The values of the theorems of `Challenge` are `sorry` on purpose; the
script records only their types.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut out := ""
  for m in [`Challenge.Defs, `Challenge] do
    let some idx := env.getModuleIdx? m | throwError "{m} not imported"
    let names := env.header.moduleData[idx.toNat]!.constNames
    let sorted := names.qsort (fun a b => a.toString < b.toString)
    for n in sorted do
      let s := n.toString
      let some ci := env.find? n | throwError "{s} not found"
      let kind := if ci matches .thmInfo _ then "theorem" else "other"
      let value := match ci.value? (allowOpaque := true) with
        | some v => (reprStr v).replace "\n" " "
        | none => "none"
      out := out ++ s!"FP-NAME {s}\nFP-MODULE {m}\nFP-KIND {kind}\n" ++
        s!"FP-TYPE {(reprStr ci.type).replace "\n" " "}\nFP-VALUE {value}\n"
  IO.print out
