import IUT
import Challenge.Defs

/-!
# Declaration inventory of the built library

Run after `lake build` with

    LEAN_DECLARATIONS_OUT=data/lean_declarations.json lake env lean scripts/LeanDeclarations.lean

Without the environment variable the JSON goes to standard output.

For every constant stored in a module `IUT`, `IUT.*` or `Challenge.Defs` of the import
closure it records: the name, the kind (theorem, definition, structure, class, instance,
inductive, constructor, recursor, axiom, opaque, quotient), the module, whether the name is
an internal detail (`Name.isInternalDetail`: auxiliary lemmas such as `_proof_1`, matchers,
equation lemmas), the axioms it depends on (`Lean.collectAxioms`, the traversal behind
`#print axioms`), and the project constants that its type and its value mention directly
(`ConstantInfo.getUsedConstantsAsSet`). Internal constants are kept so that a reader can
contract through them; `scripts/build_graph.py` does that.

Only modules imported by `IUT.lean` are seen. A module that exists on disk but is not
imported by the root is missing from the output.

This file is a reporting script. It is not part of the library and nothing imports it.
-/

open Lean Elab Command

namespace LeanDeclarations

/-- Whether a module belongs to the project. -/
def isProjectModule (m : Name) : Bool :=
  m == `IUT || (`IUT).isPrefixOf m || m == `Challenge.Defs

/-- A short name for the kind of a constant. -/
def kindOf (env : Environment) (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .inductInfo _ =>
    if isClass env ci.name then "class"
    else if isStructure env ci.name then "structure"
    else "inductive"
  | .defnInfo _ =>
    if Meta.isInstanceCore env ci.name then "instance"
    else if env.isProjectionFn ci.name then "projection"
    else "definition"

end LeanDeclarations

open LeanDeclarations in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let moduleOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx]!
  let isProject (n : Name) : Bool := (moduleOf n).any isProjectModule
  let names := env.constants.fold (init := #[]) fun acc n _ =>
    if isProject n then acc.push n else acc
  let names := names.qsort Name.lt
  let mut records : Array Json := #[]
  for n in names do
    let some ci := env.find? n | continue
    let axioms ← collectAxioms n
    let refs := (ci.getUsedConstantsAsSet.toArray.filter fun d => d != n && isProject d)
    records := records.push <| Json.mkObj [
      ("name", toJson n.toString),
      ("kind", toJson (kindOf env ci)),
      ("module", toJson ((moduleOf n).getD .anonymous).toString),
      ("internal", toJson n.isInternalDetail),
      ("axioms", toJson ((axioms.map toString).qsort (· < ·))),
      ("refs", toJson ((refs.map toString).qsort (· < ·)))]
  let modules := (env.header.moduleNames.filter isProjectModule).map toString
  let out := Json.mkObj [
    ("modules", toJson (modules.qsort (· < ·))),
    ("declarations", Json.arr records)]
  let text := out.pretty ++ "\n"
  match ← IO.getEnv "LEAN_DECLARATIONS_OUT" with
  | some path => IO.FS.writeFile path text
  | none => IO.print text
