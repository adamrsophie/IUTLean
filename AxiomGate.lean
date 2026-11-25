import IUT
import Challenge.Defs
import Solution

/-!
# Axiom gate

Enforces the project trust policy over the whole built library. Run after `lake build` with

    lake env lean AxiomGate.lean

The command ends with one summary line and fails (nonzero exit status) if any check fails.

This file is metaprogramming that runs only at elaboration time. It is not part of the
mathematical trust base: it adds no declarations that any theorem of the project uses, and
it only reads the environment produced by the kernel. All definitions here are total; the
graph traversal is a worklist loop bounded by explicit fuel, so no `partial` or `unsafe`
is used.

Checked constants: every constant whose defining module is `IUT`, `IUT.*` (except
`IUT.Experimental.*`), `Challenge.Defs` or `Solution`, private and auxiliary declarations
included. Checks:

0. Experimental modules. No module `IUT.Experimental` or `IUT.Experimental.*` is in the import
   closure. This check runs in every configuration.
1. The axioms each checked constant depends on, transitively through Mathlib and core, are
   among `propext`, `Classical.choice`, `Quot.sound`. This rejects `sorryAx`, the auxiliary
   axioms that `native_decide` introduces, and any added axiom. The traversal walks kernel
   bodies directly with one shared visited set; the per-constant attribution in the failure
   report, and a consistency cross-check, use core `Lean.collectAxioms` (the traversal behind
   `#print axioms`).
2. It is not an axiom, not `unsafe`, not `partial`, not `opaque`, and carries neither
   `@[implemented_by]` nor `@[extern]`. The one exemption is the compiler auxiliary
   `f._unsafe_rec`, which is `partial` but harmless when `f` is a safe definition. It is
   exempt only when it has exactly the shape the elaborator produces (see `helperProblems`);
   the complete inventory of exempted helpers is printed.
3. The conjecture: detection of registered forms only. The registered forms are
   `Challenge.ABC`, `Challenge.ABCFinite`, `Challenge.ABCLog` and the three statements that
   the library proves equivalent to `Challenge.ABC`, `IUT.ABC.FormalConjectures.abc`,
   `IUT.ABC.FormalConjectures.ltConstantMul` and `IUT.ABC.FormalConjectures.qualityVariant`
   (list `conjectures`). Each must be a definition of type `Prop`. No checked constant may
   have a statement that settles one of them, unless its name ends in `abcConjecture`; such a
   theorem is printed prominently with its axioms instead. A statement settles a form when it
   is definitionally equal (`Meta.isDefEq` at default transparency, so reducible and ordinary
   definitions such as `Not`, `Challenge.ABC` and `Challenge.rad` are unfolded, irreducible
   ones are not) to one of the forms in `conjectureForms`: each registered definition or its
   negation. Binder names and binder kinds do not matter. Only statements whose head normal
   form is a `∀` or an `∃` are compared; each comparison runs under its own heartbeat budget,
   and a comparison that runs out of its budget is an error that names the statement. The
   scope is definitional unfolding only. Not detected: forms that are only propositionally
   equivalent to a registered form, for example an extra hypothesis (`True → Challenge.ABC`),
   a conjunction with the conjecture, an equivalence with a true statement, a new
   formulation that is not registered, or an alias marked `@[irreducible]`. Consequences of
   the conjecture other than the registered forms are a matter for reading the statements.
4. Coverage of the library. Every constant stored in a module `IUT` or `IUT.*` of the import
   closure was checked (cross-checked against the environment's own map from constants to
   modules), and every such module other than the umbrella `IUT` stores at least one constant.
   When the environment variable `AXIOM_GATE_TRACKED_FILES` names a file listing the tracked
   files of the checkout, one path per line (the continuous integration passes the output of
   `git ls-files`), every listed `IUT.lean` or `IUT/**.lean` outside `IUT/Experimental/` must
   be a module of the import closure and conversely. When the variable is unset this check is
   skipped with a note, except under continuous integration (`CI=true`), where a missing list
   is an error.
5. Foreign modules. Every module of the import closure either matches the checked module
   names (`modulePred`) or comes from the toolchain or a dependency package, decided by the
   location of its `.olean` file: below the library folder of the running toolchain or below
   `.lake/packages/` of the working directory. Any other module (the challenge module
   `Challenge`, a second library of this package, a path dependency, a module of the project
   named like a dependency) is an error, because checks 2 and 4 would not see it.

6. Shadowing names. No checked constant has a name with a proper suffix that names a
   constant of a dependency (a module outside the checked ones), unless the name is in
   `shadowAllowed`. Inside `namespace IUT.X`, a declaration `IUT.X.Real.log` makes every later
   `Real.log` of that namespace mean the project constant, which changes what a statement says
   without any construct that the source scan reports. Private names are compared by their
   user-facing name; internal auxiliary names are skipped.
7. Foreign instances. No checked instance has a class and argument head symbols that are all
   declared outside the checked modules (an instance such as `LE ℝ` changes the meaning of
   every later statement about `≤` on `ℝ`). A bound variable as an argument counts as foreign.
   An instance whose class or some argument head is a project constant is accepted.

Not detectable at all: a vacuous hypothesis (`h : False`, or hypotheses that cannot hold
together) makes any conclusion provable, and no mechanical check of the environment can tell
it from a genuine hypothesis. Hypotheses are a matter for reading the statements.

Not detectable from the environment: a declaration added with `debug.skipKernelTC` (the
kernel never checked it; `lake check` and `lake comparator` replay the export through the
kernel), and custom elaborators or macros in project files (they leave no trace in
`ConstantInfo` beyond the declarations they produce, which are checked). The source scan
`scripts/Controls/source_scan.py` rejects both kinds of construct in the library sources.

The controls in `GateControls/` import this file as a module and run `run` with
`controlConfig`, which checks the declarations of the control file itself.
-/

open Lean Elab Command

namespace AxiomGate

/-- The only axioms the project may depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Modules where placeholders are allowed and which the library must never import. -/
def isExperimental (m : Name) : Bool := (`IUT.Experimental).isPrefixOf m

/-- Which constants the gate checks. -/
structure Config where
  /-- Modules whose constants are checked. -/
  modulePred : Name → Bool := fun m =>
    ((`IUT).isPrefixOf m && !isExperimental m) || m == `Challenge.Defs || m == `Solution
  /-- Also check the declarations of the file being elaborated (used by the controls). -/
  includeCurrent : Bool := false
  /-- Root module of the library for the coverage checks (check 4); `none` disables them. -/
  libraryRoot? : Option Name := some `IUT
  /-- Run check 5 (foreign modules). -/
  foreignCheck : Bool := true
  /-- Modules that check 5 accepts although they are foreign (used by the controls). -/
  foreignExempt : Name → Bool := fun _ => false

/-- Configuration for the controls: check only the declarations of the current file. -/
def controlConfig : Config :=
  { modulePred := fun _ => false, includeCurrent := true, libraryRoot? := none,
    foreignCheck := false }

/-- Constants referenced directly by a constant, following the cases of `Lean.collectAxioms`. -/
def directDeps (ci : ConstantInfo) : Array Name :=
  match ci with
  | .axiomInfo v  => v.type.getUsedConstants
  | .defnInfo v   => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v    => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _   => #[]
  | .ctorInfo v   => v.type.getUsedConstants
  | .recInfo v    => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray

/-- All axioms reachable from `roots`, with one shared visited set. Also returns the number of
constants visited. Total: the loop runs at most `fuel` steps and fails if fuel runs out. -/
def reachableAxioms (env : Environment) (roots : Array Name) (fuel : Nat) :
    Except String (NameSet × Nat) := Id.run do
  let mut stack := roots
  let mut visited : NameSet := {}
  let mut axioms : NameSet := {}
  for _ in [0:fuel] do
    match stack.back? with
    | none => return .ok (axioms, visited.size)
    | some n =>
      stack := stack.pop
      if visited.contains n then continue
      visited := visited.insert n
      match env.find? n with
      | none => pure ()
      | some ci =>
        if ci matches .axiomInfo _ then axioms := axioms.insert n
        for d in directDeps ci do
          unless visited.contains d do stack := stack.push d
  return .error s!"traversal fuel {fuel} exhausted"

/-- The definitions whose proof or refutation check 3 looks for. -/
def conjectures : List Name :=
  [``Challenge.ABC, ``Challenge.ABCFinite, ``Challenge.ABCLog,
   ``IUT.ABC.FormalConjectures.abc, ``IUT.ABC.FormalConjectures.ltConstantMul,
   ``IUT.ABC.FormalConjectures.qualityVariant]

/-- The statements that settle a conjecture, each with the conjecture and `true` when it
proves the conjecture, `false` when it refutes it. -/
def conjectureForms : TermElabM (Array (Expr × Name × Bool)) := do
  let mut forms : Array (Expr × Name × Bool) := #[]
  for b in [true, false] do
    for c in conjectures do
      let t ← if b then `($(mkCIdent c)) else `(¬ $(mkCIdent c))
      let e ← Term.elabTermAndSynthesize t (some (.sort .zero))
      forms := forms.push (← instantiateMVars e, c, b)
  return forms

/-- Whether the statement `ty` is definitionally equal to one of `forms` (see check 3):
the conjecture, with `true` for a proof and `false` for a refutation. -/
def settles? (forms : Array (Expr × Name × Bool)) (ty : Expr) : MetaM (Option (Name × Bool)) := do
  unless ← Meta.isProp ty do return none
  let w ← Meta.whnfD ty
  unless w.isForall || w.isAppOf ``Exists do return none
  for (f, c, b) in forms do
    if ← Meta.isDefEq ty f then return some (c, b)
  return none

/-- Heartbeat budget (in thousands) of one comparison of check 3. -/
def settlesBudget : Nat := 20000

/-- Names allowed to have a proper suffix that names a constant of a dependency (check 6).
Each entry was read: the suffix is a one-component root name of core or Mathlib (`measure`,
`trans`, `id`), and the project constant is a structure field or a definition or lemma about a
project structure that is used with its full name or by dot notation. -/
def shadowAllowed : List Name :=
  [`IUT.Countermodels.Comparison.NormalizedLine.measure, `IUT.PaperIV.Corollary2_3.BDle.trans,
   `IUT.PaperI.Capsule.Hom.id]

/-- Whether `n` is a constant of a dependency: stored in an imported module that `pred` does
not accept. Constants of the current file are not foreign. -/
def isForeign (env : Environment) (pred : Name → Bool) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => !pred env.header.moduleNames[i.toNat]!
  | none => false

/-- The proper suffixes of a name: `A.B.C` gives `B.C` and `C`. -/
def properSuffixes (n : Name) : List Name :=
  let cs := n.components
  (List.range (cs.length - 1)).map fun k => Name.fromComponents (cs.drop (k + 1))

/-- For check 6: a dependency constant named by a proper suffix of the name of `n`. -/
def shadowed? (env : Environment) (pred : Name → Bool) (n : Name) : Option Name :=
  let user := (privateToUserName? n).getD n
  if n.isInternalDetail || shadowAllowed.contains user then none
  else (properSuffixes user).find? fun s => env.contains s && isForeign env pred s

/-- For check 7: whether the instance `ci` has a foreign class and only foreign argument
heads. -/
def foreignInstance (env : Environment) (pred : Name → Bool) (ci : ConstantInfo) :
    MetaM Bool := do
  unless Meta.isInstanceCore env ci.name do return false
  Meta.forallTelescopeReducing ci.type fun _ body => do
    let .const c _ := body.getAppFn | return false
    unless isForeign env pred c do return false
    for a in body.getAppArgs do
      if let .const h _ := a.getAppFn then
        unless isForeign env pred h do return false
    return true

/-- Imported modules that neither satisfy `pred` nor come from the toolchain or a package
below `.lake/packages/` of the working directory, decided by the location of their `.olean`
file (check 5). Also returns the first name components of the dependency modules. -/
def foreignModules (env : Environment) (pred : Name → Bool) :
    IO (Array Name × NameSet) := do
  let real (p : System.FilePath) : IO (Option String) := do
    try return some ((← IO.FS.realPath p).toString ++ "/") catch _ => return none
  let roots := (← [getLibDir (← getBuildDir),
    pure ((← IO.currentDir) / ".lake" / "packages")].mapM fun r => do real (← r)).filterMap id
  let mut foreign := #[]
  let mut depRoots : NameSet := {}
  for m in env.header.moduleNames do
    if pred m then continue
    let path ← try some <$> (IO.FS.realPath (← findOLean m)) catch _ => pure none
    match path with
    | some p =>
      if roots.any (p.toString.startsWith ·) then depRoots := depRoots.insert m.getRoot
      else foreign := foreign.push m
    | none => foreign := foreign.push m
  return (foreign, depRoots)

/-- For a constant whose name has the compiler helper form `f._unsafe_rec`, the base `f` and
the exemption conditions it fails; `none` when the name does not have that form.

The elaborator (`Lean.Elab.addAndCompilePartialRec`, Lean 4.36) adds the helper for each
function of a structurally, well founded, or partial fixpoint recursive definition that is
compiled (not `noncomputable`), as a `partial` definition with the name `Compiler.mkUnsafeRecName f`, the same type
and universe parameters as `f`, in the same module, with mutual block the helper names of the
block of `f`. All those recursion strategies tag `f` with `Meta.recExt`. A `partial def f`
itself is never exempt here, because `f` is then an opaque constant, not a safe definition. -/
def helperProblems (env : Environment) (ci : ConstantInfo) : Option (Name × Array String) := do
  let base ← Compiler.isUnsafeRecName? ci.name
  let mut bad : Array String := #[]
  unless Compiler.mkUnsafeRecName base == ci.name do
    bad := bad.push "name is not mkUnsafeRecName of the base"
  unless ci matches .defnInfo { safety := .partial, .. } do
    bad := bad.push "helper is not a partial definition"
  match env.find? base with
  | some (.defnInfo v) =>
    unless v.safety == .safe do bad := bad.push "base is not a safe definition"
    unless Meta.recExt.isTagged env base do
      bad := bad.push "base is not a recursive definition"
    -- The elaborator generates no helper for a `noncomputable` base. The tag can also be
    -- added after compilation fails inside a `noncomputable section`, where a real helper
    -- exists; such a helper is then rejected, which errs on the safe side.
    if isNoncomputable env base then bad := bad.push "base is noncomputable"
    unless env.getModuleIdxFor? base == env.getModuleIdxFor? ci.name do
      bad := bad.push "base is defined in another module"
    unless v.type == ci.type do bad := bad.push "types differ"
    unless v.levelParams == ci.levelParams do bad := bad.push "universe parameters differ"
    unless ci.all == v.all.map Compiler.mkUnsafeRecName do
      bad := bad.push "mutual block does not match the base"
  | some _ => bad := bad.push "base is not a definition"
  | none => bad := bad.push "base does not exist"
  return (base, bad)

/-- Library module names for the files in a list of tracked paths: `IUT.lean` and
`IUT/**.lean` relative to the repository root, without the experimental modules. -/
def trackedModules (root : Name) (paths : List String) : List Name :=
  let rootStr := root.toString
  paths.filterMap fun line =>
    let p := line.trimAscii.toString
    if p == rootStr ++ ".lean" || (p.startsWith (rootStr ++ "/") && p.endsWith ".lean") then
      let m := ((p.dropEnd 5).toString.splitOn "/").foldl Name.str .anonymous
      if isExperimental m then none else some m
    else none

/-- Run every check. Throws an error listing all offenders, or logs one summary line. -/
def run (cfg : Config := {}) : CommandElabM Unit := do
  let t0 ← IO.monoMsNow
  let env := (← getEnv).setExporting false
  let names := env.header.moduleNames
  let projModules := (List.range names.size).filter fun i => cfg.modulePred names[i]!
  -- Every constant stored in a project module's olean, private and auxiliary ones included.
  -- (`constNames` can list a name twice, hence the deduplication.)
  let mut consts : Array ConstantInfo := #[]
  let mut listed : NameSet := {}
  for i in projModules do
    for n in env.header.moduleData[i]!.constNames do
      if listed.contains n then continue
      listed := listed.insert n
      let some ci := env.find? n | throwError "axiom gate: {n} listed in {names[i]!} but not found"
      consts := consts.push ci
  if cfg.includeCurrent then
    consts := env.constants.foldStage2 (fun acc _ ci => acc.push ci) consts
  let mut errors : Array MessageData := #[]
  let mut notes : Array MessageData := #[]
  -- Check 0: experimental modules.
  for m in names do
    if isExperimental m then
      errors := errors.push m!"module {m} is experimental and must not be in the import closure"
  -- Check 4: coverage of the library.
  if let some root := cfg.libraryRoot? then
    let libModules := (List.range names.size).filter fun i => root.isPrefixOf names[i]!
    if libModules.isEmpty then errors := errors.push m!"no module {root} or {root}.* imported"
    for i in libModules do
      let cn := env.header.moduleData[i]!.constNames
      let missed := cn.filter (!listed.contains ·)
      unless missed.isEmpty do
        errors := errors.push
          m!"module {names[i]!} skipped: {missed.size} of its constants were not checked"
      if cn.isEmpty && names[i]! != root then
        errors := errors.push m!"module {names[i]!} defines no checked constant"
    -- Cross-check the enumeration against the environment's map from constants to modules.
    let libIdx : List Nat := libModules
    let unlisted := env.constants.map₁.fold (init := (0 : Nat)) fun k n _ =>
      match env.getModuleIdxFor? n with
      | some j => if libIdx.contains j.toNat && !listed.contains n then k + 1 else k
      | none => k
    unless unlisted == 0 do
      errors := errors.push m!"{unlisted} library constants missing from the enumeration"
    -- Tracked source files.
    match ← IO.getEnv "AXIOM_GATE_TRACKED_FILES" with
    | some path =>
      let tracked := trackedModules root (← IO.FS.lines path).toList
      let loaded := libModules.map (names[·]!)
      let before := errors.size
      if tracked.isEmpty then errors := errors.push m!"source coverage: no library file in {path}"
      for m in tracked do
        unless loaded.contains m do
          errors := errors.push m!"source coverage: {m} is tracked but not imported by {root}"
      for m in loaded do
        unless tracked.contains m do
          errors := errors.push m!"source coverage: {m} is imported but not tracked"
      if errors.size == before then
        notes := notes.push
          m!"source coverage OK: {tracked.length} tracked library files, all imported by {root}"
    | none =>
      if (← IO.getEnv "CI") == some "true" then
        errors := errors.push m!"source coverage: AXIOM_GATE_TRACKED_FILES is unset under CI"
      else
        notes := notes.push m!"source coverage not checked: AXIOM_GATE_TRACKED_FILES is unset"
  -- Check 5: foreign modules.
  if cfg.foreignCheck then
    let (foreign, depRoots) ← foreignModules env cfg.modulePred
    let before := errors.size
    for m in foreign do
      unless cfg.foreignExempt m do
        errors := errors.push
          m!"module {m} is not checked and comes neither from the toolchain nor from a package"
    if errors.size == before then
      notes := notes.push m!"foreign modules: none; the dependency modules have the first name \
        components {", ".intercalate (depRoots.toList.map toString)}"
  -- Check 2: forbidden kinds of declarations.
  let mut helpers : Array MessageData := #[]
  for ci in consts do
    let n := ci.name
    let mut bad : Array String := #[]
    if ci matches .axiomInfo _ then bad := bad.push "is an axiom"
    if ci.isUnsafe then bad := bad.push "is unsafe"
    -- The compiler adds a `partial` auxiliary `f._unsafe_rec` for code generation of
    -- ordinary recursive definitions. It is harmless when `f` itself is a safe kernel
    -- definition: the kernel never lets a safe constant refer to a partial one. It is exempt
    -- only when it has exactly the shape the elaborator produces.
    if ci.isPartial then
      match helperProblems env ci with
      | some (base, #[]) =>
        let mod := match env.getModuleIdxFor? n with
          | some j => names[j.toNat]!
          | none => env.mainModule
        helpers := helpers.push m!"{n} (base {base}, module {mod})"
      | some (_, why) =>
        bad := bad.push s!"is partial (not a compiler helper: {", ".intercalate why.toList})"
      | none => bad := bad.push "is partial"
    if ci matches .opaqueInfo _ then bad := bad.push "is opaque"
    if (Compiler.implementedByAttr.getParam? env n).isSome then
      bad := bad.push "has @[implemented_by]"
    if isExtern env n then bad := bad.push "has @[extern]"
    unless bad.isEmpty do
      errors := errors.push m!"{n}: {", ".intercalate bad.toList}"
  -- Check 6: shadowing names.
  for ci in consts do
    if let some s := shadowed? env cfg.modulePred ci.name then
      errors := errors.push m!"{ci.name}: its suffix {s} names a constant of a dependency"
  -- Check 7: foreign instances.
  let commandEnv0 ← getEnv
  let foreignInsts ← liftCoreM do
    setEnv env
    let mut out : Array Name := #[]
    for ci in consts do
      if ← (foreignInstance env cfg.modulePred ci).run' then out := out.push ci.name
    return out
  setEnv commandEnv0
  for n in foreignInsts do
    errors := errors.push m!"{n}: instance of a dependency class on dependency arguments only"
  -- Check 1: axioms, by one shared traversal of the whole dependency closure.
  let (seen, visitedCount) ← match reachableAxioms env (consts.map (·.name)) 100000000 with
    | .ok r => pure r
    | .error e => throwError "axiom gate: {e}"
  let t1 ← IO.monoMsNow
  let badAxioms := seen.toList.filter (!allowedAxioms.contains ·)
  -- Cross-check against core `collectAxioms` and attribute offenders per constant.
  let mut coreSeen : NameSet := {}
  for ci in consts do
    let axs ← collectAxioms ci.name
    coreSeen := axs.foldl (·.insert ·) coreSeen
    let offending := axs.toList.filter (!allowedAxioms.contains ·)
    unless offending.isEmpty do
      errors := errors.push m!"{ci.name}: depends on {offending}"
  let t2 ← IO.monoMsNow
  unless coreSeen.toList.all seen.contains && seen.toList.all coreSeen.contains do
    errors := errors.push
      m!"axiom sets disagree: traversal {seen.toList}, collectAxioms {coreSeen.toList}"
  if !badAxioms.isEmpty && errors.isEmpty then
    errors := errors.push m!"forbidden axioms reachable: {badAxioms}"
  -- Check 3: the conjecture.
  let mut resolutions : Array MessageData := #[]
  let mut defsOk := true
  for conj in conjectures do
    match env.find? conj with
    | some (.defnInfo v) =>
      unless v.type == .sort .zero do
        errors := errors.push m!"{conj} has type {v.type}, expected Prop"
        defsOk := false
    | some _ => errors := errors.push m!"{conj} is not a definition"; defsOk := false
    | none => errors := errors.push m!"{conj} not found"; defsOk := false
  if defsOk then
    let t30 ← IO.monoMsNow
    let forms ← liftTermElabM conjectureForms
    let candidates := consts.filter fun ci =>
      ci matches .thmInfo _ || ci matches .defnInfo _ || ci matches .opaqueInfo _
    let commandEnv ← getEnv
    let (found, undecided) ← liftCoreM do
      setEnv env
      let mut found : Array (ConstantInfo × Name × Bool) := #[]
      let mut undecided : Array Name := #[]
      for ci in candidates do
        let r ← tryCatchRuntimeEx
          (withCurrHeartbeats <|
            withTheReader Core.Context (fun c => { c with maxHeartbeats := settlesBudget * 1000 })
              (Except.ok <$> (settles? forms ci.type).run'))
          (fun _ => pure (Except.error ()))
        match r with
        | .ok (some cb) => found := found.push (ci, cb)
        | .ok none => pure ()
        | .error _ => undecided := undecided.push ci.name
      return (found, undecided)
    setEnv commandEnv
    for n in undecided do
      errors := errors.push m!"{n}: comparison with the conjecture ran out of its heartbeat budget"
    notes := notes.push m!"conjecture check: {candidates.size} statements compared up to \
      unfolding with {forms.size} forms, {found.size} matches, {undecided.size} undecided, \
      {(← IO.monoMsNow) - t30} ms"
    for (ci, conj, b) in found do
      let kind := if b then toString conj else s!"the negation of {conj}"
      if ci.name matches .str _ "abcConjecture" then
        let axs ← collectAxioms ci.name
        resolutions := resolutions.push
          m!"!!! RESOLUTION: {ci.name} proves {kind}; axioms: {axs.toList} !!!"
      else
        errors := errors.push m!"{ci.name}: states {kind} but is not named abcConjecture"
  logInfo (m!"exempted compiler helpers ({helpers.size}):\n" ++
    MessageData.joinSep helpers.toList "\n")
  for r in notes do logInfo r
  for r in resolutions do logInfo r
  unless errors.isEmpty do
    throwError m!"axiom gate FAILED ({errors.size} problems):\n" ++
      MessageData.joinSep errors.toList "\n"
  let thms : Nat := consts.foldl (fun (k : Nat) ci => if ci matches .thmInfo _ then k + 1 else k) 0
  let t3 ← IO.monoMsNow
  logInfo m!"axiom gate OK: {projModules.length} modules, {consts.size} constants checked, \
    {thms} theorems, axioms seen {toString seen.toList}; enumeration and traversal of \
    {visitedCount} constants {t1 - t0} ms, collectAxioms cross-check {t2 - t1} ms, total {t3 - t0} ms"

end AxiomGate

run_cmd AxiomGate.run
