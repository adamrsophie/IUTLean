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
3. Open statements: no checked declaration proves an open statement without assuming one.
   Three registries, plain lists in this file: `closedForms` (the abc conjecture
   `Challenge.ABC`, `ABCFinite`, `ABCLog`, the statements the library proves equivalent to
   it, and other open statements related to it), `openFamilies` (constants of type
   `… → Prop` with open instances, such as `ABCWithExponent`) and `authorStatements` (claims
   of other papers that the library may assume but not prove). Each entry names a definition and its module. An entry whose module
   is not in the import closure is skipped with a note, except under continuous integration
   (`CI=true`), where it is an error, as is an entry that is missing although its module is
   imported. For every checked theorem, definition, opaque constant or axiom of type a
   proposition, the gate compares the statement and then, stripping the leading `∀` binders
   one at a time (each time after reducible unfolding), each conclusion; of each it compares
   the whole, the two conjuncts of an `∧`, and each side of an `↔` whose other side mentions
   no registered constant. A part matches an entry `c` when, after both are expanded (every
   definition of the project and of the file, instances excepted, and `Not` unfolded,
   whatever their reducibility: `expandProject`), it is equal to `c ?x₁ … ?xₙ` for fresh
   metavariables, or, for closed forms and author statements, to its negation, by
   `Meta.isDefEq` at the transparency of instances (Mathlib definitions stay folded). So a
   local `def Y : Prop := Challenge.ABC` and `theorem t : Y` match, also when `Y` is
   irreducible, and a near miss on `ℝ` fails at once instead of unfolding the reals. A match is an error unless a stripped hypothesis mentions a registered
   constant (by name, without unfolding), in which case the declaration is a conditional
   statement and accepted (`abc_of_abcLog : ABCLog → ABC`, `abcWithExponent_mono`). A match of
   the whole statement with a closed form is reported as "states ... but is not named
   abcConjecture"; a theorem named `abcConjecture` is printed prominently with its axioms
   instead of being an error. An axiom is also rejected by check 2. Comparisons are skipped
   when the reducible weak head normal forms differ in shape (`∀` or head constant), and each
   statement has its own heartbeat budget; running out of it is an error, never a pass. Negated instances of
   a family are not reported (`not_abcWithExponent_of_le_one` is proved). Not detected:
   statements only propositionally equivalent to a registered one (an extra hypothesis
   `True → Challenge.ABC`, an equivalence with a true statement whose side mentions a
   registered constant, a new formulation that is not registered), a hypothesis that mentions
   a registered constant without assuming it (`(h : Challenge.ABC → True)` exempts the
   declaration), a statement equal to a registered one only after unfolding a Mathlib
   definition, an alias that hides the binders or connectives around a registered statement
   (they are read up to reducible unfolding), an alias of a registered statement used as
   a hypothesis (it is not recognized as assumed, which fails closed), and a structure field
   that assumes a form. Consequences of the conjecture other than the registered statements
   are a matter for reading the statements.
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

6. Shadowing names. Inside `namespace IUT.X`, a declaration `IUT.X.Real.log` makes every later
   `Real.log` of that namespace mean the project constant, which changes what a statement says
   without any construct that the source scan reports. Write the name of a checked constant as
   `c₁.….cₖ` (for a private declaration, its user-facing name without the prefix
   `_private.<module>.0`, so a user-written `private def Nat.succ` is treated like a public
   one). It is rejected, unless its full name is in `shadowAllowed`, when (suffix rule) a
   constant `c₁.….cⱼ.cᵢ₊₁.….cₖ` with `j ≤ i < k` exists outside the library `IUT`, that is, a
   proper suffix of the name at the root or under an enclosing namespace names a dependency
   constant or a trusted constant of `Challenge.Defs`, `Challenge` or `Solution` (so
   `IUT.Applications.Challenge.ABC` is rejected although `Challenge.Defs` is a checked
   module); or (open rule) its namespace `c₁.….cₖ₋₁` is not itself a constant and some
   `O.cₖ` exists outside the library for `O` in `openedNamespaces`, the dependency
   namespaces whose `open` the source scan accepts (inside the namespace of `IUT.log`, the
   identifier `log` means `IUT.log` even under `open Real`). Generated names are skipped:
   a last component that the compiler or the elaborator generates (`_unsafe_rec`, `match_1`,
   `proof_1`, `eq_1`, numeric), and the recursors, `casesOn`, `noConfusion`, injectivity
   lemmas and default constructor `mk` of an inductive type (`generatedForInductive`). A
   namespace component that starts with `_` (`IUT._aux`) is no reason to skip a name. Not
   reported: a project name that shadows another project name; a member `S.c` of a project
   type `S` that captures `c` of an opened namespace inside `namespace S`; the open rule does
   not know which file opens which namespace, so it over-approximates for names declared
   directly in a namespace (the allowlist records the cases that were read). `export`,
   `open ... renaming` and `open ... hiding` are rejected by the source scan.
7. Instances. The instance registrations that the checked modules add (the instance table
   and, separately, the default-instance registry, both read per module) and the checked
   constants that are instances are inspected. No instance may have a class and argument head
   symbols that are all declared outside the checked modules (an instance such as `LE ℝ`
   changes the meaning of every later statement about `≤` on `ℝ`); the class application and
   each argument are first put in weak head normal form at the transparency of instance
   resolution (`instances`: reducible and instance definitions are unfolded), so an instance
   on `abbrev Counter := Nat` counts as an instance on `Nat`, and an instance of an `abbrev`
   of a foreign class as one of that class; a bound variable as an argument counts as
   foreign, a projection `x.i` counts as its structure. Every other instance must be in
   `instanceAllowed` with exactly the listed class, or be a `SizeOf` instance with a
   generated name (Lean adds one for each inductive type). This binds the one instance the
   source scan accepts by its full name and class. No checked module may register a default
   instance at all (`@[default_instance]` or `attribute [default_instance]`, on a project or
   a dependency constant): a default instance decides the type of otherwise undetermined
   terms, such as numerals, in later statements.

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
  /-- Check 3: under continuous integration, a registered statement whose module is not in the
  import closure is an error (off for the controls, which import few modules). -/
  requireRegistered : Bool := true
  /-- Check 3: entries added to the registries for this run (used by the controls); same
  shape as `registered`. -/
  extraRegistered : List (Name × Name × Bool × String) := []

/-- Configuration for the controls: check only the declarations of the current file. -/
def controlConfig : Config :=
  { modulePred := fun _ => false, includeCurrent := true, libraryRoot? := none,
    foreignCheck := false, requireRegistered := false }

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

/-! ### Registries of check 3

Three plain lists; an entry is the full name of a constant and the module that declares it. A
new entry needs no change of the logic below. -/

/-- Closed forms: open statements of type `Prop`: the abc conjecture, the statements that the
library proves equivalent to it, and other open statements related to it: one that implies it
(`VojtaLineMinusThreePointsBoundedDegree`) and four that it or the bounded degree statement
implies (`IUT.CompactlyBounded`). No checked declaration may
prove one, or its negation, without assuming a registered statement (check 3). -/
def closedForms : List (Name × Name) :=
  [(`Challenge.ABC, `Challenge.Defs), (`Challenge.ABCFinite, `Challenge.Defs),
   (`Challenge.ABCLog, `Challenge.Defs),
   (`IUT.ABC.FormalConjectures.abc, `IUT.Applications.ABCFormalConjectures),
   (`IUT.ABC.FormalConjectures.ltConstantMul, `IUT.Applications.ABCFormalConjectures),
   (`IUT.ABC.FormalConjectures.qualityVariant, `IUT.Applications.ABCFormalConjectures),
   (`IUT.ABC.Variants.ABCInt, `IUT.ABC.Variants),
   (`IUT.ABC.Variants.ABCIntSum, `IUT.ABC.Variants),
   (`IUT.ABCSpecialization.VojtaLineMinusThreePointsRational,
    `IUT.Applications.ABCSpecialization),
   (`IUT.ABCSpecialization.VojtaLineMinusThreePointsUnitInterval,
    `IUT.Applications.ABCSpecialization),
   (`IUT.VojtaNumberField.VojtaLineMinusThreePointsBoundedDegree,
    `IUT.Applications.VojtaNumberField),
   (`IUT.CompactlyBounded.iutIVCor2_3ReducedFormStatement, `IUT.Applications.CompactlyBounded),
   (`IUT.CompactlyBounded.abcRatioBoundedStatement, `IUT.Applications.CompactlyBounded),
   (`IUT.CompactlyBounded.cbDegreeOneAllStatement, `IUT.Applications.CompactlyBounded),
   (`IUT.CompactlyBounded.cbDegreeOneSupportFreeStatement, `IUT.Applications.CompactlyBounded)]

/-- Open families: constants of type `α₁ → … → αₙ → Prop` some of whose instances are open
(`ABCWithExponent κ` for `κ > 1`; `RationalPointBoundFor Height.logHeight₁` is the closed
form `VojtaLineMinusThreePointsRational`). No checked declaration may conclude an instance,
for any arguments, without assuming a registered statement. Negated instances are not
reported, so the refutations for `κ ≤ 1` pass (`not_abcWithExponent_of_le_one`), and so do
implications between instances (`abcWithExponent_mono`), whose hypothesis is an instance. A
proved instance that is not a negation goes in `provedInstances`. -/
def openFamilies : List (Name × Name) :=
  [(`IUT.ABC.Variants.ABCWithExponent, `IUT.ABC.Variants),
   (`IUT.ABCSpecialization.RationalPointBoundFor, `IUT.Applications.ABCSpecialization),
   (`IUT.VojtaNumberField.VojtaLineMinusThreePointsDegreeAtMost,
    `IUT.Applications.VojtaNumberField),
   (`IUT.CompactlyBounded.cbDegreeAtMostStatement, `IUT.Applications.CompactlyBounded),
   (`IUT.CompactlyBounded.genEllTheorem2_1iiStatement, `IUT.Applications.CompactlyBounded),
   (`IUT.ABC.Unconditional.uncondABCRestrictedToStatement, `IUT.ABC.Unconditional),
   (`IUT.HeightExtension.htExtDegreeAtMostAnyFieldStatement, `IUT.Applications.HeightExtension)]

/-- Author statements: constants of type `… → Prop` that state results or claims of other
papers, which the library may assume but never proves outright. Same rule as closed forms,
negations included; as hypotheses they count as assumed registered statements. -/
def authorStatements : List (Name × Name) :=
  [(`IUT.ExplicitEstimates.Thm5_4Claim, `IUT.Applications.ExplicitEstimates),
   (`IUT.ExplicitEstimates.Thm5_3iiRationalClaim, `IUT.Applications.ExplicitEstimates),
   (`IUT.ExplicitEstimates.Lemma5_7Claim, `IUT.Applications.ExplicitEstimates),
   (`IUT.ExplicitEstimates.Cor5_8Statement, `IUT.Applications.ExplicitEstimates),
   (`IUT.Applications.ZhouExplicit.ZhouTheorem32i, `IUT.Applications.ZhouExplicit),
   (`IUT.Applications.ZhouExplicit.ZhouCorollary33, `IUT.Applications.ZhouExplicit),
   (`IUT.Applications.ZhouExplicit.ZhouNLevelBound, `IUT.Applications.ZhouExplicit),
   (`IUT.Applications.ZhouExplicit.ZhouComputedRange, `IUT.Applications.ZhouExplicit),
   (`IUT.ABC.Elementary.SouleTheoremBClaim, `IUT.ABC.Elementary),
   (`IUT.ABC.Elementary.LaniewskiMullerMassBound, `IUT.ABC.Elementary),
   (`IUT.ABC.Elementary.PastenDivisorBound, `IUT.ABC.Elementary),
   (`IUT.ABC.Elementary.DivisorCountPowerBound, `IUT.ABC.Elementary)]

/-- Declarations that conclude a registered statement without assuming one and are accepted:
full name and the hash (`Expr.hash`) of the statement, so that a changed statement under the
same name is reported again. For proved instances of a family that are not open, stated
other than as a negation. Empty: the proved instances of the library are negations. -/
def provedInstances : List (Name × UInt64) := []

/-- All registered constants: name, module, whether a proved negation is reported, and the
word used in reports. -/
def registered : List (Name × Name × Bool × String) :=
  closedForms.map (fun (c, m) => (c, m, true, "form")) ++
  openFamilies.map (fun (c, m) => (c, m, false, "family")) ++
  authorStatements.map (fun (c, m) => (c, m, true, "author statement"))

/-- Whether check 3 unfolds the constant `n` before a comparison: `Not`, and every definition
(not an instance) of the project, that is, of a module whose first component is `IUT`,
`Challenge`, `Solution` or `GateControls`, or of the file being elaborated. Definitions of
Mathlib and the other dependencies stay folded. -/
def unfoldsForCheck3 (env : Environment) (n : Name) : Bool :=
  n == ``Not || (match env.find? n with
    | some (.defnInfo _) =>
      !Meta.isInstanceCore env n &&
        match env.getModuleIdxFor? n with
        | none => true
        | some i => [`IUT, `Challenge, `Solution, `GateControls].contains
            (env.header.moduleNames[i.toNat]!).getRoot
    | _ => false)

/-- `e` with every project definition unfolded (see `unfoldsForCheck3`), recursively. -/
def expandProject (e : Expr) : MetaM Expr := do
  let env ← getEnv
  Meta.deltaExpand e (unfoldsForCheck3 env)

/-- A coarse shape of the weak head normal form of `e` at reducible transparency, to skip
comparisons that cannot succeed: `∀`, or the head constant. -/
def shapeOf (e : Expr) : MetaM Name := do
  let w ← Meta.whnfR e
  if w.isForall then return `«∀»
  return w.getAppFn.constName?.getD `«?»

/-- Whether `e`, already expanded, is equal to `c ?x₁ … ?xₙ` (or to its negation when `neg`)
for fresh metavariables `?xᵢ`, both sides with project definitions unfolded, by `isDefEq` at
the transparency of instances: reducible definitions and instances are unfolded, other
definitions of Mathlib are not. Arithmetic on `ℝ` and similar types therefore fails at once
instead of unfolding the construction of the reals. The metavariable context is restored. -/
def matchesRegistered (e : Expr) (eShape : Name) (c : Name) (neg : Bool) : MetaM Bool := do
  let some ci := (← getEnv).find? c | return false
  let st ← saveState
  let lvls ← ci.levelParams.mapM fun _ => Meta.mkFreshLevelMVar
  let (xs, _, _) ← Meta.forallMetaTelescope (ci.type.instantiateLevelParams ci.levelParams lvls)
  let f := mkAppN (.const c lvls) xs
  let f ← expandProject (if neg then mkNot f else f)
  let r ← if (← shapeOf f) == eShape then
      Meta.withTransparency .instances (Meta.isDefEq e f)
    else pure false
  st.restore
  return r

/-- The first registered statement that `e` states: name, `true` for the negation, and the
kind of the entry. -/
def registeredMatch (reg : List (Name × Name × Bool × String)) (e : Expr) :
    MetaM (Option (Name × Bool × String)) := do
  unless ← Meta.isProp e do return none
  let e ← expandProject e
  let sh ← shapeOf e
  for (c, _, negs, kind) in reg do
    if ← matchesRegistered e sh c false then return some (c, false, kind)
    if negs then
      if ← matchesRegistered e sh c true then return some (c, true, kind)
  return none

/-- Whether `e` mentions a registered constant. -/
def mentionsRegistered (reg : List (Name × Name × Bool × String)) (e : Expr) : Bool :=
  e.getUsedConstants.any fun n => reg.any (·.1 == n)

/-- The parts of a conclusion that check 3 compares: the conclusion itself, the conjuncts of
an `∧`, and each side of an `↔` whose other side mentions no registered constant (after
reducible unfolding of the connective; `fuel` bounds the nesting). -/
def conclusionParts (reg : List (Name × Name × Bool × String)) :
    Nat → Expr → MetaM (Array Expr)
  | 0, e => return #[e]
  | fuel + 1, e => do
    let w ← Meta.whnfR e
    if w.isAppOfArity ``And 2 then
      return #[e] ++ (← conclusionParts reg fuel w.appFn!.appArg!) ++
        (← conclusionParts reg fuel w.appArg!)
    if w.isAppOfArity ``Iff 2 then
      let a := w.appFn!.appArg!
      let b := w.appArg!
      let mut out := #[e]
      unless mentionsRegistered reg b do out := out ++ (← conclusionParts reg fuel a)
      unless mentionsRegistered reg a do out := out ++ (← conclusionParts reg fuel b)
      return out
    return #[e]

/-- Check 3 for one statement `ty`: the first registered statement that a part of a
conclusion of `ty` states, found by stripping the leading `∀` binders one at a time (after
reducible unfolding), with `true` when no binder was stripped (the statement itself). Returns
`none` as soon as a stripped hypothesis mentions a registered constant. -/
def openConclusion (reg : List (Name × Name × Bool × String)) :
    Nat → Expr → Bool → MetaM (Option (Name × Bool × String × Bool))
  | 0, _, _ => return none
  | fuel + 1, e, top => do
    for part in ← conclusionParts reg 4 e do
      if let some (c, neg, kind) ← registeredMatch reg part then
        return some (c, neg, kind, top && part == e)
    let w ← Meta.whnfR e
    unless w.isForall do return none
    Meta.forallBoundedTelescope w (some 1) fun xs body => do
      for x in xs do
        if mentionsRegistered reg (← x.fvarId!.getType) then return none
      if xs.isEmpty then return none
      openConclusion reg fuel body false

/-- Heartbeat budget (in thousands) of one comparison of check 3. -/
def settlesBudget : Nat := 20000

/-- Names that check 6 accepts, by exact full name. Each entry was read.

* `NormalizedLine.measure`, `BDle.trans`, `Capsule.Hom.id`: the suffix is a one-component root
  name of core or Mathlib (`measure`, `trans`, `id`), and the project constant is a structure
  field or a definition or lemma about a project structure that is used with its full name or
  by dot notation. -/
def shadowAllowed : List Name :=
  [`IUT.Countermodels.Comparison.NormalizedLine.measure, `IUT.PaperIV.Corollary2_3.BDle.trans,
   `IUT.PaperI.Capsule.Hom.id]

/-- Whether `n` is a constant of a dependency: stored in an imported module that `pred` does
not accept. Constants of the current file are not foreign. -/
def isForeign (env : Environment) (pred : Name → Bool) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => !pred env.header.moduleNames[i.toNat]!
  | none => false

/-- The namespaces of dependencies whose `open` the source scan accepts in library files (its
list `ALLOWED_OPENS` holds these and namespaces of the library) (check 6). -/
def openedNamespaces : List Name :=
  [`Challenge, `Finset, `MeasureTheory, `MeasureTheory.Measure, `Set, `Classical, `NumberField,
   `Complex, `ComplexConjugate, `Filter, `Topology, `Real, `Pointwise, `ZFSet,
   `IsDedekindDomain, `IsDedekindDomain.HeightOneSpectrum, `WeierstrassCurve, `CategoryTheory,
   `Asymptotics, `Ideal, `nonZeroDivisors, `Opposite]

/-- Whether the last component of `n` is a name that the compiler or the elaborator generates
(`_unsafe_rec`, `match_1`, `proof_2`, `eq_1`, a numeric component, and so on). Only the last
component is tested: a namespace component that starts with `_`, such as `IUT._aux`, is
accepted by the frontend in user declarations, so it is no reason to skip a name. -/
def generatedLast : Name → Bool
  | .str _ s => Name.isInternalDetail (.str .anonymous s)
  | .num _ _ => true
  | .anonymous => true

/-- The last components of the constants that Lean generates for an inductive type or one of
its constructors (recursors, `casesOn`, `noConfusion`, injectivity lemmas, the default
constructor name `mk`, ...). -/
def inductiveAuxiliaries : List String :=
  ["rec", "recOn", "casesOn", "brecOn", "binductionOn", "below", "ibelow", "noConfusion",
   "noConfusionType", "ctorIdx", "ctorElim", "ctorElimType", "inj", "injEq", "sizeOf_spec", "mk"]

/-- Whether `n` (a user-facing name) is a constant generated for an inductive type or a
constructor: its last component is in `inductiveAuxiliaries` and its namespace is an inductive
type or a constructor. -/
def generatedForInductive (env : Environment) (n : Name) : Bool :=
  match n with
  | .str p s => inductiveAuxiliaries.contains s &&
      (match env.find? p with
       | some (.inductInfo _) | some (.ctorInfo _) => true
       | _ => false)
  | _ => false

/-- Whether `n` is stored in a module of the library `IUT` or in the current file. -/
def isLibraryConstant (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => (`IUT).isPrefixOf env.header.moduleNames[i.toNat]!
  | none => true

/-- For check 6: a constant that an identifier written inside the namespaces of `n` could mean
but that now resolves to `n`, with the reason. Write `n = c₁.….cₖ` (the user-facing name for a
private `n`). Two rules, both about constants outside the library `IUT` (dependency constants
and the trusted constants of `Challenge.Defs`, `Challenge` and `Solution`):

* suffix: a constant `c₁.….cⱼ.cᵢ₊₁.….cₖ` with `j ≤ i < k`, that is a proper suffix of `n`
  at the root or below an enclosing namespace of `n`;
* open: when `k ≥ 2` and the namespace `c₁.….cₖ₋₁` is not itself a constant (not a type whose
  members are used by dot notation), a constant `O.cₖ` for `O` in `openedNamespaces`: inside
  that namespace the identifier `cₖ` means `n` whatever is opened.

Generated names are skipped (see `generatedLast` and `generatedForInductive`). Project names
that shadow other project names are not reported. -/
def shadowed? (env : Environment) (n : Name) : Option (Name × String) := Id.run do
  let user := privateToUserName n
  if generatedLast user || generatedForInductive env user || shadowAllowed.contains user then
    return none
  let cs := user.components
  let k := cs.length
  let outside (t : Name) := env.contains t && !isLibraryConstant env t
  for i in [1:k] do
    let suffix := Name.fromComponents (cs.drop i)
    for j in [0:i+1] do
      let target := Name.fromComponents (cs.take j) ++ suffix
      if target != user && outside target then return some (target, "its suffix names")
  if k ≥ 2 && !env.contains (Name.fromComponents (cs.take (k - 1))) then
    let last := Name.fromComponents (cs.drop (k - 1))
    for o in openedNamespaces do
      let target := o ++ last
      if target != user && outside target then
        return some (target, s!"under `open {o}` its last component names")
  return none

/-- The name of the structure or constant at the head of `e`: the head constant of an
application, or the structure of a projection `e.i`. -/
def headName? (e : Expr) : Option Name :=
  match e with
  | .proj s _ _ => some s
  | _ => e.getAppFn.constName?

/-- For check 7: the class of an instance type, and whether the class and every argument head
are foreign, after weak head normalization at the transparency of instance resolution. -/
def instanceClass (env : Environment) (pred : Name → Bool) (type : Expr) :
    MetaM (Option Name × Bool) := do
  Meta.forallTelescopeReducing type fun _ body => do
    let whnfI (e : Expr) : MetaM Expr := Meta.withTransparency .instances (Meta.whnf e)
    let body ← whnfI body
    let some c := headName? body | return (none, false)
    let mut foreign := isForeign env pred c
    for a in body.getAppArgs do
      if let some h := headName? (← whnfI a) then
        unless isForeign env pred h do foreign := false
    return (some c, foreign)

/-- Instances that the library may register (check 7): the full name of the constant and its
class. Each entry was read: `IUT.PaperI.Capsule.fintype` is the field `[fintype : Fintype
index]` of the structure `IUT.PaperI.Capsule`, an instance on the index type of a project
structure. The source scan allows the one command that registers it
(`ALLOWED_INSTANCES`). -/
def instanceAllowed : List (Name × Name) :=
  [(`IUT.PaperI.Capsule.fintype, ``Fintype)]

/-- For check 7: the instance and default instance registrations added by the imported module
`i`, or by the current file for `none`: the instance names, and the default instances with
their class. -/
def registrations (env : Environment) (i? : Option ModuleIdx) :
    Array Name × Array (Name × Name) :=
  let insts : Array (ScopedEnvExtension.Entry Meta.InstanceEntry) := match i? with
    | some i => PersistentEnvExtension.getModuleEntries Meta.instanceExtension.ext env i
    | none => (Meta.instanceExtension.ext.getState env).newEntries.toArray
  let names := insts.filterMap fun
    | .global e => e.globalName?
    | .scoped _ e => e.globalName?
  let defaults : Array Meta.DefaultInstanceEntry := match i? with
    | some i => PersistentEnvExtension.getModuleEntries
        (Meta.defaultInstanceExtension : PersistentEnvExtension _ _ _) env i
    | none => (Meta.defaultInstanceExtension.getEntries env).toArray
  (names, defaults.map fun e => (e.instanceName, e.className))

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
    if let some (target, why) := shadowed? env ci.name then
      let shown := if isPrivateName ci.name then m!"{privateToUserName ci.name} (private)"
        else m!"{ci.name}"
      errors := errors.push m!"{shown}: {why} the constant {target}"
  -- Check 7: instances. The registrations added by the checked modules (and the current file
  -- for the controls), and the checked constants that are instances.
  let mut instNames : Array Name := #[]
  let mut defaults : Array (Name × Name) := #[]
  for i in projModules do
    let (a, d) := registrations env (some (i : ModuleIdx))
    instNames := instNames ++ a
    defaults := defaults ++ d
  if cfg.includeCurrent then
    let (a, d) := registrations env none
    instNames := instNames ++ a
    defaults := defaults ++ d
  for ci in consts do
    if Meta.isInstanceCore env ci.name then instNames := instNames.push ci.name
  let instSet : NameSet := instNames.foldl (·.insert ·) {}
  let commandEnv0 ← getEnv
  let instProblems ← liftCoreM do
    setEnv env
    let mut out : Array MessageData := #[]
    for n in instSet.toList do
      let some ci := env.find? n | out := out.push m!"{n}: registered instance not found"; continue
      let (cls, foreign) ← (instanceClass env cfg.modulePred ci.type).run'
      if foreign then
        out := out.push m!"{n}: instance of a dependency class on dependency arguments only"
      else match instanceAllowed.find? (·.1 == n) with
        | some (_, c) =>
          unless cls == some c do
            out := out.push m!"{n}: allowlisted instance of {c}, but its class is {cls}"
        | none =>
          -- The `SizeOf` instance that Lean generates for every inductive type.
          unless generatedLast (privateToUserName n) && cls == some ``SizeOf do
            out := out.push m!"{n}: instance not in the allowlist instanceAllowed"
    return out
  setEnv commandEnv0
  errors := errors ++ instProblems
  for (n, cls) in defaults do
    errors := errors.push m!"{n}: default instance of {cls} registered by a checked module"
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
  -- Check 3: registered statements.
  let mut resolutions : Array MessageData := #[]
  let present := env
  let reg := registered ++ cfg.extraRegistered
  let mut missing : Array Name := #[]
  for (c, m, _, _) in reg do
    match present.find? c with
    | some (.defnInfo _) => pure ()
    | some _ => errors := errors.push m!"{c} (registered in check 3) is not a definition"
    | none =>
      if (present.getModuleIdx? m).isSome ||
          (cfg.requireRegistered && (← IO.getEnv "CI") == some "true") then
        errors := errors.push m!"{c} (registered in check 3) not found"
      else missing := missing.push c
  unless missing.isEmpty do
    notes := notes.push m!"check 3: registered statements of modules outside the import \
      closure, not compared: {missing.toList}"
  let t30 ← IO.monoMsNow
  let candidates := consts.filter fun ci =>
    ci matches .thmInfo _ || ci matches .defnInfo _ || ci matches .opaqueInfo _ ||
      ci matches .axiomInfo _
  let commandEnv ← getEnv
  let (found, undecided) ← liftCoreM do
    setEnv env
    let mut found : Array (ConstantInfo × Name × Bool × String × Bool) := #[]
    let mut undecided : Array Name := #[]
    for ci in candidates do
      let r ← tryCatchRuntimeEx
        (withCurrHeartbeats <|
          withTheReader Core.Context (fun c => { c with maxHeartbeats := settlesBudget * 1000 })
            (Except.ok <$> (openConclusion reg 32 ci.type true).run'))
        (fun _ => pure (Except.error ()))
      match r with
      | .ok (some cb) => found := found.push (ci, cb)
      | .ok none => pure ()
      | .error _ => undecided := undecided.push ci.name
    return (found, undecided)
  setEnv commandEnv
  for n in undecided do
    errors := errors.push m!"{n}: comparison with the registered statements ran out of its \
      heartbeat budget"
  notes := notes.push m!"conjecture check: {candidates.size} statements compared up to \
    unfolding with {reg.length - missing.size} registered statements, {found.size} \
    matches, {undecided.size} undecided, {(← IO.monoMsNow) - t30} ms"
  for (ci, conj, neg, kind, top) in found do
    if provedInstances.contains (ci.name, ci.type.hash) then continue
    if provedInstances.any (·.1 == ci.name) then
      errors := errors.push m!"{ci.name}: listed in provedInstances with another statement hash \
        ({ci.type.hash})"
      continue
    let what := if neg then s!"the negation of {conj}" else toString conj
    if ci.name matches .str _ "abcConjecture" then
      let axs ← collectAxioms ci.name
      resolutions := resolutions.push
        m!"!!! RESOLUTION: {ci.name} proves {what}; axioms: {axs.toList} !!!"
    else if top && kind == "form" then
      errors := errors.push m!"{ci.name}: states {what} but is not named abcConjecture"
    else
      errors := errors.push m!"{ci.name}: concludes {what} (registered {kind}) without a \
        hypothesis that mentions a registered statement (statement hash {ci.type.hash})"
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
