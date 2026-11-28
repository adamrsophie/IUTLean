#!/bin/sh
# Runs the axiom gate controls. From the repository root, after `lake build`:
#
#     sh GateControls/run.sh [gate file]
#
# The gate file defaults to AxiomGate.lean. It is copied to a temporary directory and compiled
# there as the module AxiomGateLib (compiling it also runs the gate on the library), together
# with GateControls/GateProbe.lean as the module IUT.Experimental.GateProbe, so the controls
# can import them; nothing is written inside the repository or under .lake.
# The controls mention the words axiom, sorry and unsafe on purpose; the source scan does not
# read GateControls/.
#
# Passes only if the clean control exits 0 with the summary line, and each rejecting control
# exits with status 1 (a normal Lean error exit), reports the expected number of problems, and
# prints its intended diagnostic line (and, for NamedConditional, no resolution line). The
# clean controls ResolutionModel and DeepConclusionsClean must also print their resolution
# line and the length of their binder walk. Any other status (a crash or a signal), a panic, or a
# missing diagnostic fails the runner. Also runs the gate on the library with a tracked file
# list that names a file the root does not import (must fail and name it), the source scan
# on its controls GateControls/SourceScan.lean, GateControls/SourceScanLakefile.toml and
# GateControls/SourceScan.lake-manifest.json (every construct reported, nothing else), the
# scan's rule for tracked tooling files on a list of paths, and its rule for the allowed instance
# line on a scratch file. The controls
# VojtaRestated and ExponentThree import IUT.Applications.ABCSpecialization and
# IUT.ABC.Variants, which `lake build` builds.

set -u

gate=${1:-AxiomGate.lean}
dir=$(dirname "$0")
tmp=$(mktemp -d) || exit 2
trap 'rm -rf "$tmp"' EXIT INT TERM
mkdir -p "$tmp/src/IUT/Experimental" "$tmp/lib" "$tmp/probe"
cp "$gate" "$tmp/src/AxiomGateLib.lean" || exit 2
cp "$dir/GateProbe.lean" "$tmp/src/IUT/Experimental/GateProbe.lean" || exit 2
lean_path=$(lake env printenv LEAN_PATH) || exit 2

# Lean looks up every module IUT.* in the first search path folder that has a folder IUT, so
# the probe goes into a folder of its own that also holds a copy of the compiled library.
cp -R .lake/build/lib/lean/IUT .lake/build/lib/lean/IUT.olean "$tmp/probe/" || exit 2
mkdir -p "$tmp/probe/IUT/Experimental"
compile() {
  if ! lake env lean -R "$tmp/src" -o "$1" "$2" > "$tmp/build.log" 2>&1; then
    echo "FAIL: $2 (copy of the gate or of a control module) does not compile"
    cat "$tmp/build.log"
    exit 1
  fi
}
compile "$tmp/lib/AxiomGateLib.olean" "$tmp/src/AxiomGateLib.lean"
compile "$tmp/probe/IUT/Experimental/GateProbe.olean" "$tmp/src/IUT/Experimental/GateProbe.lean"

failures=0
total=0

# report NAME OK LOG: prints the verdict and counts a failure
report() {
  total=$((total + 1))
  if [ "$2" -eq 1 ]; then
    echo "ok   $1"
  else
    sed 's/^/     | /' "$3" | head -n 40
    failures=$((failures + 1))
  fi
}

# expect NAME STATUS LINE...: compiles GateControls/NAME.lean against the temporary modules
# (and the probe folder when PROBE is set) and checks the exit status, the absence of a
# panic, and each line. A LINE of the form 'absent:TEXT' requires that TEXT does not occur.
expect() {
  name=$1; want=$2; shift 2
  log="$tmp/$name.log"
  lake env env LEAN_PATH="${PROBE:+$tmp/probe:}$tmp/lib:$lean_path" lean "$dir/$name.lean" \
    > "$log" 2>&1
  status=$?
  ok=1
  if [ "$status" -ne "$want" ]; then
    echo "FAIL $name: exit status $status, expected $want"; ok=0
  fi
  if grep -q 'PANIC' "$log"; then echo "FAIL $name: panic"; ok=0; fi
  for line in "$@"; do
    case $line in
      absent:*)
        if grep -qF -- "${line#absent:}" "$log"; then
          echo "FAIL $name: unexpected line: ${line#absent:}"; ok=0
        fi ;;
      *) grep -qF -- "$line" "$log" || { echo "FAIL $name: missing line: $line"; ok=0; } ;;
    esac
  done
  report "$name (exit $status)" "$ok" "$log"
}

# check NAME STATUS PROBLEMS DIAGNOSTIC...
# PROBLEMS is the expected problem count of a rejection, or "-" for a clean control.
check() {
  name=$1; want=$2; problems=$3; shift 3
  if [ "$problems" = "-" ]; then
    expect "$name" "$want" 'axiom gate OK: ' "$@"
  else
    expect "$name" "$want" "axiom gate FAILED ($problems problems):" "$@"
  fi
}

check Clean 0 - \
  'GateControls.sumTo._unsafe_rec (base GateControls.sumTo' \
  'GateControls.halve._unsafe_rec (base GateControls.halve'
check Sorry 1 1 \
  'GateControls.withSorry: depends on [sorryAx]'
check ForbiddenAxiom 1 3 \
  'GateControls.usesBadAxiom: depends on [GateControls.badAxiom]'
check NativeDecide 1 3 \
  'GateControls.byNative: depends on [GateControls.byNative._native.native_decide.ax_'
check RenamedConjecture 1 11 \
  'GateControls.restated: states Challenge.ABC but is not named abcConjecture' \
  'GateControls.unfolded: states Challenge.ABC but is not named abcConjecture' \
  'GateControls.viaLog: states Challenge.ABCLog but is not named abcConjecture' \
  'GateControls.refuted: states the negation of Challenge.ABCFinite but is not named abcConjecture' \
  '!!! RESOLUTION: GateControls.abcConjecture proves Challenge.ABC; axioms:'
check EquivalentForm 1 8 \
  'GateControls.qualityBound: states IUT.ABC.FormalConjectures.qualityVariant but is not named abcConjecture' \
  'GateControls.finiteTriples: states IUT.ABC.FormalConjectures.abc but is not named abcConjecture' \
  'GateControls.noConstant: states the negation of IUT.ABC.FormalConjectures.ltConstantMul but is not named abcConjecture'
check Shadowing 1 2 \
  'GateControls.Real.log: its suffix names the constant Real.log' \
  'GateControls.fakeLE: instance of a dependency class on dependency arguments only'
check PrivateShadowing 1 1 \
  'GateControls.Nat.succ (private): its suffix names the constant Nat.succ'
check TrustedNames 1 3 \
  'GateControls.Challenge.ABC: its suffix names the constant Challenge.ABC' \
  'GateControls.log: under `open ' \
  'GateControls._aux.Real.log: its suffix names the constant Real.log'
check ForeignInstances 1 6 \
  'GateControls.counterInhabited: instance of a dependency class on dependency arguments only' \
  'GateControls.realRel: instance of a dependency class on dependency arguments only' \
  'GateControls.Capsule.fintype: instance of a dependency class on dependency arguments only' \
  'GateControls.natDefault: default instance of Inhabited registered by a checked module' \
  'instOfNat: default instance of OfNat registered by a checked module'
check VojtaRestated 1 9 \
  'GateControls.heightConductorBound: states IUT.ABCSpecialization.VojtaLineMinusThreePointsRational but is not named abcConjecture' \
  'GateControls.rationalPointBound: states IUT.ABCSpecialization.VojtaLineMinusThreePointsRational but is not named abcConjecture' \
  'GateControls.noVojta: states the negation of IUT.ABCSpecialization.VojtaLineMinusThreePointsRational but is not named abcConjecture'
check OpenStatements 1 10 \
  'GateControls.viaAlias: states GateControls.ABCIntModel but is not named abcConjecture' \
  'GateControls.viaBinders: concludes GateControls.ABCIntModel (registered form) without a hypothesis that mentions a registered statement' \
  'GateControls.viaAnd: concludes GateControls.ABCIntModel (registered form)' \
  'GateControls.viaIff: concludes GateControls.ABCIntModel (registered form)' \
  'GateControls.exp24: concludes GateControls.ExponentModel (registered family)' \
  'GateControls.expAll: concludes GateControls.ExponentModel (registered family)' \
  'GateControls.zhou: concludes GateControls.ZhouModel (registered author statement)' \
  'GateControls.libraryInt: concludes IUT.ABC.Variants.ABCInt (registered form)' \
  'GateControls.libraryExp: concludes IUT.ABC.Variants.ABCWithExponent (registered family)' \
  'GateControls.conditionalABC: concludes Challenge.ABC (registered form) without a hypothesis that mentions a registered statement'
check OpenStatementsClean 0 - \
  'matches, 0 undecided'
check ExponentThree 0 - \
  '0 matches, 0 undecided'
check NamedConditional 1 5 \
  'GateControls.abcConjecture: named abcConjecture, but its statement has hypotheses or other parts around Challenge.ABC (registered form)' \
  'GateControls.Refutation.abcConjecture: named abcConjecture, but its statement has hypotheses or other parts around the negation of Challenge.ABC (registered form)' \
  'GateControls.Family.abcConjecture: named abcConjecture, but its statement is GateControls.ExponentModel, a registered family, not a closed form' \
  'GateControls.Conditional.abcConjecture: named abcConjecture, but its statement is not a registered closed form' \
  'GateControls.Plain.abcConjecture: named abcConjecture, but its statement is not a registered closed form' \
  'absent:!!! RESOLUTION'
check DeepConclusions 1 3 \
  'GateControls.deepBinders: concludes Challenge.ABC (registered form) without a hypothesis that mentions a registered statement' \
  'GateControls.nestedAnd: concludes Challenge.ABC (registered form)' \
  'GateControls.nestedIff: concludes Challenge.ABC (registered form)'
check DeepConclusionsClean 0 - \
  '0 matches, 0 undecided, 0 incomplete; longest binder walk 40 binders, deepest split of ∧ and ↔ 6'
check ResolutionModel 0 - \
  '!!! RESOLUTION: GateControls.abcConjecture proves GateControls.ABCIntModel; axioms: []'
check WalkFuel 1 2 \
  'GateControls.fiveBinders: inspection by check 3 incomplete: the binder walk ran out of fuel after 4 binders' \
  'GateControls.nestedFive: inspection by check 3 incomplete: the split of ∧ and ↔ after 0 binders ran out of fuel'
PROBE=1 check ExperimentalImport 1 1 \
  'module IUT.Experimental.GateProbe is experimental and must not be in the import closure'

# Source coverage: a tracked list with a file that the root does not import must fail.
log="$tmp/coverage.log"
{ git ls-files -- IUT.lean IUT; echo IUT/GateExtra.lean; } > "$tmp/tracked.txt"
AXIOM_GATE_TRACKED_FILES="$tmp/tracked.txt" lake env lean "$gate" > "$log" 2>&1
status=$?
ok=1
[ "$status" -eq 1 ] || { echo "FAIL coverage: exit status $status, expected 1"; ok=0; }
for line in 'axiom gate FAILED (1 problems):' \
  'source coverage: IUT.GateExtra is tracked but not imported by IUT'; do
  grep -qF -- "$line" "$log" || { echo "FAIL coverage: missing line: $line"; ok=0; }
done
report "source coverage with an extra tracked file (exit $status)" "$ok" "$log"

# The source scan must report each construct of its control and nothing else.
log="$tmp/scan.log"
python3 -I scripts/Controls/source_scan.py "$dir/SourceScan.lean" "$dir/SourceScanLakefile.toml" \
  "$dir/SourceScan.lake-manifest.json" \
  > "$log" 2>&1
status=$?
ok=1
[ "$status" -eq 1 ] || { echo "FAIL source scan: exit status $status, expected 1"; ok=0; }
while IFS= read -r line; do
  grep -qF -- "$line" "$log" || { echo "FAIL source scan: missing line: $line"; ok=0; }
done < "$dir/SourceScan.expected"
[ "$(grep -c ': ' "$log")" -eq "$(grep -c ': ' "$dir/SourceScan.expected")" ] ||
  { echo "FAIL source scan: other findings than the expected ones"; ok=0; }
report "source scan of its controls (exit $status)" "$ok" "$log"

# Tooling exemptions are exact paths: an unlisted Lean file under scripts/ or GateControls/
# is reported, the listed ones are not.
log="$tmp/tracked-scan.log"
python3 -I -c '
import sys
sys.path.insert(0, "scripts/Controls")
import source_scan as s
tracked = ["AxiomGate.lean", "GateControls/Clean.lean", "scripts/LeanDeclarations.lean",
           "scripts/Controls/Fingerprints.lean", "scripts/Unused.lean", "GateControls/Unused.lean",
           "scripts/x/Evil.lean", "IUT.lean"]
for path, label in s.tracked_problems(["IUT.lean"], tracked):
    print(f"{path}: {label}")
' > "$log" 2>&1
ok=1
for line in 'scripts/Unused.lean: tracked Lean file outside every checked root' \
  'GateControls/Unused.lean: tracked Lean file outside every checked root' \
  'scripts/x/Evil.lean: tracked Lean file outside every checked root'; do
  grep -qF -- "$line" "$log" || { echo "FAIL tracked files: missing line: $line"; ok=0; }
done
[ "$(grep -c ': ' "$log")" -eq 3 ] || { echo "FAIL tracked files: other findings"; ok=0; }
report "tracked tooling files by exact path" "$ok" "$log"

# The allowed instance line may occur only once in its file.
log="$tmp/instance-scan.log"
mkdir -p "$tmp/scanroot/IUT/PaperI"
printf 'attribute [instance] Capsule.fintype\nattribute [instance] Capsule.fintype\n' \
  > "$tmp/scanroot/IUT/PaperI/PolyMorphism.lean"
root=$(pwd)
(cd "$tmp/scanroot" && python3 -I "$root/scripts/Controls/source_scan.py" \
  IUT/PaperI/PolyMorphism.lean) > "$log" 2>&1
ok=1
for line in 'IUT/PaperI/PolyMorphism.lean:1: allowed instance line repeated' \
  'IUT/PaperI/PolyMorphism.lean:2: allowed instance line repeated' \
  'source scan FAILED: 2 findings'; do
  grep -qF -- "$line" "$log" || { echo "FAIL repeated instance line: missing line: $line"; ok=0; }
done
report "allowed instance line repeated" "$ok" "$log"


if [ "$failures" -ne 0 ]; then
  echo "gate controls FAILED: $failures of $total"
  exit 1
fi
echo "gate controls OK: $total of $total"
