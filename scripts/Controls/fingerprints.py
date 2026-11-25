#!/usr/bin/env python3
# Untrusted helper script for the IUT Lean library.
# Fingerprints of the trust set, recorded in data/challenge_fingerprints.json:
#   * for every constant stored in the module Challenge.Defs (the trusted definitions), the
#     SHA-256 of a structural dump of its elaborated type and of its elaborated value;
#   * for every constant stored in the module Challenge (Challenge.lean, the challenge
#     statements of lake comparator), the SHA-256 of the dump of its elaborated type, and the
#     list of its theorems, which must be exactly the theorem_names of comparator.json;
#   * the SHA-256 of each file of trust_files(): the challenge, the comparator configuration,
#     the gate and its controls, the scripts of this folder, scripts/gen_root.py (the
#     continuous integration runs it before the build), the build configuration, the workflow
#     and the code owners file.
# The dumps are printed by the Lean helper scripts/Controls/Fingerprints.lean, which imports
# the module Challenge; Challenge.lean is not a default target, so build it first.
# Run from the repository root after `lake build Challenge`:
#     python3 -I scripts/Controls/fingerprints.py --write   (record the current fingerprints)
#     python3 -I scripts/Controls/fingerprints.py --check   (exit 1 if anything changed)
# A change of the record must be approved separately by a person (see scripts/README.md);
# --write is never run by the continuous integration.
# Requires: Python 3 standard library and the project's Lean toolchain (lake on PATH).
# Exit status: 0 when the record matches (or was written), 1 on a difference, 2 on a usage
# error or a failure of the Lean helper. License: GPL 3, same as the repository.

import glob
import hashlib
import json
import subprocess
import sys

HELPER = 'scripts/Controls/Fingerprints.lean'
RECORD = 'data/challenge_fingerprints.json'
COMPARATOR = 'comparator.json'
MODULES = ('Challenge.Defs', 'Challenge')


def trust_files():
    fixed = ['Challenge.lean', 'Challenge/Defs.lean', 'comparator.json', 'AxiomGate.lean',
             'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
             '.github/workflows/axiom-gate.yml', '.github/CODEOWNERS', 'scripts/gen_root.py']
    return sorted(set(fixed + glob.glob('scripts/Controls/*') + glob.glob('GateControls/*')))


def sha(data):
    return hashlib.sha256(data.encode('utf-8') if isinstance(data, str) else data).hexdigest()


def file_sha(path):
    try:
        with open(path, 'rb') as f:
            return sha(f.read())
    except OSError:
        return None


def current():
    run = subprocess.run(['lake', 'env', 'lean', HELPER], capture_output=True, text=True)
    if run.returncode != 0:
        print(run.stdout + run.stderr)
        print(f'fingerprints: {HELPER} failed with exit status {run.returncode} '
              f'(was `lake build Challenge` run?)')
        sys.exit(2)
    mods, cur = {m: {} for m in MODULES}, None
    theorems = []
    for line in run.stdout.splitlines():
        key, _, rest = line.partition(' ')
        if key == 'FP-NAME':
            cur = {'name': rest}
        elif cur is None:
            continue
        elif key == 'FP-MODULE':
            cur['module'] = rest
        elif key == 'FP-KIND':
            cur['kind'] = rest
        elif key == 'FP-TYPE':
            cur['type'] = sha(rest)
        elif key == 'FP-VALUE':
            entry = {'type': cur['type']}
            if cur.get('module') == 'Challenge.Defs':
                entry['value'] = sha(rest)
            elif cur.get('kind') == 'theorem':
                theorems.append(cur['name'])
            if cur.get('module') not in mods:
                print(f'fingerprints: unexpected module in the helper output: {cur}')
                sys.exit(2)
            mods[cur['module']][cur['name']] = entry
            cur = None
    if not all(mods.values()):
        print('fingerprints: unexpected output of the Lean helper')
        print(run.stdout[:2000])
        sys.exit(2)
    return {'modules': mods, 'challenge_theorems': sorted(theorems),
            'files': {p: file_sha(p) for p in trust_files()}}


def comparator_problems(theorems):
    try:
        with open(COMPARATOR, encoding='utf-8') as f:
            names = json.load(f).get('theorem_names', [])
    except (OSError, ValueError) as exc:
        return [f'{COMPARATOR}: cannot read: {exc}']
    out = [f'{COMPARATOR}: {n} is listed but is not a theorem of Challenge.lean'
           for n in sorted(set(names) - set(theorems))]
    out += [f'{COMPARATOR}: theorem {n} of Challenge.lean is not listed'
            for n in sorted(set(theorems) - set(names))]
    if len(names) != len(set(names)):
        out.append(f'{COMPARATOR}: a theorem name is listed twice')
    return out


def main(argv):
    if argv not in (['--write'], ['--check']):
        print('usage: fingerprints.py --write | --check')
        return 2
    now = current()
    problems = comparator_problems(now['challenge_theorems'])
    if argv == ['--write']:
        for p in problems:
            print(p)
        if problems:
            print('fingerprints: not written, comparator.json does not match Challenge.lean')
            return 1
        with open(RECORD, 'w', encoding='utf-8') as f:
            json.dump(now, f, indent=2, sort_keys=True)
            f.write('\n')
        print(f'fingerprints written: {sum(map(len, now["modules"].values()))} constants, '
              f'{len(now["files"])} files to {RECORD}')
        return 0
    try:
        with open(RECORD, encoding='utf-8') as f:
            old = json.load(f)
    except (OSError, ValueError) as exc:
        print(f'fingerprints: cannot read {RECORD}: {exc}')
        return 1
    for m in MODULES:
        olds, news = old.get('modules', {}).get(m, {}), now['modules'][m]
        for n in sorted(set(olds) | set(news)):
            if n not in news:
                problems.append(f'{m}: {n} recorded but no longer declared')
            elif n not in olds:
                problems.append(f'{m}: {n} declared but not recorded')
            else:
                for part in sorted(set(olds[n]) | set(news[n])):
                    if olds[n].get(part) != news[n].get(part):
                        problems.append(f'{m}: {n}: elaborated {part} changed')
    if old.get('challenge_theorems') != now['challenge_theorems']:
        problems.append('the list of theorems of Challenge.lean changed')
    oldf, newf = old.get('files', {}), now['files']
    for p in sorted(set(oldf) | set(newf)):
        if oldf.get(p) != newf.get(p):
            what = ('missing' if newf.get(p) is None else 'not recorded' if p not in oldf
                    else 'no longer recorded' if p not in newf else 'changed')
            problems.append(f'{p}: file {what}')
    for p in problems:
        print(p)
    if problems:
        print(f'fingerprint check FAILED: {len(problems)} differences')
        return 1
    print(f'fingerprint check OK: {sum(map(len, now["modules"].values()))} constants '
          f'of {", ".join(MODULES)}, {len(now["challenge_theorems"])} challenge theorems, '
          f'{len(newf)} files')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
