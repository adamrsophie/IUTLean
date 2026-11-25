#!/usr/bin/env python3
# Untrusted helper script for the IUT Lean library.
# Fingerprints of the trusted definitions Challenge/Defs.lean: the SHA-256 of the source file
# and, for every constant stored in the module Challenge.Defs, the SHA-256 of a structural dump
# of its elaborated type and of its elaborated value (printed by the Lean helper
# scripts/Controls/Fingerprints.lean). The record is data/challenge_fingerprints.json.
# Run from the repository root after `lake build Challenge.Defs`:
#     python3 -I scripts/Controls/fingerprints.py --write   (record the current fingerprints)
#     python3 -I scripts/Controls/fingerprints.py --check   (exit 1 if anything changed)
# A change to a trusted definition must be reviewed by hand and then recorded with --write.
# Requires: Python 3 standard library and the project's Lean toolchain (lake on PATH).
# Exit status: 0 when the record matches (or was written), 1 on a difference, 2 on a usage
# error or a failure of the Lean helper. License: GPL 3, same as the repository.

import hashlib
import json
import subprocess
import sys

SOURCE = 'Challenge/Defs.lean'
HELPER = 'scripts/Controls/Fingerprints.lean'
RECORD = 'data/challenge_fingerprints.json'


def sha(data):
    return hashlib.sha256(data.encode('utf-8') if isinstance(data, str) else data).hexdigest()


def current():
    with open(SOURCE, 'rb') as f:
        source = sha(f.read())
    run = subprocess.run(['lake', 'env', 'lean', HELPER], capture_output=True, text=True)
    if run.returncode != 0:
        print(run.stdout + run.stderr)
        print(f'fingerprints: {HELPER} failed with exit status {run.returncode}')
        sys.exit(2)
    decls, name = {}, None
    for line in run.stdout.splitlines():
        key, _, rest = line.partition(' ')
        if key == 'FP-NAME':
            name = rest
            decls[name] = {}
        elif key == 'FP-TYPE' and name is not None:
            decls[name]['type'] = sha(rest)
        elif key == 'FP-VALUE' and name is not None:
            decls[name]['value'] = sha(rest)
    if not decls or any(set(d) != {'type', 'value'} for d in decls.values()):
        print('fingerprints: unexpected output of the Lean helper')
        print(run.stdout[:2000])
        sys.exit(2)
    return {'source_file': SOURCE, 'source_sha256': source, 'declarations': decls}


def main(argv):
    if argv not in (['--write'], ['--check']):
        print('usage: fingerprints.py --write | --check')
        return 2
    now = current()
    if argv == ['--write']:
        with open(RECORD, 'w', encoding='utf-8') as f:
            json.dump(now, f, indent=2, sort_keys=True)
            f.write('\n')
        print(f'fingerprints written: {len(now["declarations"])} declarations to {RECORD}')
        return 0
    try:
        with open(RECORD, encoding='utf-8') as f:
            old = json.load(f)
    except (OSError, ValueError) as exc:
        print(f'fingerprints: cannot read {RECORD}: {exc}')
        return 1
    problems = []
    if old.get('source_sha256') != now['source_sha256']:
        problems.append(f'{SOURCE}: source hash changed')
    olds, news = old.get('declarations', {}), now['declarations']
    for n in sorted(set(olds) | set(news)):
        if n not in news:
            problems.append(f'{n}: recorded but no longer declared')
        elif n not in olds:
            problems.append(f'{n}: declared but not recorded')
        else:
            for part in ('type', 'value'):
                if olds[n].get(part) != news[n][part]:
                    problems.append(f'{n}: elaborated {part} changed')
    for p in problems:
        print(p)
    if problems:
        print(f'fingerprint check FAILED: {len(problems)} differences')
        return 1
    print(f'fingerprint check OK: {len(news)} declarations of {SOURCE}')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
