#!/usr/bin/env python3
# Writes the root module IUT.lean: one import per file IUT/**/*.lean outside IUT/Experimental/,
# sorted by module name, and nothing else.
# Run from the repository root:
#     python3 -I scripts/gen_root.py                 (rewrite IUT.lean)
#     python3 -I scripts/gen_root.py --check         (exit 1 if IUT.lean differs)
#     python3 -I scripts/gen_root.py --output FILE   (write to FILE instead of IUT.lean)
# Requires: Python 3 standard library. License: GPL 3, same as the repository.

import argparse
import os
import sys


def root_text():
    mods = []
    for root, dirs, names in os.walk('IUT'):
        if os.path.normpath(root) == os.path.join('IUT', 'Experimental'):
            dirs[:] = []
            continue
        for x in names:
            if x.endswith('.lean'):
                mods.append(os.path.join(root, x)[:-5].replace(os.sep, '.'))
    return ''.join(f'import {m}\n' for m in sorted(mods))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--check', action='store_true')
    ap.add_argument('--output', default='IUT.lean')
    args = ap.parse_args()
    if not os.path.isdir('IUT'):
        print('run from the repository root')
        return 2
    text = root_text()
    if args.check:
        try:
            with open(args.output, encoding='utf-8') as f:
                current = f.read()
        except FileNotFoundError:
            current = None
        if current != text:
            print(f'{args.output} differs from the generated root; run scripts/gen_root.py')
            return 1
        print(f'{args.output} is up to date: {text.count(chr(10))} imports')
        return 0
    with open(args.output, 'w', encoding='utf-8') as f:
        f.write(text)
    print(f'wrote {args.output}: {text.count(chr(10))} imports')
    return 0


if __name__ == '__main__':
    sys.exit(main())
