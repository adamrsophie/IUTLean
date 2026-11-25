#!/usr/bin/env python3
# Untrusted helper script for the IUT Lean library.
# Source scan of the library files for constructs that can change what a file means or let a
# declaration bypass the kernel, which AxiomGate.lean cannot see in the compiled environment:
# debug options (debug.skipKernelTC), commands that run code at elaboration time (run_cmd,
# run_meta, run_elab, run_tac, by_elab, #eval, initialize, simprocs), new syntax or elaborators
# (syntax, macro, elab, notation and the mixfix commands, elaborator and initialization
# attributes), local or scoped instances, and set_option with an option outside
# ALLOWED_OPTIONS (exactly the options the library uses, none at present).
# It also reports, as a direct syntactic search next to the environment check of
# AxiomGate.lean, the words sorry, admit, sorryAx, axiom, opaque, unsafe, partial,
# native_decide, implemented_by and extern. sorry and admit are allowed only in Challenge.lean
# and in IUT/Experimental/**.lean; everything else applies there too.
# Instances: the library declares none, so every instance command, instance attribute
# (attribute [instance], @[instance]) and deriving clause is reported. The scan cannot tell a
# lexical instance on a project type from one on a foreign type such as LE on the reals;
# check 7 of AxiomGate.lean makes that distinction in the compiled environment. Instances that
# were read and accepted are listed in ALLOWED_INSTANCES by their source line.
# Imports: no file outside IUT/Experimental/ may import IUT.Experimental or IUT.Experimental.*;
# Challenge.lean and Challenge/**.lean may import only Mathlib and Challenge.*.
# It also rejects build options in lakefile.toml that pass options or arguments to Lean, and
# compares the decoded lakefile with the recorded configuration LAKEFILE (exact require set
# with name, URL and revision; exact library names and keys, so no srcDir, roots or globs
# beyond the recorded ones). In the default form, on the whole tree, it also rejects: a file
# lakefile.lean; a lake-manifest.json whose packages differ from the recorded list MANIFEST
# (name, URL, revision); every file IUT/**.lean outside IUT/Experimental/ that the root file
# IUT.lean does not import directly, and every import of the root file without a file; every
# file under Solution/ and every file under Challenge/ other than Challenge/Defs.lean (the
# gate checks only the modules Solution and Challenge.Defs); and every tracked .lean file
# (git ls-files) outside the scanned roots and the tooling files of TOOLING.
# Comments, docstrings, string literals (raw strings included) and quoted identifiers «...» are
# removed before ordinary token matching; attribute matching also preserves quoted names.
# The match runs on the whole text, so a construct in the middle of a line or after a line
# break is found too. The scan is lexical: it does not parse Lean, so it can report a construct
# that the parser would read differently (fail closed), and it trusts the rules above for where
# comments and strings end.
# Run from the repository root:
#     python3 -I scripts/Controls/source_scan.py                 (IUT.lean, IUT/**.lean,
#                                       Challenge.lean, Challenge/**.lean, Solution.lean,
#                                       Solution/**.lean, lakefile.toml, lake-manifest.json)
#     python3 -I scripts/Controls/source_scan.py FILE [FILE ...] (the given files only; a file
#                                       ending in .toml is scanned as a lakefile, one ending in
#                                       lake-manifest.json as a manifest; the rules for a
#                                       file depend on its path as given, relative to the root)
# Prints one line per finding, "path:line: construct", then a summary line.
# Policy: bang-prefixed string syntax (s!, m!, or another such prefix) is forbidden in library
# source because embedded expressions may execute elaborator code. This is a conservative
# restriction, not a complete Lean parser. Quoted attribute names are checked as identifiers.
# TOML option keys are checked after decoding, including Unicode escapes.
# Adapted from the source scan of the OddPerfectNumber project by the same author.
# Requires: Python 3.11+ standard library. Running time: about a second.
# Exit status: 0 when nothing is found, 1 when something is found, 2 for a usage error.
# License: GPL 3, same as the repository.

import json
import os
import re
import subprocess
import sys
import tomllib

# The options the library sets. It sets none; add an option here only when a library file
# needs it, and only a limit of elaboration or a linter switch.
ALLOWED_OPTIONS = set()

# Placeholders and trust escapes, matched as whole tokens. PLACEHOLDERS are allowed in the
# files that placeholder_allowed accepts.
PLACEHOLDERS = {'sorry', 'admit'}
ESCAPES = {'axiom', 'opaque', 'unsafe', 'partial', 'native_decide', 'implemented_by', 'extern',
           'sorryAx'}

# The decoded lakefile.toml as it is recorded. A change of the build configuration changes
# this constant too, in the same change, so that it is seen.
MATHLIB_URL = 'https://github.com/leanprover-community/mathlib4.git'
LAKEFILE = {
    'name': 'IUT', 'version': '0.1.0', 'defaultTargets': ['IUT', 'Solution'],
    'require': [{'name': 'mathlib', 'git': MATHLIB_URL,
                 'rev': 'fc4f59e577feb1a4956671bc04ac18aaaf8cd842'}],
    'lean_lib': [{'name': 'IUT'}, {'name': 'Challenge'}, {'name': 'Solution'},
                 {'name': 'IUTExperimental', 'roots': [], 'globs': ['IUT.Experimental.+']}],
}

# The packages of lake-manifest.json: (name, URL, revision).
MANIFEST = [
    ('mathlib', MATHLIB_URL, 'fc4f59e577feb1a4956671bc04ac18aaaf8cd842'),
    ('plausible', 'https://github.com/leanprover-community/plausible',
     '054b228ce0ac61d767c6e71ba73a24728f191b72'),
    ('LeanSearchClient', 'https://github.com/leanprover-community/LeanSearchClient',
     '4fb58e749ef3fc0395fe274f6cab70c2ea85f1c9'),
    ('importGraph', 'https://github.com/leanprover-community/import-graph',
     '8370c640afcd1cc3fb1cb9bf1560cc66eafee5e0'),
    ('proofwidgets', 'https://github.com/leanprover-community/ProofWidgets4',
     '2f0f3520daeac2d9310ff25b7a877a0e5cdaa203'),
    ('aesop', 'https://github.com/leanprover-community/aesop',
     '66ff77cf0c4c898799e4b94d14db55f7a02d0c5a'),
    ('Qq', 'https://github.com/leanprover-community/quote4',
     'ff055a2fcc835935e0ae607339b455a5f5896b4b'),
    ('batteries', 'https://github.com/leanprover-community/batteries',
     'b4b25a3886a16daacaf6615c2eea7170a6e8f458'),
    ('Cli', 'https://github.com/leanprover/lean4-cli', '50810f72af7618bee62fe9800dc26e806c188703'),
]

# Instance commands that were read and accepted: (path, the whole source line). Each is an
# instance on a project type; check 7 of AxiomGate.lean also checks every instance.
ALLOWED_INSTANCES = {
    ('IUT/PaperI/PolyMorphism.lean', 'attribute [instance] Capsule.fintype'),
}

# Tracked Lean files that are tooling, not proof sources: no default target contains them and
# nothing in the library imports them. Paths, or folders ending in a slash.
TOOLING = ['AxiomGate.lean', 'GateControls/', 'scripts/']


def norm(path):
    return os.path.normpath(path).replace(os.sep, '/')


def is_experimental(path):
    return norm(path).startswith('IUT/Experimental/')


def placeholder_allowed(path):
    return norm(path) == 'Challenge.lean' or is_experimental(path)


def is_challenge(path):
    p = norm(path)
    return p == 'Challenge.lean' or p.startswith('Challenge/')

# Characters of Lean identifiers (ASCII letters, digits, _ ' ! ? and the dot of qualified names,
# Greek and Coptic, letterlike symbols, mathematical script letters, sub- and superscripted
# letters and digits as Lean allows them), so that a keyword glued to another symbol is
# still found.
IDENT_CHAR = (r"[A-Za-z0-9_.'!?\u0370-\u03ff\u1f00-\u1ffe\u2100-\u214f\u2080-\u209c"
              r"\u1d62-\u1d6a\U0001d49c-\U0001d59f]")


# Commands that run code at elaboration time or add syntax, matched as whole tokens.
KEYWORDS = {
    'run_cmd', 'run_meta', 'run_elab', '#eval', '#eval!', 'initialize', 'builtin_initialize',
    'syntax', 'declare_syntax_cat', 'macro', 'macro_rules', 'elab', 'elab_rules',
    'notation', 'infix', 'infixl', 'infixr', 'prefix', 'postfix', 'run_tac', 'by_elab',
    'simproc', 'dsimproc', 'simproc_decl', 'dsimproc_decl', 'notation3', 'binder_predicate',
}

TOKEN = re.compile('#?' + IDENT_CHAR + '+')
INTERPOLATION_PREFIX = re.compile('(' + IDENT_CHAR + r'+!)\s*$')

# (label, pattern) on the text without comments and strings.
CONSTRUCTS = [
    ('attribute that runs code', r'(?:@\[|\battribute\s*\[)[^\]]*(?<!' + IDENT_CHAR + r')(command_elab|term_elab|'
     r'tactic|delab|app_unexpander|macro|init|simproc|dsimproc|\w+_parser|builtin_\w+)(?!\w)'),
    ('local instance', r'(?<!' + IDENT_CHAR + r')(local|scoped)\s+instance\b'),
    ('local instance', r'attribute\s*\[[^\]]*(?<!' + IDENT_CHAR + r')(local|scoped)\s+instance\b'),
]

OPTION = re.compile(r'(?<!' + IDENT_CHAR + r')set_option\s+([^\s]+)')

LAKE_KEYS = re.compile(
    r'(?<![\w.])(leanOptions|moreLeanArgs|weakLeanArgs|moreServerOptions|moreServerArgs|'
    r'moreGlobalServerArgs|plugins|dynlibs|precompileModules|moreLeancArgs|moreLinkArgs)(?!\w)')


def blank(s):
    return ''.join('\n' if ch == '\n' else ' ' for ch in s)


OUTSIDE = re.compile(r"/-|--|\"|'|\u00ab")
RAW_OPENER = re.compile(r'r(#*)$')
INSIDE = re.compile(r'/-|-/')


def raw_hashes(text, i):
    """For a quote at position i, the hashes of a raw string opener r#...# just before it, or
    None when the quote does not open a raw string."""
    m = RAW_OPENER.search(text, max(0, i - 64), i)
    if not m or (m.start() > 0 and re.match(IDENT_CHAR, text[m.start() - 1])):
        return None
    return m.group(1)


def strip(text, preserve_quoted=False, interpolations=None):
    """Replaces comments, docstrings and string literals by spaces, keeping line breaks."""
    out = []
    i, n = 0, len(text)
    while i < n:
        m = OUTSIDE.search(text, i)
        if not m:
            out.append(text[i:])
            break
        out.append(text[i:m.start()])
        i, tok = m.start(), m.group(0)
        if tok == '/-':
            depth, j = 1, i + 2
            while depth and j < n:
                k = INSIDE.search(text, j)
                if not k:
                    j = n
                    break
                depth += 1 if k.group(0) == '/-' else -1
                j = k.end()
            out.append(blank(text[i:j]))
            i = j
        elif tok == '--':
            j = text.find('\n', i)
            j = n if j < 0 else j
            out.append(' ' * (j - i))
            i = j
        elif tok == '\u00ab':
            # a quoted identifier such as «a"b»: nothing inside it is a quote or a comment
            j = text.find('\u00bb', i + 1)
            j = n if j < 0 else j + 1
            if preserve_quoted and j <= n and text[j - 1:j] == '»':
                out.append(' ' + text[i + 1:j - 1] + ' ')
            else:
                out.append(blank(text[i:j]))
            i = j
        elif tok == '"' and raw_hashes(text, i) is not None:
            # a raw string r"..." or r#"..."#: no escapes, it ends at the quote and the hashes
            close = '"' + raw_hashes(text, i)
            j = text.find(close, i + 1)
            j = n if j < 0 else j + len(close)
            out.append(blank(text[i:j]))
            i = j
        elif tok == '"':
            # Conservative policy: bang-prefixed string syntax may elaborate embedded code.
            # Check before masking; comments and ordinary/raw strings remain excluded.
            prefix = INTERPOLATION_PREFIX.search(''.join(out))
            if prefix and interpolations is not None:
                interpolations.append((prefix.start(), prefix.group(1)))
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            j = min(j + 1, n)
            out.append(blank(text[i:j]))
            i = j
        elif i + 2 < n and (text[i + 2] == "'" or text[i + 1] == '\\') \
                and (i == 0 or not re.match(IDENT_CHAR, text[i - 1])):
            # a character literal such as '"' or '\n'
            j = text.find("'", i + 2)
            j = n if j < 0 else j + 1
            out.append(' ' * (j - i))
            i = j
        else:
            out.append(tok)
            i += 1
    return ''.join(out)


def line_of(text, pos):
    return text.count('\n', 0, pos) + 1


def scan_lean(path):
    with open(path, encoding='utf-8') as f:
        raw = f.read()
    interpolations = []
    text = strip(raw, interpolations=interpolations)
    attribute_text = strip(raw, preserve_quoted=True)
    found = [(line_of(raw, pos), 'interpolated string syntax ' + prefix)
             for pos, prefix in interpolations]
    prev = None
    for m in TOKEN.finditer(text):
        tok, before = m.group(0), prev
        prev = tok
        if tok == 'instance' and before not in ('local', 'scoped'):
            line = line_of(text, m.start())
            if (norm(path), raw.splitlines()[line - 1].strip()) not in ALLOWED_INSTANCES:
                found.append((line, 'instance'))
        elif tok == 'deriving':
            found.append((line_of(text, m.start()), 'deriving'))
        elif tok in PLACEHOLDERS and not placeholder_allowed(path):
            found.append((line_of(text, m.start()), tok))
        elif tok in ESCAPES:
            found.append((line_of(text, m.start()), tok))
        elif tok in KEYWORDS:
            found.append((line_of(text, m.start()), tok))
        elif tok.startswith('debug.'):
            found.append((line_of(text, m.start()), 'debug option ' + tok))
    for label, pat in CONSTRUCTS:
        checked = attribute_text if label == 'attribute that runs code' else text
        for m in re.finditer(pat, checked):
            found.append((line_of(checked, m.start()), label))
    for m in OPTION.finditer(text):
        if m.group(1) not in ALLOWED_OPTIONS:
            found.append((line_of(text, m.start()), 'set_option ' + m.group(1)))
    for m in IMPORT.finditer(text):
        mod = m.group(1)
        if (mod == 'IUT.Experimental' or mod.startswith('IUT.Experimental.')) \
                and not is_experimental(path):
            found.append((line_of(text, m.start()), 'import of experimental module ' + mod))
        if is_challenge(path) and not (mod == 'Mathlib' or mod.startswith('Mathlib.')
                                       or mod.startswith('Challenge.')):
            found.append((line_of(text, m.start()), 'challenge file imports ' + mod))
    return sorted(set(found))


IMPORT = re.compile(r'^(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(\S+)', re.M)


def scan_lake(path):
    with open(path, encoding='utf-8') as f:
        text = f.read()
    try:
        data = tomllib.loads(text)
    except tomllib.TOMLDecodeError as exc:
        m = re.search(r'\(at line (\d+)', str(exc))
        return [(int(m.group(1)) if m else 1, 'invalid TOML: ' + str(exc))]
    keys = set()
    def visit(value):
        if isinstance(value, dict):
            for key, child in value.items():
                if LAKE_KEYS.fullmatch(key):
                    keys.add(key)
                visit(child)
        elif isinstance(value, list):
            for child in value:
                visit(child)
    visit(data)
    found = []
    for key in sorted(set(data) | set(LAKEFILE)):
        if LAKE_KEYS.fullmatch(key):
            continue
        if key == 'lean_lib':
            libs = {lib.get('name'): lib for lib in data.get(key, []) if isinstance(lib, dict)}
            want = {lib['name']: lib for lib in LAKEFILE[key]}
            where = {}
            for m in re.finditer(r'^\[\[lean_lib\]\][^\[]*?^name\s*=\s*"([^"]*)"', text, re.M | re.S):
                where.setdefault(m.group(1), line_of(text, m.start()))
            for name in sorted(set(libs) | set(want), key=str):
                if libs.get(name) != want.get(name):
                    found.append((where.get(name, 1),
                                  f'library {name} differs from the recorded configuration'))
        elif data.get(key) != LAKEFILE.get(key):
            m = re.search(r'^\[*' + re.escape(key) + r'\b', text, re.M)
            found.append((line_of(text, m.start()) if m else 1,
                          f'lakefile key {key} differs from the recorded configuration'))
    # Locations are diagnostic only; acceptance uses the decoded TOML keys above.
    locations = {}
    for m in LAKE_KEYS.finditer(text):
        locations.setdefault(m.group(1), line_of(text, m.start()))
    for m in re.finditer(r'"(?:\\.|[^"\\])*"', text):
        try:
            value = tomllib.loads('key = ' + m.group(0))['key']
        except tomllib.TOMLDecodeError:
            continue
        if isinstance(value, str) and value in keys:
            locations.setdefault(value, line_of(text, m.start()))
    return sorted(found + [(locations.get(key, 1), 'lakefile option ' + key) for key in keys])


def manifest_problems(path='lake-manifest.json'):
    try:
        with open(path, encoding='utf-8') as f:
            packages = json.load(f).get('packages', [])
        got = [(p.get('name'), p.get('url'), p.get('rev')) for p in packages]
    except (OSError, ValueError, AttributeError) as exc:
        return [(path, f'cannot read: {exc}')]
    if sorted(got, key=str) == sorted(MANIFEST):
        return []
    return ([(path, f'package {p[0]} ({p[1]} at {p[2]}) is not in the recorded list')
             for p in sorted(set(got) - set(MANIFEST), key=str)]
            + [(path, f'recorded package {p[0]} ({p[1]} at {p[2]}) is missing')
               for p in sorted(set(MANIFEST) - set(got), key=str)])


def tracked_problems(files):
    """Tracked .lean files outside the scanned roots and the tooling files, and files under
    Solution/ or Challenge/ (other than Challenge/Defs.lean) that no gate check covers."""
    try:
        out = subprocess.run(['git', 'ls-files', '-z', '--', '*.lean'], capture_output=True,
                             check=True).stdout.decode('utf-8')
    except (OSError, subprocess.CalledProcessError) as exc:
        return [('git ls-files', f'cannot list the tracked files: {exc}')]
    scanned = set(files)
    found = []
    for path in sorted(p for p in out.split('\0') if p):
        if path.startswith('Solution/') or (path.startswith('Challenge/')
                                             and path != 'Challenge/Defs.lean'):
            found.append((path, 'not checked by the axiom gate (only the modules Solution and '
                                'Challenge.Defs are)'))
        elif path not in scanned and not any(path == t or (t.endswith('/') and path.startswith(t))
                                             for t in TOOLING):
            found.append((path, 'tracked Lean file outside every checked root'))
    for path in files:
        if path.startswith('Solution/') or (path.startswith('Challenge/')
                                             and path != 'Challenge/Defs.lean'):
            if (path, 'not checked by the axiom gate (only the modules Solution and '
                      'Challenge.Defs are)') not in found:
                found.append((path, 'not checked by the axiom gate (only the modules Solution '
                                    'and Challenge.Defs are)'))
    return found


def library_files():
    files = ['IUT.lean']
    for top in ('IUT', 'Challenge', 'Solution'):
        for root, dirs, names in os.walk(top):
            dirs.sort()
            files += [norm(os.path.join(root, x)) for x in sorted(names) if x.endswith('.lean')]
    return files + ['Challenge.lean', 'Solution.lean']


def import_problems(files):
    """Library files outside IUT/Experimental/ that the root file IUT.lean does not import
    directly, and imports of the root file without a library file. Without such a check a new
    module that is missing from the root file is never built and never seen by the gate."""
    mods = {f[:-5].replace('/', '.') for f in files
            if f.startswith('IUT/') and not is_experimental(f)}
    with open('IUT.lean', encoding='utf-8') as f:
        root = strip(f.read())
    imported = set(re.findall(r'^import\s+(IUT\.[\w.]+)\s*$', root, re.M))
    found = [(m.replace('.', '/') + '.lean', 'not imported by IUT.lean')
             for m in sorted(mods - imported)]
    found += [('IUT.lean', f'imports {m}, which has no file') for m in sorted(imported - mods)]
    return found


def main(argv):
    if any(a.startswith('-') for a in argv):
        print('usage: source_scan.py [FILE ...]')
        return 2
    manifests = []
    if argv:
        manifests = [a for a in argv if a.endswith('lake-manifest.json')]
        lean = [a for a in argv if not a.endswith('.toml') and a not in manifests]
        lake = [a for a in argv if a.endswith('.toml')]
    else:
        if not all(os.path.isfile(f) for f in ('IUT.lean', 'Challenge.lean', 'Solution.lean')):
            print('run from the repository root')
            return 2
        lean, lake = library_files(), ['lakefile.toml']
    total = 0
    for path in lean:
        for line, label in scan_lean(path):
            print(f'{path}:{line}: {label}')
            total += 1
    for path in lake:
        for line, label in scan_lake(path):
            print(f'{path}:{line}: {label}')
            total += 1
    for path in manifests:
        for where, label in manifest_problems(path):
            print(f'{where}: {label}')
            total += 1
    if not argv:
        extra = import_problems(lean) + tracked_problems(lean) + manifest_problems()
        if os.path.exists('lakefile.lean'):
            extra.append(('lakefile.lean', 'a Lean lakefile next to lakefile.toml'))
        for path, label in extra:
            print(f'{path}: {label}')
            total += 1
    if total:
        print(f'source scan FAILED: {total} findings in {len(lean) + len(lake) + len(manifests)} files')
        return 1
    print(f'source scan OK: {len(lean) + len(lake)} files')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
