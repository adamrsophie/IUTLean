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
# AxiomGate.lean, the words sorry, admit, axiom, opaque, unsafe, partial, native_decide,
# implemented_by and extern, the constants of ESCAPE_CONSTANTS (sorryAx, Lean.ofReduceBool,
# Lean.trustCompiler, ...) in any spelling (quoted identifiers decoded, _root_. removed, any
# namespace), and decide +native or native := in a configuration. sorry and admit are allowed
# only in Challenge.lean and in IUT/Experimental/**.lean; everything else applies there too.
# Names: export, open ... renaming and open ... hiding are reported, and an open of a namespace
# outside ALLOWED_OPENS (check 6 of AxiomGate.lean relies on that list).
# Instances: the library declares one, so every other instance command, instance attribute
# (attribute [instance], @[instance], @[«instance»]), deriving clause and default_instance
# attribute is reported. The scan cannot tell a lexical instance on a project type from one on
# a foreign type such as LE on the reals; check 7 of AxiomGate.lean makes that distinction in
# the compiled environment and binds the accepted instance by full name and class. Instances
# that were read and accepted are listed in ALLOWED_INSTANCES by their source line, which must
# occur exactly once in its file.
# Imports: no file outside IUT/Experimental/ may import IUT.Experimental or IUT.Experimental.*;
# Challenge.lean and Challenge/**.lean may import only Mathlib and Challenge.*.
# It also rejects build options in lakefile.toml that pass options or arguments to Lean, and
# compares the decoded lakefile with the recorded configuration LAKEFILE (exact require set
# with name, URL and revision; exact library names and keys, so no srcDir, roots or globs
# beyond the recorded ones; each library declared once). In the default form, on the whole
# tree, it also rejects: a file lakefile.lean; a lake-manifest.json that differs from the
# recorded manifest (MANIFEST_TOP, MANIFEST_PACKAGE, MANIFEST: every field, with
# multiplicity); a lean-toolchain other than TOOLCHAIN; a tracked file under .lake/ or a file
# .lake/package-overrides.json; every file IUT/**.lean outside IUT/Experimental/ that the root file
# IUT.lean does not import directly, and every import of the root file without a file; every
# file under Solution/ and every file under Challenge/ other than Challenge/Defs.lean (the
# gate checks only the modules Solution and Challenge.Defs); and every tracked .lean file
# (git ls-files) outside the scanned roots and the tooling files listed by exact path in
# TOOLING.
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
from collections import Counter
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
ESCAPES = {'axiom', 'opaque', 'unsafe', 'partial', 'native_decide', 'implemented_by', 'extern'}
# Constants that bypass the kernel or stand for a missing proof, matched by the last component
# of an identifier after quoted identifiers are decoded and a leading _root_. is removed, so
# sorryAx, _root_.sorryAx, «sorryAx», Lean.ofReduceBool and ofReduceBool under open Lean are
# all found (a project name ending in one of these is reported too, which fails closed).
ESCAPE_CONSTANTS = {'sorryAx', 'ofReduceBool', 'ofReduceNat', 'reduceBool', 'reduceNat',
                    'trustCompiler', 'native_decide'}

# Namespaces that a library file may open. The gate's list openedNamespaces (check 6) holds the
# namespaces of dependencies among them; the others are namespaces of the library, written
# relative to the namespace of the file that opens them. Every namespace IUT.* may be opened.
ALLOWED_OPENS = {
    'Challenge', 'Finset', 'MeasureTheory', 'Measure', 'Set', 'Classical', 'NumberField',
    'Complex', 'ComplexConjugate', 'Filter', 'Topology', 'Real', 'Pointwise', 'ZFSet',
    'IsDedekindDomain', 'IsDedekindDomain.HeightOneSpectrum', 'WeierstrassCurve', 'Opposite',
    'CategoryTheory', 'Asymptotics', 'Ideal', 'nonZeroDivisors',
    # namespaces of the library, opened by relative name
    'IntervalExample', 'IndeterminacyOrbit', 'NormalizedLine', 'Proposition1_2',
}

# The decoded lean-toolchain.
TOOLCHAIN = 'leanprover/lean4:v4.36.0'

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

# The decoded lake-manifest.json: its top-level keys other than packages, and every package
# with all its fields, as (name, URL, revision, scope, inputRev, inherited, configFile) plus the
# fields that every package shares (MANIFEST_PACKAGE). The comparison is complete and counts
# multiplicity: a duplicate, missing or extra package and any changed field are reported.
MANIFEST_TOP = {'version': '1.3.0', 'packagesDir': '.lake/packages', 'name': 'IUT',
                'lakeDir': '.lake', 'fixedToolchain': False}
MANIFEST_PACKAGE = {'type': 'git', 'subDir': None, 'manifestFile': 'lake-manifest.json'}
MANIFEST_FIELDS = ('name', 'url', 'rev', 'scope', 'inputRev', 'inherited', 'configFile')
LC = 'leanprover-community'
MANIFEST = [
    ('mathlib', MATHLIB_URL, 'fc4f59e577feb1a4956671bc04ac18aaaf8cd842', '',
     'fc4f59e577feb1a4956671bc04ac18aaaf8cd842', False, 'lakefile.lean'),
    ('plausible', 'https://github.com/leanprover-community/plausible',
     '054b228ce0ac61d767c6e71ba73a24728f191b72', LC, 'main', True, 'lakefile.toml'),
    ('LeanSearchClient', 'https://github.com/leanprover-community/LeanSearchClient',
     '4fb58e749ef3fc0395fe274f6cab70c2ea85f1c9', LC, 'main', True, 'lakefile.toml'),
    ('importGraph', 'https://github.com/leanprover-community/import-graph',
     '8370c640afcd1cc3fb1cb9bf1560cc66eafee5e0', LC, 'main', True, 'lakefile.toml'),
    ('proofwidgets', 'https://github.com/leanprover-community/ProofWidgets4',
     '2f0f3520daeac2d9310ff25b7a877a0e5cdaa203', LC, 'main', True, 'lakefile.lean'),
    ('aesop', 'https://github.com/leanprover-community/aesop',
     '66ff77cf0c4c898799e4b94d14db55f7a02d0c5a', LC, 'master', True, 'lakefile.toml'),
    ('Qq', 'https://github.com/leanprover-community/quote4',
     'ff055a2fcc835935e0ae607339b455a5f5896b4b', LC, 'master', True, 'lakefile.toml'),
    ('batteries', 'https://github.com/leanprover-community/batteries',
     'b4b25a3886a16daacaf6615c2eea7170a6e8f458', LC, 'main', True, 'lakefile.toml'),
    ('Cli', 'https://github.com/leanprover/lean4-cli', '50810f72af7618bee62fe9800dc26e806c188703',
     'leanprover', 'v4.36.0', True, 'lakefile.toml'),
]

# Instance commands that were read and accepted: (path, the whole source line). Each is an
# instance on a project type. The line must occur exactly once in its file; check 7 of
# AxiomGate.lean also checks every instance against its own list instanceAllowed (full name and
# class), so the line cannot be reused for another constant.
ALLOWED_INSTANCES = {
    ('IUT/PaperI/PolyMorphism.lean', 'attribute [instance] Capsule.fintype'),
}

# Tracked Lean files that are tooling, not proof sources: no default target contains them and
# nothing in the library imports them. Exact paths; a new control or helper is added here.
TOOLING = {
    'AxiomGate.lean', 'GateControls/Clean.lean', 'GateControls/DeepConclusions.lean',
    'GateControls/DeepConclusionsClean.lean', 'GateControls/EquivalentForm.lean',
    'GateControls/ExperimentalImport.lean', 'GateControls/ExponentThree.lean',
    'GateControls/ForbiddenAxiom.lean', 'GateControls/ForeignInstances.lean',
    'GateControls/GateProbe.lean', 'GateControls/NamedConditional.lean',
    'GateControls/NativeDecide.lean',
    'GateControls/OpenStatements.lean', 'GateControls/OpenStatementsClean.lean',
    'GateControls/PrivateShadowing.lean', 'GateControls/RenamedConjecture.lean',
    'GateControls/ResolutionModel.lean',
    'GateControls/Shadowing.lean', 'GateControls/Sorry.lean', 'GateControls/SourceScan.lean',
    'GateControls/TrustedNames.lean', 'GateControls/VojtaRestated.lean',
    'GateControls/WalkFuel.lean',
    'scripts/Controls/Fingerprints.lean', 'scripts/LeanDeclarations.lean',
}


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
    'export', 'renaming', 'hiding',
}

TOKEN = re.compile('#?' + IDENT_CHAR + '+')
INTERPOLATION_PREFIX = re.compile('(' + IDENT_CHAR + r'+!)\s*$')

# (label, pattern) on the text without comments and strings.
CONSTRUCTS = [
    ('attribute that runs code', r'(?:@\[|\battribute\s*\[)[^\]]*(?<!' + IDENT_CHAR + r')(command_elab|term_elab|'
     r'tactic|delab|app_unexpander|macro|init|simproc|dsimproc|\w+_parser|builtin_\w+)(?!\w)'),
    ('local instance', r'(?<!' + IDENT_CHAR + r')(local|scoped)\s+instance\b'),
    ('local instance', r'attribute\s*\[[^\]]*(?<!' + IDENT_CHAR + r')(local|scoped)\s+instance\b'),
    ('native evaluation', r'\+\s*native(?!\w)|(?<!' + IDENT_CHAR + r')native\s*:='),
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
                # decoded in place, so that _root_.«sorryAx» reads _root_.sorryAx
                out.append(text[i + 1:j - 1])
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
    for m in TOKEN.finditer(text):
        tok = m.group(0)
        if tok in PLACEHOLDERS and not placeholder_allowed(path):
            found.append((line_of(text, m.start()), tok))
        elif tok in KEYWORDS:
            found.append((line_of(text, m.start()), tok))
        elif tok.startswith('debug.'):
            found.append((line_of(text, m.start()), 'debug option ' + tok))
    # Identifiers and attribute names, on the text with quoted identifiers decoded.
    raw_lines = raw.splitlines()
    prev = None
    for m in TOKEN.finditer(attribute_text):
        tok, before = canonical(m.group(0)), prev
        prev = tok
        line = line_of(attribute_text, m.start())
        if tok == 'instance' and before not in ('local', 'scoped'):
            text_line = raw_lines[line - 1].strip()
            if (norm(path), text_line) not in ALLOWED_INSTANCES:
                found.append((line, 'instance'))
            elif sum(x.strip() == text_line for x in raw_lines) != 1:
                found.append((line, 'allowed instance line repeated'))
        elif tok == 'deriving':
            found.append((line, 'deriving'))
        elif tok == 'default_instance':
            found.append((line, 'default_instance'))
        elif tok in ESCAPES:
            found.append((line, tok))
        elif tok.split('.')[-1] in ESCAPE_CONSTANTS:
            found.append((line, tok.split('.')[-1]))
    for m in OPEN.finditer(text):
        for name in m.group(1).split():
            if name in ('renaming', 'hiding'):
                break  # reported as keywords
            if name in ('in', 'scoped') or not re.fullmatch(IDENT_CHAR + '+', name):
                continue
            if name not in ALLOWED_OPENS and not name.startswith('IUT.'):
                found.append((line_of(text, m.start()), 'open of namespace ' + name))
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


IMPORT = re.compile(r'(?<!' + IDENT_CHAR + r')import\s+(?:all\s+)?(\S+)')
# An open command: the namespaces up to the end of the line ('in' and 'scoped' are skipped).
OPEN = re.compile(r'(?<!' + IDENT_CHAR + r')open\s+([^\n(]*)')


def canonical(tok):
    """An identifier without the leading dots and _root_. prefixes it may carry."""
    while True:
        t = tok.lstrip('.')
        if t.startswith('_root_.'):
            t = t[len('_root_.'):]
        if t == tok:
            return t
        tok = t


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
            got = data.get(key, [])
            got = got if isinstance(got, list) else [got]
            libs = {lib.get('name'): lib for lib in got if isinstance(lib, dict)}
            want = {lib['name']: lib for lib in LAKEFILE[key]}
            where = {}
            for m in re.finditer(r'^\[\[lean_lib\]\][^\[]*?^name\s*=\s*"([^"]*)"', text, re.M | re.S):
                where.setdefault(m.group(1), line_of(text, m.start()))
            counts = Counter(lib.get('name') if isinstance(lib, dict) else None for lib in got)
            for name, k in sorted(counts.items(), key=str):
                if k > 1:
                    found.append((where.get(name, 1), f'library {name} is declared {k} times'))
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
    """The complete decoded manifest against MANIFEST_TOP, MANIFEST_PACKAGE and MANIFEST, with
    multiplicity."""
    try:
        with open(path, encoding='utf-8') as f:
            data = json.load(f)
        packages = data['packages']
        top = {k: v for k, v in data.items() if k != 'packages'}
        if not isinstance(packages, list) or not all(isinstance(p, dict) for p in packages):
            raise ValueError('packages is not a list of objects')
    except (OSError, ValueError, KeyError, AttributeError, TypeError) as exc:
        return [(path, f'cannot read: {exc}')]
    found = []
    for k in sorted(set(top) | set(MANIFEST_TOP)):
        if top.get(k, '<missing>') != MANIFEST_TOP.get(k, '<missing>'):
            found.append((path, f'key {k} is {top.get(k, "missing")!r}, recorded '
                                f'{MANIFEST_TOP.get(k, "absent")!r}'))
    names = Counter(p.get('name') for p in packages)
    for n, k in sorted(names.items(), key=str):
        if k > 1:
            found.append((path, f'package {n} is listed {k} times'))
    want = {r[0]: {**MANIFEST_PACKAGE, **dict(zip(MANIFEST_FIELDS, r))} for r in MANIFEST}
    key = lambda p: (p.get('name'), p.get('url'), p.get('rev'))
    got, rec = Counter(map(key, packages)), Counter(key(w) for w in want.values())
    for p in sorted((got - rec).elements(), key=str):
        found.append((path, f'package {p[0]} ({p[1]} at {p[2]}) is not in the recorded list'))
    for p in sorted((rec - got).elements(), key=str):
        found.append((path, f'recorded package {p[0]} ({p[1]} at {p[2]}) is missing'))
    for p in packages:
        w = want.get(p.get('name'))
        if w is None or key(p) != key(w) or names[p.get('name')] > 1:
            continue
        for field in sorted(set(p) | set(w)):
            if p.get(field, '<missing>') != w.get(field, '<missing>'):
                found.append((path, f'package {p.get("name")}: {field} is '
                                    f'{p.get(field, "missing")!r}, recorded '
                                    f'{w.get(field, "absent")!r}'))
    return found


def git_lean_files():
    out = subprocess.run(['git', 'ls-files', '-z', '--', '*.lean'], capture_output=True,
                         check=True).stdout.decode('utf-8')
    return [p for p in out.split('\0') if p]


GATE_UNCHECKED = ('not checked by the axiom gate (only the modules Solution and Challenge.Defs '
                  'are)')


def tracked_problems(files, tracked=None):
    """Tracked .lean files outside the scanned roots and the tooling files, and files under
    Solution/ or Challenge/ (other than Challenge/Defs.lean) that no gate check covers.
    `tracked` is the list of tracked .lean paths; by default it is read from git."""
    if tracked is None:
        try:
            tracked = git_lean_files()
        except (OSError, subprocess.CalledProcessError) as exc:
            return [('git ls-files', f'cannot list the tracked files: {exc}')]
    unchecked = lambda p: p.startswith('Solution/') or (p.startswith('Challenge/')
                                                        and p != 'Challenge/Defs.lean')
    scanned = set(files)
    found = []
    for path in sorted(set(tracked)):
        if unchecked(path):
            found.append((path, GATE_UNCHECKED))
        elif path not in scanned and path not in TOOLING:
            found.append((path, 'tracked Lean file outside every checked root'))
    for path in files:
        if unchecked(path) and (path, GATE_UNCHECKED) not in found:
            found.append((path, GATE_UNCHECKED))
    return found


def config_problems():
    """lean-toolchain against TOOLCHAIN, and Lake files that override the manifest."""
    found = []
    try:
        with open('lean-toolchain', encoding='utf-8') as f:
            if f.read().strip() != TOOLCHAIN:
                found.append(('lean-toolchain', f'differs from {TOOLCHAIN}'))
    except OSError as exc:
        found.append(('lean-toolchain', f'cannot read: {exc}'))
    try:
        out = subprocess.run(['git', 'ls-files', '-z', '--', '.lake'], capture_output=True,
                             check=True).stdout.decode('utf-8')
        found += [(p, 'tracked file under .lake/ (package overrides and build state are not '
                      'part of the project)') for p in out.split('\0') if p]
    except (OSError, subprocess.CalledProcessError) as exc:
        found.append(('git ls-files', f'cannot list the tracked files: {exc}'))
    if os.path.exists(os.path.join('.lake', 'package-overrides.json')):
        found.append(('.lake/package-overrides.json', 'a Lake package override file'))
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
        extra = (import_problems(lean) + tracked_problems(lean) + manifest_problems()
                 + config_problems())
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
