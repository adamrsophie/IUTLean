"""Rules for the statement records, shared by extract_statements.py, dashboard.py, gen_docs.py
and build_graph.py.

Fragment rule. A record for a statement of the papers (or a part or proof step of one) may
carry a status of the formalized family (STATEMENT_FORMALIZED, STATEMENT_REVIEWED) or of the
verified family (CONDITIONALLY_VERIFIED, KERNEL_VERIFIED, INDEPENDENTLY_CHECKED) only together
with a `lean_declaration` that states its entire content. A Lean lemma that checks one piece
of a statement is a separate record of kind "fragment", with id `<parent>.frag.<name>` and a
`parent` field; the parent lists it in `fragments`. A parent never counts as formalized or
verified through a fragment.

Ids. A record id is a mechanical id of data/mechanical_index.json (`IUT3.Cor3_12`), a part or
proof step of a record (`IUT3.Cor3_12.StepXI`, parent: the id without its last component), a
fragment (`IUT4.Cor2_2.iii.frag.h_lt`, parent: its `parent` field), or an unnumbered item of a
section (`IUT1.Sec0.PolyMorphism`): an independent record with no parent, whose `kind` and
pages are given by the curated file.

Validation functions return lists of messages; the callers print them and exit nonzero.
"""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
STATUSES = {"NOT_EXTRACTED", "EXTRACTED", "INTERPRETATION_AMBIGUOUS", "LEAN_STATEMENT_DRAFT",
            "STATEMENT_FORMALIZED", "STATEMENT_REVIEWED", "PROOF_IN_PROGRESS",
            "BLOCKED_BY_MATHLIB", "BLOCKED_BY_EXTERNAL_THEOREM",
            "BLOCKED_BY_MISSING_JUSTIFICATION", "CONDITIONALLY_VERIFIED", "KERNEL_VERIFIED",
            "INDEPENDENTLY_CHECKED", "COUNTERMODEL_FOUND"}
FORMALIZED = {"STATEMENT_FORMALIZED", "STATEMENT_REVIEWED"}
VERIFIED = {"KERNEL_VERIFIED", "INDEPENDENTLY_CHECKED"}
PROVED_FAMILY = {"CONDITIONALLY_VERIFIED"} | VERIFIED
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# Printed next to the status wherever statuses are explained.
LEGEND = {
    "BLOCKED_BY_MISSING_JUSTIFICATION":
        "the text gives an assertion where a formalization needs a derivation; this is not a "
        "claim that the result is false",
}
SECTION_ITEM = re.compile(r"^IUT([1-4])\.Sec(\d+)\.[A-Za-z][A-Za-z0-9_]*$")
FRAGMENT = re.compile(r"^(.+)\.frag\.[A-Za-z0-9_']+$")
# A qualified name of this library in a JSON string: IUT.*, Challenge.*, Solution.*.
DECL_TOKEN = re.compile(r"(?<![\w./])((?:IUT|Challenge|Solution)\.[A-Za-z0-9_.'Ͱ-Ͽ"
                        r"₀-ₜ]+)")
# Data files that are generated from the files checked here, or that hold no references.
GENERATED = {"statements.json", "mechanical_index.json", "dependencies.json",
             "dependency_graph.json", "dashboard.json", "lean_declarations.json",
             "references.json", "source_manifest.json", "challenge_fingerprints.json"}


def is_fragment(record):
    return record.get("kind") == "fragment"


def parent_of(sid, record):
    """The parent id of a curated record that the index does not have, or None."""
    if SECTION_ITEM.match(sid):
        return None
    m = FRAGMENT.match(sid)
    if m or is_fragment(record):
        return record.get("parent") or (m.group(1) if m else None)
    parts = sid.split(".")
    return ".".join(parts[:-1]) if len(parts) >= 3 else None


def parse_pages(text):
    """(first, last) page of a page description such as "pages 41 to 43" or "45", or None."""
    nums = [int(n) for n in re.findall(r"\d+", str(text or ""))]
    return (min(nums), max(nums)) if nums else None


def reviewed_pages(record):
    src = record.get("source")
    if not isinstance(src, dict):
        return None
    return parse_pages(src.get("pages") or src.get("pdf_pages"))


def nonempty(value):
    return bool(value.strip()) if isinstance(value, str) else bool(value)


def structural_errors(statements):
    """Errors that do not need the Lean inventory."""
    by_id = {s["id"]: s for s in statements}
    errors = []
    for s in statements:
        sid = s["id"]
        where = f"{sid} ({s.get('curated_in') or 'index'})"
        for field in ("statement_status", "proof_status"):
            if s.get(field) not in STATUSES:
                errors.append(f"{where}: {field} {s.get(field)!r} is not a status of the brief")
        parent = s.get("parent")
        if parent is not None and parent not in by_id:
            errors.append(f"{where}: parent {parent} is not a record")
        decl = s.get("lean_declaration")
        if is_fragment(s):
            if not parent or not FRAGMENT.match(sid):
                errors.append(f"{where}: a fragment id must have the form <id>.frag.<name> and "
                              f"the record a parent field")
            if not decl:
                errors.append(f"{where}: fragment without lean_declaration")
            for field in ("content", "conclusion", "covers", "not_covered"):
                if not nonempty(s.get(field)):
                    errors.append(f"{where}: fragment without {field}")
            if not isinstance(s.get("explicit_hypotheses"), list):
                errors.append(f"{where}: fragment without the list explicit_hypotheses")
            if s.get("statement_status") != "STATEMENT_FORMALIZED":
                errors.append(f"{where}: fragment statement_status must be STATEMENT_FORMALIZED")
            if s.get("proof_status") not in ("KERNEL_VERIFIED", "CONDITIONALLY_VERIFIED",
                                             "NOT_EXTRACTED"):
                errors.append(f"{where}: fragment proof_status must be KERNEL_VERIFIED or "
                              f"CONDITIONALLY_VERIFIED (a theorem) or NOT_EXTRACTED (a "
                              f"definition)")
            if s.get("proof_status") == "CONDITIONALLY_VERIFIED" and not s.get("obligations"):
                errors.append(f"{where}: conditional fragment without the assumed claims in "
                              f"obligations")
            if parent in by_id and sid not in (by_id[parent].get("fragments") or []):
                errors.append(f"{where}: not listed in the fragments of {parent}")
        else:
            formal = s.get("statement_status") in FORMALIZED
            proved = s.get("proof_status") in PROVED_FAMILY
            if (formal or proved) and not decl:
                errors.append(f"{where}: status {s.get('statement_status')}/"
                              f"{s.get('proof_status')} without a lean_declaration")
        for f in s.get("parts") or []:
            if f not in by_id or by_id[f].get("parent") != sid or is_fragment(by_id[f]):
                errors.append(f"{where}: parts lists {f}, which is not a part record with this "
                              f"parent")
        for f in s.get("fragments") or []:
            if f not in by_id or not is_fragment(by_id[f]) or by_id[f].get("parent") != sid:
                errors.append(f"{where}: fragments lists {f}, which is not a fragment record "
                              f"with this parent")
        if s.get("statement_status") == "EXTRACTED":
            missing = [f for f in ("content", "conclusion") if not nonempty(s.get(f))]
            if not isinstance(s.get("explicit_hypotheses"), list):
                missing.append("explicit_hypotheses")
            if missing:
                errors.append(f"{where}: EXTRACTED without {', '.join(missing)}")
        if SECTION_ITEM.match(sid) and s.get("curated_in"):
            if not s.get("kind") or not reviewed_pages(s):
                errors.append(f"{where}: an unnumbered section item needs kind and "
                              f"source.pdf_pages")
    return errors


def is_theorem(decl):
    """Whether a declaration of data/lean_declarations.json is a theorem. Definitions,
    structures, classes, inductive types and instances are typed in Lean but never proved."""
    return bool(decl) and decl.get("kind") == "theorem"


def declaration_errors(statements, decls, modules):
    """Every lean_declaration and every name of `lemmas`, and every qualified name of this
    library in a data file, must be a declaration (or a module) of data/lean_declarations.json.
    A record whose declaration is not a theorem may not have a proof status of the verified
    family. `decls` maps names to inventory entries."""
    names = set(decls)
    errors = []
    for s in statements:
        where = f"{s['id']} ({s.get('curated_in') or 'index'})"
        decl = s.get("lean_declaration")
        for d in ([decl] if decl else []) + list(s.get("lemmas") or []):
            if d not in names:
                errors.append(f"{where}: declaration {d} is not in data/lean_declarations.json")
        if decl in decls and not is_theorem(decls[decl]) and s.get("proof_status") in PROVED_FAMILY:
            errors.append(f"{where}: {decl} is a {decls[decl].get('kind')}, not a theorem, so "
                          f"proof_status {s.get('proof_status')} is not possible (use "
                          f"NOT_EXTRACTED)")
    files = sorted(p for p in (ROOT / "data").glob("*.json") if p.name not in GENERATED)
    files += sorted((ROOT / "data" / "curated").glob("*.json"))
    for path in files:
        try:
            text = path.read_text()
        except OSError as e:
            errors.append(f"{path.relative_to(ROOT)}: {e}")
            continue
        seen = set()
        for m in DECL_TOKEN.finditer(text):
            tok = m.group(1).rstrip(".")
            if tok.endswith(".lean") or tok in names or tok in modules or tok in seen:
                continue
            seen.add(tok)
            line = text.count("\n", 0, m.start()) + 1
            errors.append(f"{path.relative_to(ROOT)}:{line}: {tok} is not a declaration or "
                          f"module of data/lean_declarations.json")
    return errors
