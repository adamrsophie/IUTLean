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

Statements of other papers. A record whose id starts with a prefix of EXTERNAL_PAPERS
(`EXPL.Thm5_4`, `ZHOU1.Thm3_2`) states a result or claim of that paper, not of IUT I to IV. It
has kind "external_statement" and no parent, or it is a fragment of such a record. Its pages
are pages of that paper, in `source.pages_in_paper`; it never carries `source.pages` or
`source.pdf_pages`, which hold pages of IUT I to IV. Its `source` also names the authors, the
title, the arXiv identifier (`arxiv`) or a journal reference (`journal`), and the statement
number (`statement`). Its `lean_declaration` is null unless a `def ... : Prop` states it
exactly; then its statuses are STATEMENT_FORMALIZED and EXTERNAL_CLAIM (stated in Lean, used
only as a hypothesis, not proved here). The dashboard and the catalog report these records
apart from the four papers. `source.pages_in_paper` is also accepted on records of IUT I to
IV, for pages of another paper that the record relies on; it is not read as pages of IUT I to
IV.

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
            "INDEPENDENTLY_CHECKED", "COUNTERMODEL_FOUND", "EXTERNAL_CLAIM"}
FORMALIZED = {"STATEMENT_FORMALIZED", "STATEMENT_REVIEWED"}
VERIFIED = {"KERNEL_VERIFIED", "INDEPENDENTLY_CHECKED"}
PROVED_FAMILY = {"CONDITIONALLY_VERIFIED"} | VERIFIED
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# Printed next to the status wherever statuses are explained.
LEGEND = {
    "BLOCKED_BY_MISSING_JUSTIFICATION":
        "the text gives an assertion where a formalization needs a derivation; this is not a "
        "claim that the result is false",
    "EXTERNAL_CLAIM":
        "a statement of another paper, stated in Lean as a proposition and used only as a "
        "hypothesis; it is not proved in this project",
}
# Id prefixes of statements of other papers, with the paper each stands for and its arXiv
# identifiers (empty when the paper has none). One place; a new paper is one entry.
EXTERNAL_PAPERS = {
    "EXPL": ("S. Mochizuki, I. Fesenko, Y. Hoshi, A. Minamide, W. Porowski, \"Explicit "
             "Estimates in Inter-universal Teichmuller Theory\"", ()),
    "ZHOU1": ("Z.-P. Zhou, arXiv 2503.14510", ("2503.14510",)),
    "ZHOU2": ("Z.-P. Zhou, arXiv 2510.05448", ("2510.05448",)),
    "DH": ("T. Dupuy, A. Hilado, arXiv 2004.13228 and 2004.13108", ("2004.13228", "2004.13108")),
    "GENELL": ("S. Mochizuki, \"Arithmetic Elliptic Curves in General Position\", Math. J. Okayama Univ. 52 (2010)", ()),
}
EXTERNAL_STATEMENT = "external_statement"
EXTERNAL_SOURCE_FIELDS = ("authors", "title", "statement", "pages_in_paper")
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


def external_prefix(sid):
    """The prefix of EXTERNAL_PAPERS that the id `sid` starts with, or None."""
    head = str(sid).split(".")[0]
    return head if head in EXTERNAL_PAPERS else None


def parent_of(sid, record):
    """The parent id of a curated record that the index does not have, or None."""
    if SECTION_ITEM.match(sid) or (external_prefix(sid) and not FRAGMENT.match(sid)
                                   and not is_fragment(record)):
        return None
    m = FRAGMENT.match(sid)
    if m or is_fragment(record):
        return record.get("parent") or (m.group(1) if m else None)
    parts = sid.split(".")
    return ".".join(parts[:-1]) if len(parts) >= 3 else None


ROMAN = {"I": 1, "II": 2, "III": 3, "IV": 4}
_SPAN = r"\d+(?:\s+to\s+\d+)?"
PAGE_SEGMENT = re.compile(
    r"^\s*(?:IUT\s+(?P<p1>IV|III|II|I)\s+|(?P<p2>IV|III|II|I)\s+(?=pages?\b))?"
    r"(?:pages?\s+)?(?P<spans>" + _SPAN + r"(?:\s*(?:,\s*and|,|and)\s*" + _SPAN + r")*)\s*$")


def parse_pages(text, paper=None):
    """Page spans of a page description, as a list of (paper, first, last), or None when the
    text is not of the accepted form. Accepted: segments separated by ";", each an optional
    paper ("IUT III" or "III" before "page"), an optional "page" or "pages", and spans "N" or
    "N to M" separated by ",", "and" or ", and". A segment without a paper belongs to `paper`
    (the paper of the record). Examples: "pages 41 to 43", "45", "pages 10 to 12, 15",
    "IUT III pages 173 to 174; IUT IV page 23". A span whose last page precedes its first is
    rejected."""
    if isinstance(text, int):
        text = str(text)
    if not isinstance(text, str) or not text.strip():
        return None
    out = []
    for segment in text.split(";"):
        m = PAGE_SEGMENT.match(segment)
        if not m:
            return None
        roman = m.group("p1") or m.group("p2")
        p = ROMAN[roman] if roman else paper
        for span in re.findall(_SPAN, m.group("spans")):
            nums = [int(n) for n in re.findall(r"\d+", span)]
            first, last = nums[0], nums[-1]
            if last < first:
                return None
            out.append((p, first, last))
    return out


def record_paper(record):
    """The paper of a record: its `paper` field, or the digit of its id `IUT<k>.…`."""
    if isinstance(record.get("paper"), int):
        return record["paper"]
    sid = str(record.get("id", ""))
    return int(sid[3]) if sid[:3] == "IUT" and sid[3:4].isdigit() else None


def source_pages_text(record):
    """The page text of a record: pages of IUT I to IV (`pages`, else `pdf_pages`), or, for a
    statement of another paper, `pages_in_paper`."""
    src = record.get("source")
    if not isinstance(src, dict):
        return None
    if external_prefix(record.get("id", "")):
        return src.get("pages_in_paper")
    return src.get("pages") or src.get("pdf_pages")


def page_spans(record):
    """The page spans of the curated source of a record (see parse_pages), or None."""
    text = source_pages_text(record)
    return None if text is None else parse_pages(text, record_paper(record))


def reviewed_pages(record):
    """(first, last) page of the spans of a record on its own paper (on the first paper named
    when none is on its own), or None."""
    spans = page_spans(record)
    if not spans:
        return None
    own = [sp for sp in spans if sp[0] == record_paper(record)] or \
        [sp for sp in spans if sp[0] == spans[0][0]]
    return (min(sp[1] for sp in own), max(sp[2] for sp in own))


ROMAN_OF = {v: k for k, v in ROMAN.items()}


def format_spans(spans, paper):
    """Page spans for a catalog: "173 to 174" on the record's own paper, and every span of
    another paper prefixed with that paper ("III 173 to 174; IV 23")."""
    groups = []
    for p, first, last in spans:
        text = str(first) if first == last else f"{first} to {last}"
        if groups and groups[-1][0] == p:
            groups[-1][1].append(text)
        else:
            groups.append((p, [text]))
    if all(p == paper for p, _ in groups):
        return ", ".join(t for _, ts in groups for t in ts)
    return "; ".join(f"{ROMAN_OF.get(p, p)} " + ", ".join(ts) for p, ts in groups)


# The one value of `scope` with a fixed meaning: a fragment whose declaration tests a model
# (an example, a simplified setting, a countermodel to a simplified abstraction) rather than
# checking a step of the papers. Such fragments are counted as model tests, not as fragments
# checked. Any other `scope` is free text.
MODEL_TEST = "model_test"


def is_model_test(record):
    return record.get("scope") == MODEL_TEST


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
            m = FRAGMENT.match(sid)
            if not parent or not m:
                errors.append(f"{where}: a fragment id must have the form <id>.frag.<name> and "
                              f"the record a parent field")
            elif m.group(1) != parent:
                errors.append(f"{where}: the id has the prefix {m.group(1)}, but the parent is "
                              f"{parent} (the id must be <parent>.frag.<name>)")
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
        if is_model_test(s) and not is_fragment(s):
            errors.append(f"{where}: scope {MODEL_TEST} is only for fragment records")
        if s.get("curated_in") and source_pages_text(s) is not None and not page_spans(s):
            errors.append(f"{where}: source pages {source_pages_text(s)!r} are not of the form "
                          f"\"pages N to M, K\" or \"IUT III pages N to M; IUT IV page K\"")
        errors += external_errors(s, where, by_id)
        if SECTION_ITEM.match(sid) and s.get("curated_in"):
            if not s.get("kind") or not reviewed_pages(s):
                errors.append(f"{where}: an unnumbered section item needs kind and "
                              f"source.pdf_pages")
    return errors


def external_errors(s, where, by_id):
    """The rules for statements of other papers (see the module docstring)."""
    sid = s["id"]
    prefix = external_prefix(sid)
    errors = []
    if s.get("proof_status") == "EXTERNAL_CLAIM" or s.get("statement_status") == "EXTERNAL_CLAIM":
        if not (prefix and s.get("kind") == EXTERNAL_STATEMENT
                and s.get("proof_status") == "EXTERNAL_CLAIM"):
            errors.append(f"{where}: EXTERNAL_CLAIM is only the proof status of an "
                          f"external_statement record")
    if s.get("kind") == EXTERNAL_STATEMENT and not prefix:
        errors.append(f"{where}: kind external_statement needs an id prefix of "
                      f"records.EXTERNAL_PAPERS ({', '.join(EXTERNAL_PAPERS)})")
    if not prefix:
        return errors
    if s.get("paper") is not None:
        errors.append(f"{where}: a statement of another paper has no paper field of IUT I to IV")
    src = s.get("source") if isinstance(s.get("source"), dict) else {}
    for key in ("pages", "pdf_pages"):
        if key in src:
            errors.append(f"{where}: source.{key} holds pages of IUT I to IV; pages of the "
                          f"paper {prefix} go in source.pages_in_paper")
    if is_fragment(s):
        parent = by_id.get(s.get("parent"))
        if parent is not None and parent.get("kind") != EXTERNAL_STATEMENT:
            errors.append(f"{where}: the parent of a fragment with prefix {prefix} must be an "
                          f"external_statement record")
        return errors
    if s.get("kind") != EXTERNAL_STATEMENT:
        errors.append(f"{where}: a record with prefix {prefix} has kind external_statement or "
                      f"fragment")
    if s.get("parent"):
        errors.append(f"{where}: an external_statement record has no parent")
    for key in EXTERNAL_SOURCE_FIELDS:
        if not nonempty(src.get(key)):
            errors.append(f"{where}: external_statement without source.{key}")
    arxiv, ids = src.get("arxiv"), EXTERNAL_PAPERS[prefix][1]
    if not nonempty(arxiv) and not nonempty(src.get("journal")):
        errors.append(f"{where}: external_statement without source.arxiv or source.journal")
    elif nonempty(arxiv) and ids and arxiv not in ids:
        errors.append(f"{where}: source.arxiv {arxiv} is not an identifier of {prefix} "
                      f"({', '.join(ids)})")
    if s.get("lean_declaration"):
        if (s.get("statement_status"), s.get("proof_status")) != ("STATEMENT_FORMALIZED",
                                                                  "EXTERNAL_CLAIM"):
            errors.append(f"{where}: an external_statement with a lean_declaration has the "
                          f"statuses STATEMENT_FORMALIZED and EXTERNAL_CLAIM")
    elif s.get("proof_status") in PROVED_FAMILY or s.get("proof_status") == "EXTERNAL_CLAIM":
        errors.append(f"{where}: proof_status {s.get('proof_status')} without a "
                      f"lean_declaration")
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
        if s.get("proof_status") in PROVED_FAMILY:
            for d in ([decl] if decl else []) + list(s.get("lemmas") or []):
                bad = sorted(set(decls[d].get("axioms") or []) - ALLOWED_AXIOMS) if d in decls else []
                if bad:
                    errors.append(f"{where}: proof_status {s.get('proof_status')}, but {d} "
                                  f"depends on {', '.join(bad)}")
        if decl in decls and is_theorem(decls[decl]) and s.get("proof_status") == "EXTERNAL_CLAIM":
            errors.append(f"{where}: {decl} is a theorem; an EXTERNAL_CLAIM is stated by a "
                          f"definition of type Prop, never proved")
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


def _self_test():
    assert parse_pages("pages 41 to 43", 4) == [(4, 41, 43)]
    assert parse_pages("45", 1) == [(1, 45, 45)]
    assert parse_pages("page 7", 2) == [(2, 7, 7)]
    assert parse_pages("pages 10 to 12, 15, 20 to 22", 3) == [(3, 10, 12), (3, 15, 15),
                                                              (3, 20, 22)]
    assert parse_pages("pages 3 and 5 to 6", 1) == [(1, 3, 3), (1, 5, 6)]
    assert parse_pages("IUT III pages 173 to 174; IUT IV page 23", 3) == [(3, 173, 174),
                                                                         (4, 23, 23)]
    assert parse_pages("III pages 173 to 174; IV page 23", 3) == [(3, 173, 174), (4, 23, 23)]
    for bad in ("", "pages 12 to 10", "see page 3", "pages 3-5", "p. 4", None, "III 4"):
        assert parse_pages(bad, 1) is None, bad
    assert format_spans([(3, 173, 174), (4, 23, 23)], 3) == "III 173 to 174; IV 23"
    assert format_spans([(3, 10, 12), (3, 15, 15)], 3) == "10 to 12, 15"
    rec = {"id": "IUT3.X.frag.y", "kind": "fragment", "parent": "IUT4.Z",
           "source": {"pdf_pages": "III pages 173 to 174; IV page 23"}}
    assert reviewed_pages(rec) == (173, 174)
    errs = structural_errors([rec, {"id": "IUT4.Z", "statement_status": "NOT_EXTRACTED",
                                    "proof_status": "NOT_EXTRACTED", "fragments": ["IUT3.X.frag.y"]}])
    assert any("the id has the prefix IUT3.X, but the parent is IUT4.Z" in e for e in errs), errs
    decls = {"A.b": {"kind": "theorem", "axioms": ["propext", "sorryAx"]}}
    cond = {"id": "IUT1.Q.frag.b", "lean_declaration": "A.b",
            "proof_status": "CONDITIONALLY_VERIFIED"}
    assert any("depends on sorryAx" in e for e in declaration_errors([cond], decls, set())), \
        "a conditional record with sorryAx must be an error"
    ext = {"id": "ZHOU1.Thm3_2", "kind": EXTERNAL_STATEMENT, "statement_status": "EXTRACTED",
           "proof_status": "NOT_EXTRACTED", "content": "c", "conclusion": "c",
           "explicit_hypotheses": [], "curated_in": "external.json",
           "source": {"authors": "Z.-P. Zhou", "title": "t", "arxiv": "2503.14510",
                      "statement": "Theorem 3.2", "pages_in_paper": "pages 27 to 29"}}
    assert parent_of(ext["id"], ext) is None
    assert page_spans(ext) == [(None, 27, 29)]
    assert structural_errors([ext]) == [], structural_errors([ext])
    bad = dict(ext, id="ZHOU1.Thm3_3", source=dict(ext["source"], arxiv="2510.05448",
                                                   pdf_pages="page 3"))
    errs = structural_errors([bad])
    assert any("source.pdf_pages holds pages of IUT I to IV" in e for e in errs), errs
    assert any("is not an identifier of ZHOU1" in e for e in errs), errs
    claim = dict(ext, id="ZHOU1.Cor3_3", lean_declaration="A.c", proof_status="KERNEL_VERIFIED",
                 statement_status="STATEMENT_FORMALIZED")
    assert any("STATEMENT_FORMALIZED and EXTERNAL_CLAIM" in e for e in structural_errors([claim]))
    wrong = {"id": "IUT1.X", "proof_status": "EXTERNAL_CLAIM", "statement_status": "EXTRACTED"}
    assert any("only the proof status of an external_statement" in e
               for e in structural_errors([wrong]))
    print("records self-test OK")


if __name__ == "__main__":
    _self_test()
