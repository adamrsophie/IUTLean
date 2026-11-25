#!/usr/bin/env python3
"""Formalization status dashboard.

Usage: python3 scripts/dashboard.py   (after extract_statements.py merge and build_graph.py)

Writes docs/DASHBOARD.md and data/dashboard.json. Every number is computed from
data/statements.json (mechanical index merged with data/curated/*.json),
data/dependency_graph.json, data/lean_declarations.json and data/countermodels.json. The
statuses that drive the counts are written by hand in data/curated/*.json; this script only
checks them against the rules of scripts/records.py and against the Lean inventory. It exits
nonzero, after writing, if a record is invalid (scripts/records.py: unknown status, parent
that is not a record, formalized or verified status without a declaration, EXTRACTED without
content, hypotheses and conclusion) or if a declaration named in data/ is not in the
inventory.

Definitions used for the counts. A record is a fragment when its kind is "fragment"; every
other record is a statement record (a numbered or lettered statement, a part or proof step,
or an unnumbered section item).
  formalized in full     statement record, statement_status STATEMENT_FORMALIZED or
                         STATEMENT_REVIEWED, and the named lean_declaration exists
  proved in full, unconditional  formalized in full, proof_status KERNEL_VERIFIED or
                         INDEPENDENTLY_CHECKED, and the declaration depends only on the
                         allowed axioms
  proved in full, conditional    formalized in full and proof_status CONDITIONALLY_VERIFIED
  fragments checked      fragment records whose declaration exists, other than model tests;
                         unconditional when KERNEL_VERIFIED, conditional when
                         CONDITIONALLY_VERIFIED, in both cases only when the declaration
                         depends on the allowed axioms alone (otherwise the record is a
                         validation error). A parent is never counted through them.
  model tests            fragment records with scope "model_test" (scripts/records.py): a
                         declaration that tests a model or an example rather than checking a
                         step of the papers; counted when a theorem with a proof status of
                         the proved family and allowed axioms, never among fragments checked
  record kinds           the status tables and the status totals are split into full
                         statements (records without a parent), parts and steps (records
                         with a parent, not fragments) and fragments
  obligation entries     items of the obligations lists (open claims and notes alike, as the
                         curated files write them), and the number of records with one
  BLOCKED_BY_EXTERNAL_THEOREM  records with that proof status
  countermodel catalog   the entries of data/countermodels.json by their kind
  unauthorized axioms    axioms other than propext, Classical.choice, Quot.sound that a
                         project declaration depends on, and declarations of kind axiom
  placeholders           project declarations that depend on sorryAx
  other papers           records whose id has a prefix of records.EXTERNAL_PAPERS (statements
                         of other papers and their fragments) are left out of every count
                         above and reported in their own section and in the "external" part
                         of data/dashboard.json; a conditional fragment shows what it assumes
"""
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path

import records

ROOT = Path(__file__).resolve().parent.parent
ALLOWED = records.ALLOWED_AXIOMS
FIDELITY = ["NOT_EXTRACTED", "EXTRACTED", "INTERPRETATION_AMBIGUOUS", "LEAN_STATEMENT_DRAFT",
            "STATEMENT_FORMALIZED", "STATEMENT_REVIEWED"]
PROOF = ["NOT_EXTRACTED", "EXTRACTED", "PROOF_IN_PROGRESS", "BLOCKED_BY_MATHLIB",
         "BLOCKED_BY_EXTERNAL_THEOREM", "BLOCKED_BY_MISSING_JUSTIFICATION",
         "CONDITIONALLY_VERIFIED", "KERNEL_VERIFIED", "INDEPENDENTLY_CHECKED",
         "COUNTERMODEL_FOUND"]
KINDS = ["full_statements", "parts_and_steps", "fragments"]
KIND_TITLES = {"full_statements": "Full statements", "parts_and_steps": "Parts and proof steps",
               "fragments": "Fragments"}
COUNTERMODEL_KINDS = {"countermodel": "Countermodels (of a simplified abstraction unless the "
                                      "entry says otherwise)",
                      "positive": "Positive results", "lemma": "Lemmas"}


def load(name, default=None):
    path = ROOT / "data" / name
    return json.loads(path.read_text()) if path.exists() else default


def table(rows, header):
    lines = ["| " + " | ".join(header) + " |", "|" + "---|" * len(header)]
    return "\n".join(lines + ["| " + " | ".join(str(c) for c in r) + " |" for r in rows])


def main():
    statements = load("statements.json")
    graph = load("dependency_graph.json")
    lean = load("lean_declarations.json")
    countermodels = load("countermodels.json", {"entries": []})
    decls = {d["name"]: d for d in lean["declarations"]}
    critical = set(graph["analysis"]["critical_path"])
    errors = records.structural_errors(statements)
    errors += records.declaration_errors(statements, decls, set(lean["modules"]))
    external = [s for s in statements if records.external_prefix(s["id"])]
    statements = [s for s in statements if not records.external_prefix(s["id"])]

    def exists(s):
        return s.get("lean_declaration") in decls

    def clean_axioms(s):
        return exists(s) and set(decls[s["lean_declaration"]]["axioms"]) <= ALLOWED

    def theorem(s):
        return exists(s) and records.is_theorem(decls[s["lean_declaration"]])

    def typed_definition(s):
        return exists(s) and not theorem(s)

    def formalized(s):
        return (not records.is_fragment(s) and s.get("statement_status") in records.FORMALIZED
                and exists(s))

    def proved(s):
        return (formalized(s) and theorem(s) and s.get("proof_status") in records.VERIFIED
                and clean_axioms(s))

    def conditional(s):
        return formalized(s) and theorem(s) and s.get("proof_status") == "CONDITIONALLY_VERIFIED"

    def frag_unconditional(s):
        return (records.is_fragment(s) and not records.is_model_test(s) and theorem(s)
                and s.get("proof_status") == "KERNEL_VERIFIED" and clean_axioms(s))

    def frag_conditional(s):
        return (records.is_fragment(s) and not records.is_model_test(s) and theorem(s)
                and s.get("proof_status") == "CONDITIONALLY_VERIFIED" and clean_axioms(s))

    def model_test(s):
        return (records.is_fragment(s) and records.is_model_test(s) and theorem(s)
                and s.get("proof_status") in records.PROVED_FAMILY and clean_axioms(s))

    def record_kind(s):
        if records.is_fragment(s):
            return "fragments"
        return "parts_and_steps" if s.get("parent") else "full_statements"

    def ambiguous(s):
        return s.get("statement_status") == "INTERPRETATION_AMBIGUOUS" or bool(s.get("ambiguities"))

    paper_records = [s for s in statements if not records.is_fragment(s)]
    fragments = [s for s in statements if records.is_fragment(s)]

    def coverage(group):
        group_frag = [s for s in fragments if s.get("parent") in {g["id"] for g in group}]
        return {"statement_records": len(group),
                "extracted_by_reading": sum(s.get("statement_status") != "NOT_EXTRACTED"
                                            for s in group),
                "formalized_in_full": sum(formalized(s) for s in group),
                "proved_in_full_unconditional": sum(proved(s) for s in group),
                "proved_in_full_conditional": sum(conditional(s) for s in group),
                "fragments_checked": sum(frag_unconditional(s) or frag_conditional(s)
                                         for s in group_frag),
                "ambiguous": sum(ambiguous(s) for s in group)}

    indexed_ids = {m["id"] for m in load("mechanical_index.json")}
    indexed = [s for s in paper_records if s["id"] in indexed_ids]
    section_items = [s for s in paper_records if records.SECTION_ITEM.match(s["id"])]
    parts = [s for s in paper_records if s.get("parent")]
    obligations = [(s["id"], o) for s in statements for o in (s.get("obligations") or [])]
    claimed_missing = sorted(s["id"] for s in statements
                             if s.get("lean_declaration") and not exists(s))
    unconfirmed = sorted(s["id"] for s in paper_records
                         if s.get("proof_status") in records.VERIFIED and not proved(s))
    bad_axioms = sorted({(d["name"], a) for d in decls.values() for a in d["axioms"]
                         if a not in ALLOWED})
    axiom_decls = sorted(d["name"] for d in decls.values() if d["kind"] == "axiom")
    placeholders = sorted(d["name"] for d in decls.values() if "sorryAx" in d["axioms"])
    on_disk = sorted(".".join(p.relative_to(ROOT).with_suffix("").parts)
                     for base in ("IUT", "Challenge") for p in (ROOT / base).rglob("*.lean"))
    not_built = [m for m in on_disk if m not in lean["modules"]
                 and not m.startswith("IUT.Experimental")]
    extracted_proof_open = sum(s.get("statement_status") not in ("NOT_EXTRACTED", None)
                               and s.get("proof_status") == "NOT_EXTRACTED"
                               for s in paper_records)
    catalog = Counter(e.get("kind") for e in countermodels.get("entries", []))
    fragment_rows = sorted(
        ([f"`{f['id']}`", f"`{f.get('parent')}`", f"`{f.get('lean_declaration')}`",
          decls[f["lean_declaration"]]["kind"] if exists(f) else "not found",
          f.get("proof_status"), "model test" if records.is_model_test(f) else ""]
         for f in fragments), key=lambda r: r[0])

    per_paper = {f"IUT{p}": coverage([s for s in paper_records if s.get("paper") == p])
                 for p in range(1, 5)}
    data = {
        "statements_indexed": len(indexed_ids),
        "statements_by_kind": dict(sorted(Counter(s.get("kind") for s in indexed).items())),
        "curated_parts_and_steps": len(parts),
        "unnumbered_section_items": len(section_items),
        "fragments": len(fragments),
        "curated_records": sum(bool(s.get("curated_in")) for s in statements),
        "extracted_by_reading": sum(s.get("statement_status") != "NOT_EXTRACTED"
                                    for s in paper_records),
        "extracted_statement_with_proof_status_not_extracted": extracted_proof_open,
        "formalized_in_full": sum(formalized(s) for s in statements),
        "proved_in_full_unconditional": sum(proved(s) for s in statements),
        "proved_in_full_conditional": sum(conditional(s) for s in statements),
        "fragments_checked_unconditional": sum(frag_unconditional(s) for s in fragments),
        "fragments_checked_conditional": sum(frag_conditional(s) for s in fragments),
        "model_tests": sum(model_test(s) for s in fragments),
        "model_test_records": sorted(s["id"] for s in fragments if records.is_model_test(s)),
        "definitions_typed_in_lean": sum(typed_definition(s) for s in statements),
        "parents_with_checked_fragments": sorted({f["parent"] for f in fragments
                                                  if frag_unconditional(f) or frag_conditional(f)}),
        "obligation_entries": len(obligations),
        "records_with_obligations": len({i for i, _ in obligations}),
        "ambiguous": sum(ambiguous(s) for s in paper_records),
        "blocked_by_external_theorem": sum(s.get("proof_status") == "BLOCKED_BY_EXTERNAL_THEOREM"
                                           for s in paper_records),
        "external_keys_on_critical_path": len(graph["analysis"]["external_keys_on_critical_path"]),
        "countermodel_statuses": sum(s.get("statement_status") == "COUNTERMODEL_FOUND"
                                     or s.get("proof_status") == "COUNTERMODEL_FOUND"
                                     for s in statements),
        "countermodel_catalog": dict(sorted(catalog.items(), key=lambda kv: str(kv[0]))),
        "unauthorized_axioms": [{"declaration": n, "axiom": a} for n, a in bad_axioms],
        "axiom_declarations": axiom_decls,
        "placeholders": placeholders,
        "lean_declarations_claimed_but_missing": claimed_missing,
        "verified_status_not_confirmed": unconfirmed,
        "validation_errors": errors,
        "lean_modules_checked": lean["modules"],
        "lean_modules_on_disk_not_checked": not_built,
        "statement_status": {kind: dict(sorted(Counter(
            s.get("statement_status") for s in statements if record_kind(s) == kind).items()))
            for kind in KINDS},
        "proof_status": {kind: dict(sorted(Counter(
            s.get("proof_status") for s in statements if record_kind(s) == kind).items()))
            for kind in KINDS},
        "coverage_per_paper": per_paper,
        "coverage_critical_path": coverage([s for s in paper_records if s["id"] in critical]),
        "external": {
            "statements": sum(not records.is_fragment(s) for s in external),
            "stated_in_lean": sum(not records.is_fragment(s) and exists(s)
                                  and s.get("proof_status") == "EXTERNAL_CLAIM"
                                  for s in external),
            "fragments_checked_unconditional": sum(frag_unconditional(s) for s in external),
            "fragments_checked_conditional": sum(frag_conditional(s) for s in external),
            "by_paper": dict(sorted(Counter(records.external_prefix(s["id"])
                                            for s in external).items())),
        },
    }
    (ROOT / "data" / "dashboard.json").write_text(
        json.dumps(data, indent=1, ensure_ascii=False, sort_keys=True) + "\n")

    cov_rows = [[k] + list(v.values()) for k, v in per_paper.items()]
    cov_rows.append(["Critical path"] + list(data["coverage_critical_path"].values()))
    cov_header = ["Scope", "Statement records", "Extracted by reading", "Formalized in full",
                  "Proved in full, unconditional", "Proved in full, conditional",
                  "Fragments checked (of these parents)", "Ambiguous"]
    by_paper = {kind: defaultdict(Counter) for kind in KINDS}
    by_paper_proof = {kind: defaultdict(Counter) for kind in KINDS}
    for s in statements:
        by_paper[record_kind(s)][s.get("paper")][s.get("statement_status")] += 1
        by_paper_proof[record_kind(s)][s.get("paper")][s.get("proof_status")] += 1

    def status_table(counts, order):
        seen = order + sorted({k for c in counts.values() for k in c if k not in order},
                              key=str)
        seen = [k for k in seen if any(c.get(k) for c in counts.values())]
        rows = [[k] + [counts[p].get(k, 0) for p in range(1, 5)] for k in seen]
        return table(rows, ["Status", "IUT1", "IUT2", "IUT3", "IUT4"]) if rows else "None."

    def status_tables(counts, order):
        out = []
        for kind in KINDS:
            out += [f"### {KIND_TITLES[kind]}", "", status_table(counts[kind], order), ""]
        return out

    def assumes(s):
        if s.get("proof_status") != "CONDITIONALLY_VERIFIED":
            return ""
        return "; ".join(str(o) for o in s.get("obligations") or [])

    external_rows = [[f"`{s['id']}`", s.get("kind"),
                      f"`{s.get('parent')}`" if s.get("parent") else "",
                      f"`{s['lean_declaration']}`" if s.get("lean_declaration") else "",
                      s.get("statement_status"), s.get("proof_status"), assumes(s)]
                     for s in sorted(external, key=lambda s: s["id"])]
    external_doc = [
        "## Statements of other papers", "",
        "Records whose id has a prefix of `records.EXTERNAL_PAPERS`: results and claims of "
        "other papers (" + "; ".join(f"`{k}`: {v[0]}" for k, v in
                                    records.EXTERNAL_PAPERS.items()) + "), and the Lean "
        "fragments that check pieces of them. They are not counted in any number above or "
        "in the tables of the four papers. A statement with proof status EXTERNAL_CLAIM is "
        "stated in Lean as a proposition and only assumed. \"Assumes\" gives, for a "
        "conditional fragment, the claims its theorem takes as hypotheses.", "",
        table([["Statements of other papers", data["external"]["statements"]],
               ["Of these, stated in Lean (EXTERNAL_CLAIM, assumed, not proved)",
                data["external"]["stated_in_lean"]],
               ["Their fragments checked in Lean, unconditionally",
                data["external"]["fragments_checked_unconditional"]],
               ["Their fragments checked in Lean, conditionally",
                data["external"]["fragments_checked_conditional"]]], ["Measure", "Count"]), "",
        table(external_rows, ["Id", "Kind", "Parent", "Lean declaration", "Statement",
                              "Proof", "Assumes"]) if external_rows else "None yet.", ""]

    def listing(items):
        return "\n".join(f"- `{i}`" for i in items) if items else "None."

    legend = [f"{k}: {v}." for k, v in sorted(records.LEGEND.items())]
    doc = ["# Formalization dashboard", "",
           "Generated by `scripts/dashboard.py` from `data/statements.json`, "
           "`data/dependency_graph.json`, `data/lean_declarations.json` and "
           "`data/countermodels.json`. Do not edit by hand; rerun the scripts (see "
           "`scripts/README.md`). Machine-readable form: `data/dashboard.json`. The statuses "
           "behind the counts are written by hand in `data/curated/*.json`; the scripts check "
           "them against fixed rules and against the Lean inventory, not against the papers.", "",
           "Progress is measured by statements and their statuses, not by lines of Lean or "
           "numbers of files. Statement fidelity (is the statement extracted and faithfully "
           "stated in Lean?) and proof status (is it proved, and under which hypotheses?) are "
           "reported separately.", "",
           "A statement counts as formalized only when one Lean declaration states its entire "
           "content. A Lean lemma that checks one step or one arithmetic piece of a statement "
           "is a fragment record of its own (`<parent>.frag.<name>`); fragments are counted "
           "separately, and a parent is never counted as formalized or proved through its "
           "fragments.", "",
           "## Summary", "",
           table([
               ["Statements in the mechanical index (numbered and lettered)",
                data["statements_indexed"]],
               ["Curated parts and proof steps", data["curated_parts_and_steps"]],
               ["Curated unnumbered items of a section", data["unnumbered_section_items"]],
               ["Statement records extracted by reading (statement status other than "
                "NOT_EXTRACTED)", data["extracted_by_reading"]],
               ["Statement records formalized in full", data["formalized_in_full"]],
               ["Statement records proved in full, unconditionally",
                data["proved_in_full_unconditional"]],
               ["Statement records proved in full, conditionally (named hypotheses)",
                data["proved_in_full_conditional"]],
               ["Fragments checked in Lean, unconditionally",
                data["fragments_checked_unconditional"]],
               ["Fragments checked in Lean, conditionally", data["fragments_checked_conditional"]],
               ["Model tests (fragments that test a model or an example, not a step of the "
                "papers; scope model_test)", data["model_tests"]],
               ["Records (statements and fragments) whose declaration is a definition, "
                "structure or other non-theorem typed in Lean (never counted as proved)",
                data["definitions_typed_in_lean"]],
               ["Parents with at least one checked fragment (not counted as formalized)",
                len(data["parents_with_checked_fragments"])],
               ["Obligation entries (items of the obligations lists, open claims and notes "
                "alike)", data["obligation_entries"]],
               ["Records with at least one obligation entry", data["records_with_obligations"]],
               ["Statement records with an ambiguity (status INTERPRETATION_AMBIGUOUS or a "
                "nonempty ambiguities list)", data["ambiguous"]],
               ["Statement records with proof status BLOCKED_BY_EXTERNAL_THEOREM",
                data["blocked_by_external_theorem"]],
               ["External bibliography keys cited by critical-path statements",
                data["external_keys_on_critical_path"]],
               ["Records with status COUNTERMODEL_FOUND", data["countermodel_statuses"]],
               ["Unauthorized axioms", len(bad_axioms) + len(axiom_decls)],
               ["Proof placeholders (sorryAx)", len(placeholders)],
               ["Validation errors of the records", len(errors)],
           ], ["Measure", "Count"]), "",
           "## Countermodel catalog", "",
           "Entries of `data/countermodels.json`, by the kind that each entry gives itself. A "
           "countermodel refutes a simplified abstraction unless its entry says otherwise; it "
           "is not by itself a counterexample to a statement of the papers.", "",
           table([[COUNTERMODEL_KINDS.get(k, str(k)), n]
                  for k, n in sorted(catalog.items(), key=lambda kv: str(kv[0]))]
                 or [["None", 0]], ["Kind", "Entries"]), "",
           "## Fragments", "",
           "Each row is one Lean lemma that checks a piece of the parent named. The parent "
           "keeps its own status.", "",
           table(fragment_rows, ["Fragment", "Parent", "Lean declaration", "Declaration kind",
                                 "Proof status", "Scope"]) if fragment_rows else "None yet.", "",
           "## Coverage per paper and on the critical path", "",
           "Statement records only; the fragment column counts checked fragments whose parent "
           "is in the row. The critical path is defined in `docs/CRITICAL_PATH.md`; it is "
           "built from mechanical citations and curated edges, and it both over-approximates "
           "logical dependence (citations for comparison or motivation are edges) and "
           "under-approximates it (citations not written as \"Kind N.M\", citations of "
           "targets that are not indexed, and uses the text does not cite are missing).", "",
           table(cov_rows, cov_header), "",
           "## Statement fidelity status", "",
           "One table per kind of record, so that no table adds fragments to statements: full "
           "statements (numbered statements and unnumbered section items, no parent), parts and "
           "proof steps (records with a parent), and fragments.", ""] + status_tables(by_paper, FIDELITY) + [
           "## Proof status", ""] + status_tables(by_paper_proof, PROOF) + [
           "Statement status NOT_EXTRACTED means that the statement is not yet recorded to the "
           "standard of an extracted statement (content, hypotheses and conclusion from pages "
           "read); the record may already hold partial content. Proof status NOT_EXTRACTED "
           "means that no proof has been recorded to that standard, and it is also the proof "
           f"status of a record whose Lean declaration is a definition. {extracted_proof_open} "
           "statement records have a statement status other than NOT_EXTRACTED and proof "
           "status NOT_EXTRACTED.", ""] + legend + ["",
           ] + external_doc + [
           "## Validation of the records", "",
           "Rules of `scripts/records.py`. Any line here makes `scripts/dashboard.py` and the "
           "continuous integration fail.", "", listing(errors), "",
           "## Trust checks on the Lean library", "",
           f"Modules checked: {len(lean['modules'])}. Allowed axioms: "
           + ", ".join(sorted(ALLOWED)) + ".", "",
           "Unauthorized axioms:", "",
           listing([f"{n}: {a}" for n, a in bad_axioms] + [f"{n} (declared axiom)"
                                                          for n in axiom_decls]), "",
           "Declarations depending on sorryAx:", "", listing(placeholders), "",
           "Lean declarations named by a record but missing from the built library:", "",
           listing(claimed_missing), "",
           "Statement records whose proof status says verified but that fail the checks above "
           "(no formalized statement status, declaration missing, or disallowed axioms); they "
           "are not counted as proved:", "", listing(unconfirmed), "",
           "Modules on disk that the inventory did not see (not imported by `IUT.lean`, or "
           "not built when `scripts/LeanDeclarations.lean` last ran):", "",
           listing(not_built), ""]
    (ROOT / "docs" / "DASHBOARD.md").write_text("\n".join(doc))
    print(f"dashboard: {data['statements_indexed']} indexed, {data['extracted_by_reading']} "
          f"read, {data['formalized_in_full']} formalized in full, "
          f"{data['proved_in_full_unconditional']} proved in full, {len(fragments)} fragments")
    for e in errors:
        print("error: " + e, file=sys.stderr)
    if errors:
        sys.exit(f"dashboard: {len(errors)} validation errors")


if __name__ == "__main__":
    main()
