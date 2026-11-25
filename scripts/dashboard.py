#!/usr/bin/env python3
"""Formalization status dashboard.

Usage: python3 scripts/dashboard.py   (after extract_statements.py and build_graph.py)

Writes docs/DASHBOARD.md and data/dashboard.json. Every number is computed from
data/statements.json (mechanical index merged with data/curated/*.json),
data/dependency_graph.json and data/lean_declarations.json. Nothing is typed by hand.

Definitions used for the counts:
  formalized            statement_status STATEMENT_FORMALIZED or STATEMENT_REVIEWED, and the
                        named lean_declaration exists in the built library
  unconditional verified  formalized, proof_status KERNEL_VERIFIED or INDEPENDENTLY_CHECKED,
                        and the declaration depends only on the allowed axioms
  conditional           proof_status CONDITIONALLY_VERIFIED
  unresolved obligations  entries of the obligations lists of all records
  ambiguous             statement_status INTERPRETATION_AMBIGUOUS, or a nonempty
                        ambiguities list
  external gaps         records with proof_status BLOCKED_BY_EXTERNAL_THEOREM; separately,
                        the bibliography keys cited by critical-path statements
  countermodels         records with status COUNTERMODEL_FOUND; separately, theorems in the
                        Lean modules IUT.Countermodels.*
  unauthorized axioms   axioms other than propext, Classical.choice, Quot.sound that a
                        project declaration depends on, and declarations of kind axiom
  placeholders          project declarations that depend on sorryAx
"""
import json
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FIDELITY = ["NOT_EXTRACTED", "EXTRACTED", "INTERPRETATION_AMBIGUOUS", "LEAN_STATEMENT_DRAFT",
            "STATEMENT_FORMALIZED", "STATEMENT_REVIEWED"]
PROOF = ["NOT_EXTRACTED", "EXTRACTED", "PROOF_IN_PROGRESS", "BLOCKED_BY_MATHLIB",
         "BLOCKED_BY_EXTERNAL_THEOREM", "BLOCKED_BY_MISSING_JUSTIFICATION",
         "CONDITIONALLY_VERIFIED", "KERNEL_VERIFIED", "INDEPENDENTLY_CHECKED",
         "COUNTERMODEL_FOUND"]
FORMALIZED = {"STATEMENT_FORMALIZED", "STATEMENT_REVIEWED"}
VERIFIED = {"KERNEL_VERIFIED", "INDEPENDENTLY_CHECKED"}


def load(name, default=None):
    path = ROOT / "data" / name
    return json.loads(path.read_text()) if path.exists() else default


def table(rows, header):
    lines = ["| " + " | ".join(header) + " |", "|" + "---|" * len(header)]
    return "\n".join(lines + ["| " + " | ".join(str(c) for c in r) + " |" for r in rows])


def main():
    statements = load("statements.json")
    graph = load("dependency_graph.json")
    lean = load("lean_declarations.json", {"modules": [], "declarations": []})
    decls = {d["name"]: d for d in lean["declarations"]}
    critical = set(graph["analysis"]["critical_path"])

    def formalized(s):
        return s.get("statement_status") in FORMALIZED and s.get("lean_declaration") in decls

    def verified(s):
        d = decls.get(s.get("lean_declaration"))
        return (formalized(s) and s.get("proof_status") in VERIFIED
                and set(d["axioms"]) <= ALLOWED)

    def ambiguous(s):
        return s.get("statement_status") == "INTERPRETATION_AMBIGUOUS" or bool(s.get("ambiguities"))

    def coverage(group):
        return {"statements": len(group),
                "extracted_by_reading": sum(s.get("statement_status") != "NOT_EXTRACTED"
                                            for s in group),
                "formalized": sum(formalized(s) for s in group),
                "unconditional_verified": sum(verified(s) for s in group),
                "conditional": sum(s.get("proof_status") == "CONDITIONALLY_VERIFIED"
                                   for s in group),
                "ambiguous": sum(ambiguous(s) for s in group)}

    indexed = [s for s in statements if not s.get("parent")]
    parts = [s for s in statements if s.get("parent")]
    obligations = [(s["id"], o) for s in statements for o in (s.get("obligations") or [])]
    claimed_missing = sorted(s["id"] for s in statements
                             if s.get("lean_declaration") and s["lean_declaration"] not in decls)
    unconfirmed = sorted(s["id"] for s in statements
                         if s.get("proof_status") in VERIFIED and not verified(s))
    bad_axioms = sorted({(d["name"], a) for d in decls.values() for a in d["axioms"]
                         if a not in ALLOWED})
    axiom_decls = sorted(d["name"] for d in decls.values() if d["kind"] == "axiom")
    placeholders = sorted(d["name"] for d in decls.values() if "sorryAx" in d["axioms"])
    countermodel_theorems = sorted(d["name"] for d in decls.values()
                                   if d["module"].startswith("IUT.Countermodels")
                                   and d["kind"] == "theorem" and not d["internal"])
    on_disk = sorted(".".join(p.relative_to(ROOT).with_suffix("").parts)
                     for base in ("IUT", "Challenge") for p in (ROOT / base).rglob("*.lean"))
    not_built = [m for m in on_disk if m not in lean["modules"]
                 and not m.startswith("IUT.Experimental")]

    per_paper = {f"IUT{p}": coverage([s for s in statements if s.get("paper") == p])
                 for p in range(1, 5)}
    data = {
        "statements_indexed": len(indexed),
        "statements_by_kind": dict(sorted(Counter(s.get("kind") for s in indexed).items())),
        "curated_parts_and_steps": len(parts),
        "curated_records": sum(bool(s.get("curated_in")) for s in statements),
        "extracted_by_reading": sum(s.get("statement_status") != "NOT_EXTRACTED"
                                    for s in statements),
        "formalized": sum(formalized(s) for s in statements),
        "unconditional_verified": sum(verified(s) for s in statements),
        "conditional": sum(s.get("proof_status") == "CONDITIONALLY_VERIFIED" for s in statements),
        "unresolved_obligations": len(obligations),
        "records_with_obligations": len({i for i, _ in obligations}),
        "ambiguous": sum(ambiguous(s) for s in statements),
        "external_prerequisite_gaps": sum(s.get("proof_status") == "BLOCKED_BY_EXTERNAL_THEOREM"
                                          for s in statements),
        "external_keys_on_critical_path": len(graph["analysis"]["external_keys_on_critical_path"]),
        "countermodel_statuses": sum(s.get("statement_status") == "COUNTERMODEL_FOUND"
                                     or s.get("proof_status") == "COUNTERMODEL_FOUND"
                                     for s in statements),
        "countermodel_theorems_in_lean": len(countermodel_theorems),
        "unauthorized_axioms": [{"declaration": n, "axiom": a} for n, a in bad_axioms],
        "axiom_declarations": axiom_decls,
        "placeholders": placeholders,
        "lean_declarations_claimed_but_missing": claimed_missing,
        "verified_status_not_confirmed": unconfirmed,
        "lean_modules_checked": lean["modules"],
        "lean_modules_on_disk_not_checked": not_built,
        "statement_status": dict(sorted(Counter(s.get("statement_status")
                                                for s in statements).items())),
        "proof_status": dict(sorted(Counter(s.get("proof_status") for s in statements).items())),
        "coverage_per_paper": per_paper,
        "coverage_critical_path": coverage([s for s in statements if s["id"] in critical]),
    }
    (ROOT / "data" / "dashboard.json").write_text(
        json.dumps(data, indent=1, ensure_ascii=False, sort_keys=True) + "\n")

    cov_rows = [[k] + list(v.values()) for k, v in per_paper.items()]
    cov_rows.append(["Critical path"] + list(data["coverage_critical_path"].values()))
    cov_header = ["Scope", "Statements", "Extracted by reading", "Formalized",
                  "Unconditional verified", "Conditional", "Ambiguous"]
    by_paper = defaultdict(Counter)
    by_paper_proof = defaultdict(Counter)
    for s in statements:
        by_paper[s.get("paper")][s.get("statement_status")] += 1
        by_paper_proof[s.get("paper")][s.get("proof_status")] += 1

    def status_table(counts, order):
        seen = order + sorted({k for c in counts.values() for k in c if k not in order},
                              key=str)
        seen = [k for k in seen if any(c.get(k) for c in counts.values())]
        rows = [[k] + [counts[p].get(k, 0) for p in range(1, 5)] for k in seen]
        return table(rows, ["Status", "IUT1", "IUT2", "IUT3", "IUT4"])

    def listing(items):
        return "\n".join(f"- `{i}`" for i in items) if items else "None."

    doc = ["# Formalization dashboard", "",
           "Generated by `scripts/dashboard.py` from `data/statements.json`, "
           "`data/dependency_graph.json` and `data/lean_declarations.json`. Do not edit by "
           "hand; rerun the scripts (see `scripts/README.md`). Machine-readable form: "
           "`data/dashboard.json`.", "",
           "Progress is measured by statements and their statuses, not by lines of Lean or "
           "numbers of files. Statement fidelity (is the statement extracted and faithfully "
           "stated in Lean?) and proof status (is it proved, and under which hypotheses?) are "
           "reported separately.", "",
           "## Summary", "",
           table([
               ["Statements in the index (numbered and lettered)", data["statements_indexed"]],
               ["Curated parts and proof steps", data["curated_parts_and_steps"]],
               ["Records extracted by reading (status other than NOT_EXTRACTED)",
                data["extracted_by_reading"]],
               ["Formalized statements", data["formalized"]],
               ["Unconditional verified results", data["unconditional_verified"]],
               ["Conditional results", data["conditional"]],
               ["Unresolved obligations (in records)",
                f"{data['unresolved_obligations']} (in {data['records_with_obligations']} records)"],
               ["Ambiguous statements", data["ambiguous"]],
               ["External prerequisite gaps (BLOCKED_BY_EXTERNAL_THEOREM)",
                data["external_prerequisite_gaps"]],
               ["External bibliography keys cited on the critical path",
                data["external_keys_on_critical_path"]],
               ["Countermodels (status COUNTERMODEL_FOUND)", data["countermodel_statuses"]],
               ["Countermodel theorems in IUT.Countermodels", data["countermodel_theorems_in_lean"]],
               ["Unauthorized axioms", len(bad_axioms) + len(axiom_decls)],
               ["Proof placeholders (sorryAx)", len(placeholders)],
           ], ["Measure", "Count"]), "",
           "A countermodel theorem in Lean refutes a simplified abstraction unless its "
           "docstring says otherwise; it is not by itself a counterexample to a statement of "
           "the papers.", "",
           "## Coverage per paper and on the critical path", "",
           "The critical path is defined in `docs/CRITICAL_PATH.md`; it is an over-approximation "
           "built from mechanical citations.", "",
           table(cov_rows, cov_header), "",
           "## Statement fidelity status", "", status_table(by_paper, FIDELITY), "",
           "## Proof status", "", status_table(by_paper_proof, PROOF), "",
           "NOT_EXTRACTED in either table means that only the mechanical index has seen the "
           "statement: its location is known, its content has not been read.", "",
           "## Trust checks on the Lean library", "",
           f"Modules checked: {len(lean['modules'])}. Allowed axioms: "
           + ", ".join(sorted(ALLOWED)) + ".", "",
           "Unauthorized axioms:", "",
           listing([f"{n}: {a}" for n, a in bad_axioms] + [f"{n} (declared axiom)"
                                                          for n in axiom_decls]), "",
           "Declarations depending on sorryAx:", "", listing(placeholders), "",
           "Lean declarations named by a record but missing from the built library:", "",
           listing(claimed_missing), "",
           "Records whose proof status says verified but that fail the checks above (no "
           "formalized statement status, declaration missing, or disallowed axioms); they are "
           "not counted as verified:", "", listing(unconfirmed), "",
           "Modules on disk that the inventory did not see (not imported by `IUT.lean`, or "
           "not built when `scripts/LeanDeclarations.lean` last ran):", "",
           listing(not_built), ""]
    (ROOT / "docs" / "DASHBOARD.md").write_text("\n".join(doc))
    print(f"dashboard: {data['statements_indexed']} indexed, {data['extracted_by_reading']} "
          f"read, {data['formalized']} formalized, {data['unconditional_verified']} verified")


if __name__ == "__main__":
    main()
