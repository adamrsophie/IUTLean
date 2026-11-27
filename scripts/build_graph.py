#!/usr/bin/env python3
"""Dependency graph of the four IUT papers and of the Lean library.

Usage: python3 scripts/build_graph.py

Reads data/statements.json, data/dependencies.json, data/references.json and
data/lean_declarations.json. Writes

  data/dependency_graph.json   nodes, typed edges and the analyses below
  docs/DEPENDENCY_GRAPH.md     what the graph contains and its structure
  docs/CRITICAL_PATH.md        everything the derivation of abc cites, transitively
  docs/dependency_graph.svg    the critical path, rendered with Graphviz `dot`

Exits nonzero if Graphviz `dot` is missing or fails, or if an edge has an endpoint that is not
a node.

Node types:
  statement               a record of data/statements.json other than a fragment
  fragment                a fragment record: one Lean lemma that checks a piece of a parent
  missing_record          the parent named by a part or fragment that is not a record (an
                          invalid record, which the merge of extract_statements.py rejects)
  unresolved_citation     a citation target that is not a record (a numbered result that the
                          index does not have, or a citation of an external paper whose key
                          the text gives only once for a list)
  external_reference      a bibliography key named in a curated external_dependencies entry
  lean_declaration        a non-internal declaration of the built library
  external_lean_theorem   a theorem of Mathlib or another dependency that a project
                          declaration uses directly (edges only when there are few, see
                          MAX_EXTERNAL)

Edge kinds:
  cites_in_statement, cites_in_proof   a citation found in the statement or in the text
                                       from its "Proof." line to the next header
  cites_in_context                     for a lettered result of an Introduction: a
                                       citation in the paragraph before or after it
  part_of                              a curated part or proof step to its parent
  fragment_of                          a fragment to its parent (it does not make the
                                       parent formalized or verified)
  depends_on                           a record to a result listed in its curated
                                       results_used
  depends_on_external                  a record to an entry of its curated
                                       external_dependencies: a statement of another of
                                       the four papers, or a bibliography key
  formalized_by                        a statement or fragment to the Lean declaration
                                       that states its entire content
  lean_uses                            a Lean declaration to the project declarations its
                                       type or value mentions (contracted through internal
                                       auxiliary declarations), and to the external theorems
                                       it uses directly when there are at most MAX_EXTERNAL
"""
import json
import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

import records

ROOT = Path(__file__).resolve().parent.parent
ROOTS = ["IUT4.ThmA", "IUT4.Cor2_3"]
CITATION_KINDS = {"statement": "cites_in_statement", "proof": "cites_in_proof",
                  "context": "cites_in_context"}
# Edges followed for the critical path, as statement to what it uses. part_of is followed
# from the parent to the part. Context edges (the paragraphs around a lettered result) are not
# followed; the path computed with them is reported for comparison. Fragments are not
# followed: a fragment is a Lean check of a piece, not a step of the papers.
FOLLOWED = {"cites_in_statement", "cites_in_proof", "part_of", "depends_on",
            "depends_on_external"}
MAX_EXTERNAL = 5
RESOLVED = {"KERNEL_VERIFIED", "INDEPENDENTLY_CHECKED"}
DRAWN_KINDS = {"Theorem", "Proposition", "Corollary", "Lemma", "Definition"}
IUT_KEYS = {"IUTchI": 1, "IUTchII": 2, "IUTchIII": 3, "IUTchIV": 4}
KINDS = {"Definition": "Def", "Proposition": "Prop", "Lemma": "Lem", "Theorem": "Thm",
         "Corollary": "Cor", "Example": "Ex", "Remark": "Rem"}
EXT_KEY = re.compile(r"\[([A-Za-z][A-Za-z0-9-]*)\]|^\s*([A-Za-z][A-Za-z0-9-]*)\s*:")
EXT_ITEM = re.compile(r"(" + "|".join(KINDS) + r")\s+(\d+(?:\.\d+){1,2}|[A-Z]\b)")
NOTE = ("Citation edges are mechanical. A citation of B in the text of A is recorded as an "
        "edge A to B whether or not A logically depends on B: the text cites results for "
        "comparison, motivation and notation as well as for proof steps. The graph therefore "
        "over-approximates logical dependence in that respect. It also under-approximates "
        "it: citations not written as \"Kind N.M\" (by section, by display, by "
        "unnumbered discussion), citations whose target is not indexed, and uses that the "
        "text does not cite at all are not edges. The critical path is therefore neither an "
        "upper nor a lower bound on what the derivation of abc uses; it is a reading list "
        "for checking that derivation.")
NO_ABC_EDGE = ("There is no Lean edge from `Challenge.ABC` to IUT IV Theorem A (`IUT4.ThmA`) or "
               "to Corollary 2.3: the reduction of the abc conjecture to these statements is not "
               "formalized, and neither statement is stated in Lean. The roots of the critical "
               "path are therefore statements of the papers, not the Lean target.")


def load(name, default=None):
    path = ROOT / "data" / name
    return json.loads(path.read_text()) if path.exists() else default


def tarjan(nodes, succ):
    """Strongly connected components, iterative, in a deterministic order."""
    index, low, on_stack, stack, comps, counter = {}, {}, set(), [], [], [0]
    for root in nodes:
        if root in index:
            continue
        work = [(root, iter(succ.get(root, ())))]
        index[root] = low[root] = counter[0]
        counter[0] += 1
        stack.append(root)
        on_stack.add(root)
        while work:
            v, it = work[-1]
            advanced = False
            for w in it:
                if w not in index:
                    index[w] = low[w] = counter[0]
                    counter[0] += 1
                    stack.append(w)
                    on_stack.add(w)
                    work.append((w, iter(succ.get(w, ()))))
                    advanced = True
                    break
                if w in on_stack:
                    low[v] = min(low[v], index[w])
            if advanced:
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[v])
            if low[v] == index[v]:
                comp = []
                while True:
                    w = stack.pop()
                    on_stack.discard(w)
                    comp.append(w)
                    if w == v:
                        break
                comps.append(sorted(comp))
    return comps


def reach(roots, succ):
    """Nodes reachable from roots, with the breadth-first distance from the nearest root."""
    dist = {r: 0 for r in roots}
    frontier = list(roots)
    while frontier:
        nxt = []
        for v in frontier:
            for w in sorted(succ.get(v, ())):
                if w not in dist:
                    dist[w] = dist[v] + 1
                    nxt.append(w)
        frontier = nxt
    return dist


def contract_lean(decls):
    """Project references and external theorems of each non-internal declaration, looking
    through internal ones."""
    by_name = {d["name"]: d for d in decls}
    out, ext_out = {}, {}
    for d in decls:
        if d["internal"]:
            continue
        seen, todo, refs = {d["name"]}, list(d["refs"]), set()
        ext = set(d.get("external_theorems") or [])
        while todo:
            r = todo.pop()
            if r in seen or r not in by_name:
                continue
            seen.add(r)
            if by_name[r]["internal"]:
                todo += by_name[r]["refs"]
                ext |= set(by_name[r].get("external_theorems") or [])
            else:
                refs.add(r)
        out[d["name"]] = sorted(refs)
        ext_out[d["name"]] = sorted(ext)
    return out, ext_out


def table(rows, header):
    lines = ["| " + " | ".join(header) + " |", "|" + "---|" * len(header)]
    lines += ["| " + " | ".join(str(c).replace("|", "\\|") for c in r) + " |" for r in rows]
    return "\n".join(lines)


def pages(s):
    a, b = s.get("pdf_page"), s.get("pdf_page_end")
    if a is None:
        src = s.get("source") or {}
        return str(src.get("pdf_pages") or src.get("sections_in_paper") or "") if isinstance(src, dict) else ""
    return str(a) if b in (None, a) else f"{a} to {b}"


def external_targets(entry, by_id):
    """Node ids for one curated external_dependencies entry: a statement of one of the four
    papers (or an unresolved citation of one), or a bibliography key."""
    text = str(entry)
    m = EXT_KEY.search(text)
    if not m:
        return []
    key = m.group(1) or m.group(2)
    if key in IUT_KEYS:
        out = []
        for kind, num in EXT_ITEM.findall(text[m.end():]):
            out.append(f"IUT{IUT_KEYS[key]}.{KINDS[kind]}{num.replace('.', '_')}")
        return out or [f"ref:{key}"]
    return [f"ref:{key}"]


def main():
    statements = load("statements.json")
    citations = load("dependencies.json")
    references = {r["key"]: r for r in load("references.json")}
    lean = load("lean_declarations.json")
    by_id = {s["id"]: s for s in statements}
    fragments = {i for i, s in by_id.items() if records.is_fragment(s)}
    paper_ids = sorted(set(by_id) - fragments)

    edges = set()
    for e in citations:
        for where in e["cited_in"]:
            edges.add((e["from"], e["to"], CITATION_KINDS[where]))
    for s in statements:
        if s.get("parent"):
            edges.add((s["id"], s["parent"], "fragment_of" if s["id"] in fragments else "part_of"))
        for r in s.get("results_used") or []:
            if isinstance(r, str) and r != s["id"]:
                edges.add((s["id"], r, "depends_on"))
        for entry in s.get("external_dependencies") or []:
            for t in external_targets(entry, by_id):
                if t != s["id"]:
                    edges.add((s["id"], t, "depends_on_external"))
    lean_names = {d["name"] for d in lean["declarations"]}
    links = []
    for s in statements:
        decl = s.get("lean_declaration")
        if decl:
            links.append({"record": s["id"], "declaration": decl,
                          "scope": "fragment" if s["id"] in fragments else "whole statement",
                          "parent": s.get("parent") if s["id"] in fragments else None,
                          "declaration_found": decl in lean_names})
            edges.add((s["id"], "lean:" + decl, "formalized_by"))
    lean_refs, lean_ext = contract_lean(lean["declarations"])
    external_lean = set()
    for name, refs in lean_refs.items():
        for r in refs:
            edges.add(("lean:" + name, "lean:" + r, "lean_uses"))
        if 0 < len(lean_ext[name]) <= MAX_EXTERNAL:
            for t in lean_ext[name]:
                edges.add(("lean:" + name, "ext:" + t, "lean_uses"))
                external_lean.add(t)

    # Nodes. Every endpoint that is not a record, a declaration or an external theorem is an
    # unresolved citation or a bibliography key.
    nodes = {}
    for s in statements:
        frag = s["id"] in fragments
        nodes[s["id"]] = {"id": s["id"], "type": "fragment" if frag else "statement",
                          "paper": s.get("paper"), "kind": s.get("kind"),
                          "title": s.get("title"), "parent": s.get("parent"),
                          "statement_status": s.get("statement_status"),
                          "proof_status": s.get("proof_status"),
                          "lean_declaration": s.get("lean_declaration")}
    for d in lean["declarations"]:
        if not d["internal"]:
            nodes["lean:" + d["name"]] = {"id": "lean:" + d["name"], "type": "lean_declaration",
                                          "kind": d["kind"], "module": d["module"],
                                          "axioms": d["axioms"]}
    for t in external_lean:
        nodes["ext:" + t] = {"id": "ext:" + t, "type": "external_lean_theorem"}
    for a, b, kind in sorted(edges):
        if b in nodes:
            continue
        if b.startswith("ref:"):
            key = b[4:]
            nodes[b] = {"id": b, "type": "external_reference",
                        "entry": (references.get(key) or {}).get("entry"),
                        "in_bibliography": key in references}
        elif not b.startswith(("lean:", "ext:")):
            # A missing parent is an invalid record (the merge reports it), not a citation.
            nodes[b] = {"id": b, "type": "missing_record" if kind in ("part_of", "fragment_of")
                        else "unresolved_citation"}

    succ, succ_all = defaultdict(set), defaultdict(set)
    for a, b, kind in edges:
        if kind == "part_of":
            a, b = b, a  # the parent uses its part
        if a in fragments or b in fragments or b not in by_id:
            continue
        if kind in FOLLOWED | {"cites_in_context"}:
            succ_all[a].add(b)
            if kind in FOLLOWED:
                succ[a].add(b)
    missing_roots = [r for r in ROOTS if r not in by_id]
    dist = reach([r for r in ROOTS if r in by_id], succ)
    with_context = sorted(set(reach([r for r in ROOTS if r in by_id], succ_all)) - set(dist))
    critical = sorted(dist)
    off_path = [i for i in paper_ids if i not in dist]
    for i, n in nodes.items():
        if n["type"] in ("statement", "fragment"):
            n["on_critical_path"] = i in dist
            n["distance_from_abc"] = dist.get(i)

    # Circular citation: strongly connected components with more than one statement.
    sccs = [c for c in tarjan(paper_ids, {k: sorted(v) for k, v in succ_all.items()})
            if len(c) > 1]
    sccs.sort(key=lambda c: (-len(c), c))
    # Independent subtheories: weakly connected components over the statement records only
    # (unresolved citation targets, fragments and Lean nodes are left out).
    undirected = defaultdict(set)
    for a, bs in succ_all.items():
        for b in bs:
            undirected[a].add(b)
            undirected[b].add(a)
    components, seen = [], set()
    for i in paper_ids:
        if i in seen:
            continue
        comp = sorted(reach([i], undirected))
        seen.update(comp)
        components.append(comp)
    components.sort(key=lambda c: (-len(c), c))

    citers = defaultdict(set)
    for a, b, kind in edges:
        if kind.startswith("cites_") and b in by_id:
            citers[b].add(a)
    unresolved = [i for i in paper_ids if by_id[i].get("proof_status") not in RESOLVED]
    most_cited = sorted(unresolved, key=lambda i: (-len(citers[i]), i))[:40]
    most_cited = [{"id": i, "cited_by": len(citers[i]),
                   "cited_by_critical": len(citers[i] & set(dist)),
                   "on_critical_path": i in dist, "kind": by_id[i].get("kind"),
                   "proof_status": by_id[i].get("proof_status")} for i in most_cited]

    external = defaultdict(dict)  # key -> {statement: count}
    for i in critical:
        for key, n in (by_id[i].get("external_keys") or {}).items():
            external[key][i] = n
    external_on_path = [{"key": k, "entry": (references.get(k) or {}).get("entry"),
                         "statements": len(v), "citations": sum(v.values()),
                         "cited_by": sorted(v)} for k, v in external.items()]
    external_on_path.sort(key=lambda r: (-r["statements"], r["key"]))

    dangling = sorted({(a, b, kind) for a, b, kind in edges
                       if nodes.get(b, {}).get("type") == "unresolved_citation"})
    bad = sorted((a, b, k) for a, b, k in edges if a not in nodes or b not in nodes)

    analysis = {
        "note": NOTE, "no_lean_edge_to_roots": NO_ABC_EDGE, "roots": ROOTS,
        "missing_roots": missing_roots,
        "critical_path": critical, "not_on_critical_path": off_path,
        "added_if_context_edges_followed": with_context,
        "strongly_connected_components": sccs,
        "weakly_connected_components": [{"size": len(c), "members": c} for c in components],
        "component_scope": f"{len(paper_ids)} statement records; {len(fragments)} fragments "
                           f"and {sum(n['type'] == 'unresolved_citation' for n in nodes.values())}"
                           f" unresolved citation targets are left out",
        "most_cited_unresolved": most_cited,
        "external_keys_on_critical_path": external_on_path,
        "citations_to_unresolved_targets": [{"from": a, "to": b, "kind": k}
                                            for a, b, k in dangling],
        "record_to_lean": sorted(links, key=lambda l: (l["record"], l["declaration"])),
        "lean_modules": lean["modules"]}
    graph = {"nodes": sorted(nodes.values(), key=lambda n: n["id"]),
             "edges": [{"from": a, "to": b, "kind": k} for a, b, k in sorted(edges)],
             "analysis": analysis}
    (ROOT / "data" / "dependency_graph.json").write_text(
        json.dumps(graph, indent=1, ensure_ascii=False, sort_keys=True) + "\n")

    write_docs(statements, by_id, edges, nodes, analysis, dist, lean)
    ok = render_svg(by_id, edges, dist)
    print(f"{len(nodes)} nodes, {len(edges)} edges; critical path {len(critical)} of "
          f"{len(paper_ids)} statements; {len(sccs)} citation cycles; "
          f"{len(components)} weakly connected components")
    for a, b, k in bad:
        print(f"error: edge {a} -> {b} ({k}) has an endpoint that is not a node",
              file=sys.stderr)
    if bad or not ok:
        sys.exit(1)


def kind_counts(id_list, by_id):
    if not id_list:
        return "None."
    counts = defaultdict(lambda: defaultdict(int))
    for i in id_list:
        counts[by_id[i].get("paper")]["part or step" if by_id[i].get("parent") else by_id[i].get("kind")] += 1
    kinds = sorted({k for c in counts.values() for k in c})
    rows = [[f"IUT{p}"] + [counts[p].get(k, 0) for k in kinds] + [sum(counts[p].values())]
            for p in sorted(counts, key=lambda p: (p is None, p))]
    return table(rows, ["Paper"] + kinds + ["Total"])


def write_docs(statements, by_id, edges, nodes, analysis, dist, lean):
    kind_totals = defaultdict(int)
    for _, _, k in edges:
        kind_totals[k] += 1
    type_totals = defaultdict(int)
    for n in nodes.values():
        type_totals[n["type"]] += 1
    sccs = analysis["strongly_connected_components"]
    comps = analysis["weakly_connected_components"]
    singletons = sum(1 for c in comps if c["size"] == 1)
    unresolved = analysis["citations_to_unresolved_targets"]
    doc = ["# Dependency graph", "",
           "Generated by `scripts/build_graph.py` from `data/statements.json`, "
           "`data/dependencies.json` and `data/lean_declarations.json`. Do not edit by hand.",
           "Machine-readable form: `data/dependency_graph.json`. Picture of the critical path: "
           "[dependency_graph.svg](dependency_graph.svg).", "",
           "## What an edge means", "", NOTE, "",
           "Citation edges distinguish where the citation occurs: in the statement, in the proof "
           "(from the line starting with \"Proof.\" to the next header; a statement with no "
           "such line has all of its text, up to the next header, counted as statement), or, "
           "for the lettered results "
           "of the Introductions, in the paragraph before or after the result. A citation "
           "that follows a bibliography key of another work (\"[Silv], Chapter VII, "
           "Proposition 5.4\") is a citation of that work and is not an edge. Curated records "
           "add typed edges: `part_of` from a part or proof step to its parent, `fragment_of` "
           "from a fragment (one Lean lemma that checks a piece of a statement) to its parent, "
           "`depends_on` to the results their readers listed, and `depends_on_external` to the "
           "statements of other papers and the bibliography keys listed as external "
           "dependencies. `formalized_by` links a record to a Lean declaration that states its "
           "entire content; a fragment never makes its parent formalized. Lean edges "
           "(`lean_uses`) are read from the elaborated declarations "
           "(`scripts/LeanDeclarations.lean`) and are exact for the modules imported by "
           "`IUT.lean` and for `Solution`; edges to theorems of Mathlib and other dependencies "
           f"are kept for a declaration that uses at most {MAX_EXTERNAL} of them directly, and "
           "the full lists are in the field `external_theorems` of "
           "`data/lean_declarations.json`. Every edge ends at a node: a citation target that "
           "is not a record is a node of type `unresolved_citation`.", "",
           table(sorted(kind_totals.items()), ["Edge kind", "Count"]), "",
           table(sorted(type_totals.items()), ["Node type", "Count"]), "",
           "## Circular citation", "",
           f"{len(sccs)} strongly connected components with more than one statement. A cycle "
           "of citations is not a circular argument: a remark may cite a later result that "
           "cites the remark back for context. Each cycle below needs a reader to decide "
           "whether any edge in it is a logical use.", ""]
    for c in sccs:
        doc.append(f"- {len(c)} statements: " + ", ".join(f"`{i}`" for i in c))
    doc += ["", "## Independent subtheories", "",
            f"The graph of statement records (citations and curated edges, read without "
            f"direction) has {len(comps)} connected components over "
            f"{sum(c['size'] for c in comps)} records; {singletons} of them are single "
            "statements that cite no indexed statement and are cited by none. The count "
            f"covers {analysis['component_scope']}. Component sizes: "
            + ", ".join(str(c["size"]) for c in comps if c["size"] > 1) + ".", "",
            "## Citations to targets that are not records", "",
            f"{len(unresolved)} edges end at an `unresolved_citation` node. Such a target is "
            "usually a numbered result of an external paper whose key the text gives only "
            "once for a list, or a typo in the source. Each is listed so that it can be "
            "checked.", "",
            table([[f"`{d['from']}`", f"`{d['to']}`", d["kind"]] for d in unresolved],
                  ["From", "To", "Edge kind"]), "",
            "## Records and Lean declarations", "",
            "Scope \"whole statement\" means that the record claims the declaration states its "
            "entire content; \"fragment\" means that the record is a fragment of the parent "
            "named, and the parent is not formalized by it.", ""]
    links = analysis["record_to_lean"]
    if links:
        doc.append(table([[f"`{l['record']}`", f"`{l['declaration']}`", l["scope"],
                           f"`{l['parent']}`" if l["parent"] else "",
                           "yes" if l["declaration_found"] else "no, not in the built library"]
                          for l in links],
                         ["Record", "Lean declaration", "Scope", "Parent", "Found"]))
    else:
        doc.append("No curated record names a Lean declaration yet.")
    decls = [d for d in lean["declarations"] if not d["internal"]]
    doc += ["", "## Lean declarations", "",
            f"{len(decls)} declarations (plus "
            f"{len(lean['declarations']) - len(decls)} internal auxiliary ones) in "
            f"{len(lean['modules'])} modules: " + ", ".join(f"`{m}`" for m in lean["modules"])
            + ". Direct project references per declaration are in "
            "`data/dependency_graph.json` (edge kind `lean_uses`).", ""]
    (ROOT / "docs" / "DEPENDENCY_GRAPH.md").write_text("\n".join(doc) + "\n")

    crit = analysis["critical_path"]
    doc = ["# Critical path to abc", "",
           "Generated by `scripts/build_graph.py`. Do not edit by hand.", "",
           "## Method", "",
           "Start from " + " and ".join(f"`{r}`" for r in ROOTS) + " (the diophantine "
           "inequalities of IUT IV from which the papers derive abc) and follow, transitively, "
           "every citation in a statement and in a proof, together with the edges that curated "
           "records add (parts, proof steps, results used, external dependencies on the other "
           "papers). Every statement reached is on the critical path. Fragments are not "
           "followed. Citations in the paragraphs around a lettered result are not "
           "followed; following them as well would add "
           + (", ".join(f"`{i}`" for i in analysis["added_if_context_edges_followed"])
              or "no statement") + ".", "",
           NOTE, "", NO_ABC_EDGE, "",
           f"Missing roots: {', '.join(analysis['missing_roots']) or 'none'}.", "",
           f"## Size: {len(crit)} of {len(crit) + len(analysis['not_on_critical_path'])} "
           "statement records", "",
           kind_counts(crit, by_id), "",
           "Not on the critical path (no chain of edges from the roots reaches them):", "",
           kind_counts(analysis["not_on_critical_path"], by_id), "",
           "## Most cited unresolved statements", "",
           "Unresolved means a proof status other than KERNEL_VERIFIED or "
           "INDEPENDENTLY_CHECKED. Ranked by the number of statements whose text cites them.", ""]
    doc += [f"{k}: {v}." for k, v in sorted(records.LEGEND.items())] + ["",
           table([[f"`{r['id']}`", r["kind"], r["cited_by"], r["cited_by_critical"],
                   "yes" if r["on_critical_path"] else "no", r["proof_status"]]
                  for r in analysis["most_cited_unresolved"]],
                 ["Statement", "Kind", "Cited by", "Cited by critical-path statements",
                  "On path", "Proof status"]), "",
           "## External bibliography keys on the critical path", "",
           "Keys cited in the text of critical-path statements (statement and proof parts). "
           "Each is an external prerequisite that the formalization would have to state or "
           "prove.", "",
           table([[f"`{r['key']}`", r["statements"], r["citations"], r["entry"] or ""]
                  for r in analysis["external_keys_on_critical_path"]],
                 ["Key", "Statements", "Citations", "Entry"]), "",
           "## Statements on the critical path", "",
           "Distance is the shortest chain of edges from a root."]
    for paper in sorted({by_id[i].get("paper") for i in crit}, key=lambda p: (p is None, p)):
        doc += ["", f"### IUT {['', 'I', 'II', 'III', 'IV'][paper] if paper else '?'}", ""]
        rows = sorted((i for i in crit if by_id[i].get("paper") == paper),
                      key=lambda i: (by_id[i].get("pdf_page") or 0, i))
        doc.append(table([[f"`{i}`", by_id[i].get("kind") or "part", by_id[i].get("title") or "",
                           pages(by_id[i]), dist[i], by_id[i].get("statement_status"),
                           by_id[i].get("proof_status")] for i in rows],
                         ["Id", "Kind", "Title", "PDF pages", "Distance", "Statement",
                          "Proof"]))
    (ROOT / "docs" / "CRITICAL_PATH.md").write_text("\n".join(doc) + "\n")


def render_svg(by_id, edges, dist):
    # Curated parts and proof steps are left out too; their edges are in the JSON.
    drawn = sorted(i for i in dist if (by_id[i].get("kind") in DRAWN_KINDS
                                       and not by_id[i].get("parent")) or i in ROOTS)
    keep = set(drawn)
    shape = {"Theorem": "doubleoctagon", "Corollary": "box", "Proposition": "ellipse",
             "Lemma": "ellipse", "Definition": "note"}
    out = ["digraph critical {", '  graph [rankdir=LR, fontname="Helvetica", fontsize=10, '
           'label="Critical path to abc: theorems, propositions, corollaries, lemmas, '
           'definitions. Solid: cited in the statement; dashed: cited in the proof; dotted: '
           'cited around a lettered result; bold: a curated dependency. Remarks, examples and curated proof steps are left '
           'out, so chains through them do not appear. Edges are mechanical citations.", '
           'labelloc=t];',
           '  node [fontname="Helvetica", fontsize=9, style=filled, fillcolor="#f4f4f4"];']
    for paper in range(1, 5):
        out.append(f'  subgraph cluster_{paper} {{ label="IUT {"I" * paper if paper < 4 else "IV"}"; '
                   'color="#999999";')
        for i in drawn:
            if by_id[i].get("paper") == paper:
                fill = "#ffd27f" if i in ROOTS else "#f4f4f4"
                out.append(f'    "{i}" [label="{i[5:]}", shape={shape.get(by_id[i]["kind"], "box")}, '
                           f'fillcolor="{fill}"];')
        out.append("  }")
    style = {"cites_in_statement": "solid", "cites_in_proof": "dashed",
             "cites_in_context": "dotted", "depends_on": "bold", "depends_on_external": "bold"}
    pairs = {}
    for a, b, k in sorted(edges):
        if a in keep and b in keep and k in style:
            pairs.setdefault((a, b), k)
    for (a, b), k in sorted(pairs.items()):
        out.append(f'  "{a}" -> "{b}" [style={style[k]}, color="#55555588", arrowsize=0.5];')
    out.append("}")
    dot = "\n".join(out) + "\n"
    try:
        svg = subprocess.run(["dot", "-Tsvg"], input=dot, capture_output=True, text=True,
                             check=True).stdout
    except (OSError, subprocess.CalledProcessError) as e:
        print(f"error: Graphviz dot failed ({e}); docs/dependency_graph.svg not written",
              file=sys.stderr)
        return False
    (ROOT / "docs" / "dependency_graph.svg").write_text(svg)
    return True


if __name__ == "__main__":
    main()
