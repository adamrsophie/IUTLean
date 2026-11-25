#!/usr/bin/env python3
"""Mechanical statement index for the four IUT papers.

Usage: python3 scripts/extract_statements.py <dir-with-the-four-PDFs>

Reads the PDFs with `pdftotext -layout`, finds every numbered header
(Definition, Proposition, Lemma, Theorem, Corollary, Example, Remark), and writes

  data/source_manifest.json   file name, SHA-256, page count, dates
  data/statements.json        one record per numbered statement
  data/dependencies.json      citation edges found in the source text
  data/references.json        bibliography keys and how often each is cited

The index is mechanical: it records where a statement is and what its text cites.
It does not judge mathematical content. Hand-reviewed fields live in
data/curated.json and are merged over the mechanical record, so a rerun never
loses them. No paper text is written to the output apart from statement titles.
"""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAPERS = {  # paper number -> (file name, citation key used by the other papers)
    1: ("Inter-universal Teichmuller Theory I.pdf", "IUTchI"),
    2: ("Inter-universal Teichmuller Theory II.pdf", "IUTchII"),
    3: ("Inter-universal Teichmuller Theory III.pdf", "IUTchIII"),
    4: ("Inter-universal Teichmuller Theory IV.pdf", "IUTchIV"),
}
KEY_TO_PAPER = {key: n for n, (_, key) in PAPERS.items()}
KINDS = {"Definition": "Def", "Proposition": "Prop", "Lemma": "Lem", "Theorem": "Thm",
         "Corollary": "Cor", "Example": "Ex", "Remark": "Rem"}
KIND_RE = "|".join(KINDS)
# A header is a line that starts with "Kind N.M." or "Kind N.M.K." followed by space or end.
HEADER = re.compile(rf"^\s*({KIND_RE}) (\d+(?:\.\d+){{1,2}})\.(?:\s+(.*))?$")
# Lettered main results of the Introductions: "Theorem A.", "Corollary C.".
LETTERED = re.compile(r"^\s*(Theorem|Corollary) ([A-Z])\.\s+\((.*)$")
SECTION = re.compile(r"^\s*Section (\d+):\s*(.+?)\s*$")
BIBLIOGRAPHY = re.compile(r"^\s*Bibliography\s*$")
# A citation: optional "[Key], " then "Kind N.M(.K)".
CITE = re.compile(rf"(?:\[([A-Za-z0-9]+)\],?\s+)?({KIND_RE}) (\d+(?:\.\d+){{1,2}})")
BRACKET = re.compile(r"\[([A-Za-z][A-Za-z0-9-]*)\]")
LIGATURES = {"\ufb00": "ff", "\ufb01": "fi", "\ufb02": "fl", "\ufb03": "ffi", "\ufb04": "ffl"}
# Text allowed between two citations of one list, as in "[Key], Corollary 4.5, (iv); Remark 4.5.1".
LIST_GAP = re.compile(r"^(?:,? ?\([ivxlcdm]+\)|,| |;|and|\d+\.\d+(?:\.\d+)?)*$")
BIB_ENTRY = re.compile(r"^\s*\[([A-Za-z][A-Za-z0-9-]*)\]\s+(\S.*)$")


def pages_of(pdf):
    text = subprocess.run(["pdftotext", "-layout", str(pdf), "-"], check=True,
                          capture_output=True, text=True).stdout
    for ligature, plain in LIGATURES.items():  # "Deﬁnition" must read "Definition"
        text = text.replace(ligature, plain)
    return text.split("\f")


def pdfinfo(pdf):
    out = subprocess.run(["pdfinfo", "-isodates", str(pdf)], check=True,
                         capture_output=True, text=True).stdout
    return dict((k.strip(), v.strip()) for k, v in
                (line.split(":", 1) for line in out.splitlines() if ":" in line))


def printed_page(page_text, pdf_page):
    """Printed page number from the running head, or None if the head has none."""
    for line in page_text.splitlines()[:3]:
        m = re.match(r"^\s*(\d+)\s+SHINICHI MOCHIZUKI\s*$", line) or \
            re.match(r"^\s*INTER-UNIVERSAL TEICHM.LLER THEORY [IV]+\s+(\d+)\s*$", line)
        if m:
            return int(m.group(1))
    return 1 if pdf_page == 1 else None


def statement_id(paper, kind, number):
    return f"IUT{paper}.{KINDS[kind]}{number.replace('.', '_')}"


def title_of(first_line, following):
    """Title in parentheses right after the header, possibly wrapped over two lines."""
    text = (first_line or "").strip()
    if not text.startswith("("):
        return None
    for extra in following:
        if ")" in text:
            break
        text += " " + extra.strip()
    if ")" not in text:
        return None
    return re.sub(r"\s+", " ", text[1:text.index(")")]).strip()


def index_paper(paper, pdf):
    pages = pages_of(pdf)
    lines = []  # (pdf_page, printed_page, text)
    for i, page in enumerate(pages, start=1):
        printed = printed_page(page, i)
        lines += [(i, printed, text) for text in page.splitlines()]

    section, section_title, in_bib = 0, "Introduction", False
    found, order, bib, lettered = {}, [], {}, []
    for n, (pdf_page, printed, text) in enumerate(lines):
        if BIBLIOGRAPHY.match(text):
            in_bib = True
            continue
        if in_bib:
            m = BIB_ENTRY.match(text)
            if m:
                bib[m.group(1)] = re.sub(r"\s+", " ", m.group(2))
            continue
        m = SECTION.match(text)
        if m:
            section, section_title = int(m.group(1)), m.group(2)
            continue
        following = [t for _, _, t in lines[n + 1:n + 3]]
        m = LETTERED.match(text)
        if m and section == 0:
            lettered.append({
                "id": f"IUT{paper}.{'Thm' if m.group(1) == 'Theorem' else 'Cor'}{m.group(2)}",
                "paper": paper, "kind": m.group(1), "number": m.group(2),
                "title": title_of("(" + m.group(3), following),
                "section": 0, "section_title": "Introduction",
                "pdf_page": pdf_page, "printed_page": printed, "line": n})
            continue
        m = HEADER.match(text)
        if not m:
            continue
        kind, number, rest = m.groups()
        # Statements are numbered by section; a header whose first component is not the
        # current section is a line of running text that happens to start with a citation.
        if int(number.split(".")[0]) != section:
            continue
        sid = statement_id(paper, kind, number)
        if sid in found:
            found[sid]["repeated_header_lines"] += 1
            continue
        found[sid] = {
            "id": sid, "paper": paper, "kind": kind, "number": number,
            "title": title_of(rest, following),
            "section": section, "section_title": section_title,
            "pdf_page": pdf_page, "printed_page": printed, "line": n,
            "repeated_header_lines": 0}
        order.append(sid)

    # Body of a statement: from its header to the next header. The part before the first
    # "Proof." line is the statement, the rest is its proof and the text that follows it.
    edges, body_end = [], {}
    bib_start = next((n for n, (_, _, t) in enumerate(lines) if BIBLIOGRAPHY.match(t)),
                     len(lines))
    for k, sid in enumerate(order):
        start = found[sid]["line"]
        end = found[order[k + 1]]["line"] if k + 1 < len(order) else bib_start
        body = [t for _, _, t in lines[start:end]]
        proof_at = next((j for j, t in enumerate(body) if re.match(r"^\s*Proof\.", t)), None)
        found[sid]["pdf_page_end"] = lines[end - 1][0]
        found[sid]["has_proof_marker"] = proof_at is not None
        parts = {"statement": body if proof_at is None else body[:proof_at],
                 "proof": [] if proof_at is None else body[proof_at:]}
        external = {}
        for where, part in parts.items():
            # Join lines so that a citation split by a line break is still found.
            text = re.sub(r"\s+", " ", " ".join(part))
            last_key, last_end = None, 0
            for m in CITE.finditer(text):
                key, kind, number = m.groups()
                # A citation with no key of its own continues the list of the previous one.
                inherited = None
                if not key and last_key and LIST_GAP.match(text[last_end:m.start()]):
                    inherited = last_key
                last_key, last_end = key or inherited, m.end()
                if (key or inherited) and (key or inherited) not in KEY_TO_PAPER:
                    continue  # a numbered result of an external paper; counted below
                target = statement_id(KEY_TO_PAPER.get(key, paper), kind, number)
                if inherited:
                    edges.append((sid, target, where, statement_id(KEY_TO_PAPER[inherited],
                                                                   kind, number)))
                elif target != sid:
                    edges.append((sid, target, where, None))
            for key in BRACKET.findall(text):
                if key not in KEY_TO_PAPER:
                    external[key] = external.get(key, 0) + 1
        found[sid]["external_keys"] = dict(sorted(external.items()))
        body_end[sid] = end

    full_text = " ".join(t for _, _, t in lines[:bib_start])
    cited = {}
    for key in BRACKET.findall(full_text):
        cited[key] = cited.get(key, 0) + 1
    return pages, [found[s] for s in order], lettered, edges, bib, cited


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    pdf_dir = Path(sys.argv[1])
    curated_path = ROOT / "data" / "curated.json"
    curated = json.loads(curated_path.read_text()) if curated_path.exists() else {}

    manifest, statements, edge_set, references, pending = [], [], {}, {}, []
    for paper, (name, key) in PAPERS.items():
        pdf = pdf_dir / name
        info = pdfinfo(pdf)
        pages, numbered, lettered, edges, bib, cited = index_paper(paper, pdf)
        date = next((m.group(0) for line in pages[0].splitlines()[:12]
                     for m in [re.search(r"(January|February|March|April|May|June|July|August|"
                                         r"September|October|November|December) \d{4}", line)]
                     if m), None)
        manifest.append({
            "paper": paper, "citation_key": key, "file": name,
            "sha256": hashlib.sha256(pdf.read_bytes()).hexdigest(),
            "bytes": pdf.stat().st_size, "pdf_pages": int(info["Pages"]),
            "title_page_date": date, "pdf_creation_date": info.get("CreationDate"),
            "pdf_title": info.get("Title"), "pdf_producer": info.get("Producer"),
            "numbered_statements": len(numbered), "lettered_results": len(lettered)})
        for record in lettered + numbered:
            record.pop("line")
            record.setdefault("statement_status", "EXTRACTED_MECHANICALLY")
            record.setdefault("proof_status", "NOT_STARTED")
            record.update(curated.get(record["id"], {}))
            statements.append(record)
        pending += edges
        for k in sorted(set(bib) | set(cited)):
            entry = references.setdefault(k, {"key": k, "entry": None, "cited_in": {}})
            entry["entry"] = entry["entry"] or bib.get(k)
            if cited.get(k):
                entry["cited_in"][f"IUT{paper}"] = cited[k]

    # Curated records that the mechanical pass does not produce (proof steps, for example).
    known = {s["id"] for s in statements}
    for sid, record in curated.items():
        if sid not in known:
            statements.append({"id": sid, **record})
    known = {s["id"] for s in statements}
    # A keyless citation inside a list that began with another paper's key is read as a
    # citation of this paper if that statement exists, and of the other paper otherwise.
    for source, target, where, alternative in pending:
        if alternative and target not in known and alternative in known:
            target = alternative
        if target != source:
            edge_set.setdefault((source, target), set()).add(where)

    edges = [{"from": s, "to": t, "cited_in": sorted(w), "target_indexed": t in known}
             for (s, t), w in sorted(edge_set.items())]
    data = ROOT / "data"
    data.mkdir(exist_ok=True)
    for name, value in [("source_manifest.json", manifest), ("statements.json", statements),
                        ("dependencies.json", edges),
                        ("references.json", sorted(references.values(), key=lambda r: r["key"]))]:
        (data / name).write_text(json.dumps(value, indent=1, ensure_ascii=False) + "\n")
    dangling = sum(not e["target_indexed"] for e in edges)
    print(f"{len(statements)} statements, {len(edges)} citation edges "
          f"({dangling} to targets not in the index), {len(references)} bibliography keys")
    for m in manifest:
        print(f"  IUT{m['paper']}: {m['numbered_statements']} numbered, "
              f"{m['lettered_results']} lettered, {m['pdf_pages']} pages, {m['title_page_date']}")


if __name__ == "__main__":
    main()
