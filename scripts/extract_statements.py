#!/usr/bin/env python3
"""Mechanical statement index for the four IUT papers.

Usage: python3 scripts/extract_statements.py <dir-with-the-four-PDFs>

Reads the PDFs with `pdftotext -layout`, finds every numbered header
(Definition, Proposition, Lemma, Theorem, Corollary, Example, Remark) and the lettered
main results of the Introductions (Theorem A, Corollary C), and writes

  data/source_manifest.json   file name, SHA-256, page count, dates, publication data
  data/statements.json        one record per statement, curated records merged in
  data/dependencies.json      citation edges found in the source text
  data/references.json        bibliography keys and how often each is cited

The index is mechanical: it records where a statement is and what its text cites.
It does not judge mathematical content. Hand-reviewed records live in
data/curated/*.json and are merged over the mechanical record, so a rerun never loses
them. No paper text is written to the output apart from statement titles.

Status fields. A statement that only the mechanical pass has seen gets
statement_status and proof_status NOT_EXTRACTED (its location is indexed, its content
has not been extracted by a reader). Curated records set their own statuses.
"""
import hashlib
import json
import re
import subprocess
import sys
import unicodedata
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAPERS = {  # paper number -> (file name, citation key used by the other papers)
    1: ("Inter-universal Teichmuller Theory I.pdf", "IUTchI"),
    2: ("Inter-universal Teichmuller Theory II.pdf", "IUTchII"),
    3: ("Inter-universal Teichmuller Theory III.pdf", "IUTchIII"),
    4: ("Inter-universal Teichmuller Theory IV.pdf", "IUTchIV"),
}
# Publication data, checked by hand on 2026-11-25: each DOI was resolved with
# `curl -sIL https://doi.org/<doi>` (redirect to ems.press, final status 200), and the
# title, journal, volume, issue, pages, publisher and date were read from the Crossref record
# `https://api.crossref.org/works/<doi>` (fields container-title, volume, issue, page,
# publisher, published-print). Not fetched at run time, so that reruns are deterministic.
PUBLICATION = {
    n: {"journal": "Publications of the Research Institute for Mathematical Sciences",
        "volume": "57", "issue": "1", "pages": pages, "year": 2021,
        "publisher": "European Mathematical Society - EMS - Publishing House GmbH",
        "doi": f"10.4171/PRIMS/57-1-{n}",
        "crossref_published_print": "2021-03-04",
        "verified": "DOI resolved (HTTP 200 at ems.press) and Crossref record read on "
                    "2026-11-25",
        "version_in_hand": "author's manuscript, dated on its title page (title_page_date); "
                           "not the journal typesetting: its page count differs from the "
                           "journal page range, and its pages are numbered from 1"}
    for n, pages in {1: "3-207", 2: "209-401", 3: "403-626", 4: "627-723"}.items()
}
KEY_TO_PAPER = {key: n for n, (_, key) in PAPERS.items()}
KINDS = {"Definition": "Def", "Proposition": "Prop", "Lemma": "Lem", "Theorem": "Thm",
         "Corollary": "Cor", "Example": "Ex", "Remark": "Rem"}
PLURALS = {"Definitions": "Definition", "Propositions": "Proposition", "Lemmas": "Lemma",
           "Theorems": "Theorem", "Corollaries": "Corollary", "Examples": "Example",
           "Remarks": "Remark"}
STATUSES = {"NOT_EXTRACTED", "EXTRACTED", "INTERPRETATION_AMBIGUOUS", "LEAN_STATEMENT_DRAFT",
            "STATEMENT_FORMALIZED", "STATEMENT_REVIEWED", "PROOF_IN_PROGRESS",
            "BLOCKED_BY_MATHLIB", "BLOCKED_BY_EXTERNAL_THEOREM",
            "BLOCKED_BY_MISSING_JUSTIFICATION", "CONDITIONALLY_VERIFIED", "KERNEL_VERIFIED",
            "INDEPENDENTLY_CHECKED", "COUNTERMODEL_FOUND"}
KIND_RE = "|".join(KINDS)
NUM = r"\d+(?:\.\d+){1,2}"
# A header is a line that starts with "Kind N.M." or "Kind N.M.K." followed by space or end.
# The text layer sometimes replaces the space by a control character or doubles it
# ("Example\x103.2.", "Example   3.3.").
HEADER = re.compile(rf"^\s*({KIND_RE})[\s\x00-\x1f]*({NUM})\.(?:\s+(.*))?$")
# A line that ends like this continues into the next line, so a "header" after it is the
# tail of a citation ("... the proof of [FrdI]," / "Proposition 5.6.").
CONTINUES = re.compile(r"(,|\bof|\bin)\s*$")
# Lettered main results of the Introductions: "Theorem A.", "Corollary C.".
LETTERED = re.compile(r"^\s*(Theorem|Corollary) ([A-Z])\.\s+\((.*)$")
SECTION = re.compile(r"^\s*Section (\d+):\s*(.+?)\s*$")
BIBLIOGRAPHY = re.compile(r"^\s*Bibliography\s*$")
# A citation: optional "[Key], " then "Kind N.M(.K)" or "Theorem A".
CITE = re.compile(rf"(?:\[([A-Za-z0-9]+)\],?\s+)?({KIND_RE}) ({NUM}|[A-Z]\b)")
# A plural citation: "Corollaries 2.18, 2.19", "Theorems A, (i), (ii); 3.11, (i)".
ITEM = rf"(?:{NUM}|[A-Z]\b|\([ivx]+\))"
PLURAL_CITE = re.compile(rf"(?:\[([A-Za-z0-9]+)\],?\s+)?({'|'.join(PLURALS)}) "
                         rf"({ITEM}(?:(?:,\s*|;\s*|\s+and\s+){ITEM})*)")
BRACKET = re.compile(r"\[([A-Za-z][A-Za-z0-9-]*)\]")
LIGATURES = {"ﬀ": "ff", "ﬁ": "fi", "ﬂ": "fl", "ﬃ": "ffi", "ﬄ": "ffl"}
# Text allowed between two citations of one list, as in "[Key], Corollary 4.5, (iv); Remark 4.5.1".
LIST_GAP = re.compile(r"^(?:,? ?\([ivxlcdm]+\)|,| |;|and|\d+\.\d+(?:\.\d+)?)*$")
BIB_ENTRY = re.compile(r"^\s*\[([A-Za-z][A-Za-z0-9-]*)\]\s+(\S.*)$")
RUNNING_HEAD = [re.compile(r"^\s*(\d+)\s+SHINICHI MOCHIZUKI\s*$"),
                # the Ü of the running head may be one or two code points
                re.compile(r"^\s*INTER-UNIVERSAL TEICHM\S*LLER THEORY [IV]+\s+(\d+)\s*$")]


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
        line = unicodedata.normalize("NFC", line)
        for head in RUNNING_HEAD:
            m = head.match(line)
            if m:
                return int(m.group(1))
    return 1 if pdf_page == 1 else None


def statement_id(paper, kind, number):
    return f"IUT{paper}.{KINDS[kind]}{number.replace('.', '_')}"


def clean(text):
    """Collapse white space and drop control characters left by the text layer."""
    text = "".join(c for c in text if unicodedata.category(c) != "Cc")
    return re.sub(r"\s+", " ", text).strip()


def join_wrapped(text, extra):
    """Append a wrapped line: a hyphen at the line end joins without a space, and is
    dropped when the next line starts in lower case (a word broken across lines)."""
    extra, text = extra.strip(), text.rstrip()
    if text.endswith("-"):
        return (text[:-1] if extra[:1].islower() else text) + extra
    return text + " " + extra


def title_of(kind, first_line, following):
    """Title of a statement, or None.

    Parenthesized titles directly after the header, possibly wrapped over two lines.
    Examples carry unparenthesized titles ending at the first period ("Example 5.1.
    Global Frobenioids."); only those are read, and only from the header line.
    """
    text = (first_line or "").strip()
    if not text.startswith("("):
        if kind == "Example" and "." in text and text[:1].isupper():
            title = text[:text.index(".")]
            return clean(title) if 0 < len(title) <= 80 else None
        return None
    for extra in following:
        if ")" in text:
            break
        text = join_wrapped(text, extra)
    if ")" not in text:
        return None
    return clean(text[1:text.index(")")])


def paragraph_bounds(lines, n, step):
    """Index range of the paragraph next to line n: step -1 is the one ending before it,
    step +1 the one starting at or after n. Paragraphs are separated by blank lines."""
    i = n + step
    while 0 <= i < len(lines) and not lines[i][2].strip():
        i += step
    j = i
    while 0 <= j + step < len(lines) and lines[j + step][2].strip():
        j += step
    return (min(i, j), max(i, j) + 1) if 0 <= i < len(lines) else (n, n)


def citations(text, paper, sid):
    """Citation edges (target, alternative) in text; external keys counted separately."""
    hits = []
    for m in CITE.finditer(text):
        hits.append((m.start(), m.end(), m.group(1), m.group(2), [m.group(3)]))
    for m in PLURAL_CITE.finditer(text):
        numbers = re.findall(rf"{NUM}|\b[A-Z]\b", m.group(3))
        hits.append((m.start(), m.end(), m.group(1), PLURALS[m.group(2)], numbers))
    hits.sort()
    out, last_key, last_end = [], None, 0
    for start, end, key, kind, numbers in hits:
        # A citation with no key of its own continues the list of the previous one.
        inherited = None
        if not key and last_key and LIST_GAP.match(text[last_end:start]):
            inherited = last_key
        last_key, last_end = key or inherited, end
        if (key or inherited) and (key or inherited) not in KEY_TO_PAPER:
            continue  # a numbered result of an external paper
        for number in numbers:
            if number.isalpha() and kind not in ("Theorem", "Corollary"):
                continue
            target = statement_id(KEY_TO_PAPER.get(key, paper), kind, number)
            if inherited:
                out.append((target, statement_id(KEY_TO_PAPER[inherited], kind, number)))
            elif target != sid:
                out.append((target, None))
    return out


def index_paper(paper, pdf):
    pages = pages_of(pdf)
    lines = []  # (pdf_page, printed_page, text)
    for i, page in enumerate(pages, start=1):
        printed = printed_page(page, i)
        lines += [(i, printed, text) for text in page.splitlines()]
    bib_start = next((n for n, (_, _, t) in enumerate(lines) if BIBLIOGRAPHY.match(t)),
                     len(lines))

    section, section_title = 0, "Introduction"
    found, order, bib, rejected, bib_key = {}, [], {}, [], None
    for n, (pdf_page, printed, text) in enumerate(lines):
        if n >= bib_start:
            # An entry runs from its "[Key]" line over its indented continuation lines,
            # skipping running heads, until the next key or the closing note.
            m = BIB_ENTRY.match(text)
            if m:
                bib_key = m.group(1)
                bib[bib_key] = clean(m.group(2))
            elif text.strip().startswith("Updated versions"):
                bib_key = None
            elif bib_key and text.strip() and not any(h.match(unicodedata.normalize("NFC", text))
                                                      for h in RUNNING_HEAD):
                bib[bib_key] = join_wrapped(bib[bib_key], text)
            continue
        m = SECTION.match(text)
        if m:
            section, section_title = int(m.group(1)), m.group(2)
            order.append(("section", n))
            continue
        following = [t for _, _, t in lines[n + 1:n + 3]]
        m = LETTERED.match(text)
        if m and section == 0:
            kind = m.group(1)
            sid = f"IUT{paper}.{KINDS[kind]}{m.group(2)}"
            found[sid] = {
                "id": sid, "paper": paper, "kind": kind, "number": m.group(2),
                "title": title_of(kind, "(" + m.group(3), following),
                "section": 0, "section_title": "Introduction",
                "pdf_page": pdf_page, "printed_page": printed, "line": n,
                "repeated_header_lines": 0, "lettered": True}
            order.append((sid, n))
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
        if n > 0 and CONTINUES.search(lines[n - 1][2]):
            rejected.append({"id": sid, "pdf_page": pdf_page,
                             "reason": "previous line continues into this one"})
            continue
        if sid in found:
            found[sid]["repeated_header_lines"] += 1
            continue
        found[sid] = {
            "id": sid, "paper": paper, "kind": kind, "number": number,
            "title": title_of(kind, rest, following),
            "section": section, "section_title": section_title,
            "pdf_page": pdf_page, "printed_page": printed, "line": n,
            "repeated_header_lines": 0}
        order.append((sid, n))

    # Body of a statement: from its header to the next header or section heading. The part
    # before the first "Proof." line is the statement, the rest is its proof and the text
    # that follows it. A lettered result of an Introduction ends at the first new indented
    # paragraph; the paragraphs right before and after it, which in these Introductions say
    # where in the body the result is proved, are kept as its "context".
    edges = []
    for k, (sid, start) in enumerate(order):
        if sid == "section":
            continue
        end = order[k + 1][1] if k + 1 < len(order) else bib_start
        record = found[sid]
        context = []
        if record.get("lettered"):
            stop = next((j for j in range(start + 1, end)
                         if re.match(r"^ {5}\S", lines[j][2]) and not lines[j - 1][2].strip()),
                        end)
            before, after = paragraph_bounds(lines, start, -1), paragraph_bounds(lines, stop, 1)
            context = [t for _, _, t in lines[before[0]:before[1]] + lines[after[0]:after[1]]]
            end = stop
        body = [t for _, _, t in lines[start:end]]
        proof_at = next((j for j, t in enumerate(body) if re.match(r"^\s*Proof\.", t)), None)
        record["pdf_page_end"] = lines[max(end - 1, start)][0]
        record["has_proof_marker"] = proof_at is not None
        parts = {"statement": body if proof_at is None else body[:proof_at],
                 "proof": [] if proof_at is None else body[proof_at:],
                 "context": context}
        external = {}
        for where, part in parts.items():
            # Join lines so that a citation split by a line break is still found.
            text = re.sub(r"\s+", " ", " ".join(part))
            edges += [(sid, t, where, alt) for t, alt in citations(text, paper, sid)]
            if where == "context":
                continue
            for key in BRACKET.findall(text):
                if key not in KEY_TO_PAPER:
                    external[key] = external.get(key, 0) + 1
        record["external_keys"] = dict(sorted(external.items()))

    full_text = " ".join(t for _, _, t in lines[:bib_start])
    cited = {}
    for key in BRACKET.findall(full_text):
        cited[key] = cited.get(key, 0) + 1
    statements = [found[s] for s, _ in order if s != "section"]
    return pages, statements, edges, bib, cited, rejected


def load_curated():
    """All records of data/curated/*.json, in file order. Invalid JSON is an error."""
    curated, origin = {}, {}
    for path in sorted((ROOT / "data" / "curated").glob("*.json")):
        try:
            records = json.loads(path.read_text())
        except json.JSONDecodeError as e:
            sys.exit(f"error: {path.relative_to(ROOT)} is not valid JSON: {e}")
        if not isinstance(records, dict):
            sys.exit(f"error: {path.relative_to(ROOT)} must hold one object id -> record")
        for sid, record in sorted(records.items()):
            if sid in curated:
                print(f"warning: {sid} curated in both {origin[sid]} and {path.name}; "
                      f"the later file wins", file=sys.stderr)
            curated[sid], origin[sid] = record, path.name
    return curated, origin


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    pdf_dir = Path(sys.argv[1])
    curated, origin = load_curated()

    manifest, statements, edge_set, references, pending, rejected = [], [], {}, {}, [], []
    for paper, (name, key) in PAPERS.items():
        pdf = pdf_dir / name
        info = pdfinfo(pdf)
        pages, found, edges, bib, cited, dropped = index_paper(paper, pdf)
        rejected += dropped
        date = next((m.group(0) for line in pages[0].splitlines()[:12]
                     for m in [re.search(r"(January|February|March|April|May|June|July|August|"
                                         r"September|October|November|December) \d{4}", line)]
                     if m), None)
        printed = [printed_page(p, i) for i, p in enumerate(pages, start=1) if p.strip()]
        manifest.append({
            "paper": paper, "citation_key": key, "file": name,
            "sha256": hashlib.sha256(pdf.read_bytes()).hexdigest(),
            "bytes": pdf.stat().st_size, "pdf_pages": int(info["Pages"]),
            "title_page_date": date, "pdf_creation_date": info.get("CreationDate"),
            "pdf_title": info.get("Title"), "pdf_producer": info.get("Producer"),
            "pages_without_printed_number": sum(p is None for p in printed),
            "pdf_page_equals_printed_page": all(p is None or p == i
                                                for i, p in enumerate(printed, start=1)),
            "numbered_statements": sum(not s.get("lettered") for s in found),
            "lettered_results": sum(bool(s.get("lettered")) for s in found),
            "publication": PUBLICATION[paper]})
        for record in found:
            record.pop("line")
            record["statement_status"] = "NOT_EXTRACTED"
            record["proof_status"] = "NOT_EXTRACTED"
            statements.append(record)
        pending += edges
        for k in sorted(set(bib) | set(cited)):
            entry = references.setdefault(k, {"key": k, "entry": None, "cited_in": {}})
            entry["entry"] = entry["entry"] or bib.get(k)
            if cited.get(k):
                entry["cited_in"][f"IUT{paper}"] = cited[k]

    # A bracketed word is a bibliography key only if some bibliography lists it; the text
    # also uses brackets for asides ("[local]", "[iso]").
    bib_keys = {k for k, r in references.items() if r["entry"]}
    references = {k: r for k, r in references.items() if k in bib_keys}
    for record in statements:
        record["external_keys"] = {k: n for k, n in record.get("external_keys", {}).items()
                                   if k in bib_keys}

    # Merge curated records. Ids the mechanical pass does not produce are parts or proof
    # steps ("IUT3.Cor3_12.StepXI"); they become records whose parent is the id with its
    # last component dropped. An unknown id with only two components is reported and
    # skipped: it is either a typo or a header that this script misses (fix the script).
    by_id = {s["id"]: s for s in statements}
    warnings = []
    for sid in sorted(curated, key=lambda s: (s.count("."), s)):
        record = curated[sid]
        if sid in by_id:
            by_id[sid].update(record)
            by_id[sid]["curated_in"] = origin[sid]
            continue
        parts = sid.split(".")
        if len(parts) < 3:
            warnings.append(f"{sid} ({origin[sid]}): not in the mechanical index; skipped")
            continue
        parent = ".".join(parts[:-1])
        if parent not in by_id:
            warnings.append(f"{sid} ({origin[sid]}): parent {parent} is not a known statement")
        new = {"id": sid, "parent": parent, "paper": int(parts[0][3:]) if parts[0][3:].isdigit()
               else None, "curated_in": origin[sid], **record}
        parent_record = by_id.get(parent, {})
        for field in ("kind", "section", "section_title"):
            new.setdefault(field, parent_record.get(field))
        new.setdefault("kind", None)
        statements.append(new)
        by_id[sid] = new
    for record in statements:
        for field in ("statement_status", "proof_status"):
            if record.get(field) not in STATUSES:
                warnings.append(f"{record['id']}: {field} {record.get(field)!r} is not a "
                                f"status of the brief")
    known = set(by_id)

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
    for name, value in [("source_manifest.json", manifest), ("statements.json", statements),
                        ("dependencies.json", edges),
                        ("references.json", sorted(references.values(), key=lambda r: r["key"]))]:
        (data / name).write_text(json.dumps(value, indent=1, ensure_ascii=False,
                                            sort_keys=True) + "\n")
    dangling = sum(not e["target_indexed"] for e in edges)
    print(f"{len(statements)} statements ({len(curated)} curated records), {len(edges)} "
          f"citation edges ({dangling} to targets not in the index), "
          f"{len(references)} bibliography keys, {len(rejected)} header lines rejected")
    for m in manifest:
        print(f"  IUT{m['paper']}: {m['numbered_statements']} numbered, "
              f"{m['lettered_results']} lettered, {m['pdf_pages']} pages, "
              f"{m['title_page_date']}, {m['pages_without_printed_number']} pages without "
              f"a printed number")
    for w in warnings:
        print("warning: " + w, file=sys.stderr)


if __name__ == "__main__":
    main()
