"""Build the static publication from the collected catalogues, without research runs."""
from __future__ import annotations

from wip_notice import WIP_HTML
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import gzip
import html
import json
from pathlib import Path
import re
import shutil
import subprocess
from urllib.parse import quote

ROOT = Path(__file__).resolve().parents[1]
DIST = ROOT / "site" / "dist"
PUBLIC_MATH_DOCS = {'audit/full/CANONICAL-FOUNDATIONS.md', 'audit/full/INDEPENDENT-ASYMPTOTIC-CROSSCHECK.md',
    'audit/full/paper-a/DEATH-SWAP-REPAIR.md', 'audit/full/paper-a/SLOPE-SECOND-REVIEW.md',
    'audit/full/paper-a/STRICT-LIMINF-DERIVATION.md', 'audit/full/paper-b/SLOPE-REPAIR.md'}
LABELS = {
    "lean-verified": "Lean verified (stated scope)",
    "source-collected": "Source collected — verification not asserted",
    "paper-reviewed": "Paper proof with recorded review",
    "paper-proof": "Paper proof",
    "conditional": "Conditional result",
    "open": "Open problem or supplier",
    "refuted": "Refuted claim",
    "withheld": "Withheld — unresolved proof dependency",
}


def read_records(path: Path) -> list[dict]:
    if path.is_file():
        data = json.loads(path.read_text(encoding="utf-8-sig"))
        # Keep a small transport copy for repositories and upload archives.
        with path.with_suffix(path.suffix + '.gz').open('wb') as raw:
            with gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0) as output:
                output.write(json.dumps(data, ensure_ascii=False, separators=(",", ":")).encode('utf-8'))
    else:
        with gzip.open(path.with_suffix(path.suffix + ".gz"), "rt", encoding="utf-8-sig") as source:
            data = json.load(source)
    if isinstance(data, list):
        return data
    for key in ("results", "records", "entries", "items"):
        if isinstance(data.get(key), list):
            return data[key]
    raise ValueError(f"Unrecognized catalogue shape: {path}")


def esc(value) -> str:
    if isinstance(value, (list, dict)):
        value = json.dumps(value, ensure_ascii=False, indent=2)
    return html.escape(str(value or ""))


def safe_id(value: str) -> str:
    slug = re.sub(r"[^a-zA-Z0-9_-]+", "-", value).strip("-")[:110]
    return (slug or "result") + "-" + hashlib.sha256(value.encode()).hexdigest()[:8]


def copy_if_changed(source, destination):
    """Avoid rewriting immutable archived copies; validation rechecks hashes."""
    source_path, destination_path = Path(source), Path(destination)
    if destination_path.is_file():
        source_stat, destination_stat = source_path.stat(), destination_path.stat()
        if (source_stat.st_size, source_stat.st_mtime_ns) == (destination_stat.st_size, destination_stat.st_mtime_ns):
            return str(destination_path)
    return shutil.copy2(source, destination)


def shell(title: str, body: str, prefix="", description="", canonical="") -> str:
    canonical_tag = f'<link rel="canonical" href="{esc(canonical)}">' if canonical else ""
    status = json.loads((ROOT / 'PUBLICATION-STATUS.json').read_text(encoding='utf-8'))
    hold = '<aside class="evidence">Selected reviewed edition. Each result retains its exact hypotheses and verification scope.</aside>'
    return f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>{esc(title)} · Three-Row Chomp</title>
<meta name="description" content="{esc(description[:280])}">{canonical_tag}
<link rel="stylesheet" href="{prefix}document.css"><link rel="stylesheet" href="{prefix}math/katex.min.css"></head>
<body>{WIP_HTML}<header><a class="brand" href="{prefix}index.html">Three-Row Chomp <span>Research Library</span></a>
<nav aria-label="Library"><a href="{prefix}index.html">Search</a><a href="{prefix}browse.html">Browse all</a><a href="{prefix}guide.html">Reading guide</a><a href="https://arxiv.org/abs/2605.23837">Uniqueness paper ↗</a></nav></header>
<main>{hold}{body}</main><footer>Three-Row Chomp research library · Statements retain their assumptions and recorded verification scope.</footer></body></html>'''


def evidence_text(record: dict) -> str:
    status = record.get("status", "source-collected")
    if status == "source-collected":
        return "This record inventories source material. Collection and declaration extraction do not certify that the source compiles or that every statement in it is proved."
    if status == "withheld":
        return "The original claim has an unresolved proof dependency and is withheld from publication as an established result. Read the full audit verdict and the precisely scoped replacement."
    if status == "conditional":
        return "The implication is recorded with its hypotheses. Its conclusion is not asserted for the canonical recurrence unless those hypotheses have separately been established."
    if status == "lean-verified":
        return "Verification applies only to the recorded source snapshot and check scope. Consult the coverage report for build and axiom-check details."
    if status in ("paper-proof", "paper-reviewed"):
        return "This is a mathematical paper proof with the evidence recorded below. Its status does not by itself imply a checked Lean formalization."
    if status == "refuted":
        return "This is a negative result or a recorded counterexample to a candidate claim. It is included to document the research boundary."
    return "This item records a remaining mathematical obligation. It must not be cited as a proved theorem."


def record_html(record: dict, base_url: str) -> str:
    title = record.get("title") or record["id"]
    fields = []
    for key, label in (("statement", "Statement"), ("assumptions", "Hypotheses and scope"),
                       ("proof", "Proof"), ("proofText", "Proof text"),
                       ("formalization", "Formalization correspondence"),
                       ("verification", "Verification evidence"), ("evidence", "Evidence")):
        value = record.get(key)
        if key == "statement" and record.get("kind") == "lean":
            continue
        if value:
            if isinstance(value, list) and all(isinstance(x, str) for x in value):
                content = "<ul>" + "".join(f"<li>{esc(x)}</li>" for x in value) + "</ul>"
            else:
                content = f'<pre class="prose">{esc(value)}</pre>'
            fields.append(f"<section><h2>{label}</h2>{content}</section>")
    if record.get('audit'):
        verdict = record['audit'].get('originalClaimVerdict', record['audit'].get('kernelVerdict', 'reviewed'))
        correction = record['audit'].get('exactCorrection')
        fields.insert(0, '<section><h2>Scientific review</h2><p>Review verdict: ' + esc(verdict) + '. Evidence and exact scope are linked above.</p>' + ('<p><strong>Correction:</strong> ' + esc(correction) + '</p>' if correction else '') + '</section>')
    decls = record.get("declarations") or record.get("extractedDeclarations")
    if decls:
        if isinstance(decls, list):
            rows = []
            for item in decls:
                if isinstance(item, str):
                    rows.append(f"<li><code>{esc(item)}</code></li>")
                else:
                    name = item.get("name") or item.get("title") or "Declaration"
                    text = item.get("statement") or item.get("signature") or item.get("snippet") or ""
                    rows.append(f'<li><code>{esc(name)}</code><pre class="prose">{esc(text)}</pre></li>')
            description = ('These are exact elaborated statement types from the full kernel audit, including private and generated declarations. Generated helper statements are not separate mathematical results.' if record.get('declarationEvidence') == 'full-kernel-census' else 'These are extracted names and signature excerpts, which may be incomplete. Open the full source for exact statements and proofs. This list is not a count of independently verified theorems.')
            fields.append('<section><h2>Formal declarations</h2><p>' + description + '</p><details><summary>Browse ' + str(len(decls)) + ' declarations</summary><ul class="declarations">' + "".join(rows) + "</ul></details></section>")
    links = []
    if record.get("englishProof"):
        links.append(f'<a class="button" href="../{esc(quote(record["englishProof"], safe="/#"))}">Read the English proof</a>')
    if record.get("receiptHref"):
        links.append(f'<a href="../{esc(quote(record["receiptHref"], safe="/#"))}">Verification receipt</a>')
    attachment = record.get("attachment")
    if attachment:
        label = 'Audited Lean source' if record.get('kind') == 'lean' else 'Download proof (Markdown)'
        links.append(f'<a class="button" href="../{esc(quote(attachment, safe="/"))}">{label}</a>')
    for item in record.get("additionalAttachments", []):
        path = item if isinstance(item, str) else item.get("path") or item.get("href") or item.get("attachment")
        if path:
            label = item.get("label", "Supporting source") if isinstance(item, dict) else "Supporting source"
            public_path = re.sub(r"\.md(?=#|$)", ".html", path) if path.startswith(('papers/', 'audit/prepublication/')) or path.split('#')[0] in PUBLIC_MATH_DOCS else path
            links.append(f'<a href="../{esc(quote(public_path, safe="/#"))}">{esc(label)}</a>')
    source = record.get("sourcePath", "")
    if source:
        line = record.get("sourceLine")
        fields.append(f'<section><h2>Provenance</h2><p class="path">{esc(source)}{":" + esc(line) if line else ""}</p>' +
                      (f'<p>SHA-256: <code class="path">{esc(record.get("sha256"))}</code></p>' if record.get("sha256") else "") + "</section>")
    body = f'''<p class="eyebrow">{esc(record.get("topic", "Research"))} · {esc(record.get("kind", "result"))}</p>
<h1>{esc(title)}</h1><p class="lead">{esc(record.get("summary", ""))}</p>
<p class="badge">{esc(LABELS.get(record.get("status"), record.get("status", "Source collected")))}</p>
<p class="evidence">{esc(evidence_text(record))}</p><div class="source-links">{' '.join(links)}</div>
{''.join(fields)}<p><a href="../index.html#id={esc(quote(record['id']))}">Find this record in the search interface →</a></p>'''
    return shell(title, body, "../", record.get("summary", ""), f"{base_url}/{record['pageHref']}" if base_url else "")


CSS = '''*{box-sizing:border-box}body{margin:0;color:#1c3040;background:#faf8f2;font:17px/1.65 system-ui,sans-serif}a{color:#076d6a;text-underline-offset:3px}header{padding:25px max(5vw,20px);border-bottom:1px solid #d5ded8;display:flex;align-items:center;justify-content:space-between;gap:20px;flex-wrap:wrap}.brand{font:700 25px Georgia,serif;text-decoration:none;color:#173a48}.brand span{display:block;font:11px system-ui;text-transform:uppercase;letter-spacing:.15em;color:#64746f}nav{display:flex;gap:24px;flex-wrap:wrap;font-size:14px}main{max-width:1080px;margin:55px auto;padding:0 24px}h1{font:normal clamp(30px,5vw,48px)/1.18 Georgia,serif;overflow-wrap:anywhere;margin:14px 0 22px}h2{font:normal 26px Georgia,serif;margin-top:36px}.lead{font-size:20px;color:#53645f}.eyebrow{text-transform:uppercase;font-size:12px;letter-spacing:.13em;color:#55786e}.badge{display:inline-block;background:#e8efeb;border:1px solid #cadad2;border-radius:30px;padding:4px 13px;font-size:13px}.evidence{font-size:14px;border-left:3px solid #c5a46d;padding:12px 16px;background:#f1eee5}.prose{font:inherit;white-space:pre-wrap;overflow-wrap:anywhere}.path,code{overflow-wrap:anywhere;font-size:13px}code{font-family:ui-monospace,monospace}.source-links{display:flex;gap:20px;align-items:center;flex-wrap:wrap;margin:25px 0}.button{padding:10px 16px;background:#155b57;color:white;border-radius:5px;text-decoration:none}.result{padding:22px 0;border-bottom:1px solid #d5ded8}.result h2{font:600 19px system-ui;margin:0}.result p{margin:8px 0}.meta{font-size:12px;color:#667770}.declarations li{margin-bottom:20px}footer{max-width:1080px;margin:60px auto 0;padding:25px 24px;border-top:1px solid #d5ded8;font-size:12px;color:#677b70}.pagination{display:flex;gap:16px;flex-wrap:wrap;margin:30px 0}table{border-collapse:collapse;width:100%}th,td{text-align:left;border-bottom:1px solid #d5ded8;padding:12px}details{margin:15px 0}@media(max-width:600px){main{margin-top:30px}nav{gap:16px}header{padding:20px}.lead{font-size:17px}}'''


def main() -> None:
    from check_review_inputs import verify_reviewed_inputs
    verify_reviewed_inputs()
    parser = argparse.ArgumentParser()
    parser.add_argument("--base-url", default="", help="Public site root, e.g. https://owner.github.io/project")
    args = parser.parse_args()
    base_url = args.base_url.rstrip("/")
    if base_url and not base_url.startswith("https://"):
        parser.error("--base-url must start with https://")
    if base_url:
        from check_release_gate import require_approved
        require_approved()
    DIST.mkdir(parents=True, exist_ok=True)
    reviewed_path = ROOT / 'data/reviewed-catalog.json'
    if not reviewed_path.is_file():
        raise SystemExit('Preview blocked: the theorem-by-theorem review has not been integrated. Broad source inventories cannot be used as a publication catalogue.')
    records = read_records(reviewed_path)
    if not records or any(not r.get('audit') for r in records):
        raise ValueError('Every preview record needs an explicit full-audit disposition')
    for asset in (ROOT / 'site/ui').iterdir():
        if asset.is_file():
            shutil.copy2(asset, DIST / asset.name)
    shutil.copytree(ROOT / 'site/math', DIST / 'math', dirs_exist_ok=True)
    proof_sections = {}
    compendium = ROOT / "papers/ENGLISH-PROOFS.md"
    if compendium.is_file():
        for line in compendium.read_text(encoding="utf-8-sig").splitlines():
            if line.startswith("## Source: "):
                heading = line[3:]
                slug = re.sub(r"\s+", "-", re.sub(r"[^\w -]", "", heading.lower()).strip())
                proof_sections[line[len("## Source: "):]] = slug
    ids = set()
    for r in records:
        if not r.get("id") or r["id"] in ids:
            raise ValueError(f"Missing/duplicate result ID: {r.get('id')}")
        ids.add(r["id"])
        r["pageHref"] = f"results/{safe_id(r['id'])}.html"
        if isinstance(r.get("assumptions"), str):
            r["assumptions"] = [r["assumptions"]] if r["assumptions"] else []
        if isinstance(r.get("verificationReceipt"), str) and not r.get("receiptHref"):
            receipt = r["verificationReceipt"].replace("\\", "/")
            r["receiptHref"] = "sources/" + receipt if receipt.startswith("lean/") else receipt
        if isinstance(r.get("englishProof"), str):
            r["englishProof"] = re.sub(r"\.md(?=#|$)", ".html", r["englishProof"])
            if r["englishProof"] == "papers/ENGLISH-PROOFS.html" and r.get("sourcePath") in proof_sections:
                r["englishProof"] += "#" + proof_sections[r["sourcePath"]]
    # Only explicit audited attachments and pinned configuration are copied.
    # A newly added workspace file cannot silently enter the preview.
    selected_files = {
        'papers/ENGLISH-PROOFS.md', 'PUBLICATION-STATUS.json',
        'audit/release/ORIGIN.json', 'audit/release/EXCLUDED-CLAIMS.json', 'audit/release/REVIEW.json', 'audit/release/INPUTS.json',
        'audit/full/lean/formal-audit-ledger.json',
        'audit/full/lean/declarations.jsonl.gz',
        'audit/full/lean/independent-uniqueness-review.md',
        'audit/full/lean-documentation-amendment/receipt.json',
        'sources/lean/core/lakefile.lean', 'sources/lean/core/lean-toolchain',
        'sources/lean/core/lake-manifest.json',
    }
    # Copy only preselected audit/certificate inputs, never a workspace inventory.
    inputs = json.loads((ROOT / 'audit/release/INPUTS.json').read_text(encoding='utf-8'))
    selected_files.update(p for p in inputs['files'] if p.startswith(('audit/', 'certificates/')))
    selected_files.update(p for p in inputs['files'] if p.startswith('papers/supplements/'))
    selected_files.add('RELEASE-NOTES.md')
    for record in records:
        for field in ('attachment', 'receiptHref'):
            if record.get(field):
                selected_files.add(record[field].split('#')[0])
        for item in record.get('additionalAttachments', []):
            path = item if isinstance(item, str) else item.get('path') or item.get('href') or item.get('attachment')
            if path:
                selected_files.add(path.split('#')[0])
    for relative in selected_files:
        original_relative = relative.removeprefix('sources/') if relative.startswith('sources/lean/') else relative
        source = (ROOT / original_relative).resolve()
        target = (DIST / relative).resolve()
        if not source.is_relative_to(ROOT.resolve()) or not target.is_relative_to(DIST.resolve()):
            raise ValueError('Selected source escaped publication directory: ' + relative)
        if not source.is_file():
            raise FileNotFoundError('Missing selected publication evidence: ' + relative)
        target.parent.mkdir(parents=True, exist_ok=True)
        copy_if_changed(source, target)
    docs_dir = DIST / "documentation"
    docs_dir.mkdir(exist_ok=True)
    for path in (ROOT / "docs").glob("*.md"):
        shutil.copy2(path, docs_dir / path.name)
    (DIST / "data").mkdir(exist_ok=True)
    for name in ():
        source = ROOT / "data" / name
        if source.is_file():
            shutil.copy2(source, DIST / "data" / name)
    (DIST / "results").mkdir(exist_ok=True)
    # Only remove this generator's own pages, inside its checked output root.
    for old in (DIST / "results").glob("*.html"):
        if old.resolve().is_relative_to((DIST / "results").resolve()):
            old.unlink()
    for old in DIST.glob("browse*.html"):
        if re.fullmatch(r"browse(?:-\d+)?\.html", old.name):
            old.unlink()
    (DIST / "document.css").write_text(CSS + '\n.math-display{overflow-x:auto;overflow-y:hidden;padding:8px 0}.katex{font-size:1.06em}.katex-display{margin:.6em 0}pre{overflow-x:auto}table{display:block;overflow-x:auto}\n', encoding="utf-8")
    for r in records:
        (DIST / r["pageHref"]).write_text(record_html(r, base_url), encoding="utf-8")
    status_counts = dict(Counter(r.get("status", "source-collected") for r in records))
    kind_counts = dict(Counter(r.get("kind", "unknown") for r in records))
    stats = {"total": len(records), "byStatus": status_counts, "byKind": kind_counts,
             "leanModules": sum(r.get("kind") == "lean" for r in records),
             "paperResults": sum(r.get("kind") == "paper" for r in records),
             "sourceDocuments": sum(r.get("kind") == "paper-source" for r in records)}
    catalog = {"results": records, "stats": stats, "generatedAt": inputs.get('snapshotAt', '2026-10-14T00:00:00+03:00'),
               "coverageNote": "Counts describe catalogue records and distinct source versions, not independent theorems. See the coverage reports.",
               "paperUrl": "https://arxiv.org/abs/2605.23837"}
    (ROOT / "data/catalog.json").write_text(json.dumps(catalog, ensure_ascii=False, indent=2), encoding="utf-8")
    # A compressed complete catalogue is suitable for download; the browser gets
    # a leaner search index below.
    with (DIST / 'catalog-full.json.gz').open('wb') as raw:
        with gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0) as output:
            output.write(json.dumps(catalog, ensure_ascii=False, separators=(",", ":")).encode("utf-8"))
    # Keep complete provenance and signatures in the downloadable JSON and static
    # pages, while keeping the first browser load practical for a large archive.
    ui_fields = {"id", "title", "kind", "status", "summary", "statement", "assumptions", "topic",
                 "sourcePath", "sourceLine", "attachment", "formalization", "date", "pageHref",
                 "englishProof", "additionalAttachments", "leanSource", "sourceHref", "receiptHref",
                 "verification", "sourceLanguage", "scopeNote", "evidenceLevel", "mainResult",
                 "provenanceClassification", "declarationCount", "module", "sha256", "audit"}
    compact_records = []
    for r in records:
        compact = {k: v for k, v in r.items() if k in ui_fields}
        decls = r.get("extractedDeclarations") or r.get("declarations") or []
        names = [d.get("name", "") if isinstance(d, dict) else str(d) for d in decls]
        compact["searchText"] = " ".join(names) + " " + str(r.get("searchText", ""))[:8000]
        compact_records.append(compact)
    browser_catalog = {**catalog, "results": compact_records}
    (DIST / "catalog.js").write_text("window.CHOMP_CATALOG = " + json.dumps(browser_catalog, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/") + ";\n", encoding="utf-8")
    # Ordinary linked HTML navigation is available even without a JavaScript engine.
    ordered = sorted(records, key=lambda r: (r.get("kind") != "paper", r.get("status") == "source-collected", r.get("title", "").lower()))
    chunks = [ordered[i:i + 100] for i in range(0, len(ordered), 100)] or [[]]
    pages = []
    for number, chunk in enumerate(chunks):
        filename = "browse.html" if number == 0 else f"browse-{number + 1}.html"
        pages.append(filename)
        prev = ("browse.html" if number == 1 else f"browse-{number}.html") if number else None
        nxt = f"browse-{number + 2}.html" if number + 1 < len(chunks) else None
        nav = '<div class="pagination">' + (f'<a href="{prev}">← Previous</a>' if prev else "") + f"<span>Page {number + 1} of {len(chunks)}</span>" + (f'<a href="{nxt}">Next →</a>' if nxt else "") + "</div>"
        rows = "".join(f'<article class="result"><p class="meta">{esc(r.get("topic", "Research"))} · {esc(LABELS.get(r.get("status"), r.get("status")))}</p><h2><a href="{r["pageHref"]}">{esc(r.get("title", r["id"]))}</a></h2><p>{esc(r.get("summary", ""))}</p></article>' for r in chunk)
        body = f'<p class="eyebrow">Complete linked index</p><h1>Browse the research library</h1><p>{len(records):,} catalogue records. File versions and source documents are not counts of independent theorems.</p>{nav}{rows}{nav}'
        (DIST / filename).write_text(shell("Browse the research library", body), encoding="utf-8")
    guide = '''<p class="eyebrow">Reading guide</p><h1>From a statement to its evidence</h1><p class="lead">Find a mathematical result, check its hypotheses, and follow the source.</p>
<h2>Three ways into the library</h2><ol><li>Search an English topic, a Lean declaration name, or a phrase in a statement.</li><li>Filter paper results separately from the audited Lean modules.</li><li>Open a result page for its exact scope, original-claim verdict, and source attachment.</li></ol>
<h2>What the labels mean</h2><ul><li><strong>Lean verified:</strong> an exact source snapshot has the recorded verification evidence; inspect its scope.</li><li><strong>Paper proof / reviewed paper proof:</strong> a mathematical proof is recorded; Lean correspondence is stated separately.</li><li><strong>Conditional:</strong> a proved implication whose required hypotheses must still be checked in the intended application.</li><li><strong>Counterexample results:</strong> accepted negative statements are proved within their stated model; they do not refute a stronger canonical claim without a bridge.</li></ul>
<h2>Coverage and reproducibility</h2><p><a href="documentation/AUDIT-SCOPE.html">Scientific audit and release scope</a> · <a href="documentation/LEAN-COVERAGE.html">Lean checks</a> · <a href="documentation/PAPER-COVERAGE.html">Paper-proof coverage</a> · <a href="catalog-full.json.gz">Download the reviewed catalogue</a></p><p>Published descriptions and proofs are in English. The downloadable English proofs use the corrected reviewed statements; superseded original drafts are excluded. Source copies and generated declarations do not constitute additional independent results. Open targets and the unresolved original victim-gate claim are excluded from this result catalogue; the audit scope records these exclusions.</p>
<h2>Published uniqueness result</h2><p>Erez Sheiner, <a href="https://arxiv.org/abs/2605.23837">Unique Winning Opening Move in Three-Row Chomp</a>. Later structural and asymptotic research retains its own proof status.</p>'''
    (DIST / "guide.html").write_text(shell("Reading guide", guide), encoding="utf-8")
    markdown_paths = {"documentation/" + p.name for p in (ROOT / "docs").glob("*.md")}
    markdown_paths.update(re.sub(r"\.html$", ".md", r["englishProof"].split("#")[0]) for r in records if r.get("englishProof"))
    markdown_paths.update(p for p in selected_files if p.endswith('.md') and (p.startswith(('papers/', 'audit/prepublication/')) or p=='RELEASE-NOTES.md' or p in PUBLIC_MATH_DOCS))
    tasks = []
    for relative in sorted(markdown_paths):
        input_path = DIST / relative
        if not input_path.is_file():
            raise FileNotFoundError(f"Missing English proof/document: {relative}")
        output_path = input_path.with_suffix(".html")
        prefix = "../" * len(output_path.relative_to(DIST).parts[:-1])
        text = input_path.read_text(encoding="utf-8-sig")
        title = next((line.lstrip("# ") for line in text.splitlines() if line.startswith("# ")), input_path.stem)
        before, after = shell(title, "<!--DOCUMENT-->", prefix).split("<!--DOCUMENT-->")
        tasks.append({"input": str(input_path), "output": str(output_path), "siteRoot": str(DIST), "before": before, "after": after,
                      "rewriteLeanLinks": relative.startswith("documentation/")})
    if tasks:
        rendered = subprocess.run(["node", str(ROOT / "scripts/render_markdown.mjs")], input=json.dumps(tasks), text=True, check=True, capture_output=True)
        print(rendered.stdout.strip(), flush=True)
    (DIST / ".nojekyll").touch()
    if base_url:
        paths = ["index.html", "guide.html", *pages, *(r["pageHref"] for r in records)]
        xml = '<?xml version="1.0" encoding="UTF-8"?><urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">' + "".join(f"<url><loc>{esc(base_url + '/' + p)}</loc></url>" for p in paths) + "</urlset>"
        (DIST / "sitemap.xml").write_text(xml, encoding="utf-8")
        (DIST / "robots.txt").write_text(f"User-agent: *\nAllow: /\nSitemap: {base_url}/sitemap.xml\n", encoding="utf-8")
    else:
        status = json.loads((ROOT / "PUBLICATION-STATUS.json").read_text(encoding="utf-8"))
        (DIST / "robots.txt").write_text("User-agent: *\n" + ("Allow: /\n" if status.get("releaseApproved") else "Disallow: /\n"), encoding="utf-8")
    print(json.dumps({"site": str(DIST), "stats": stats, "staticResultPages": len(records), "browsePages": len(chunks), "sitemapGenerated": bool(base_url)}))


if __name__ == "__main__":
    main()
