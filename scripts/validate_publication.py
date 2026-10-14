"""Validate the collected publication's links, IDs and source attachments."""
from __future__ import annotations
from collections import Counter
from datetime import datetime, timezone
from functools import lru_cache
import hashlib
from html.parser import HTMLParser
import json
import os
from pathlib import Path
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
DIST = ROOT / "site/dist"


@lru_cache(maxsize=None)
def resolved_absolute(path: str) -> Path:
    return Path(path).resolve()


def resolved(path: Path) -> Path:
    return resolved_absolute(os.path.abspath(path))


class Links(HTMLParser):
    def __init__(self):
        super().__init__()
        self.links = []
        self.ids = set()
    def handle_starttag(self, tag, attrs):
        for key, value in attrs:
            if key in ("href", "src") and value:
                self.links.append(value)
            if key == "id" and value:
                self.ids.add(value)


def main():
    failures = []
    dist_resolved = resolved(DIST)
    catalog = json.loads((ROOT / "data/catalog.json").read_text(encoding="utf-8"))
    records = catalog["results"]
    counts = Counter(r["id"] for r in records)
    failures.extend(f"Duplicate ID: {k}" for k, v in counts.items() if v != 1)
    attachments = 0
    source_hashes = 0
    for r in records:
        for field in ("pageHref", "attachment"):
            value = r.get(field)
            if value and not (DIST / value).is_file():
                failures.append(f"Missing {field}: {value}")
        attachment = r.get("attachment")
        if attachment:
            attachments += 1
        if attachment and r.get("sha256") and (DIST / attachment).is_file():
            actual = hashlib.sha256((DIST / attachment).read_bytes()).hexdigest()
            if actual != r["sha256"]:
                failures.append(f"Attachment hash mismatch: {r['id']}")
            source_hashes += 1
        if r.get("status") == "lean-verified" and not (r.get("verification") or r.get("evidence") or r.get("verificationEvidence")):
            failures.append(f"Lean-verified record lacks evidence: {r['id']}")
    print(json.dumps({"phase": "attachment hashes", "checked": source_hashes, "failures": len(failures)}), flush=True)
    html_files = list(DIST.rglob("*.html"))
    parsed_files = {}
    for file in html_files:
        parser = Links()
        parser.feed(file.read_text(encoding="utf-8"))
        parsed_files[resolved(file)] = parser
    print(json.dumps({"phase": "HTML parsing", "pages": len(html_files)}), flush=True)
    checked_links = 0
    for file in html_files:
        parser = parsed_files[resolved(file)]
        for link in parser.links:
            parsed = urlsplit(link)
            if parsed.scheme or parsed.netloc:
                continue
            target = resolved(file.parent / unquote(parsed.path)) if parsed.path else resolved(file)
            checked_links += 1
            if not target.is_relative_to(dist_resolved):
                failures.append(f"Link escapes site: {file.relative_to(DIST)} -> {link}")
            elif not target.exists():
                failures.append(f"Broken link: {file.relative_to(DIST)} -> {link}")
            elif parsed.fragment and target.suffix == ".html" and not (target.name == "index.html" and "=" in parsed.fragment):
                target_parser = parsed_files.get(target)
                if target_parser and unquote(parsed.fragment) not in target_parser.ids:
                    failures.append(f"Missing fragment: {file.relative_to(DIST)} -> {link}")
    forbidden = [p.relative_to(DIST).as_posix() for p in DIST.rglob("*") if p.is_file() and (p.suffix in (".olean", ".ilean", ".pyc") or ".lake" in p.parts)]
    failures.extend("Compiled/cache artifact in site: " + p for p in forbidden)
    receipt = {"checkedAt": datetime.now(timezone.utc).isoformat(), "status": "PASS" if not failures else "FAIL",
               "catalogueRecords": len(records), "htmlPages": len(html_files), "localLinksChecked": checked_links,
               "attachments": attachments, "attachmentHashesChecked": source_hashes, "failures": failures,
               "scope": "Package integrity and local link validation only. Mathematical proofs and complete Lean axiom dependencies are not certified by this check."}
    (ROOT / "docs/VALIDATION.json").write_text(json.dumps(receipt, ensure_ascii=False, indent=2), encoding="utf-8")
    print(json.dumps({**receipt, "failures": failures[:30]}, ensure_ascii=False))
    raise SystemExit(0 if not failures else 1)


if __name__ == "__main__":
    main()
