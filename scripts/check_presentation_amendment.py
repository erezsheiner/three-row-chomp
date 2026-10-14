"""Authenticate the notice-only WIP delta without relabeling old page hashes."""
from pathlib import Path
import hashlib
import json
import re
from wip_notice import WIP_NOTICE, WIP_HTML, WIP_MARKDOWN

ROOT = Path(__file__).resolve().parents[1]
PARENT_ZIP_SHA256 = 'f89f6c88e71fd9e56bf7a702f20a18c0e69d970eba6308515c32ca561b5a306d'
RECEIPT = 'audit/presentation/AMENDMENT-REVIEW.json'
INDEPENDENT = 'audit/presentation/INDEPENDENT-REVIEW.json'
PARENT = 'audit/presentation/PARENT-ARCHIVE.json'
MARKDOWN = {'README.md', 'papers/ENGLISH-PROOFS.md', 'site/dist/papers/ENGLISH-PROOFS.md'}
IMPLEMENTATION = {'scripts/build_publication.py', 'scripts/check_release_gate.py'}
CONTROLS = {'PUBLICATION-STATUS.json', 'audit/release/INPUTS.json',
            'audit/release/RELEASE-FILES.json', 'audit/release/REVIEW.json',
            'docs/VALIDATION.json', 'site/dist/PUBLICATION-STATUS.json',
            'site/dist/audit/release/INPUTS.json', 'site/dist/audit/release/REVIEW.json'}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def fail(reason):
    raise SystemExit('PUBLICATION BLOCKED: WIP presentation amendment: ' + reason)


def read(rel):
    path = (ROOT / rel).resolve()
    if not path.is_relative_to(ROOT.resolve()) or not path.is_file():
        fail('missing or invalid path ' + rel)
    return path.read_bytes()


def require_presentation_amendment(review):
    binding = review.get('presentationAmendment', {})
    if binding.get('receiptPath') != RECEIPT or binding.get('independentReviewPath') != INDEPENDENT:
        fail('current presentation review is not bound')
    receipt_bytes, independent_bytes = read(RECEIPT), read(INDEPENDENT)
    if sha(receipt_bytes) != binding.get('receiptSha256') or sha(independent_bytes) != binding.get('independentReviewSha256'):
        fail('current presentation review hash differs')
    receipt = json.loads(receipt_bytes)
    independent = json.loads(independent_bytes)
    if receipt.get('result') != 'PASS' or independent.get('result') != 'PASS' or independent.get('findings') != []:
        fail('presentation review did not pass')
    if (receipt.get('parentRepositoryZipSha256') != PARENT_ZIP_SHA256
            or receipt.get('notice') != WIP_NOTICE
            or receipt.get('historicalScientificEvidencePreserved') is not True):
        fail('parent scientific edition or exact notice differs')
    parent_bytes = read(PARENT)
    if sha(parent_bytes) != receipt.get('parentInventorySha256'):
        fail('parent inventory differs')
    parent = json.loads(parent_bytes)
    if parent.get('parentRepositoryZipSha256') != PARENT_ZIP_SHA256 or len(parent.get('files', {})) != 3415:
        fail('wrong parent archive inventory')
    files = parent['files']
    html = {p for p in files if p.startswith('site/dist/') and p.endswith('.html')}
    if len(html) != 432:
        fail('parent HTML coverage differs')
    if {p.relative_to(ROOT).as_posix() for p in (ROOT / 'site/dist').rglob('*.html')} != html:
        fail('public HTML page set differs')
    normalized = receipt.get('noticeOnlyFiles', {})
    if set(normalized) != html | {'site/ui/index.html'} | MARKDOWN:
        fail('notice-only file coverage differs')
    implementations = receipt.get('implementationFiles', {})
    if set(implementations) != IMPLEMENTATION:
        fail('implementation delta scope differs')
    html_notice, markdown_notice = WIP_HTML.encode(), WIP_MARKDOWN.encode()
    for rel, expected in files.items():
        if rel in CONTROLS:
            continue  # Authenticated by the enclosing current release gate.
        content = read(rel)
        if rel in normalized:
            item = normalized[rel]
            if item.get('parentSha256') != expected or item.get('currentSha256') != sha(content):
                fail('notice file hash differs: ' + rel)
            if rel in MARKDOWN:
                if not content.startswith(markdown_notice):
                    fail('missing leading Markdown notice: ' + rel)
                original = content[len(markdown_notice):]
            else:
                matches = list(re.finditer(br'<body(?:\s[^>]*)?>', content, re.I))
                if len(matches) != 1 or content.count(html_notice) != 1:
                    fail('missing or repeated HTML notice: ' + rel)
                pos = matches[0].end()
                if content[pos:pos + len(html_notice)] != html_notice:
                    fail('HTML notice is not the first body content: ' + rel)
                original = content[:pos] + content[pos + len(html_notice):]
            if sha(original) != expected:
                fail('non-notice page or document change: ' + rel)
        elif rel in IMPLEMENTATION:
            item = implementations[rel]
            if item.get('parentSha256') != expected or item.get('currentSha256') != sha(content):
                fail('reviewed implementation differs: ' + rel)
        elif sha(content) != expected:
            fail('parent scientific or supporting file changed: ' + rel)
    for rel, expected in receipt.get('newPresentationFiles', {}).items():
        if sha(read(rel)) != expected:
            fail('new presentation implementation differs: ' + rel)
    if sha(read('data/reviewed-catalog.json')) != receipt.get('reviewedCatalogueSha256'):
        fail('reviewed mathematical catalogue changed')
    if sha(read('audit/presentation/parent/REVIEW.json')) != binding.get('parentScientificReviewSha256'):
        fail('historical scientific approval differs')
    if review.get('pageHashEvidenceScope') != 'Parent page hashes are historical; current pages are authenticated by the additive WIP presentation amendment.':
        fail('historical page-hash scope is not explicit')
    return len(html)
