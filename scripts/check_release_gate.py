"""The scoped release gate cannot approve the excluded original claims."""
from pathlib import Path
import hashlib,json
from check_review_inputs import verify_reviewed_inputs
from check_presentation_amendment import require_presentation_amendment
ROOT=Path(__file__).resolve().parents[1]

def require_renewed_review(review):
    """An earlier edition's approval cannot admit this corrected edition."""
    required={
        'audit/prepublication/formal/FINAL-REVIEW.json',
        'audit/prepublication/lean-semantics/SEMANTIC-REVIEW.json',
        'audit/prepublication/lean-semantics/FINAL-COMMENT-AMENDMENT-REVIEW.json',
        'audit/prepublication/lean-semantics/FINAL-PUBLIC-INTERFACE-COMPARISON.json',
        'audit/prepublication/papers/PAPER-REVIEW.json',
        'audit/prepublication/papers/FINAL-CANDIDATE-PAPER-REVIEW.json',
        'audit/prepublication/papers/FINITE-CERTIFICATE-REPLAY.json',
        'audit/prepublication/root/SUPPLEMENT-SECOND-REVIEW.json',
        'audit/prepublication/root/FINAL-INTEGRATION-REVIEW.json',
    }
    bound=review.get('independentReviewHashes',{})
    if not required <= set(bound):
        raise SystemExit('PUBLICATION BLOCKED: renewed scientific review is incomplete')
    receipts={p:json.loads((ROOT/p).read_text(encoding='utf-8')) for p in required}
    formal=receipts['audit/prepublication/formal/FINAL-REVIEW.json']
    if formal.get('result')!='PASS' or formal.get('modules')!=265:
        raise SystemExit('PUBLICATION BLOCKED: corrected sources lack a complete fresh formal audit')
    semantic=receipts['audit/prepublication/lean-semantics/SEMANTIC-REVIEW.json']
    if (semantic.get('result')!='passed-with-documentation-corrections-in-candidate'
            or semantic.get('moduleCount')!=265 or semantic.get('unresolvedMathematicalCorrespondenceFindings')!=[]):
        raise SystemExit('PUBLICATION BLOCKED: mathematical correspondence is incomplete')
    for path in ('audit/prepublication/lean-semantics/FINAL-COMMENT-AMENDMENT-REVIEW.json',
                 'audit/prepublication/lean-semantics/FINAL-PUBLIC-INTERFACE-COMPARISON.json',
                 'audit/prepublication/root/FINAL-INTEGRATION-REVIEW.json'):
        if receipts[path].get('result') not in ('PASS','passed'):
            raise SystemExit('PUBLICATION BLOCKED: corrected evidence or public display not verified')
    papers=receipts['audit/prepublication/papers/PAPER-REVIEW.json']
    if papers.get('result')!='PASS' or len(papers.get('records',[]))!=59:
        raise SystemExit('PUBLICATION BLOCKED: complete paper review is missing')
    final_papers=receipts['audit/prepublication/papers/FINAL-CANDIDATE-PAPER-REVIEW.json']
    if final_papers.get('result')!='PASS' or final_papers.get('recordCount')!=59 or final_papers.get('findings')!=[]:
        raise SystemExit('PUBLICATION BLOCKED: public paper proofs have not passed final review')
    if receipts['audit/prepublication/papers/FINITE-CERTIFICATE-REPLAY.json'].get('result')!='passed':
        raise SystemExit('PUBLICATION BLOCKED: finite certificate replay is missing')
    second=receipts['audit/prepublication/root/SUPPLEMENT-SECOND-REVIEW.json']
    if second.get('result')!='PASS' or second.get('supplements')!=12 or second.get('unresolvedFindings')!=[]:
        raise SystemExit('PUBLICATION BLOCKED: full derivations lack an independent second review')
def require_approved():
    verify_reviewed_inputs()
    status=json.loads((ROOT/'PUBLICATION-STATUS.json').read_text(encoding='utf-8'))
    review=json.loads((ROOT/'audit/release/REVIEW.json').read_text(encoding='utf-8'))
    if status.get('status')!='APPROVED_SCOPED_RELEASE' or status.get('releaseApproved') is not True:
        raise SystemExit('PUBLICATION BLOCKED: selected release not approved')
    if review.get('result')!='PASS' or review.get('unresolvedPublishedClaims')!=[]:
        raise SystemExit('PUBLICATION BLOCKED: unresolved included claims')
    require_renewed_review(review)
    require_presentation_amendment(review)
    if review.get('inputManifestSha256')!=hashlib.sha256((ROOT/'audit/release/INPUTS.json').read_bytes()).hexdigest():
        raise SystemExit('PUBLICATION BLOCKED: release inputs differ from reviewed inputs')
    for rel,expected in review.get('independentReviewHashes',{}).items():
        if hashlib.sha256((ROOT/rel).read_bytes()).hexdigest()!=expected:
            raise SystemExit('PUBLICATION BLOCKED: independent review changed')
    if not review.get('independentReviewHashes'): raise SystemExit('PUBLICATION BLOCKED: missing independent review')
    manifest=ROOT/'audit/release/RELEASE-FILES.json'
    if not manifest.is_file() or hashlib.sha256(manifest.read_bytes()).hexdigest()!=review.get('releaseFileManifestSha256'):
        raise SystemExit('PUBLICATION BLOCKED: release file allowlist is not the approved one')
    for rel,expected in json.loads(manifest.read_text(encoding='utf-8'))['repository'].items():
        p=(ROOT/rel).resolve()
        if not p.is_relative_to(ROOT.resolve()) or not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=expected:
            raise SystemExit('PUBLICATION BLOCKED: an approved release file changed: '+rel)
    for rel in ('audit/release/REVIEW.json','PUBLICATION-STATUS.json'):
        if (ROOT/rel).read_bytes()!=(ROOT/'site/dist'/rel).read_bytes():
            raise SystemExit('PUBLICATION BLOCKED: website approval envelope differs from repository')
if __name__=='__main__':
    require_approved()
    print('Selected scientific release gate: PASS')
