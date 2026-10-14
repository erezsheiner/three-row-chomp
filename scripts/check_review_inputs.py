"""Verify exact inputs of this selected release, without approving new claims."""
from pathlib import Path
import hashlib, json
ROOT=Path(__file__).resolve().parents[1]
EXCLUDED={'q-victim-gate-small-class','q-a1-open','q-sublinear-open'}
def verify_reviewed_inputs():
    manifest=json.loads((ROOT/'audit/release/INPUTS.json').read_text(encoding='utf-8'))
    hashes=manifest['files']
    if len(hashes)<330: raise SystemExit('Incomplete release input manifest')
    for rel,expected in hashes.items():
        p=(ROOT/rel).resolve()
        if not p.is_relative_to(ROOT.resolve()) or not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=expected:
            raise SystemExit('Reviewed release input changed or missing: '+rel)
    rows=json.loads((ROOT/'data/reviewed-catalog.json').read_text(encoding='utf-8'))
    if len(rows)!=324 or len({r['id'] for r in rows})!=324 or EXCLUDED & {r['id'] for r in rows}:
        raise SystemExit('Release result selection changed')
    lean=[r for r in rows if r['kind']=='lean']; papers=[r for r in rows if r['kind']=='paper']
    if len(lean)!=265 or len(papers)!=59 or any(r['audit']['originalClaimVerdict'] not in ('accepted','repaired') for r in papers):
        raise SystemExit('Unreviewed claim in release')
    if any(r['status'] not in ('lean-verified','paper-reviewed','conditional') for r in rows):
        raise SystemExit('Open or withheld result in release')
    return len(hashes)
if __name__=='__main__': print('Verified release input hashes:',verify_reviewed_inputs())
