"""Package only exact files listed in the independently checked release manifest."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,zipfile
from check_release_gate import require_approved
ROOT=Path(__file__).resolve().parents[1]
def main():
    require_approved()
    validation=json.loads((ROOT/'docs/VALIDATION.json').read_text(encoding='utf-8'))
    if validation['status']!='PASS': raise SystemExit('Technical validation has not passed')
    manifest=json.loads((ROOT/'audit/release/RELEASE-FILES.json').read_text(encoding='utf-8'))
    outputs=[]
    for kind,base in [('repository',ROOT),('website',ROOT/'site/dist')]:
        files=dict(manifest[kind])
        # These fixed approval-envelope files cannot hash themselves. The gate
        # authenticates their relationship; final ZIP hashes include every byte.
        envelope=['audit/release/REVIEW.json','PUBLICATION-STATUS.json']
        if kind=='repository': envelope+=['audit/release/RELEASE-FILES.json','site/dist/audit/release/REVIEW.json','site/dist/PUBLICATION-STATUS.json']
        for rel in envelope:
            if rel in files: raise ValueError('Approval envelope must not create a hash cycle')
            files[rel]=hashlib.sha256((base/rel).read_bytes()).hexdigest()
        if not files: raise ValueError('Empty release list')
        archive=ROOT.parent/f'{ROOT.name}-{kind}.zip'
        for rel,expected in files.items():
            p=(base/rel).resolve()
            if not p.is_relative_to(base.resolve()) or not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=expected:
                raise ValueError('Release file changed: '+rel)
            if p.stat().st_size>=100*1024*1024: raise ValueError('Oversized individual release file: '+rel)
        with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
            for rel in sorted(files): z.write(base/rel,rel)
        with zipfile.ZipFile(archive) as z:
            if z.testzip() or set(z.namelist())!=set(files): raise ValueError('Archive content/checksum mismatch')
            for rel,expected in files.items():
                if hashlib.sha256(z.read(rel)).hexdigest()!=expected: raise ValueError('Archive byte mismatch: '+rel)
        outputs.append({'kind':kind,'path':str(archive),'files':len(files),'bytes':archive.stat().st_size,
                        'sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'everyArchivedFileHashVerified':True})
    receipt={'createdAt':datetime.now(timezone.utc).isoformat(),'result':'PASS','archives':outputs,
             'published':False,'scope':'Selected release only. The original broader collection remains on HOLD.'}
    (ROOT.parent/f'{ROOT.name}-delivery.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    (ROOT.parent/f'{ROOT.name}-SHA256SUMS.txt').write_text(''.join(x['sha256']+'  '+Path(x['path']).name+'\n' for x in outputs),encoding='ascii')
    print(json.dumps(receipt))
if __name__=='__main__': main()
