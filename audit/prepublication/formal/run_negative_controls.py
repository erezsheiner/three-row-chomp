"""Fresh isolated controls for strict holes and recursive custom-axiom rejection."""
from pathlib import Path
import datetime as dt,hashlib,json,subprocess
HERE=Path(__file__).resolve().parent;PKG=HERE.parent.parent/'releases/three-row-chomp-2026-10-14';ROOT=HERE/'negative-controls'
LAKE=Path('C:/Users/user/.elan/toolchains/leanprover--lean4---v4.29.1/bin/lake.exe')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n',encoding='utf8')
def run(label,args,expected):
    log=ROOT/(label+'.log');started=dt.datetime.now(dt.timezone.utc).isoformat()
    with log.open('wb') as f:r=subprocess.run(list(map(str,args)),cwd=ROOT,stdout=f,stderr=subprocess.STDOUT,timeout=180)
    assert (r.returncode==0)==(expected==0),(label,r.returncode)
    receipt={'result':'passed','exitCode':r.returncode,'expectedExit':'zero' if expected==0 else 'nonzero rejection',
      'command':list(map(str,args)),'startedAt':started,'finishedAt':dt.datetime.now(dt.timezone.utc).isoformat(),'logSha256':sha(log)}
    save(ROOT/(label+'.json'),receipt);return receipt
ROOT.mkdir(exist_ok=False)
(ROOT/'lean-toolchain').write_bytes((PKG/'lean/core/lean-toolchain').read_bytes())
(ROOT/'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage NegativeAuditControl where\n  moreLeanArgs := #["-DwarningAsError=true"]\n@[default_target]\nlean_lib AuditBadAxiom where\n',encoding='utf8')
source=PKG/'audit/full/lean/negative-controls/custom-axiom-detector/AuditBadAxiom.lean.txt'
(ROOT/'AuditBadAxiom.lean').write_bytes(source.read_bytes())
(ROOT/'RejectSorry.lean').write_bytes((PKG/'audit/full/lean/negative-controls/RejectSorry.lean.txt').read_bytes())
save(ROOT/'source-manifest.json',{'modules':['AuditBadAxiom']})
helper=(PKG/'lean/core/audits/FullKernelAudit.lean').read_text(encoding='utf8').replace('import ResearchCore\nimport SJSDiagonalDictionary','import AuditBadAxiom').replace('../source-manifest.json','source-manifest.json').replace('../kernel-census.','control-kernel-census.')
(ROOT/'AuditDetector.lean').write_text(helper,encoding='utf8')
run('reject-sorry',[LAKE.with_name('lean.exe'),'-DwarningAsError=true','RejectSorry.lean'],1)
run('build-custom-axiom-fixture',[LAKE,'build'],0)
run('reject-custom-axiom-and-derived-proof',[LAKE,'env','lean','AuditDetector.lean'],1)
summary=json.loads((ROOT/'control-kernel-census.summary.json').read_text(encoding='utf8'))
assert {r['name'] for r in summary['violations']}=={'auditForbidden','auditDerivedFalse'}
assert all('auditForbidden' in r['nonstandardAxioms'] for r in summary['violations'])
save(ROOT/'CONTROL-REVIEW.json',{'result':'passed','sorryRejected':True,'customAxiomAndDerivedProofRejected':True,
  'meaning':'These deliberately invalid proof fixtures are separate from the admitted release and are never imported by its modules.',
  'helperSha256':sha(ROOT/'AuditDetector.lean'),'sourceBindings':{name:sha(ROOT/name) for name in ['AuditBadAxiom.lean','RejectSorry.lean','lakefile.lean','lean-toolchain']}})
print('Fresh negative controls passed: sorry rejected; custom axiom and derived theorem both rejected.')
