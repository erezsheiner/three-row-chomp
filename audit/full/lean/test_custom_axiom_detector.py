"""Negative control for recursive custom-axiom detection; never an admitted result."""
from pathlib import Path
import json,subprocess,hashlib,datetime as dt
HERE=Path(__file__).resolve().parent
ROOT=HERE/'negative-controls/custom-axiom-detector'
LAKE=Path.home()/'.elan/toolchains/leanprover--lean4---v4.29.1/bin/lake.exe'
ROOT.mkdir(parents=True,exist_ok=True)
(ROOT/'lean-toolchain').write_text('leanprover/lean4:v4.29.1\n')
(ROOT/'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage AuditNegativeControl where\n  moreLeanArgs := #["-DwarningAsError=true"]\n@[default_target]\nlean_lib AuditBadAxiom where\n',encoding='utf8')
(ROOT/'AuditBadAxiom.lean').write_text('-- Intentionally invalid mathematical premise: isolated audit detector test.\naxiom auditForbidden : False\ntheorem auditDerivedFalse : False := auditForbidden\n',encoding='utf8')
manifest=ROOT.parent/'custom-control-manifest.json'
manifest.write_text(json.dumps({'modules':['AuditBadAxiom']}),encoding='utf8')
helper=(HERE.parents[2]/'lean/core/audits/FullKernelAudit.lean').read_text(encoding='utf8')
helper=helper.replace('import ResearchCore\nimport SJSDiagonalDictionary','import AuditBadAxiom').replace('../source-manifest.json','../custom-control-manifest.json').replace('../kernel-census.','../custom-control-kernel-census.')
(ROOT/'AuditDetector.lean').write_text(helper,encoding='utf8')
build=subprocess.run([str(LAKE),'build'],cwd=ROOT,capture_output=True,text=True,encoding='utf8',timeout=120)
assert build.returncode==0,build.stdout+build.stderr
r=subprocess.run([str(LAKE),'env','lean','AuditDetector.lean'],cwd=ROOT,capture_output=True,text=True,encoding='utf8',timeout=120)
log=r.stdout+r.stderr
(ROOT.parent/'custom-axiom-detector.log').write_text(build.stdout+build.stderr+log,encoding='utf8')
summary=json.loads((ROOT.parent/'custom-control-kernel-census.summary.json').read_text(encoding='utf8'))
violations=summary['violations']
assert r.returncode!=0 and {x['name'] for x in violations}=={'auditForbidden','auditDerivedFalse'}
assert all('auditForbidden' in x['nonstandardAxioms'] for x in violations)
(ROOT.parent/'custom-axiom-detector.json').write_text(json.dumps({'result':'passed','exitCode':r.returncode,'meaning':'Passed means the deliberately invalid custom axiom and its derived theorem were both rejected by the exact recursive inspector. This isolated control is excluded from project proof scope.','violationNames':[x['name'] for x in violations],'auditHelperSha256':hashlib.sha256((ROOT/'AuditDetector.lean').read_bytes()).hexdigest(),'sourceSha256':hashlib.sha256((ROOT/'AuditBadAxiom.lean').read_bytes()).hexdigest(),'finishedAt':dt.datetime.now(dt.timezone.utc).isoformat()},indent=2)+'\n',encoding='utf8')
print('Custom-axiom negative control passed: axiom and derived theorem rejected.')
