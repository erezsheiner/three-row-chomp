"""Check the final scientific bytes against independent completed reviews."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
R=HERE.parent.parent/'releases/three-row-chomp-2026-10-14'
if (HERE.parents[2]/'data/reviewed-catalog.json').is_file():
 R=HERE.parents[2] # Same checker packaged under audit/prepublication/root/.
S=R/'site/dist'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text(encoding='utf-8'))
checked={}
def bind(rel,expected,base=R):
 p=base/rel
 assert p.is_file() and sha(p)==expected, 'Reviewed bytes differ: '+str(p)
 checked[str(p.relative_to(R)).replace('\\','/')]=expected
def receipt(rel):
 p=R/'audit/prepublication'/rel
 checked[p.relative_to(R).as_posix()]=sha(p)
 return read(p)
formal=receipt('formal/FINAL-REVIEW.json')
assert formal['result']=='PASS' and formal['modules']==265
ev=receipt('formal/EVIDENCE-FILES.json')
for f in ev['files']:bind('audit/prepublication/formal/'+f['path'],f['sha256'])
lm=read(R/'audit/release/LEAN-FILES.json')
assert lm['moduleCount']==265 and len(lm['files'])==268
for f in lm['files']:bind(f['path'],f['sha256'])
assert lm['formalReviewSha256']==sha(R/lm['formalReviewPath'])
a=receipt('lean-semantics/FINAL-PUBLIC-INTERFACE-COMPARISON.json')
assert a['result']=='PASS' and a['moduleCount']==265 and not a['failures']
bind('data/reviewed-catalog.json',a['catalogueSha256'])
for path,digest in a['documentationSha256'].items():bind(path,digest)
for r in a['records']:
 assert r['result']=='PASS' and not r['findings']
 for stem in ('source','export','page'):bind(r[stem+'Path'],r[stem+'Sha256'])
 bind('sources/'+r['sourcePath'],r['sourceSha256'],S)
 bind(r['exportPath'],r['exportSha256'],S)
b=receipt('papers/FINAL-CANDIDATE-PAPER-REVIEW.json')
assert b['result']=='PASS' and b['recordCount']==59 and b['conditionalCount']==8 and not b['findings']
bind('data/reviewed-catalog.json',b['candidateCatalogueSHA256'])
bind('catalog.js',b['siteCatalogueSHA256'],S)
bind('papers/ENGLISH-PROOFS.md',b['englishBookSHA256'])
bind('audit/prepublication/papers/PAPER-REVIEW.json',b['reviewInputSHA256'])
bind('audit/prepublication/root/SUPPLEMENT-SECOND-REVIEW.json',b['independentSupplementReviewSHA256'])
bind('audit/prepublication/papers/FINITE-CERTIFICATE-REPLAY.json',b['freshFiniteReplaySHA256'])
for r in b['records']:
 assert r['result']=='PASS' and r['correctedFieldScopePreserved']
 bind(r['page'],r['pageSHA256'],S)
 bind('papers/results/'+r['id']+'.md',r['proofSHA256'])
 bind('papers/results/'+r['id']+'.md',r['proofSHA256'],S)
for r in b['supplements']:
 bind(r['path'],r['sha256']);bind(r['path'],r['sha256'],S)
 bind(r['htmlPath'],r['htmlSHA256'],S)
for r in b['certificateFiles']:
 bind(r['path'],r['sha256']);bind(r['path'],r['sha256'],S)
c=receipt('root/SUPPLEMENT-SECOND-REVIEW.json')
assert c['result']=='PASS' and c['supplements']==12 and not c['unresolvedFindings']
for r in c['records']:bind(r['path'],r['sha256'])
rows=read(R/'data/reviewed-catalog.json')
assert len(rows)==324 and len({r['id'] for r in rows})==324
assert not set(b['excludedIds'])&{r['id'] for r in rows}
assert sum(r['kind']=='paper' and r['status']=='conditional' for r in rows)==8
assert sum(r['kind']=='lean' for r in rows)==265
assert receipt('papers/FINITE-CERTIFICATE-REPLAY.json')['result']=='passed'
assert receipt('root/FINITE-GAME-MODEL-CHECK.json')['result']=='PASS'
assert receipt('root/exact-algebra-checks.json')['status']=='PASS'
assert receipt('root/strict-gap-algebra.json')['result']=='PASS'
browser=receipt('root/BROWSER-SMOKE-REVIEW.json')
assert browser['result']=='PASS'
for path,digest in browser['checkedFileHashes'].items():bind(path,digest)
for rel in ('site/ui/index.html','site/ui/app.js','site/dist/index.html','site/dist/app.js'):
 checked[rel]=sha(R/rel)
report={'result':'PASS','scope':'Final byte binding of completed independent model-assisted scientific reviews to the corrected candidate. This check does not itself supply a mathematical proof.','leanModules':265,'serializedDeclarations':21064,'paperResults':59,'conditionalPaperResults':8,'fullProofSupplements':12,'formalEvidencePayloadFiles':len(ev['files']),'excludedIds':b['excludedIds'],'unresolvedFindings':[],'checkedFileHashes':dict(sorted(checked.items())),'published':False}
out=HERE/'FINAL-INTEGRATION-REVIEW.json'
out.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'result':'PASS','boundFiles':len(checked),'sha256':sha(out)}))
