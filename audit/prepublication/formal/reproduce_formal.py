"""Portable fresh verification. Run from any location; outputs stay in a new directory.

python reproduce_formal.py --repository /path/to/repository --output /new/audit/path
Add --compare-inherited to rebuild the preserved baseline and compare every term.
Requires Python 3 and the repository's pinned Lean/Lake toolchain via elan.
"""
from pathlib import Path
import argparse,collections,datetime,gzip,hashlib,json,shutil,subprocess

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text(encoding='utf8'))
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n',encoding='utf8')
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--repository',required=True,type=Path);ap.add_argument('--output',required=True,type=Path);ap.add_argument('--compare-inherited',action='store_true');ap.add_argument('--lake',default='lake');a=ap.parse_args()
 repo=a.repository.resolve();out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
 evidence=Path(__file__).resolve().parent;manifest=read(evidence/'source-manifest.json');mods=manifest['modules'];core=out/'core';core.mkdir()
 receipts={}
 def run(name,args,cwd=core,expect=0):
  start=datetime.datetime.now(datetime.timezone.utc).isoformat();log=out/(name+'.log')
  with log.open('wb') as f:r=subprocess.run(list(map(str,args)),cwd=cwd,stdout=f,stderr=subprocess.STDOUT)
  assert (r.returncode==0)==(expect==0),(name,r.returncode,str(log))
  rec={'result':'PASS','exitCode':r.returncode,'expectedExit':expect,'command':list(map(str,args)),'startedAt':start,'finishedAt':datetime.datetime.now(datetime.timezone.utc).isoformat(),'logSha256':sha(log)}
  save(out/(name+'.json'),rec);receipts[name]=sha(out/(name+'.json'));print(name,'PASS',flush=True)
 def copy_core(target,source_hashes,baseline=False):
  if target!=core:target.mkdir()
  correction=read(evidence/'COMMENT-CORRECTIONS-APPLIED.json');changes={x['module']:x for x in correction['files']}
  preserved=repo/'audit/full/lean-documentation-amendment/immutable-base/sources'
  for m in mods:
   rel=m.replace('.','/')+'.lean';p=repo/'lean/core'/rel;data=p.read_bytes()
   if baseline:
    old=preserved/(rel+'.txt')
    if old.exists():data=old.read_bytes()
    elif m in changes:
     for change in reversed(changes[m]['changes']):
      x=change['replacement'].encode();y=change['old'].encode();assert data.count(x)==1;data=data.replace(x,y)
   assert hashlib.sha256(data).hexdigest()==source_hashes[m],m
   dest=target/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
  for name in ['lakefile.lean','lean-toolchain','lake-manifest.json']:
   p=repo/'lean/core'/name;assert sha(p)==manifest['zipMemberSha256']['lean/core/'+name];shutil.copy2(p,target/name)
 copy_core(core,manifest['sourceSha256'])
 version=subprocess.check_output([a.lake,'env','lean','--version'],cwd=core,text=True).strip();assert 'version 4.29.1' in version
 run('clean-strict-build',[a.lake,'build','ResearchCore','ChompLean'])
 save(out/'source-manifest.json',manifest)
 helper=(repo/'lean/core/audits/FullKernelAudit.lean').read_text(encoding='utf8').replace('import SJSDiagonalDictionary','import SJSDiagonalDictionary\nimport ClaudeFutureFreezeDiagonal')
 helper=helper.replace('../source-manifest.json',(out/'source-manifest.json').as_posix()).replace('../kernel-census.',(out/'kernel-census.').as_posix())
 (out/'FullKernelAudit.lean').write_text(helper,encoding='utf8')
 run('full-elaborated-census',[a.lake,'env','lean',out/'FullKernelAudit.lean'])
 raw=(repo/'lean/core/audits/RawModuleCensus.lean').read_text(encoding='utf8').replace('../source-manifest.json',(out/'source-manifest.json').as_posix()).replace('../serialized-module-census.jsonl',(out/'serialized-module-census.jsonl').as_posix())
 (out/'RawModuleCensus.lean').write_text(raw,encoding='utf8');run('serialized-census',[a.lake,'env','lean','--run',out/'RawModuleCensus.lean'])
 files=[out/'kernel-census.raw.jsonl']
 for m in ['R14FrontierLaw','R15ParkedValueSwap']:
  pm=out/(m+'-manifest.json');save(pm,{'modules':[m]})
  ph=out/(m+'Audit.lean');text=helper.replace('import ResearchCore\nimport SJSDiagonalDictionary\nimport ClaudeFutureFreezeDiagonal','import '+m).replace((out/'source-manifest.json').as_posix(),pm.as_posix()).replace((out/'kernel-census.').as_posix(),(out/(m+'-kernel-census.')).as_posix());ph.write_text(text,encoding='utf8')
  run(m+'-origin-census',[a.lake,'env','lean',ph]);files.append(out/(m+'-kernel-census.raw.jsonl'))
 roots=['ResearchCore','SJSDiagonalDictionary','ClaudeFutureFreezeDiagonal','R14FrontierLaw','R15ParkedValueSwap']
 for m in roots:run('fresh-replay-'+m,[a.lake,'env','leanchecker','--fresh','--verbose',m])
 expected={}
 for line in (out/'serialized-module-census.jsonl').open(encoding='utf8'):
  d=json.loads(line);key=(d['module'],d['name']);assert key not in expected;expected[key]=d['kind']
 seen={};partial=[];proofs=0;counts=collections.Counter();axioms=set()
 for f in files:
  for line in f.open(encoding='utf8'):
   d=json.loads(line);key=(d['module'],d['name']);assert expected[key]==d['kind']
   assert not d['nonstandardAxioms'] and set(d['axioms'])<={'propext','Classical.choice','Quot.sound'}
   assert not d['isUnsafe'] and not d['typeHasMetavariables'] and not d['typeHasFreeVariables'] and d['kind']!='axiom'
   sig=[d['typeExpression'],d['universeParameters'],d['isProof'],sorted(d['axioms'])]
   if key in seen:assert seen[key]==sig;continue
   seen[key]=sig;counts[d['kind']]+=1;proofs+=d['isProof'];axioms.update(d['axioms'])
   if d['isPartial']:assert d['kind']=='definition' and not d['isProof'] and d['name'].endswith('._unsafe_rec');partial.append(key)
   for dep in d['directTypeDependencies']+d['directValueDependencies']:
    if dep.endswith('._unsafe_rec'):assert dep==d['name'] and d['isPartial'] and not d['isProof']
 assert set(seen)==set(expected) and len(seen)==21064 and proofs==20028 and counts['theorem']==19991 and len(partial)==25
 if a.compare_inherited:
  base=repo/'audit/full/lean-documentation-amendment/immutable-base/lean/final-source-manifest.json';old=read(base);baseline=out/'baseline-core';copy_core(baseline,old['sourceSha256'],True)
  run('baseline-clean-build',[a.lake,'build','ResearchCore','ChompLean'],baseline)
  run('exact-all-declaration-identity',[a.lake,'env','lean','-DwarningAsError=true','--run',evidence/'CompareDeclarations.lean',out/'source-manifest.json',baseline/'.lake/build/lib/lean',core/'.lake/build/lib/lean',out/'exact-declaration-identity.jsonl'])
  ds=[json.loads(l) for l in (out/'exact-declaration-identity.jsonl').open(encoding='utf8')];assert len(ds)==21064 and all(d['exactTypeValueAndFieldsIdentical'] for d in ds)
 # Negative controls are isolated and never imported by the proof library.
 neg=out/'negative-controls';neg.mkdir();fixture=repo/'audit/full/lean/negative-controls'
 shutil.copy2(core/'lean-toolchain',neg/'lean-toolchain')
 (neg/'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage NegativeControl where\n  moreLeanArgs := #["-DwarningAsError=true"]\n@[default_target]\nlean_lib AuditBadAxiom where\n',encoding='utf8')
 shutil.copy2(fixture/'RejectSorry.lean.txt',neg/'RejectSorry.lean');shutil.copy2(fixture/'custom-axiom-detector/AuditBadAxiom.lean.txt',neg/'AuditBadAxiom.lean')
 save(neg/'source-manifest.json',{'modules':['AuditBadAxiom']})
 text=(repo/'lean/core/audits/FullKernelAudit.lean').read_text(encoding='utf8').replace('import ResearchCore\nimport SJSDiagonalDictionary','import AuditBadAxiom').replace('../source-manifest.json','source-manifest.json').replace('../kernel-census.','control-kernel-census.')
 (neg/'AuditDetector.lean').write_text(text,encoding='utf8')
 run('reject-sorry',[a.lake,'env','lean','-DwarningAsError=true','RejectSorry.lean'],neg,1);run('custom-fixture-build',[a.lake,'build'],neg)
 run('reject-custom-axiom',[a.lake,'env','lean','AuditDetector.lean'],neg,1)
 assert {x['name'] for x in read(neg/'control-kernel-census.summary.json')['violations']}=={'auditForbidden','auditDerivedFalse'}
 for m in mods:assert sha(core/(m.replace('.','/')+'.lean'))==manifest['sourceSha256'][m]
 save(out/'REPRODUCTION-REVIEW.json',{'result':'PASS','modules':265,'declarations':21064,'proofValuedDeclarations':20028,'observedAxioms':sorted(axioms),'freshReplayRoots':roots,'exactInheritedIdentityReproduced':a.compare_inherited,'toolchain':version,'receipts':receipts})
 print('Complete fresh reproduction PASS',flush=True)
if __name__=='__main__':main()
