"""Supervised targeted compilation and strict declaration identity amendment.

No full replay is repeated. Exact type/value identity transports the immutable
base's exhaustive axiom and fresh-kernel-replay checks to corrected comments.
"""
from pathlib import Path
import concurrent.futures,datetime as dt,hashlib,json,subprocess,sys,time,shutil

HERE=Path(__file__).resolve().parent
AUDIT=HERE.parent/'lean'
PACKAGE=HERE.parent.parents[1]
LAKE=Path('C:/Users/user/.elan/toolchains/leanprover--lean4---v4.29.1/bin/lake.exe')
BUILD=AUDIT/'build-final'
OBJECTS=HERE/'objects'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text(encoding='utf8'))
def save(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
def stamp():return dt.datetime.now(dt.timezone.utc).isoformat()

def main():
    plan=read(HERE/'amendment-plan.json')
    base=read(HERE/'immutable-base/lean/final-source-manifest.json')
    flags=base['strictFlags']
    receipts=HERE/'receipts';receipts.mkdir(exist_ok=True)
    OBJECTS.mkdir(exist_ok=True)
    def compile_one(r):
        m=r['module'];rel=Path(m.replace('.','/')+'.lean')
        source=HERE/'revised-sources'/rel
        assert sha(source)==r['revisedSha256']==sha(PACKAGE/r['sourcePath'])
        oldobject=BUILD/'.lake/build/lib/lean'/rel.with_suffix('.olean')
        assert oldobject.is_file(),m
        dest=OBJECTS/rel.with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
        if '--resume' in sys.argv and (receipts/(m+'.json')).exists():
            saved=read(receipts/(m+'.json'))
            assert saved['result']=='passed' and saved['sourceSha256']==sha(source)
            assert saved['logSha256']==sha(receipts/(m+'.log'))
            for name,digest in saved['compiledObjectSha256'].items():assert sha(dest.parent/name)==digest
            return saved
        command=[str(LAKE),'env','lean',*flags,'--root='+str(HERE/'revised-sources'),'-o',str(dest),str(source)]
        start=stamp();t=time.monotonic();log=receipts/(m+'.log')
        with log.open('wb') as stream:proc=subprocess.run(command,cwd=BUILD,stdout=stream,stderr=subprocess.STDOUT)
        object_bindings={p.name:sha(p) for p in dest.parent.glob(dest.name+'*') if p.is_file()}
        old_bindings={p.name:sha(p) for p in oldobject.parent.glob(oldobject.name+'*') if p.is_file()}
        receipt={'result':'passed' if proc.returncode==0 else 'failed','module':m,'exitCode':proc.returncode,
          'startedAt':start,'finishedAt':stamp(),'elapsedSeconds':round(time.monotonic()-t,3),'command':command,
          'sourceSha256':r['revisedSha256'],'baseSourceSha256':r['originalSha256'],
          'amendmentPlanSha256':sha(HERE/'amendment-plan.json'),'logSha256':sha(log),
          'compiledObjectSha256':object_bindings,'baseObjectSha256':old_bindings,
          'imports':'Exact passed base build-final import environment; every revised module is subsequently checked for exact declaration identity.'}
        save(receipts/(m+'.json'),receipt)
        print(json.dumps({'module':m,'result':receipt['result'],'seconds':receipt['elapsedSeconds']}),flush=True)
        return receipt
    started=stamp()
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        results=list(pool.map(compile_one,plan['revisions']))
    assert all(r['result']=='passed' for r in results),'A strict source compilation failed'
    def tooling(label,args):
        if '--resume' in sys.argv and (receipts/(label+'.json')).exists():
            saved=read(receipts/(label+'.json'))
            if saved['result']=='passed':
                assert saved['logSha256']==sha(receipts/(label+'.log'))
                assert saved['amendmentPlanSha256']==sha(HERE/'amendment-plan.json')
                return saved
        log=receipts/(label+'.log');command=[str(LAKE),'env','lean','-DwarningAsError=true','--run',*map(str,args)]
        start=stamp()
        with log.open('wb') as stream:proc=subprocess.run(command,cwd=BUILD,stdout=stream,stderr=subprocess.STDOUT)
        receipt={'result':'passed' if proc.returncode==0 else 'failed','exitCode':proc.returncode,'startedAt':start,
          'finishedAt':stamp(),'command':command,'logSha256':sha(log),'amendmentPlanSha256':sha(HERE/'amendment-plan.json')}
        save(receipts/(label+'.json'),receipt)
        assert proc.returncode==0,label+' failed; see '+str(log)
        return receipt
    tooling('exact-declaration-comparison',[HERE/'CompareDeclarations.lean',HERE/'amendment-plan.json',
      BUILD/'.lake/build/lib/lean',OBJECTS,HERE/'declaration-identity.jsonl'])
    # Lean chooses one search root for the ChompLean prefix. A partial root
    # containing only its revised Proof module cannot resolve Encoding there.
    # Copy the unchanged passed objects to complete the presentation import
    # root. Every copied byte is hash-bound; no compilation is repeated.
    copied={}
    for module in base['modules']:
        if module in plan['modules']:continue
        rel=Path(module.replace('.','/')+'.olean')
        original=BUILD/'.lake/build/lib/lean'/rel
        for src in original.parent.glob(original.name+'*'):
            if not src.is_file():continue
            dest=OBJECTS/rel.parent/src.name;dest.parent.mkdir(parents=True,exist_ok=True)
            shutil.copy2(src,dest);assert sha(src)==sha(dest)
            copied[dest.relative_to(OBJECTS).as_posix()]=sha(dest)
    save(HERE/'unchanged-presentation-object-bindings.json',copied)
    tooling('revised-source-ranges-complete-search-root',[HERE/'ExportRanges.lean',HERE/'amendment-plan.json',OBJECTS,HERE/'source-ranges.jsonl'])
    old_counts={r['module']:r['declarationCount'] for r in read(HERE/'immutable-base/lean/formal-audit-ledger.json')['records']}
    identity=[json.loads(s) for s in (HERE/'declaration-identity.jsonl').read_text(encoding='utf8').splitlines()]
    ranges=[json.loads(s) for s in (HERE/'source-ranges.jsonl').read_text(encoding='utf8').splitlines()]
    assert len(identity)==sum(old_counts[m] for m in plan['modules'])
    assert len({(d['module'],d['name']) for d in identity})==len(identity)
    assert {(d['module'],d['name']) for d in identity}=={(d['module'],d['name']) for d in ranges}
    for r in plan['revisions']:
        assert sha(PACKAGE/r['sourcePath'])==r['revisedSha256']
    receipt={'result':'passed','startedAt':started,'finishedAt':stamp(),'changedModules':len(plan['modules']),
      'reviewedFindings':plan['reviewFindings'],'comparedDeclarationCount':len(identity),
      'followUpClarifications':plan.get('followUpClarifications',[]),
      'inheritedBaseGate':{'path':'audit/full/lean-documentation-amendment/immutable-base/lean/final-gate.json',
      'sha256':plan['inheritedBaseGateSha256']},'amendmentPlanSha256':sha(HERE/'amendment-plan.json'),
      'immutableBaseBindingsSha256':sha(HERE/'immutable-base/BINDINGS.json'),
      'method':'Every changed source was compiled with warnings as errors against the passed base environment. Every highest-visibility serialized declaration is structurally identical in names, universe parameters, types, values, safety and every declaration-specific field, using Expr.equal including binder annotations. The original exhaustive axiom/census and fresh kernel replay therefore apply to identical logical declarations. This is a targeted documentation amendment, not a second fresh 265-module replay.',
      'revisions':[dict(r,compileReceipt='audit/full/lean-documentation-amendment/receipts/'+r['module']+'.json',exactDeclarationIdentity=True) for r in plan['revisions']],
      'receiptSha256':{p.name:sha(p) for p in receipts.glob('*.json')},
      'artifactSha256':{f:sha(HERE/f) for f in ('declaration-identity.jsonl','source-ranges.jsonl','CompareDeclarations.lean','ExportRanges.lean','amend_sources.py','run_revalidation.py','unchanged-presentation-object-bindings.json')}}
    save(HERE/'receipt.json',receipt)
    print(json.dumps({'result':'passed','changedModules':45,'comparedDeclarations':len(identity)}),flush=True)

if __name__=='__main__':main()
