"""Fresh complete formal audit of the exact delivered source ZIP.

All writes are confined to this audit root and the extracted .lake build.
Neither the donor certificate nor the original release is changed.
"""
from pathlib import Path
import concurrent.futures,datetime as dt,hashlib,importlib.util,json,os,re,shutil,subprocess,threading,zipfile

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;PKG=ROOT.parent/'releases/three-row-chomp-2026-10-14';CORE=PKG/'lean/core'
DONOR=ROOT.parent/'three-row-chomp/audit/full/lean/build-final'
LAKE=Path('C:/Users/user/.elan/toolchains/leanprover--lean4---v4.29.1/bin/lake.exe')
LOCK=threading.Lock();STATUS={'state':'preparing','tasks':{}}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text(encoding='utf8'))
def utc():return dt.datetime.now(dt.timezone.utc).isoformat()
def save(p,x):
    tmp=p.with_suffix(p.suffix+'.tmp');tmp.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n',encoding='utf8');tmp.replace(p)
def status(label,value):
    with LOCK:
        STATUS['updatedAt']=utc();STATUS['tasks'][label]=value;save(HERE/'STATUS.json',STATUS)
def run(name,args,cwd=CORE,expect=0):
    command=list(map(str,args));started=utc();status(name,{'state':'running','startedAt':started,'command':command})
    log=HERE/(name+'.log')
    with log.open('wb') as stream:p=subprocess.run(command,cwd=cwd,stdout=stream,stderr=subprocess.STDOUT,timeout=7200)
    passed=(p.returncode==0 if expect==0 else p.returncode!=0)
    receipt={'result':'passed' if passed else 'failed','startedAt':started,'finishedAt':utc(),'exitCode':p.returncode,
      'expectedExit':'zero' if expect==0 else 'nonzero rejection','command':command,'cwd':str(cwd),
      'sourceSnapshotSha256':INPUT['sourceArchiveSha256'],'sourceManifestSha256':sha(HERE/'source-manifest.json'),'logSha256':sha(log)}
    save(HERE/(name+'.json'),receipt);status(name,receipt)
    print(json.dumps({'task':name,'result':receipt['result'],'finishedAt':receipt['finishedAt']}),flush=True)
    if not passed:raise RuntimeError(name+' failed: '+str(log))
    return receipt

def main():
    global INPUT
    INPUT={'sourceArchiveSha256':sha(HERE/'FINAL-SOURCE-HASHES.json')}
    manifest=read(HERE/'frozen-input-manifest.json');modules=manifest['modules']
    assert len(modules)==len(set(modules))==265
    sourcefiles={p.relative_to(CORE).with_suffix('').as_posix().replace('/','.') for p in CORE.rglob('*.lean') if 'audits' not in p.relative_to(CORE).parts and '.lake' not in p.relative_to(CORE).parts and p.name!='lakefile.lean'}
    assert sourcefiles==set(modules)
    sourcebindings={m:sha(CORE/(m.replace('.','/')+'.lean')) for m in modules}
    assert sourcebindings==manifest['sourceSha256']
    zipbindings={'lean/core/'+m.replace('.','/')+'.lean':v for m,v in sourcebindings.items()}
    for name in ['lakefile.lean','lean-toolchain','lake-manifest.json']:zipbindings['lean/core/'+name]=sha(CORE/name)
    basebuild=read(HERE/'clean-strict-build.json')
    assert basebuild['result']=='PASS' and basebuild['exitCode']==0 and basebuild['initialProjectCacheAbsent']
    assert basebuild['sourceHashesSha256']==sha(HERE/'FINAL-SOURCE-HASHES.json') and basebuild['logSha256']==sha(HERE/'clean-strict-build.log')
    assert (CORE/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.29.1'
    assert sha(CORE/'lakefile.lean')==manifest['configurationSha256']
    assert sha(CORE/'lean-toolchain')==manifest['toolchainSha256']
    assert not read(CORE/'lake-manifest.json')['packages'],'Unexpected third-party Lake dependencies'
    for flag in manifest['strictFlags']:assert flag in (CORE/'lakefile.lean').read_text()
    save(HERE/'source-manifest.json',{'modules':modules,'sourceSha256':sourcebindings,'strictFlags':manifest['strictFlags'],
      'configurationSha256':manifest['configurationSha256'],'toolchainSha256':manifest['toolchainSha256'],
      'sourceSnapshotSha256':INPUT['sourceArchiveSha256'],'cleanBuildCacheInitiallyAbsent':True, 'inputKind':'frozen-corrected-source-snapshot', 'parentArchiveSha256':manifest['parentArchiveSha256'],
      'inheritedCurrentGateSha256':sha(PKG/'audit/full/lean/final-gate.json'),'zipMemberSha256':zipbindings})
    version=subprocess.check_output([str(LAKE.with_name('lean.exe')),'--version'],text=True).strip()
    assert 'version 4.29.1' in version
    save(HERE/'toolchain-binding.json',{'version':version,'binarySha256':{n:sha(LAKE.with_name(n)) for n in ['lean.exe','lake.exe','leanchecker.exe']}})
    spec=importlib.util.spec_from_file_location('prep',PKG/'scripts/prepare_lean.py');prep=importlib.util.module_from_spec(spec);spec.loader.exec_module(prep)
    patterns=read(PKG/'audit/full/lean/final-source-trust-scan.json')['patterns'];flags=[];imports={}
    inheritedflags=read(PKG/'audit/full/lean/final-source-trust-scan.json')['reviewedFlags']
    for m in modules:
        masked=prep.mask_noncode((CORE/(m.replace('.','/')+'.lean')).read_text(encoding='utf8'))
        imports[m]=re.findall(r'^\s*(?:public\s+)?import\s+(?:all\s+)?([\w.]+)',masked,re.M)
        for dep in imports[m]:assert dep in modules or dep in ['Lean','Std','Init'],(m,dep)
        for category,pattern in patterns.items():
            for match in re.finditer(pattern,masked):
                old=next((r for r in inheritedflags if r['module']==m and r['category']==category and r['token']==match.group()),None)
                assert old,'Unreviewed source trust mechanism '+m+'/'+match.group()
                flags.append(dict(old,line=masked[:match.start()].count('\n')+1,sourceSha256=sourcebindings[m]))
    save(HERE/'source-coverage-and-trust.json',{'result':'passed','admittedModules':265,'exactZipSourceBindings':True,
      'imports':imports,'reviewedSourceTrustTokens':flags,'meaning':'Lexical coverage supplement; recursive elaborated dependencies and fresh kernel replays are checked separately.'})
    helper=(CORE/'audits/FullKernelAudit.lean').read_text(encoding='utf8')
    helper=helper.replace('import SJSDiagonalDictionary','import SJSDiagonalDictionary\nimport ClaudeFutureFreezeDiagonal')
    helper=helper.replace('../source-manifest.json',(HERE/'source-manifest.json').as_posix()).replace('../kernel-census.',(HERE/'kernel-census.').as_posix())
    (HERE/'FullKernelAudit.lean').write_text(helper,encoding='utf8')
    raw=(CORE/'audits/RawModuleCensus.lean').read_text(encoding='utf8').replace('../source-manifest.json',(HERE/'source-manifest.json').as_posix()).replace('../serialized-module-census.jsonl',(HERE/'serialized-module-census.jsonl').as_posix())
    (HERE/'RawModuleCensus.lean').write_text(raw,encoding='utf8')
    for m in ['R14FrontierLaw','R15ParkedValueSwap']:
        save(HERE/('origin-'+m+'-manifest.json'),{'modules':[m],'sourceSha256':{m:sourcebindings[m]}})
        isolated=helper.replace('import ResearchCore\nimport SJSDiagonalDictionary\nimport ClaudeFutureFreezeDiagonal','import '+m).replace((HERE/'source-manifest.json').as_posix(),(HERE/('origin-'+m+'-manifest.json')).as_posix()).replace((HERE/'kernel-census.').as_posix(),(HERE/('origin-'+m+'-kernel-census.')).as_posix())
        (HERE/('Origin-'+m+'.lean')).write_text(isolated,encoding='utf8')
    shutil.copy2(PKG/'audit/full/lean-documentation-amendment/CompareDeclarations.lean',HERE/'CompareDeclarations.lean')
    STATUS['state']='running';STATUS['startedAt']=utc();status('input-validation',{'result':'passed','modules':265,'snapshotSha256':INPUT['sourceArchiveSha256']})
    status('clean-strict-build',basebuild)
    # Verify the new build produced every admitted module before inspecting it.
    objects={}
    for m in modules:
        rel=Path(m.replace('.','/')+'.olean');obj=CORE/'.lake/build/lib/lean'/rel;assert obj.is_file(),m
        objects[m]={p.name:sha(p) for p in obj.parent.glob(obj.name+'*') if p.is_file()}
    save(HERE/'fresh-object-bindings.json',objects)
    run('full-elaborated-census',[LAKE,'env','lean',HERE/'FullKernelAudit.lean'])
    run('serialized-census',[LAKE,'env','lean','--run',HERE/'RawModuleCensus.lean'])
    for m in ['R14FrontierLaw','R15ParkedValueSwap']:
        run('origin-'+m+'-census',[LAKE,'env','lean',HERE/('Origin-'+m+'.lean')])
    donorobjects={}
    for m in modules:
        p=DONOR/'.lake/build/lib/lean'/(m.replace('.','/')+'.olean');assert p.is_file(),m
        donorobjects[m]={f.name:sha(f) for f in p.parent.glob(p.name+'*') if f.is_file()}
    save(HERE/'inherited-object-bindings.json',{'snapshot':str(DONOR),'objects':donorobjects,
      'meaning':'Read-only preserved full-pass base objects. New source validation/replay is independent; equality additionally binds the delivered proof terms to the inherited certificate.'})
    jobs=[('fresh-replay-'+m,[LAKE,'env',LAKE.with_name('leanchecker.exe'),'--fresh','--verbose',m]) for m in ['ResearchCore','SJSDiagonalDictionary','ClaudeFutureFreezeDiagonal','R14FrontierLaw','R15ParkedValueSwap']]
    jobs.append(('exact-all-declaration-identity',[LAKE,'env','lean','-DwarningAsError=true','--run',HERE/'CompareDeclarations.lean',HERE/'source-manifest.json',DONOR/'.lake/build/lib/lean',CORE/'.lake/build/lib/lean',HERE/'exact-declaration-identity.jsonl']))
    with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
        futures=[pool.submit(run,name,args) for name,args in jobs]
        for future in concurrent.futures.as_completed(futures):future.result()
    for rel,digest in zipbindings.items():assert sha(PKG/rel)==digest,'Source/config changed during audit: '+rel
    STATUS['state']='checks-complete-awaiting-census-reconciliation';status('source-recheck',{'result':'passed'})
    print('All executable checks passed; reconcile full census and seal FORMAL-REVIEW.json.',flush=True)

if __name__=='__main__':
    try:main()
    except BaseException as e:
        STATUS['state']='failed';status('failure',{'type':type(e).__name__,'message':str(e)});raise
