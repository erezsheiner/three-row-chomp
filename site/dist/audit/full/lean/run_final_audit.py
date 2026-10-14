"""Final fresh check after documentation-only revisions and FFD promotion."""
from pathlib import Path
import json,shutil,hashlib,subprocess,datetime as dt
HERE=Path(__file__).resolve().parent
PACKAGE=HERE.parents[2]
CORE=PACKAGE/'lean/core'
SNAP=HERE/'build-final'
LAKE=Path.home()/'.elan/toolchains/leanprover--lean4---v4.29.1/bin/lake.exe'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def utc():return dt.datetime.now(dt.timezone.utc).isoformat()
def save(n,o):(HERE/n).write_text(json.dumps(o,indent=2)+'\n',encoding='utf8')
def run(name,args,timeout=3600):
    cmd=[str(LAKE),'env',*map(str,args)]
    if args[0]=='build':cmd=[str(LAKE),*args]
    r={'startedAt':utc(),'command':cmd,'sourceManifestSha256':sha(HERE/'final-source-manifest.json')}
    with (HERE/(name+'.log')).open('w',encoding='utf8') as log:
        p=subprocess.run(cmd,cwd=SNAP,stdout=log,stderr=subprocess.STDOUT,timeout=timeout)
    r.update(finishedAt=utc(),exitCode=p.returncode,result='passed' if p.returncode==0 else 'failed',logSha256=sha(HERE/(name+'.log')))
    save(name+'.json',r);print(name+': '+r['result'],flush=True)
    if p.returncode:raise SystemExit(p.returncode)
if __name__=='__main__':
    assert not SNAP.exists(),'Do not overwrite final audit snapshot.'
    SNAP.mkdir()
    baseline=json.loads((HERE/'source-manifest.json').read_text())
    modules=sorted(baseline['modules']+['ClaudeFutureFreezeDiagonal'])
    hashes={}
    for m in modules:
        rel=m.replace('.','/')+'.lean';src=CORE/rel;dst=SNAP/rel
        dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);hashes[m]=sha(src)
    for name in ('lakefile.lean','lean-toolchain','lake-manifest.json'):shutil.copyfile(CORE/name,SNAP/name)
    save('final-source-manifest.json',{'createdAt':utc(),'modules':modules,'baselineModuleCount':264,'promotedModuleCount':1,'sourceSha256':hashes,'strictFlags':baseline['strictFlags'],'configurationSha256':sha(CORE/'lakefile.lean'),'toolchainSha256':sha(CORE/'lean-toolchain'),'freshBuildDirectory':True,'baselineManifestSha256':sha(HERE/'source-manifest.json'),'documentationRevisionReceiptSha256':sha(HERE/'source-documentation-revisions.json')})
    census=(CORE/'audits/FullKernelAudit.lean').read_text(encoding='utf8').replace('import SJSDiagonalDictionary','import SJSDiagonalDictionary\nimport ClaudeFutureFreezeDiagonal').replace('../source-manifest.json','../final-source-manifest.json').replace('../kernel-census.','../final-kernel-census.')
    raw=(CORE/'audits/RawModuleCensus.lean').read_text(encoding='utf8').replace('../source-manifest.json','../final-source-manifest.json').replace('../serialized-module-census.','../final-serialized-module-census.')
    (SNAP/'FullKernelAudit.lean').write_text(census,encoding='utf8')
    (SNAP/'RawModuleCensus.lean').write_text(raw,encoding='utf8')
    run('final-strict-build',['build','ResearchCore','ChompLean'])
    run('final-environment-census',['lean','FullKernelAudit.lean'])
    run('final-serialized-census',['lean','--run','RawModuleCensus.lean'])
    # Lean may serialize the same generated equation name in more than one
    # module. The combined environment retains one origin, so inspect these
    # two additional origins independently; final comparison requires all.
    for module in ('R14FrontierLaw','R15ParkedValueSwap'):
        save('origin-'+module+'-manifest.json',{'modules':[module],'sourceSha256':{module:hashes[module]}})
        text=census.replace('import ResearchCore\nimport SJSDiagonalDictionary\nimport ClaudeFutureFreezeDiagonal','import '+module).replace('../final-source-manifest.json','../origin-'+module+'-manifest.json').replace('../final-kernel-census.','../origin-'+module+'-kernel-census.')
        (SNAP/'OriginAudit.lean').write_text(text,encoding='utf8')
        run('origin-'+module+'-environment-census',['lean','OriginAudit.lean'])
    for root in ('ResearchCore','SJSDiagonalDictionary','ClaudeFutureFreezeDiagonal','R14FrontierLaw','R15ParkedValueSwap'):
        run('final-replay-'+root,[LAKE.with_name('leanchecker.exe'),'--fresh','--verbose',root])
