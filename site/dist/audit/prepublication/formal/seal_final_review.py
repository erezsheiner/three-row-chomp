"""Reconcile every fresh declaration and seal the exact-ZIP formal verdict."""
from pathlib import Path
import collections,datetime as dt,gzip,hashlib,json,subprocess,zipfile
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;PKG=ROOT.parent/'releases/three-row-chomp-2026-10-14';CORE=PKG/'lean/core'
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text(encoding='utf8'))
def save(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()).hexdigest()
def type_axiom_signature(d):return digest([d['kind'],d['typeExpression'],d['universeParameters'],d['isProof'],sorted(d['axioms'])])
def semantic_signature(d):return digest([type_axiom_signature(d),sorted(d['directTypeDependencies']),sorted(d['directValueDependencies']),d['isUnsafe'],d['isPartial']])

def export_modules(manifest):
    target=HERE/'modules';target.mkdir(exist_ok=True)
    grouped={m:[] for m in manifest['modules']}
    keep=['name','module','kind','isProof','sourceLine','typePretty','axioms','sourceSha256','sourcePath','universeParameters']
    with (HERE/'fresh-declarations.jsonl').open(encoding='utf8') as f:
        for line in f:
            d=json.loads(line);grouped[d['module']].append({k:d[k] for k in keep})
    index=[]
    for m,ds in grouped.items():
        ds.sort(key=lambda d:d['name']);p=target/(m+'.json')
        save(p,{'module':m,'sourcePath':'lean/core/'+m.replace('.','/')+'.lean','sourceSha256':manifest['sourceSha256'][m],'declarationCount':len(ds),'theoremDeclarationCount':sum(d['kind']=='theorem' for d in ds),'proofValuedDeclarationCount':sum(d['isProof'] for d in ds),'scope':'All serialized module declarations including private/generated auxiliaries; not independent theorem counts. Fresh final-source ranges and exact elaborated types.','declarations':ds})
        index.append({'module':m,'sourceSha256':manifest['sourceSha256'][m],'path':'modules/'+m+'.json','sha256':sha(p),'declarations':len(ds)})
    save(HERE/'module-export-index.json',{'modules':index,'declarations':sum(len(x) for x in grouped.values())})


def main():
    manifest=read(HERE/'source-manifest.json');modules=manifest['modules'];inherited=read(PKG/'audit/full/lean/final-gate.json')
    assert read(HERE/'STATUS.json')['state']=='checks-complete-awaiting-census-reconciliation'
    names=['clean-strict-build','full-elaborated-census','serialized-census','origin-R14FrontierLaw-census','origin-R15ParkedValueSwap-census','exact-all-declaration-identity']+['fresh-replay-'+m for m in ['ResearchCore','SJSDiagonalDictionary','ClaudeFutureFreezeDiagonal','R14FrontierLaw','R15ParkedValueSwap']]
    receipts={}
    for name in names:
        r=read(HERE/(name+'.json'));assert r['result'].lower()=='passed' or r['result']=='PASS',name
        assert r['exitCode']==0 and r['logSha256']==sha(HERE/(name+'.log'))
        if name=='clean-strict-build':
            assert r['sourceHashesSha256']==sha(HERE/'FINAL-SOURCE-HASHES.json') and r['initialProjectCacheAbsent']
        else:
            assert r['sourceManifestSha256']==sha(HERE/'source-manifest.json')
            assert r['sourceSnapshotSha256']==manifest['sourceSnapshotSha256']
        receipts[name]=sha(HERE/(name+'.json'))
    assert read(HERE/'negative-controls/CONTROL-REVIEW.json')['result']=='passed'
    imports=read(HERE/'source-coverage-and-trust.json')['imports'];closure=set()
    replay_roots=['ResearchCore','SJSDiagonalDictionary','ClaudeFutureFreezeDiagonal','R14FrontierLaw','R15ParkedValueSwap']
    def visit(module):
        if module in closure:return
        closure.add(module)
        for dependency in imports[module]:
            if dependency in imports:visit(dependency)
    for module in replay_roots:visit(module)
    assert closure==set(modules)
    save(HERE/'module-replay-coverage.json',{'result':'passed','roots':replay_roots,'admittedModules':len(modules),'coveredModules':sorted(closure),'missingModules':[],'sourceImportsEvidenceSha256':sha(HERE/'source-coverage-and-trust.json')})
    summaries=['kernel-census.summary.json','origin-R14FrontierLaw-kernel-census.summary.json','origin-R15ParkedValueSwap-kernel-census.summary.json']
    for name in summaries:assert not read(HERE/name)['violations']
    assert set(read(HERE/'kernel-census.summary.json')['importedIntendedModules'])==set(modules)
    expected={}
    for line in (HERE/'serialized-module-census.jsonl').open(encoding='utf8'):
        d=json.loads(line);key=(d['module'],d['name']);assert key not in expected;expected[key]=d['kind']
    identity={}
    for line in (HERE/'exact-declaration-identity.jsonl').open(encoding='utf8'):
        d=json.loads(line);key=(d['module'],d['name']);assert key not in identity and d['exactTypeValueAndFieldsIdentical'];identity[key]=True
    assert set(identity)==set(expected) and len(expected)==21064
    inherited_gz=PKG/'audit/full/lean/declarations.jsonl.gz'
    assert sha(inherited_gz)==inherited['compressedFullDeclarationCensusSha256']
    prior={};prior_raw_hash=hashlib.sha256();prior_manifest=read(PKG/'audit/full/lean/final-source-manifest.json')
    with gzip.open(inherited_gz,'rb') as f:
        for line in f:
            prior_raw_hash.update(line);d=json.loads(line);key=(d['module'],d['name']);assert key not in prior
            assert d['sourceSha256']==prior_manifest['sourceSha256'][d['module']]
            prior[key]=semantic_signature(d)
    assert prior_raw_hash.hexdigest()==inherited['fullDeclarationCensusSha256'] and set(prior)==set(expected)
    seen={};counts=collections.Counter();permodule=collections.defaultdict(collections.Counter);axioms=set();partial=[];partial_references=[];proof_count=0;duplicate_count=0
    sources=['kernel-census.raw.jsonl','origin-R14FrontierLaw-kernel-census.raw.jsonl','origin-R15ParkedValueSwap-kernel-census.raw.jsonl']
    with (HERE/'fresh-declarations.jsonl').open('w',encoding='utf8') as out:
        for filename in sources:
            for line in (HERE/filename).open(encoding='utf8'):
                d=json.loads(line);key=(d['module'],d['name']);assert key in expected and expected[key]==d['kind']
                assert not d['nonstandardAxioms'] and set(d['axioms'])<=ALLOWED
                assert not d['isUnsafe'] and not d['typeHasMetavariables'] and not d['typeHasFreeVariables'] and d['kind']!='axiom'
                if d['isPartial']:assert d['kind']=='definition' and not d['isProof'] and d['name'].endswith('._unsafe_rec')
                ts=type_axiom_signature(d)
                if key in seen:
                    assert seen[key]==ts;duplicate_count+=1;continue
                seen[key]=ts
                assert semantic_signature(d)==prior[key],'Fresh declaration/census differs from inherited exact final source: '+str(key)
                if d['isPartial']:partial.append({'module':d['module'],'name':d['name'],'isProof':d['isProof']})
                for dependency in d['directTypeDependencies']+d['directValueDependencies']:
                    if dependency.endswith('._unsafe_rec'):partial_references.append({'from':d['name'],'to':dependency,'isProof':d['isProof'],'isPartial':d['isPartial']})
                counts[d['kind']]+=1;permodule[d['module']][d['kind']]+=1;proof_count+=d['isProof'];axioms.update(d['axioms'])
                d['sourceSha256']=manifest['sourceSha256'][d['module']];d['sourcePath']='lean/core/'+d['module'].replace('.','/')+'.lean'
                d['freshCensusOrigin']=filename;d['exactValueIdentityVerified']=True
                out.write(json.dumps(d,ensure_ascii=False,separators=(',',':'))+'\n')
    assert set(seen)==set(expected) and len(partial)==25 and proof_count==20028 and counts['theorem']==19991
    assert all(r['from']==r['to'] and r['isPartial'] and not r['isProof'] for r in partial_references)
    save(HERE/'declaration-completeness.json',{'result':'passed','modules':265,'serializedDeclarations':len(expected),'elaboratedDeclarations':len(seen),'exactIdentityDeclarations':len(identity),'inheritedCensusMatches':len(prior),'isolatedDuplicateChecks':duplicate_count,'declarationKinds':dict(counts),'proofValuedDeclarations':proof_count,'missingDeclarations':[],'unaccountedDeclarations':[],'moduleCounts':{m:dict(permodule[m]) for m in modules}})
    save(HERE/'axiom-and-trust-review.json',{'result':'passed','allowedAxioms':sorted(ALLOWED),'observedAxioms':sorted(axioms),'sorryAx':False,'customAxioms':False,'nativeTrustAxioms':False,'unsafeProjectDeclarations':False,'openTypes':False,'generatedPartialRuntimeHelpers':partial,'partialHelperReferences':partial_references,'logicalDependenciesOnPartialRuntimeHelpers':[],'meaning':'All 21,064 source-module declaration identities were inspected. The only references to partial runtime helpers are their own nonproof self-calls; no logical declaration relies on them.'})
    with (HERE/'fresh-declarations.jsonl').open('rb') as src,(HERE/'fresh-declarations.jsonl.gz').open('wb') as raw:
        with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0,compresslevel=9) as out:
            for chunk in iter(lambda:src.read(1024*1024),b''):out.write(chunk)
    h=hashlib.sha256()
    with gzip.open(HERE/'fresh-declarations.jsonl.gz','rb') as f:
        for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
    assert h.hexdigest()==sha(HERE/'fresh-declarations.jsonl')
    # Current frozen source snapshot, distinct from the historical archive.
    for rel,digest_value in manifest['zipMemberSha256'].items():assert sha(PKG/rel)==digest_value
    assert sha(HERE/'FINAL-SOURCE-HASHES.json')==manifest['sourceSnapshotSha256']
    assert sha(CORE/'lakefile.lean')==manifest['configurationSha256'] and sha(CORE/'lean-toolchain')==manifest['toolchainSha256']
    for m,parts in read(HERE/'fresh-object-bindings.json').items():
        parent=CORE/'.lake/build/lib/lean'/Path(m.replace('.','/')+'.olean').parent
        for name,expected_hash in parts.items():assert sha(parent/name)==expected_hash
    donor=read(HERE/'inherited-object-bindings.json')
    for m,parts in donor['objects'].items():
        parent=Path(donor['snapshot'])/'.lake/build/lib/lean'/Path(m.replace('.','/')+'.olean').parent
        for name,expected_hash in parts.items():assert sha(parent/name)==expected_hash
    # Bind the read-only donor objects back to the previously sealed amendment,
    # rather than merely trusting that a directory named build-final is old.
    amendment_root=PKG/'audit/full/lean-documentation-amendment'
    amendment=read(amendment_root/'receipt.json')
    assert sha(amendment_root/'receipt.json')==inherited['documentationAmendment']['receiptSha256']
    unchanged_name='unchanged-presentation-object-bindings.json'
    assert sha(amendment_root/unchanged_name)==amendment['artifactSha256'][unchanged_name]
    unchanged=read(amendment_root/unchanged_name);revised={r['module'] for r in amendment['revisions']}
    historical_receipts={};bound_parts=0
    for m,parts in donor['objects'].items():
        if m in revised:
            rp=amendment_root/'receipts'/(m+'.json')
            assert sha(rp)==amendment['receiptSha256'][rp.name]
            expected_parts=read(rp)['baseObjectSha256'];historical_receipts[m]=sha(rp)
        else:
            prefix=m.replace('.','/')+'.olean'
            expected_parts={Path(p).name:h for p,h in unchanged.items() if p.startswith(prefix)}
        assert parts==expected_parts,('Unbound historical object bytes',m)
        bound_parts+=len(parts)
    assert len(donor['objects'])==265
    save(HERE/'inherited-base-object-provenance.json',{'result':'passed','modules':265,'objectFileParts':bound_parts,'inheritedAmendmentReceiptSha256':sha(amendment_root/'receipt.json'),'unchangedObjectBindingsSha256':sha(amendment_root/unchanged_name),'changedModuleReceiptSha256':historical_receipts,'currentDonorBindingsSha256':sha(HERE/'inherited-object-bindings.json'),'meaning':'Every donor object byte hash matches a hash recorded in the previously sealed amendment: revised-module receipts bind base objects, and the unchanged-object manifest binds the remaining modules. The comparison donor is therefore tied to inherited evidence, not only its directory name.'})
    runtime=Path('C:/Users/user/.elan/toolchains/leanprover--lean4---v4.29.1/bin/lake.exe')
    observed=subprocess.check_output([str(runtime),'env','lean','--version'],cwd=CORE,text=True).strip()
    assert observed==read(HERE/'toolchain-binding.json')['version']
    save(HERE/'resolved-runtime.json',{'lakeEnvLeanVersion':observed,'matchesPinnedBinary':True})
    report={
      'result':'PASS','modules':265,'completedAt':dt.datetime.now(dt.timezone.utc).isoformat(),'sourceSnapshotSha256':manifest['sourceSnapshotSha256'],'parentArchiveSha256':manifest['parentArchiveSha256'],
      'scope':'Complete new formal verification of the frozen corrected release source snapshot; final archive members must match this source manifest. This report does not publish anything or substitute for the separate paper/content audits.',
      'admittedModules':265,'cleanBuildCacheInitiallyAbsent':True,'allAdmittedModulesBuilt':True,'strictBuildWarningsAsErrors':True,
      'freshKernelReplayRoots':['ResearchCore','SJSDiagonalDictionary','ClaudeFutureFreezeDiagonal','R14FrontierLaw','R15ParkedValueSwap'],
      'declarations':21064,'theoremDeclarations':19991,'proofValuedDeclarations':20028,'countMeaning':'Serialized module declaration identities, including private/generated auxiliaries and duplicate-origin equations; not independent theorem counts.',
      'completeSerializedElaboratedCoverage':True,'allTypesAndValuesIdenticalToInheritedCertificate':True,'inheritedFinalCensusMatches':21064,
      'observedAxioms':sorted(axioms),'sorryAx':False,'customAxioms':False,'nativeTrustAxioms':False,'unsafeProjectDeclarations':False,
      'generatedPartialRuntimeHelpers':25,'logicalDependenciesOnPartialRuntimeHelpers':0,'freshNegativeControls':'passed',
      'receiptSha256':receipts,'sourceManifestSha256':sha(HERE/'source-manifest.json'),'toolchainBindingSha256':sha(HERE/'toolchain-binding.json'),
      'negativeControlsReceiptsSha256':{name:sha(HERE/'negative-controls'/name) for name in ['reject-sorry.json','build-custom-axiom-fixture.json','reject-custom-axiom-and-derived-proof.json']},
      'freshDeclarationCensusSha256':sha(HERE/'fresh-declarations.jsonl'),'compressedFreshDeclarationCensusSha256':sha(HERE/'fresh-declarations.jsonl.gz'),
      'inheritedCurrentGateSha256':sha(PKG/'audit/full/lean/final-gate.json'),
      'limitations':['Fresh replay uses the Lean kernel, not a second proof assistant.','This proves the formal statements with their exact assumptions; it does not promote unproved manuscript targets or infer semantics from successful compilation.','The whole fresh verification used Windows Lean 4.29.1; binaries and commands are recorded.'],
      'evidenceSha256':{name:sha(HERE/name) for name in ['declaration-completeness.json','axiom-and-trust-review.json','source-coverage-and-trust.json','module-replay-coverage.json','fresh-object-bindings.json','inherited-object-bindings.json','inherited-base-object-provenance.json','exact-declaration-identity.jsonl','resolved-runtime.json','negative-controls/CONTROL-REVIEW.json','run_final_checks.py','run_negative_controls.py','seal_final_review.py','FullKernelAudit.lean','RawModuleCensus.lean','CompareDeclarations.lean']}}
    export_modules(manifest)
    report['moduleExportIndexSha256']=sha(HERE/'module-export-index.json')
    save(HERE/'FINAL-REVIEW.json',report)
    (HERE/'FORMAL-REPORT.md').write_text("""# Fresh corrected-source formal review

**PASS.** All 265 final corrected Lean modules were compiled from an absent project build cache with pinned Lean 4.29.1 and warnings treated as errors. The build was launched by the root reviewer and its source-bound receipt is preserved unchanged. The remaining checks were newly executed against those exact compiled modules.

The elaborated and serialized censuses account for 21,064 declaration identities: 19,991 theorem declarations and 20,028 proposition-valued declarations, including private/generated auxiliaries rather than independent results. Isolated R14/R15 inspections recover coalescing equation origins. All exact types, values, binders and declaration-specific fields match the preserved full-pass base objects. Historical source line numbers are not reused: the current census exports current declaration ranges and source hashes for every module.

Five fresh Lean-kernel replay roots passed: ResearchCore, SJSDiagonalDictionary, ClaudeFutureFreezeDiagonal, R14FrontierLaw and R15ParkedValueSwap. All recursive axiom dependencies belong to propext, Classical.choice or Quot.sound. There are no sorry/custom/native trust axioms, unsafe project declarations or open types. The 25 compiler-generated nonproof partial helpers have only self-references and no logical dependency. Fresh isolated controls reject a sorry proof and a deliberately custom axiom plus its derived theorem.

FINAL-REVIEW.json binds the frozen sources, configuration, runtime, receipts, complete losslessly compressed census and per-module exports. This snapshot supersedes an interrupted census of the earlier archive; the earlier archive's full fresh audit is not claimed to have passed. Final ZIP packaging must verify its source/config members against this final manifest. A complete bundle hash is a separate packaging receipt.

The result validates exact formal statements with their own hypotheses. It does not promote stronger paper targets, prove semantic correspondence merely from compilation, or replace the separate manuscript/source-prose audits. Fresh replay uses Lean's own kernel, not a second independent proof assistant. Nothing is published by this audit.
""",encoding='utf8')
    status=read(HERE/'STATUS.json');status.update(state='passed',finishedAt=report['completedAt'],formalReviewSha256=sha(HERE/'FINAL-REVIEW.json'));save(HERE/'STATUS.json',status)
    print(json.dumps({'result':'passed','modules':265,'declarations':21064,'proofValuedDeclarations':20028,'formalReviewSha256':sha(HERE/'FINAL-REVIEW.json')}))

if __name__=='__main__':main()
