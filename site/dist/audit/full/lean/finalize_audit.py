"""Executable source, kernel, declaration-completeness and claim-scope gate.

Run only after run_final_audit.py completes. This gate does not admit unresolved
paper claims or infer mathematics from source filenames.
"""
from pathlib import Path
import collections,datetime as dt,gzip,hashlib,importlib.util,json,re,shutil,sys
HERE=Path(__file__).resolve().parent
PACKAGE=HERE.parents[2]
CORE=PACKAGE/'lean/core'
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(n,o):(HERE/n).write_text(json.dumps(o,indent=2,ensure_ascii=False)+'\n',encoding='utf8')
def read(n):return json.loads((HERE/n).read_text(encoding='utf8'))
def check(v,msg):
    if not v:raise AssertionError(msg)
def main():
    manifest=read('final-source-manifest.json');modules=manifest['modules'];sources=manifest['sourceSha256']
    baseline=read('source-manifest.json')
    check(len(modules)==265 and len(set(modules))==265,'Expected 264 baseline plus 1 promoted module')
    check(set(modules)==set(baseline['modules'])|{'ClaudeFutureFreezeDiagonal'},'Unexpected final source scope')
    actual={str(p.relative_to(CORE).with_suffix('')).replace('\\','/').replace('/','.') for p in CORE.rglob('*.lean') if p.name!='lakefile.lean' and 'audits' not in p.relative_to(CORE).parts and '.lake' not in p.relative_to(CORE).parts}
    check(actual==set(modules),'Unaccounted public proof source module')
    for module,digest in sources.items():
        rel=module.replace('.','/')+'.lean'
        check(sha(CORE/rel)==digest,module+' public source changed')
        check(sha(HERE/'build-final'/rel)==digest,module+' final snapshot changed')
    check(sha(CORE/'lakefile.lean')==manifest['configurationSha256'],'Publication configuration changed')
    check(sha(HERE/'build-final/lakefile.lean')==manifest['configurationSha256'],'Build configuration differs')
    check((CORE/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.29.1','Wrong Lean version')
    check(sha(CORE/'lean-toolchain')==manifest['toolchainSha256'],'Public toolchain file changed')
    check(sha(HERE/'build-final/lean-toolchain')==manifest['toolchainSha256'],'Snapshot toolchain file changed')
    check('-DwarningAsError=true' in manifest['strictFlags'],'Warnings were not errors')
    receipt_names=['final-strict-build','final-environment-census','final-serialized-census','origin-R14FrontierLaw-environment-census','origin-R15ParkedValueSwap-environment-census','final-replay-ResearchCore','final-replay-SJSDiagonalDictionary','final-replay-ClaudeFutureFreezeDiagonal','final-replay-R14FrontierLaw','final-replay-R15ParkedValueSwap']
    receipts={}
    for name in receipt_names:
        r=read(name+'.json');check(r['result']=='passed' and r['exitCode']==0,name+' did not pass')
        check(r['sourceManifestSha256']==sha(HERE/'final-source-manifest.json'),name+' manifest mismatch')
        check(r['logSha256']==sha(HERE/(name+'.log')),name+' log mismatch')
        receipts[name]=sha(HERE/(name+'.json'))
    check(read('negative-controls/reject-sorry.json')['result']=='passed','Sorry rejection control failed')
    check(read('negative-controls/custom-axiom-detector.json')['result']=='passed','Recursive custom-axiom negative control failed')
    check(read('final-kernel-census.summary.json')['violations']==[],'Environment violations')
    expected={};serialized_count=0
    for line in (HERE/'final-serialized-module-census.jsonl').open(encoding='utf8'):
        d=json.loads(line);key=(d['module'],d['name']);serialized_count+=1
        check(key not in expected,'Repeated serialized declaration identity '+str(key));expected[key]=d['kind']
    needed_main_names={n for m in read('main-claim-mapping.json')['mappings'] for n in m['requiredDeclarations']}
    main_expression_types={}
    seen={};duplicate_checks=0;by_module={m:[] for m in modules};axioms=set();kind_counts=collections.Counter();proof_count=0;partial_helpers=[];partial_references=[]
    summary_keys=('name','module','kind','isProof','sourceLine','typePretty','axioms','sourceSha256','sourcePath','universeParameters')
    inputs=['final-kernel-census.raw.jsonl','origin-R14FrontierLaw-kernel-census.raw.jsonl','origin-R15ParkedValueSwap-kernel-census.raw.jsonl']
    with (HERE/'declarations.jsonl').open('w',encoding='utf8') as output:
        for filename in inputs:
            for line in (HERE/filename).open(encoding='utf8'):
                d=json.loads(line);key=(d['module'],d['name'])
                check(key in expected,'Unserialized environment entry '+str(key));check(expected[key]==d['kind'],'Kind mismatch '+str(key))
                check(not d['nonstandardAxioms'] and set(d['axioms'])<=ALLOWED,'Forbidden axiom '+str(key))
                check(not d['isUnsafe'],'Unsafe project declaration '+str(key))
                if d['isPartial']:
                    check(d['kind']=='definition' and not d['isProof'] and d['name'].endswith('._unsafe_rec'),'Unexpected partial declaration '+str(key))
                check(not d['typeHasMetavariables'] and not d['typeHasFreeVariables'],'Open elaborated type '+str(key))
                check(d['kind']!='axiom','Project axiom '+str(key))
                signature=hashlib.sha256(json.dumps([d['kind'],d['typeExpression'],sorted(d['axioms'])],sort_keys=True).encode()).hexdigest()
                if key in seen:
                    check(seen[key]==signature,'Different isolated type/axioms for '+str(key));duplicate_checks+=1;continue
                seen[key]=signature;d['sourceSha256']=sources[d['module']];d['sourcePath']='lean/core/'+d['module'].replace('.','/')+'.lean'
                if d['name'] in needed_main_names:main_expression_types[d['name']]=d['typeExpression']
                if d['isPartial']:partial_helpers.append({'module':d['module'],'name':d['name'],'isProof':d['isProof'],'sourceSha256':d['sourceSha256']})
                for dependency in d['directTypeDependencies']+d['directValueDependencies']:
                    if dependency.endswith('._unsafe_rec'):partial_references.append({'from':d['name'],'to':dependency,'isProof':d['isProof'],'isPartial':d['isPartial']})
                d['censusOrigin']=filename;d['fullTypeMeaning']='Elaborated expression tree; binder indices and universes retained. Metadata payloads omitted, semantic body retained.'
                output.write(json.dumps(d,ensure_ascii=False,separators=(',',':'))+'\n')
                by_module[d['module']].append({k:d[k] for k in summary_keys})
                axioms.update(d['axioms']);kind_counts[d['kind']]+=1;proof_count+=d['isProof']
    check(set(seen)==set(expected),'Serialized declarations missing from elaborated census: '+str(sorted(set(expected)-set(seen))))
    check(len(partial_helpers)==25,'Unexpected generated partial helper scope')
    check(all(r['from']==r['to'] and r['isPartial'] and not r['isProof'] for r in partial_references),'Logical declaration depends on a partial compiler helper')
    save('generated-partial-helper-review.json',{'result':'passed','count':len(partial_helpers),'helpers':partial_helpers,'references':partial_references,'logicalDeclarationReferences':[],'meaning':'Lean creates runtime recursion implementations named ._unsafe_rec with DefinitionSafety.partial. They remain in the exhaustive census. None is proposition-valued; the only references to them in project declaration types/values are their own recursive self-calls. Logical definitions and proofs do not use these runtime implementations.','compilerSource':'Lean/Elab/PreDefinition/Basic.lean:addAndCompilePartialRec, Lean 4.29.1, creates DefinitionSafety.partial and Compiler.mkUnsafeRecName; Lean/Compiler/LCNF/ToDecl.lean:getDeclInfo? selects these for code generation.'})
    # Source scanning supplements, rather than substitutes for, recursive
    # environment axiom inspection and the fresh kernel replay.
    spec=importlib.util.spec_from_file_location('prepare',PACKAGE/'scripts/prepare_lean.py');prep=importlib.util.module_from_spec(spec);spec.loader.exec_module(prep)
    patterns={
      'proof_hole_or_axiom':r'\b(sorry|admit|axiom)\b',
      'unsafe_or_native_trust':r'\b(unsafe|native_decide|ofReduceBool|ofReduceNat|skipKernel|skipKernelTC|trustLevel|implemented_by|extern)\b',
      'custom_elaboration':r'\b(elab|macro|macro_rules|elab_rules|builtin_elab|syntax|initialize|builtin_initialize|run_cmd|run_meta|run_tac|run_elab)\b',
      'warning_override':r'\bset_option\s+warningAsError\s+false\b',
      'evaluation':r'#(?:eval|eval!|reduce)\b'}
    flags=[]
    for m in modules:
        source=(CORE/(m.replace('.','/')+'.lean')).read_text(encoding='utf8');masked=prep.mask_noncode(source)
        for category,pattern in patterns.items():
            for match in re.finditer(pattern,masked):
                row={'module':m,'sourceSha256':sources[m],'category':category,'line':masked[:match.start()].count('\n')+1,'token':match.group()}
                if category=='custom_elaboration' and m=='EarlyCol16Col17Rails' and row['token']=='macro':
                    row['disposition']='Reviewed proof-producing tactic quotation: finite witnesses, intro/rcases, omega and simp. No environment mutation or unsafe evaluation.'
                elif category=='evaluation' and m=='SJSDiagonalDictionary' and row['token']=='#eval':
                    row['disposition']='Finite computation of initial terms, excluded from theorem evidence.'
                else:raise AssertionError('Unreviewed source trust token '+str(row))
                flags.append(row)
    check(len([r for r in flags if r['category']=='custom_elaboration'])==6,'Unexpected macro review scope')
    save('final-source-trust-scan.json',{'result':'passed','sourceManifestSha256':sha(HERE/'final-source-manifest.json'),'patterns':patterns,'reviewedFlags':flags,'allowedAxioms':sorted(ALLOWED),'observedAxioms':sorted(axioms),'meaning':'No source trust bypass found. A lexical scan alone is not a kernel certificate; all elaborated dependencies and fresh kernel replay are checked separately.'})
    mappings=read('main-claim-mapping.json');main_by_module={x['module']:x for x in mappings['mappings']}
    check(len(main_by_module)==14,'Principal mapping coverage mismatch')
    reviews=read('non-main-summary-review.json');other_by_module={x['module']:x for x in reviews['modules']}
    check(len(other_by_module)==251 and not(set(main_by_module)&set(other_by_module)),'Other-module coverage mismatch')
    check(set(main_by_module)|set(other_by_module)==set(modules),'Semantic metadata coverage incomplete')
    catalogue=json.loads((PACKAGE/'data/formal-catalog.json').read_text(encoding='utf8'))
    by_id={x['id']:x for x in catalogue}
    corrections=read('catalogue-corrections.json');correction_by_module={x['module']:x for x in corrections['corrections']}
    ledger=[];(HERE/'modules').mkdir(exist_ok=True)
    for module in modules:
        decls=sorted(by_module[module],key=lambda x:(x['sourceLine'] or 0,x['name']))
        counts=dict(collections.Counter(x['kind'] for x in decls));proofs=sum(x['isProof'] for x in decls)
        main=main_by_module.get(module);review=main or other_by_module[module];original=by_id[review['catalogueId']]
        change=correction_by_module.get(module,{}).get('changes',{})
        if main:
            declarations_by_name={d['name']:d for d in decls}
            for required in main['requiredDeclarations']:check(required in declarations_by_name,'Missing main exact declaration '+required)
            # Replace initial source anchors/pretty types with final elaboration.
            for d in main['declarations']:
                final=declarations_by_name[d['name']]
                d.update({k:final[k] for k in ('sourceLine','typePretty','axioms','sourceSha256')})
                d['typeExpression']=main_expression_types[d['name']]
            main['kernelVerdict']='passed-final-source-bound-census-and-replay'
        attachment='audit/full/lean/modules/'+module+'.json'
        save('modules/'+module+'.json',{'module':module,'sourceSha256':sources[module],'declarationCount':len(decls),'theoremDeclarationCount':counts.get('theorem',0),'proofValuedDeclarationCount':proofs,'scope':'All serialized module declarations including private/generated auxiliaries. These are declaration counts, not counts of independent mathematical results.','declarations':decls,'fullExpressionTrees':'audit/full/lean/declarations.jsonl'})
        ledger.append({'id':original['id'],'module':module,'sha256':sources[module],'originalSha256':original['sha256'],'sourcePath':'lean/core/'+module.replace('.','/')+'.lean','attachment':'sources/lean/core/'+module.replace('.','/')+'.lean','title':change.get('title',original['title']),'summary':change.get('summary',original['summary']),'assumptions':change.get('assumptions','Every declaration retains its exact explicit and implicit hypotheses in the attached elaborated type. The generic module summary is inventory metadata, not an unconditional mathematical theorem.'),'mainResult':original.get('mainResult',False),'baselineModule':module!='ClaudeFutureFreezeDiagonal','status':'lean-verified','kernelVerdict':'passed','semanticVerdict':review['verdict'],'semanticScope':main['semanticReview'] if main else review['mathematicalAssertion'],'notEstablished':main['notEstablished'] if main else (['The all-row SJS dword/gameF bridge remains unproved.'] if module=='SJSDiagonalDictionary' else []),'declarationCount':len(decls),'lexicalDeclarationCount':original['declarationCount'],'theoremDeclarationCount':counts.get('theorem',0),'proofValuedDeclarationCount':proofs,'declarationCountsByKind':counts,'observedAxioms':sorted({a for d in decls for a in d['axioms']}),'declarationsAttachment':attachment,'auditReceipt':'audit/full/lean/final-gate.json'})
    save('main-claim-mapping.json',mappings)
    save('formal-audit-ledger.json',{'scope':'264 baseline module records and1 promoted FFD dependency; original IDs retained with final exact source hashes. Conditional interfaces remain conditional; declaration counts include generated auxiliaries.','moduleCount':265,'records':ledger})
    with (HERE/'declaration-index.jsonl').open('w',encoding='utf8') as index:
        for module in modules:
            for d in by_module[module]:index.write(json.dumps(d,ensure_ascii=False,separators=(',',':'))+'\n')
    with (HERE/'declarations.jsonl').open('rb') as src,(HERE/'declarations.jsonl.gz').open('wb') as raw:
        with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0,compresslevel=9) as compressed:shutil.copyfileobj(src,compressed)
    decompressed=hashlib.sha256()
    with gzip.open(HERE/'declarations.jsonl.gz','rb') as compressed:
        for chunk in iter(lambda:compressed.read(1024*1024),b''):decompressed.update(chunk)
    check(decompressed.hexdigest()==sha(HERE/'declarations.jsonl'),'Compressed census failed lossless validation')
    save('declaration-completeness.json',{'result':'passed','moduleCount':265,'baselineModuleCount':264,'extensionModuleCount':1,'serializedDeclarationCount':serialized_count,'elaboratedDeclarationCount':len(seen),'theoremDeclarationCount':kind_counts['theorem'],'proofValuedDeclarationCount':proof_count,'kinds':dict(kind_counts),'missingSerializedDeclarations':[],'unserializedEnvironmentDeclarations':[],'isolatedOriginChecksCompared':duplicate_checks,'duplicateNameExplanation':'Generated equation declarations can be serialized by multiple modules under one name. Isolated R14/R15 environments recover every source-module identity; each identity is counted, not claimed to be a unique mathematical theorem.','observedAxioms':sorted(axioms),'forbiddenAxioms':[],'fullCensusSha256':sha(HERE/'declarations.jsonl'),'compressedFullCensusSha256':sha(HERE/'declarations.jsonl.gz'),'compactIndexSha256':sha(HERE/'declaration-index.jsonl'),'sourceManifestSha256':sha(HERE/'final-source-manifest.json')})
    independent=['independent-uniqueness-review.md','../CANONICAL-FOUNDATIONS.md']
    for f in independent:check((HERE/f).is_file(),'Missing independent review '+f)
    result={'result':'passed','finishedAt':dt.datetime.now(dt.timezone.utc).isoformat(),'scope':'Strict source-bound Lean acceptance, exhaustive declaration/axiom census and exact reviewed catalogue semantics for 265 modules. This is not an approval to publish and does not close unresolved paper claims.','modules':265,'baselineModules':264,'promotedDependencies':1,'declarations':len(seen),'theoremDeclarations':kind_counts['theorem'],'proofValuedDeclarations':proof_count,'allowedAxioms':sorted(ALLOWED),'observedAxioms':sorted(axioms),'sorryAx':False,'customAxioms':False,'nativeTrustAxioms':False,'unsafeProjectDeclarations':False,'metavariablesInTypes':False,'allSerializedModuleDeclarationsAccountedFor':True,'sourceManifestSha256':sha(HERE/'final-source-manifest.json'),'receiptSha256':receipts,'semanticMappingSha256':sha(HERE/'main-claim-mapping.json'),'nonMainReviewSha256':sha(HERE/'non-main-summary-review.json'),'ledgerSha256':sha(HERE/'formal-audit-ledger.json'),'fullDeclarationCensusSha256':sha(HERE/'declarations.jsonl'),'independentReviewSha256':{f:sha(HERE/f) for f in independent},'documentationCorrectionsSha256':sha(HERE/'source-documentation-revisions.json'),'limitations':['Fresh replay uses the Lean kernel, not an independent proof assistant.','Finite #eval output is not theorem evidence.','Two import umbrellas and statement definitions are navigation entries, not independent theorems.','The reviewed source set is 265 modules; archived/generated source-only candidates are excluded.','Unproved all-row SJS equivalence, stronger +10 diagonal slack, concrete end-to-end algorithm and unformalized analytic applications are not promoted by this gate.']}
    result['compressedFullDeclarationCensusSha256']=sha(HERE/'declarations.jsonl.gz')
    result['compactDeclarationIndexSha256']=sha(HERE/'declaration-index.jsonl')
    result['generatedPartialRuntimeHelpers']=len(partial_helpers)
    result['logicalDependenciesOnPartialRuntimeHelpers']=0
    result['generatedPartialReviewSha256']=sha(HERE/'generated-partial-helper-review.json')
    result['negativeControlsSha256']={f:sha(HERE/'negative-controls'/f) for f in ('reject-sorry.json','custom-axiom-detector.json')}
    result['toolchainBindingSha256']=sha(HERE/'toolchain-binding.json')
    result['auditToolingSha256']={str(p.relative_to(PACKAGE)).replace('\\','/'):sha(p) for p in (HERE/'run_final_audit.py',HERE/'finalize_audit.py',HERE/'build-final/FullKernelAudit.lean',HERE/'build-final/RawModuleCensus.lean',HERE/'prepare_semantic_review.py')}
    save('final-gate.json',result)
    report=['# Full Lean prepublication audit','',f"**Passed for the exact 265-module reviewed source set:** 264 baseline modules plus the separately promoted future-freeze dependency. All {len(seen):,} serialized declaration identities are covered, including {kind_counts['theorem']:,} theorem declarations and {proof_count:,} proposition-valued declarations. Generated auxiliaries are included; these counts are not numbers of independent mathematical theorems.",'','The final sources were freshly built with warnings treated as errors (only three stylistic linters disabled). An intentionally invalid sorry control was rejected. Every declaration was obtained from Lean’s elaborated environment, matched to serialized object-file identities, and recursively checked for axiom dependencies. The only observed axioms are propext, Classical.choice and Quot.sound. No sorryAx, custom/native trust axiom, unsafe project declaration, proof dependency on a generated partial runtime helper, or free/metavariable type was found. All imported proofs were replayed in a fresh Lean kernel environment. The complete census also retains 25 compiler-generated partial runtime recursion helpers; their only references in project declaration types and values are their own self-calls, never logical proof dependencies.','','The census required isolated R14/R15 imports to recover four generated equation declarations whose origin is coalesced in the combined environment. No declaration was dropped to make the completeness check pass. Full types, source modules and final SHA256 hashes are in declarations.jsonl; compact per-module types are in modules/.','','The semantic review covers all 13 principal baseline catalogue entries plus the promoted dependency and all 251 remaining inventory-only summaries. Actual-game uniqueness has an independent semantic review. Explicit hypotheses remain visible for sparse-failure, finite Fekete, lag-eight and EAA statements. EndToEndInvariantAssembly is an abstract conditional interface, with no concrete game instantiation or complexity conclusion. The SJS all-row dictionary assertion was false as documentation: its source now states the actual local lemma scope. Both documentation corrections preserve every noncomment code token, and the revised files passed the final fresh build and replay.','','This gate does not authorize publication or discharge unresolved paper claims. In particular no general SJS implementation bridge, stronger diagonal +10 bound, analytic Fekete limit, or concrete logarithmic-time algorithm is inferred from these Lean results.','','Reproduce: run run_final_audit.py in a newly named empty snapshot if rebuilding, then run finalize_audit.py. Existing evidence is intentionally not silently overwritten by a fresh snapshot launch. The final gate binds the source manifest, logs, ledger, semantic reviews and full census.','','## Reproduction and platform scope','','The saved Python audit harness currently selects the Windows Lean 4.29.1 executable under the launching user’s .elan toolchains directory. It is a Windows harness, not a claim of a platform-independent audit command. A fresh full rerun needs an empty newly named snapshot (adjust SNAP in run_final_audit.py, or preserve the old evidence elsewhere); run run_final_audit.py followed by finalize_audit.py. The initial negative controls are supplied separately by run_full_audit.py and test_custom_axiom_detector.py. The final manifest pins the exact lean-toolchain and Lake configuration hashes; toolchain-binding.json records the observed binary version and hashes.','','For a portable build/replay check, install the toolchain from lean/core/lean-toolchain, enter lean/core, then run:','','```sh','lake build ResearchCore ChompLean','lake env leanchecker --fresh --verbose ResearchCore','lake env leanchecker --fresh --verbose SJSDiagonalDictionary','lake env leanchecker --fresh --verbose ClaudeFutureFreezeDiagonal','lake env leanchecker --fresh --verbose R14FrontierLaw','lake env leanchecker --fresh --verbose R15ParkedValueSwap','```','','These portable commands rebuild and replay the proofs. They do not independently regenerate the full declaration census or semantic-review ledger. The complete census rerun is performed by the documented snapshot harness, whose generated Lean inspection files and manifests are retained. The public package itself sets warningAsError=true and disables only linter.unnecessarySimpa, linter.unusedSimpArgs and linter.unusedVariables.']
    (HERE/'REPORT.md').write_text('\n'.join(report)+'\n',encoding='utf8')
    print(f'PASSED: 265 modules; {len(seen)} declarations; {kind_counts["theorem"]} theorem declarations; {proof_count} proof-valued declarations.')
if __name__=='__main__':main()
