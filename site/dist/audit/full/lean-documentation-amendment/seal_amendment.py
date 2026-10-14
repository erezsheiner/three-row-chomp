"""Seal current source bindings after the rigorous documentation amendment.

The immutable base retains all original evidence. No inherited receipt is
rewritten to claim a fresh audit of revised bytes. Current AST/axiom evidence is
transferred only for strictly compiled, structurally identical declarations.
"""
from pathlib import Path
import collections,datetime as dt,gzip,hashlib,importlib.util,json,re,shutil

HERE=Path(__file__).resolve().parent
FULL=HERE.parent;AUDIT=FULL/'lean';BASE=HERE/'immutable-base/lean'
PACKAGE=FULL.parents[1];CORE=PACKAGE/'lean/core'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text(encoding='utf8'))
def save(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n',encoding='utf8')

def main():
    plan=read(HERE/'amendment-plan.json');receipt=read(HERE/'receipt.json')
    assert receipt['result']=='passed' and receipt['changedModules']==45 and receipt['comparedDeclarationCount']==2109
    for rel,digest in read(HERE/'immutable-base/BINDINGS.json')['files'].items():
        assert sha(HERE/'immutable-base'/rel)==digest,'Immutable base changed: '+rel
    for f,digest in receipt['artifactSha256'].items():assert sha(HERE/f)==digest
    for f,digest in receipt['receiptSha256'].items():assert sha(HERE/'receipts'/f)==digest
    revisions={r['module']:r for r in receipt['revisions']}
    modules=read(BASE/'final-source-manifest.json')['modules']
    assert len(modules)==265 and len(revisions)==45
    review_hashes={};reviewed=set()
    for lane,expected in [('paper-a',37),('paper-b',17)]:
        p=FULL/lane/'FINAL-AMENDMENT-REVIEW.json';r=read(p)
        assert r['result']=='passed' and r['correctionsVerified']==expected and not r['unresolvedFindings']
        review_hashes[p.relative_to(PACKAGE).as_posix()]=sha(p)
        for row in r['records']:
            assert row['verdict']=='passed'
            assert row['sourceSha256']==revisions[row['module']]['revisedSha256']
            reviewed.add(row['module'])
    assert reviewed==set(revisions)
    spec=importlib.util.spec_from_file_location('amend',HERE/'amend_sources.py');amend=importlib.util.module_from_spec(spec);spec.loader.exec_module(amend)
    for m in modules:
        rel=Path(m.replace('.','/')+'.lean')
        expected=revisions[m]['revisedSha256'] if m in revisions else read(BASE/'final-source-manifest.json')['sourceSha256'][m]
        assert sha(CORE/rel)==expected,m
        if m in revisions:
            assert amend.mask_comments((CORE/rel).read_text(encoding='utf8')).split()==amend.mask_comments((HERE/'immutable-base/sources'/rel).read_text(encoding='utf8')).split()
    receipt['independentAmendmentReviews']=review_hashes
    receipt['sealingToolSha256']=sha(Path(__file__))
    receipt['sealedAt']=dt.datetime.now(dt.timezone.utc).isoformat()
    save(HERE/'receipt.json',receipt)
    manifest=read(BASE/'final-source-manifest.json')
    manifest['createdAt']=receipt['sealedAt']
    manifest['inheritedBaseSourceManifestSha256']=sha(BASE/'final-source-manifest.json')
    manifest['baseFreshBuildDirectory']=True
    manifest['freshBuildDirectory']=False
    manifest['baseDocumentationRevisionReceiptSha256']=manifest.pop('documentationRevisionReceiptSha256')
    manifest['validationMethod']='Full base fresh build/census/axiom audit/replay plus strict compilation and exact serialized declaration identity for 45 documentation-only revisions. No second full replay claimed.'
    manifest['documentationAmendmentReceiptSha256']=sha(HERE/'receipt.json')
    for m,r in revisions.items():manifest['sourceSha256'][m]=r['revisedSha256']
    for name,key in [('lakefile.lean','configurationSha256'),('lean-toolchain','toolchainSha256')]:assert sha(CORE/name)==manifest[key]
    save(AUDIT/'final-source-manifest.json',manifest)
    ranges={(d['module'],d['name']):d['sourceLine'] for d in map(json.loads,(HERE/'source-ranges.jsonl').read_text(encoding='utf8').splitlines())}
    identical={(d['module'],d['name']) for d in map(json.loads,(HERE/'declaration-identity.jsonl').read_text(encoding='utf8').splitlines())}
    assert len(ranges)==len(identical)==2109 and set(ranges)==identical
    def refresh(d):
        m=d['module']
        if m in revisions:
            d['sourceSha256']=revisions[m]['revisedSha256']
            if 'name' in d:d['sourceLine']=ranges[(m,d['name'])]
        return d
    counts=collections.Counter();seen=set()
    with (BASE/'declarations.jsonl').open(encoding='utf8') as inp,(AUDIT/'declarations.jsonl').open('w',encoding='utf8') as out:
        for line in inp:
            d=refresh(json.loads(line));key=(d['module'],d['name']);assert key not in seen;seen.add(key)
            if d['module'] in revisions:
                d['documentationAmendment']='audit/full/lean-documentation-amendment/receipt.json'
                d['sourceLineOrigin']='Revised compiled declaration-range extension; original type/axiom evidence transferred by exact serialized declaration identity.'
            counts[d['kind']]+=1;out.write(json.dumps(d,ensure_ascii=False,separators=(',',':'))+'\n')
    assert len(seen)==21064 and counts['theorem']==19991
    with (BASE/'declaration-index.jsonl').open(encoding='utf8') as inp,(AUDIT/'declaration-index.jsonl').open('w',encoding='utf8') as out:
        for line in inp:out.write(json.dumps(refresh(json.loads(line)),ensure_ascii=False,separators=(',',':'))+'\n')
    for m in modules:
        data=read(BASE/'modules'/(m+'.json'))
        if m in revisions:
            data['sourceSha256']=revisions[m]['revisedSha256'];data['documentationAmendment']='audit/full/lean-documentation-amendment/receipt.json'
            data['declarations']=[refresh(d) for d in data['declarations']]
            assert len(data['declarations'])==sum(1 for k in identical if k[0]==m)
        save(AUDIT/'modules'/(m+'.json'),data)
    with (AUDIT/'declarations.jsonl').open('rb') as inp,(AUDIT/'declarations.jsonl.gz').open('wb') as raw:
        with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0,compresslevel=9) as out:shutil.copyfileobj(inp,out)
    digest=hashlib.sha256()
    with gzip.open(AUDIT/'declarations.jsonl.gz','rb') as f:
        for chunk in iter(lambda:f.read(1024*1024),b''):digest.update(chunk)
    assert digest.hexdigest()==sha(AUDIT/'declarations.jsonl')
    mappings=read(BASE/'main-claim-mapping.json')
    for m in mappings['mappings']:
        if m['module'] in revisions:
            m['sourceSha256']=revisions[m['module']]['revisedSha256']
            m['declarations']=[refresh(d) for d in m['declarations']]
            m['kernelVerdict']='passed-base-full-audit-plus-exact-declaration-identity-amendment'
    save(AUDIT/'main-claim-mapping.json',mappings)
    md=(BASE/'MAIN-CLAIM-MAPPING.md').read_text(encoding='utf8')
    for r in revisions.values():md=md.replace(r['originalSha256'],r['revisedSha256'])
    (AUDIT/'MAIN-CLAIM-MAPPING.md').write_text(md,encoding='utf8')
    for filename,arraykey in [('non-main-summary-review.json','modules'),('catalogue-corrections.json','corrections')]:
        obj=read(BASE/filename)
        for r in obj[arraykey]:
            if r['module'] in revisions:r['sourceSha256']=revisions[r['module']]['revisedSha256']
        save(AUDIT/filename,obj)
    partial=read(BASE/'generated-partial-helper-review.json')
    for r in partial['helpers']:
        if r['module'] in revisions:r['sourceSha256']=revisions[r['module']]['revisedSha256']
    partial['documentationAmendment']='audit/full/lean-documentation-amendment/receipt.json'
    save(AUDIT/'generated-partial-helper-review.json',partial)
    ledger=read(BASE/'formal-audit-ledger.json')
    for row in ledger['records']:
        if row['module'] in revisions:
            row['sha256']=revisions[row['module']]['revisedSha256']
            row['documentationAmendment']={'receipt':'audit/full/lean-documentation-amendment/receipt.json','exactDeclarationIdentity':True,'strictRecompilation':'passed'}
        row['sourceProseReview']='All source comments and corresponding types reviewed; historical observations and conditional suppliers remain explicitly scoped.'
    save(AUDIT/'formal-audit-ledger.json',ledger)
    oldrevs=read(BASE/'source-documentation-revisions.json')
    oldrevs.extend({'module':r['module'],'originalSha256':r['originalSha256'],'revisedSha256':r['revisedSha256'],
      'proofTokensIdenticalAfterCommentRemoval':True,'originalSource':r['originalSource'],'revisedSource':r['sourcePath'],
      'reason':'Independent full-source prose audit correction; no noncomment token, declaration type or value changed.',
      'amendmentReceipt':'audit/full/lean-documentation-amendment/receipt.json'} for r in revisions.values())
    save(AUDIT/'source-documentation-revisions.json',oldrevs)
    # Repeat the supplementary source trust scan on current bytes. Proof axiom
    # checks are inherited through exact term equality, not replaced by this.
    spec=importlib.util.spec_from_file_location('prep',PACKAGE/'scripts/prepare_lean.py');prep=importlib.util.module_from_spec(spec);spec.loader.exec_module(prep)
    scan=read(BASE/'final-source-trust-scan.json');newflags=[]
    for m in modules:
        masked=prep.mask_noncode((CORE/(m.replace('.','/')+'.lean')).read_text(encoding='utf8'))
        for category,pattern in scan['patterns'].items():
            for match in re.finditer(pattern,masked):
                old=next((f for f in scan['reviewedFlags'] if f['module']==m and f['category']==category and f['token']==match.group()),None)
                assert old,'Unreviewed trust token '+m+'/'+match.group()
                f=dict(old,sourceSha256=manifest['sourceSha256'][m],line=masked[:match.start()].count('\n')+1);newflags.append(f)
    assert collections.Counter((f['module'],f['category'],f['token']) for f in newflags)==collections.Counter((f['module'],f['category'],f['token']) for f in scan['reviewedFlags'])
    scan.update(sourceManifestSha256=sha(AUDIT/'final-source-manifest.json'),reviewedFlags=newflags,
      documentationAmendment='audit/full/lean-documentation-amendment/receipt.json')
    save(AUDIT/'final-source-trust-scan.json',scan)
    completeness=read(BASE/'declaration-completeness.json')
    completeness.update(fullCensusSha256=sha(AUDIT/'declarations.jsonl'),compressedFullCensusSha256=sha(AUDIT/'declarations.jsonl.gz'),
      compactIndexSha256=sha(AUDIT/'declaration-index.jsonl'),sourceManifestSha256=sha(AUDIT/'final-source-manifest.json'),
      documentationAmendment='audit/full/lean-documentation-amendment/receipt.json')
    save(AUDIT/'declaration-completeness.json',completeness)
    gate=read(BASE/'final-gate.json')
    gate.update(finishedAt=receipt['sealedAt'],sourceManifestSha256=sha(AUDIT/'final-source-manifest.json'),
      semanticMappingSha256=sha(AUDIT/'main-claim-mapping.json'),nonMainReviewSha256=sha(AUDIT/'non-main-summary-review.json'),
      ledgerSha256=sha(AUDIT/'formal-audit-ledger.json'),fullDeclarationCensusSha256=sha(AUDIT/'declarations.jsonl'),
      compressedFullDeclarationCensusSha256=sha(AUDIT/'declarations.jsonl.gz'),compactDeclarationIndexSha256=sha(AUDIT/'declaration-index.jsonl'),
      documentationCorrectionsSha256=sha(AUDIT/'source-documentation-revisions.json'),generatedPartialReviewSha256=sha(AUDIT/'generated-partial-helper-review.json'))
    gate['independentReviewSha256']['../CANONICAL-FOUNDATIONS.md']=sha(FULL/'CANONICAL-FOUNDATIONS.md')
    gate['receiptScope']='receiptSha256 entries are immutable base full-audit receipts, bound to the base manifest; current bytes are bound by documentationAmendment. The unchanged base copies are retained under immutable-base/lean.'
    gate['documentationAmendment']={'result':'passed','changedModules':45,'reviewedFindings':54,'followUpClarifications':1,
      'comparedDeclarationCount':2109,'receipt':'audit/full/lean-documentation-amendment/receipt.json','receiptSha256':sha(HERE/'receipt.json'),
      'inheritedBaseGate':receipt['inheritedBaseGate'],'independentReviews':review_hashes,
      'method':'Strict compilation of every changed module plus exact serialized type/value/field identity; inherited full census, axiom and fresh-kernel-replay certificate. No second 265-module replay.'}
    gate['currentSourceTrustScanSha256']=sha(AUDIT/'final-source-trust-scan.json')
    gate['auditToolingSha256'][Path(__file__).relative_to(PACKAGE).as_posix()]=sha(Path(__file__))
    report=(BASE/'REPORT.md').read_text(encoding='utf8')
    report=report.replace('The final sources were freshly built','The immutable base sources were freshly built')
    report=report.replace('Both documentation corrections preserve every noncomment code token, and the revised files passed the final fresh build and replay.',
      'Those first two documentation corrections preserved every noncomment code token and were included in the full base fresh build and replay.')
    intro='''
## Final documentation amendment

Independent source-prose reviews cover all 265 modules. They requested 54 corrections across 45 modules, plus one adjacent clarification that a reported R177 replay is finite. All corrections are present in the final source bytes and independently accepted by both reviewers. The original review ledgers and full passing audit remain immutable under `audit/full/lean-documentation-amendment/immutable-base/`.

Every changed module was strictly recompiled. All 2,109 serialized declarations in these 45 modules have exactly identical names, universe parameters, types, proof/definition values, safety and declaration-specific fields compared with the full-pass objects. The comparator uses structural `Expr.equal`, including binder names and annotations, and its negative controls reject altered binders and values. All noncomment tokens, including strings, are unchanged. The remaining 220 sources are byte-identical to the base.

Consequently the original exhaustive axiom inspection and fresh kernel replays apply to identical logical declarations. This is a targeted documentation amendment, not a second fresh 265-module replay. Revised line anchors come from Lean's newly compiled declaration-range metadata. The first range-export attempt failed because a partial search root shadowed the ChompLean dependency directory; completing that root with hash-identical unchanged objects fixed the presentation export. Both receipts are retained; the failed metadata attempt is not a failed proof check.

The current manifest, catalogue ledger, complete census, compact index and main-claim mapping bind the final sources. `final-gate.json.documentationAmendment` points to the targeted receipts and immutable base gate. The full initial run and targeted amendment are deliberately distinguished.

To repeat the targeted checks on this Windows host, use `run_revalidation.py` in the amendment directory (omit `--resume` to actually recompile). The compiled base snapshot is required. `seal_amendment.py` refreshes presentation metadata only after strict checks and independent amendment reviews pass. For an independent new full audit of the final sources, use the full snapshot harness in a separate output tree; do not overwrite the preserved base or relabel its receipts.
'''
    report=report.replace('\n## Reproduction and platform scope\n',intro+'\n## Reproduction and platform scope\n')
    (AUDIT/'REPORT.md').write_text(report,encoding='utf8')
    gate['currentReportSha256']=sha(AUDIT/'REPORT.md')
    save(AUDIT/'final-gate.json',gate)
    # Final executable consistency gate across every current output.
    assert len(ledger['records'])==265 and all(sha(PACKAGE/r['sourcePath'])==r['sha256'] for r in ledger['records'])
    assert all(read(AUDIT/'modules'/(r['module']+'.json'))['sourceSha256']==r['sha256'] for r in ledger['records'])
    print(json.dumps({'result':'passed','modules':265,'changedModules':45,'identicalDeclarations':2109,
      'allDeclarations':21064,'gateSha256':sha(AUDIT/'final-gate.json'),'manifestSha256':sha(AUDIT/'final-source-manifest.json')}))

if __name__=='__main__':main()
