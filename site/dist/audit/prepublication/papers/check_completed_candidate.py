"""Read-only candidate review. Invoke only after the root signals rendering is final."""
from pathlib import Path
import hashlib,html,json,re,sys
lane=Path(__file__).resolve().parent;audit=lane.parent
candidate=Path(sys.argv[1]).resolve()if len(sys.argv)>1 else audit.parent/'releases/three-row-chomp-2026-10-14'
site=candidate/'site/dist'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:p.read_text(encoding='utf-8-sig')
baseline=[r for r in json.loads(read(audit/'extracted/data/reviewed-catalog.json'))if r['kind']=='paper']
patch=json.loads(read(lane/'CROSS-CLOCK-CORRECTION.json'));changes={r['id']:r['fields']for r in patch['corrections']}
rows=json.loads(read(candidate/'data/reviewed-catalog.json'))
papers={r['id']:r for r in rows if r['kind']=='paper'}
assert len(papers)==59 and set(papers)=={r['id']for r in baseline}
assert sum(r['status']=='conditional'for r in papers.values())==8
integration=json.loads(read(lane/'SUPPLEMENT-INTEGRATION.json'))
mapping={r['id']:r['supplementPaths']for r in integration['perRecord']}
raw=read(site/'catalog.js');catalog=json.loads(raw[raw.index('{'):].rstrip().rstrip(';'))
ui={r['id']:r for r in catalog['results']}
assert catalog['stats']['byKind']=={'lean':265,'paper':59}
assert catalog['stats']['byStatus']=={'lean-verified':265,'paper-reviewed':51,'conditional':8}
book=read(candidate/'papers/ENGLISH-PROOFS.md')
assert set(re.findall(r'<a id="([^"]+)"',book))==set(papers)
records=[]
for original in baseline:
    expected={**original,**changes.get(original['id'],{})};r=papers[original['id']]
    if r['id']=='cross-clock-departure-injection':
        expected['summary']=expected['statement']
    for field in ['title','summary','statement','assumptions','proofText','status','formalization']:
        assert r[field]==expected[field],(r['id'],field)
    page=site/ui[r['id']]['pageHref'];plaintext=html.unescape(read(page))
    proof=candidate/r['attachment'];prooftext=read(proof)
    for field in ['title','statement','proofText']:
        assert r[field]in plaintext and r[field]in prooftext and r[field]in book,(r['id'],field,'delivery')
    for hypothesis in r['assumptions']:
        assert hypothesis in plaintext and hypothesis in prooftext
    for supplemental in mapping[r['id']]:
        # Math renderer converts Markdown supplement link targets to their HTML siblings.
        assert supplemental in json.dumps(r,ensure_ascii=False)or Path(supplemental).name in prooftext,(r['id'],supplemental,'public linkage')
        assert Path(supplemental).with_suffix('.html').name in plaintext or Path(supplemental).name in plaintext,(r['id'],supplemental,'static page')
    for attachment in r.get('additionalAttachments',[]):
        assert (candidate/attachment['path']).is_file(),(r['id'],attachment['path'],'repository attachment')
        assert (site/attachment['path']).is_file(),(r['id'],attachment['path'],'website attachment')
    assert r['audit']['originalClaimVerdict']==original['audit']['originalClaimVerdict']
    records.append({'id':r['id'],'result':'PASS','page':ui[r['id']]['pageHref'],'pageSHA256':sha(page),'proofSHA256':sha(proof),'completeSupplementLinks':mapping[r['id']],'correctedFieldScopePreserved':True})
supplement_records=[]
for f in integration['files']:
    p=candidate/f['destinationPath'];s=site/f['destinationPath']
    assert sha(p)==f['sha256']and sha(s)==f['sha256'],f['destinationPath']
    rendered=s.with_suffix('.html');assert rendered.is_file()
    text=read(rendered);assert 'katex-error'not in text
    supplement_records.append({'path':f['destinationPath'],'sha256':sha(p),'htmlPath':rendered.relative_to(site).as_posix(),'htmlSHA256':sha(rendered),'result':'PASS'})
excluded=['q-victim-gate-small-class','q-a1-open','q-sublinear-open']
for x in excluded:
    assert x not in papers and x not in ui
    assert not any(x in p.name for p in (site/'results').glob('*.html'))
    assert x not in read(site/'browse.html')
assert not (candidate/'papers/originals').exists()
replay=json.loads(read(lane/'FINITE-CERTIFICATE-REPLAY.json'));assert replay['result']=='passed'
certificate_records=[]
for p in sorted((audit/'extracted/certificates').rglob('*')):
    if not p.is_file():continue
    relative=p.relative_to(audit/'extracted/certificates')
    assert sha(p)==sha(candidate/'certificates'/relative)==sha(site/'certificates'/relative),str(relative)
    certificate_records.append({'path':'certificates/'+relative.as_posix(),'sha256':sha(p)})
strict=next(r for r in papers.values()if r['id']=='q-unconditional-liminf-gap')
links={a['path']for a in strict['additionalAttachments']}
assert {'audit/prepublication/root/strict-gap-algebra.json','audit/prepublication/root/replay_strict_gap_algebra.py','audit/full/paper-a/independent-checks.json'}<=links
for rel in ['root/strict-gap-algebra.json','root/replay_strict_gap_algebra.py']:
    target=candidate/'audit/prepublication'/rel
    assert sha(target)==sha(audit/rel)
exact=json.loads(read(candidate/'audit/prepublication/root/strict-gap-algebra.json'))
assert exact['result']=='PASS'and exact['checkerSha256']==sha(candidate/'audit/prepublication/root/replay_strict_gap_algebra.py')
result={'result':'PASS','scope':'Final exact candidate paper proof-completeness and scoped statement review after all public supplements and four corrections are integrated. Read-only; no publication performed.','candidatePath':str(candidate),
 'recordCount':59,'conditionalCount':8,'records':records,'supplements':supplement_records,'certificateFiles':certificate_records,'excludedIds':excluded,'findings':[],
 'candidateCatalogueSHA256':sha(candidate/'data/reviewed-catalog.json'),'siteCatalogueSHA256':sha(site/'catalog.js'),'englishBookSHA256':sha(candidate/'papers/ENGLISH-PROOFS.md'),'reviewInputSHA256':sha(lane/'PAPER-REVIEW.json'),
 'independentSupplementReviewSHA256':sha(audit/'root/SUPPLEMENT-SECOND-REVIEW.json'),'freshFiniteReplaySHA256':sha(lane/'FINITE-CERTIFICATE-REPLAY.json'),
 'limitations':'This establishes complete supplied written proof material for the selected exact statements. It does not establish novelty, human peer review, new Lean formalizations of derived paper claims or the open canonical suppliers.'}
(lane/'FINAL-CANDIDATE-PAPER-REVIEW.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'result':'PASS','paperRecords':59,'conditional':8,'supplements':len(supplement_records),'findings':0}))
