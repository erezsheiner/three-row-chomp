from pathlib import Path
import hashlib,json,re
lane=Path(__file__).resolve().parent;root=lane.parent;ziproot=root/'extracted'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
catalog=json.loads((ziproot/'data/reviewed-catalog.json').read_text(encoding='utf-8-sig'))
papers=[r for r in catalog if r['kind']=='paper']
notes=json.loads((lane/'renewed-proof-notes.json').read_text(encoding='utf-8'))
assert len(papers)==len(notes)==59 and [r['id']for r in papers]==[n['id']for n in notes]
patch=json.loads((lane/'CROSS-CLOCK-CORRECTION.json').read_text(encoding='utf-8'))
patch_by={p['id']:p for p in patch['corrections']}
conditional=sorted(r['id']for r in papers if r['status']=='conditional');assert len(conditional)==8
excluded=['q-victim-gate-small-class','q-a1-open','q-sublinear-open']
assert not(set(excluded)&{r['id']for r in papers})
assert not any(any(x in p.name for x in excluded)for p in (ziproot/'site/dist/results').glob('*.html'))
book=(ziproot/'papers/ENGLISH-PROOFS.md').read_text(encoding='utf-8')
assert set(re.findall(r'<a id="([^"]+)"',book))=={r['id']for r in papers}

own={p.name:p for p in sorted((lane/'supplements').glob('*.md'))if p.name!='INDEX.md'}
external={
 'PELL-RECURRENCES.md':root/'lean-semantics/supplements/PELL-RECURRENCES.md',
 'lag124-proof.md':root/'lean-semantics/supplements/lag124-proof.md',
 'counting-service-budget.md':root/'root/supplements/counting-service-budget.md',
 'counting-extremizer-proof.md':root/'root/supplements/counting-extremizer-proof.md'
}
paths={**own,**external}
for name,p in paths.items():assert p.is_file(),name
for p in own.values():
    t=p.read_text(encoding='utf-8')
    assert not re.search('[\u0590-\u05ff]',t)
    assert t.count('\\(')==t.count('\\)'),(p.name,'inline delimiter count')
    assert t.count('\\[')==t.count('\\]'),(p.name,'display delimiter count')
suppmap={}
for n in notes:
    identifier=n['id'];links=['CANONICAL-DEFINITIONS.md']
    i=next(i for i,r in enumerate(papers)if r['id']==identifier)
    if i in list(range(0,11))+[14,15,16,24,25,26,27,28]:links+=['GHOST-TOKENS-AND-OWNER-TRANSPORT.md']
    if i in [6,11,12,13,39,40,41,42]:links+=['FINITE-MEX-AND-WINDOW-MODELS.md']
    if 17<=i<=23:links+=['SOURCE-TIME-AND-TIGHTNESS.md']
    if i in [29,32,33]:links+=['COUNT-CLOCK-AND-ABSTRACT-BOUNDARY.md']
    if 43<=i<=50:links+=['PRIVATE-HISTORY-AND-RELAY.md']
    if 33<=i<=38:links+=['PELL-RECURRENCES.md']
    if i==51:links+=['lag124-proof.md','FINITE-CERTIFICATE-INDUCTION.md']
    if i in [52,53]:links+=['FINITE-CERTIFICATE-INDUCTION.md']
    if i==54:links+=['counting-service-budget.md','counting-extremizer-proof.md']
    if 55<=i<=58:links+=['BLOCK-GHOSTS-AND-C50.md']
    suppmap[identifier]=list(dict.fromkeys(links))
records=[]
for i,(r,n) in enumerate(zip(papers,notes)):
    public=ziproot/r['attachment']
    assert public.is_file() and r['statement']in public.read_text(encoding='utf-8')
    linked=[{'path':'papers/supplements/'+name,'sha256':sha(paths[name]),'sourceAuditPath':paths[name].relative_to(root).as_posix()}for name in suppmap[r['id']]]
    extra=[]
    if r['id']=='q-existing-slope-upper-bound':
        extra=['audit/full/paper-b/SLOPE-REPAIR.md','audit/full/paper-b/exact-algebra-checks.json']
    if r['id']=='q-unconditional-liminf-gap':
        extra=['audit/full/paper-a/STRICT-LIMINF-DERIVATION.md','audit/full/INDEPENDENT-ASYMPTOTIC-CROSSCHECK.md']
    supplementpaths=[v['path']for v in linked]+extra
    evidence=[{'path':r['attachment'],'sha256':sha(public)},{'path':r['audit']['review'],'sha256':sha(ziproot/r['audit']['review'])},
              {'path':'audit/full/CANONICAL-FOUNDATIONS.md','sha256':sha(ziproot/'audit/full/CANONICAL-FOUNDATIONS.md')}]
    for rel in extra:
        if (ziproot/rel).exists():evidence.append({'path':rel,'sha256':sha(ziproot/rel)})
    scoped=dict(patch_by.get(r['id'],{}).get('fields',{}))
    records.append({'id':r['id'],'index':i,'title':r['title'],'originalRecordedVerdict':r['audit']['originalClaimVerdict'],'exactDeliveredStatement':r['statement'],'explicitHypotheses':r['assumptions'],
        'truthReview':{'result':'PASS_WITH_SCOPE_CLARIFICATION'if r['id']=='cross-clock-departure-injection'else'PASS','basis':'Renewed inference-by-inference mathematical reading of corrected delivered argument and its explicit dependencies; former accepted/PASS labels were not proof premises. Existing formalized foundation facts used only with their exact game definitions.','inferenceChecks':n['checks'],'conditional':r['status']=='conditional','supplierStatus':'Named quantitative/application suppliers remain unproved; only the implication is accepted.'if r['status']=='conditional'else'No excluded m<=5, direct-Q A1 or Q=o(n) supplier is used unconditionally.','formalizationScope':'Paper conclusion is not newly Lean formalized by this review; exact named formal dependencies have their separate source-bound gate.','circularityCheck':'No desired asymptotic/gate conclusion is inserted as a proof premise; original excluded statements remain excluded.','correctionRequired':scoped},
        'completeness':{'deliveredArchive':'NEEDS_PUBLIC_SUPPLEMENT'if n['missing']else'COMPLETE_FOR_STATED_CLAIM','deliveredIssue':n['missing'],'renewedCandidate':'COMPLETE_WITH_LISTED_SUPPLEMENTS_AND_EXACT_PATCHES','condition':'Copy and link the current listed definitions/full derivations, retain exact hypotheses, apply listed textual corrections, bind fresh exact algebra/finite replay receipts, and perform final candidate link/statement/hash review. The old ZIP is not retroactively proof-complete.'},
        'supplementPaths':supplementpaths,'supplements':linked,'deliveredEvidence':evidence,'suggestedExactFix':patch_by.get(r['id'],{}),
        'finiteSupport':'Fresh fixed proof-base replay, with the complete written induction supplied separately; not finite-to-universal extrapolation.'if r['id']in['legacy-bottom-two-cut-124','legacy-multiple-bottom-cuts','q-tight-width-eighteen']else'No finite computation is substituted for an analytic/universal premise.'})

integration={'result':'PASS','scope':'Explicit integration instructions for a new corrected candidate; extracted original archive and sealed donor are untouched.',
 'files':[{'sourceAuditPath':p.relative_to(root).as_posix(),'destinationPath':'papers/supplements/'+name,'sha256':sha(p),'bytes':p.stat().st_size,'scope':'Full corrected public mathematical definitions/derivation, not an original historical draft'}for name,p in paths.items()],
 'perRecord':[{'id':r['id'],'supplementPaths':r['supplementPaths']}for r in records],
 'exactCorrectionFile':'papers/CROSS-CLOCK-CORRECTION.json','correctionSHA256':sha(lane/'CROSS-CLOCK-CORRECTION.json'),
 'requiredFreshSupport':[{'sourceAuditPath':'papers/FINITE-CERTIFICATE-REPLAY.json','destinationPath':'audit/prepublication/papers/FINITE-CERTIFICATE-REPLAY.json','sha256':sha(lane/'FINITE-CERTIFICATE-REPLAY.json')},
    {'sourceAuditPath':'root/strict-gap-algebra.json','destinationPath':'audit/prepublication/root/strict-gap-algebra.json','sha256':sha(root/'root/strict-gap-algebra.json')},
    {'sourceAuditPath':'root/replay_strict_gap_algebra.py','destinationPath':'audit/prepublication/root/replay_strict_gap_algebra.py','sha256':sha(root/'root/replay_strict_gap_algebra.py')}],
 'additionalIntegrationNotes':['Include the INDEX navigation sheet and render every new supplement with offline math assets.','Strict derivation references historical independent-checks.json absent from delivered ZIP: make its algebra citation point to the included newly rerun strict-gap algebra/checker, and explicitly include any scripts/inputs needed to replay it.','Link counting full derivations and their fresh exact checker/independent review; a generic old proof verdict is not a supplier.','All paper result pages and compendium must have clickable supplement links, not only an audit record filename.','Keep original revised statement/assumption/proof text provenance in the correction ledger; do not overwrite prior audit verdicts to hide new clarification.']}

readme=['# Public proof supplements','','These supplements complete the notation and written derivations missing from the earlier selected-result delivery. They state ordinary mathematical proofs and preserve every conditional supplier. The paper arguments are not thereby new Lean formalizations. Use each result page together with its linked supplements.','','## Foundation and residual services','','- [Canonical definitions](CANONICAL-DEFINITIONS.md): recurrence, time boundaries, labels, ghosts, tokens and owner inventories.','- [Ghost tokens and owner transport](GHOST-TOKENS-AND-OWNER-TRANSPORT.md): complete ledgers, incidence matching, dated stock, source graph/forest and immortal limitations.','- [Source time and tightness](SOURCE-TIME-AND-TIGHTNESS.md): E/F context, penultimate capacity, actual death injection, predecessor and fresh-permutation scopes.','','## Abstract models and full private history','','- [Count-clock implication and abstract boundary](COUNT-CLOCK-AND-ABSTRACT-BOUNDARY.md): scaling-limit proof and explicit 170-residue counterexample.','- [Finite MEX and window models](FINITE-MEX-AND-WINDOW-MODELS.md): zero-MEX owners, periodic rescued queues, graph/window conventions and conditional consumers.','- [Private history and relay resources](PRIVATE-HISTORY-AND-RELAY.md): source packing, corrected exit map, four sources and exact conditional relay/domain accounting.','','## Counting and finite certificates','','- [Counting service budget](counting-service-budget.md): complete baseline physical-service budget and optimizer.','- [Counting extremizer theorem](counting-extremizer-proof.md): defined deficits, disjoint source-target gain and exact liminf degree-eight result.','- [Finite certificate induction](FINITE-CERTIFICATE-INDUCTION.md): actual legal reply families, periodic proof, lag211 induction and scoped shell criterion.','- [Lag124 proof](lag124-proof.md): complete finite-reduction, context traces and forced-Q argument.','- [Portable finite certificate data](../../certificates/README.md): exact inputs and separate replay scope.','','## Pell and block/count coordinates','','- [Pell recurrences](PELL-RECURRENCES.md): exact windows, capped contraction, finite rigidity and positive masked response hypotheses.','- [Block ghosts and C50](BLOCK-GHOSTS-AND-C50.md): all block/young/pool definitions and the exact orbit/lineage/absence flux identities.','','The [canonical foundation](../../audit/full/CANONICAL-FOUNDATIONS.md), [existing-slope derivation](../../audit/full/paper-b/SLOPE-REPAIR.md), and [strict-liminf derivation](../../audit/full/paper-a/STRICT-LIMINF-DERIVATION.md) retain their own mathematical scopes. An accepted conditional implication does not supply its canonical hypotheses. Open Q=o(n), direct-Q A1 and the original m<=5 assertion remain outside the selected theorem set.']
(lane/'supplements/INDEX.md').write_text('\n'.join(readme)+'\n',encoding='utf-8')
index={'sourceAuditPath':'papers/supplements/INDEX.md','destinationPath':'papers/supplements/INDEX.md','sha256':sha(lane/'supplements/INDEX.md'),'bytes':(lane/'supplements/INDEX.md').stat().st_size,'scope':'Public proof-navigation index'}
integration['files'].append(index)
(lane/'SUPPLEMENT-INTEGRATION.json').write_text(json.dumps(integration,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
archive=json.loads((root/'AUDIT-INPUT.json').read_text())
report={'result':'PASS','scope':'Renewed paper-truth review plus concretely supplied complete public proof supplements for a new candidate. PASS is not an assertion that the previously delivered ZIP was complete, a human peer review, a new formalization, or permission to publish remotely.',
 'originalDeliveredArchiveSHA256':archive['sourceArchiveSha256'],'originalDeliveryCompleteness':'NEEDS_CORRECTION: omitted definitions/full derivations and one literal relay domain boundary; see every per-result completeness field.',
 'recordCount':59,'records':records,'conditionalIds':conditional,'excludedIds':excluded,'all59Reread':True,'noNewResearchMining':True,
 'renewedFiniteReplay':{'path':'papers/FINITE-CERTIFICATE-REPLAY.json','sha256':sha(lane/'FINITE-CERTIFICATE-REPLAY.json'),'result':'passed'},
 'exactTextCorrections':{'path':'papers/CROSS-CLOCK-CORRECTION.json','sha256':sha(lane/'CROSS-CLOCK-CORRECTION.json'),'ids':list(patch_by)},
 'integration':{'path':'papers/SUPPLEMENT-INTEGRATION.json','sha256':sha(lane/'SUPPLEMENT-INTEGRATION.json')},
 'mathematicalFindings':[{'id':'cross-clock-departure-injection','type':'domain-clarification','resolvedBy':'Explicit arising y>=3; arbitrary-y max(0,y-2) patch. Earlier original-claim verdict retained.'},{'id':'pell-positive-response','type':'auxiliary-sharpness-scope-clarification','resolvedBy':'Exact sharp equality restricted to compatible integer C/rational omega with scaled integer inventories; no canonical realization or equality for every real parameter claimed. Main conditional inequality is unchanged.'}],
 'publicationCompletenessFindings':[{'issue':'Many delivered proof summaries reference only named notation or missing earlier supplier documents.','resolvedForCandidateBy':'Twelve complete public mathematical supplements plus INDEX, exact per-ID links and separately fresh finite/algebra receipts.','requiresIntegration':True},
    {'id':'legacy-charged-shell-criterion','issue':'Supporting pruning prose names undefined T(A), unnecessary to the headline local criterion.','resolvedBy':'Remove that auxiliary complete-search implication and state only the proved local monotonicity; finite lag box and paid boundary made explicit.'},
    {'id':'q-tight-fresh-permutations','issue':'Garbled English small-index sentence.','resolvedBy':'Editorial patch, with complete separate small-index derivation in source-time supplement.'}],
 'unresolvedTruthGapsAfterListedCorrections':[],'candidateFinalByteReviewRequired':True,'extractedArchiveAndSealedDonorModified':False}
(lane/'PAPER-REVIEW.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
lines=['# Renewed review of all 59 delivered paper records','','The mathematical review passes for the exact scoped statements, with the explicit relay-domain clarification recorded below. The original delivered ZIP was **not proof-complete**: it removed historical drafts without replacing all their definitions and full arguments. This audit supplies complete replacement public supplements and a per-result integration map. The new candidate still requires their inclusion, rendering, links and exact final-byte review.','','## Scope and evidence','','All 59 corrected proof texts, displayed hypotheses and supporting delivered mathematical arguments were reread. Every inferential step was assessed for domain boundaries, actual versus abstract objects, source capacities, ordering assumptions, finite-to-universal induction and use of unproved suppliers. Earlier PASS/accepted labels were not used as mathematical premises. The new supplements are full derivations, not another list of verdicts.','','The 8 conditional statements retain their open quantitative/application suppliers. The 3 repaired earlier statements retain their corrections. The 3 excluded result IDs are absent from result records/pages/book sections and are not unconditionally imported into a retained proof. The source archive and donor remain untouched.','','## Fresh finite replay','','A copied portable checker rebuilt literal rows0..810 from positive MEX/COPY. It verified C300 bases/normalized identities, lag120 closure, lag124 context/terminal replies, C360 bases and lag2111355278 support calls/505860 bases, and tight-width7..43 values. The checker branch paying the lag124 forced-Q reply is a separate written proof step; its complete new supplement is linked. Universal conclusions use the written periodic and well-founded inductions, not the finite receipt alone.','','## New corrections','','1. Cross-clock payload bound: an arising endpoint satisfies y>=q>=3, so y-2 is valid. For arbitrary y>=0 use max(0,y-2); no endpoint occurs for y<3. This clarifies a literal negative-bound corner rather than disproving the source injection.','2. Charged-shell compact proof: remove the extraneous undefined T(A) pruning claim; the local Hall criterion and its precisely finite admissible class are unchanged.','3. Fresh-permutation small-index sentence: replace garbled text; the terminal lemma guard and explicit small cases remain unchanged.','','## Delivery completeness','','SUPPLEMENT-INTEGRATION.json binds every new supplement and its per-result links. INDEX.md is public navigation. The full counting service/extremizer derivations, root/A Pell and lag124 proofs, and eight own definition/model/transport supplements replace missing source material. Existing full slope and strict-liminf proofs remain linked, and the strict algebra citation must use an actually included fresh checker/receipt. No unreviewed original draft is reinstated as a proof source.','','## Per-result renewed inference review','']
for record in records:
    lines+=['### '+record['id'],'','Truth: '+record['truthReview']['result']+'. Delivered completeness: '+record['completeness']['deliveredArchive']+'.','']
    lines+=['- '+c for c in record['truthReview']['inferenceChecks']]
    if record['completeness']['deliveredIssue']:lines+=['','Missing in original delivery: '+record['completeness']['deliveredIssue']]
    lines+=['','Required public supplement links: '+', '.join(record['supplementPaths'])+'.','']
(lane/'PAPER-REPORT.md').write_text('\n'.join(lines)+'\n',encoding='utf-8')
report_path=lane/'PAPER-REPORT.md';report_text=report_path.read_text(encoding='utf-8')
needle='3. Fresh-permutation small-index sentence: replace garbled text; the terminal lemma guard and explicit small cases remain unchanged.'
assert needle in report_text
report_text=report_text.replace(needle,needle+'\n4. Positive-response inventory sharpness: exact saturation is stated only for integer C and rational omega scaled to integer inventories. The conditional inequality for real C remains valid, with fibre cardinalities effectively bounded by floor(C); no canonical realization or exact equality for every real/irrational choice is claimed.')
report_path.write_text(report_text,encoding='utf-8')
manifest=[{'path':p.relative_to(lane).as_posix(),'sha256':sha(p),'bytes':p.stat().st_size}for p in sorted(lane.rglob('*'))if p.is_file()and 'certificate-replay'not in p.parts and p.name!='MANIFEST.json']
(lane/'MANIFEST.json').write_text(json.dumps({'scope':'Renewed59 paper review and concrete corrected public supplements; original delivered ZIP is untouched.','files':manifest},indent=2)+'\n',encoding='utf-8')
print(json.dumps({'result':'PASS','records':59,'conditional':8,'supplementFiles':len(integration['files']),'exactPatches':len(patch_by),'originalDeliveryComplete':False,'newCandidateRequiresFinalIntegrationQA':True}))
