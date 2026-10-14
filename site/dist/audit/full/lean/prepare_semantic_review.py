"""Write reviewed English claim mappings; no inference from compilation alone."""
from pathlib import Path
import json,hashlib,re
HERE=Path(__file__).resolve().parent
PACKAGE=HERE.parents[2]
CORE=PACKAGE/'lean/core'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(n,o):(HERE/n).write_text(json.dumps(o,indent=2,ensure_ascii=False)+'\n',encoding='utf8')
def item(module,title,summary,assumptions,review,names,nonclaims,kind='theorem-family'):
    return dict(module=module,title=title,summary=summary,assumptions=assumptions,semanticReview=review,requiredDeclarations=names,notEstablished=nonclaims,claimKind=kind,verdict='accepted-exact-scope')
P='ChompLean.';O=P+'OBUQ.'
M=[
item('ChompLean.Statement','Three-row Chomp: definitions and uniqueness statement',
 'Defines sorted three-row positions, legal moves that avoid poison, recursively losing positions, and the uniqueness claim for positive rectangular boards.',
 'Rows are natural numbers p >= q >= r; a rectangle has n > 0 squares per row. Poison-taking moves are excluded because they lose immediately.',
 'Move.first cuts the top row to a positive smaller length and truncates both lower rows; second/third moves truncate the corresponding suffix. IsP requires a nonempty board and every legal move to be non-P, recursively on total squares. This is a statement/definition module, not a proof of the uniqueness claim.',
 [P+'Move',P+'IsP',P+'UniqueActualWinningTargetClaim'],['No uniqueness proof is asserted by this module alone.'],'definitions'),
item('ChompLean.Proof','Unique winning opening in positive three-row rectangles',
 'For every n > 0, the three-row n-by-3 rectangle has exactly one legal non-poison target that is a losing position for the next player.',
 'Only n > 0 remains in the final mathematical statement. All recurrence-model fields are discharged from the recursively defined actual game.',
 'gameF is built from the actual P-position encoding. game_encodes, game_complete and game_lower_blocked discharge the model rather than assume the desired uniqueness. actualWins_iff_wins connects its diagonal/second-cut opening representation to actual P-targets. uniqueActualWinningTarget_checked expands the exact quantified claim. The independent review checks the move-to-target correspondence and poison convention.',
 [P+'game_encodes',P+'game_complete',P+'game_lower_blocked',P+'actualWins_iff_wins',P+'uniqueActualWinningTarget_checked'],['No efficient algorithm or diagonal asymptotic follows from uniqueness.']),
item('XGameFOrderedBlockerUnionReconstruction','Canonical game reconstruction and blocker-count bounds',
 'Identifies the canonical blocker-union orbit with the actual game at row n+1, including normalized diagonal output and positive blocker counts; derives quadratic and square-root count certificates.',
 'The orbit starts at canonicalSeed = ([[0]],[0]), equal to canonicalQState 1. The all-row step uses forcing [0] at row 0 and [] thereafter. The square-root certificate assumes R*R <= 2*N, for natural N and R.',
 'sourceQueue and rowQueue normalize exact historical and current-row source values by the row cut. The scan proof identifies both outputs and survivors. canonical_step and canonicalOrbit_eq_state inductively bind that quotient to gameF. Output is gameF(n+1,n+1)-(n+1), with truncated natural subtraction; absolute target and hole-count bridges account for the index shift. The count A(N) satisfies 2*N <= A(N)^2+5*A(N)+2 and R-2 <= A(N) when R^2 <= 2*N.',
 [O+'canonical_step',O+'canonical_output',O+'canonicalOrbit_eq_state',O+'canonical_absoluteHoleCount_eq_gameFBlockerCountThrough',O+'gameFBlockerCountThrough_sqrt_certificate'],['No equivalence for an arbitrary initial quotient state. No SJS.dword bridge: SJS uses different state definitions.']),
item('XDeadlineCutYoungDiag','Deadline cuts with explicit low-offset thresholds',
 'Partitions a diagonal owner of q+k into disjoint old and new arms. For q >= 3 and k < 3, q+k is a blocker exactly when it has no old diagonal owner.',
 'The general blocker complement requires q+k > 0. The low-offset simplification requires q >= 3 and k < 3; finite landing-window statements retain k < H.',
 'YoungDiag means an owner a<q with d(a)=q+k; NewDiagAfterCut means an owner q+i with i<k. Injectivity and d(a)>a make this an exhaustive disjoint split. D/S partition supplies the positive blocker complement. The absence of a new owner at k<3 is a separate thresholded game theorem, not a general NoTriple assumption.',
 [P+'diagonalOwner_cut_partition',P+'youngDiag_disjoint_newDiagAfterCut',P+'blocker_iff_cut_deadline_absent',P+'blocker_iff_not_youngDiag_of_lt_three',P+'gameF_deadlineLandingOffset_cut_iff'],['No low-offset formula outside the stated q and k domain.']),
item('ClaudeCanonicalRankThreePrefix','Canonical rank-three prefix and peeled tail',
 'For q >= 10, the canonical live columns start [0,2,5], with queues [0], [0,1], [0,1,2,3]; scanning them emits [1,2,4] before the remaining tail.',
 'The canonical-game prefix requires q >= 10. The separate scan identity holds for any supplied queue tail T, with empty initial forcing and history.',
 'The actual-game source-queue theorems discharge each of the three fixed queues. liveCols_rank3_prefix and canonicalQState_rank3_prefix preserve the filtered live tail from columns 6 through q-1. scanQueues_rank3_peel is an exact equality retaining both output and survivor tails; canonical_rank3_peeled_tail bundles these identities.',
 [O+'sourceQueue_col0',O+'sourceQueue_col2',O+'sourceQueue_col5',O+'canonical_rank3_peeled_tail'],['No finite bound or independent algorithm for the moving tail.']),
item('R201DiagDoubleSlackCeilingChain','Actual-game diagonal slack and blocker-count bounds',
 'Proves d(a)+2 <= 2*a for a >= 9; 3*a+5 <= 2*d(a) for a >= 16; 2*A(a)+4 <= a+1 for a >= 16; and v <= 3*A(v-1)+2 for v >= 26.',
 'All indices are natural numbers and the displayed thresholds are required. A(n) counts positive actual-game blockers through n.',
 'gameF_diagDoubleSlack closes the actual-game supplier chain. gameF_FloorPlus uses an explicit k=d(a), not an arbitrary k. The ceiling and AFloor theorems specialize to the actual blocker count; no residual generic recurrence assumption remains.',
 [P+'gameF_diagDoubleSlack',P+'gameF_FloorPlus',P+'gameFBlockerCountThrough_ceiling',P+'gameFBlockerCountThrough_AFloor'],['The stronger d(a)+10 <= 2*a from a >= 37 is not this theorem and is not supplied by its +2 bound.']),
item('XEAARecordFreezeGap','Positive EAA freeze-seat gap',
 'For q >= 50, k=A(q), h=A(k)+2*k-q >= 1 and a freeze gameF(q,f)=q with f<q, proves q-k<f and 2*h-1 <= 5*(f-(q-k)).',
 'The positive height and actual freeze are explicit premises. Subtractions are natural-number subtractions.',
 'The theorem combines the independently proved terminal three-fifths floor with the stated positive EAA height. It bounds a supplied freeze seat and proves uniqueness separately; it does not manufacture a blocker, positive height, or a later record.',
 [P+'gameF_positiveEAA_ranked_freeze_gap',P+'gameF_positiveEAA_freeze_gap',P+'gameF_freeze_seat_unique'],['The cross-record RecordFreezeRefractory assertion remains outside this result.']),
item('SparseDualFailures','Conditional finite sparse-failure bound',
 'An abstract natural-valued sequence with at most B bad indices through N has x(r) <= 2*B+3 for all r <= N under the stated one-sided growth and good-index bounds.',
 'x(0)=0; x(j)<=x(i)+2*(j-i) for i<=j; not bad(a) implies x(a)<=3; no injection from Fin(B+1) into bad indices <=N.',
 'The budget is the finite-cardinality formulation of at most B bad indices. The growth hypothesis is one-sided, not an absolute Lipschitz assertion. sparseDualFailures_uniform packages the pointwise bracketing theorem. The module is abstract and contains no Chomp-specific instantiation or limit argument.',
 [P+'sparseDualFailures_bracket',P+'sparseDualFailures_uniform'],['No density-one statement, o(n) bound, or Chomp AA application is established here.']),
item('MinErrorFekete','Conditional finite block inequalities',
 'For natural-valued u and err satisfying the minimum-error addition hypothesis, bounds u(k*q) and u(k*q+r) by repeated q-blocks and an explicit remainder.',
 'u(m+n)<=u(m)+u(n)+err(n) whenever 0<n<=m; q,k>0; the remainder formula also assumes 0<r<q.',
 'The elaborated inequalities are u(k*q)<=k*u(q)+(k-1)*err(q) and u(k*q+r)<=k*u(q)+(k-1)*err(q)+u(r)+err(r). Induction iterates the smaller summand q, then applies the small remainder r. Natural codomain, positivity and ordering are essential to the actual statement.',
 [P+'minErrorFekete_mul',P+'minErrorFekete_mul_add'],['No analytic limit-existence theorem, real-valued generalization, or actual Chomp subadditivity supplier appears in this module.']),
item('R182ForwardFreezeCollisionExchange','Conditional forward-freeze exchange and lag-eight restriction',
 'Constructs unique exchange witnesses from an actual forward-freeze collision. In the stated lag-eight seven-host schedule and row window, a collision can only occur at row q and freeze at q+1 or q+2.',
 'The exchange retains all host/freeze equalities and strict index inequalities. The lag-eight theorem requires q>=26, Lag8TargetSevenHostSchedule q g host, q-4<=t<=q+2, c=host(t), c<k, gameF(k,c)=k and k<q+3.',
 'The companion witness lies below c, equals k in row t, and is unique by row injectivity. The full exchange additionally reconstructs v at row k left of its original victim. The specialized schedule theorem rules out all but its two dynamic rows only after the supplied schedule is unfolded.',
 [P+'gameF_forward_freeze_collision_forces_left_companion',P+'gameF_terminal_relay_forward_collision_exchange',P+'gameF_lag8_tail_forward_collision_only_dynamic_topTwo'],['No existence theorem for the seven-host schedule or a global collision bound.']),
item('EndToEndInvariantAssembly','Abstract conditional composition interface',
 'Composes supplied stage-correctness implications for arbitrary carriers and predicates. The winning-move conclusion is conditional on that interface and an exact initial state; the cost theorem projects an assumed inequality.',
 'Eight arbitrary carrier types; all functions and correctness predicates supplied in EndToEndInvariantPortfolio; an initial StateExact hypothesis. stepCostWithinLogBudget is assumed and logBudget is arbitrary.',
 'The theorem expands stage definitions and applies portfolio fields in sequence. StateExact can be identically false, so no inhabited exact state is established. WinningMove can be any predicate, so the result alone is not actual Chomp correctness. Functions may consult arbitrary data. The cost conclusion follows directly from its field and has no mathematical logarithm requirement. Documentation was corrected without changing code tokens.',
 [P+'EndToEndInvariantPortfolio',P+'endToEnd_step_exact',P+'endToEnd_emits_winning_move',P+'endToEnd_step_cost_bound'],['No concrete Chomp algorithm, oracle restriction, initialized exact state, or logarithmic complexity theorem.'],'conditional-interface'),
item('ResearchCore','Research core: nine principal import roots',
 'Imports the nine principal research modules. Each linked declaration retains its own exact assumptions and scope.',
 'This umbrella has no independent theorem statement.',
 'The source consists of imports. Its successful build and replay attest its import closure; they do not create a stronger combined theorem.',[],['No additional mathematical claim is inferred from an umbrella import.'],'import-umbrella'),
item('ChompLean','Uniqueness: statement and proof entry point',
 'Imports the actual-game uniqueness proof and statement.',
 'This umbrella has no independent theorem statement.',
 'The source is an import entry point. The mathematical claim and its semantic review belong to ChompLean.Statement and ChompLean.Proof.',[],['No separate theorem is counted for this import entry point.'],'import-umbrella'),
item('ClaudeFutureFreezeDiagonal','Actual-game future-freeze diagonal inequality',
 'For natural c<q, if gameF(q,c)=q then q<gameF(c,c). Also supplies the prehost consequence and an independent recurrence-based specialization.',
 'The actual-game theorem has only c<q and the freeze equality as premises. The abstract model theorem additionally requires a no-repeat property, discharged in the actual game.',
 'Propagation assigns every intermediate row a host left of c. No-repeat and row injectivity inject those rows into row-c values strictly between c and d(c), giving q<=d(c). D/S disjointness rules out equality. The adjacent case follows from diagonal growth and the same disjointness. The original source was omitted from the core; its exact bytes are promoted as dependency 265, preserving the baseline 264 count.',
 [P+'gameF_futureFreezeDiagonal',P+'gameF_futureFreezeDiagonal_via_recurrence',P+'gameF_freezeSeatPrehost'],['This does not supply the stronger diagonal slack +10 from row37.'])
]

if __name__=='__main__':
    catalogue=json.loads((PACKAGE/'data/formal-catalog.json').read_text(encoding='utf8'))
    manifest=json.loads((HERE/'final-source-manifest.json').read_text())
    bymod={x['module']:x for x in catalogue if x.get('attachment','').startswith('sources/lean/core/')}
    extension=next(x for x in catalogue if x['sha256']=='f92ad3a06d1adfeec5d0603bc98cb2ad8f1041eb158238e6901d15079ac9d1f8')
    bymod['ClaudeFutureFreezeDiagonal']=extension
    needed={n for m in M for n in m['requiredDeclarations']}
    declarations={}
    for filename in ('kernel-census.raw.jsonl','extension-kernel-census.raw.jsonl'):
        for line in (HERE/filename).open(encoding='utf8'):
            d=json.loads(line)
            if d['name'] in needed:
                declarations[d['name']]={k:d[k] for k in ('name','module','kind','sourceLine','typePretty','typeExpression','axioms')}
    missing=needed-declarations.keys()
    if missing:raise RuntimeError('Missing required exact theorem identifiers: '+str(sorted(missing)))
    corrections=[]
    for m in M:
        entry=bymod[m['module']]
        m['catalogueId']=entry['id'];m['sourceSha256']=manifest['sourceSha256'][m['module']]
        m['sourcePath']='lean/core/'+m['module'].replace('.','/')+'.lean'
        m['declarations']=[declarations[n] for n in m['requiredDeclarations']]
        for d in m['declarations']:d['sourceSha256']=manifest['sourceSha256'][d['module']]
        m['kernelVerdict']='pending-final-completeness-gate'
        corrections.append({'id':entry['id'],'module':m['module'],'originalSha256':entry['sha256'],'changes':{k:m[k] for k in ('title','summary','assumptions')},'sourceSha256':m['sourceSha256'],'audit':'audit/full/lean/main-claim-mapping.json','reason':'Make exact mathematical scope and premises visible.'})
    save('main-claim-mapping.json',{'scope':'13 baseline principal entries plus the separately promoted FFD dependency; exact mathematical correspondence independently of build success.','baselinePrincipalEntries':13,'extensionEntries':1,'mappings':M})
    out=['# Exact mathematical correspondence of the public Lean claims','',
      'This review separates semantic meaning from kernel acceptance. Exact elaborated types and expression trees are in the companion JSON; the final gate supplies source-bound kernel evidence. There are thirteen baseline principal entries, including two import umbrellas and the statement module, plus one promoted dependency. The ten original principal declarations are not ten independent unconditional Chomp theorems.','']
    for m in M:
        out += ['## '+m['title'],'',m['summary'],'','**Premises and domain.** '+m['assumptions'],'','**Correspondence review.** '+m['semanticReview'],'','**Not established.** '+' '.join(m['notEstablished']),'','Source: `'+m['sourcePath']+'`, SHA256 `'+m['sourceSha256']+'`.','']
        out += ['Declarations: '+', '.join('`'+n+'`' for n in m['requiredDeclarations'])+'.',''] if m['requiredDeclarations'] else []
    (HERE/'MAIN-CLAIM-MAPPING.md').write_text('\n'.join(out),encoding='utf8')
    # Generic remaining catalogue summaries assert inventory metadata, not a
    # new natural-language mathematical theorem. Validate that exact scope.
    principal={m['module'] for m in M}
    nonmain=[]
    for module in manifest['modules']:
        if module in principal:continue
        entry=bymod[module]
        prefix=entry['summary'].split('. ')[0]
        assert prefix in ('Canonical research core','Uniqueness and game foundations')
        expected=f"{prefix}. {entry['declarationCount']} lexically extracted declarations in this source version; {len(entry['sourcePaths'])} original path(s) retained."
        assert entry['summary']==expected,(module,entry['summary'])
        rec={'module':module,'catalogueId':entry['id'],'sourceSha256':manifest['sourceSha256'][module],'summaryReviewed':entry['summary'],'verdict':'accepted-inventory-only','mathematicalAssertion':'None: the summary is explicitly lexical source metadata, not a mathematical theorem or unique theorem count.'}
        if module=='SJSDiagonalDictionary':
            rec.update(verdict='corrected-overclaim',mathematicalAssertion='Only SJS implementation/local mex/initial-state lemmas are established. No all-q dword/gameF bridge is present. The original false header has been corrected, preserving code tokens.')
            corrections.append({'id':entry['id'],'module':module,'originalSha256':entry['sha256'],'sourceSha256':manifest['sourceSha256'][module],'changes':{'title':'SJS implementation and initial-state lemmas','summary':'Defines the SJS implementation and proves local mex and initial-state facts. The all-row dword/gameF diagonal bridge remains unproved in this module. The original overclaiming header was corrected.','assumptions':'Finite evaluations are computational evidence only; no general implementation-equivalence theorem is claimed.'},'reason':'False all-row dictionary claim removed from public source documentation.','audit':'audit/full/lean/source-documentation-revisions.json'})
        nonmain.append(rec)
    assert len(nonmain)==251
    save('non-main-summary-review.json',{'scope':'Every one of the 251 non-main baseline module summaries. No unreviewed mathematical extrapolation is added from module titles.','count':len(nonmain),'modules':nonmain})
    save('catalogue-corrections.json',{'instructions':'Apply these corrections to public metadata. Revised source hashes must replace old verification bindings. Preserve original provenance; do not claim original bytes equal corrected files. Final kernel status comes from final-gate.json. FFD is an existing content record promoted to core, not duplicate new content.','corrections':corrections,'extension':{'module':'ClaudeFutureFreezeDiagonal','id':extension['id'],'sha256':extension['sha256'],'attachment':'sources/lean/core/ClaudeFutureFreezeDiagonal.lean','provenance':'Exact same bytes as original supplemental record; dependency265 beyond baseline 264.','mainResult':False}})
    print('Reviewed 13 baseline main entries + FFD, and 251 inventory-only summaries.')

