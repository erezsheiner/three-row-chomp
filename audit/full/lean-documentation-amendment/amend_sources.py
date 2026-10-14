"""Preserve the passing audit and apply the independently reviewed prose fixes.

Only publication copies are changed. Run once; it refuses to overwrite its base.
"""
from pathlib import Path
import collections, datetime as dt, difflib, hashlib, json, re, shutil, textwrap

HERE=Path(__file__).resolve().parent
FULL=HERE.parent
AUDIT=FULL/'lean'
PACKAGE=FULL.parents[1]
CORE=PACKAGE/'lean/core'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_text(encoding='utf8'))
def save(p,x): p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
def mask_comments(s):
    out=list(s);i=0;depth=0;string=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i): out[i:i+2]='  ';depth+=1;i+=2
            elif s.startswith('-/',i): out[i:i+2]='  ';depth-=1;i+=2
            else:
                if s[i]!='\n':out[i]=' '
                i+=1
        elif string:
            if s[i]=='\\':i+=2
            elif s[i]=='"':string=False;i+=1
            else:i+=1
        elif s[i]=='"':string=True;i+=1
        elif s.startswith('/-',i):out[i:i+2]='  ';depth=1;i+=2
        elif s.startswith('--',i):
            end=s.find('\n',i)
            if end<0:end=len(s)
            out[i:end]=' '*(end-i);i=end
        else:i+=1
    assert depth==0
    return ''.join(out)

def replace_once(s,old,new):
    pat=r'\s+'.join(re.escape(x) for x in old.split())
    matches=list(re.finditer(pat,s))
    assert len(matches)==1,(old,len(matches))
    m=matches[0]
    return s[:m.start()]+new+s[m.end():]

# Reviewer B supplied exact mathematical corrections with line ranges. These
# source-exact replacements preserve the rest of each explanatory paragraph.
B={
'G1LCarryDischarge':[(
'no diagonal\nvalue above `q` equals any value in the closed budget `[·, T]`.',
'no future\nowner `a > q` has diagonal value `gameF a a <= T`.')],
'R144TwoRowTripleCapCounterframe':[(
'Both consecutive rows have exact positive MEX outputs,\nfixed-row injectivity, the full critical record packet, and even the\ndefect-nine form of the cell ceiling.',
'Both displayed consecutive-row prefixes through column `r143C2 m` are\ninjective; their three target cells have exact positive MEX outputs, the\ncritical record packet, and the defect-nine form of the cell ceiling.\nThis is a local source counterframe, not a full triangular-row or canonical\nrecurrence realization.')],
'R164Lag8PreviewOwnerTwoArmNormalForm':[(
'Write `q=v-3` and `c=r-1`.  Four unconditional affine rails emit `q`\nstrictly before row `q`:',
'Write `q=v-3` and `c=r-1`. For `q >= 26`, four affine rails emit `q`\nstrictly before row `q`:'),(
'If owner coverage puts an opening owner of `q` strictly left of `c`, these',
'Under the displayed lag-eight frame, if owner coverage puts an opening\nowner of `q` strictly left of `c`, these')],
'R189Lag8StrictIntermediateRelayCover':[(
'Every column strictly between the lag-three host of `u-5` and the lag-eight\nhost of `u` is exactly one of:',
'Under the displayed atomic lag-eight frame with `q >= 26`, every column\nstrictly between the lag-three host of `u-5` and the lag-eight host of `u`\nsatisfies at least one of:'),(
'The old-relay arm has a unique witness row.',
'No mutual exclusion of the old-carry and old-target-relay predicates is\nasserted. The old-relay arm has a unique witness row.')],
'R198B43PlusTwoDiagonalRoute':[(
'For a first skipped-affine continuation, the row-64 skipped-cell\nclassification already makes `u+1` a blocker.',
'Assuming `SkippedOffsetCellIsBlockerFrom64` and\n`GameFNoThreeConsecutiveBlockers`, the row-64 skipped-cell classification\nfor a first skipped-affine continuation makes `u+1` a blocker.'),(
'Only the first successor row must be at least 64.',
'In addition to those two supplied laws, the first successor row must be\nat least 64.'),(
'Concrete high source reduction from the two proposed structural inputs.\nThe D/S half is discharged here; only the owner-left half remains external.',
'Under the supplied skipped-blocker and NoTriple premises, the D/S\nimplication is proved here. Combining it with the separately supplied\nowner-left premise yields the high past-diagonal source conclusion.')],
'R31TopTailCoreMexNormalForm':[(
'The output two columns before `V3`',
'The output at column `e+2` (two columns before `V2`)')],
'R47FutureBackfillOwnerPacking':[(
'Quantitative upper-half packing.  This is the reusable cardinal core of\nthe `s≥7` argument: `k` distinct owners satisfying `s<2*i` force\n`2*k+1≤s`.',
'Quantitative upper-half packing. For `s > 0`, a duplicate-free list of\n`k` owners with every owner `i < s` and `s < 2*i` satisfies `2*k+1 <= s`.\nThe canonical future-first-gap application supplies at least three owners\nand `s >= 7`.')],
'R51EventECrossEdgeSurvivorExplosion':[(
'Every event E satisfies the stronger cross-edge survivor inequality\n`2*delta+7 <= s+2*|T|`.',
'Under `UnitDip` and the displayed numerical-margin consecutive-dip\nframe, the canonical Event-E packet satisfies the cross-edge survivor\ninequality `2*delta+7 <= s+2*|T|`.')],
'R51EventEMaxDefectHighSurvivorAtom':[(
'Unconditional maximal-defect reduction.  Either the R49 survivor has\nalready reached its owner by row `s+1`, or the only remaining high branch is\nthe explicit finite atom above.',
'Under `UnitDip` and the displayed maximal-defect numerical-margin\nEvent-E frame, the R49 survivor has already reached its owner by row `s+1`,\nor satisfies the explicit high-survivor atom above.')],
'R52RM2BulkFrozenSevenAtomResidual':[(
'The seven feasible predecessor pairs of the maximal high atom.',
'The seven predecessor pairs permitted by the necessary high-atom menu.'),(
'The existing high atom really has seven, rather than eight, feasible\npredecessor configurations.',
'Every existing high atom satisfies one of these seven predecessor\ncombinations. No canonical realization of every combination is proved.')],
'R58Q4FirstLoss':[(
'R58: exact sharpening of the Q4 first-loss branch.',
'R58: exact sharpening of a named certified Q4 loss edge.\n\nThe edge is not asserted minimal: the finite fate certificate supplies\nprevious-row presence and current-row absence, with no earlier-loss\nexclusion. The conclusions below retain their displayed hypotheses.')],
'R59Q4OwnerChronology':[(
'R59: chronology and owner collapse for the surviving Q4 first-loss arm.',
'R59: chronology and owner collapse for a named certified Q4 loss edge.\n\nNo minimality of that edge is asserted. The conclusions below retain the\ndisplayed previous-row presence/current-row absence and UnitDip/residual\nhypotheses.')],
'SJSDiagonalDictionary':[(
'-- The engine reproduces the head of OEIS A029900 -- the frozen canonical\n-- d-word cache -- by kernel evaluation.',
'-- Finite #eval execution prints the first 21 engine d-word values below.\n-- This is not an all-row gameF equivalence theorem or a kernel-certified\n-- equality proof.')],
'XDeadlineCutYoungDiag':[(
'It yields an all-horizon blocker certificate and, below depth three,\nthe three low-bit formulas without assuming `NoTriple` or any host-cover law.',
'It yields an all-horizon blocker certificate with its positive-target\nguard. For cuts `q >= 3` and depths `k < 3`, the three low-bit formulas\nfollow without assuming `NoTriple` or any host-cover law.'),(
'Below depth three, no diagonal born after the cut can mature at the\ntarget.  This is the exact role of the unconditional diagonal rail\n`d(t) >= t + 3`.',
'For `q >= 3` and `k < 3`, no diagonal born after the cut can mature\nat `q+k`. This uses the diagonal rail `d(t) >= t+3` for `t >= 3`.'),(
'The all-`k < 3` low-bit formula.',
'The low-bit formula for `q >= 3` and `k < 3`; no claim for cuts 0, 1, 2.')],
'XTauPrebirthRails':[(
'Forward: coverage of\n  the diagonal MEX at `(q,q)`, with the diagonal source arm killed by owner\n  uniqueness.  Backward: `diagonalMaximal` + row injectivity.',
'Forward: `diagonalMaximal` and row injectivity give `d(t) < d(q)`.\n  Backward: diagonal MEX coverage at `(q,q)` forces a host, with the\n  diagonal source arm excluded by owner uniqueness.')],
}

def main():
    a=read(FULL/'paper-a/LEAN-SOURCE-PROSE-REVIEW.json')
    b=read(FULL/'paper-b/LEAN-SOURCE-PROSE-REVIEW.json')
    assert a['moduleCount']==133 and a['corrections']==37
    assert b['moduleCount']==132 and b['findingsCount']==17
    manifest=read(AUDIT/'final-source-manifest.json')
    gate=read(AUDIT/'final-gate.json')
    assert gate['result']=='passed' and sha(AUDIT/'final-source-manifest.json')==gate['sourceManifestSha256']
    assert set(r['module'] for r in a['records'])|set(r['module'] for r in b['modules'])==set(manifest['modules'])
    changed={r['module']:r for r in a['records'] if r.get('corrections')}
    assert set(changed).isdisjoint(B) and len(changed)==30 and len(B)==15
    for m in manifest['modules']:
        assert sha(CORE/(m.replace('.','/')+'.lean'))==manifest['sourceSha256'][m]
    base=HERE/'immutable-base'
    assert not base.exists(),'Refusing to replace frozen evidence'
    base.mkdir()
    # Preserve every original audit file and its two small evidence subtrees.
    # build-final/build-core remain untouched; their source inputs are also
    # copied below. Compiled objects are hash-bound separately by the run.
    for p in AUDIT.iterdir():
        if p.is_file():
            (base/'lean').mkdir(exist_ok=True);shutil.copy2(p,base/'lean'/p.name)
        elif p.name in ('modules','negative-controls'):
            shutil.copytree(p,base/'lean'/p.name)
    for m in manifest['modules']:
        rel=Path(m.replace('.','/')+'.lean');dest=base/'sources'/rel
        dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(CORE/rel,dest)
    for name in ('lakefile.lean','lean-toolchain','lake-manifest.json'):
        shutil.copy2(CORE/name,base/'sources'/name)
    old_foundation=FULL/'CANONICAL-FOUNDATIONS-at-initial-review.md'
    assert sha(old_foundation)==gate['independentReviewSha256']['../CANONICAL-FOUNDATIONS.md']
    shutil.copy2(old_foundation,base/'CANONICAL-FOUNDATIONS.md')
    for lane in ('paper-a','paper-b'):
        shutil.copy2(FULL/lane/'LEAN-SOURCE-PROSE-REVIEW.json',base/(lane+'-source-prose-review.json'))
    bindings={p.relative_to(base).as_posix():sha(p) for p in base.rglob('*') if p.is_file()}
    save(base/'BINDINGS.json',{'createdAt':dt.datetime.now(dt.timezone.utc).isoformat(),'files':bindings,
      'meaning':'Immutable copy of the initial full passing audit and all original source inputs. Original compiled snapshots remain untouched at audit/full/lean/build-final and build-core.'})
    revisions=[]
    for module in sorted(set(changed)|set(B)):
        rel=Path(module.replace('.','/')+'.lean');original=(CORE/rel).read_text(encoding='utf8');revised=original
        requested=[]
        if module in changed:
            for c in changed[module]['corrections']:
                requested.append(c)
                if c['old'].startswith('[scope omitted'):
                    assert '/-!' in revised
                    scope=textwrap.fill(c['replacement'],78)
                    revised=revised.replace('/-!','/-!\nPublication scope: '+scope+'\n',1)
                elif module=='R168DeepTerminalLeftRelayNormalForm':
                    revised=replace_once(revised,
                      'A source-hole theorem would imply the desired all-depth owner descent,\nbut is strictly stronger: it excludes not only left opening owners but every\npossible column-tail occurrence of the preview value.',
                      'The source-hole condition implies the desired all-depth owner descent.\nIt excludes every column-tail occurrence of the preview value as well as\nleft opening owners. No actual-game separation proving strictness is supplied.')
                else:revised=replace_once(revised,c['old'],c['replacement'])
        else:
            requested=[f for f in b['findings'] if f['module']==module]
            for old,new in B[module]:revised=replace_once(revised,old,new)
        if module=='R177Lag8DiagonalOwnerEarlyDescent':
            revised=replace_once(revised,
              'Computationally, keeping the two terminal strands ascending through row\n`q-1` forces exactly that forbidden neighbour emission.',
              'In the reported finite seeded replay, keeping the two terminal strands\nascending through row `q-1` forced that forbidden neighbour emission.')
        assert original!=revised
        assert mask_comments(original).split()==mask_comments(revised).split(),module+' changed code'
        out=HERE/'revised-sources'/rel;out.parent.mkdir(parents=True,exist_ok=True)
        out.write_text(revised,encoding='utf8')
        diff=''.join(difflib.unified_diff(original.splitlines(True),revised.splitlines(True),fromfile='before/'+rel.as_posix(),tofile='after/'+rel.as_posix()))
        dp=HERE/'diffs'/(module+'.diff');dp.parent.mkdir(exist_ok=True);dp.write_text(diff,encoding='utf8')
        revisions.append({'module':module,'originalSha256':manifest['sourceSha256'][module],
          'revisedSha256':sha(out),'noncommentTokensIncludingStringsIdentical':True,
          'sourcePath':'lean/core/'+rel.as_posix(),'originalSource':(base/'sources'/rel).relative_to(PACKAGE).as_posix(),
          'revisedSource':out.relative_to(PACKAGE).as_posix(),'diff':dp.relative_to(PACKAGE).as_posix(),
          'requestedCorrections':requested})
    assert len(revisions)==45
    save(HERE/'amendment-plan.json',{'result':'staged','createdAt':dt.datetime.now(dt.timezone.utc).isoformat(),
      'inheritedBaseGateSha256':sha(base/'lean/final-gate.json'),'modules':[r['module'] for r in revisions],
      'reviewFindings':54,'followUpClarifications':[{'module':'R177Lag8DiagonalOwnerEarlyDescent','reason':'Independent amendment review requested explicit finite seeded replay scope for the adjacent historical computational observation.'}],
      'reviewBindings':{lane:sha(FULL/lane/'LEAN-SOURCE-PROSE-REVIEW.json') for lane in ('paper-a','paper-b')},
      'revisions':revisions})
    # Public source mutation occurs only after every staged change has passed
    # the code-token guard. The final gate is updated only after revalidation.
    for r in revisions:shutil.copy2(PACKAGE/r['revisedSource'],PACKAGE/r['sourcePath'])
    print(json.dumps({'stagedAndAppliedModules':len(revisions),'reviewFindings':54,'baseBindings':len(bindings)}))

if __name__=='__main__':main()
