"""Portable deterministic finite proof obligations; Python standard library only.
Run: python run_checks.py
This is not mining. All-index conclusions require the accompanying written induction.
"""
from pathlib import Path
from collections import deque
import hashlib,json,sys,time
if not __debug__:
    raise RuntimeError('Do not run with -O: assertion checks must be enabled.')
HERE=Path(__file__).resolve().parent
start=time.perf_counter()
checks={}
manifest=json.loads((HERE/'INPUT-MANIFEST.json').read_text(encoding='utf-8'))
for entry in manifest['inputs']:
    actual=hashlib.sha256((HERE/entry['input']).read_bytes()).hexdigest()
    assert actual==entry['sha256'],entry['input']
# Independently regenerate exactly the finite prefix required by the C300 proof.
# Use literal positive MEX, with no live-floor shortcut or stored recurrence engine.
rows=[]; journals=[]; diagonals=set()
for q in range(811):
    journals.append(set(diagonals))
    prefix=set(); row=[]
    for c in range(q+1):
        if c<q and rows[q-1][c]<q:
            y=rows[q-1][c]
        else:
            y=1
            while y in journals[c] or y in prefix:
                y+=1
        row.append(y);prefix.add(y);journals[c].add(y)
    rows.append(row);diagonals.add(row[-1])
assert rows[:3]==[[1],[2,3],[3,2,4]]
checks['literal_prefix']={'last_row':810,'cells':sum(map(len,rows)),
    'recurrence':'positive MEX from 1, private journal plus inherited prior diagonals; COPY iff old value<q'}

certpath=HERE/'inputs/periodic_C300_and_lag120.json'
cert=json.loads(certpath.read_text())
pc=cert['periodic_prefix']; patterns={int(c):g for c,g in pc['patterns'].items()}
frozen={int(c):v for c,v in pc['frozen'].items()}
assert set(patterns)|set(frozen)==set(range(301))
assert not (set(patterns)&set(frozen))
G=max(max(g) for g in patterns.values())
H=max([rows[t][c] for c in range(301) for t in range(c,500)]+[rows[t][t] for t in range(300)])
T=max(500+G,H+1); assert T==676
base=0
for c in range(301):
    if c in frozen: assert frozen[c]==rows[499][c] and frozen[c]<500
    else: assert all(g>=1 for g in patterns[c])
    for q in range(500,T):
        assert rows[q][c]==(frozen[c] if c in frozen else q+patterns[c][q%2])
        base+=1
normalized=0
for c,g in patterns.items():
    for r in range(2):
        blocked={g[(r-s)%2]-s for s in range(1,G+1)}
        blocked.update(gs[r] for col,gs in patterns.items() if col<c)
        z=0
        while z in blocked:z+=1
        assert z==g[r]
        normalized+=1
rails=[{g[r]:c for c,g in patterns.items()} for r in range(2)]
assert all(len(x)==len(patterns) for x in rails)
assert all(rails[r][123]==208 and rails[r][124]==210 for r in range(2))
checks['periodic_C300']={'base_cells':base,'normalized_mex':normalized,'G':G,'H':H,'T':T}

def children(k,m):
    # Direct complete new-reply families after one bottom-cell deletion.
    for j in range(1,m+1):yield k+j,m+1-j,j
    for h in range(1,m+1):yield 0,h,m+1-h
    for ell in range(k):yield ell,m+1,0

# Prior 120 certificate: rebuild closure, then compare saved finite state list.
seen={(k,1,r) for k in range(121) for r in range(2) if k not in rails[r]}
queue=deque(seen); edges=0
while queue:
    k,m,r=queue.popleft()
    for kk,mm,back in children(k,m):
        edges+=1;rr=(r-back)%2
        assert back>0 or kk<k
        if kk in rails[rr]:assert rails[rr][kk]+mm<500
        else:
            child=(kk,mm,rr)
            if child not in seen:seen.add(child);queue.append(child)
        assert len(seen)<10000
assert seen==set(map(tuple,cert['W_certificate']['states']))
M=max(m for k,m,r in seen);count=0
for b in range(500,500+M):
    for k,m,r in seen:
        if b%2==r:assert rows[b][b-m]!=b+k;count+=1
checks['prior_lag120']={'states':len(seen),'edges':edges,'base_checks':count,'max_age':M}

# Rebuild the context graph with four-letter stopping patterns, retaining exact root.
ctx={(k,1,r,'') for k in range(123) for r in range(2) if k not in rails[r]}
queue=deque(ctx);edges=0;stops=set()
while queue:
    k,m,r,hist=queue.popleft()
    for kk,mm,back in children(k,m):
        edges+=1; rr=(r-back)%2
        assert back>0 or kk<k
        assert kk-back<=k and back<=39
        if kk in rails[rr]:assert mm<=40 and rails[rr][kk]+mm<500;continue
        tag='A' if (k,kk,mm,back)==(121,122,m,1) else ('B' if (k,kk,mm,back)==(122,121,m+1,0) else 'X')
        trace=(hist+tag)[-4:]
        if trace in ('ABAB','BABA'):
            rootk,rootm,shift=kk,mm,0
            for tag0 in reversed(trace):
                if tag0=='A':assert rootk==122;rootk=121;shift+=1
                else:assert rootk==121;rootk=122;rootm-=1
            assert rootm==1 and shift==2
            stops.add((trace,rootk,rootm,rr));continue
        child=(kk,mm,rr,trace[-3:] if tag!='X' else '')
        if child not in ctx:ctx.add(child);queue.append(child)
        assert len(ctx)<10000
M=max(x[1] for x in ctx);count=0
for b in range(500,500+M):
    for k,m,r in {(k,m,r) for k,m,r,h in ctx}:
        if b%2==r:assert rows[b][b-m]!=b+k;count+=1
for r in range(2):
    for k in range(121):
        if k not in rails[r]:
            assert all((k,m,r,'') in ctx for m in (2,3))
replies=0
for r in range(2):
    replylist=[(122+j,3-j,j) for j in (1,2)]+[(0,h,3-h) for h in (1,2)]+[(ell,3,0) for ell in range(122)]
    for kk,mm,back in replylist:
        rr=(r-back)%2
        if kk in rails[rr]: assert 539-back>=500 and 539-back-mm>rails[rr][kk]
        elif (kk,mm,rr) in seen: assert 539-back>=500
        elif (kk,mm,back)==(121,3,0):pass # attacked by forced Q; paper step
        else:assert kk<=120 and (kk,mm,rr,'') in ctx
        replies+=1
checks['lag124_context']={'states':len(ctx),'edges':edges,'base_checks':count,'max_age':M,
    'stop_patterns':sorted(stops),'two_cut_replies':replies,
    'limits':'Certificate verifies finite premises; the well-founded all-index descent and game move interpretation are separately audited in the written review.'}


# Tight-width finite base uses the same literal prefix, with no external engine.
death=[(q,row.index(q))for q,row in enumerate(rows)if q>0 and q in row]
# Tight width18 finite base. +col31 all-index bridge is a separate theorem.
tight=[]
for h in range(7,44):
 A=sum(t<=h for t,c in death);E=rows[h][-1]+A-(2*h+1)
 assert E>0;tight.append({'h':h,'d':rows[h][-1],'A':A,'E':E})
source=HERE/'inputs/tight_width18_base.json'
assert json.loads(source.read_text())['rows']==tight
checks['tight_width18']={'status':'PASS literal base7..43','minimumE':min(x['E'] for x in tight),'certificateSHA256':hashlib.sha256(source.read_bytes()).hexdigest()}

base=HERE/'inputs'
cert=json.loads((base/'multi_cut_K211_T6.json').read_text());prefix=json.loads((base/'periodic_prefix_C360.json').read_text())['periodic_prefix']
C=prefix['columns_through'];q0=prefix['q0'];p=prefix['period'];G=prefix['G'];T=prefix['induction_start'];patterns={int(c):g for c,g in prefix['patterns'].items()};frozen={int(c):v for c,v in prefix['frozen'].items()}
assert set(patterns)|set(frozen)==set(range(C+1));assert set(patterns).isdisjoint(frozen)
oldmax=max([rows[t][c] for c in range(C+1) for t in range(c,q0)]+[rows[t][-1] for t in range(C)])
assert oldmax==prefix['old_history_max'];assert T>=q0+G and T>oldmax and q0>C
periodic_cells=0
for q in range(q0,T):
 for c in range(C+1):
  assert rows[q][c]==(frozen[c] if c in frozen else q+patterns[c][q%p]);periodic_cells+=1
for c,g in patterns.items():
 assert min(g)>=1
 for phase in range(p):
  # Negative-offset history never changes normalized nonnegative MEX.
  blocks={g[(phase-s)%p]-s for s in range(1,G+1)}|{gd[phase] for d,gd in patterns.items() if d<c}
  x=0
  while x in blocks:x+=1
  assert x==g[phase]
for c,v in frozen.items():assert rows[q0-1][c]==v<q0
rails=[{g[r]:c for c,g in patterns.items()} for r in range(p)]
assert all(len(rail)==len(patterns) for rail in rails)
states={(s['lag'],s['age'],s['phase']) for s in cert['proof']};assert len(states)==len(cert['proof']);Bmax=cert['max_back'];bt=cert['base_start'];relations=0
def support(k,m,phase):
 global relations
 relations+=1
 if k in rails[phase]:assert bt>=q0 and bt-m>rails[phase][k];return True
 return (k,m,phase) in states
for s in cert['proof']:
 k,m,r=s['lag'],s['age'],s['phase'];cuts=s['cuts'];assert cuts and len(cuts)==len(set(cuts));assert all(1<=t<=bt-m for t in cuts);union=set()
 for t in cuts:
  for j in range(1,m+t):assert j<=Bmax and support(k+j,m+t-j,(r-j)%p)
  for h in range(1,m+t):
   back=m+t-h;assert 1<=back<=Bmax and support(0,h,(r-back)%p)
  union.update(l for l in range(k) if not support(l,m+t,r))
 assert union==set(s['residual_lags']) and len(union)<len(cuts)
for k in range(cert['K']+1):
 for r in range(p):assert support(k,1,r)
wchecks=0
for b in range(bt,bt+Bmax):
 for k,m,r in states:
  if b%p==r:assert rows[b][b-m]!=b+k;wchecks+=1
checks['legacy211']={'status':'PASS periodic normalized identities, literal bases and multi-cut induction support','states':len(states),'supportRelations':relations,'periodicBaseCells':periodic_cells,'normalizedMexIdentities':len(patterns)*p,'wBaseChecks':wchecks,'certificateSHA256':hashlib.sha256((base/'multi_cut_K211_T6.json').read_bytes()).hexdigest(),'prefixSHA256':hashlib.sha256((base/'periodic_prefix_C360.json').read_bytes()).hexdigest()}

checks['tight_width18']['low_boundary_deaths']=[{'h':h,'death':next((q for q,a in death if a==h),None)}for h in range(7)]
checks['status']='PASS'
checks['scope']='Finite bases, normalized periodic MEX identities, lag120 closure, lag124 context descent obligations and lag211 support obligations. Universal statements require the corrected legal-move/induction proofs and exact canonical foundation; no excluded m<=5 claim is checked or promoted.'
checks['elapsedSeconds']=time.perf_counter()-start
checks['checkerSha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
checks['inputManifestSha256']=hashlib.sha256((HERE/'INPUT-MANIFEST.json').read_bytes()).hexdigest()
(HERE/'CHECK-RESULTS.json').write_text(json.dumps(checks,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'status':'PASS','literalLastRow':810,'periodicC300':checks['periodic_C300'],'prior120':checks['prior_lag120'],'lag124':checks['lag124_context'],'legacy211':checks['legacy211'],'tightWidth18':checks['tight_width18'],'elapsedSeconds':checks['elapsedSeconds']},indent=2))
