"""Independent finite physical-board and outcome checks, not an all-n proof."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json

HERE = Path(__file__).resolve().parent
def targets(p, q, r):
    return ([(a, min(a,q), min(a,r)) for a in range(1,p)]
          + [(p, a, min(a,r)) for a in range(q)]
          + [(p, q, a) for a in range(r)])

physical_boards = 0
physical_choices = 0
for p in range(1,9):
    for q in range(p+1):
        for r in range(q+1):
            lengths = (p,q,r)
            cells = {(row,col) for row,n in enumerate(lengths) for col in range(n)}
            actual = []
            for row,col in sorted(cells - {(0,0)}):
                after = {(i,j) for i,j in cells if not (i>=row and j>=col)}
                actual.append(tuple(sum(i==k for i,j in after) for k in range(3)))
            expected = targets(p,q,r)
            assert len(actual)==len(set(actual))
            assert len(actual)==len(expected) and set(actual)==set(expected)
            physical_boards += 1
            physical_choices += len(actual)

losing = {}
for p in range(1,66):
    for q in range(p+1):
        for r in range(q+1):
            losing[p,q,r] = not any(losing[t] for t in targets(p,q,r))
assert losing[1,0,0]
rectangle_winners = []
for n in range(1,66):
    winning = [t for t in targets(n,n,n) if losing[t]]
    assert len(winning)==1, (n,winning)
    rectangle_winners.append({'width':n,'winningTarget':winning[0]})

f = []
for q in range(33):
    row = []
    for r in range(q+1):
        if r<q and f[q-1][r]<q:
            value=f[q-1][r]
        else:
            blocked={f[a][min(a,r)] for a in range(q)} | set(row)
            value=1
            while value in blocked: value+=1
        row.append(value)
    f.append(row)

encoding_cells = 0
for q,row in enumerate(f):
    for r,value in enumerate(row):
        hits=[]
        for p in range(r+1,66):
            board=(p,p,r) if p<q else (p,q,r)
            if losing[board]: hits.append(p)
        assert hits==[value], (q,r,value,hits)
        encoding_cells+=1

report = {'result':'PASS','checkedAt':datetime.now(timezone.utc).isoformat(),
    'physicalBoardMoveComparisons':physical_boards,'physicalNonpoisonChoices':physical_choices,
    'gamePositionsSolved':len(losing),'rectangleWidthsChecked':[1,65],
    'canonicalRowsChecked':[0,32],'completeEncodingCellsChecked':encoding_cells,
    'rectangleWinningTargets':rectangle_winners,
    'scope':'Independent finite model correspondence and boundary regression. Physical cell removal agrees with all three formal cut constructors. Direct game-tree outcomes agree with the literal MEX/COPY completion encoding on this finite domain. Universal statements require the separate Lean proof and semantic audit.',
    'scriptSha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(HERE/'FINITE-GAME-MODEL-CHECK.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in report.items() if k!='rectangleWinningTargets'}))
