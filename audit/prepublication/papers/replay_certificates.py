from pathlib import Path
import hashlib,json,shutil,subprocess,sys
lane=Path(__file__).resolve().parent
extracted=lane.parent/'extracted'
copy=lane/'certificate-replay'
assert copy.resolve().parent==lane.resolve()
if not copy.exists():shutil.copytree(extracted/'certificates',copy)
run=subprocess.run([sys.executable,str(copy/'run_checks.py')],cwd=lane,capture_output=True,text=True)
assert run.returncode==0,run.stderr
receipt=json.loads((copy/'CHECK-RESULTS.json').read_text())
assert receipt['status']=='PASS'
assert receipt['prior_lag120']['states']==1284 and receipt['lag124_context']['two_cut_replies']==252
assert receipt['legacy211']['states']==8431 and receipt['legacy211']['supportRelations']==1355278
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
report={'result':'passed','method':'Fresh deterministic replay of the exact delivered checker and projected inputs, copied to this audit lane. The extracted ZIP and release receipts were not modified. The checker text and induction interpretation were reread; old PASS labels are not used to establish its obligations.',
 'sourceCheckerSHA256':digest(extracted/'certificates/run_checks.py'),'copiedCheckerSHA256':digest(copy/'run_checks.py'),'inputManifestSHA256':digest(copy/'INPUT-MANIFEST.json'),
 'freshResults':receipt,'inputHashes':[{'path':p.relative_to(copy).as_posix(),'sha256':digest(p)}for p in sorted((copy/'inputs').glob('*.json'))],
 'inductionBridgeChecks':['Periodic prefix: inherited/pre-q0 labels below T; awards older than G lie below current row; LIVE-FLOOR rules out smaller labels; finite normalized MEX identities close lexicographic induction on row and column.','Lag120: replies either paid by rail or in closed state family; every unpaid support decreases middle row or same-row top lag, and the maximum-back base interval is checked.','Lag124: context stopping traces recover an actual earlier/equal-top penultimate failure. The forced-Q terminal reply is a written mathematical step and is not falsely certified by the Python pass branch.','Lag211: distinct bottom cuts need distinct residual top lags because P positions with common top/middle and different bottoms attack one another. Exact residual Hall deficits, shifted phases and backward/same-row supports are checked.','Tight width: finite E>0 on 7..43 is combined with the separate all-index col31 rail for h>=44; null small-row death observations are not proofs of immortality.'],
 'limits':'This confirms finite proof obligations and their exact data. Complete public definitions and written legal-move/induction derivations remain a separate delivery requirement, and no excluded m<=5, A1 or Q=o(n) claim is established.'}
(lane/'FINITE-CERTIFICATE-REPLAY.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'result':'passed','lastRow':receipt['literal_prefix']['last_row'],'lag211States':receipt['legacy211']['states'],'seconds':receipt['elapsedSeconds']}))
