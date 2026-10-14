#!/usr/bin/env python3
"""Fresh, strict audit of the publication's 264 intended core Lean modules."""
from __future__ import annotations
import datetime as dt
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parents[2]
CORE = PACKAGE / "lean" / "core"
SNAPSHOT = HERE / "build-core"
LAKE = Path.home() / ".elan/toolchains/leanprover--lean4---v4.29.1/bin/lake.exe"
LEAN = LAKE.with_name("lean.exe")
FLAGS = ["-DwarningAsError=true", "-Dlinter.unnecessarySimpa=false", "-Dlinter.unusedSimpArgs=false", "-Dlinter.unusedVariables=false"]

def utc(): return dt.datetime.now(dt.timezone.utc).isoformat()
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def save(name,obj): (HERE/name).write_text(json.dumps(obj,indent=2,ensure_ascii=False)+"\n",encoding="utf-8")

def prepare():
    old = json.loads((PACKAGE / "lean/receipts/core-build.json").read_text(encoding="utf-8"))
    modules = old["builtLocalModules"]
    assert len(modules) == 264 and len(set(modules)) == 264
    if (SNAPSHOT/".lake/build").exists():
        raise RuntimeError("Fresh audit snapshot already contains build output; preserve receipt and choose a new explicit audit directory instead of silently reusing it")
    SNAPSHOT.mkdir(parents=True,exist_ok=True)
    source_hashes = {}
    for module in modules:
        relative = module.replace(".","/")+".lean"
        src=CORE/relative; target=SNAPSHOT/relative
        assert sha(src)==old["sourceSha256"][relative], relative
        target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(src,target)
        source_hashes[module] = sha(src)
    for name in ("lean-toolchain","lake-manifest.json"):
        shutil.copyfile(CORE/name,SNAPSHOT/name)
    config=(CORE/"lakefile.lean").read_text(encoding="utf-8")
    options=", ".join(json.dumps(x) for x in FLAGS)
    config=config.replace("package ChompLean where", "package ChompLean where\n  moreLeanArgs := #["+options+"]")
    (SNAPSHOT/"lakefile.lean").write_text(config,encoding="utf-8")
    manifest={"createdAt":utc(),"scope":"Every intended core source module, including all generated declarations owned by those modules.","modules":modules,"sourceSha256":source_hashes,"strictFlags":FLAGS,"snapshotConfigurationSha256":sha(SNAPSHOT/"lakefile.lean"),"originalPublicationConfigurationSha256":sha(CORE/"lakefile.lean"),"proofSourcesModified":False}
    save("source-manifest.json",manifest)
    return manifest

def strict_build(manifest):
    receipt={"startedAt":utc(),"command":[str(LAKE),"build","ResearchCore","ChompLean"],"cleanInitialBuildDirectory":not (SNAPSHOT/".lake/build").exists(),"sourceManifestSha256":sha(HERE/"source-manifest.json"),"strictFlags":FLAGS}
    with (HERE/"strict-build.log").open("w",encoding="utf-8") as log:
        result=subprocess.run(receipt["command"],cwd=SNAPSHOT,stdout=log,stderr=subprocess.STDOUT,timeout=3600)
    receipt.update({"finishedAt":utc(),"exitCode":result.returncode,"result":"passed" if result.returncode==0 else "failed","proofSourcesUnchanged":all(sha(SNAPSHOT/(m.replace('.','/')+'.lean'))==h and sha(CORE/(m.replace('.','/')+'.lean'))==h for m,h in manifest['sourceSha256'].items())})
    save("strict-build.json",receipt)
    return receipt

def reject_sorry_control():
    control=HERE/"negative-controls"
    control.mkdir(exist_ok=True)
    source=control/"RejectSorry.lean"
    source.write_text("-- Deliberately invalid negative control; never an admitted project result.\nimport Std\ntheorem auditMustRejectSorry : False := by sorry\n",encoding="utf-8")
    result=subprocess.run([str(LEAN),*FLAGS,str(source)],cwd=SNAPSHOT,capture_output=True,text=True,encoding="utf-8",errors="replace",timeout=60)
    log=result.stdout+result.stderr
    (HERE/"negative-controls/reject-sorry.log").write_text(log,encoding="utf-8")
    receipt={"command":[str(LEAN),*FLAGS,"negative-controls/RejectSorry.lean"],"exitCode":result.returncode,"sourceSha256":sha(source),"result":"passed" if result.returncode!=0 and 'declaration uses `sorry`' in log else "failed","meaning":"Passed means that the intentionally invalid sorry proof was rejected."}
    save("negative-controls/reject-sorry.json",receipt)
    return receipt

if __name__=="__main__":
    manifest=prepare()
    print("Fresh audit snapshot prepared: 264 unchanged proof modules.",flush=True)
    control=reject_sorry_control()
    print("Sorry rejection negative control: "+control["result"],flush=True)
    if control["result"]!="passed":sys.exit(1)
    result=strict_build(manifest)
    print("Strict core build: "+result["result"],flush=True)
    sys.exit(0 if result["result"]=="passed" else 1)
