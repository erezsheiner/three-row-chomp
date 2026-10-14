#!/usr/bin/env python3
"""Collect first-party Lean sources without merging incompatible module versions.

The inventory is a source archive, not a theorem-certification claim. Run with
--build to attempt a fresh build of the preserved, pinned canonical core.
"""
from __future__ import annotations
import argparse
import collections
import concurrent.futures
import datetime as dt
import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

PACKAGE = Path(__file__).resolve().parents[1]
DEFAULT_ROOTS = {
    "aug": PACKAGE.parents[1],
    "legacy": PACKAGE.parents[1].parent / "Real Three Row Chomp",
}
ROOT_LABELS = {
    "XGameFOrderedBlockerUnionReconstruction": "Canonical game reconstruction in the blocker-union quotient",
    "XDeadlineCutYoungDiag": "Deadline cuts and young diagonal bounds",
    "EndToEndInvariantAssembly": "End-to-end invariant assembly and winning-move emission",
    "SparseDualFailures": "Sparse dual failure bounds",
    "MinErrorFekete": "Minimum-error Fekete inequalities",
    "XEAARecordFreezeGap": "Record, freeze and gap bounds",
    "R201DiagDoubleSlackCeilingChain": "Diagonal double-slack ceiling chain",
    "R182ForwardFreezeCollisionExchange": "Forward-freeze collision exchange",
    "ClaudeCanonicalRankThreePrefix": "Canonical rank-three prefix and peeled tail",
    "ChompLean.Statement": "Three-row Chomp: game definitions and the uniqueness statement",
    "ChompLean.Proof": "Uniqueness of the winning opening in three-row Chomp",
    "ResearchCore": "Research core: nine principal research roots",
    "ChompLean": "Uniqueness: statement and proof entry point",
}
ROOT_SUMMARIES = {
    "ChompLean.Statement": "Defines legal non-poison moves, P-positions and the claim that every positive three-row rectangle has exactly one winning target.",
    "ChompLean.Proof": "Derives the recurrence model from the actual game and proves uniqueActualWinningTarget_checked for every positive rectangle.",
    "XGameFOrderedBlockerUnionReconstruction": "Reconstructs the canonical game in the ordered blocker-union quotient using normalized old source values at a cut.",
    "XDeadlineCutYoungDiag": "Splits diagonal owners into disjoint old and new arms, giving a blocker certificate and depth-below-three formulas without NoTriple or a host-cover law.",
    "EndToEndInvariantAssembly": "Conditional composition theorem for the thirty-track algorithm; game-specific macro obligations remain explicit fields of EndToEndInvariantPortfolio.",
    "SparseDualFailures": "Finite bracketing estimate: B bad indices cannot support height above 2B+3 under the stated speed and good-index bounds. This module does not by itself prove the asymptotic Chomp application.",
    "MinErrorFekete": "Finite arithmetic bounds for iterating a fixed block under a minimum-error subadditivity hypothesis; supplies estimates used by a Fekete limit argument.",
    "XEAARecordFreezeGap": "Proves a height-dependent gap for a positive EAA blocker's freeze seat. The separate cross-record RecordFreezeRefractory statement remains outside this result.",
    "R201DiagDoubleSlackCeilingChain": "Strong induction establishing the sharp interior ceiling and improved diagonal source bound in the positional double-slack argument.",
    "R182ForwardFreezeCollisionExchange": "Shows that forward freeze collisions force four-cell exchanges and specializes the result to the lag-eight terminal tail.",
    "ClaudeCanonicalRankThreePrefix": "For physical rows q >= 10, identifies live columns [0,2,5], their source queues and the canonical peeled [1,2,4] output prefix.",
    "ResearchCore": "Import umbrella for the nine principal canonical research modules; follow each module for its exact statement and hypotheses.",
    "ChompLean": "Import umbrella for the audited game statement and uniqueness proof.",
}
EXCLUDES = [".git", ".lake", "node_modules", ".venv", "venv", "__pycache__", ".elan", "publication"]

def utc():
    return dt.datetime.now(dt.timezone.utc).isoformat()

def write_json(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

def mask_noncode(text):
    """Mask nested comments and string literals, retaining offsets and newlines.

    This is a lexical audit only; it is deliberately not described as Lean parsing.
    """
    out = list(text)
    i = 0
    n = len(text)
    while i < n:
        start = i
        if text.startswith("/-", i):
            depth = 1
            i += 2
            while i < n and depth:
                if text.startswith("/-", i): depth += 1; i += 2
                elif text.startswith("-/", i): depth -= 1; i += 2
                else: i += 1
        elif text.startswith("--", i):
            i = text.find("\n", i)
            if i < 0: i = n
        elif text[i] == '"':
            i += 1
            while i < n:
                if text[i] == "\\": i += 2
                elif text[i] == '"': i += 1; break
                else: i += 1
        else:
            i += 1
            continue
        for j in range(start, min(i, n)):
            if out[j] not in "\r\n": out[j] = " "
    return "".join(out)

DECL = re.compile(r"(?m)^[ \t]*(?:@\[[^\n]*\][ \t]*)?(?:(?:private|protected|noncomputable|unsafe)\s+)*(theorem|lemma|def|abbrev|structure|class|inductive|opaque|axiom)\s+([^\s:({\[]+)")

def extract(text):
    code = mask_noncode(text)
    declarations = []
    for m in DECL.finditer(code):
        end = code.find(":=", m.end())
        where = re.search(r"\bwhere\b", code[m.end():m.end()+1600])
        stops = [m.end()+1200, len(code)]
        if end >= 0: stops.append(end)
        if where: stops.append(m.end()+where.start())
        snippet = " ".join(text[m.start():min(stops)].strip().split())
        declarations.append({"kind": m.group(1), "name": m.group(2),
                             "line": code.count("\n", 0, m.start(1)) + 1,
                             "statement": snippet[:1200]})
    flags = {}
    for token in ("sorry", "admit", "axiom", "native_decide"):
        flags[token] = [{"line": code.count("\n", 0, m.start()) + 1}
                        for m in re.finditer(r"(?<![\w'])" + token + r"(?![\w'])", code)]
    imports = []
    for m in re.finditer(r"(?m)^\s*import\s+([^\r\n]+)", code):
        imports.extend(m.group(1).split())
    return declarations, flags, imports

def discover(roots):
    paths = []
    errors = []
    for alias, root in roots.items():
        if not root.is_dir():
            errors.append({"root": alias, "error": "Source root is missing", "path": str(root)})
            continue
        args = ["rg", "--files", "--hidden", "--no-ignore", "-g", "*.lean"]
        for x in EXCLUDES: args += ["-g", f"!**/{x}/**"]
        result = subprocess.run(args, cwd=root, capture_output=True, text=True, encoding="utf-8", errors="replace")
        for line in result.stdout.splitlines():
            p = root / line
            paths.append((alias, root, p))
        for line in result.stderr.splitlines():
            errors.append({"root": alias, "error": line.replace(str(root), alias)})
        if result.returncode not in (0, 1, 2):
            errors.append({"root": alias, "error": f"rg returned {result.returncode}"})
    return paths, errors

def read_source(item):
    alias, root, path = item
    try:
        data = path.read_bytes()
        return {"sourcePath": alias + "/" + path.relative_to(root).as_posix(),
                "path": path, "sha256": hashlib.sha256(data).hexdigest(), "sizeBytes": len(data)}, None
    except OSError as exc:
        return None, {"root": alias, "error": str(exc), "path": str(path)}

def priority(item):
    p = item["sourcePath"]
    return (0 if p.startswith("aug/bank/formal-core/") else 1,
            bool(re.search(r"(?:snapshot|backup|archive|copied|_old)", p, re.I)), len(p), p)

def module_for(source_path):
    if source_path.startswith("aug/bank/formal-core/"):
        return source_path[len("aug/bank/formal-core/"):-5].replace("/", ".")
    return Path(source_path).stem

def core_closure(core):
    pending = ["ResearchCore", "ChompLean"]
    closure = set()
    missing = set()
    while pending:
        module = pending.pop()
        if module in closure or module in ("Std", "Init", "Lean", "Lake") or module.startswith(("Std.", "Init.", "Lean.", "Lake.")):
            continue
        path = core / (module.replace(".", "/") + ".lean")
        if not path.exists(): missing.add(module); continue
        closure.add(module)
        pending.extend(extract(path.read_text(encoding="utf-8-sig"))[2])
    return sorted(closure), sorted(missing)

def prepare_lake_layout(core, catalog, inventory):
    """Register the historical top-level modules without editing proof sources."""
    original = PACKAGE / "lean" / "receipts" / "lakefile.original.lean"
    original.parent.mkdir(parents=True, exist_ok=True)
    matching = next(e for e in catalog if e["sourcePath"] == "aug/bank/formal-core/lakefile.lean")
    if hashlib.sha256((core / "lakefile.lean").read_bytes()).hexdigest() == matching["sha256"]:
        shutil.copyfile(core / "lakefile.lean", original)
    if not original.exists() or hashlib.sha256(original.read_bytes()).hexdigest() != matching["sha256"]:
        raise RuntimeError("The original Lake configuration is not preserved with its exact inventory hash")
    matching["attachment"] = "sources/lean/receipts/lakefile.original.lean"
    matching["summary"] = "Original canonical Lake configuration, preserved as provenance. The public build configuration additionally registers all top-level research modules."
    for item in inventory["contents"]:
        if item["sha256"] == matching["sha256"]:
            item["packagedPath"] = "lean/receipts/lakefile.original.lean"
    modules = sorted(p.stem for p in core.glob("*.lean") if p.stem not in ("lakefile", "ChompLean"))
    registered = ",\n    ".join(".one `" + m for m in modules)
    generated = "import Lake\nopen Lake DSL\n\npackage ChompLean where\n\nlean_lib ChompLean where\n\n@[default_target]\nlean_lib ResearchCore where\n  roots := #[`ResearchCore]\n  globs := #[\n    " + registered + "\n  ]\n"
    (core / "lakefile.lean").write_text(generated, encoding="utf-8")
    (core / "README.md").write_text("# Canonical Lean core\n\nPinned Lean 4.29.1 package for `lake build ResearchCore ChompLean`.\n\nSee [coverage and verification](../../docs/LEAN-COVERAGE.md) for principal results, assumptions and current receipts. Every theorem proof source is preserved byte-for-byte from `aug/bank/formal-core`. The publication Lake configuration registers all top-level research modules for a fresh build; its original is preserved at [lakefile.original.lean](../receipts/lakefile.original.lean). No precompiled artifacts are part of this source package.\n", encoding="utf-8")
    inventory["publicationAdaptations"] = [{"path": "lean/core/lakefile.lean", "reason": "Register all top-level canonical research modules so a fresh Lake build discovers the import closure.", "original": "lean/receipts/lakefile.original.lean", "proofSourcesChanged": False}]

def build_core(core, lake):
    receipt_dir = PACKAGE / "lean" / "receipts"
    receipt_dir.mkdir(parents=True, exist_ok=True)
    source_hashes = {p.relative_to(core).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                     for p in sorted(core.rglob("*.lean")) if ".lake" not in p.parts}
    for name in ("lean-toolchain", "lake-manifest.json"):
        source_hashes[name] = hashlib.sha256((core / name).read_bytes()).hexdigest()
    clean = not (core / ".lake" / "build").exists()
    receipt = {"startedAt": utc(), "command": [lake, "build", "ResearchCore", "ChompLean"],
               "workingDirectory": "lean/core", "cleanInitialBuildDirectory": clean,
               "sourceSha256": source_hashes, "verificationScope": "Build of ResearchCore and ChompLean and their imported local dependency closure; no stale build artifacts copied."}
    log = receipt_dir / "core-build.log"
    try:
        version = subprocess.run([lake, "--version"], cwd=core, capture_output=True, text=True, timeout=30)
        receipt["lakeVersion"] = (version.stdout + version.stderr).strip()
        with log.open("w", encoding="utf-8") as out:
            result = subprocess.run(receipt["command"], cwd=core, stdout=out, stderr=subprocess.STDOUT, timeout=900)
        receipt["exitCode"] = result.returncode
        receipt["result"] = "passed" if result.returncode == 0 else "failed"
    except (OSError, subprocess.TimeoutExpired) as exc:
        receipt["result"] = "blocked" if isinstance(exc, OSError) else "timeout"
        receipt["error"] = str(exc)
    receipt["finishedAt"] = utc()
    receipt["sourceUnchangedAfterBuild"] = all((core / p).exists() and hashlib.sha256((core / p).read_bytes()).hexdigest() == h for p,h in source_hashes.items())
    receipt["localModuleClosure"], receipt["missingLocalImports"] = core_closure(core)
    write_json(receipt_dir / "core-build.json", receipt)
    return receipt

def refresh_verification(catalog, receipt):
    closure = set(receipt.get("builtLocalModules", receipt.get("localModuleClosure", [])))
    passed = receipt.get("result") == "passed" and receipt.get("sourceUnchangedAfterBuild")
    for entry in catalog:
        entry["status"] = "source-collected"
        entry["verification"] = "Collected source only; not independently rebuilt in this publication package."
        entry.pop("verificationReceipt", None)
        relative = entry["attachment"].removeprefix("sources/lean/core/")
        verified = (passed and entry["attachment"].startswith("sources/lean/core/") and
                    entry["module"] in closure and receipt["sourceSha256"].get(relative) == entry["sha256"])
        if verified:
            entry["status"] = "lean-verified"
            entry["verification"] = "Fresh pinned Lean build passed for this exact source hash and its core import closure. Build acceptance is distinct from an axiom audit."
            entry["verificationReceipt"] = "sources/lean/receipts/core-build.json"

def bind_fresh_build_coverage(core, receipt, receipt_path):
    if receipt.get("result") != "passed" or not receipt.get("cleanInitialBuildDirectory") or not receipt.get("sourceUnchangedAfterBuild"):
        return
    if "builtLocalModules" in receipt:
        return
    compiled = []
    for relative, sha in receipt["sourceSha256"].items():
        if not relative.endswith(".lean") or relative == "lakefile.lean": continue
        module = relative[:-5].replace("/", ".")
        if (core / ".lake" / "build" / "lib" / "lean" / relative).with_suffix(".olean").is_file():
            compiled.append(module)
    if compiled:
        receipt["builtLocalModules"] = sorted(compiled)
        receipt["builtModuleEvidence"] = "Successful source-unchanged build began with no .lake/build directory; each listed source has an output produced in that fresh directory. The ResearchCore library registers all top-level research source modules, including modules outside the umbrella import closure."
        write_json(receipt_path, receipt)

def enrich_catalog(catalog, inventory):
    counts = collections.Counter()
    for entry in catalog:
        path = entry["sourcePath"].lower()
        if entry["sourcePath"].startswith("aug/bank/formal-core/"):
            classification = "canonical-core"
            if entry["module"] in ROOT_SUMMARIES:
                entry["summary"] = ROOT_SUMMARIES[entry["module"]]
        elif any(word in path for word in ("miner", "/generated/", "/proposals/", "-proposed", "/fixtures/", "prover-eval")):
            classification = "experimental-or-generated"
        elif any(word in path for word in ("snapshot", "backup", "/archive/", "audit", "/_c0/", "/verification/", "/review/")):
            classification = "historical-or-audit"
        else:
            classification = "supplemental-project"
        entry["provenanceClassification"] = classification
        if classification == "experimental-or-generated":
            entry["topic"] = "Experimental and generated Lean sources"
            entry["summary"] = "Experimental, generated or miner-related source retained for completeness. Collection is not evidence that this candidate compiled or proves a project result. " + str(entry["declarationCount"]) + " declarations extracted lexically."
        counts[classification] += 1
    inventory["summary"]["contentCountsByProvenanceClassification"] = dict(counts)

def audit_principal_axioms(core, lake, build_receipt):
    source = PACKAGE / "lean" / "audits" / "PrincipalAxioms.lean"
    receipt_dir = PACKAGE / "lean" / "receipts"
    log_path = receipt_dir / "principal-axioms.log"
    command = [lake, "env", "lean", "../audits/PrincipalAxioms.lean"]
    receipt = {"startedAt": utc(), "command": command, "workingDirectory": "lean/core",
               "auditSourceSha256": hashlib.sha256(source.read_bytes()).hexdigest(),
               "coreBuildReceiptSha256": hashlib.sha256((receipt_dir / "core-build.json").read_bytes()).hexdigest(),
               "scope": "Kernel axiom dependencies of the ten explicitly named principal declarations only; explicit theorem hypotheses remain in force."}
    with log_path.open("w", encoding="utf-8") as out:
        result = subprocess.run(command, cwd=core, stdout=out, stderr=subprocess.STDOUT, timeout=180)
    log = log_path.read_text(encoding="utf-8", errors="replace")
    reported = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log, re.S)
    reported += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", log)]
    receipt["declarations"] = [{"name": name, "axioms": [a.strip() for a in axioms.split(",") if a.strip()]} for name,axioms in reported]
    receipt["exitCode"] = result.returncode
    receipt["finishedAt"] = utc()
    receipt["result"] = "passed" if result.returncode == 0 and len(reported) == 10 else "failed"
    receipt["nonstandardAxioms"] = sorted({a for d in receipt["declarations"] for a in d["axioms"] if a not in {"propext", "Classical.choice", "Quot.sound"}})
    write_json(receipt_dir / "principal-axioms.json", receipt)
    return receipt

def verify_source_archive(inventory):
    def check(item):
        path = PACKAGE / item["packagedPath"]
        try:
            actual = hashlib.sha256(path.read_bytes()).hexdigest()
            return None if actual == item["sha256"] else {"path": item["packagedPath"], "expected": item["sha256"], "actual": actual}
        except OSError as exc:
            return {"path": item["packagedPath"], "error": str(exc)}
    receipt = {"startedAt": utc(), "scope": "Rehash every unique archived source against its original SHA-256; generated publication configuration is separately bound by the build receipt."}
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        errors = [result for result in pool.map(check, inventory["contents"]) if result]
    receipt.update({"finishedAt": utc(), "checkedContents": len(inventory["contents"]), "errors": errors,
                    "result": "passed" if not errors else "failed",
                    "sourceHashSetSha256": hashlib.sha256("\n".join(sorted(x["sha256"] for x in inventory["contents"])).encode()).hexdigest()})
    write_json(PACKAGE / "lean" / "receipts" / "source-integrity.json", receipt)
    return receipt

def attach_axiom_evidence(catalog):
    path = PACKAGE / "lean" / "receipts" / "principal-axioms.json"
    if not path.is_file(): return
    audit = json.loads(path.read_text(encoding="utf-8"))
    build = PACKAGE / "lean" / "receipts" / "core-build.json"
    if audit.get("result") != "passed" or audit.get("coreBuildReceiptSha256") != hashlib.sha256(build.read_bytes()).hexdigest(): return
    for entry in catalog:
        if entry["status"] != "lean-verified" or not entry.get("mainResult"): continue
        local_names = {d["name"] for d in entry["extractedDeclarations"]}
        hits = [d for d in audit["declarations"] if d["name"].split(".")[-1] in local_names]
        if hits:
            entry["principalAxiomAudit"] = {"receipt": "sources/lean/receipts/principal-axioms.json", "declarations": hits, "scope": "Only these named declarations; explicit theorem hypotheses still apply."}

def write_docs(inventory, catalog, receipt):
    summary = inventory["summary"]
    verified = sum(e["status"] == "lean-verified" for e in catalog)
    audit_path = PACKAGE / "lean" / "receipts" / "principal-axioms.json"
    audit = json.loads(audit_path.read_text(encoding="utf-8")) if audit_path.exists() else {}
    rows = []
    for e in catalog:
        if e.get("mainResult"):
            path = e["attachment"].removeprefix("sources/")
            rows.append(f"| {e['title']} | `{e['module']}` | {e['status']} | [Source](../{path}) |")
    content = f"""# Lean source coverage and verification

This publication package preserves first-party Lean source from both local project
workspaces. It is an English navigation layer over the collected sources. Original
source bytes, including original comments, are preserved for hash verification.

- Discovered readable source paths: **{summary['sourcePathCount']:,}**.
- Distinct source contents (SHA-256): **{summary['uniqueContentCount']:,}**.
- Searchable module-content records: **{len(catalog):,}**.
- Exact source records covered by this package's fresh successful build: **{verified:,}**.
- Discovery/read limitations: **{len(inventory['errors'])}** recorded errors.

Content records by representative source provenance: {json.dumps(summary.get('contentCountsByProvenanceClassification', {}), ensure_ascii=False)}.
This path-based classification is a navigation aid, not a proof-status judgment.

These are file/content counts, **not a count of independent or unique theorems**.
The same theorem can occur in multiple module versions and several theorem names
can express related or conditional results.

## Principal entry points

| Result family | Module | Verification | Source |
| --- | --- | --- | --- |
{chr(10).join(rows)}

The nine roots imported by `ResearchCore.lean` are preserved exactly. The
`ChompLean` entry point additionally exposes the game statement and uniqueness
proof. In particular, locate `ChompLean.uniqueActualWinningTarget_checked` in
`core/ChompLean/Proof.lean`; `core/ChompLean/Statement.lean` defines the intended
game and `UniqueActualWinningTargetClaim`.

## What was collected

Discovery used `rg --files --hidden --no-ignore` in each named source root.
Excluded directories: {', '.join('`'+x+'`' for x in EXCLUDES)}.
Dependencies, `.olean` products, native binaries, logs and build caches are not
used as proof evidence. First-party `.lean` files under other build, run, snapshot
or archive directories remain in the inventory and are labelled as source only
unless this package has exact build evidence. Access-denied paths are retained in
`data/lean-source-inventory.json`; the inventory is exhaustive for the readable,
discoverable files in this scope, not an assertion about inaccessible directories.

The canonical source closure is in `lean/core/`. Additional distinct source
contents are archived under `lean/supplemental/<sha256>/<original-filename>`.
Each record retains **all original source paths**. Identical copies are merged by
byte hash; differing versions are kept separately. Supplemental files deliberately
do not form a single Lean import path: incompatible historical module names must
not silently overwrite each other. Their original project contexts are identified
by provenance and must be reconstructed before independent builds.

One build-only adaptation is explicit: the publication's `lean/core/lakefile.lean`
registers every top-level research module. The original Lake configuration only
registered the umbrella and a fresh build could not resolve its imports. Its
exact original bytes are preserved in `lean/receipts/lakefile.original.lean` and
remain catalogued by their original hash. **No theorem proof source was changed.**

## Search extraction and assumptions

Catalogue entries describe modules (unique source contents), not kernel-resolved
declarations. `extractedDeclarations` records lexical names, source lines and
statement excerpts for theorem, lemma, definition and structural declarations.
Names are local as written; namespace resolution, macro expansion, generated
declarations and complete elaborated types are outside the extraction scope.
`declarationCount` is a lexical count and is not a unique theorem count.

The source audit masks nested block comments, line comments and string literals
before looking for `sorry`, `admit`, `axiom` and `native_decide`. The per-module
`sourceAudit` lists hits by line. It is **not a kernel axiom certificate**: theorem
hypotheses, imported axioms, metaprogramming and trust assumptions require separate
inspection. A successful build alone does not show a theorem is unconditional.
Conditional research implications and counterframes retain their original
statements and assumptions in the source.

An additional named-declaration audit is supplied at
`lean/audits/PrincipalAxioms.lean`. Its current status is
**{audit.get('result', 'not run')}**. When run successfully, the
`lean/receipts/principal-axioms.json` receipt lists the kernel axiom dependencies
of exactly those ten named principal results, with the raw output in the matching
log. This audit does not cover every archived source. Explicit hypotheses remain
part of each theorem even when its kernel axiom list contains only standard Lean
foundations (`propext`, `Classical.choice`, `Quot.sound`).

## Reproduction

```sh
cd lean/core
lake build ResearchCore ChompLean
```

The pinned toolchain is `leanprover/lean4:v4.29.1`; the canonical package has no
external Lake dependencies. Run a fresh checkout with no `.lake/build` directory.
`lean/receipts/core-build.json` records the command, tool version, start/end,
module closure and exact source hashes when a package build was attempted.
`lean/receipts/core-build.log` contains its output. Current attempt:
**{receipt.get('result', 'not attempted')}**.

To regenerate the archive from the local source workspaces:

```sh
python scripts/prepare_lean.py
python scripts/prepare_lean.py --build
python scripts/prepare_lean.py --refresh-only --audit-axioms
```

Supply `--source-root aug=/path/to/ThreeRowChompAug --source-root
legacy=/path/to/RealThreeRowChomp` when source locations differ. The script never
deletes a source workspace or merges historical module versions. A prior build
receipt remains applicable only while its source hashes match.
"""
    (PACKAGE / "docs").mkdir(exist_ok=True)
    (PACKAGE / "docs" / "LEAN-COVERAGE.md").write_text(content, encoding="utf-8")
    readme = """# Three-row Chomp Lean sources

Start with [coverage and verification](../docs/LEAN-COVERAGE.md).

- `core/`: canonical Lean 4.29.1 package, principal research roots and uniqueness.
- `supplemental/`: additional distinct source versions, content-addressed, with
  provenance in `../data/lean-source-inventory.json`.
- `receipts/`: reproducible verification evidence for this publication snapshot.

Search catalogue status describes the exact collected source. Historical files
and experimental candidates are retained without promotion to proved results.
"""
    (PACKAGE / "lean" / "README.md").write_text(readme, encoding="utf-8")

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", action="append", default=[])
    parser.add_argument("--build", action="store_true")
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--audit-axioms", action="store_true", help="Audit the ten principal declarations after a successful current core build.")
    parser.add_argument("--verify-sources", action="store_true", help="Rehash every archived source against the inventory.")
    parser.add_argument("--refresh-only", action="store_true", help="Refresh catalogue verification from the existing receipt; do not rescan.")
    args = parser.parse_args()
    roots = {alias: Path(path).resolve() for alias,path in (x.split("=",1) for x in args.source_root)} if args.source_root else DEFAULT_ROOTS
    core = PACKAGE / "lean" / "core"
    data_dir = PACKAGE / "data"
    receipt_path = PACKAGE / "lean" / "receipts" / "core-build.json"
    receipt = json.loads(receipt_path.read_text(encoding="utf-8")) if receipt_path.exists() else {}
    if args.refresh_only:
        catalog = json.loads((data_dir / "formal-catalog.json").read_text(encoding="utf-8"))
        inventory = json.loads((data_dir / "lean-source-inventory.json").read_text(encoding="utf-8"))
    else:
        print("Discovering Lean source paths...", flush=True)
        paths, errors = discover(roots)
        grouped = {}
        with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
            for item, error in pool.map(read_source, paths):
                if error: errors.append(error)
                else: grouped.setdefault(item["sha256"], []).append(item)
        print(f"Read {sum(map(len, grouped.values()))} source paths; {len(grouped)} distinct contents.", flush=True)
        catalog = []
        contents = []
        for index, (sha, origins) in enumerate(sorted(grouped.items())):
            origins.sort(key=priority)
            primary = origins[0]
            source = primary["sourcePath"]
            src = primary["path"]
            is_core = source.startswith("aug/bank/formal-core/")
            relative = "core/" + source[len("aug/bank/formal-core/"):] if is_core else f"supplemental/{sha}/{src.name}"
            target = PACKAGE / "lean" / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(src, target)
            text = target.read_text(encoding="utf-8-sig", errors="replace")
            declarations, flags, imports = extract(text)
            module = module_for(source)
            title = ROOT_LABELS.get(module) if is_core else None
            if not title: title = re.sub(r"(?<=[a-z0-9])(?=[A-Z])", " ", Path(source).stem).replace("_", " ")
            topic = "Uniqueness and game foundations" if is_core and module.startswith("ChompLean") else "Canonical research core" if is_core else "Supplemental and historical Lean sources"
            origins_public = [x["sourcePath"] for x in origins]
            assumptions = "Read statement-specific hypotheses in the linked source; source collection alone does not establish an unconditional theorem."
            record = {"id": "lean-" + sha[:20], "title": title, "kind": "lean", "status": "source-collected",
                      "summary": f"{topic}. {len(declarations)} lexically extracted declarations in this source version; {len(origins)} original path(s) retained.",
                      "statement": "\n".join(d["statement"] for d in declarations if d["kind"] in ("theorem", "lemma"))[:8000],
                      "assumptions": assumptions, "topic": topic, "sourcePath": source, "sourceLine": 1,
                      "attachment": "sources/lean/" + relative, "module": module, "sha256": sha,
                      "mainResult": is_core and module in ROOT_LABELS, "sourcePaths": origins_public,
                      "extractionScope": "module; lexical local declaration names and statement excerpts; not kernel-resolved theorem inventory",
                      "declarationCount": len(declarations), "extractedDeclarations": declarations,
                      "sourceAudit": flags, "imports": imports,
                      "searchText": " ".join([module, *origins_public, *(d["name"] for d in declarations)]),
                      "verification": "Collected source only; not independently rebuilt in this publication package."}
            catalog.append(record)
            contents.append({"sha256": sha, "sizeBytes": primary["sizeBytes"], "packagedPath": "lean/"+relative, "sourcePaths": origins_public})
            if (index + 1) % 500 == 0: print(f"Packaged {index+1} distinct files.", flush=True)
        # Preserve every canonical import path even if two core files are byte-identical.
        original_core = roots["aug"] / "bank" / "formal-core"
        for path in original_core.rglob("*"):
            rel = path.relative_to(original_core)
            if ".lake" in rel.parts or not path.is_file(): continue
            if path.suffix == ".lean" or path.name in ("lean-toolchain", "lake-manifest.json"):
                dest = core / rel
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(path, dest)
        (core / "README.md").write_text("# Canonical Lean core\n\nPinned source package for `lake build ResearchCore ChompLean`.\nSee [coverage and verification](../../docs/LEAN-COVERAGE.md) for status and scope.\nSource bytes are preserved from `aug/bank/formal-core`; no compiled artifacts were copied.\n", encoding="utf-8")
        inventory = {"schemaVersion": 1, "generatedAt": utc(), "sourceRoots": {k: str(v) for k,v in roots.items()},
                     "scope": "All discoverable readable first-party .lean files after documented dependency/cache/output exclusions.",
                     "excludedDirectoryNames": EXCLUDES,
                     "summary": {"sourcePathCount": sum(map(len,grouped.values())), "uniqueContentCount": len(grouped),
                                 "canonicalCoreSourceFiles": len([p for p in core.rglob("*.lean") if ".lake" not in p.parts]),
                                 "uniqueContentBytes": sum(x["sizeBytes"] for x in contents)},
                     "errors": errors, "contents": contents}
    prepare_lake_layout(core, catalog, inventory)
    if args.verify_sources:
        integrity = verify_source_archive(inventory)
        print("Archived-source integrity: " + integrity["result"], flush=True)
    if args.build:
        print("Attempting pinned canonical-core build; output is saved to lean/receipts/core-build.log.", flush=True)
        receipt = build_core(core, args.lake)
        print("Core build: " + receipt["result"], flush=True)
    # A receipt is usable only if all current core source bytes still match it.
    if receipt:
        receipt["sourceUnchangedAfterBuild"] = all((core/p).is_file() and hashlib.sha256((core/p).read_bytes()).hexdigest() == h for p,h in receipt.get("sourceSha256", {}).items())
        bind_fresh_build_coverage(core, receipt, receipt_path)
    if args.audit_axioms:
        if receipt.get("result") != "passed" or not receipt.get("sourceUnchangedAfterBuild"):
            raise RuntimeError("Principal axiom audit requires a successful matching core build first")
        audit = audit_principal_axioms(core, args.lake, receipt)
        print("Principal axiom audit: " + audit["result"], flush=True)
    refresh_verification(catalog, receipt)
    enrich_catalog(catalog, inventory)
    attach_axiom_evidence(catalog)
    catalog.sort(key=lambda x: (not x["mainResult"], x["topic"], x["title"], x["sha256"]))
    write_json(data_dir / "formal-catalog.json", catalog)
    write_json(data_dir / "lean-source-inventory.json", inventory)
    write_docs(inventory, catalog, receipt)
    print(json.dumps({**inventory["summary"], "verifiedRecords": sum(x["status"] == "lean-verified" for x in catalog), "discoveryErrors":len(inventory["errors"])}), flush=True)

if __name__ == "__main__":
    main()
