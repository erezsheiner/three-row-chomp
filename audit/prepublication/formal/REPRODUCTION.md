# Reproducing the final formal checks

The receipt `FINAL-REVIEW.json` describes the execution that actually occurred on Windows using Lean 4.29.1. Its original logs and command paths are retained as provenance. The supplied portable wrapper is a separate convenience script; it was syntax checked and its baseline reconstruction was checked for all 265 source hashes, but the whole wrapper was not itself rerun after the recorded audit.

Install Python 3 and the Lean version named by `lean/core/lean-toolchain` through elan, then run:

```text
python audit/prepublication/formal/reproduce_formal.py --repository . --output /new/empty/audit-directory --compare-inherited
```

The output directory must not exist. On Windows, use an absolute Windows output path. The wrapper copies only the 265 admitted sources and three configuration files into an isolated core, verifies their exact hashes, and starts without any project build cache. It builds both research libraries with the strict pinned configuration, runs the complete elaborated and serialized censuses, examines the isolated R14/R15 equation origins, replays all five necessary roots with Lean's fresh kernel checker, reconciles every serialized declaration, and runs negative controls for holes and custom axioms. The installed Lean standard library is part of the pinned toolchain; project objects are freshly produced.

The optional `--compare-inherited` step additionally reconstructs the preserved baseline source bytes, builds that baseline in a second clean directory, and compares all declaration types, proof values, binder annotations and declaration-specific fields. Reconstruction reverses the 16 documented final comment changes and overlays the 45 source snapshots preserved with the earlier amendment. Each reconstructed source must match the immutable baseline manifest before it is built. Omitting this option still performs the complete fresh current-source kernel/axiom audit, but the reproduction receipt explicitly reports that inherited structural identity was not rerun.

The all-declaration census includes private and generated declarations. The only allowed logical axioms are `propext`, `Classical.choice` and `Quot.sound`. Generated partial runtime helper definitions are checked separately: they are not proofs, and no logical declaration may depend on them. The complete gzip census is lossless; per-module JSON files expose readable types and current source ranges. Declaration counts are not counts of independent mathematical results.

`source-manifest.json` pins the final proof sources and configuration independently of the final repository ZIP. The final packaging check must verify that every corresponding archive member has that hash. The historical archive and prior audit remain historical evidence; neither their old source line numbers nor the interrupted fresh census of the earlier archive substitutes for the current-source audit.

Successful checking certifies the exact Lean propositions and their hypotheses. The separate source-prose and paper reviews determine whether the English claims match those propositions. This procedure does not publish any files.
