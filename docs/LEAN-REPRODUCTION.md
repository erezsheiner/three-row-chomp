# Lean release evidence and reproduction

The release contains exactly 265 admitted Lean source modules, pinned to Lean 4.29.1. Their exact bytes and the three Lake/toolchain configuration files are bound in `audit/release/LEAN-FILES.json`. Audit tooling and inert `.lean.txt` historical/negative-control fixtures are separate from the admitted source set. Do not copy `.lake`, object files, supplemental candidates, or giant raw census files.

The retained historical certificate covers 21,064 serialized declaration identities, including generated/private auxiliaries. These are not counts of independent mathematical results. Its only observed logical axioms were `propext`, `Classical.choice`, and `Quot.sound`; it admitted no `sorryAx`, custom/native trust axiom, or logical dependency on a generated partial runtime helper.

This edition adds a renewed **2026-10-14** audit of the delivered archive and a separate corrected candidate. After 16 comment replacements in 12 modules, all 265 modules passed a new clean strict build, exhaustive census, recursive axiom/dependency check, full serialized-declaration comparison and five fresh kernel replays. Independent review also confirms each replacement and unchanged noncomment source text. The fresh census accounts for all 21,064 declaration identities, with none missing or unaccounted for, and confirms the standard-axiom boundary above. No logical declaration depends on the 25 generated partial runtime helpers. Fresh negative controls passed.

The older **2026-10-13** evidence is retained separately: a complete strict base build, exhaustive census and five fresh replays, followed by strict recompilation of 45 modules after 54 documentation corrections and one finite-replay clarification. All 2,109 affected declaration types, values and declaration-specific fields were structurally identical. That older targeted amendment was not a second complete replay. Historical gates and receipts remain unchanged rather than being renamed as current results.

The [current formal review](../audit/prepublication/formal/FINAL-REVIEW.json) binds the renewed run. The [renewed correspondence review](../audit/prepublication/lean-semantics/SEMANTIC-REVIEW.json) and [comment-amendment review](../audit/prepublication/lean-semantics/FINAL-COMMENT-AMENDMENT-REVIEW.json) record the distinct mathematical-scope and documentation checks.

The current `audit/release/LEAN-FILES.json` uses the `lean-release-files-v2` schema: it binds exactly the 265 current modules and three Lake/toolchain files from the fresh source manifest, and references the new formal evidence. It does not inventory the older documentation archives. The preserved `audit/release/LEAN-FILES-2026-10-13.json` retains the earlier inventory and its `referenceAliases`, `compressedReferenceAliases` and `historicalInventoryResolutions`, including the inert pre-amendment source texts and compressed historical censuses. Historical receipts are not rewritten to change their original paths or claims.

The complete public-file inventory is `audit/release/INPUTS.json` together with `audit/release/RELEASE-FILES.json`. The historical `BINDINGS.json` describes a larger local audit and is not the release inventory. Fresh per-module JSON exports provide current source hashes, line locations, exact types and axiom dependencies for the public type browser. These exports and the retained historical evidence are unnecessary for the ordinary build and kernel-replay commands below.

From a clean release checkout, after installing the pinned toolchain, run in `lean/core`:

```sh
lake build ResearchCore ChompLean
lake env leanchecker --fresh --verbose ResearchCore
lake env leanchecker --fresh --verbose SJSDiagonalDictionary
lake env leanchecker --fresh --verbose ClaudeFutureFreezeDiagonal
lake env leanchecker --fresh --verbose R14FrontierLaw
lake env leanchecker --fresh --verbose R15ParkedValueSwap
```

The configuration already treats warnings as errors and disables only three style linters. The separate R14/R15 replays cover generated declarations whose module origins coalesce in the combined environment. `leanchecker --fresh` uses a fresh environment in the Lean kernel; it is not a different proof assistant. These portable commands provide a new build/replay of the released sources. They do not rerun the model-assisted correspondence review or regenerate the full declaration census.

The saved Python census/amendment harnesses are historical Windows tooling, with snapshot-relative paths and a Windows toolchain executable path. Preserve them for provenance; do not advertise them as portable turnkey commands. A complete new census can be generated with the included Lean inspectors in an isolated snapshot, with their manifest/output paths and R14/R15 origin inspections configured as documented in the full audit report. Never overwrite the original certificate or relabel the original receipts as results of that new run.

This Lean evidence does not certify unresolved manuscript claims, the proposed all-row SJS implementation bridge, or a concrete fast game algorithm from the abstract end-to-end interface. The parent release process chooses the separately approved paper set; this manifest does not change the original package's HOLD status or publish anything.
