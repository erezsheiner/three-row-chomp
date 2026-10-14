# Full Lean prepublication audit

**Passed for the exact 265-module reviewed source set:** 264 baseline modules plus the separately promoted future-freeze dependency. All 21,064 serialized declaration identities are covered, including 19,991 theorem declarations and 20,028 proposition-valued declarations. Generated auxiliaries are included; these counts are not numbers of independent mathematical theorems.

The final sources were freshly built with warnings treated as errors (only three stylistic linters disabled). An intentionally invalid sorry control was rejected. Every declaration was obtained from Lean’s elaborated environment, matched to serialized object-file identities, and recursively checked for axiom dependencies. The only observed axioms are propext, Classical.choice and Quot.sound. No sorryAx, custom/native trust axiom, unsafe project declaration, proof dependency on a generated partial runtime helper, or free/metavariable type was found. All imported proofs were replayed in a fresh Lean kernel environment. The complete census also retains 25 compiler-generated partial runtime recursion helpers; their only references in project declaration types and values are their own self-calls, never logical proof dependencies.

The census required isolated R14/R15 imports to recover four generated equation declarations whose origin is coalesced in the combined environment. No declaration was dropped to make the completeness check pass. Full types, source modules and final SHA256 hashes are in declarations.jsonl; compact per-module types are in modules/.

The semantic review covers all 13 principal baseline catalogue entries plus the promoted dependency and all 251 remaining inventory-only summaries. Actual-game uniqueness has an independent semantic review. Explicit hypotheses remain visible for sparse-failure, finite Fekete, lag-eight and EAA statements. EndToEndInvariantAssembly is an abstract conditional interface, with no concrete game instantiation or complexity conclusion. The SJS all-row dictionary assertion was false as documentation: its source now states the actual local lemma scope. Both documentation corrections preserve every noncomment code token, and the revised files passed the final fresh build and replay.

This gate does not authorize publication or discharge unresolved paper claims. In particular no general SJS implementation bridge, stronger diagonal +10 bound, analytic Fekete limit, or concrete logarithmic-time algorithm is inferred from these Lean results.

Reproduce: run run_final_audit.py in a newly named empty snapshot if rebuilding, then run finalize_audit.py. Existing evidence is intentionally not silently overwritten by a fresh snapshot launch. The final gate binds the source manifest, logs, ledger, semantic reviews and full census.

## Reproduction and platform scope

The saved Python audit harness currently selects the Windows Lean 4.29.1 executable under the launching user’s .elan toolchains directory. It is a Windows harness, not a claim of a platform-independent audit command. For a fresh full rerun, preserve the existing audit evidence elsewhere and use an empty build-final directory at the expected path; run run_final_audit.py followed by finalize_audit.py. If instead changing the snapshot name, update the matching build-final paths in finalize_audit.py as well as SNAP in run_final_audit.py. The harness intentionally refuses to overwrite an existing snapshot. The initial negative controls are supplied separately by run_full_audit.py and test_custom_axiom_detector.py. The final manifest pins the exact lean-toolchain and Lake configuration hashes; toolchain-binding.json records the observed binary version and hashes.

For a portable build/replay check, install the toolchain from lean/core/lean-toolchain, enter lean/core, then run:

```sh
lake build ResearchCore ChompLean
lake env leanchecker --fresh --verbose ResearchCore
lake env leanchecker --fresh --verbose SJSDiagonalDictionary
lake env leanchecker --fresh --verbose ClaudeFutureFreezeDiagonal
lake env leanchecker --fresh --verbose R14FrontierLaw
lake env leanchecker --fresh --verbose R15ParkedValueSwap
```

These portable commands rebuild and replay the proofs. They do not independently regenerate the full declaration census or semantic-review ledger. The complete census rerun is performed by the documented snapshot harness, whose generated Lean inspection files and manifests are retained. The public package itself sets warningAsError=true and disables only linter.unnecessarySimpa, linter.unusedSimpArgs and linter.unusedVariables.
