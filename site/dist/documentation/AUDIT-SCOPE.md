# Audit scope

This release covers an explicitly selected set: **265 Lean modules and 59 corrected paper-result entries**. The admission decision applies to the exact statements, hypotheses and file hashes recorded for this edition. It is not a certification of every historical or experimental file in the research workspaces.

## Formal evidence

The renewed 2026-10-14 review started from the exact delivered archive, then staged a separate corrected candidate. All 265 modules in that candidate passed a new clean strict build. Its complete serialized and elaborated declaration census, recursive axiom inspection, exact declaration-identity comparison and five fresh Lean kernel replays also passed. All 21,064 serialized declaration identities are accounted for, including private/generated auxiliaries; their types, values and declaration-specific fields are structurally identical to the preserved full-pass base objects. The fresh exports bind the current source hashes and line locations.

Private and generated declarations are compiler entities, not a count of independent mathematical achievements. Finite `#eval` output is not theorem evidence. The fresh census observed only Lean's standard `propext`, `Classical.choice` and `Quot.sound`. It found no `sorryAx`, custom axiom, native trust axiom, unsafe project declaration or logical dependency on the 25 generated partial runtime helpers. Fresh negative controls verified that the checks reject `sorry` and an unapproved custom-axiom dependency.

The renewed semantic review required **16 comment replacements in 12 modules**, covering missing hypotheses, proposed-law scope, historical proof status and unsupported human-review provenance. Independent comparison confirms that all replacements are present in the candidate and no text outside block comments changed. The complete fresh formal audit was performed on this corrected candidate, rather than inferred from the comment-only nature of the changes.

The retained **2026-10-13** evidence has its own chronology: a full base build, census and kernel replay, followed by targeted strict recompilation of **45 modules** after documentation amendments. All **2,109 compared serialized declaration identities** in that earlier amendment were unchanged. That earlier amendment was not a second full replay. The old receipts remain historical evidence and are not relabeled as the renewed run.

The [current formal review](../audit/prepublication/formal/FINAL-REVIEW.json) and [renewed semantic ledger](../audit/prepublication/lean-semantics/SEMANTIC-REVIEW.json) record these separate checks. The sources pin `leanprover/lean4:v4.29.1`. From `lean/core/`, the portable build and replay commands used for the source set are:

```text
lake build ResearchCore ChompLean
lake env leanchecker --fresh --verbose ResearchCore
lake env leanchecker --fresh --verbose SJSDiagonalDictionary
lake env leanchecker --fresh --verbose ClaudeFutureFreezeDiagonal
lake env leanchecker --fresh --verbose R14FrontierLaw
lake env leanchecker --fresh --verbose R15ParkedValueSwap
```

These commands rebuild and replay proofs. They do not, by themselves, regenerate the complete audit census or independently repeat the English-to-formal correspondence review. Kernel replay uses Lean's kernel, not a second proof assistant.

## Mathematical correspondence

The renewed model-assisted review accounts for all **265 advertised Lean module records**, with individual reasoning and reviewer attribution. It compares public statements, module summaries and mathematical source prose with actual definitions and theorem interfaces, including assumptions, quantifiers, domains, endpoints and conclusion strength. All displayed elaborated types and hypotheses were also compared exactly with their catalogue and export. The actual-game foundation was independently reread, including legal moves, poison convention, positive rectangle domain, the P-position encoding and noncircular discharge of the recurrence-model fields.

Inventory descriptions do not acquire an extra mathematical interpretation merely from their filenames. A Lean proof of `P → Q` verifies that implication. If `P` is an open supplier, the audit does not silently turn the theorem into an unconditional proof of `Q`. Source definitions of proposed conditions are likewise not proofs of those conditions.

This is model-assisted mathematical correspondence review, not external human peer review or an independent handwritten reconstruction of every generated Lean proof body. Exact formal statements and the kernel evidence remain the authority for what the Lean declarations assert. The new review records its findings against the original archive separately from their corrections in this candidate.

## Paper proofs and finite certificates

The paper subset consists of **56 accepted entries and 3 repaired entries**. Acceptance is always for the corrected statement with its displayed hypotheses. Conditional implications are included with their suppliers exposed. Counterexample results concern the precisely specified abstract inference or model; they do not refute canonical Chomp merely by refuting that abstraction.

The renewed independent paper review reconstructs the arguments and dependencies rather than relying on earlier “accepted” or “banked” labels. Complete English derivations supply definitions, limiting arguments and finite-certificate interpretations where the earlier edition had only review summaries. Their source hashes and second-review receipts must be bound in the final release evidence. These paper derivations are not thereby Lean formalizations of their conclusions.

Finite certificates use a separate evidence layer. The checked data establish the stated bases and finite obligations. All-index conclusions additionally require the reviewed induction or finite-reduction argument. Replaying a certificate alone is not an independent proof of every surrounding mathematical claim. The release's portable certificate instructions identify the inputs and scope of each replay.

## Selection and exclusions

The earlier full audit accounted for all 62 original paper entries: 56 accepted, 3 repaired, 2 open as stated and 1 unresolved. This release includes the first 59 and excludes the other 3 from its public result records. The [release notes](../RELEASE-NOTES.md) identify the excluded entries and the unresolved ten-unit diagonal premise.

The original full-collection audit remains on **HOLD**, outside this release. Its adverse dispositions have not been changed to manufacture a pass. A separate release decision admits only this selected subset, while every conditional result retains its assumptions.

The release is bound by:

- `PUBLICATION-STATUS.json`: this edition's release status.
- `audit/release/REVIEW.json`: the scoped admission decision and evidence.
- `audit/release/INPUTS.json`: the reviewed input hashes.
- `audit/release/RELEASE-FILES.json`: the explicit release-file allowlist.

Changes to a statement, hypothesis, proof or included file require an appropriate new review and updated bindings. Successful website validation is not mathematical approval.

The audit does not establish novelty or priority against the entire literature. It also does not certify unselected archives, future research, an efficient algorithm from an abstract interface, or conclusions stronger than the displayed formal or paper statements.
