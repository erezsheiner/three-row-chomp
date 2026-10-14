# Release notes — 14 October 2026

This edition selects the reviewed results that can be presented with their exact proved scope. It contains 265 Lean modules and 59 paper-result entries: 56 accepted and 3 repaired.

## Renewed prepublication review

This edition supersedes the 13 October delivery. That archive compiled successfully, but several paper pages omitted definitions or full derivations retained only in historical drafts. The corrected edition includes complete public supplements, linked from each affected result, and explicit distinctions between theorem truth, proof completeness, formal verification and finite computation.

The renewed source correspondence review identified sixteen comment corrections in twelve Lean modules. They restore omitted range conditions, distinguish proposed laws from proved implications, date historical roadmaps and remove unsupported human-review provenance. No definition, theorem or proof token was changed. The corrected source set receives its own fresh build, declaration/axiom audit and kernel replay; the final receipts are in `audit/prepublication/formal/`.

The cross-clock endpoint bound now explicitly states the arising-payload domain `y >= 3`; for an arbitrary positive label its count bound is `max(0, y-2)`. The injection argument is unchanged. This clarification prevents the vacuous `y=1` case from being written as `0 <= -1`.

The website renders formulas locally and links the full proof supplements. The review is model-assisted, with separate agents examining the formal, semantic and paper layers. It does not claim human peer review.

## What the edition includes

The formal source set includes the actual-game uniqueness development and the previously omitted future-freeze dependency. Every selected Lean module is bound to the audited source manifest. The English paper edition presents reviewed statements and derivations, with explicit hypotheses for conditional results.

Three paper entries use substantive corrected statements or completed proof arguments:

- **Death-swap identity:** the unrestricted identity includes the immediate-death term, `K = |S| − |M| + 1[p = a+1]`. This identity alone does not prove `K ≥ 0`.
- **Full-history source map:** the proved map is injective and satisfies `Φ(h) > h`. No order-preserving property is claimed.
- **Existing-slope upper bound:** the reviewed derivation includes the union supplier and the exclusion of the large-slope range. Its conclusion still assumes that the diagonal slope converges; it does not prove convergence.

The strict unconditional improvement to the earlier liminf endpoint retains its liminf scope. Its proof uses valid one-sided monotonicity estimates for the step counting function. The microscopic improvement of `10^-50` is not a limsup bound or a numerical convergence claim.

## Documentation corrections

The explanatory text now exposes conditional hypotheses, correct interval endpoints and non-strict bounds. Unsupported claims of strict logical separation or symmetric independence have been removed. A certified loss edge is not called the first loss unless minimality is actually part of the statement. Historical finite observations remain identified as finite observations.

The SJS dictionary module establishes local and initial-state facts, not a complete all-row implementation/game correspondence. The end-to-end assembly is a conditional interface, not a concrete fast Chomp algorithm or a logarithmic complexity theorem. Finite block inequalities are not presented as an analytic limit theorem.

## Deliberate exclusions

The following three entries are absent from the public result catalogue:

| Original ID | Disposition | Reason for exclusion |
| --- | --- | --- |
| `q-a1-open` | Open as stated | The canonical terminal-service conclusion has not been proved; the reviewed injection does not close it. |
| `q-sublinear-open` | Open as stated | The requested sublinear conclusion remains an open obligation. |
| `q-victim-gate-small-class` | Unresolved; original unconditional claim withheld | The all-index `m ≤ 5` argument needs the unproved premise `d(i) + 10 ≤ 2i` for every `i ≥ 37`. A finite check does not prove that premise. |

The unconditional `m ≤ 1` observation, the checked finite base and the implication under the extra ten-unit premise do not establish the excluded unconditional `m ≤ 5` claim. The original adverse findings remain in the separate full-collection audit; selection does not erase them.

Historical source-only inventories, unadmitted supplemental snapshots, superseded publication packages and unrelated documents are also outside this release's file allowlist. Old drafts are not promoted to accepted result entries merely because a later proof cites the same topic.

The original full collection remains on HOLD. This edition has a separate, source-bound release review. No remote publication is performed by preparing it.
