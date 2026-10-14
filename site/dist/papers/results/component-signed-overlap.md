# Component-local signed overlap identity

**Statement.** For old/new injective rows a, b on the same finite column set U, edges c->d when b_c=a_d form paths/cycles. For path root old label x and exit new label z, overlap with fixed O changes by1_O(z)-1_O(x); cycles contribute0. If every new label is below old D and every positive label below D lies in O union A, then all path exits owned and |B intersect O|-|A intersect O|=|(A minus B)minus O|.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Private history, increasing source exits and departure resources](../supplements/PRIVATE-HISTORY-AND-RELAY.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Identical retained domain U={0,..., q-2}, q>=2.
- Drop corollary uses positivity, strict new diagonal maximum<old D and old diagonal MEX cover.

## Argument

1. Injectivity bounds in/outdegrees by1. A root with indegree0 cannot enter a cycle: the first cycle entry would have an external predecessor besides its cycle predecessor. Distinct root paths cannot merge by the same indegree bound. Finite components are paths or cycles.

2. On path c0->...->ck, b_ci=a_c(i+1) for i<k. Internal old/new labels cancel as sets; exactly x=a_c0 is lost and z=b_ck gained. Cycle label sets coincide. This does not require monotonic labels along edges.

3. Every exit belongs B minus A globally: otherwise it would have an outgoing edge. Under drop z<D and positive, old MEX coverage forces z in O. Root labels are exactly A minus B; thus owned roots contribute0 and unowned roots1. Sum components for global formula.

4. The old penultimate p belongs A but is notin the project strict old source; actual LowLoss excludes p and D-1and requires absence/nonpast guards. The identity cannot replace all those guards or bound eligible paths by1.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/component-signed-overlap.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Private history, increasing source exits and departure resources](../supplements/PRIVATE-HISTORY-AND-RELAY.md)
