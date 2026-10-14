# The reverse forest cannot terminate at the final blocker source

**Statement.** Every reverse-forest terminal has blocker source date ≤p−2; host 0 is not a terminal.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.

## Argument

1. A C event has a<t<σ_h<p, so its y row is at most p−2. At that recomputed y cell the smaller blocker p must occur in the strict left prefix because it is absent from the C host’s journal.

2. At a reverse host the unique y service precedes the unique p service. Traversing to its same-row left p source strictly reduces the physical host, and the next reverse y row is strictly earlier than the preceding p row.

3. Distinct y source rows give distinct same-row p cells; private p nonreuse then gives distinct p hosts. Thus no two C paths merge, and every finite descending path ends at a forward or W host.

4. Every terminal’s p row remains≤p−2. Col0’s unique private p service is at p−1 by the independently derived rail, so it cannot be a terminal.

5. The host-prefix Hall consequence counts each initial C/B domain host through its distinct strictly lower source. It allows unpaid forward D endpoints and does not prove A1. Unrestricted E-host descent is not used.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/q-last-source-exclusion.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)
