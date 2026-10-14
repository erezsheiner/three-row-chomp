# Many earlier diagonal barriers share one current ghost capacity

**Statement.** #{b<q:q≤d(b)<d(q), A(d(q))−A(d(b))>H(b)+2(q−b)−1}≤2q+1−d(q)−H(q).

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.

## Argument

1. For owner b<q, M=d(b), q≤M<d(q), the hosts<h=b having M in their start-q journal are exactly its H(b) prebirth services plus G_b(q) postbirth services. Birth occurs only at b, inherited seed membership at h<b is impossible, and private nonreuse makes all such hosts distinct.

2. If M is absent now, each blocker M<x<d(q) has a genuine recomputed current cell by coverage and x>q. At a host<h=b, MEX forces M into its journal because M is absent from the full current prefix.

3. These lower hosts have capacity H+G; hosts b,…,q−1 add at most q−b. Birth column q is diagonal. Absence therefore implies A(d(q))−A(M)≤H(b)+G_b(q)+q−b.

4. Contraposition forces every violating owner’s distinct diagonal into an actual current ghost cell. Row injectivity bounds their number by I(q)=2q+1−d(q)−H(q).

5. Finally G_b(q)≤q−b−1 gives MB3. The guard M≥q is essential to rule out frozen blocker cells; the theorem does not certify joint history/placement feasibility.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/q-multi-owner-barrier.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)
