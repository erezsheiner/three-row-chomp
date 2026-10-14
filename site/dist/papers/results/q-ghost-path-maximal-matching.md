# Optimal blocker matching on one ghost path

**Statement.** A ghost path with e edges and k available blocker vertices has maximum matching size min(e,k).

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.

## Argument

1. A path v0→…→ve has e candidate ghost edges, and k available endpoint vertices. Capacity one on edges and vertices bounds every matching by min(e,k).

2. If all e+1 vertices are available, assign each edge to its target, obtaining e matches.

3. Otherwise choose a nonavailable vj. Assign every available vi with i<j to edge i and every available vi with i>j to edge i−1. On either side edge indexes are distinct, and the two sets are disjoint, so all k available vertices are saturated.

4. There are e+1−k nonavailable vertices, hence unmatched edge count max(0,e−k)=max(0,r−1). An available non-source vertex is exactly a surviving mortal echo owner, since q<σ_a<d(a)<d(q) gives its actual blocker service.

5. Owner-only matching already uses every available target. The source gains one additional match precisely when it is available and some target is unavailable. This proves μ=L+T and the stated U,V,Q formulas, without any asymptotic assertion.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/q-ghost-path-maximal-matching.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)
