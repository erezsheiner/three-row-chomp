# Two-owner MEX response has an exact carrier normal form

**Statement.** For arbitrary finite A, B, S subset N0, u=mex(A union S), v=mex(B union S union{u}). With I=A intersect B and E(x, y)=[x notin A, y not inB]or[x in A minus B, y notin A], sorted outputs x<y satisfy x=mex(S union I), y=min{t>x:t notinS, E(x, t)}. Equality of E is exactly equality of carrier response in all finite contexts.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Finite MEX insertion, periodic queues and window graph conventions](../supplements/FINITE-MEX-AND-WINDOW-MODELS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Zero-based MEX; finite journal/context sets; outputs distinct.

## Argument

1. Every label below x is either in S or banned by both owners. If x notin A, first owner takes x; the second takes first later label outside B union S. If x in A, then x notin B and first owner takes first later label outside A union S; second take x. These are exactly the two clauses of E.

2. Finite bans ensure existence of y. The description is also lexicographically first edge outsideS. Therefore equal E implies equal responses.

3. Conversely if E and E prime differ at(x, y), choose S={0,..., y}minus{x, y}. The pair accepting the edge emits exactly{x, y}; the other cannot emit this pair by the already proved normal form. Thus responses differ. E recovers I because x notin I iff E(x, z) for all sufficiently large z, so no additional hidden coordinate is needed.

4. This concerns current carrier response only. It does not claim private journal updates agree or canonical state compression.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/two-owner-response-content.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Finite MEX insertion, periodic queues and window graph conventions](../supplements/FINITE-MEX-AND-WINDOW-MODELS.md)
