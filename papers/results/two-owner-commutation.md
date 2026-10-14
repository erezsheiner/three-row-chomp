# Exact commutation criterion for two MEX insertion factors

**Statement.** For finite journals A, B subset N0, maps P_G(S)=S union{mex(G union S)} commute on every finite contextS iff A symmetric_difference B subset{0,..., c-1}, c=mex(A union B).

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Finite MEX insertion, periodic queues and window graph conventions](../supplements/FINITE-MEX-AND-WINDOW-MODELS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- All finite contexts; equality of carrier maps, not owner memories.

## Argument

1. Put a=mex(A union S), b=mex(B union S). If a<b, adding a cannot change B mex b because a was already B-banned or in S; adding b cannot change A mex a. Thus both orders yield{a, b}. Symmetric argument handles a>b.

2. If a=b=t, t is outside A union B and hence t>=c. If all disagreements are<c, journals agree above t, while all labels belowt were blocked. After first service t, both second MEX values coincide.

3. If a disagreement u exists at/above c, then u>c since c belongs neither journal. Let S={0,..., u}minus{c, u}. Both first MEX values are c; after c the owner allowing u emits u, the other cannot. The two order response sets differ. This also handles c0 and empty journals without special exceptions.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/two-owner-commutation.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Finite MEX insertion, periodic queues and window graph conventions](../supplements/FINITE-MEX-AND-WINDOW-MODELS.md)
