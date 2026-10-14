# Dated matching and one-sided variation imply a square-root discrepancy bound

**Statement.** U(I_N±)=O(N), W_M(n)=O(n), Q(q)−Q(q−1)≤K ⇒ |Q(N)|=O(√N).

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Finite MEX insertion, periodic queues and window graph conventions](../supplements/FINITE-MEX-AND-WINDOW-MODELS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- One fixed matching on all actual residual tokens, with constant endpoint ratio κ.
- O(N) unmatched counts in both √N window directions.
- O(n) matching crossings at every cut.
- A constant upper bound on Q(q)−Q(q−1). These canonical suppliers remain open.

## Argument

1. The degree≤2 completed graph satisfies 2Σ_inside sign=Σ_inside sign(2−degree)+Σ_boundary sign(inside endpoint). An internal opposite-sign edge cancels; each boundary edge contributes its inside sign.

2. Ordered-cycle crossing control gives O(N) cut counts at either end of a√N-window. UnmatchedO(N) and bounded singleton endpoints give O(N) total intrinsic defect. Therefore |Σ_window(Q+2)|≤CN in both orientations.

3. With Q(q)−Q(q−1)≤K, backward values obey Q(N−j)≥Q(N)−Kj; forward values obey Q(N+j)≤Q(N)+Kj. Replacing K by max(K,0) if needed preserves the premise.

4. Summing L=ceil√N terms in the backward and forward windows gives Q(N)≤CN/L+K(L−1)/2−2 and −Q(N)≤CN/L+K(L−1)/2+2. Hence Q=O(√N).

5. Edges jumping across the full window have no inside endpoint, but counting both boundary cuts only enlarges an upper bound. The initial finite exceptions are absorbed into C. Every canonical matching/endpoint/crossing/increment supplier remains a premise.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/q-sqrt-block-consumer.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Finite MEX insertion, periodic queues and window graph conventions](../supplements/FINITE-MEX-AND-WINDOW-MODELS.md)
