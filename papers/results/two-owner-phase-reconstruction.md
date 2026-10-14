# Response content plus one label and one bit reconstructs the ordered journals

**Statement.** The exact response relation E_AB, r=min(A∖B) (r=∞ when A∖B is empty), and β=1[mex(A)∈B] determine the ordered finite journals (A,B).

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Finite MEX insertion, periodic queues and window graph conventions](../supplements/FINITE-MEX-AND-WINDOW-MODELS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Arbitrary ordered finite subsets A,B of ℕ, ordinary mex on ℕ including zero, and the exact response relation E_AB defined by the two-owner protocol.

## Argument

1. The response relation E determines I=A∩B because x∉I iff E(x,z) holds for all sufficiently large z (both finite journals eventually omit z).

2. If r=min(A∖B) is infinite, A=I. Otherwise below r, A membership equals I; r∈A, and for x>r the first clause of E(r,x) is false while the second says x∉A. This reconstructs all A.

3. Put a=mex(A). Below a every label is in A, so B membership equals I membership. At a the missing bit is preciselyβ=1[a∈B]. For x>a, E(a,x) reduces to x∉B because a∉A. This reconstructs all B.

4. The two-owner response normal form itself follows by examining the smallest label allowed by at least one owner outsideS. Whichever owner can take it does so, and the other takes the first admissible larger label. This proves the E relation used above.

5. For alphabet0..M−1 the phase choices give at most 2(M+1) pairs. AtM≥2 the unrestricted-response class has A=empty or one singleton and B=empty or{mexA}, all allowed and distinct, attaining the bound. The label and bit are each independently necessary. No storage compression of the potentially quadratic E table is inferred.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/two-owner-phase-reconstruction.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Finite MEX insertion, periodic queues and window graph conventions](../supplements/FINITE-MEX-AND-WINDOW-MODELS.md)
