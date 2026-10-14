# A complete chronological signed rank ray

**Statement.** Edges u_k—v_k and v_k—u_{k+1}: opposite signs, degree≤2, total intrinsic endpoint defect 1.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.

## Argument

1. The exact source theorem gameFBlockerCountThrough_strict_square states 2N<(A(N)+3)^2, so blocker count cannot be bounded. Each distinct blocker has a distinct mortal owner; therefore mortal owners are infinite.

2. For each mortal a, a<p<y. At its birth row a the p service exists and is B0, since a is not an old owner. This produces infinitely many distinct negative tokens.

3. The col0 rail follows directly by induction from literal MEX: its private awards are1,…,q, so f(q,0)=q+1. At q=y−1 this serves y after its owner’s death p<y, producing a D token. Distinct diagonal owners yield distinct positive tokens.

4. Every date contains finitely many tokens. Chronological order with deterministic tags therefore enumerates each positive and negative token exactly once. Classification is finite: σ_a<d(a)≤2a+1 resolves old mortal status and d(a)>a resolves value ownership.

5. The edges uk—vk and vk—u(k+1) form one alternating ray. Every vertex has degree2 except u1 of degree1, proving complete coverage and intrinsic defect1. The construction supplies no timing/cut bound.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/q-complete-rank-ray.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)
