# Two exact inversion-source links

**Statement.** H1(a,t) ↔ F(t,a); mortal H2(a,t) ↪ B0(t,σ_a).

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.

## Argument

1. For t<a and d(t)>d(a)=y, y>a>t is nonpast at row t. Coverage and strict row maximum supply one actual interior private y cell. Row injectivity makes its host unique.

2. Conversely each future-diagonal service y=d(a) at row t has a>t and y<d(t), so it determines exactly that inversion. Injective diagonal labels and row indexes make the correspondence bijective.

3. For mortal a, p=σ_a satisfies t<a<p<y<d(t), so coverage also supplies a private p cell at row t. This blocker cannot belong to the L cancellation, because its victim a is not yet an old owner. Hence it is B0.

4. The pair(row t, blocker p) determines the victim a uniquely; distinct mortal inversions thus have distinct target cells. H1 and H2 are distinct copies, not two claims on one positive token. No equality between their different dates is assumed.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/q-inversion-source-links.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)
