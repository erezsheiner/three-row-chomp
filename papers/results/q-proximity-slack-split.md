# Gap-three birth exposure reduces to three nonnegative slack pairs

**Statement.** For a mortal missing-p host h in the gap-three setting p=sigma_a=r+3, r=sigma_h and h<a<a+1<r, E=d(h)+A(h)-(2h+1)>=0 and F=2h-r-A(h)>=0 satisfy d(h)-r=1+E+F. If d(h)<p then (E, F) is(0,0),(1,0)or(0,1).

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Source-time capacity and the precisely scoped tight cases](../supplements/SOURCE-TIME-AND-TIGHTNESS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- Gap-three p=r+3 is essential; the conclusion is an exhaustive remaining-case split, not exclusion.

## Argument

1. Alive-after-h count is h+1-A(h); each live award>h and<=d(h), so d(h)-h>=h+1-A(h), giving E>=0. FFD and victim propagation supply r on every row h,..., r-1, in distinct surviving old hosts<h; there are h-A(h) of them, so F>=0.

2. Adding definitions cancels A and2h, leaving d(h)-r=1+E+F exactly. FFD gives d(h)>r. Since p blocker cannot equal a diagonal and d(h)<p=r+3, d(h)-r is1or2. Integer nonnegative E, F therefore have sum0or1, yielding exactly three pairs.

3. At E0 all live awards fill their available integer interval; old survivors fill[h+1, d(h)-1]. At F0 the r-host injection saturates the survivor roster. These are equality structures only; neither forces a private p booking or excludes gap four.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/q-proximity-slack-split.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Source-time capacity and the precisely scoped tight cases](../supplements/SOURCE-TIME-AND-TIGHTNESS.md)
