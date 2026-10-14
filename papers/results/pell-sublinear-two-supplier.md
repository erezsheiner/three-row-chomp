# Two sublinear suppliers suffice for central discrepancy

**Statement.** μ_n≥−h(n), h=o(n), and b_j/q_j→0 ⇒ D_cen(n)=o(n).

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Ordering error, Pell windows and conditional discrepancy consumers](../supplements/PELL-RECURRENCES.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- The canonical complementary count and reach identities, with the exact central-discrepancy/counting coupling in the attached proof.
- A nonnegative nondecreasing h=o(n) bounds the record drop μ_n from below.
- Uniform Pell-window discrepancy norms satisfy b_j=o(q_j). These two quantitative canonical suppliers remain open.

## Argument

1. From a nonnegative nondecreasing record-drop envelope h, earlier inversions lie in(d(n),M_n], giving B_n≤h(n). Any later owner contributing d(r)<d(n) has r<d(r)<d(n)≤2n+1 and d(r)≥d(n)−h(2n+1); injectivity gives F_n≤h(2n+1). Hence |η_n|≤h(2n+1)=o(n).

2. Uniform Pell-window bound b_j=o(q_j) gives density by elementary tiling, avoiding an external Ostrowski theorem: fix j, tile[0,N] into q_j intervals, and bound |A(N)−βN|/N≤(b_j+|p_j−βq_j|)/q_j+O(q_j/N). First letN→∞, thenj→∞, using p_j/q_j→β.

3. Rank counting gives η=d(n)−A(d(n))−n−1. Expanding J(n)−(2+√2)J(d(n))−√2(1+η) and using(2+√2)(√2−1)=√2 proves I3 directly.

4. Since n<d(n)≤2n+1, J(d(n))=o(n). All three I3 terms are o(n), so D_cen=o(n). No game supplier is proved.

5. The source’s additional subcritical recurrence corollary has its displayed endpoint rate already corrected: at coefficienta=0 with additiveC>0 the rate is O(j), not O(1). Both rates remain o(q_j).

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/pell-sublinear-two-supplier.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ordering error, Pell windows and conditional discrepancy consumers](../supplements/PELL-RECURRENCES.md)
