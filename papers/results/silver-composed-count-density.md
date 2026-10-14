# Sublinear composed blocker-count defect is equivalent to silver blocker density

**Statement.** E_AA(N)=A(A(N))+2A(N)−N=o(N) ⇔ A(x)/x→√2−1.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Block ghost identities, composed density and the C50 lineage ledger](../supplements/BLOCK-GHOSTS-AND-C50.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.
- Canonical injectivity and reach give an upper count bound; the independently supplied quantitative count floor gives liminf A(x)/x≥1/3.
- The conclusion concerns blocker value-set density. A bridge to the ordered diagonal slope is not part of this entry.

## Argument

1. If A(x)/x→β=√2−1, then A(N)→∞ and A(A(N))=β A(N)+o(N)=β²N+o(N). Sinceβ²+2β−1=0, E_AA=o(N).

2. Conversely E_AA=o(N) and lower boundliminfA(N)/N≥1/3 imply A(N)→∞. Setx_N=A(N)/N; division byA(N) gives x_(A(N))=1/x_N−2+o(1).

3. The compact cluster setC lies in[1/3,1/2], the upper bound following from distinct d(i)≤2i+1. For eachc∈C, subsequence convergence and A(N)→∞ give G(c)=1/c−2∈C.

4. Thus eachc∈C isH(y)=1/(y+2) for somey∈C, so C⊆H(C). On y≥0, H has Lipschitz constant≤1/4. Diameter(C)≤diameter(C)/4 forces a singleton.

5. Its unique value satisfiesc=1/c−2, so c=√2−1. This is blocker value-set density only; ordering discrepancyε remains unpaid. No inference to d(n)/n is made.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/silver-composed-count-density.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Block ghost identities, composed density and the C50 lineage ledger](../supplements/BLOCK-GHOSTS-AND-C50.md)
