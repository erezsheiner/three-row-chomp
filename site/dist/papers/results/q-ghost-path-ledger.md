# Exact signed ledger of the current ghost paths

**Statement.** Q(q)=X_L+X_D+2H_q−Z−1.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.

## Argument

1. A currently served old diagonal cannot be a frozen blocker, so its physical host is live after the row. Seed exclusion gives host<owner. One emitted value and row/diagonal injectivity give outdegree and indegree at most 1. Strictly increasing indexes exclude cycles.

2. An e-edge path has e+1 live vertices if its terminal is live and e otherwise: every nonterminal is an actual current service host. Its contribution to 2I−m is e−1 in the first case and e in the second. Each isolated live vertex contributes−1.

3. Summing path contributions gives 2I−m=X_L+X_D−Z, including current column q among the isolates. The exact overlap equation d+I+H=2q+1 and live count m=q+1−A(q) imply Q=2I+2H−m−1.

4. Substitution proves Q=X_L+X_D+2H−Z−1. At q=0, Z=1 and Q=−2, so the initial constant is consistent. The proof makes no bound on long paths, dead endpoints or Z.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/q-ghost-path-ledger.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)
