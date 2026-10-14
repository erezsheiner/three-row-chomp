# The rank-ray crossing count identifies its exact quantitative gap

**Statement.** For chronological positive tokens u_1, u_2,... and negative tokens v_1, v_2,... with ray edges u_k-v_k and v_k-u_(k+1), cut width equals |p_n-m_n|+|m_n-max(p_n-1,0)|. For canonical residual tokens p_n-m_n=sum_{q<=n}(Q(q)+2).

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- Both token types infinite; finitely many tokens per date; fixed tie-breaking tags.
- In canonical application, infinitely many blockers and rail0 provide infinite negative/positive populations.

## Argument

1. The first edge family crosses exactly when k lies in the symmetric difference of initial segments[1, p_n] and[1, m_n], so contributes|p_n-m_n|. In the second family u_(k+1) is before the cut iff k<=p_n-1, while v_k is iff k<=m_n. Its symmetric difference gives the second term, including p_n=0.

2. At p_n>=1 the second absolute value differs from the first by1 in magnitude; therefore W differs from2|p_n-m_n| by exactly1. O(n) cut width is equivalent to an O(n) signed-prefix estimate for this ray, which remains open.

3. Each mortal owner a yields B0 at birth because sigma_a<d(a), and yields a postdeath D token at y-1 on rail0 because a<sigma_a<y. Distinct owners give distinct death labels and diagonal labels. The established positive blocker count tends to infinity, so both lists are infinite. Source row q tokens can be classified using deaths through 2a+1 and owners below the numeric labels, but decidability is not a quantitative cut estimate.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/q-rank-ray-cut.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)
