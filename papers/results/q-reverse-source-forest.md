# A reverse-source forest injects C events into forward or missing hosts

**Statement.** For every mortal owner a there is a source-defined injection C_a to F_a disjoint-union W_a, whose terminal physical host is strictly left of the starting C host. It avoids the p-service at row p-1 and host0. For any integer b<=a, |{C hosts<=b}|+|{reverse hosts<=b}|<=|{P hosts<b}|.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- p=sigma_a, y=d(a), P actual predeath p hosts. Reverse hosts have v_y<u_p; forward hosts have u_p<v_y; W has no y service.

## Argument

1. At a C or reverse y cell, p<y is absent from that host journal: C never books p, reverse books it only later. MEX puts p strictly left in the same row. That source is an actual predeath private p cell because the current row< p.

2. All domain y cells occupy distinct rows; row injectivity forbids two y cells in one row, and private nonreuse forbids duplicating one host service. Distinct target p cells also have distinct hosts by p nonreuse. Thus the first-source map from C union reverse hosts toP is injective and strictly decreases host.

3. Each reverse P vertex has one outgoing edge, and every P vertex indegree<=1. C starts are outside P. Finite strictly decreasing host chains cannot cycle or merge from distinct C starts; they terminate at P outside reverse, hence forward or W. A continuation through a reverse target also strictly decreases y source time since its y precedes its current p service.

4. C starts satisfy t<sigma_h<p, hence t<=p-2. Later steps only decrease source time, so terminal p service is before p-1; rail0 serves p exactly at p-1 and is excluded. The host-prefix inequality follows by restricting the first-source injection, not by assuming terminal F is compensation.

5. A forward terminal can be a D service after owner death. Therefore this injection does not prove C maps to X/W, A1, or |C|<=|X|+|W|.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/q-reverse-source-forest.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)
