# A degree-two source multigraph preserves mortal service provenance

**Statement.** The residual dated tokens admit the described recurrence-native opposite-sign multigraph of maximum degree2. Each contracted mortal edge has endpoint-row ratio<4; every H1/F edge has ratio<2. Immortal J/H2 and some other endpoints remain explicit.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- Token multiplicity is retained; two H copies are distinct vertices.
- Virtual E positives and their same-row p negatives are contracted as paired vertices; spliced walks retained as witnesses.

## Argument

1. An inversion t<a, d(t)>d(a) gives the unique future-diagonal cell in rowt by coverage, bijecting H1(a, t) and F(t, a). For mortal a, p=sigma_a satisfies t<a<p<d(a)<d(t), so the same row supplies unique blocker p; since a is unborn it is B0. Equality of target row and death label recovers(t, a), giving H2 injection.

2. For each mortal owner, same-host p/y matching S has degree<=1 on each side by private nonreuse; same-row T joins E to p and H2 to its prebirth source p. Their row ranges exclude a and are disjoint, so T is also a matching. Different owners use different blocker labels.

3. The union has degree<=2 including parallel edges. Contracting an E/p T-pair splices two external endpoints of opposite sign; one external edge leaves an endpoint; no external edges delete the pair/cycle. No degree can increase above2. Same-row opposite signs cancel with zero signed row charge.

4. A p service at u has p<d(u)<=2u+1 and a<p<=2a+1, hence a/2<u<=2a. Remaining H2 dates equal a and D dates satisfy a<=v<=2a. Thus any splice endpoint ratio<4, independent of walk length. For H1/F, d(t)>d(a)>a and integrality/reach give2t>a, hence a/t<2. There is no zero-date endpoint with these inequalities.

5. The construction alone says nothing about how many isolates occur or how many edges cross a cut. In particular D vertices can become isolated after contraction; their original source does not give an automatic surviving edge.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/q-source-multigraph.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)
