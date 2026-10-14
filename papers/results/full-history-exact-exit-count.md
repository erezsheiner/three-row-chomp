# Full-history nonpast roots biject with pending diagonal holes

**Statement.** For currently fresh old column c at rowq, H={f(a, c):c<a<q}, G={d(a):c<a<q}, the actual source map Phi:H->G is bijective and satisfies Phi(h)>h for every h. Nonpast(H)=H minus G; |nonpast(H)|=|G minus H|. Directed Phi paths biject original nonpast roots H minus G with pending diagonal holes G minus H.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Private history, increasing source exits and departure resources](../supplements/PRIVATE-HISTORY-AND-RELAY.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- The current value in old column c exceeds the previous diagonal record. H uses the entire strict postbirth private history c<a<q.
- The source map satisfies Phi(h)>h for each input. No order-preserving comparison between different inputs is asserted.

## Argument

1. Current fresh cell cannot be copied, so column has not frozen earlier. All private awards are distinct and outside seeds D_<=c; each original row a has one award. Thus source row map H->(c, q) is bijective, and distinct diagonals yield Phi image G. Since c<a, strict row max gives Phi(h)=d(a)>h.

2. Every past diagonal owner is<=c or in(c, q); the seed part is excluded from H, so exactly H intersect G are past labels. Equal cardinalities give|H minus G|=|G minus H|.

3. For z in G minus H, diagonal injectivity also excludes the seed set, so z is absent from full journal. Since z<=T<current fresh MEX, it must occur before c in rowq. A currently present diagonal label cannot be<=q: values<q are frozen blockers and value q would be a blocker by P07. Thus q<z<=T; distinct exits have unique distinct holders.

4. The finite graph h->Phi(h) has indegree/outdegree<=1 and strictly increases along edges, so acyclic. Roots H minus G and exits G minus H pair exactly along paths. This needs inflationarity only. Max G is outsideH because each h<Phi(h)<=max G, giving a nonempty exit when H nonempty.

5. If visible first-fresh surplus P is defined as actual H-labels held before c, it is disjoint from exits and prefix capacity gives|nonpast H|+|P|<=c. This is conditional on the precise surplus definition and does not assert arbitrary surplus labels are roots.

## Review and supporting evidence

- Historical original-claim verdict: repaired.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/full-history-exact-exit-count.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Private history, increasing source exits and departure resources](../supplements/PRIVATE-HISTORY-AND-RELAY.md)
