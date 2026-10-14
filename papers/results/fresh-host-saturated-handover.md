# Saturated private-history handover and a jump of at least 2k

**Statement.** For record rowq>=1 with k=d(q)-T(q)-1>=1, let c*<q be rightmost old fresh host. Then {f(a, c*):c*<a<q}={f(q, r):c*<r<q}, both sets with q-c*-1 distinct labels, each<=T-k. If c*<=q-2, f(q, c*)-f(q-1, c*)>=2k.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Private history, increasing source exits and departure resources](../supplements/PRIVATE-HISTORY-AND-RELAY.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- Full canonical journals; fresh means value>T(q).
- C19 age>=17 corollary is separately conditional and not part of unconditional statement.

## Argument

1. Fresh labels T+1,..., d-1 all occur by P11 and cannot belong to old journals. Two fresh hosts in physical order cannot decline: MEX would place the later fresh value in the earlier journal<=T. Thus c* holds T+k and all strict right tail cells are<=T.

2. For any tail valuex and any fresh hostc<r, MEX forces x into that journal. It cannot be a seed d(i), i<c, or own birth d(c), because current column r>c cannot emit any earlier diagonal. Therefore x was privately served at some c<a<q with d(a)>x.

3. Different fresh hosts for fixed x have distinct source rows by row injectivity. Therefore k<=#{a<q:d(a)>x}<=T-x, giving x<=T-k.

4. At fixed c*, the distinct q-c*-1 tail values map into the equally many postbirth rows(c*, q). They cannot share one source row because one cell has one value. Thus bijection onto all rows and all postbirth values distinct; no historical row is omitted. Birth row excluded essentially.

5. If previous postbirth row exists, its value<=T-k while current is T+k, giving jump>=2k. If c*=q-1, history and tail are empty and jump corollary is inapplicable. Nothing bounds positive column jumps or proves NoTriple.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/fresh-host-saturated-handover.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Private history, increasing source exits and departure resources](../supplements/PRIVATE-HISTORY-AND-RELAY.md)
