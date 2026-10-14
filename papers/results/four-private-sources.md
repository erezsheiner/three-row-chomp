# A fourth private source for an old return after three fresh hosts

**Statement.** If q≤T bounds all earlier diagonals, three current fresh hosts precede an old return x≤T, then an increasing private-source path supplies a fourth distinct source for that same x and x+4≤T.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Private history, increasing source exits and departure resources](../supplements/PRIVATE-HISTORY-AND-RELAY.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- RecurrenceModel with explicit LowCellRowStart hook, paid for gameF by named adapter; source/current ordering and diagonal ceiling. No K2 or NoTriple conclusion.

## Argument

1. The three fresh-host inversions give private x sources; focus on the rightmost fresh hostc2 and its complete postbirth historyH. Because the host is still live atq, every y∈H has source c2<a<q with a<y<d(a)≤T.

2. Startingx∈H, replace each current labely by the diagonal at its actual source row if that diagonal is still inH. This strictly increases positive integer labels bounded byT; it terminates atz=d(b)≤T outsideH with c2<b<q. Source dates need not increase.

3. The endpoint is not in c2’s seeds (its ownerb>c2) or privateH. At the current fresh c2 cell, positive no-skip therefore places z at an actual hosth<c2. The LowCellRowStart hook plus diagonal/death disjointness excludes z≤q, giving q<z.

4. The current x at r lies right of h and below z. Inversion gives a new private x source at h. Its host differs from all three fresh hosts because its current valuez≤T, whereas theirs exceedT.

5. All four x source rows are distinct by row injectivity, and their four diagonals are distinct and lie in(x,T]. Hence x+4≤T. This is a paper proof requiring the explicit actual LowCellRowStart hook, not a claimed kernel certificate or NoTriple exclusion.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/four-private-sources.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Private history, increasing source exits and departure resources](../supplements/PRIVATE-HISTORY-AND-RELAY.md)
