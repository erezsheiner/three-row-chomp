# A reversed minimum common source requires smaller private extras

**Statement.** Let x0 be the minimum label in the rightmost fresh host's postbirth history. If an earlier fresh host has not received x0 before its rightmost-host source row a*, it receives a distinct smaller private extra y with a*<y<x0 at that row. Several late hosts require distinct extras.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Private history, increasing source exits and departure resources](../supplements/PRIVATE-HISTORY-AND-RELAY.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY table, record row, nonempty saturated right-tail history. Does not rule out extras.

## Argument

1. The rightmost fresh host’s postbirth historyH equals its current right tail: packing injects each distinct tail value into an equally sized set of private source rows, so the injection is bijective. Every earlier fresh host’s historyH_i containsH and has |H_i\H|=c_*−c_i.

2. Letx0=minH and let a* be its unique source row atc*. It has no inherited seed at an earlier fresh host, since its current tail occurrence is right of all those hosts; seed exclusion forbids earlier ownership.

3. For a host that has not previously receivedx0, x0 is absent from its journal at a*. It is also absent from its current left prefix because the row’s unique x0 lies later atc*. MEX therefore returns at mostx0, and row injectivity makes it strictly smaller.

4. That host remains live throughq, so its source output exceedsa* (equality would freeze it). The source row a*>c*>c_i is postbirth, hence its output belongs toH_i, and minimality ofx0 excludes membership inH.

5. Several late hosts produce distinct smaller extras in the same row. An extra can be legitimate; no contradiction or NoTriple conclusion follows. The signed source permutation has total displacement0; positive displacement needs backward compensation, but this is accounting, not a prohibition.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/minimum-common-private-extra.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Private history, increasing source exits and departure resources](../supplements/PRIVATE-HISTORY-AND-RELAY.md)
