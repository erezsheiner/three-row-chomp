# Private ancestry packing across any number of fresh hosts

**Statement.** An old-value return x to the right of j fresh hosts has j distinct earlier private source rows, whose distinct diagonals lie in (x,T]. Therefore j≤T−x. Fresh hosts occur in increasing value order but need not be a physical suffix.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Private history, increasing source exits and departure resources](../supplements/PRIVATE-HISTORY-AND-RELAY.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical table, P02/P03/P05/P14/P16 and exact journal identity. No K2 or NoTriple assumption.

## Argument

1. At a record row, earlier fresh outputs exceedT≥q. For a later returning valuex≤T, MEX inversion placesx in each earlier fresh host’s journal.

2. It is not an inherited seed: a diagonal owner left of a fresh host is also left of the current return host and seed exclusion forbids that current occurrence. A source at the fresh host’s birth is likewise forbidden by seed exclusion.

3. Thus every one ofj fresh hosts supplies a private source row c<a_c<q with valuex. Its source diagonal is strictly above x by row maximality and injectivity.

4. Two hosts cannot share a source row, or that row would repeatx. Their diagonal values are also distinct, all lying in(x,T], so j≤#{a<q:d(a)>x}≤T−x.

5. Fresh hosts themselves are in increasing value order: a later smaller fresh output would have to be in an earlier journal, contradicting journal ceilingT. This does not make the hosts a physical suffix, and the returning cell need not be live.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/private-ancestry-arbitrary-packing.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Private history, increasing source exits and departure resources](../supplements/PRIVATE-HISTORY-AND-RELAY.md)
