# Higher cells before the penultimate column inject into earlier service rows

**Statement.** For every q>=3, y=f(q, q-1), the higher earlier cells inject into source rows t<q with d(t)>y, hence #{c<q-1:f(q, c)>y}<=#{t<q:d(t)>y}.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Source-time capacity and the precisely scoped tight cases](../supplements/SOURCE-TIME-AND-TIGHTNESS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- q>=3 ensures y>=q+1; actual full journal, not a truncated history.

## Argument

1. A higher current cell is recomputed since its value>y>=q+1. The unique current y is later atq-1, so y is absent from the cell left prefix and MEX forces y in its journal.

2. P10 says y is not a past diagonal; it does not assert that y is a diagonal label. This excludes both inherited seeds and the source column birth diagonal. There is an actual private y award at a strict old column on some earlier row t<q. Row injectivity makes these t distinct between columns; strict row maximality gives d(t)>y.

3. This injection has capacity one and no record/tightness/density assumption. The finite q>=3 guard is retained rather than derived by an unproved penultimate live-floor extension.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/q-terminal-service-capacity.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Source-time capacity and the precisely scoped tight cases](../supplements/SOURCE-TIME-AND-TIGHTNESS.md)
