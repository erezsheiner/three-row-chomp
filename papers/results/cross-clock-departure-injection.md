# Cross-clock injection into original departure events

**Statement.** Distinct original roots with certified same-transition absent-root relays inject into their endpoint old payload and original endpoint column, across all clocks in one fixed history. Every arising endpoint payload y satisfies y>=3; its charged-root count is at most the number of relay-eligible departure columns, hence at most y-2. For an arbitrary nonnegative payload y, the bound is max(0,y-2), with no arising endpoints when y<3.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Private history, increasing source exits and departure resources](../supplements/PRIVATE-HISTORY-AND-RELAY.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- One fixed full history; distinct original roots with exact absent-root guards and certified rising relay endpoints. Does not prove relay existence or capacity one.
- Every relay starts at a strict old-core host b<q-2, so q>=3; its finite exact leftward path ends at a rising column c<=q-3. Endpoint old payload y>=q>=3. Root absence is in the new retained prefix, and all row/source domains are as defined in the public relay supplement.

## Argument

1. A departing value v cannot return to the same column: choose a first return, COPY would retain a different previous value, while MEX forbids the earlier v already in that column’s full history.

2. At one clock, exact leftward relay maps have indegree/outdegree≤1 by old/new row injectivity. Two paths meeting would imply one root lies on the other path, but the earlier path then emits that root’s old value in the new retained prefix, contradicting root absence. Distinct absent roots therefore have distinct rise endpoints.

3. Charge an original root to(endpoint old value y, endpoint column c). Equal-clock equality contradicts distinct endpoints. If clocksq1<q2 share the same key, the rise atq1 is a departure of y, forbidding y at rowq2−1 by no-return.

4. A rise cannot be COPY, so its old value y>=q. The strict old-core starting host b<q-2 requires q>=3, and a leftward relay ends at 0<=c<=q-3<=y-3. Thus every arising endpoint payload has y>=3, and there are at most y-2 eligible columns for that payload. For arbitrary y>=0 use max(0,y-2); no endpoint with y<3 can arise. This is the restricted departure-resource count, not a bound on all value departures.

5. Different histories require a source identifier in the key. Actual relay existence, exact absence guards and earlier replacement absence are not proved by this accounting. The optional min(y−2,r) refinement needs the separate row-start-owner theorem; it is not part of the headline injection.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- Renewed clarification: With no endpoints, the unguarded expression at y=1 could read 0<=-1. Arising endpoints have y>=q>=3; the nonnegative totalized bound retains exactly the proved resource count.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/cross-clock-departure-injection.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Private history, increasing source exits and departure resources](../supplements/PRIVATE-HISTORY-AND-RELAY.md)
