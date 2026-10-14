# Every postdeath diagonal service has an earlier same-host blocker source

**Statement.** D-service at (t,h), σ_a≤t<d(a), injects into a private σ_a-service at (u,h) with u<σ_a.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.

## Argument

1. For mortal a put p=σ_a,y=d(a), with a<p<y. A postdeath private y service at(t,h), p≤t<y, has h<a by seed exclusion; its continuing host remains live at row p.

2. At row p the unique p cell is the victim a, strictly right of h. Thus f(p,h)>p: it is recomputed and cannot equal the victim label.

3. Positive MEX then requires p in h’s earlier journal. Because p is a blocker it is not an inherited diagonal seed; its source is a genuine private service(u,h), u<p.

4. Two y services have different hosts by column nonreuse; two extracted p services therefore have different cells. Source uniqueness follows from private nonreuse. The case t=p is allowed. This does not assert the source is a free B0 cell.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/q-postdeath-source.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)
