# Every nonrecord high suffix row needs a distinct later actual death

**Statement.** In the canonical E(h)=F(h)=0 missing-booker context with r=sigma_h, for every integer 0<=u<h, #{t:u<=t<h, d(t)>r}<=A(h)-A(u).

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Source-time capacity and the precisely scoped tight cases](../supplements/SOURCE-TIME-AND-TIGHTNESS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- E0 gives d(h)=r+1; F0 requires every older survivor after h to privately book r on[h, r).
- Deaths are counted by their actual blocker rows, including death h and excluding death u.

## Argument

1. Because r is a blocker, P11 supplies it in each prebirth row with d(t)>r, and maximality excludes it on the other rows. Its prebirth service hosts c_t are distinct and strictly old c_t<t, since r cannot be a diagonal.

2. No such host survives after h: F0 makes all survivors book r again on[h, r), contradicting private nonreuse. Each has death b_t<=h; the prebirth service value r>t cannot be a death cell, so t<b_t. Victim uniqueness makes b_t distinct.

3. For t>=u, the target death lies in(u, h], whose blocker count is A(h)-A(u). This proves every suffix inequality and the total bound H<=A(h). It does not show that a strict suffix deficit exists.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/q-tight-suffix-death-injection.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Source-time capacity and the precisely scoped tight cases](../supplements/SOURCE-TIME-AND-TIGHTNESS.md)
