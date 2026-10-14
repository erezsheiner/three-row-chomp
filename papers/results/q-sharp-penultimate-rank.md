# At a row-sharp birth, the penultimate blocker has an exact rank bound

**Statement.** For h≥3, E(h)=0 and r=d(h)−1 imply A(v(h))≥r−h and A(r)−A(v(h))≤H(h).

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Source-time capacity and the precisely scoped tight cases](../supplements/SOURCE-TIME-AND-TIGHTNESS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.
- h≥3 is required.

## Argument

1. Row-sharp follows by counting distinct after-row live values>h: d(h)≥2h+1−A(h). Its lower envelope increases by1 or2 at each step. Equality E(h)=0 therefore forces every later diagonal strictly above d(h)=r+1.

2. The h−A(h)=r−h old after-row survivors have distinct values in[h+1,r], so they fill that interval. The penultimate y lies there for h≥3 and is not a prior diagonal by the penultimate core lemma. No future owner has value≤r, so y is a blocker.

3. Each of the r−y higher survivor awards occurs before the last-old y source, forcing y into a distinct older private journal; row injectivity supplies distinct prior service rows with d(t)>y.

4. All diagonal values≤y have owners<h. Hence the available prior source count is h−R(y)=h−y+A(y), giving A(y)≥r−h.

5. Because r is below current diagonal, R(r)=h−H(h); therefore A(r)=r−h+H(h), and A(r)−A(y)≤H(h). To conclude y=r one needs both H(h)=0 and r blocker. The general two rank inequalities do not need r to be a blocker.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/q-sharp-penultimate-rank.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Source-time capacity and the precisely scoped tight cases](../supplements/SOURCE-TIME-AND-TIGHTNESS.md)
