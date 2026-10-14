# Tight births have an exact diagonal/blocker predecessor dichotomy

**Statement.** h diagonal ⇒ d(h−1)=r−1, E(h−1)=0; h blocker ⇒ d(h−1)≥r+2, E(h−1)≥2.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Source-time capacity and the precisely scoped tight cases](../supplements/SOURCE-TIME-AND-TIGHTNESS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.
- Mortal owner a with death p and a missing-booker host h<a; r=σ_h satisfies a+1<r<p, and h≥3.
- Tight slacks E(h)=d(h)+A(h)−(2h+1)=0 and F(h)=2h−r−A(h)=0. No predecessor F(h−1)=0 or predecessor missing-booker membership is supplied.

## Argument

1. Under E=F=0 and r=σ_h, prebirth r-service rows are exactly t<h with d(t)>r. Their source hosts cannot be in U because F0 requires a new r service from every U host. Nonreuse thus forces their distinct actual deaths into(t,h].

2. This gives for each u<h the suffix injection #{t∈[u,h):d(t)>r}≤A(h)−A(u). It uses actual deaths, not guessed deadlines.

3. If numeric h is diagonal, A(h)=A(h−1), so the u=h−1 bound excludes d(h−1)>r. Row-sharp gives d(h−1)≥r−1, while r is a blocker; equality follows and E(h−1)=0.

4. If numeric h is a blocker, row-sharp gives d(h−1)≥r. It cannot equal blocker r or repeat current diagonal r+1, hence≥r+2. The row h−1 r booker must die after h−1 and by h, so it is the actual victim c=s(h). Thus f(h−1,c)=r and f(h,c)=h.

5. Substituting A(h−1)=A(h)−1 yields E(h−1)=d(h−1)−r≥2. Neither branch proves F(h−1)=0 or predecessor M membership.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/q-tight-predecessor-dichotomy.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Source-time capacity and the precisely scoped tight cases](../supplements/SOURCE-TIME-AND-TIGHTNESS.md)
