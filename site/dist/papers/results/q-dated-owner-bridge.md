# One fixed dated owner matching gives an exact interval ledger

**Statement.** Σ_{q∈[l,r]}(Q(q)+2)=U₊([l,r])−U₋([l,r])+X(l−1)−X(r).

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.

## Argument

1. Retain H1/F and mortal H2/R source pairs. Their negative source rows t precede the positive owner row a. Their token types are disjoint and all sources have capacity1.

2. For each mortal owner remove the T paired R tokens. Choose the earliest m=min(|D|,|R|−T) D services and latest m remaining R services. All R dates<p≤all D dates; pairing selected lists preserves capacity and forward time. Unmatched D and R counts are the positive/negative parts of χ=T+|D|−|R|.

3. Partition actual p-booker hosts by their unique y service: prebirth X, living E−C, postdeath D, or never-y W. Thus |P|=X+(E−C)+D+W and R=|P|−E, proving D−R=C−X−W and χ=C+T−X−W.

4. On any finite interval each forward matched edge contributes−1 if its negative date is inside and+1 if its positive date is inside. This equals its crossing indicator at the left cut minus that at the right cut. Local finiteness permits summation; unmatched signs give U+−U−.

5. Therefore Σ(Q+2)=U+−U−+X(l−1)−X(r). The inversion components are Inv+Inv_m; remaining selected D/R crossings add X_DR. Before p the latest R selection minimizes crossings, after p the earliest D selection does; the bijection itself does not change these cut counts. This is not a bound on that minimum.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/q-dated-owner-bridge.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)
