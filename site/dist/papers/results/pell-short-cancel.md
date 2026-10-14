# Pell slack splits exactly into magnitude shortfall and signed cancellation

**Statement.** S_j=min_s(Short_j(s)+Cancel_j(s)); at a selected maximizing parent window, S_j=Short_j+Cancel_j.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Ordering error, Pell windows and conditional discrepancy consumers](../supplements/PELL-RECURRENCES.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Pell three-child window decomposition and finite-window maximizing starts; Short and Cancel are nonnegative and use the selected parent sign.
- The equality for one selected window requires that it maximizes the parent norm; no positive-slack supplier is assumed.

## Argument

1. For one exact child triple x,y,z, magnitude shortfall is2b_j+b_(j−1)−|x|−|y|−|z|≥0.

2. Writing P as positive mass and M as negative absolute mass gives cancellation P+M−|P−M|=2min(P,M)≥0.

3. Adding gives Short+Cancel=2b_j+b_(j−1)−|W_(j+1)(s)|. Bounded integer window defects attain their maxima, so minimizing over starts gives S_j=2b_j+b_(j−1)−b_(j+1).

4. The identity S=Short+Cancel applies at a parent maximizer (or after taking minimum), not indiscriminately at every start. S=0 requires all child norms saturated and no nonzero opposite-sign child.

5. For δ=min(2,S/max(1,b)), δb≤S even at b=0, so the cumulative-transfer premise follows ifΣδ diverges. Divergence itself is not proved by the identity.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/pell-short-cancel.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ordering error, Pell windows and conditional discrepancy consumers](../supplements/PELL-RECURRENCES.md)
