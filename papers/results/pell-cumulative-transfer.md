# Divergent cumulative relative Pell slack gives sublinear scale defects

**Statement.** Let q_-1=0, q_0=1, q_(j+1)=2q_j+q_(j-1), b_j>=0, S_j=2b_j+b_(j-1)-b_(j+1)>=0. If sum_j min(2, S_j/max(1, b_j)) diverges, then b_j/q_j->0. More generally the same conclusion holds if b_(j+1)<=(2-delta_j)b_j+b_(j-1)+C, 0<=delta_j<=2, C>=0and sum delta_j diverges.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Ordering error, Pell windows and conditional discrepancy consumers](../supplements/PELL-RECURRENCES.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- The displayed nonnegative Pell defect recurrence holds after a finite initial segment, and any additive constant C is fixed.
- The sum of capped relative slacks diverges. It can be indexed from j=1; changing a finite prefix has no effect.
- In the window application, b_j is the supremum over all starting positions. The required canonical slack supply is not proved here.

## Argument

1. Letρ=1+sqrt2, x_j=b_j/ρ^j, e_j=C/ρ^(j+1), M_j=max(x_j, x_(j-1)). Normalized coefficients sum1-delta_j/ρ. Hence x_(j+1)<=(1-delta_j/ρ)M_j+e_j.

2. At next step discard its nonnegative saving. Substitute previous bound to get x_(j+2)<=(1-2delta_j/ρ²)M_j+(2/ρ)e_j+e_(j+1). Since2/ρ<1, both entries of M_(j+2) obey(1-c delta_j)M_j+g_j with c=min(1/ρ,2/ρ²), g=e_j+e_(j+1). 0<=c delta_j<1 and sum g finite.

3. At least one parity has sum delta infinite. On that parity the product of contraction factors tends0 by log(1-u)<=-u. Every fixed prefix of error contributions vanishes under future products; remaining tail is bounded by sum tail g. Thus M tends0 along that parity; its adjacent entries cover every x_j, so full sequence x->0. Pell q_j is comparable toρ^j.

4. For capped relative slack delta=min(2, S/max(1, b)), delta*b<=S even for b=0or0<b<1, so recurrence holds with C0. No saving is assumed canonical.

5. Optional J(N)=o(N) bridge can be proved without an Ostrowski supplier: tile[0, N] by fixed q_j windows and one remainder. Then limsup_N |J(N)|/N<=(b_j+|p_j-beta q_j|)/q_j; let j grow. This requires exact Pell approximants and bounded unit word increments, explicit in the window application.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/pell-cumulative-transfer.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ordering error, Pell windows and conditional discrepancy consumers](../supplements/PELL-RECURRENCES.md)
