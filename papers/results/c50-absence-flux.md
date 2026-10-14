# Exact one-row absence flux for any root class

**Statement.** Abs_C(q+1)−Abs_C(q)=F⁺_C(q)−F⁻_C(q)+E_C(q)−Out_C(q).

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Block ghost identities, composed density and the C50 lineage ledger](../supplements/BLOCK-GHOSTS-AND-C50.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.
- A fixed class C of orbit roots and the source’s exact pending/hosted/above/absent and flux definitions.
- Hosted⊆Pending is a proved canonical membership lemma, distinct from open direct-Q transport A1. No asymptotic flux or matching bound is assumed or proved.

## Argument

1. By definition Pend_(q+1)=(Pend_q\{x:d(x)=q})∪{q}, because d(x)>x and integer thresholds change by1.

2. For owners remaining in both pending sets, split change of absence into not-absent→absent (F+) and absent→not-absent (F−). Hosted and above cases are disjoint by diagonal maximum and injectivity.

3. The entrantq contributes E_C exactly when root(q)∈C and d(q) is absent on rowq+1.

4. An exit with d(x)=q is absent at rowq: a diagonal label cannot occur in the prefix at its numerical deadline, and q<d(q). Its class is root(x)=root(q), so its contribution is−Out_C.

5. Summing gives ΔAbs_C=F+−F−+E−Out. The direct inventory identity does not need a separate Hosted⊆Pending premise. That membership follows from the canonical frozen-blocker partition: an old hosted diagonal below q would be a frozen blocker, contradicting diagonal/blocker disjointness. Hence the C50 lineage reconciliation is also supplied. Sublinear flux bounds remain unproved; the distinct direct-Q transport A1 is not supplied by this lemma.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/c50-absence-flux.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Block ghost identities, composed density and the C50 lineage ledger](../supplements/BLOCK-GHOSTS-AND-C50.md)
