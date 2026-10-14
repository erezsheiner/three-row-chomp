# Exact multilevel Pell rigidity on every finite frontier

**Statement.** For an exact three-child Pell window recursion with finite globally attained maxima b_j, fixed orientationσ, and a maximizing root at n, the sum of oriented leaf gaps in a complete decomposition to scales k, k-1 equals Lambda_(n, k)=sum_{ell=k}^{n-1}q_(n-ell-1)S_ell. The stated finite frontier/ray corollaries hold with their positive-capacity guards.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Ordering error, Pell windows and conditional discrepancy consumers](../supplements/PELL-RECURRENCES.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- n>k>=1; q_-1=0, q_0=1; W_(j+1)(s)=W_j(s)+W_j(s+q_j)+W_(j-1)(s+2q_j).
- b_j=max_s|W_j(s)|; for integer word discrepancies suprema are attained because range at fixed length finite.
- Ray theorem requires b_(k-1),..., b_n>0and D=sum_{ell=k}^{n-1}S_ell/b_ell<1.

## Argument

1. Define Gσ(m, s)=b_m-σW_m(s)>=0. Sum of child capacities is b_m+S_(m-1), while defects sum W_m; hence G(parent)+S=sum G(children). Each frontier expansion adds exactly its S, proving the general finite frontier identity by induction.

2. Complete silver-tree internal-node counts are q_(n-ell-1) at slack scale ell; check base n=k+1:(2leaves k,1leaf k-1,1internal). The 2,1 recursion propagates these and the leaf counts q_(n-k), q_(n-k-1). A maximizing aligned root has G0, proving the formula.

3. Every descendant subtree leaf set is a subset of the fixed root leaf set; nonnegativity gives G(v)+Lambda_(m, k)<=Lambda_(n, k). This is scoped to that tree. G=shortfall+2opposite-sign mass yields both unsigned identities; absolute-value telescope cancels internal defects.

4. Pell product bounds q_a q_c<=q_(a+c+1), proved by induction in the positive 2,1 recursion, yield Lambda<=D*C_(n, k), where the zero-slack capacity C=q_(n-k)b_k+q_(n-k-1)b_(k-1). Thus b_n=C-Lambda>=(1-D)C.

5. Normalized child gaps capacity-average to(g_parent+alpha)/(1+alpha), alpha=S_(m-1)/b_m. Choose a child with minimum ratio. Its1-g is at least(1-g_parent)/(1+alpha). D<1givesb_(ell+1)>b_ell and alpha_ell<=S_ell/b_ell. Products or1-product<=sum give every selected gap<=D and positive aligned defect.

6. For integer b, S with summable capped slack, eventually delta<1. Either b stays0, or once positive it stays positive and increases, and tail relative-slack sums tend0; this yields arbitrarily long finite near-rigid rays. No infinite ray in the original word follows: starts may drift. Counterframe/scalar stress claims are not premises for the identity or finite-ray theorem.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/pell-multilevel-rigidity.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ordering error, Pell windows and conditional discrepancy consumers](../supplements/PELL-RECURRENCES.md)
