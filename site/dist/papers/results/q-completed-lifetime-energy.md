# Completed lifetimes give a weak quadratic negative-energy bound

**Statement.** For M_N=sum_{a=0}^N(a-A(a)), C_N=sum_{p blocker, p<=2N} min(A(p)-1,(min(N, p-1)-s(p))_+), M_N<=sum_{q=0}^{2N}I_q+sum_{a=0}^NH_a+C_N. Consequently limsup C_N/N^2<=23/144, liminf sum_{q<=N}(I_q+H_q)/N^2>=13/576, and limsup sum_{q<=N}(-Q(q))_+/N^2<=179/576.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- Canonical recurrence and positive blocker convention.
- P98 victim bound; A(x)<=floor(x/2); A(x)>=x/3-O(1); 2d(q)>=3q+5 for q>=16.

## Argument

1. Fix a and y=d(a). Older hosts alive after a split into: unique private y service before a; unique service a<t<y; or no service and death a<p<y. A survivor at row y cannot omit y from its journal: no row-y cell may equal the diagonal label y, a live old cell is>y, and positive MEX forces historical y. It cannot be an inherited seed when c<a. Birth/death endpoint equalities are excluded by injectivity and D/S disjointness.

2. Prebirth y source rows have d(t)>y and are distinct for different hosts, so count<=H_a. Postbirth services for a<=N occur at t<d(a)<=2a+1, hence t<=2N, and inject into actual I_t cells.

3. Unserved deaths inject into pairs(p, a) with s(p)<a<p<d(a). One cap is (min(N, p-1)-s(p))_+. The other is A(p)-1: exactly A(p) predeath rows serve p, while s(p) is one such row by FFD and is excluded by a>s(p). Thus the finite inequality keeps completion horizon 2N.

4. Write p_j for blocker rank j. P98 and count bounds give 2j<=p_j<=3j+o(j) and s_j>=j+p_j/6-o(p_j). Maximize min(j,(min(N, p)-j-p/6)_+) over p in[2j,3j]. The cap is j through 5N/12, 5N/6-j through N/2, N-4j/3 through 3N/4, then0. Integrals are25/288,9/288,12/288 times N^2, summing23/144. Uniform o(N) errors over O(N) ranks give o(N^2), with a finite initial segment harmless.

5. A<=q/2 gives M_N>=N(N+1)/4. Enlarge the H sum to 2N, replace N by floor(X/2), and obtain13X^2/576-o(X^2). Put K=I+H. The lower diagonal bound gives K<=q/2-3/2<=m+1 eventually. Therefore(m+1-2K)_+<=m+1-K. Sum and use A>=q/3-o(q): coefficient1/3-13/576=179/576.

6. The quadratic coefficient is not a subquadratic estimate, does not meet a smaller consumer threshold, and does not prove a density improvement. No finite lifetime panel is used as an asymptotic premise.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/q-completed-lifetime-energy.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)
