# Signed cumulative balance plus downward blocker-clock regularity implies Q=o(n)

**Statement.** For an injective positive-integer sequence d(n) satisfying n<d(n)<=2n+1, with A complementary count and Q(n)=3n+A(n)-2d(n), signed prefix balance sum_{n<N}Q(n)=o(N^2) and lim_{K->infinity}limsup_N N^-1 sum_{n<=N}(u_n-K)_+=0, u_n=(A(d(n-1))-A(d(n)))_+, imply Q(n)=o(n).

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Count-clock implication and its abstract boundary](../supplements/COUNT-CLOCK-AND-ABSTRACT-BOUNDARY.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- d is an injective positive-integer sequence with n<d(n)<=2n+1. A counts the complement of its entire range and is linearly interpolated at real arguments.
- Signed prefix balance SB and downward-count-clock uniform integrability CU are assumptions; neither is proved here for the canonical table.
- Define u_n for n>=1; the CU sum uses 1<=n<=N. No limiting density is assumed.

## Argument

1. Let g=(3n+A(n))/2 and E=A(d(n))-A(g(n)). Since A is increasing1-Lipschitz and1.5<=Delta g<=2, E(n-1)-E(n)<=K+2+(u_n-K)_+. For a positive E spike eta N choose fixed K with tail through 2N<=eta N/4 and fixed window delta N with(K+2)delta<=eta/4. E remains>=eta N/2 forward, hence Q<=-eta N throughout. Negative E spikes persist backward with Q>=eta N. Either contradicts SB because proportional-window sums are differences of o(N^2) prefixes. Thus E=o(n), uniformly in prefix maxima through C N.

2. Complementarity gives M_N=sum_{q<N}(q-A(q))=sum_{i<N}(N-d(i))_+ and sum_{i<N}d(i)=N^2-M_N+Dhead. Algebra yields sum_{n<N}(Q(n)+2)=M_N-2Dhead. There are A(N-1)+1 emitted values>=N, each<=2N-1, so Dhead<=N(A(N)+1). Also M_N>=N(N-1)/2-NA(N). Therefore A(N)>=N/6-5/6-S2(N)/(3N), and SB implies liminf A(N)/N>=1/6.

3. Along any scaling subsequence, one-Lipschitz a_N(x)=A(Nx)/N has a locally uniform limit a by compactness/diagonal extraction; a(x)>=x/6. If it has a nontrivial plateau, its maximal level set[l, r] has0<l<r<infinity. For smallε, the interior label interval contains(r-l-2ε)N+o(N) distinct diagonal labels.

4. Their distinct owners i<rN have uniform E(i)=o(N), forcing g(i)/N in(l-ε, r+ε), since a(l-ε) and a(r+ε) lie strictly below/above the plateau. But g increments>=3/2 permit at most(2/3)(r-l+2ε)N+1 owners. Takingε<(r-l)/20 contradicts cardinality. Thus every scaling limit a is strictly increasing.

5. A Q spike gives separated subsequential limits z=d(N)/N and w=g(N)/N. Clock tracking and local uniform convergence imply a(z)=a(w); strict increase forces z=w, contradicting the spike. No density, monotonicity, absolute-energy or canonical service hypothesis entered this argument.

6. Checked endpoints: d(0)=1 follows from reach; all d-values<=x have owners<x; A(0)=0; forward/backward windows stay nonnegative for delta<1/2. The compactness proof does not assume uniqueness of scaling limits.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/q-count-clock-consumer.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Count-clock implication and its abstract boundary](../supplements/COUNT-CLOCK-AND-ABSTRACT-BOUNDARY.md)
