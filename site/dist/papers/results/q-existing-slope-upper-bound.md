# If a diagonal slope exists, it is below 1.868565865679

**Statement.** For the canonical table, if d(n)/n→c, then c≤c_*<1.868565865679, where c_* is the unique root in [9/5,15/8] of 7c⁷−25c⁶+22c⁵+25c⁴−58c³+11c²+27c−9.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Independent completion of the existing-slope upper bound](../../audit/full/paper-b/SLOPE-REPAIR.md)
- [Exact algebra checks](../../audit/full/paper-b/exact-algebra-checks.json)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.
- Existence of the ordered diagonal slope d(n)/n→c. The proof supplies all service, union-exclusion, rank-area and logarithmic-population inequalities used by this conditional consumer.
- See the full independently reconstructed SLOPE-REPAIR.md; no convergence, Q=o(n), or count-uniform-integrability conclusion is asserted.

## Argument

1. Existence d(n)/n→c and reach give c≤2, R(x)=x/c+o(x), A(x)=(1−1/c)x+o(x), and uniform errors on bounded multiples. P98 is rederived by excluding victims dying before the first p-service row from its j distinct bookers; P99 adds reach-forbidden victims with p_i+s_i<p_j. Both exclusion classes lie below s_j and are disjoint from bookers.

2. With v_j=s_j/j, L=1+1/c, r_j=j/c+o(j) and m_i=i(1+bv_i)+o(i), the full union yields s_j≥j+r_j+#{i>r_j:m_i<j}. Weighted summation over j gives liminf(logJ)^−1Σ(v_i−L−φ(v_i))/i≥0. The sufficient j interval is (1+bv_i+ξ)i<j<i/(1/c+ξ); omitted proportional tails and integer boundaries have Oξ(1) weight.

3. For φ=[1/(1+bv)−1/c]+, H(v)=1/v+k(v−L−φ) is convex on[L,c] and[c,2]. Chord coefficient k equalizes outer endpoint values; the kink is smaller by(2−c)(k−1/(2c))≥0. Thus reciprocal-victim mean≤C, and actual victim census gives log-average Imm(h)/h≥V=1−C. V−1/(c+1)>0 because c²−c−1>0; V<1/2 because2c²−1>0.

4. MEX diagonal-rank counting bounds each live journal ceiling, giving cK_h≥B N−(c−1)h−Imm(h), while direct journal exclusions give K_h≥N/c−b h−Imm(h). Integrating the maximum at a fixed immortal host has exact coefficient Ψ=B²/[c(c−1+u)]+bz²/u. The line crossing is N=u h/z and is after birth/positivity thresholds. Summing hosts and Stieltjes integration gives the concave integrand g=uΨ, with bounded endpoint primitive.

5. The chord of g on[u0,1/2] at meanV yields U10. Independent polynomial expansion gives[-9,27,11,−58,25,22,−25,7]. Exact Bernstein positivity of its derivative on[9/5,15/8] and a90-step rational bracket prove the unique root c_*<1.868565865679.

6. The source’s vague prior upper-endpoint exclusion is replaced by a self-contained repair: the rank-integrated two-line MEX inequality M8 has positive surplus159327/60696000 at15/8. Its derivative is positive throughout[15/8,2), using |(1/(cD))′|<15/64 and positive derivative of(c−1)^3(c²−3)^2/(c³D). At c=2, a positive fraction of immortal hosts demandsΩ(N²) diagonal cells while row capacity is o(N²). Thus no c≥15/8 occurs; c<9/5 trivially satisfies the final bound.

## Review and supporting evidence

- Historical original-claim verdict: repaired.
- The complete repaired paper argument was independently reconstructed and second-reviewed. No matching Lean certificate for this derived bound was identified.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/q-existing-slope-upper-bound.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Detailed audit proof or correction](../../audit/full/paper-b/SLOPE-REPAIR.md)
- [Detailed audit proof or correction](../../audit/full/paper-b/exact-algebra-checks.json)
- [Detailed audit proof or correction](../../audit/full/paper-a/SLOPE-SECOND-REVIEW.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Independent completion of the existing-slope upper bound](../../audit/full/paper-b/SLOPE-REPAIR.md)
- [Full proof and definitions: Exact algebra checks](../../audit/full/paper-b/exact-algebra-checks.json)
