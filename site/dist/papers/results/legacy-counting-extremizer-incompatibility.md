# Quantitative incompatibility of two counting extremizers

**Statement.** For the canonical table, liminf A(n)/n≤b_new, the unique root in [0.469,0.471] of 12496+112497b−24984b²−524992b³−237524b⁴+249993b⁵+87520b⁶−100006b⁷+25000b⁸=0; consequently liminf d(n)/n≤1/(1−b_new)<1.886593095.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [The finite counting service budget and baseline bound](../supplements/counting-service-budget.md)
- [Quantitative incompatibility of the two counting extremizers](../supplements/counting-extremizer-proof.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.
- The actual prebooker/victim and completed-diagonal service inventories are independently reconstructed in the audit. Exact coefficient positivity and root isolation were independently checked.
- For each fixed a<liminf A(n)/n, take N→∞ before a approaches that liminf. No convergence or limsup ceiling is asserted.

## Argument

1. The actual booker/victim facts give distinct s_j, s_j≤2j−1 and s_j≥j+#{i:p_i+s_i<p_j}. Under global A≥a x−C, put e_j=j−a p_j+C. The baseline ranks i≤floor((j−e_j)/h) are strictly reach-excluded because a(p_i+s_i)≤h i+C−a<j+C−e_j. Thus δ_j=e_j−2g j+h s_j+h≥0; every additional excluded rank adds h.

2. For selected retired indexesI belowm, summingδ and exact rank gaps gives X=S_N−B_ret=Σ_Iδ+2gΓ+Σ_notI e_j+hm/2−aK≥0, with the last term≥m/2. Missing ranks below b m cost at least K−b m inΓ; no victim order is assumed.

3. For the latest selected rankJ≥K, e_J≥2gJ−hm and e_J−e_j≤(1−a)(J−j). On v=u/m in[.332,.336], the resulting ramp starts after .58m. Its integral givesB_peak, while target e_j in[.56m,.58m] is disjoint from ramp support. Thus Y=S_N−B_peak≥that separate target mass.

4. Good source/target counts use distinct rank omissions and Markov bounds: G_s≥(.01m−2−21X/m)+ and G_t≥(.02m−2−4.1X/m−100Y/m)+. Exact source-time and baseline inequalities show every good source is an extra reach exclusion for every good target. Hence X≥h G_sG_t; the product lower bound and h0=.969*2 imply X+Y≥m²/5000−.06m.

5. The prior finite service budget is independently reconstructed from distinct completed diagonal demands and high journal labels: full lower excess area remains after canceling distinct E(N+r) samples; the exact square identity retains the endpoint E(N−1)^2/(2a). This yields U_N≥m u−aW−u²/2+S_N/a−E_endpoint²/(2a)−O(N).

6. Optimizing over unrestricted real first momentz is a valid lower relaxation. The old quadratic J_a has its vertex in(.332,.336); both outside boundary gaps and the inside incompatibility gain exceed1/25000. Independent polynomial/Fraction/Bernstein checks confirm denominator positivity, vertex, ramp, baseline/source margins, outer/inner gains and the degree8 coefficients.

7. Fixa<β=liminfA/n before choosingC and taking a subsequence toβ. The high-sample range holds with a fixed margin. Only after N→∞ let a↑β, so no uniform-in-C error is needed. The necessary newQ(β)≥0 and exact decreasing/root bracket give β≤b_new. Injectivity transfers a hypothetical larger diagonal liminf into a contradictory larger blocker liminf.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- The full paper derivation and its inherited service budget were independently reconstructed, with exact rational checks in exact-algebra-checks.json. The original source had no referee or Lean verification; this publication adds a mathematical audit, not a Lean certificate.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/legacy-counting-extremizer-incompatibility.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: The finite counting service budget and baseline bound](../supplements/counting-service-budget.md)
- [Full proof and definitions: Quantitative incompatibility of the two counting extremizers](../supplements/counting-extremizer-proof.md)
