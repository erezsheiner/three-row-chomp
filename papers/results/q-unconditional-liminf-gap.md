# A strict unconditional improvement below the earlier liminf endpoint

**Statement.** For the canonical table, let b_dagger be the unique root in[.467,.469] of3b^4-34b^3-70b^2+27b+6 and a_*=b_dagger-10^-50. Then liminf A(n)/n<=a_* and liminf d(n)/n<=1/(1-a_*). No convergence or limsup statement is asserted.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Independent reconstruction of the strict liminf gap](../../audit/full/paper-a/STRICT-LIMINF-DERIVATION.md)
- [Second review of the strict unconditional liminf gap](../../audit/full/INDEPENDENT-ASYMPTOTIC-CROSSCHECK.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- The full positive-MEX/COPY journal, FFD and victim propagation are supplied by the shared foundation.
- The P108 budget, retained chronological slack, local missing-rank coercivity and local MEX gap are reconstructed in the linked full audit; they are not additional unproved hypotheses.
- The conclusion concerns liminf only. The microscopic margin 10^-50 is explicit and is not a practical numerical approximation.

## Argument

1. Independently rebuilt the P108 budget: weighted row census, Abel identity, sorted diagonal rank bound u_i<=2i-1, concave tangent of2-1/(1-z), retained chronological prefix slack; victim envelope/Hall swap; two-anchor rational certificate; immortal mean and deficit budgets; chord lower bound; disjoint column service integration. Every error is O_{a, C}(1), not an unproved o(N). Detailed derivation is in the adjacent document.

2. Set P_m=sum_{i<=m}[A(d(i-1))-A(u_i)]>=0. Abel gives weighted slack=P_N/N^2+J_N, J_N=2 integral_1^N P_floor(t)/t^3dt. Retaining this term strengthens budget to kappa_a Ecal_a+J<=D(a)logX+O(1), with kappa>.1336 and D(a)=aP(a)/[(1-a)(3a+1)(6a^2+9a+2)].

3. Every missing numerical rank r<=m is replaced by an emitted rank>m, giving P_m>=sum_missing[A(u_(m+1))-A(u_r)]. On a near-linear counting profile, anη fraction of ε-low chronological rows has rank delay>=δN. Each missing label persists over at leastδN/5 prefix indices, contributing at least aδN/4 each. Weighted energy per bad row>=aδ²/(10N), so J_local>=aηδ²/100. Lower bound d(i-1)>=i already places labels aboveηN/2; the stronger1.5reach quoted in source is unnecessary.

4. Local MEX contradiction independently reconstructed: local density gives Imm(h)>=h/3-δN. Discard at mostρN bad award rows; positive MEX forces remaining awards<=u_(h+K+T+1). This quantile exceeds2h, so all earlier-death forbidden labels are counted. Combining new and old service lines gives S_N>=F(c)N²-eN²-4N. Rational identity F(c)-(2-c)/2>1/2560 on[1.877,1.878] contradicts good-row capacity wheneverε+7δ+2ρ+5/N<1/2560.

5. Use ε=ρ=10^-5,ν=δ_count=10^-15, M=10^16, w0=10^-35. If W_a(N)<w0, any E_a>=νN/2 on[N/M,4N] creates a triangle of integral>=ν²/400>w0; small initial x and C/N handle the remainder. If≥ρN low rows, discard only firstρN/4; remaining>ηN withη=ε_prime=5e-6 force J_local>=g>10^-31, hence W>=g/2>w0. Therefore every large scale has W>=w0.

6. Fubini gives logarithmic mean W<=16logM D(a). Mean-value/rational bounds give D(a_*)<=100*10^-50=10^-48 and16logM<800, so upper mean<8e-46<w0/2. Contradiction rules out any global A>=a_*x-C. If liminfA/n>a_* such C would exist. For ell=liminf d/n, injectivity and eventual d(n)>=(ell-ε)n imply R(x)<=x/(ell-ε)+O(1), yielding ell<=1/(1-a_*).

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/q-unconditional-liminf-gap.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Detailed audit proof or correction](../../audit/full/paper-a/STRICT-LIMINF-DERIVATION.md)
- [Detailed audit proof or correction](../../audit/full/INDEPENDENT-ASYMPTOTIC-CROSSCHECK.md)
- [Detailed audit proof or correction](../../audit/full/paper-b/SECOND-REVIEW-A.json)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Independent reconstruction of the strict liminf gap](../../audit/full/paper-a/STRICT-LIMINF-DERIVATION.md)
- [Full proof and definitions: Second review of the strict unconditional liminf gap](../../audit/full/INDEPENDENT-ASYMPTOTIC-CROSSCHECK.md)
- [Fresh exact algebra replay](../../audit/prepublication/root/strict-gap-algebra.json)
- [Exact algebra checker (Sympy 1.14.0)](../../audit/prepublication/root/replay_strict_gap_algebra.py)
- [Historical exact algebra receipt](../../audit/full/paper-a/independent-checks.json)
