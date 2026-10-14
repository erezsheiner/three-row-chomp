# Second review of the strict unconditional liminf gap

This is a root-agent cross-check of the argument independently reconstructed in the paper-A lane. It supplements, rather than replaces, that lane's review of the P108 analytic dependency. Source statements reviewed here are `UNCONDITIONAL-MEX-GAP.md`, `REARRANGEMENT-STABILITY-BRIDGE.md`, `lanes/macro/LOCAL-MEX-GAP.md`, and `lanes/drop-source/MEX-PREFIX-MOMENT.md` in `projects/central-first-exit/work/DIRECT-Q-DATED-BLOCK-20261013-011/`.

## Local MEX contradiction

The mortality count uses every eventual mortal host u<h, including hosts whose deaths occur after the current cut. Its death p is <=2u+1 and therefore lies inside the local density interval. With j=A(p), P98 and the two density inequalities give u>=3j/2−3δN/2. Distinct deaths have distinct j, so there are at most2h/3+δN mortal hosts below h and Imm(h)>=h/3−δN. For an immortal of rank k=Imm(h), this gives h<=3k+3δN. No ordering of victim columns is assumed.

The private-award MEX ceiling is a rank inequality: smaller diagonal labels must be in the inherited journal, the host's previous private diagonal awards, or the current left prefix. Their counts are bounded by h,K,T. Thus R(z−1)<=h+K+T for a good-row award z, and z<=u_(h+K+T+1). This works for blocker awards as well as diagonal awards. At most ρN bad rows at a fixed host are discarded explicitly. Earlier mortal death labels are forbidden at this later host by whole-history victim-host exclusion.

Write j=h+K+T+1 and U=u_j. Since K<=N−h and T<=N−1, j<=2N, and the sorted reach bound gives U<=4N−1. Local density at U gives c(j−δN)<=U<=c(j+δN). The lower bound, using K>=0 and the definition of T, yields U−2h>=(2−c)(cN−h)+cbεN>0. Therefore every earlier eventual death is in the forbidden pool at U. This verifies the step from a truncated death count to all earlier mortal hosts; it does not assume an upper bound on the chronological birth diagonal.

Substituting the immortal-rank bound yields the two affine lower service lines in the source. Their crossing is2−c; the later zero is(c²−3c+3)/(3c−2)<1/4 on the stated interval. All needed immortal ranks are available. Since the service cells of distinct immortal hosts are disjoint, summation is legitimate. Integrating the decreasing envelope gives the displayed F(c), and subtracting good-row capacity yields (c−1)(4c³−16c²+25c−17)/(2c(3c−2)). The rational lower bound1/2560 and error allowance ε+7δ+2ρ+5/N have substantial slack at the stated constants.

## Rearrangement coercivity and scale extraction

For each prefix m, missing diagonal ranks <=m are replaced by distinct emitted ranks>m. Monotonicity of A(u_r) therefore gives the missing-rank lower bound for P_m; no monotonicity of d by time is needed. For each low emission at i, its numerical rank is at least δN behind i. In the preceding interval of aboutδN/4 prefixes, its label is still missing and contributes at least aδN/4. Different emissions have distinct ranks, so contributions add inside each P_m even when their prefix intervals overlap. The weight is at least2/N³ for m<N. This proves the positive local energy bound. All relevant diagonal values lie in the local counting interval by the lower and upper reach bounds.

There is one literal wording correction: the step-function extension A(x)=A(floor x) is not Lipschitz. The triangle argument needs only

    E_a(y) >= E_a(x) − a(y−x),  y>=x,

which follows from monotonicity of A. A large excess therefore stays at least half as large on a suitable interval to its right. Alternatively one may explicitly interpolate linearly and track an additive unit. The corrected publication should use the displayed one-sided inequality; discontinuities do not invalidate the proof.

The Fubini factor is safe. If κ>.1336, then Ecal+J/2<=8(κ Ecal+J). Each t belongs to N-windows of logarithmic length2log M. The extra range[X,MX] contributes O(log M), independent of X, because excess is O(t)+C and P_m=O(m²). Dividing by log X gives the bound16log(M)D(a).

For the explicit choice ε=ρ=10^-5,ν=10^-15,M=10^16, the delay parameter is greater than3·10^-12. Its admissible counting error exceeds10^-15, and g=aηδ_delay²/100 exceeds10^-31. The triangle thresholdν²/400 exceeds10^-35. Thus W<10^-35 forces the two incompatible local conditions. With a*=b†−10^-50, D(a*)<=10^-48 and16log M<800, the average upper bound is below8·10^-46, while every sufficiently large cut has W>=10^-35. The large-N threshold may depend on the fixed envelope constant C, which is harmless.

Finally, the deduction from no global lower envelope to liminf A(n)/n<=a* is correct: a strictly larger liminf would supply such an envelope. If ℓ=liminf d(n)/n, an eventual lower bound d(n)>=(ℓ−ε)n gives R(x)<=x/(ℓ−ε)+O(1) by injectivity, hence liminf A(x)/x>=1−1/(ℓ−ε). Letting ε decrease gives the stated bound for ℓ. This is a liminf theorem, not a limsup bound, eventual pointwise estimate, convergence theorem, or proof of the silver constant.

Subject to the independently audited P108 retained-budget premise and the shared canonical foundation bridge, the assembled mathematical argument passes this second check after the wording repair. The numerical improvement10^-50 is deliberately microscopic; its significance must not be advertised as a useful numerical approximation.
