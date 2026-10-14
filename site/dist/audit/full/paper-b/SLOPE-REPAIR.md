# Independent completion of the existing-slope upper bound

This repairs the proof package for `q-existing-slope-upper-bound`. It proves a restriction on an **existing** ordered slope; it does not prove convergence. Earlier paper-review assertions are not used as mathematical premises. Exact algebra is independently checked in `exact-algebra-checks.json`. The actual-game recurrence, floor/max/injectivity/partition, propagation and FFD bridges are specified in the root's `CANONICAL-FOUNDATIONS.md`; their final kernel authentication remains a separate admission requirement.

Assume the canonical diagonal satisfies d(n)/n→c. Write b=1−1/c, B=c²−3c+3, D=c²+c−1 and z=2−c. Reach gives c≤2, and the checked diagonal lower bound gives c≥3/2. Value-set counting gives A(x)=bx+o(x), uniformly on bounded multiples of a growing parameter. No diagonal order beyond the assumed slope is used.

## 1. Actual service inputs, independently reconstructed

A blocker p has exactly A(p) distinct private predeath service hosts, all strictly left of its victim. The first source row is τ(p)=min{q:d(q)>p}. Victims of blockers t≤τ(p) never booked p: before τ there was no p service, and they freeze by τ. Reach also excludes a victim s(t) if t+s(t)<p. These excluded victim columns lie below s(p): propagation gives s(p)≥(p−1)/2, while 2s(t)+1≤t+s(t)<p. They are disjoint from p bookers. Counting the **union** gives

`s(p) ≥ A(p)+#{t blocker:t≤τ(p) or t+s(t)<p}`.

For p_j, the j-th blocker, all still-live columns before s_j must have booked p_j earlier; at most j−1 earlier frozen victims are present there. Hence s_j≤2j−1. The first-appearance exclusion gives s_j≥j+A(τ(p_j)). Under the existing slope, τ(p_j)=p_j/c+o(j) and p_j=j/b+o(j), so s_j≥(1+1/c)j+o(j). Thus, with I(h) the number of immortal columns strictly below h,

`1/(c+1)−o(1) ≤ I(h)/h ≤ 1/2+O(1/h)`.

The upper bound follows because the first floor(h/2) distinct victims all lie below h. No victim ordering is assumed.

At START N an immortal host h<N has exactly N distinct journal labels: h inherited diagonal seeds and N−h distinct private awards. Every earlier mortal victim's blocker is excluded from that journal. Its labels are at most N+h, so the private diagonal count K_h(N) obeys

`K_h(N) ≥ N−A(N+h)−I(h)`.

Every blocker at most d(q) is present in row q, either by pending coverage, its actual death, or its frozen copy. The row therefore has exactly q+1−A(d(q)) diagonal cells. Consequently

`S(N):=Σ_{q<N}(q+1−A(d(q)))=(2−c)N²/2+o(N²)`

and every sum of K_h over distinct immortal hosts is bounded by S(N).

The literal MEX journal ceiling gives the second service line. At each private award v before N, every smaller diagonal label is in the host's journal or the current prefix. The journal has h+K_h(N) diagonal labels, and the prefix has at most M_N=max_{q<N}(q+1−A(d(q)))=(2−c)N+o(N). Thus R(v−1)≤h+K_h(N)+M_N. Inverting the sorted diagonal value count bounds private awards by the expression below. The inherited seeds have ceiling max_{a<h}d(a)≤ch+o(N), uniformly for h<N under the existing slope; since K_h(N)+(2−c)N is nonnegative, that seed ceiling is covered by the same expression. Hence the whole journal ceiling is bounded by

`c[h+K_h(N)+(2−c)N]+o(N)`.

It also contains every excluded earlier victim's blocker, since those are below their birth diagonals among the inherited seeds. Counting available blocker entries in that ceiling yields

`c K_h(N) ≥ B N−(c−1)h−I(h)−o(N)`.

All errors are uniform for h<N. These are actual journal arguments, not arbitrary continuum schedules.

## 2. Complete exclusion of c≥15/8, without a prior endpoint theorem

Index immortal hosts by k, with I(e_k)=k−1. The lower immortal density gives e_k≤(c+1)k+o(N), uniformly in the relevant rank range. The two preceding service bounds give

`K_{e_k}(N) ≥ max(0,(N−Dk)/c,(B N−c²k)/c)−o(N)`.

For √3<c<2 the nonzero lines cross at k/N=z, the old line ends at α=1/D, and the new line ends at β=B/c². The inequalities 0<z<α<β<1/(c+1) ensure every positive required rank is actually available. The last inequality is equivalent to c³−3c²+3<0, already negative at √3 and nonincreasing up to2.

Integrating in rank gives

`2S(N)/N² ≥ 1/(cD)+(c−1)³(c²−3)²/(c³D)+o(1)`.

For example, direct integration of the two line segments is

`2 area = (c−1)(2−c)²/c + B²/c³`,

which expands to the displayed expression. Hence define the necessary surplus

`F(c)=1/(cD)+(c−1)³(c²−3)²/(c³D)−(2−c) ≤0`.

At c=15/8, exact rational evaluation gives

`F(15/8)=159327/60696000>0`.

For every c∈[15/8,2), D+cD′=3c²+2c−1≤15 and cD>8, so the magnitude of the negative derivative of 1/(cD) is less than15/64. The positive additional term has logarithmic derivative

`3/(c−1)+4c/(c²−3)−3/c−D′/D`.

On the whole interval this is at least 3+15/2−8/5−5/4=153/20>0: c−1≤1, c²−3≤1, c≥15/8, and D>4. Therefore F′(c)>1−15/64>0. No c∈[15/8,2) satisfies the necessary inequality.

At c=2 the same rank bounds reduce to `(N−5k)/2` and `(N−4k)/2`. There are at least N/3−o(N) immortal hosts below N. For k≤N/4 the second line is positive and integrates to N²/16+o(N²), whereas S(N)=o(N²). This contradiction excludes c=2 directly. Thus any existing slope has c<15/8. This argument avoids the earlier source's vague appeal to a separately proved P104 endpoint.

## 3. The full union produces a logarithmic population gain

It remains to treat c∈[9/5,15/8], since smaller c already satisfies the claimed final bound. Put L=1+1/c, v_j=s_j/j and r_j=A(τ(p_j)); define m_i=A(p_i+s_i). Uniform asymptotics give r_j=j/c+o(j), m_i=i(1+bv_i)+o(i), and v_j∈[L−o(1),2]. The exact union is

`s_j ≥ j+r_j+#{i>r_j:m_i<j}`.

For fixed ξ>0, each sufficiently large i contributes to the last count whenever

`(1+bv_i+ξ)i < j < i/(1/c+ξ)`.

Divide by j² and sum j≤J. The ranks i≤(1/c+ξ)J have their complete sufficient interval inside the sum. Omitting the other proportional tail from the desired reciprocal-weighted expression costs O_ξ(1); each integer boundary costs O(i⁻²). Let J→∞ before ξ→0. With φ(v)=[1/(1+bv)−1/c]_+, this proves

`liminf (log J)⁻¹ Σ_{i≤J}(v_i−L−φ(v_i))/i ≥0`.

Define

`k=c(2c²−1)/[2(c²−1)(3c+2)]`,

`C=(5c²+5c+1)/[2(c+1)(3c+2)]`,

`V=1−C=(c²+5c+3)/[2(c+1)(3c+2)]`.

The pointwise reciprocal bound is `1/v≤C−k(v−L−φ(v))` on [L,2]. To prove it, H(v)=1/v+k(v−L−φ(v)) has equal outer endpoint values C. Its second derivative is 2/v³−2kb²/(1+bv)³>0 on [L,c] and 2/v³>0 on [c,2]. Here k<1, b<1/2 and (1+bv)/v>b+1/2>0.9, so the first curvature dominates the second. The kink value is smaller by `(2−c)(k−1/(2c))≥0`; positivity reduces to `(c²−c−1)(2c²−c−2)>0` on the stated interval. Convexity on each piece then proves the bound everywhere.

Applying it to the weighted union gives

`limsup (log J)⁻¹ Σ_{i≤J}1/s_i ≤C`.

The actual mortal-victim census M(x) satisfies

`∫_1^X M(t)t⁻²dt = Σ_{i≤X}1/s_i+O(1)`.

Indeed exact summation over victims with s_i<X gives Σ1/s_i−M(X)/X; because i≤s_i≤2i−1, replacement by indexes i≤X changes only a proportional reciprocal tail of bounded mass. Since I(x)=x−M(x),

`liminf (log X)⁻¹∫_1^X I(t)t⁻²dt ≥V`.

This is a logarithmic mean, never a pointwise immortal-density assertion.

## 4. Integrate the two service lines before averaging the population

First omit the finite host h=0 from the weighted host sum. Its K_0(N)≤N contribution integrates against 2dN/N³ to O(1), so it does not affect the logarithmic coefficient. For each remaining fixed immortal physical host h>0, write u=I(h)/h. The two affine service lines are

`old=N/c−b h−u h`,

`new=B N/c−b h−u h/c`.

Their crossing is N=uh/z and occurs after birth and after both positivity thresholds: u≥u0−o(1), u0=1/(c+1), and u0>z/(c−1) throughout this interval. Integrating the maximum of0 and these lines against 2dN/N³ gives exactly

`Ψ_c(u)/h`, where `Ψ_c(u)=B²/[c(c−1+u)]+b z²/u`.

The first summand is the full new-line triangle. The second is the integrated old-minus-new line beyond their crossing. Truncating each host's upper integration at X costs O(1/X) per host, hence O(1) in total. Uniform service errors are first bounded by εN, giving O(ε log X), and ε is then sent to zero. Summing the actual diagonal-cell budget yields

`2−c ≥ limsup (log X)⁻¹Σ_{h<X, h immortal} Ψ_c(I(h)/h)/h`.

Stieltjes summation, using dI=u dh+h du, turns this into the logarithmic integral of

`g_c(u)=u Ψ_c(u)=(B²/c)u/(c−1+u)+b z²`.

The remaining ∫Ψ_c(u)du is a bounded primitive evaluated at endpoints. Discrete jumps cost O(Σh⁻²); an ε-enlargement accommodates the asymptotic lower endpoint. Thus the passage uses neither a limit of u nor pointwise saturation.

The function g_c is increasing and concave. Its chord on [u0,1/2], evaluated at the independently proved mean lower bound V, gives

`g_c(u0)+(V−u0)[g_c(1/2)−g_c(u0)]/(1/2−u0) ≤2−c`.

Here V>u0 because c²−c−1>0, and V<1/2 because 2c²−1>0. The chord of u/(c−1+u) at V simplifies to

`(c³+4c²+c−1)/[c²(3c+2)(2c−1)]`.

Clearing positive denominators gives

`(c²−3c+3)²(c³+4c²+c−1) ≤ (2−c)c²(3c+2)(2c−1)(c²−2c+2)`.

Independent expansion of left minus right is

`P(c)=7c⁷−25c⁶+22c⁵+25c⁴−58c³+11c²+27c−9`.

Exact Bernstein coefficients of P′ on [9/5,15/8] are all strictly positive. Endpoint signs and independent rational bisection therefore establish one unique root c_*. Its upper rational bracket is below 1.868565865679. The necessary P(c)≤0 gives c≤c_*. Together with Section2 and the trivial c<9/5 branch, the restriction holds for every existing canonical slope.

The proof supplies no convergence theorem, canonical signed balance, clock uniform integrability, or Q=o(n). It also does not replace the separate unconditional liminf theorem by this conditional numerical bound.
