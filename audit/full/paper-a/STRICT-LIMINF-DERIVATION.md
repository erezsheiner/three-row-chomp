# Independent reconstruction of the strict liminf gap

This is a mathematical audit, not a new Lean formalization. It reconstructs the analytic suppliers rather than accepting the P108 label as a proof. The canonical recurrence and game interpretation are covered by `../CANONICAL-FOUNDATIONS.md`. In particular, positive blocker labels have distinct victims; a blocker's private services all occur strictly left of its victim; a diagonal label never freezes; FFD holds; and row entries are distinct with strict diagonal maximum.

The primary sources are the dated-block `UNCONDITIONAL-MEX-GAP.md`, `REARRANGEMENT-STABILITY-BRIDGE.md`, `lanes/drop-source/MEX-PREFIX-MOMENT.md`, and `lanes/macro/LOCAL-MEX-GAP.md`, together with the earlier unconditional-liminf `lanes/DRAFT-BRIEF-SECTION-21.md` and `lanes/L2-rowcap.md`. Their individual paths and hashes are bound in the per-ID JSON. Exact algebra and rational constant checks are separately recorded in `independent-checks.json`. Those calculations do not replace the following analytic arguments.

## Statement and conventions

Let (A(x)=A(\lfloor x\rfloor)) count positive blocker labels at most (x). Write (R(x)=\lfloor x\rfloor-A(x)) for the count of positive diagonal labels. Let (u_1<u_2<\cdots) list those labels and (d(q)) be the chronological diagonal. Let (b_\dagger) be the unique root in ([.467,.469]) of

\[
P(b)=3b^4-34b^3-70b^2+27b+6.
\]

The audited conclusion is

\[
\liminf_n A(n)/n\le a_*:=b_\dagger-10^{-50},\qquad
\liminf_n d(n)/n\le (1-a_*)^{-1}.
\]

There is no convergence conclusion and no bound on the limsup in this statement. Existence and uniqueness of this root follow from opposite endpoint signs and (P'<0) on the displayed interval; the rational checks also put (c_\dagger=(1-b_\dagger)^{-1}) in ([1.877,1.878]).

Suppose, towards contradiction, that (A(x)\ge ax-C) for all (x\ge1), where (a\in[.467,.469]) and (C\ge a). Set

\[
E(x)=A(x)-ax+C\ge0,\qquad \mathcal E(X)=\int_1^X E(t)t^{-2}\,dt.
\]

The step counting function is **not uniformly Lipschitz**. The correct bounds used below are

\[
E(y)\ge E(x)-a(y-x),\quad
E(y)\le E(x)+(1-a)(y-x)+1\qquad(y\ge x).
\]

The first follows from monotonicity of (A); the second follows from (A(y)-A(x)\le y-x+1). Consequently replacing a point by a point within a fixed distance changes (E) by a bounded amount. Every resulting error in a sum with weights (i^{-2}) is summable. The later positive-triangle argument uses only the first inequality. Alternatively, piecewise linear interpolation changes all these formulas by (O(1)) and their integrals by (O(1)).

## 1. Row capacity with retained rearrangement energy

Let (D_q=q+1-A(d(q))) be the number of diagonal labels in completed row (q). Every blocker label at most (d(q)) occurs there, and no larger one does. Let (S_N=\sum_{q<N}D_q) and (\operatorname{Cap}(X)=\int_1^X S_{\lfloor t\rfloor}t^{-3}\,dt). Exact integration on unit intervals gives

\[
2\operatorname{Cap}(N)=\sum_{q<N}\frac{D_q}{(q+1)^2}-\frac{S_N}{N^2}.
\]

Put (z_i=A(d(i-1))), (v_i=A(u_i)=u_i-i), and (P_m=\sum_{i\le m}(z_i-v_i)). Among any (m) distinct diagonal labels, the sum of their (A)-values is at least that for the smallest (m), so (P_m\ge0). Abel summation gives

\[
\sum_{i\le N}\frac{z_i-v_i}{i^2}
=\frac{P_N}{N^2}+J_N,\qquad
J_N=\sum_{m<N}P_m\left(\frac1{m^2}-\frac1{(m+1)^2}\right)
=2\int_1^N\frac{P_{\lfloor t\rfloor}}{t^3}\,dt.
\]

The reach bound supplies (u_i\le2i-1). Since (R(t)=i) on ([u_i,u_{i+1})), a second Abel identity is

\[
\int_1^{u_N}\frac{dt}{R(t)}
=\frac{u_N}{N-1}-1+\sum_{i=2}^{N-1}\frac{u_i}{i(i-1)}\quad(N>1).
\]

Replacing (i(i-1)) by (i^2), and changing the upper integration endpoint from (u_N) to (N), costs (O(1)): the errors are summable because (u_i=O(i)), and the endpoint ratio is bounded. This avoids assuming bounded gaps between successive diagonals.

Writing (f(z)=2-(1-z)^{-1}), its concavity gives the tangent bound

\[
f(A(t)/t)\le f(a)-\frac{E(t)-C}{(1-a)^2t}.
\]

The floor in (R(t)) contributes only an integrable (O(t^{-2})) error, because (R(t)\gg t). Substitution in the row identity, dropping the nonnegative boundary terms, yields

\[
2\operatorname{Cap}(X)
\le f(a)\log X-\frac{\mathcal E(X)}{(1-a)^2}-J_{\lfloor X\rfloor}+O_{a,C}(1).
\tag{R}
\]

## 2. Victim counts and a quantitative immortal supply

Let (p_i) be the (i)-th blocker, (s_i) its victim, and (I(x)) the number of immortal columns (h<x). The necessary service counts are independently justified as follows.

* There are (A(p_i)=i) distinct private hosts for (p_i), all below (s_i). Every column below (s_i) survives or dies; the usual birth/death census gives (s_i\le2i-1).
* If (p_j+s_j<p_i), then victim (s_j) cannot have served (p_i): before its death the reach inequality (f(t,s_j)\le t+s_j+1) excludes the larger label, and afterwards it is frozen. It is below (s_i) by the victim propagation bound. Therefore
  (s_i\ge i+\#\{j:p_j+s_j<p_i\}). This is the Hall count used below.
* Let (\tau(p)=\min\{q:d(q)>p\}). The (A(p)) private hosts and the (A(\tau(p))) earlier-dead victims are disjoint subsets of the columns below (s(p)). The latter could not serve (p) before (\tau), and afterwards are frozen. Hence (s(p)\ge A(p)+A(\tau(p))\ge A(p)+A(\lceil p/2\rceil)).

Using (A\ge ax-C) in the Hall count gives

\[
s_i\ge\gamma i-O_{a,C}(1),\quad
\gamma=\frac{1+4a}{1+2a},\qquad
I(x)\ge\frac{2a}{1+4a}x-O_{a,C}(1).
\]

For example (p_j\le(j+C)/a) and (s_j\le2j-1); all ranks up to (2ai/(1+2a)-O(1)) fit into the Hall set, giving the first formula. Here p_i>=2i follows from A(x)<=floor(x/2): the reach bound d(q)<=2q+1 ensures at least ceil(x/2) distinct diagonal labels at most x. Combining this with p_j+s_j<=(1+2a)j/a+O(1) justifies the factor 2 in the sufficient rank cutoff. The victim bound (s_i\le2i-1) also gives (I(x)\le x/2+O(1)). The last disjoint count, after writing (i=ap_i+E(p_i)-C), gives the more precise

\[
s_i\ge\tfrac32 i-\tfrac12 E(p_i)-C/2.
\tag{V}
\]

For separated increasing sample points (z_i), with (z_{i+1}-z_i\ge g>0) and (z_i\le Bi+O(1)), the elementary sampling estimate is

\[
\sum_{i\le X}\frac{E(z_i)}{i^2}
\le\frac{B^2}{g}\mathcal E(X)+O_{a,C,B,g}(1).
\tag{S}
\]

Integrate the one-sided bound for (E) over the disjoint intervals ([z_i,z_i+g]); replacing (z_i^{-2}) by (i^{-2}/B^2) costs a summable error. Extending the integral to a fixed multiple of (X) costs (O(1)) since (E(t)=O(t)+C). This proves (S), with no incorrect continuous Lipschitz premise.

Write (v_i=s_i/i), (w_i=\max(v_i,3/2)), and (m_i=A(p_i+s_i)). Swapping the finite Hall sums gives

\[
\sum_{i\le X}\frac{v_i}{i}\ge
\sum_{i\le X}\frac1i+\sum_{i\le X}\frac1{m_i+1}-1.
\]

For anchors (h=3/2,2), monotonicity and the unit-increment bound for (A) give

\[
m_i\le i[1+ah+(w_i-h)_+]+E(p_i+hi)+O(1).
\]

Taking the better reciprocal bound and applying (S) gives

\[
\sum_{i\le X}\frac{F_a(w_i)}i\ge-\frac{11}{15a^2}\mathcal E(X)-O(1),
\quad F_a(w)=w-1-U_a(w)^{-1},
\quad U_a(w)=\min(1+w-\tfrac32(1-a),1+2a).
\]

For (D=6a^2+9a+2), define

\[
k=\frac{(2a+1)(3a+2)}{3D},\qquad
c_a=\frac{30a^2+35a+6}{6D}.
\]

The pointwise certificate (1/w\le c_a-kF_a(w)) holds for (3/2\le w\le2). On the first branch its numerator factors as (-(2w-3)Q_a(w)), where (Q_a) is convex and both endpoint values are nonpositive. On the second it factors as (-(w-2)B_a(w)), with (B_a\ge0). Denominators are positive throughout. The exact identities and endpoint inequalities were independently checked with rational arithmetic, so no plot or rounded maximizer is used.

Equation (V), the lower bound (s_i\ge\gamma i-O(1)), and (S) account for replacing (w_i) by the actual (s_i/i). With (\eta=1/(3\gamma a^2)), this gives both

\[
\int_1^X I(t)t^{-2}\,dt
\ge (1-c_a)\log X-\left(\frac{11k}{15a^2}+\eta\right)\mathcal E(X)-O(1)
\]

and

\[
\int_1^X(1/3-I(t)/t)_+\,dt/t\le\eta\mathcal E(X)+O(1).
\]

The second estimate charges each deficit interval (s_i<t\le3i/2) to the same reciprocal difference. No pointwise immortal density limit is assumed.

For (g_a(u)=u/(a+u)), use its chord between (u=1/3) and (1/2), with an explicit linear penalty below (1/3). Its slope is (6a/[(2a+1)(3a+1)]), and the extra penalty is (3/[(2a+1)(3a+1)(4a+3)]). The preceding two integral estimates give

\[
\int_1^X g_a(I(t)/t)\,dt/t\ge G\log X-\Theta\mathcal E(X)-O(1),
\]

where

\[
G=\frac{3a^2+11a+2}{(3a+1)D},\qquad
\Theta=\frac{444a^3+734a^2+327a+30}{15a^2(3a+1)(4a+3)D}.
\]

## 3. Column capacity and the retained budget

For immortal column (h<N), its full journal before row (N) has exactly (N) distinct labels. Every mortal column below (h) has a different death blocker which cannot be in this journal: all services of that blocker are strictly left of its own victim. The journal ceiling from the reach bound is (N+h). Thus its number of diagonal awards is at least

\[
[N-A(N+h)-I(h)]_+.
\]

Summing over immortal columns counts disjoint cells. Substituting (A(x)=ax+E(x)-C), and discarding (C\ge0), gives

\[
S_N\ge\sum_{h<N,\ h\text{ immortal}}[(1-a)N-ah-I(h)]_+
-\sum_{h<N}E(N+h).
\]

Before dividing by a h+I(h) or using I(h)/h, omit host h=0. Its at most N service cells contribute only O(1) after integration against 2N^{-3}; any fixed finite collection of other small hosts is harmless for the same reason. The reciprocal summation below is over immortal h>0.

Integration against (2N^{-3}) turns one positive part into ((1-a)^2/[ah+I(h)]), up to summable integer errors. Its threshold lies above (h+1) for all large (h), since (I(h)/h\ge2a/(1+4a)-o(1)>1-2a). Stieltjes summation over immortal (h) turns the reciprocal sum into the integral of (g_a(I(t)/t)/t), with a bounded logarithmic boundary and summable rounding terms. For the excess error, exchanging the two integrals gives coefficient at most (3), since (2\int_{s/2}^{s}N^{-3}\,dN=3/s^2). Hence

\[
2\operatorname{Cap}(X)\ge(1-a)^2G\log X-\{3+(1-a)^2\Theta\}\mathcal E(X)-O(1).
\tag{C}
\]

Combining (R) and (C) yields

\[
\kappa_a\mathcal E(X)+J_{\lfloor X\rfloor}
\le D_*(a)\log X+O_{a,C}(1),
\]

\[
\kappa_a=\frac1{(1-a)^2}-3-(1-a)^2\Theta>.1336,\qquad
D_*(a)=\frac{aP(a)}{(1-a)(3a+1)(6a^2+9a+2)}.
\tag{B}
\]

Every error above is bounded for fixed (a,C). In particular, no step assumes (E=o(x)).

## 4. Missing ranks force local rearrangement energy

For the first (m) chronological diagonals, let a numerical rank be missing if it is at most (m) and has not yet appeared. Sorting the omitted and substituted ranks gives

\[
P_m\ge\sum_{r\le m,\ r\text{ missing}}{A(u_{m+1})-A(u_r)}.
\]

Suppose (A(x)=ax\pm\tau N) on ([\eta N/2,2N]), and at least (\eta N) indices (i\ge\eta N/2) satisfy (d(i-1)\le(c-\varepsilon)i), where (c=(1-a)^{-1}). Put (\delta=(1-a)\varepsilon\eta/4). If (\tau\le\min(\delta/2,a\delta/16)), then their numerical ranks satisfy (r_i\le i-\delta N). The elementary lower bound (d(i-1)\ge i) puts the labels in the required counting interval; the stronger slope lower bound is unnecessary here.

For each such row, its rank remains missing throughout the integer interval ([i-\delta N/2,i-\delta N/4]), containing at least (\delta N/5) integers for large (N). On that interval the (A)-difference is at least (a\delta N/4), and the Abel weight is at least (2/N^3). Distinct bad rows have distinct missing ranks, so their contributions can be added, even when the time intervals overlap. Therefore

\[
J_{\rm local}\ge a\eta\delta^2/100.
\tag{J}
\]

## 5. Local MEX capacity gap

Let (c\in[1.877,1.878]), (b=1-1/c). Assume (A(x)=bx\pm\delta_0N) on ([0,4N]), and at most (\rho N) rows below (N) have (d(t)<(c-\varepsilon)t). The victim disjoint count gives (I(h)\ge h/3-\delta_0N), so immortal number (k) has index at most (3k+3\delta_0N), for the available range (0\le k\le N/4).

A good row has at most ((2-c+b\varepsilon)t+\delta_0N+1) diagonal awards. Choose

\[
T=\lceil(2-c+b\varepsilon+\delta_0)N\rceil+2.
\]

For an immortal column (h), let (K) count all its private diagonal awards before (N), and set (j=h+K+T+1), (U=u_j). At a good-row MEX award, the journal and left prefix cannot cover more than (j-1) earlier diagonal labels, so that award is at most (U). Discarding the at most (\rho N) bad-row awards loses at most that many labels. The quantile bounds (c(j-\delta_0N)\le U\le c(j+\delta_0N)), the definition of (T), and (K\ge0) give (U>2h), while (U\le4N). Consequently all deaths of earlier mortal columns are below this ceiling and may be excluded from the journal. The count yields

\[
cK\ge B N-(3c-2)k-eN-4,
\quad B=c^2-3c+3,
\quad e=b(c-1)\varepsilon+(5c-4)\delta_0+\rho.
\]

The older reach count independently gives

\[
cK\ge N-(4c-3)k-(4c-3)\delta_0N.
\]

Integrate the maximum of these two lines and zero over the available immortal ranks. All breakpoints lie in the stated range. The result is

\[
S_N\ge F(c)N^2-eN^2-4N,
\quad F(c)=\frac{B^2}{2c(3c-2)}+\frac{(c-1)(2-c)^2}{2c}.
\]

The exact difference is

\[
F(c)-\frac{2-c}{2}
=\frac{(c-1)(4c^3-16c^2+25c-17)}{2c(3c-2)}>1/2560.
\]

The good-row upper count, with bad rows charged their full capacity, is

\[
S_N\le[(2-c)/2+b\varepsilon/2+\delta_0+\rho]N^2+N.
\]

Thus these hypotheses are inconsistent whenever (\varepsilon+7\delta_0+2\rho+5/N<1/2560). This is a finite-scale deterministic contradiction, not an inference from numerical experiments.

## 6. Explicit contradiction and liminf transfer

Use (a=a_*), (\varepsilon=\rho=10^{-5}), (\nu=\delta_0=10^{-15}), (M=10^{16}), and (w_0=10^{-35}). Define

\[
W_a(N)=\int_{N/M}^{MN}\left(\frac{E(t)}{t^2}+\frac{P_{\lfloor t\rfloor}}{t^3}\right)dt.
\]

If (W_a(N)<w_0) and (E(x)\ge\nu N/2) somewhere in ([N/M,4N]), the one-sided monotonicity inequality ensures (E\ge\nu N/4) on a right interval of length (\nu N/4), where (t\le5N). Its contribution is at least (\nu^2/400>w_0), a contradiction. The interval below (N/M), the fixed (C/N) error, and (4|a-b_\dagger|) are smaller than the remaining tolerance for sufficiently large (N). Hence the required local density bound holds on ([0,4N]).

If there are at least (\rho N) low rows, discard only the first (\rho N/4) indices. More than (\eta N) remain with (\eta=\varepsilon'=5\cdot10^{-6}). In (J), (\delta>3\cdot10^{-12}), the allowed density tolerance (a\delta/16) exceeds (10^{-15}), and the energy lower bound exceeds (10^{-31}). Its entire integration range lies inside ([N/M,MN]). Thus (W_a(N)>10^{-31}/2>w_0). Otherwise there are fewer than (\rho N) bad rows, and the local MEX contradiction applies. Therefore every sufficiently large scale satisfies (W_a(N)\ge w_0).

On the other hand, Tonelli's theorem for the nonnegative integrands, followed by (B), bounds the logarithmic mean of (W_a) by (16\log M\,D_*(a)). Indeed (\mathcal E+J/2\le8(\kappa_a\mathcal E+J)), and every interior point lies in a multiplicative window of logarithmic length (2\log M). Fixed endpoint ranges contribute (O(1)), vanishing after division by (\log X).

On the root interval, elementary rational bounds give (|P'|<125), denominator at least (1), and (a<1/2), so (D_*(a_*)\le100(b_\dagger-a_*)=10^{-48}). Since (16\log M<800), the upper logarithmic mean is less than (8\cdot10^{-46}<w_0/2). This contradicts the pointwise lower bound for all sufficiently large scales. No global envelope (A(x)\ge a_*x-C) can hold.

If (\liminf A(n)/n>a_*), such an envelope would hold after increasing (C) to cover the finite initial segment. Therefore (\liminf A(n)/n\le a_*). Finally, if (\ell=\liminf d(n)/n), eventual (d(n)\ge(\ell-\epsilon)n) and injectivity imply (R(x)\le x/(\ell-\epsilon)+O(1)). Thus (\liminf A(n)/n\ge1-1/\ell), and the displayed bound on (\ell) follows. This last step does not assert that either ratio converges.

## Audit result

The strict-gap headline survives this independent reconstruction. The source's continuous Lipschitz wording must be replaced as above; the weaker lower reach (d(i-1)\ge i) also resolves the counting-domain endpoint without an additional asymptotic assumption. All shared canonical premises must be tied to the independent foundation review and its exact kernel receipts. This document supplies a paper argument, not a claim that this complete analytic theorem has been formalized in Lean.
