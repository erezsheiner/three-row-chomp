# Ordering error, Pell windows and conditional discrepancy consumers

This document gives complete proofs for `eta-envelope`, `pell-sublinear-two-supplier`, `pell-cumulative-transfer`, `pell-short-cancel`, `pell-multilevel-rigidity` and `pell-positive-response`. The analytic identities are proved here. The record-drop, cumulative-saving, positive-orientation and response-incidence assumptions are retained as assumptions; none is asserted to hold at all scales of canonical Chomp merely because it is a sufficient condition.

## 1. Counting and ordering conventions

Let `d : {0,1,...} -> {1,2,...}` be injective, with

\[
 n<d(n)\le2n+1.
\]

The canonical Chomp diagonal has these properties. Let `D` be its image, let `S` be the positive integers outside `D`, and define

\[
 A(N)=\#(S\cap[1,N]),\quad A(0)=0,\quad R(N)=N-A(N).
\]

Thus `A(N+1)-A(N)` is either zero or one. All counting arguments here concern integer endpoints. Define the earlier record and its signed drop by

\[
 M_0=0,\qquad M_n=\max_{0\le r<n}d(r)\ (n>0),\qquad
 \mu_n=d(n)-M_n.
\]

Define the finite inversion counts and the ordering error by

\[
 F_n=\#\{r>n:d(r)<d(n)\},\quad
 B_n=\#\{r<n:d(r)>d(n)\},\quad \eta_n=F_n-B_n.
\]

Finiteness follows from `r<d(r)<d(n)` in the first set. Finally put

\[
 \beta=\sqrt2-1,\qquad J(N)=A(N)-\beta N,
 \qquad D_{\rm cen}(n)=n+A(n)-2A(d(n)).
\]

The symbol `D_cen` is this counting discrepancy, not a record drop and not the set `D`.

**Exact rank identity.** Of the diagonal values before row `n`, precisely `n-B_n` are smaller than `d(n)`. Add the value at row `n` and the `F_n` later smaller values. Injectivity gives

\[
 R(d(n))=n+1+\eta_n,
 \qquad \eta_n=d(n)-A(d(n))-n-1.
\tag{1}
\]

Consequently

\[
 D_{\rm cen}(n)
 =-\sqrt2(1+\eta_n)+J(n)-(2+\sqrt2)J(d(n)).
\tag{2}
\]

For a direct verification, substitute (1), `J(x)=A(x)-beta*x`, and `(2+sqrt(2))*beta=sqrt(2)`. The coefficient of `d(n)` cancels, the coefficient of `A(d(n))` becomes `-2`, and that of `n` is `sqrt(2)-beta=1`. No assumption that the emitted diagonal values are increasing is used.

## 2. A record-drop envelope bounds ordering error

Suppose `h` is a nonnegative, nondecreasing integer-valued function with

\[
 d(n)\ge M_n-h(n)\quad\text{for every }n.
\tag{3}
\]

Then

\[
 B_n\le h(n),\qquad F_n\le h(2n+1),\qquad
 |\eta_n|\le h(2n+1).
\tag{4}
\]

If `d(n)>=M_n`, the backward set is empty. Otherwise its distinct integer values lie in `(d(n),M_n]`, an interval containing at most `h(n)` integers. For a forward contributor `r>n`,

\[
 r<d(r)<d(n)\le2n+1,\qquad M_r\ge d(n).
\]

By (3) and monotonicity, `d(r)>=d(n)-h(2n+1)`. The contributing values are distinct integers in `[d(n)-h(2n+1),d(n))`, so there are at most `h(2n+1)`. The absolute difference of two nonnegative counts is no larger than their maximum, proving (4). At `n=0`, the reach bound gives `d(0)=1` and both inversion sets are empty.

A real-valued nonnegative nondecreasing envelope can be replaced by its ceiling. This adds at most one and preserves sublinearity. In particular `h(n)=o(n)` implies `eta_n=o(n)`. More generally, if a nonnegative nondecreasing function `phi` bounds `|J(x)|`, equation (2) gives

\[
 |D_{\rm cen}(n)|\le
 \sqrt2(1+h(2n+1))+\phi(n)+(2+\sqrt2)\phi(2n+1).
\tag{5}
\]

Thus bounded or logarithmic record-drop envelopes have the expected conditional consumers. Neither a canonical envelope nor a bound for `J` is proved by (4).

## 3. Pell numbers, exact windows and maximum norms

Define

\[
 q_{-1}=0,\quad q_0=1,\quad q_1=2,\quad
 q_{j+1}=2q_j+q_{j-1},\qquad p_j=q_{j-1}\ (j\ge0).
\]

In particular `(p_0,q_0)=(0,1)` and `(p_1,q_1)=(1,2)`, and `p` obeys the same recurrence from these initial values. With `rho=1+sqrt(2)` and `theta=1-sqrt(2)=-beta`,

\[
 q_j=\frac{\rho^{j+1}-\theta^{j+1}}{2\sqrt2},
 \qquad p_j-\beta q_j=-\beta\theta^j.
\tag{6}
\]

These formulas satisfy the recurrence and initial values, which proves them by induction. Hence `q_j` is comparable to `rho^j`, `p_j/q_j -> beta`, and `|p_j-beta*q_j|=beta^(j+1)`.

For every integer start `s>=0`, let

\[
 W_j(s)=A(s+q_j)-A(s)-p_j,\qquad
 b_j=\max_{s\ge0}|W_j(s)|.
\tag{7}
\]

At a fixed length, `A(s+q_j)-A(s)` is an integer between zero and `q_j`. The set of possible defects is therefore a nonempty finite set of integers, so the displayed maximum exists even though the set of starts is infinite.

For `j>=1`, the three consecutive child windows have starts `s`, `s+q_j`, `s+2q_j` and scales `j,j,j-1`. Telescoping their counts and using both Pell recurrences gives the exact identity

\[
 W_{j+1}(s)=W_j(s)+W_j(s+q_j)+W_{j-1}(s+2q_j).
\tag{8}
\]

Consequently `b_(j+1)<=2b_j+b_(j-1)`. Define its nonnegative slack by

\[
 S_j=2b_j+b_{j-1}-b_{j+1}\ge0\qquad(j\ge1).
\tag{9}
\]

These identities hold for any binary counting function `A`; game chronology is not needed.

## 4. Sublinear scale norms imply sublinear discrepancy

Assume `b_j/q_j -> 0`. Fix a scale `j` first and write `N=tq_j+r`, where `0<=r<q_j`. Partition `[1,tq_j]` into `t` consecutive length-`q_j` windows. By (7),

\[
 |J(N)|\le t\bigl(b_j+|p_j-\beta q_j|\bigr)+r.
\]

The last term bounds the discrepancy on the remaining interval, since it has length `r` and binary increments. Thus

\[
 \limsup_{N\to\infty}\frac{|J(N)|}{N}
 \le\frac{b_j+|p_j-\beta q_j|}{q_j}.
\]

Now let `j` tend to infinity, using (6). This proves `J(N)=o(N)` without an external expansion or an interchange of limits.

Combining this with (4) proves the **two-supplier consumer**: if `mu_n>=-h(n)` for a nonnegative nondecreasing sublinear envelope, and the window norms are uniformly sublinear in their lengths, then

\[
 \eta_n=o(n),\quad J(N)=o(N),\quad D_{\rm cen}(n)=o(n).
\]

For the last step, `n<d(n)<=2n+1` gives

\[
 \frac{|J(d(n))|}{n}
 =\frac{|J(d(n))|}{d(n)}\frac{d(n)}n\longrightarrow0,
\]

and every term of (2), divided by `n`, tends to zero. Both suppliers remain open when this consumer is applied to canonical Chomp.

## 5. Divergent cumulative saving contracts the Pell scale

The following general analytic statement permits a fixed additive error. Let `b_j>=0` be any real sequence, and suppose, after a finite prefix,

\[
 b_{j+1}\le(2-\delta_j)b_j+b_{j-1}+C,
 \qquad 0\le\delta_j\le2,\quad C\ge0,
 \qquad\sum_j\delta_j=\infty.
\tag{10}
\]

Then `b_j/rho^j -> 0`, and hence `b_j/q_j -> 0`.

Set

\[
 x_j=b_j/\rho^j,\quad e_j=C/\rho^{j+1},\quad
 M_j=\max(x_j,x_{j-1}).
\]

Because `rho^2=2rho+1`, normalized coefficients sum to `1-delta_j/rho`; therefore

\[
 x_{j+1}\le(1-\delta_j/\rho)M_j+e_j.
\]

At the next step, discard its nonnegative saving and substitute this bound:

\[
 x_{j+2}\le(1-2\delta_j/\rho^2)M_j+(2/\rho)e_j+e_{j+1}.
\]

Put `c=min(1/rho,2/rho^2)>0` and `g_j=e_j+e_(j+1)`. Since `2/rho<1`, both entries of `M_(j+2)` satisfy

\[
 M_{j+2}\le(1-c\delta_j)M_j+g_j,
 \qquad 0\le c\delta_j<1,\quad\sum_jg_j<\infty.
\tag{11}
\]

At least one parity class has divergent sum of `delta_j`. Iterate (11) over that class. Products of the contraction factors tend to zero, since `log(1-u)<=-u`. In the expanded affine recursion, each fixed finite collection of error terms is multiplied by a tail product tending to zero. The remaining terms are bounded by the corresponding tail of the convergent series `sum g_j`. Therefore `M_j -> 0` on that parity. Its pairs `(x_j,x_(j-1))` contain every sufficiently late `x_k`, so the entire sequence tends to zero. This proves (10).

For the exact nonnegative slack (9), define

\[
 \delta_j=\min\left(2,\frac{S_j}{\max(1,b_j)}\right).
\tag{12}
\]

One always has `delta_j*b_j<=S_j`, including `b_j=0` and real `0<b_j<1`. Thus divergence of the sum in (12) implies (10) with `C=0`. In the window application, Section 4 then gives `J(N)=o(N)`. An average over starts cannot replace the maximum-norm assumption; the inequality must control every start through `b_j`.

A fixed coefficient saving is a special case. If eventually `b_(j+1)<=a*b_j+b_(j-1)+C` with `0<a<2`, put `u_j=b_j+C/a`. Then `u_(j+1)<=a*u_j+u_(j-1)`, and induction against a sufficiently large multiple of `lambda_a^j`, where `lambda_a=(a+sqrt(a^2+4))/2`, gives `b_j=O(lambda_a^j)=o(q_j)`. At the included endpoint `a=0`, parity-wise iteration gives only `O(j)` when `C>0`, which is still `o(q_j)`; a bounded `O(1)` rate at that endpoint would be false.

## 6. Exact magnitude shortfall and cancellation

At any start in (8), write the three child defects as `x,y,z`. Define

\[
 \operatorname{Short}_j(s)
 =(b_j-|x|)+(b_j-|y|)+(b_{j-1}-|z|),
\]

\[
 \operatorname{Cancel}_j(s)=|x|+|y|+|z|-|x+y+z|.
\]

Every shortfall term is nonnegative. If `P` is the sum of the positive child values and `N` the sum of absolute values of the negative children, then

\[
 \operatorname{Cancel}_j(s)=P+N-|P-N|=2\min(P,N)\ge0.
\]

Adding the definitions gives, at every start,

\[
 \operatorname{Short}_j(s)+\operatorname{Cancel}_j(s)
 =2b_j+b_{j-1}-|W_{j+1}(s)|.
\]

Taking the minimum over starts, which is attained at a parent maximizer, yields

\[
 S_j=\min_s\bigl(\operatorname{Short}_j(s)+\operatorname{Cancel}_j(s)\bigr).
\tag{13}
\]

Thus `S_j=Short_j(s)+Cancel_j(s)` is an equality at a maximizing parent, not at an arbitrary start. Zero slack means that some parent has all three child magnitudes at their respective maxima and all nonzero children have one sign. Positive slack requires a shortfall or opposite-sign mass at every maximizing candidate. The identity alone supplies no divergent amount of slack; that is the additional hypothesis needed in (12).

For example, a uniform lower bound `Short+Cancel>=epsilon_j*max(1,b_j)` at all starts gives `delta_j>=min(2,epsilon_j)`. If the nonnegative `epsilon_j` have divergent sum, the clipped sum also diverges: either infinitely many exceed two, or the tail is unclipped. This is a sufficient condition, not a canonical supplier theorem.

## 7. Finite Pell trees and oriented conservation

Fix `n>k>=1`. The complete tree rooted at `(n,s)` splits a node `(m,a)` of scale `m>=k+1` into

\[
 (m-1,a),\quad(m-1,a+q_{m-1}),\quad(m-2,a+2q_{m-1}).
\tag{14}
\]

Nodes of scales `k` and `k-1` are leaves. The associated consecutive target intervals partition the root interval. Induction with the same `2,1` recurrence gives `q_(n-k)` leaves of scale `k`, `q_(n-k-1)` leaves of scale `k-1`, and `q_(n-ell-1)` internal nodes using the slack `S_ell`, for each `k<=ell<=n-1`. The one-step case has two scale-`k` leaves, one scale-`k-1` leaf and one internal node, which fixes the indexing.

Fix one orientation `sigma` in `{+1,-1}` throughout the tree and define

\[
 G_\sigma(m,a)=b_m-\sigma W_m(a)\ge0.
\]

The child capacities sum to `b_m+S_(m-1)`, while their signed defects sum to `sigma*W_m(a)`. Hence

\[
 G_\sigma(m,a)+S_{m-1}=\sum_{\text{children }v}G_\sigma(v).
\tag{15}
\]

For any finite frontier obtained by expanding nodes, induction over those expansions proves

\[
 \sum_{v\text{ on frontier}}G_\sigma(v)
 =G_\sigma(n,s)+\sum_{u\text{ expanded}}S_{\operatorname{scale}(u)-1}.
\tag{16}
\]

For the complete tree put

\[
 \Lambda_{n,k}=\sum_{\ell=k}^{n-1}q_{n-\ell-1}S_\ell,
 \qquad C_{n,k}=q_{n-k}b_k+q_{n-k-1}b_{k-1}.
\tag{17}
\]

Choose a root attaining `b_n` and its sign; if `b_n=0`, either sign has zero root gap. Then (16) says that the sum of all oriented leaf gaps is exactly `Lambda_(n,k)`. Summing leaf capacities and signed defects also gives

\[
 b_n=C_{n,k}-\Lambda_{n,k}.
\tag{18}
\]

This identity does not assert that every leaf is nearly extremal. It does give, within this fixed tree, for every descendant node `v=(m,a)`,

\[
 G_\sigma(v)+\Lambda_{m,k}\le\Lambda_{n,k},
\]

where `Lambda_(k,k)=Lambda_(k-1,k)=0`. The reason is that the descendant leaves form a subset of the same root's leaves and all gaps are nonnegative. It is not a bound for unrelated nodes elsewhere in the word.

To see the two unsigned forms, set `H(v)=b_scale(v)-|W(v)|` and let `C(u)` be the sum of absolute child defects minus the absolute parent defect. The equality

\[
 G_\sigma(v)=H(v)+2|W(v)|\,1_{\{\sigma W(v)<0\}}
\]

and telescoping absolute values give

\[
 \Lambda_{n,k}
 =\sum_{\rm leaves}H(v)+2\sum_{\text{opposite-sign leaves}}|W(v)|
 =\sum_{\rm leaves}H(v)+\sum_{\rm internal}C(u).
\tag{19}
\]

In particular, for any `tau>0`, the total capacity of leaves with `G_sigma(v)>tau*b_scale(v)` is at most `Lambda_(n,k)/tau`.

## 8. Relative block slack and a coherent finite ray

Assume `b_ell>0` for `k<=ell<=n-1` and put

\[
 D_{k,n}=\sum_{\ell=k}^{n-1}\frac{S_\ell}{b_\ell}.
\]

The zero-slack recurrence implies `b_ell<=q_(ell-k)b_k+q_(ell-k-1)b_(k-1)`. The elementary identity

\[
 q_{a+c}=q_aq_c+q_{a-1}q_{c-1}\quad(a,c\ge0)
\]

follows by induction in either index, with `q_-1=0`. In particular `q_aq_c<=q_(a+c+1)`. Apply this separately to the two coefficients of the preceding envelope (the term containing `q_-1` is zero). It follows that

\[
 q_{n-\ell-1}b_\ell\le C_{n,k},\quad
 \Lambda_{n,k}\le D_{k,n}C_{n,k},\quad
 b_n\ge(1-D_{k,n})C_{n,k}.
\tag{20}
\]

For the stronger pathwise conclusion require `b_(k-1),...,b_n>0` and `D_(k,n)<1`. At a node define its normalized gap `g=G_sigma/b_m` and put `alpha_(m-1)=S_(m-1)/b_m`. Equation (15) says that the capacity-weighted average of the three child normalized gaps is

\[
 \frac{g(\text{parent})+\alpha_{m-1}}{1+\alpha_{m-1}}.
\]

Choose a child of minimum normalized gap, resolving ties from left to right. It satisfies

\[
 1-g(\text{child})\ge
 \frac{1-g(\text{parent})}{1+\alpha_{m-1}}.
\]

Beginning with the zero-gap maximizing root and iterating gives

\[
 g(v)\le1-\prod_{\rm ancestors}(1+\alpha)^{-1}
 \le\sum_{\rm ancestors}\alpha.
\]

Each block summand `S_ell/b_ell` is less than one, so `b_(ell+1)=2b_ell+b_(ell-1)-S_ell>b_ell`. Consequently `alpha_ell<=S_ell/b_ell`. The ancestors use distinct scales in the block, yielding

\[
 0\le G_\sigma(v)\le D_{k,n}b_m,\qquad
 \sigma W_m(a)>0,\qquad |W_m(a)|\ge(1-D_{k,n})b_m.
\tag{21}
\]

This constructs one coherent nested ray down to scale `k` or `k-1`; it does not make the discarded siblings near-extremal.

For integer window norms and slacks, suppose the capped sum in (12) is finite. Eventually `delta_j<1`. Either all norms vanish eventually, or a positive norm occurs on this tail. In the latter case `S_j/b_j<1`, so `b_(j+1)>b_j+b_(j-1)>=b_j`; positivity then persists. On that tail the cap is inactive and `sum S_j/b_j` converges. Given `0<epsilon<1`, choose `k` after positivity starts with tail sum less than `epsilon`. For every `n>k`, (21) gives a finite same-sign ray with relative error at most `epsilon`. Taking `n-k` unbounded gives arbitrarily long such rays.

No single infinite ray in the original word follows. The maximizing starts may differ without bound, giving an infinitely rooted forest. Even a disjoint union of one finite path of each length has arbitrarily long paths and no infinite path. A common-root or compatible-translation hypothesis would be additional content. A translation-limit word also need not carry the actual game's owner and victim data.

## 9. Physical inventories behind a positive extremizer

For the remaining conditional mechanism, return to the canonical game. A blocker day `u in S` has its unique victim column `s(u)` with `F(u,s(u))=u`. Different blocker days have different victims because retired columns copy permanently. A diagonal owner is its integer row label `a`, with target `d(a)`; injectivity makes that owner unique. These facts refine the following counts into actual records, but do not themselves provide a response map.

For a selected transition `j` and start `s`, let the child target intervals be

\[
 I_0=(s,s+q_j],\quad I_1=(s+q_j,s+2q_j],\quad
 I_2=(s+2q_j,s+2q_j+q_{j-1}].
\]

Their scales are `ell_0=ell_1=j`, `ell_2=j-1`. For child `i`, write `P_i=p_(ell_i)` and `R_i=q_(ell_i)-p_(ell_i)`. Let `B_i` be the list of blocker days in `I_i`, sorted increasingly by day. Let `O_i` be the list of all diagonal owners whose targets lie in `I_i`, sorted increasingly by the owner label, not by target. The range partition gives

\[
 |B_i|+|O_i|=q_{\ell_i},\qquad
 w_i=|B_i|-P_i=R_i-|O_i|.
\]

Define the **fixed quota tails**

\[
 \mathrm{ExtraBlock}_i=\operatorname{drop}(P_i,B_i),\qquad
 \mathrm{ExtraOwner}_i=\operatorname{drop}(R_i,O_i).
\]

Dropping more entries than a list contains leaves the empty list. Thus their sizes are respectively `(w_i)_+` and `(-w_i)_+`. The orders and quotas are fixed before any response matching is sought. Across children, the owner lists combine as a disjoint set union and a sorted merge; they are not generally concatenated in owner chronology.

Each extra blocker is represented by `(day u,victim s(u))`; each extra owner by `(owner a,target d(a))`. Tag these records also by transition, selected parent and child. Define

\[
 D=\sum_i(w_i)_+,\quad E=\sum_i(-w_i)_+,\quad
 K=\sum_i(b_{\ell_i}-|w_i|),\quad T=2b_j+b_{j-1}.
\]

Here `D` counts extra-blocker records, `E` counts actual extra-owner-tail records, and `K>=0` is magnitude shortfall. If the parent is a **positive absolute maximizer**, meaning `W_(j+1)(s)=b_(j+1)>0`, then

\[
 D-E=b_{j+1},\quad D+E+K=T,\quad
 S_j=K+2E,\quad
 D=\frac{T-K+b_{j+1}}2\ge b_j-K/2.
\tag{22}
\]

The positive orientation matters. An arbitrary absolute maximizer may be negative, reversing the majority/minority roles.

## 10. The buffered, masked one-way response theorem

Fix before inspecting response success a set `I` of transitions, weights `0<omega_j<=1`, a fibre bound `C>=1`, an ordering of the tagged sources, and admissible response relations based on the intended game data. At each selected transition with `b_(j+1)>0`, require a positive absolute maximizer. One may fix the least such start under a predeclared location condition, require the theorem for all such starts, or state existence of a positive maximizer with a response witness in the already fixed relation. The location or sign condition is an assumption, not a consequence of small discrepancy.

At such a parent put

\[
 m_j=\max\left(0,\left\lceil\omega_jb_j-K_j/2\right\rceil\right).
\tag{23}
\]

The full extra-blocker union has at least `m_j` elements: (22), `omega_j<=1` and integrality of `D` prove this. In the unmasked version let `Q_j` be its first `m_j` records in child-then-day order. If an additional eligibility mask restricts the sources, the **masked version additionally assumes and checks that the eligible subset contains at least `m_j` actual extra-blocker records**; positive orientation guarantees availability in the full union only. Select its first `m_j` records in the fixed order. This makes masking and support explicit rather than hiding them in a cardinality count.

Suppose, whenever `b_j>0` and `b_(j+1)>0`, there is a map

\[
 \phi_j:Q_j\longrightarrow
 \mathrm{ExtraOwner}_0\mathbin{\dot\cup}
 \mathrm{ExtraOwner}_1\mathbin{\dot\cup}
 \mathrm{ExtraOwner}_2
\tag{24}
\]

whose pairs belong to the predeclared admissible relation and whose every fibre has size at most `C`. A target must be in the actual quota tail, not merely somewhere in its child's complete owner list. Then `m_j<=CE_j`, and (23) gives

\[
 CE_j+K_j/2\ge\omega_jb_j.
\]

Using `C>=1` and (22),

\[
 S_j=K_j+2E_j\ge\frac{2\omega_jb_j}{C}.
\tag{25}
\]

If `b_(j+1)=0`, no positive selector or response is needed, because `S_j=T>=2b_j` already gives (25). On an active scale `b_j>0`, the integer norm is at least one. Division by `max(1,b_j)=b_j` and clipping at two therefore preserve

\[
 \delta_j\ge2\omega_j/C.
\]

If `sum_(j in I,b_j>0) omega_j` diverges, Section 5 applies and proves `b_j/q_j -> 0`, and Section 4 proves `J(N)=o(N)`. No reverse owner-to-blocker map is needed under the positive-parent premise. The required orientation, eligible support, tail incidence and divergent active weights are all retained as suppliers.

The coefficient in (25) has exact inventory sharpness for a positive integer `C` and rational `omega`: choose a sufficiently divisible positive integer `b`, put `e=omega*b/C`, and use child values `(b,b,-e)` at saturated capacities `(b,b,e)`. Then `e` and `omega*b` are integers, `K=0`, `E=e`, the selected sample has size `omega*b=CE`, and a map with exactly `C` preimages per target attains `S=2e=2omega*b/C`. Irrational weights can be approached by rational examples; exact equality is not asserted for every real parameter choice. The inequality itself remains valid for real `C>=1`, but a fibre cardinality bound then effectively uses `floor(C)`, so the displayed coefficient need not be sharp for that real `C`. These are local inventory examples, not claims of canonical-word realizability.

The stronger full-response condition `D<=CE` would give, when `T>0`,

\[
 S/T=(K+2E)/(K+D+E)\ge2/(C+1),
\]

because `(C+1)(K+2E)-2(K+D+E)=(C-1)K+2(CE-D)>=0`. The buffer in (23) asks for fewer source records by letting already visible shortfall pay part of the slack.

## 11. Quantifiers and limits of the mechanism

An arbitrary map with the stated fibre bound suffices for the abstract counting implication, but presenting its existence as an independent game proof requires the predeclared incidence relation and an actual proof that its edges reach the quota tails. Choosing weights from the already desired value of `S_j`, or selecting only successful scales after the fact, would restate the target instead of supplying it. An average response over starts is also insufficient for an absolute maximizing window.

Scale tags permit the same absolute day or owner to occur in different scale-local inequalities. The proof does not subtract all these occurrences from one finite global resource pool, so it does not require cross-scale injectivity. Conversely, a proposed construction based on a finite set of single-use chronological tickets must justify its reuse or prove the required tail incidence independently at every tagged scale; the analytic theorem does not do so.

The six statements above do not prove a constant or logarithmic record-drop envelope, a divergent canonical Pell saving, an all-scale positive extremizer theorem, or a canonical bounded-fibre response. They prove exactly what follows once those indicated suppliers are present. No finite empirical window, scalar counterframe or infinite-ray compactness inference is used to fill a missing game premise.
