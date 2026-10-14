# The finite counting service budget and baseline bound

This proof supplies the service budget and baseline estimate used in the [counting extremizer theorem](counting-extremizer-proof.md). All counts exclude the label zero. The parameter alpha is fixed before any limit is taken.

Let beta_star be the unique zero on [2/5,1/2] of

    P(b) = 1+9b-2b^2-42b^3-19b^4+20b^5+7b^6-8b^7+2b^8.

The argument proves liminf A(n)/n <= beta_star and liminf d(n)/n <= 1/(1-beta_star). It does not assume an ordered diagonal inverse or prove convergence. In the proof below the same root is written beta_*.

## 1. Definitions and established game core

For q>=r>=0, use the complete positive-mex/carry recurrence. Its history
and same-row prefix at (q,r) are respectively

    H(q,r)={d(a):a<r} union {f(a,r):r<=a<q},
    C(q,r)={f(q,b):b<r},      d(q)=f(q,q).

For q>r, if f(q-1,r)<q the value is carried; otherwise the value is the
positive mex of H(q,r) union C(q,r). Write D=image(d), S=positive integers
outside D, and R(x)=#(D intersect [1,x])=x-A(x).

We use these established facts of the actual game:

1. d is injective; each row consists of distinct positive values and has
   maximum d(q)>q. A noncarry value is at least q.
2. A column's pre-retirement awards are distinct and avoid its inherited
   diagonal labels. The mex envelope is f(q,r)<=q+r+1.
3. Each p in S has exactly one victim s(p)<p with f(p,s(p))=p. That column
   carries permanently afterward. These victims are distinct for distinct p.
4. Row-start propagation: if f(p,s)=p, then p occurs in a column below s
   in every row s<q<p.

The [canonical foundation](../../audit/full/CANONICAL-FOUNDATIONS.md) derives these inputs from the actual-game definitions and names their exact Lean bridges. In particular, row-start propagation, persistent COPY, positive MEX coverage and diagonal maximality are actual-game facts.

For clarity, the two booker consequences used below follow directly.
If p in S and q<p, then p occurs in row q exactly when d(q)>p, by the
diagonal mex and row maximality. All R(p) owners of D-labels <=p have
index below p, since d(a)>a. Therefore p has precisely p-R(p)=A(p)
predeath occurrences. They occupy distinct columns. Every such column
is below s(p): for q<s this is automatic, at q=s the diagonal is in D,
and for s<q<p use row-start propagation and row injectivity. Call this
BOOKER-BELOW. Propagation in the p-s-1 intervening rows further gives
p-s-1<=s, hence s(p)>=(p-1)/2.

Enumerate S by p_1<p_2<... and write s_j=s(p_j). Diagonal injectivity
and d(q)<=2q+1 imply R(x)>=ceil(x/2), so A(x)<=floor(x/2) and p_j>=2j.

## 2. The upper service budget retains the full excess area

Let G(N) be the number of physical nonbirth D-service cells in rows q<N.
Every S-label below d(q) occurs in row q by diagonal mex, and no greater
label occurs by maximality. Removing the single diagonal birth gives

    G(N)=sum_(q<N)[q-A(d(q))].                                (1)

Fix 0<alpha<1/2 and C>=0 with A(x)>=alpha*x-C for all nonnegative x.
Put lambda=1-alpha and E(x)=A(x)-alpha*x+C>=0. Constants in O(N) below
may depend on this fixed alpha,C, but never on N.

Let b_j be the jth smallest element of the SET D, indexed from j=1.
The first N emitted diagonal labels form an N-element subset of D;
sorting this subset and using monotonicity of A gives

    sum_(q<N) A(d(q)) >= sum_(j=1)^N A(b_j)
                     =sum_(j=1)^N (b_j-j).

Thus G(N)<=N^2-sum b_j. The layer-cake identity is exact:

    sum_(j=1)^N b_j=sum_(x>=0)(N-R(x))_+.

For sufficiently large N put B=floor((N-C)/lambda). For 0<=x<=B,
N-R(x)=N-C-lambda*x+E(x)>=0. Keeping these terms yields

    G(N)<=U_N-sum_(x=0)^B E(x),                              (2)
    U_N=N^2-(B+1)(N-C)+lambda*B(B+1)/2
       =[(1-2alpha)/(2(1-alpha))]N^2+O(N).

The coefficient of the area is exactly one. No order of emitted diagonals
has been assumed.

## 3. Current live histories, and payment for static and birth labels

Let F_N(a) count columns 0<=r<a live at the START of row N. A column
retiring at N is included. Put

    m=R(N-1),   u=F_N(m),
    W=sum_(r<m, r live at N) r.

All m owners with d(a)<N have a<N. Each old live column r<N has a history
H(N,r) containing N distinct positive labels: r inherited labels and
N-r awards. Its missing labels below N are exactly

    {p in S:p<N, s(p)<=r}.                                   (3)

Indeed, a D-label below N cannot occur in the row-N prefix, where sub-N
values are carried S-labels, and hence must lie in the history. An S-label
with victim at most r was not booked by this live column, by BOOKER-BELOW.
For a victim above r, inspect column r in row p: it was live then, and its
current service exceeds p, since p occurs later in that row. The mex rule
therefore forces p into its history.

Consequently the future-label part Q_r=H(N,r) intersect [N,infinity) has
size one plus the number of columns <=r retired before N. If r_i is the
ith live column (i=1,2,...), this size is r_i+2-i. The envelope on inherited,
birth and later awards gives Q_r subset [N,N+r].

Let FD_r count actual nonbirth D-awards represented in Q_r. Removing
possible S-labels and all possible inherited/birth D-labels gives

    FD_r>=|Q_r|-[A(N+r)-A(N-1)]-#{a<=r:d(a)>=N}.             (4)

Completed D-labels force a separate count

    C_N=sum_(a:d(a)<N) F_N(a).

For each pair (a,r), r<a live at N, mex forces d(a) into the column's
history. It is neither inherited nor that column's birth. Distinct pairs
give distinct physical nonbirth cells. Their labels are <N, whereas the
labels counted by FD_r are >=N; the two counts are disjoint.

On the prefix r<m, the total static/birth subtraction in (4) is

    T=sum_(a<m,d(a)>=N)[u-F_N(a)].

There are exactly as many missing completed owners below m as completed
owners at or beyond m. Direct expansion gives the exact identity

    C_N-T=sum_(a<m)F_N(a)
               +sum_(a>=m,d(a)<N)[F_N(a)-u]
           >=sum_(a<m)F_N(a).                               (5)

This pays the entire subtraction without ordering the diagonal owners.

Sum (4) over the u live columns r<m and use (5). Since their ranks are
1 through u, sum |Q_r|=W+3u/2-u^2/2. Also

    sum_(a<m)F_N(a)=(m-1)u-W,
    A(N+r)-A(N-1)=alpha(r+1)+E(N+r)-E(N-1).

Combine with (2). If N+m-1<=B, the distinct samples E(N+r) are all terms
of its area and cancel with coefficient one. The whole low area remains:

    m*u-alpha*W-u^2/2+L_N<=U_N,
    L_N=sum_(x=0)^(N-1)E(x).                                (6)

The terms dropped to obtain (6) are nonnegative: (1/2-alpha)u,
u*E(N-1), the last surplus in (5), and unsampled high excess area.
This is a finite statement about currently live columns, not a limit or
an assumption of immortality.

## 4. Chronologically unusable columns sharpen the victim bound

First s_j<=2j-1: in row p_j every live column before the victim must have
booked p_j earlier. The prefix is covered by at most j prebookers and at
most j-1 columns already retired.

A column s_i retiring at p_i never awards above p_i+s_i. Before death
this follows from the mex envelope; after death its value is p_i. If
p_i+s_i<p, it therefore never booked p. Moreover it is below s(p), since

    2s_i+1<=p_i+s_i<p,    s(p)>=(p-1)/2.

These unusable columns are distinct from the A(p) booker columns, and
both sets lie strictly below the victim. Hence

    s(p)>=A(p)+#{i:p_i+s_i<p}.                               (7)

Since i=A(p_i)>=alpha*p_i-C and s_i<=2i-1,
p_i+s_i<=(1/alpha+2)i+O(1). Thus (7) implies

    s(p)>=A(p)+[alpha/(1+2alpha)]p-O(1).                     (8)

Set h=1+2alpha and g=1+alpha. Using E(p_j)=j-alpha*p_j+C,
(8) is equivalently the useful lower constraint

    E(p_j)>=2g*j-h*s_j-O(1).                                (9)

All constants here are uniform in the deadline rank.

## 5. Past retirements force low excess: a first moment and a backward ramp

There are K=m-u already-dead columns below m, with distinct deadline
ranks and deadlines p<N. The sum of their physical indices is
m(m-1)/2-W. Summing (9), and using a rank sum at least K(K+1)/2, gives
for the FULL low S-sample sum

    S_N:=sum_(p in S,p<N)E(p) >= B_ret-O(N),
    B_ret=h*W+g*(m-u)^2-h*m^2/2.                            (10)

We may pass from the selected subset to the full sum because E>=0.

For a second estimate, suppose K>0 and let J be the largest selected
deadline rank. Then J>=K, p_J<N, and s_J<m. Equation (9) gives

    E(p_J)>=2g*J-h*m-O(1)>=H-O(1),
    H=m-2g*u.                                               (11)

For every j<=J, distinct increasing deadlines obey p_J-p_j>=J-j, so

    E(p_J)-E(p_j)=(J-j)-alpha*(p_J-p_j)
                   <=(1-alpha)(J-j).                        (12)

Thus a high excess at p_J forces a backward ramp through all preceding
S-ranks, including ranks whose victims were not selected. Its width fits
inside ranks 1 through J up to O(1), because p_J>=J implies
E(p_J)<=(1-alpha)J+C. Summing the nonnegative ramp gives

    S_N>=B_peak-O(N),
    B_peak=(m-2g*u)_+^2/[2(1-alpha)].                        (13)

The discrete triangular-sum and initial-boundary errors are O(N), for
fixed alpha,C; replacing E(p_J) by H-O(1) has the same error size. If K=0,
then H<=0, so (13) follows from S_N>=0 without defining J.

The two estimates concern the SAME mass. Therefore we take their maximum,
not their sum. For t>=1, Delta E(t)=1_S(t)-alpha. The exact square identity is

    S_N=alpha*sum_(t=1)^(N-1)E(t)
         +[E(N-1)^2-E(0)^2]/2
         +sum_(t=1)^(N-1)(Delta E(t))^2/2.                  (14)

It follows by summing 2E(t)Delta E(t)=E(t)^2-E(t-1)^2+(Delta E(t))^2.
The last sum is O(N). Combining (10),(13),(14) therefore yields

    L_N>=max(B_ret,B_peak)/alpha
               -E(N-1)^2/(2alpha)-O(N).                    (15)

The endpoint square is retained. All these samples have p<N and were
not used in cancelling the high samples N+r in Section 3.

## 6. Joint optimization of the finite inequality

For m>0 put v=u/m and z=W/m^2. Apart from the endpoint cost in (15),
the normalized left side of (6) is bounded below by

    v-v^2/2-alpha*z
      +max(h*z+g*(1-v)^2-h/2,
            (1-2g*v)_+^2/[2(1-alpha)])/alpha.               (16)

Minimizing over every real z enlarges the physical feasible set and is
a valid lower relaxation. The z-slope is -alpha below the crossing of
the two branches and h/alpha-alpha>0 above it. At the crossing (16) is

    J_alpha(v)=alpha/(2h)+k*(v-v^2/2)
                          +w*(1-2g*v)_+^2/2,
    k=(1-2alpha^2)/h,
    w=(h-alpha^2)/(alpha*h*(1-alpha)).                       (17)

For 2/5<=alpha<1/2, k,w>0. On v>=1/(2g), J is nondecreasing since its
derivative is k(1-v). Below that breakpoint J is strictly convex, with
vertex

    v_*=(2g*w-k)/(4g^2*w-k).

This is positive, since 2g(h-alpha^2)>alpha(1-alpha)(1-2alpha^2), and
v_*<1/(2g) follows from (2g-1)k>0. The global minimum on 0<=v<=1 is

    M(alpha)=[3+7alpha+alpha^2-5alpha^3-2alpha^4+2alpha^5]
               /[2(4+15alpha+17alpha^2+2alpha^3-6alpha^4)]. (18)

The denominator is positive on [2/5,1/2]. Physical first-moment and
rank-spacing constraints have been relaxed, not asserted to attain this
minimum. Equations (6),(15)--(18) give the finite inequality

    U_N >= m^2*M(alpha)-E(N-1)^2/(2alpha)-O(N).               (19)

## 7. Fixed-parameter limit order, root, and diagonal transfer

Let beta=liminf A(N)/N<=1/2. If beta<=2/5, the baseline density conclusion is
automatic. Otherwise fix 2/5<alpha<beta. A finite global C as used above
exists by the definition of liminf. Choose a subsequence A(N)/N -> beta.
Then

    m/N -> 1-beta,   B/N -> 1/(1-alpha),
    E(N-1)/N -> beta-alpha.

The range condition N+m-1<=B eventually holds: 2-beta<8/5 while
1/(1-alpha)>5/3. Divide (19) by N^2 at this FIXED alpha and take the
subsequence limit:

    (1-2alpha)/(2(1-alpha))
       >=(1-beta)^2*M(alpha)-(beta-alpha)^2/(2alpha).         (20)

Only now let alpha increase to beta. The endpoint cost tends to zero;
there is no exchange of limits requiring uniform error constants. With

    V(b)=3+7b+b^2-5b^3-2b^4+2b^5,
    D0(b)=4+15b+17b^2+2b^3-6b^4,

the resulting necessary inequality is

    (1-2beta)D0(beta)-(1-beta)^3 V(beta)=P(beta)>=0.          (21)

On [2/5,1/2],

    P'(b)=9-4b-126b^2-76b^3+100b^4+42b^5-56b^6+16b^7
          <=9-4b-95b^2-76b^3-48b^6<0.

Here use 100b^4<=25b^2, 42b^5<=6b^2 and 16b^7<=8b^6.
The endpoint signs are positive at 2/5 and negative at 1/2. Exact integer
evaluation certifies

    .46995152763789 < beta_* < .46995152763790,
    1.88661990769183 < 1/(1-beta_*) < 1.88661990769187.

The strict derivative estimate above proves uniqueness. The displayed decimal bracket is verified by substituting its two rational endpoints in P; it is not a floating-point assumption.
Therefore (21) implies beta<=beta_*.

Finally, if liminf d(n)/n>c, then d(n)>=c*n-O(1), whence injectivity
gives R(x)<=x/c+O(1) and liminf A(x)/x>=1-1/c. If the diagonal liminf
exceeded 1/(1-beta_*), choose c strictly between them to contradict the
density bound. This proves the baseline bound without assuming an inverse ordered sequence.

