# Quantitative incompatibility of the two counting extremizers

The complete argument below defines every optimization variable and retains the finite counting inequalities and order of limits. Read it together with the [finite service-budget proof](counting-service-budget.md) and the [canonical foundation](../../audit/full/CANONICAL-FOUNDATIONS.md).

## 1. Result

Let A(x) count positive S-labels at most x, and d(n) be the diagonal of the
canonical positive-mex/carry recurrence for three-row Chomp. Define

    Q(b) = 12496 +112497b -24984b^2 -524992b^3 -237524b^4
                 +249993b^5 +87520b^6 -100006b^7 +25000b^8.

Let b_new be the unique zero of Q in [.469,.471]. Then

    liminf A(n)/n <= b_new,
    liminf d(n)/n <= 1/(1-b_new) < 1.886593095.

Exact rational root isolation gives approximately

    b_new              = .4699439942048371,
    1/(1-b_new)         = 1.8865930940634306.

No existence of a limit, limsup ceiling, or fast algorithm follows.

## 2. Inputs and notation

The [finite service-budget proof](counting-service-budget.md) supplies the complete baseline argument. Its sections 2 and 3 define U_N exactly and prove the finite service budget; section 5 derives the discrete square identity; sections 6 and 7 supply the baseline optimizer and bound. Thus the numbered inputs below are included in this release, rather than referred to an unavailable draft.

Write S={p_1<p_2<...}, and s_j for the column that retires at p_j.
The canonical facts needed for the new part are:

    s_j <= 2j-1,
    the s_j are distinct,
    s_j >= j + #{i : p_i+s_i < p_j}.                         (1)

The last fact counts the j distinct predeath booker columns and the
chronologically unusable columns, all strictly below s_j. These two sets
are disjoint. The service-budget proof derives these facts from the actual recurrence in its sections 1 and 4.

Fix

    469/1000 <= a <= 471/1000,
    A(x) >= a*x-C for all x>=0, with a fixed C>=0.

Put

    E(x)=A(x)-a*x+C >=0,    e_j=E(p_j),
    h=1+2a,  g=1+a,  lambda=1-a.

At the START of row N put

    m=R(N-1),  R(x)=x-A(x),
    u=#live columns r<m,    W=sum of their indices,
    K=m-u,
    I={j:p_j<N and s_j<m},  |I|=K,
    S_N=sum_{p_j<N} e_j,
    B_ret=hW+gK^2-hm^2/2,
    B_peak=(m-2g*u)_+^2/(2lambda).

All uses of the symbol S_N below refer to this weighted sum, not the set S.

For these quantities the linked service-budget proof supplies, under its high-sample range
condition, the finite inequalities

    U_N >= m*u-a*W-u^2/2 + L_N,                              (2)
    L_N >= S_N/a - E(N-1)^2/(2a) - O(N),                    (3)
    U_N = (1-2a)/(2(1-a))*N^2 + O(N).

The fixed-parameter constants in O(N) can depend on a,C. Equation (3)
is the exact discrete square identity with its linear terms bounded.

## 3. A nonnegative slack for each deadline

Define

    delta_j = e_j-2g*j+h*s_j+h.

Then delta_j>=0. To see this, e_i>=0 and s_i<=2i-1 give

    a*(p_i+s_i) <= h*i+C-a.

Consequently every positive i<=floor((j-e_j)/h) satisfies
p_i+s_i<p_j. If that floor is negative, it remains a valid lower bound
on the number of such i. Inserting this count into (1) gives

    delta_j >= h*floor((j-e_j)/h)-(j-e_j)+h >=0.             (4)

There is a useful stronger version. If G further ranks lie above
(j-e_j)/h and obey p_i+s_i<p_j, the same proof gives

    delta_j >= h*G.                                        (5)

These extra ranks must be distinct from the baseline ranks; this
disjointness will be checked explicitly below.

Put

    Gamma = sum_{j in I}j - K(K+1)/2 >=0,
    X = S_N-B_ret.

Since sum_{j in I}s_j=m(m-1)/2-W, exact expansion gives

    X = sum_{j in I}delta_j +2g*Gamma
        +sum_{j not in I,p_j<N}e_j +hm/2-a*K.

The last term is at least m/2. In particular,

    X>=0,   sum_{j in I}delta_j<=X,   Gamma<=X/(2g).         (6)

If an interval of ranks lies below b*m<K, the number of its ranks absent
from I is at most Gamma/(K-b*m). Indeed, every omitted rank j<=K
must be replaced by a rank above K, costing at least K+1-j in Gamma.
This argument needs no monotonicity of the physical victim columns.

## 4. The backward ramp leaves a separate budget for early ranks

For this section and the next assume

    332/1000 <= u/m <= 336/1000.                            (7)

Thus K>=.664m>0. Let J be the largest rank in I. It obeys J>=K.
From (4) and s_J<=m-1,

    e_J >= 2g*J-hm.

The deadline labels are distinct integers, so, for j<=J,

    e_J-e_j <= lambda*(J-j).

It follows for j<=K that

    e_j >= R_j :=
      ((2g-lambda)*K-hm+lambda*j)_+.

Set H=m-2g*u and

    j0=K-H/lambda=(-a+(1+3a)*u/m)*m/lambda.

Throughout the parameter rectangle (7), .58m<j0<K. The first inequality
is certified rationally; H>0 gives the second. Thus R_j vanishes for
j<=.58m. Since R_j is increasing, its right-endpoint sum dominates its
integral:

    sum_{j=1}^K R_j >= H^2/(2lambda)=B_peak.

All these deadlines occur before N, because J is a past deadline.
Therefore, putting Y=S_N-B_peak,

    Y>=0,   sum_{.56m<=j<=.58m}e_j <=Y.                    (8)

This uses the SAME excess mass as the old proof. It does not add two
overlapping lower bounds: it identifies mass outside the ramp's support.

## 5. Two rank intervals force additional chronological exclusions

Call a source rank good when

    .30m<=i<=.31m,  i in I,  delta_i<=m/20,

and a target rank good when

    .56m<=j<=.58m,  j in I,  e_j<=m/100.

Let their counts be G_s,G_t. The missing-rank estimate following (6),
Markov's counting inequality, and (8) give

    G_s >= (.01m-2-21X/m)_+,
    G_t >= (.02m-2-4.1X/m-100Y/m)_+.                       (9)

Here the missing-rank coefficients use, on the entire parameter rectangle,

    2g*(.664-.31)>1,
    4.1*2g*(.664-.58)>1.

The two subtracted units safely cover rounding of interval endpoints.

Every good source is an EXTRA unusable predecessor for every good target.
Indeed, set D=1+2ag/h. The definition of delta_i gives exactly

    i+a*s_i-e_i
      =D*i+(a/h)*delta_i-(1+a/h)*e_i-a
      <= .31D*m + a*m/(20h)
      < .55m
      <= j-e_j.

Since a*p_i=i+C-e_i, this is precisely p_i+s_i<p_j.
Also i>=.30m>.58m/h>=j/h>=(j-e_j)/h. Hence these sources
are disjoint from the baseline ranks in (4). The two needed strict
numeric inequalities hold throughout [.469,.471], by the exact rational polynomial checks linked below.

Equation (5) and then (6) now imply

    X >= h*G_s*G_t >= (969/500)*G_s*G_t.

For x,y,l_1,l_2>=0,

    (x-l_1)_+*(y-l_2)_+ >= xy-y*l_1-x*l_2.

Apply this to (9). With h0=969/500,

    X >= h0*(m^2/5000 - .461X - Y - .06m).

The coefficient comparison 1+.461h0<=h0 is strict:

    h0*(1-.461)-1 = 22291/500000 >0.

As X>=0, it follows that

    X+Y >= m^2/5000 - .06m.

We have proved the new finite inequality

    S_N >= (B_ret+B_peak)/2 + m^2/10000 - .03m.             (10)

Its premises are exactly the stated canonical facts, nonnegative E, and
the parameter rectangle. No density limit or victim-order premise enters.

## 6. A uniform improvement of the old relaxed minimum

Put v=u/m, z=W/m^2, q=S_N/m^2,
r=B_ret/m^2 and p=B_peak/m^2. Inside (7), (10) says

    r<=2q-p-1/5000+.06/m,   q>=p.

As 1/a-2a/h>0, substituting this inequality for r=hz+g(1-v)^2-h/2
shows

    v-v^2/2-a*z+q/a
      >= J_a(v)+a/(5000h)-.06a/(hm),                        (11)

where the old relaxed objective is

    J_a(v)=a/(2h)+k*(v-v^2/2)+w*(1-2g*v)_+^2/2,
    k=(1-2a^2)/h,
    w=(h-a^2)/(a*h*(1-a)).

Its old minimum is

    M(a)=V(a)/(2D0(a)),
    V(a)=3+7a+a^2-5a^3-2a^4+2a^5,
    D0(a)=4+15a+17a^2+2a^3-6a^4.

On all [.469,.471], exact polynomial certificates establish:

* the unique minimizing v_* lies strictly between .332 and .336;
* J_a(.332)-M(a)>1/25000;
* J_a(.336)-M(a)>1/25000;
* a/(5000h)>1/25000.

Below 1/(2g), J is strictly convex. Above that breakpoint it is
nondecreasing on v<=1, and the breakpoint exceeds .336. Thus outside
(7) the old bound already gains 1/25000. Inside (7), (11) gains at
least that much, with an O(m) error before normalization.

Combining (2),(3) with these two cases yields

    U_N >= m^2*(M(a)+1/25000)
               -E(N-1)^2/(2a)-O(N).                       (12)

This is a uniform positive improvement of the relaxed minimum in the
stated interval of a. It is not just nonattainment at one exact optimizer.

## 7. Limit order and diagonal transfer

Let beta=liminf A(n)/n. The old theorem gives beta<=.46995152763790.
If beta<=.469, the new conclusion is automatic. Otherwise fix
.469<a<beta. A global constant C with E>=0 exists.

Take a subsequence A(N)/N->beta. Then

    m/N->1-beta,  E(N-1)/N->beta-a.

The old high-sample range condition holds eventually along this sequence;
its endpoint is B=floor((N-C)/(1-a)) and N+m-1<=B.
Applying (12) at FIXED a gives

    (1-2a)/(2(1-a))
      >=(1-beta)^2*(M(a)+1/25000)-(beta-a)^2/(2a).

Only now let a increase to beta. No error estimate uniform in C or in
a->beta is needed. We obtain

    P(beta) >= (1-beta)^3*D0(beta)/12500,

where the old polynomial is

    P(b)=1+9b-2b^2-42b^3-19b^4+20b^5+7b^6-8b^7+2b^8.

Thus Q(beta)=12500P(beta)-(1-beta)^3D0(beta)>=0.
Exact rational polynomial checks show Q is strictly decreasing on [.469,.471]
and has one zero there, namely b_new. Hence beta<=b_new.

Finally, if liminf d(n)/n>1/(1-b_new), choose c strictly between them.
The eventual bound d(n)>=c*n-O(1), together with injectivity, implies
R(x)<=x/c+O(1). Then liminf A(x)/x>=1-1/c>b_new, a contradiction.


## Exact algebra and reproducibility

All decimal constants appearing in interval endpoints, thresholds and margins are terminating decimals and therefore exact rational numbers. Polynomial coefficients are in ascending order in the checker. A polynomial is transformed from [l,r] to [0,1] and written in the Bernstein basis. Strict positivity of every Bernstein coefficient proves positivity throughout the full interval.

The [checker](../../audit/prepublication/root/check_algebra.py) verifies the displayed degree-eight expansion, positivity of the optimizer denominator, both vertex bounds, the ramp support and its positivity, the source-time margin, baseline disjointness, missing-rank constants, objective slopes, both outer gains and strict monotonicity of Q. It also isolates the unique root by exact rational bisection and verifies 1/(1-b_new) < 1.886593095. The [fresh result](../../audit/prepublication/root/exact-algebra-checks.json) records those checks. This algebra supplements the counting proof; it does not replace it.
