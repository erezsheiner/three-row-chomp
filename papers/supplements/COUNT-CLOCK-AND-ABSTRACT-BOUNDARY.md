# Count-clock implication and its abstract boundary

These are statements about an injective integer sequence. The canonical game is an intended application only if the stated additional suppliers are proved. This supplement defines the actual counterexample and fills the compactness/counting steps missing from the short release summaries.

## Conditional count-clock theorem

Let \(d:\mathbb N_0\to\mathbb Z_{>0}\) be injective, with \(n<d(n)\le2n+1\). Let \(A(x)\) count positive integers at most \(x\) outside the **entire** image of \(d\), linearly interpolated between integers. Put

\[
Q(n)=3n+A(n)-2d(n),\quad
u_n=[A(d(n-1))-A(d(n))]_+\quad(n\ge1).
\]

Assume signed balance \(\sum_{n<N}Q(n)=o(N^2)\), and

\[
\lim_{K\to\infty}\limsup_{N\to\infty}\frac1N\sum_{n=1}^N(u_n-K)_+=0.
\]

Then \(Q(n)=o(n)\). Neither assumption is proved here for canonical Chomp.

Define \(g(n)=(3n+A(n))/2\), so \(3/2\le g(n)-g(n-1)\le2\), and \(E(n)=A(d(n))-A(g(n))\). Because \(A\) is increasing and 1-Lipschitz,

\[
E(n-1)-E(n)\le u_n+2\le K+2+(u_n-K)_+.
\]

Suppose \(E(N)\ge\eta N\) along unbounded \(N\). Choose a fixed \(K\) such that the clipped tail through (2N) is at most \(\eta N/4\) for all sufficiently large \(N\). Next choose \(0<\delta<1/2\) with \((K+2)\delta\le\eta/4\). Summing the last inequality gives \(E(j)\ge\eta N/2\) on \(N\le j\le N+\lfloor\delta N\rfloor\). Positive \(E\) implies \(d(j)-g(j)\ge E(j)\), hence \(Q(j)=2(g(j)-d(j))\le-\eta N\). This proportional window has sum at most \(-\eta\delta N^2+O(N)\), whereas its sum is the difference of two signed-balance prefixes, hence \(o(N^2)\), a contradiction. If \(E(N)\le-\eta N\), use the same inequality backwards on \(N-\lfloor\delta N\rfloor\le j\le N\); then \(E(j)\le-\eta N/2\), \(Q(j)\ge\eta N\), with the same contradiction. Therefore \(E(n)=o(n)\). In particular, for each fixed \(C_0>0\), \(max_{i\le C_0N}|E(i)|=o(N)\): a fixed finite initial segment is bounded, and the remaining terms are bounded by \(\varepsilon C_0N\).

This clock tracking must still be converted into pointwise label tracking; strict increase of the scaled count is the missing ingredient. It cannot be assumed.

Let \(R(x)=\lfloor x\rfloor-A(x)\) at integers, \(M_N=\sum_{q<N}(q-A(q))\), and \(D_N=\sum_{i<N}(d(i)-N)_+\). Every label through (N-1) has owner \(i<N\), by \(i<d(i)\). Double counting gives

\[
M_N=\sum_{i<N}(N-d(i))_+,\quad
\sum_{i<N}d(i)=N^2-M_N+D_N,
\]

and consequently

\[
S_2(N):=\sum_{n<N}(Q(n)+2)=M_N-2D_N.
\]

Of the \(N\) values emitted by owners \(0,\ldots,N-1\), exactly (A(N-1)+1) lie at least \(N\); each is at most (2N-1). Thus \(D_N\le N(A(N)+1)\). Also \(M_N\ge N(N-1)/2-NA(N)\). Combining gives

\[
A(N)\ge N/6-5/6-S_2(N)/(3N),
\]

so signed balance implies \(liminf A(N)/N\ge1/6\).

For any diverging scale sequence, the functions \(a_N(x)=A(Nx)/N\) have a subsequence converging locally uniformly to a continuous, increasing, 1-Lipschitz \(a\), with \(a(0)=0\) and \(a(x)\ge x/6\). This follows by equicontinuity, boundedness on each compact interval and diagonal subsequence extraction. Suppose \(a\) has a nontrivial plateau. Its maximal level interval is ([l,r]), with \(0<l<r<\infty\): the lower bound rules out a positive-length zero plateau or an unbounded plateau.

Choose \(0<\varepsilon<(r-l)/20\), with \(l-\varepsilon>0\). Since \(a\) is constant on the plateau, the integer label interval \([(l+\varepsilon)N,(r-\varepsilon)N]\) contains \((r-l-2\varepsilon)N+o(N)\) diagonal labels. Their owners satisfy \(lN/3<i<rN\) eventually, using \(i<d(i)\le2i+1\). Uniform clock tracking gives

\[
A(g(i))/N=A(d(i))/N+o(1)\to a(l).
\]

The values of \(a\) strictly below \(l\) and strictly above \(r\) bracket this plateau level. Local uniform convergence therefore forces all these (g(i)/N) into \((l-\varepsilon,r+\varepsilon)\) eventually. But \(g\) increments at least (3/2), so this interval contains at most \((2/3)(r-l+2\varepsilon)N+1\) of them. This is smaller than the diagonal-label count by the choice of \(\varepsilon\). Hence every scaling limit \(a\) is strictly increasing.

Finally suppose \(|Q(N)|\ge\eta N\) on a subsequence. Extract a scaling limit and limits \(z=d(N)/N\), \(w=g(N)/N\). They are in a fixed compact interval, and \(|z-w|\ge\eta/2\). Clock tracking and local uniform convergence yield \(a(z)=a(w)\), contradicting strict increase. This proves the conditional theorem without assuming convergence or a unique scaling limit.

## Explicit abstract counterexample to signed balance alone

For \(n\ge1\), write its residue modulo 170 as (10k+j), \(0\le k\le16\), \(0\le j\le9\). Call it low if

* \(j\in\{0,2,3,5,7\}\) for \(0\le k\le11\);
* \(j\in\{0,2,5,7\}\) for \(12\le k\le16\).

There are 80 low and 90 high residues. Set \(d(0)=1\), and

\[
d(n)=2\lfloor4n/5\rfloor+2\quad\hbox{on low residues},\qquad
d(n)=2\lfloor9n/10\rfloor+3\quad\hbox{on high residues}.
\]

The two phase images have opposite parity. Equal adjacent values of \(lfloor4n/5\rfloor\) can occur only at (5k,5k+1), and the rule never selects both for the low phase. Equal adjacent values of \(lfloor9n/10\rfloor\) can occur only at (10k,10k+1), always split between phases. Thus the sequence is injective. The isolated initial output 1 is not repeated. Direct integer bounds give \(n<d(n)\le2n+1\).

Each period translates the 80 low outputs by 272 and the 90 high outputs by 306, with no within-phase block overlap. Consequently

\[
R(x)=10x/17+O(1),\quad A(x)=7x/17+O(1).
\]

Let \(H(q)=\#\{a<q:d(a)>d(q)\}\). Uniform periodic counting in proportional owner intervals gives \(H(q)=q/17+O(1)\) on low rows and \(O(1)\) on high rows. The signed discrepancy is

\[
Q(q)=(18/85)q+O(1)\quad\hbox{low},\qquad
Q(q)=-(16/85)q+O(1)\quad\hbox{high}.
\]

The coefficient sum in a full period is \(80\cdot18-90\cdot16=0\). Complete periods have bounded accumulated error per period; a partial period contributes \(O(N)\). Thus \(sum_{q\le N}Q(q)=O(N)\), yet (Q(q)/q) has two distinct nonzero subsequential limits.

For completeness, the abstract multi-owner barrier is the numerical inequality

\[
\#\{a<q:q\le d(a)<d(q),\ A(d(q))-A(d(a))>H(a)+2(q-a)-1\}
\le2q+1-d(q)-H(q).
\]

For a high current row, low earlier owners can be forced only when \(a/q>107/109+O(1/q)\); the lower label guard is \(a/q\ge5/8+O(1/q)\). Their count is (16q/1853+O(1)), versus right side (q/5+O(1)). Earlier high owners contribute \(O(1)\). For low current rows, low-owner forcing would require \(a/q>114/109+O(1/q)>1\), and high-owner forcing would require \(a/q>114/107+O(1/q)>1\), while its label guard requires \(a/q\le8/9+O(1/q)\). The forcing expressions have respective negative margins (-q/17+O(1)) and (-2q/9+O(1)). The right side is (29q/85+O(1)). These strict margins prove the barrier eventually. Similarly \(d(q)-(2q+1-A(q))\) has margin (q/85+O(1)) on low rows and (18q/85+O(1)) on high rows, so ROW-SHARP holds eventually.

At all residues \(n=1\pmod {10}\) the clock goes low to high, and at \(n=2\pmod {10}\) high to low. The downward increments therefore have size ((7/85)n+O(1)) on a positive-density set. For every fixed \(K\), their clipped sum through \(N\) is at least \(7N^2/1700-O_K(N)\); count-clock uniform integrability fails. No canonical triangular journal or actual-game realization has been constructed. This is an abstract counterexample to the stated implication, not to canonical \(Q=o(n)\).

## Record-drop envelope

For the same abstract domain, define \(M_0=0\), \(M_n=\max_{r<n}d(r)\), backward inversions \(B_n=\#\{r<n:d(r)>d(n)\}\), and forward inversions \(F_n=\#\{r>n:d(r)<d(n)\}\). If a nonnegative, nondecreasing integer \(b\) satisfies \(d(n)\ge M_n-b(n)\), then \(B_n\le b(n)\): its distinct values lie in (\(d(n),M_n]\). A forward contributor has \(r<d(r)<d(n)\le2n+1\), and \(M_r\ge d(n)\), so

\[
d(n)-b(2n+1)\le d(r)<d(n).
\]

Injectivity gives \(F_n\le b(2n+1)\). Both counts are nonnegative, hence \(|F_n-B_n|\le\max(F_n,B_n)\le b(2n+1)\). At \(n=0\) both inversion sets are empty. The theorem supplies no such canonical \(b\).
