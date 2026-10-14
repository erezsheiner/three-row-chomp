# Block ghost identities, composed density and the C50 lineage ledger

Use [Canonical definitions](CANONICAL-DEFINITIONS.md) and the [canonical foundation](../../audit/full/CANONICAL-FOUNDATIONS.md). Symbols below are locally defined so that the block and C50 set notation cannot be confused with residual service-token counts.

## Frozen labels and exact block definitions

In row \(t\), every label \(<t\) is a frozen blocker, and every blocker \(p<t\) occurs exactly once at its persistent victim. To see the first direction, let \(r\) be a column's last recomputation before its first copied row. Recomputed value is at least \(r\); COPY at \(r+1\) requires it below \(r+1\), so it equals \(r\), making it the death blocker by the partition theorem. COPY then persists. Thus the number of frozen cells is \(A(t-1)\), not \(A(t)\).

An old diagonal label in row \(t\) is a ghost; its value is necessarily at least \(t\), since diagonal labels cannot freeze. Let \(I(t)\) count all such row ghosts, \(H_t=\#\{a<t:d(a)>d(t)\}\), and \(b_t=A(t)-A(t-1)\). The pool consists of row labels at least \(t\) that are not past diagonals and are not the current own diagonal. It includes blockers, including the death-row blocker \(t\) when present, and future diagonals. Write \(\operatorname{pool}(t)\) for its size.

For \(t\ge4\), the **block** is columns \(c\le t-4\). Define:

* \(G_4(t)\): ghosts in that block;
* \(\operatorname{ygh}(t)\): ghosts at ages \(1,2,3\), namely columns \(t-1,t-2,t-3\);
* \(G'_4(t)=\#\{c\le t-4:f(t-1,c)\ge t,\ f(t-1,c)\in\{d(a):a<t-1\}\}\);
* \(\operatorname{ygh}_{3}(t-1)\): the indicator that column \(t-4\), of age 3 in row \(t-1\), is such a ghost with value at least \(t\);
* \(\operatorname{ygh}_{2p}(t)\): the ghosts of row \(t-1\) at ages 1 and 2;
* \(dG_4(t)=G_4(t)-G'_4(t)\);
* \(\operatorname{step}(t)=d(t)-d(t-1)\).

The overlap identity gives \(I(t)=2t+1-d(t)-H_t\), hence \(G_4(t)=I(t)-\operatorname{ygh}(t)\). No ghost has value exactly \(t-1\) in row \(t-1\), because a prefix equality to the row index would make that label a blocker. Therefore the threshold change from \(t-1\) to \(t\) removes no old ghost, and

\[
G'_4(t)=G_4(t-1)+\operatorname{ygh}_3(t-1).
\]

Subtracting overlap identities and using
\(\operatorname{ygh}(t-1)-\operatorname{ygh}_3(t-1)=\operatorname{ygh}_{2p}(t)\) proves

\[
dG_4(t)=2-\operatorname{step}(t)-(H_t-H_{t-1})
-\operatorname{ygh}(t)+\operatorname{ygh}_{2p}(t).
\]

This \(dG_4\) is the change on one fixed retained block with its threshold adjustment; it is not an unrelated statistic called \(\Delta G\).

Partitioning all \(t+1\) row cells into \(A(t-1)\) frozen blockers, \(I(t)\) ghosts, pool and own diagonal gives

\[
\operatorname{pool}(t)=t-A(t-1)-I(t).
\]

Algebra then yields

\[
I(t)-\operatorname{pool}(t)+b_t-2+2H_t
=3t+A(t)-2d(t)=Q(t).
\]

The pool also equals \(A(d(t)-1)-A(t-1)+F_t\), where \(F_t\) counts current future-diagonal services, by nonpast coverage and maximum. None of these identities supplies a density or sublinear discrepancy estimate.

For the \(t=4\) boundary, define \(G_4(s)\) for every integer \(s\ge0\) by its column-count formula \(0\le c\le s-4\), using an empty domain when \(s<4\). The age-3 indicator at row 3 refers to column zero, and its previous-row threshold is still at least 4. Thus \(G_4(3)=0\) and the displayed \(G'_4(4)\) identity is defined without extending any negative column index. Young counts below age 3 similarly include only existing nonnegative columns.

## Composed blocker-count defect and silver density

Put \(\beta=\sqrt2-1\) and \(E_{AA}(N)=A(A(N))+2A(N)-N\). The canonical upper count \(A(N)\le N/2\) follows because distinct diagonals of owners \(0,\ldots,\lceil N/2\rceil-1\) lie through \(N\). The actual-game quantitative floor gives \(\liminf A(N)/N\ge1/3\).

If \(A(x)/x\to\beta\), then \(A(N)\to\infty\), and
\[
A(A(N))=\beta A(N)+o(N)=\beta^2N+o(N).
\]
Since \(\beta^2+2\beta-1=0\), \(E_{AA}=o(N)\).

Conversely suppose \(E_{AA}=o(N)\). Set \(x_N=A(N)/N\). The count floor guarantees \(A(N)\to\infty\), so division by \(A(N)\) gives
\[
x_{A(N)}=1/x_N-2+o(1).
\]
The nonempty compact cluster set \(C\) of \(x_N\) lies in \([1/3,1/2]\). Every \(c\in C\) gives \(G(c)=1/c-2\in C\) by the last identity. Thus \(G(C)\subseteq C\), and applying \(H(y)=1/(y+2)=G^{-1}(y)\) gives \(C\subseteq H(C)\). On nonnegative \(y\), \(|H'(y)|\le1/4\). Therefore
\(\operatorname{diam}C\le\operatorname{diam}C/4\); \(C\) is a singleton \(c=G(c)\), necessarily \(\beta\). A bounded sequence with just one cluster point converges, so \(A(N)/N\to\beta\). This concerns density of the value set, not order of the diagonal sequence. No conclusion \(d(n)/n\to1+1/\sqrt2\) is asserted.

## C50 sets, orbit roots and their exact counts

The injective map \(d\) has \(d(x)>x\). Repeated inverse images strictly decrease integer indexes, so every nonnegative integer has a unique root: zero or a positive blocker. The forward orbit of a root is strictly increasing and unbounded, and these orbits partition the nonnegative integers.

For \(q\ge1\), define owner sets
\[
\operatorname{Pend}_q=\{x<q:d(x)\ge q\},\quad
\operatorname{Hosted}_q=\{x<q:d(x)\in C_q\},\quad
\operatorname{Above}_q=\{x<q:d(x)>d(q)\}.
\]
Here \(C_q=\{f(q,c):c<q\}\) is the row prefix. Write \(\mathcal H_q=\operatorname{Hosted}_q\sqcup\operatorname{Above}_q\); it is a set, not the scalar inversion count \(H_q\). An owner \(x\in\operatorname{Pend}_q\) is **absent** when \(d(x)<d(q)\) and \(d(x)\notin C_q\). Let \(\operatorname{AbsB}(q)\) be the number absent.

Each root below \(q\) has exactly one node \(x\) crossing \(x<q\le d(x)\), giving
\[
|\operatorname{Pend}_q|=1+A(q-1).
\]
If a hosted diagonal were below \(q\), it would be a frozen blocker, contradiction. Thus Hosted is contained in Pend; Above is also, since \(d(q)>q\). Injectivity excludes \(d(x)=d(q)\) for \(x<q\), and maximum makes hosted and above disjoint. These three classes partition Pend. Overlap gives
\[
|\mathcal H_q|=2q+1-d(q),\qquad
\operatorname{AbsB}(q)=d(q)-2q+A(q-1).
\]
This proves the membership sometimes called hosted A1. It is distinct from the open direct-Q owner-transport A1.

For positive integers \(m,n\), let \(N=m+n\). Define
\[
\begin{aligned}
\operatorname{Abs}_{\rm old}(m,N)&=\#\{x\in\operatorname{Pend}_N:x\text{ absent},\ \operatorname{root}(x)<m\},\\
\operatorname{Abs}_{\rm young}(m,N)&=\#\{x\in\operatorname{Pend}_N:x\text{ absent},\ \operatorname{root}(x)\ge m\},\\
X(m,n)&=\operatorname{Abs}_{\rm young}(m,N),\\
\operatorname{defA}(m,n)&=A(N-1)-A(m-1)-A(n-1)-1,\\
\Delta_{\rm old}(m,n)&=\#\{x\in\mathcal H_N:\operatorname{root}(x)<m\}-|\mathcal H_m|,\\
\Delta_{\rm young}(m,n)&=\#\{x\in\mathcal H_N:\operatorname{root}(x)\ge m\}-|\mathcal H_n|.
\end{aligned}
\]
There are \(1+A(m-1)\) old roots and \(A(N-1)-A(m-1)\) young roots at row \(N\). Subtract their absent counts from their pending counts, then subtract the corresponding \(\mathcal H_m,\mathcal H_n\) counts. This yields
\[
\begin{aligned}
\Delta_{\rm old}&=\operatorname{AbsB}(m)-\operatorname{Abs}_{\rm old}(m,N)
=X-[\operatorname{AbsB}(N)-\operatorname{AbsB}(m)],\\
\Delta_{\rm young}&=\operatorname{AbsB}(n)-X+\operatorname{defA}(m,n).
\end{aligned}
\]
Adding gives \(\Delta_{\rm old}+\Delta_{\rm young}=-(1+d(N)-d(m)-d(n))\). Bounds \(\Delta_{\rm old}\ge-b_{\rm old}(n)\), \(\Delta_{\rm young}\ge-b_{\rm young}(n)\), uniform in the intended \(m\) range, would imply the corresponding defect upper bound. Neither sublinear supplier nor any converse is proved by the identity.

## One-row absence flux for a fixed root class

Fix a set \(C\) of roots once and for all. Let \(\operatorname{Abs}_C(q)\) count absent pending owners whose root lies in \(C\). Among continuing owners \(x\in\operatorname{Pend}_q\cap\operatorname{Pend}_{q+1}\), let \(F_C^+(q)\) count not-absent to absent switches, and \(F_C^-(q)\) absent to not-absent switches, always with root in \(C\).

The entrant is \(x=q\), because \(q<q+1\le d(q)\). Define
\[
E_C(q)=1[\operatorname{root}(q)\in C,\ d(q)\text{ absent at row }q+1].
\]
If \(q\) is a diagonal label, its unique owner \(x\) with \(d(x)=q\) exits Pend. This owner was absent at row \(q\): the diagonal label \(q\) cannot occur at its numerical deadline in the prefix, and \(q<d(q)\). Define
\[
\operatorname{Out}_C(q)=1[q\in\operatorname{range}(d),\ \operatorname{root}(q)\in C].
\]
Its root agrees with that of its inverse owner. Since
\[
\operatorname{Pend}_{q+1}=(\operatorname{Pend}_q\setminus\{x:d(x)=q\})\cup\{q\},
\]
the exact change is the sum of continuing switches, entrant and exit:
\[
\operatorname{Abs}_C(q+1)-\operatorname{Abs}_C(q)
=F_C^+(q)-F_C^-(q)+E_C(q)-\operatorname{Out}_C(q).
\]
The formula is stated for \(q\ge1\). With empty Pend at \(q=0\), no exit and the entrant definition, it also extends to zero directly. Nothing bounds the flux difference asymptotically, and the root class cannot be changed after seeing each row.
