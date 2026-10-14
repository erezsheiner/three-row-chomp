# Source-time capacity and the precisely scoped tight cases

Use the canonical table and conventions of [Canonical definitions](CANONICAL-DEFINITIONS.md). In particular \(A\) counts positive blockers, \(\sigma_h=\infty\) for immortal hosts, \(H(h)=\#\{t<h:d(t)>d(h)\}\), and \(T(h)=\max_{t<h}d(t)\). The penultimate \(v(h)=f(h,h-1)\) is defined only for \(h>0\).

## Standing missing-booker context and nonnegative slacks

Fix mortal owner \(a\), its blocker \(p=\sigma_a\), and an older host \(h<a\) which has never privately served \(p\) and whose death is \(r=\sigma_h\), with \(a+1<r<p\). The gap-three context additionally has \(p=r+3\). Put

\[
E(h)=d(h)+A(h)-(2h+1),\qquad F(h)=2h-r-A(h),\qquad L=r-h.
\]

After row \(h\), there are \(h+1-A(h)\) distinct live awards, all greater than \(h\) and at most \(d(h)\). Their count proves \(E(h)\ge0\). Victim propagation serves the blocker \(r\) on every row \(h,\ldots,r-1\), with all hosts strictly below \(h\); no host repeats. These \(r-h\) hosts survive after row \(h\), because a frozen label cannot later serve \(r>h\). There are \(h-A(h)\) older survivors, proving \(F(h)\ge0\).

Adding definitions gives \(d(h)-r=1+E(h)+F(h)\). When \(p=r+3\) and \(d(h)<p\), the blocker \(p\) cannot equal a diagonal; integrality gives \(d(h)-r\in\{1,2\}\). Thus \((E,F)\) is exactly one of \((0,0),(1,0),(0,1)\). This is a remaining-case split, not a contradiction.

When \(E=F=0\), \(d(h)=r+1\), the older survivors \(U_h=\{c<h:\sigma_c>h\}\) number \(r-h\) and their awards fill \([h+1,r]\). The \(r\)-service injection saturates this roster: each such host serves \(r\) exactly once on \([h,r)\). No assertion about a predecessor \(F=0\) follows.

## Tight widths at most 18 are excluded in this gap-three context

The exact actual-game Lean theorem [R195B30Depth20AffineRails.gameF_col31_rail](../../lean/core/R195B30Depth20AffineRails.lean) states

\[
44\le q\quad\Longrightarrow\quad f(q,31)=q+19.
\]

For \(h\ge44\), column 31 is older and live in the birth row \(h\). Under \(E=F=0\), its value lies in \([h+1,r]\), so \(h+19\le r\) and \(L\ge19\).

For \(7\le h\le43\), the delivered [tight-width base](../../certificates/inputs/tight_width18_base.json) values are independently recomputed by the portable literal positive-MEX checker, and all \(E(h)>0\). For \(h<7\), the exact early rows and positive periodic-rail certificate show columns \(0,2,5\) are immortal; periodicity proves the tail and the finite preceding rows contain no death. The other small deaths are \(\sigma_1=2,\sigma_3=5,\sigma_4=7,\sigma_6=9\). The first two violate \(h<a\) and \(a+1<r\). For \(h=4\), the only possible \(a\) is 5 and gap three would make \(p=10\), a diagonal label \(d(5)\), impossible. For \(h=6\), the only possible \(a\) is 7 and gap three makes \(p=12\), whose actual unique victim is 8, not 7. Therefore no small context remains. These exact boundary data are stable facts of the uniquely determined recurrence; a null finite death observation alone is not used to infer immortality.

The result is only \(L\ge19\) in the stated context. It does not exclude width 19, all gap-three cases, or an unconditional victim gate.

## Terminal service capacity without tightness

Let \(q\ge3\), \(y=v(q)\). The independently proved penultimate bound gives \(y\ge q+1\). At a current higher cell \(f(q,c)>y\), \(c<q-1\), COPY is impossible, and its left prefix does not contain the row's unique \(y\)-cell, which is later at \(q-1\). MEX forces \(y\) into its old journal.

The penultimate MEX theorem excludes every past diagonal from \(y\); it does not assert that \(y\) itself is diagonal. Thus the journal witness cannot be a seed or the host's birth diagonal. It is a strict postbirth private \(y\)-service on some \(t<q\). Two different higher columns require different such rows, by row injectivity. Strict row maximality gives \(d(t)>y\), proving

\[
\#\{c<q-1:f(q,c)>y\}\le\#\{t<q:d(t)>y\}.
\]

No tightness, record, slope, or victim ordering is assumed.

## Penultimate rank when \(E(h)=0\) alone

Take \(h\ge3\), \(E(h)=0\), and put \(r=d(h)-1\); here \(r\) need not be a blocker or death time. ROW-SHARP and \(A(j)-A(h)\le j-h\) give \(d(j)\ge d(h)+(j-h)\) for every \(j>h\). Thus no future diagonal is at most \(r\).

There are \(h-A(h)=r-h\) older survivors, whose distinct awards fill \([h+1,r]\). The penultimate \(y=v(h)\) belongs to it, is not past diagonal by its MEX, and cannot be current or future diagonal; hence it is a blocker. The \(r-y\) higher awards occur before its terminal host, so terminal capacity gives

\[
r-y\le\#\{t<h:d(t)>y\}=h-R(y)=h-y+A(y).
\]

Thus \(A(y)\ge r-h\). Also \(R(r)=h-H(h)\), so \(A(r)=r-h+H(h)\) and \(A(r)-A(y)\le H(h)\). To infer \(y=r\), one needs both \(H(h)=0\) and \(r\) a blocker: only then a smaller blocker \(y\) has \(A(y)<A(r)\). No such equality is inferred from the two general inequalities.

## Tight suffix injection and predecessor dichotomy

Now require \(E(h)=F(h)=0\) and \(r=\sigma_h\). A prebirth row \(t<h\) serves blocker \(r\) exactly when \(d(t)>r\), by coverage and strict maximality. Its host \(c_t<t\) is strict old, because \(r\) is not diagonal. Distinct source rows use distinct private hosts.

No such host survives after \(h\): every survivor must serve \(r\) anew on \([h,r)\) by \(F=0\), contrary to nonreuse. Its actual death \(b_t\) satisfies \(t<b_t\le h\). Distinct hosts have distinct deaths. For \(t\ge u\), these deaths lie in \((u,h]\), proving

\[
\#\{t:u\le t<h,\ d(t)>r\}\le A(h)-A(u)\qquad(0\le u<h).
\]

If numeric \(h\) is diagonal, \(A(h)=A(h-1)\). The \(u=h-1\) suffix has no available death, so \(d(h-1)\le r\). ROW-SHARP gives \(d(h-1)\ge r-1\), and blocker \(r\) cannot be diagonal. Therefore \(d(h-1)=r-1\), \(E(h-1)=0\).

If numeric \(h\) is a blocker, \(A(h-1)=A(h)-1\), and ROW-SHARP gives \(d(h-1)\ge r\). It is neither blocker \(r\) nor repeated diagonal \(r+1=d(h)\), so \(d(h-1)\ge r+2\). The row-\((h-1)\) \(r\)-booker dies after \(h-1\) and by \(h\); hence it is exactly the victim \(s(h)\), with \(f(h-1,s(h))=r,f(h,s(h))=h\). Substitution gives \(E(h-1)=d(h-1)-r\ge2\). Neither branch proves predecessor \(F=0\) or predecessor missing-booker membership.

## Record-tight fresh labels permit only disjoint adjacent swaps

Assume the tight context with \(H(h)=0\). The blocker-\(h\) predecessor branch would contradict record maximality, so \(h\) is diagonal and \(d(h-1)=r-1\). Earlier diagonals are at most \(r-1\). If \(v(h)=y<r\), terminal capacity needs \(r-y\) distinct prior diagonals above \(y\), but at most \(r-1-y\) distinct integer labels are available; contradiction. Hence \(v(h)=r\).

Let \(m=T(h-1)=\max_{t<h-1}d(t)\), a **strict** earlier record excluding \(d(h-1)\). Continuing hosts \(U_h\setminus\{h-1\}\) have complete awards \([h,r-2]\) before the transition and \([h+1,r-1]\) after it; there is no death at row \(h\), since numeric \(h\) is diagonal. Consider the consecutive integer set

\[
\mathcal F=[\max(h+1,m+1),\,r-2].
\]

A label \(y\in\mathcal F\) was absent in every row before \(h-1\), whose maximum is at most \(m\), and is not a diagonal seed. The birth diagonals \(r-1,r+1\) and later diagonals are also outside this interval. Therefore it is a blocker, and the unique row-\((h-1)\) service host \(k_y\) is the only older host whose row-\(h\) journal contains \(y\). Each such journal contains at most one \(\mathcal F\)-label.

If a larger current \(\mathcal F\)-label \(z\) precedes a smaller \(y\), the larger recomputed cell's MEX needs \(y\) in its journal, because the unique current \(y\) is later. Its host is necessarily \(k_y\). Thus any smaller label has at most one larger predecessor, and any larger label has at most one smaller successor. No value can have both an incoming and outgoing inversion, because the resulting length-two descending chain creates a second inversion at its first/last value. An inverted pair with a numerical intermediate value creates a second inversion at one endpoint, according to whether the intermediate is before or after the larger value. Hence inversions are disjoint pairs of numerically adjacent labels. The subsequence is the increasing list up to those swaps; other labels may interleave physically.

For \(h=1\), the literal tight case has \(r=2\) and empty \(\mathcal F\). For \(h=2\), tightness would force \(r=3\), but 3 is the already-born diagonal \(d(1)\), so cannot be a death blocker. Column zero is immortal. These cover the small cases without applying the \(q\ge3\) terminal lemma below its domain. Nothing says every physical column increases by one.
