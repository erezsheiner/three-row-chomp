# Finite certificates and the all-index bridge

This supplement proves the certificate interpretation used for lag 211 and the local charged-shell criterion. The separate lag-124 context supplement supplies its more specific ABAB/BABA descent and forced-Q argument. Use the [canonical foundation](../../audit/full/CANONICAL-FOUNDATIONS.md) for the exact completion/game dictionary and [portable finite certificate instructions](../../certificates/README.md) for the actual checked inputs. A finite PASS does not by itself prove these all-index conclusions.

## 1. Game events and the complete new reply list

A sorted positive three-row position is \((a,b,c)\), \(a\ge b\ge c\ge0\). It is \(P\) if it is losing for the next player, and \(N\) otherwise. Legal non-poison moves decrease the top to \(0<a'<a\), truncating both lower rows at \(a'\); decrease the middle to \(0\le b'<b\), truncating the bottom there; or decrease the bottom to \(0\le c'<c\). For a nonempty \(P\), all legal moves are \(N\). A nonempty \(N\) has at least one \(P\)-reply, by the defining finite recursion. The actual-game completion dictionary is \(P(a,b,c)\) iff \(a=f(b,c)\), in the sorted domain.

Write
\[
E(k,m;b):=P(b+k,b,b-m),\qquad k\ge0,\quad 1\le m\le b.
\]
Suppose \(X=(b+k,b,b-m)\) is \(P\). For \(1\le t\le b-m\), its bottom-cut neighbor \(Y_t=(b+k,b,b-m-t)\) is \(N\) and is nonempty. Its possible \(P\)-replies that are not already legal options of \(X\) are exactly:
\[
\begin{array}{ll}
\mathrm{I}: &E(k+j,m+t-j;b-j),\quad 1\le j\le m+t-1,\\
\mathrm{II}:&E(0,h;b-m-t+h),\quad 1\le h\le m+t-1,\\
\mathrm{III}:&E(\ell,m+t;b),\quad 0\le\ell<k.
\end{array}
\]

Indeed bottom-row replies of \(Y_t\) are already replies of \(X\). For a middle cut to \(b'=b-j\), if \(b'\le b-m-t\) both original and new positions truncate to the same \((b+k,b',b')\), already an option of \(X\). The remaining range \(1\le j\le m+t-1\) retains the new bottom \(b-m-t\), giving I. For a top cut \(a'<b-m-t\), both lower rows truncate at \(a'\) and give a common original option. For \(b-m-t\le a'<b\), write \(a'=b-m-t+h\); equality \(h=0\) is again a common cube, whereas \(1\le h\le m+t-1\) gives II. Finally \(b\le a'<b+k\) gives \(a'=b+\ell\), type III. Every listed move respects the sorted domain; other moves were paid because \(X\) was \(P\).

Choose distinct legal cuts \(U\). Suppose all I/II candidates are \(N\), and possible III replies at cut \(t\) have their lag in a set \(L_t\subseteq\{0,\ldots,k-1\}\). Two different cuts cannot use the same lag \(\ell\): the corresponding \(P\)-positions have common top \(b+\ell\), common middle \(b\), and different bottoms, so the larger-bottom one moves to the smaller, impossible. Thus the cuts inject into \(\bigcup_tL_t\). If
\[
\left|\bigcup_{t\in U}L_t\right|<|U|,
\]
then \(X\) cannot be \(P\). No uniqueness of a winning reply to arbitrary \(N\) positions is assumed.

## 2. Periodic fixed-column induction, including the history boundary

Suppose a finite column prefix \(0\le c\le C\) is proposed to have frozen values \(v_c<q_0\) or live positive offsets \(f(b,c)=b+g_c(b\bmod p)\), \(b\ge q_0>C\). Frozen columns and live columns must partition that prefix. Let \(G\) bound all offsets, and \(H\) bound all inherited diagonal seeds and all awards in that prefix before \(q_0\). Choose \(T\ge q_0+G\), \(T>H\).

The literal positive-MEX replay checks every proposed cell on \(q_0\le b<T\); frozen labels already occur below \(q_0\) and subsequently COPY. For each live column and phase, the normalized blocked set is
\[
\{g_c((r-s)\bmod p)-s:1\le s\le G\}
\ \cup\ \{g_h(r):h<c,\ h\text{ live}\}.
\]
Its zero-based MEX must be \(g_c(r)>0\); the offset zero is therefore blocked.

Induct first on row \(b\ge T\), then column \(c\). Inherited seeds and pre-\(q_0\) awards are below \(b\), since \(H<T\le b\). A private award older than \(G\) rows is at most \(b-1\), so cannot affect nonnegative normalized offsets. Recent awards and earlier current live columns produce exactly the finite blocked set above. Frozen current columns lie below \(b\). LIVE-FLOOR for recomputation rules out absolute outputs below \(b\); its hypotheses are supplied by the exact actual-game dictionary, not by a modified local table. The positive MEX on absolute labels is consequently \(b\) plus that normalized MEX. A live previous value is at least \(b\), because its previous offset is positive, so COPY is not applicable. This closes the proposed pattern induction.

The delivered C360 input has \(q_0=600\), \(G=211\), \(H=810\), \(T=811\), period two, columns \(0,\ldots,360\). The fresh replay checks all 76,171 base cells and 300 normalized identities. These are finite-column all-row rails, not a hypothesis that arbitrary columns settle.

## 3. Phase-aware multi-cut induction

A finite certificate consists of distinct triples \((k,m,r)\), with middle phase \(r=b\bmod p\), selected nonempty cut sets \(U\), and exact residual lag unions. A fixed-column rail \(f(b,c)=b+k\) excludes \(E(k,m;b)\) whenever \(b-m>c\): if the larger-bottom position \((b+k,b,b-m)\) were \(P\), its legal bottom cut to \(c\) would be the other \(P\)-position \((b+k,b,c)\).

For each certificate state and selected cut:

* I/II supports must be a rail or another state at the correct shifted middle phase;
* every III candidate outside the recorded residual union must be a rail or state;
* I/II decrease middle by a positive integer at most \(J\), and III decreases top lag at the same middle;
* the exact residual union has cardinality less than the number of distinct cuts.

Pick base row \(B\) large enough for all rail domains, host inequalities and cut legality. Replay all certificate states at their matching phases on the \(J\) consecutive rows \(B,\ldots,B+J-1\), establishing they are \(N\).

For rows at least \(B+J\), induct on middle row \(b\); within a fixed row induct on \(k\). A putative \(P\) state forces \(P\)-replies after every selected bottom cut. I/II candidates are \(N\) by previous rows or rails; their positive backward jumps cannot skip below \(B\). Paid III candidates are \(N\) by smaller \(k\) or rails. Remaining III lags cannot supply enough distinct replies by Section 1. Contradiction proves every state \(N\) for all \(b\ge B\). The proof uses the checked final certificate family, not its search history.

For lag 211, \(B=600\), \(J=120\), there are 8,431 distinct states. The portable reader explicitly reconstructs every residual set/union, legal cut, shifted support and deficit, checks 1,355,278 calls including 424 target-coverage calls, and checks all 505,860 matching-phase base states on 600 through 719. Each target \((k,1,r)\), \(0\le k\le211\), is a state or rail.

The penultimate actual cell is a recomputation and at least \(b\). Were \(f(b,b-1)\le b+211\), it would equal \(b+k\) for some integer \(0\le k\le211\), making precisely that excluded \(E(k,1;b)\) a \(P\)-position by the completion dictionary. Therefore
\[
f(b,b-1)>b+211\qquad(b\ge600).
\]
This proves the specific lag, not an arbitrary-lag or unbounded-lag theorem.

## 4. Neighboring winning-target sets

Let \(W(a,b,c)\) be the set of legal targets which are \(P\), not a Boolean outcome. Put \(X=(a,b,b)\), \(Y=(a,b,b-1)\), \(b\le a<d(b)\), and \(f=f(b,b-1)\ge b\). Middle-cut target lists coincide. Bottom-cut lists differ only by the extra target \(Y\) from \(X\). Top cuts below \(b\) coincide. The remaining top cuts of \(X\) have top below \(d(b)\), so are not \(P\). The remaining top cuts of \(Y\) can be \(P\) only at top \(f\).

If \(f>a\), none of these differing top targets is \(P\), and \(Y\) itself is \(N\), hence \(W(X)=W(Y)\). If \(f=a\), \(Y\) is an extra \(P\)-target of \(X\) and none of its own moves is \(P\). If \(f<a\), \((f,b,b-1)\) is a \(P\)-target of \(Y\) and no one-move target of \(X\). Thus equality holds exactly when \(f>a\). Lag 211 implies it on \(a=b+k\), \(0\le k\le211\), because strict diagonal maximality also gives \(d(b)>f>b+211\). No separate stronger slope bound is needed for this corollary.

## 5. Exact local rule for charged bounded shells

This is a finite proof class, not a necessary condition for every Chomp argument. Fix a periodic mask of independently proved rails; nonrail lags at each phase are **holes**, including lag zero. Give selected holes a nonnegative integer cap \(A(k,r)\), with common zero-lag cap \(M\) and positive caps at positive holes. A cap denotes excluded ages through that cap. At a parent hole \(v=(k,r)\) with age cap \(A_v\), choose bottom-cut parameters \(u=A_v+1,\ldots,n\), with \(n\le M\) for a positive lag; lag zero uses its specified terminal \(M+1\).

All I/II replies must be fully covered by rails or previously established cap states. III supports from previous shaving levels can be used. In the same shell, a top drop \(k-\ell\le J\) may be used; larger drops are deliberately retained as possible \(P\)-replies. The induction order is prior shaving level, then lower top coordinate, then decreasing lag in a fixed top slice, exactly as required by this class. This last order is used only on a specified finite admissible lag/rank box, with every child outside the box already paid by an external rail or prior boundary theorem. I/II keep or lower the top coordinate while increasing the lag within a fixed top slice, so they are earlier in this finite decreasing-lag order; there is no well-founded decreasing order on an unrestricted infinity of natural lags. A cap table without the finite-box and paid-boundary condition is not a certificate of this class.

At cut parameter \(u\), an unresolved III hole \(\ell<k\) remains precisely when
\[
A_\ell<u,\quad\hbox{or}\quad A_\ell=u\ \hbox{and}\ k-\ell>J.
\]
As \(u\le n\) varies, the union is exactly
\[
D_J(v,n;A)=\#\{\ell<k:\ell\text{ a phase-}r\text{ hole},A_\ell<n\}
+\#\{\ell<k:\ell\text{ a phase-}r\text{ hole},A_\ell=n,k-\ell>J\}.
\]
Interior far equality \(A_\ell=u<n\) already belongs to the first set. By Section 1 one lower lag can provide at most one \(P\)-reply across all cuts. Thus the precise Hall contradiction for this prescribed overcount is
\[
n-A_v>D_J(v,n;A),
\]
alongside the full I/II support requirements. “Exact” here describes this overcount test, not truth of arbitrary positions outside the class.

Any successful selected subset with largest cut \(n\) can be filled in to the initial interval \(A_v+1,\ldots,n\). The largest cut already produces the same residual union, and I/II ranges for earlier cuts shrink, so support becomes easier. More cuts can only strengthen the contradiction.

For near holes the union indicator is \(1[A_\ell<n]\); for far holes it is \(1[A_\ell\le n]\). Hence
\[
D_J(n)-D_J(n-1)=\#\{\text{near}:A_\ell=n-1\}
+\#\{\text{far}:A_\ell=n\}\ge0.
\]
If a least successful terminal \(n\) had any far equality charge, this difference would be at least one, and strict integer success at \(n\) would imply \((n-1)-A_v>D_J(n-1)\). Its right side is nonnegative, so \(n-1>A_v\), a legal earlier terminal with easier supports. Contradiction. A least successful terminal therefore has no far equality charge.

Finally growing a child's cap can only weaken charged indicators and enlarge support. Any monotone cap-deletion operation which keeps all supported Hall witnesses preserves every valid certificate below its current table. Finite descending integer tables terminate, but claims of a greatest table or target-complete search need the separately specified update operator, rank box and support proof. Uniform shaving by \(c\) respects the local test at a retained positive terminal \(n-c>0\):
\[
(A_\ell-c)_+<n-c\iff A_\ell<n,\qquad
(A_\ell-c)_+=n-c\iff A_\ell=n.
\]
Only when forward/face supports survive the same shaving may this be used for normalization. No C460 numeric search result, obstruction at 72, or general proof-class exhaustion is included in the released local-criterion theorem.
