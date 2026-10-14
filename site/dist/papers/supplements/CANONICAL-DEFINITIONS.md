# Canonical definitions for the corrected paper proofs

This is a definition and dependency sheet for the selected paper statements. It does not assert an asymptotic bound. It replaces references to notation that appeared only in excluded historical drafts. An entry must still state its own additional hypotheses.

## The table, labels and time boundaries

Rows and columns are nonnegative integers, with \(0\le c\le q\). The table is \(f(q,c)\). Put \(d(q)=f(q,q)\). The journal used before the cell ((q,c)) is

\[
J_q(c)=\{f(t,\min(t,c)):0\le t<q\}.
\]

It is the union of the diagonal seeds \(\{d(t):t<c\}\) and private awards \(\{f(t,c):c\le t<q\}\). The strict current prefix is \(\{f(q,h):h<c\}\). If \(c<q\) and \(f(q-1,c)<q\), COPY sets \(f(q,c)=f(q-1,c)\). Otherwise the cell is the least **positive** integer absent from the journal and prefix. Thus \(f(0,0)=1\). This positive MEX differs from the zero-based MEX used in the finite two-owner insertion propositions.

A positive label is a **diagonal label** if it equals \(d(t)\) for some \(t\). All other positive labels are **blockers**. Define

\[
A(x)=\#\{p\in\mathbb Z_{>0}:p\le x,\ p\text{ a blocker}\},\qquad
R(x)=\lfloor x\rfloor-A(x).
\]

For integer arguments, \(R\) counts positive diagonal labels through that argument. When a result specifies linear interpolation, use that interpolation instead; otherwise \(A(x)=A(\lfloor x\rfloor)\). Both conventions differ by at most one. \(A\) never counts zero.

Each blocker \(p\) has a unique victim \(s(p)<p\) with \(f(p,s(p))=p\). The column subsequently copies \(p\) forever. Define a column's death time \(\sigma_c=p\) if \(s(p)=c\), and \(\sigma_c=\infty\) if no such \(p\) exists. A column is **live after** row \(q\) when \(f(q,c)>q\), equivalently \(\sigma_c>q\). It is live at **START \(N\)** if it has not died before row \(N\), so \(\sigma_c\ge N\). These two boundaries must not be interchanged. Let

\[
\operatorname{Imm}(x)=\#\{c<x:\sigma_c=\infty\}.
\]

A **private service** of label \(v\) at host \(c\) means an actual recomputed cell \(f(t,c)=v\), with \(t\ge c\); repeated frozen COPY cells are not new services. “Strict postbirth” means \(t>c\). Diagonal-label services at another host are strict old cells. A blocker's predeath services have \(t<p\), so they are recomputations rather than frozen copies.

The canonical premises used below are separately proved in the delivered [canonical foundation](../../audit/full/CANONICAL-FOUNDATIONS.md) and its exact Lean anchors: row injectivity and strict diagonal maximum; diagonal injectivity; positive MEX clauses; \(d(q)>q\); \(d(q)\le2q+1\); cell reach \(f(q,c)\le q+c+1\); seeded-column nonreuse; positive diagonal/blocker partition; every nonpast positive label below the current diagonal is in the prefix; victim propagation; and future-freeze \(c<\sigma_c<d(c)\) for mortal \(c\). None means that chronological diagonals are increasing.

## Overlap, live rows and the signed token inventory

For a completed row \(q\), let

\[
O_q=\{d(a):a<q\},\quad C_q=\{f(q,c):c<q\},\quad
I_q=|O_q\cap C_q|,\quad H_q=\#\{a<q:d(a)>d(q)\}.
\]

The subscript \(q\) on \(C_q\) here denotes the current prefix set; it is distinct from the owner-indexed exceptional service set \(C_a\) below. Row injectivity and diagonal injectivity make both source sets have \(q\) elements. Positive MEX at the diagonal and strict row maximum give

\[
|O_q\cup C_q|=d(q)-1+H_q,\qquad d(q)+I_q+H_q=2q+1.
\]

The old source labels above \(d(q)\) are exactly the \(H_q\) extras; no prefix value exceeds the diagonal. The live count is \(m_q=q+1-A(q)\). The central discrepancy is

\[
Q(q)=3q+A(q)-2d(q)=2(I_q+H_q)-m_q-1.
\]

Each currently served old diagonal \(d(a)\), \(a<q\), has an actual physical host \(c<a\). Partition these services by owner:

* \(L_q\): mortal \(a\) with \(q<\sigma_a\);
* \(J_q\): immortal \(a\);
* \(D_q\): mortal \(a\) with \(\sigma_a\le q\).

Here each symbol denotes a count, or the corresponding set of actual tagged services when used as vertices. The equality-at-death case belongs to \(D_q\), not \(L_q\). Thus \(I_q=L_q+J_q+D_q\).

Let \(B_q\) be the set/count of live blocker services in row \(q\), and \(F_q\) the set/count of current services of diagonals \(d(a)\) with owner \(a>q\). Future-freeze and nonpast coverage give one distinct live blocker service \(\sigma_a\) for every \(L_q\) owner. Remove exactly those services from \(B_q\); the remainder is \(B_{0,q}\), with count \(B_q-L_q\). The live row consists of its own diagonal and these three classes, hence

\[
m_q=1+I_q+B_q+F_q,\qquad
Q(q)+2=J_q+D_q+2H_q-B_{0,q}-F_q.
\]

The residual token multiset uses positive \(J,D,H_1,H_2\) and negative \(B_0,F\). \(H_1,H_2\) are two distinct copies of each inversion ((t,a)), \(t<a\), \(d(t)>d(a)\). Both copies are dated at owner row \(a\); the corresponding future-diagonal service \(F\) is dated at its actual source row \(t\). A service token retains its type, date, physical host, numeric label, owner/victim and copy tag. Distinct copies are never merged by equality of their numeric coordinates.

## The spatial ghost paths

On the live column vertices and their old-owner endpoints draw \(c\to a\) when \(f(q,c)=d(a)\), \(a<q\). Include isolated live columns, including \(q\). Each vertex has indegree and outdegree at most one; every edge has \(c<a\), so nontrivial components are finite directed paths.

Let \(Z_q\) count isolated live vertices. For a nontrivial path with \(e\) edges, let its terminal status be live or dead after row \(q\). Define \(X_{L,q}\) as the sum of (e-1) over live-ended paths, and \(X_{D,q}\) as the sum of \(e\) over dead-ended paths. These are the \(X_L,X_D,Z\) in the ghost ledger; they are unrelated to the owner prebirth set \(X_a\).

For endpoint matching, an **available vertex** \(v\) means that its own death blocker is a current **live** service: \(\sigma_v<\infty\), \(q<\sigma_v<d(q)\). That particular blocker token may be paired with an incident ghost edge, with capacity one on both the token and edge. Frozen blocker copies are not available residual tokens. The maximum-matching proposition concerns precisely this endpoint incidence rule.

## The two-label inventory for one mortal owner

Fix mortal owner \(a\), and write \(p=\sigma_a\), \(y=d(a)\), so \(a<p<y\). Let \(P_a\) be the physical hosts of actual private \(p\)-services before \(p\); all are \(<a\), no host repeats, and \(|P_a|=A(p)\). Write \(u_h\) for the unique \(p\)-service time at \(h\in P_a\).

Every private \(y\)-service has a unique host and date. Use the following owner-indexed sets:

* \(E_a\): \(y\)-services at \(a<t<p\), while owner \(a\) is alive;
* \(D_a\): \(y\)-services at \(p\le t<y\), after owner death;
* \(R_a\): \(p\)-services at rows not carrying an \(E_a\) service; these are exactly this blocker's \(B_0\) services;
* \(C_a\): the \(E_a\) services whose host is outside \(P_a\);
* \(X_a\): \(y\)-services at \(t<a\) whose host is in \(P_a\);
* \(W_a\): the hosts in \(P_a\) which never privately serve \(y\).

Use event cardinalities for (E,D,R,C,X) and host cardinalities for (W,P); private nonreuse identifies each event with its host where needed. The birth cell ((a,a)) is not among these older-host services. For \(h\in P_a\), write \(v_h\) for its unique \(y\)-service time if one exists; otherwise write \(z_h=\sigma_h\), its actual death before \(y\). For a serviced host set \(z_h=v_h\). Thus the signed service stock is

\[
V_a(q)=\sum_{h\in P_a}\bigl(1[u_h\le q]-1[z_h\le q]\bigr),\quad V_a(-1)=0.
\]

It includes negative intervals when \(v_h<u_h\). Aggregate \(V(q)=\sum_{a\text{ mortal}}V_a(q)\); each fixed row/cut has only finitely many nonzero terms. For dated \(W_q\), use actual deaths \(z_h=q\), not the diagonal owner's death \(p\).

In the reverse-source forest, partition the serviced \(P_a\) hosts into **reverse** \(v_h<u_h\) and **forward** \(u_h<v_h\). Equality is impossible in one cell because \(p\ne y\). A forward terminal may have \(v_h\ge p\); it is then an unpaid \(D\) endpoint, not an \(X\) or \(W\) compensation. Write \(F_a^{\rm forward}\) for this set to avoid confusing it with row-wise future-diagonal \(F_q\).

For the specified dated global matching, \(T_a=\#\{t<a:d(t)>y\}\) counts all prebirth \(y\)-services, whose corresponding \(p\)-services lie in \(R_a\). After pairing them to mortal \(H_2\), choose the earliest \(\min(|D_a|,|R_a|-T_a)\) \(D\)-services and latest equally many remaining \(R_a\)-services. They form forward ledger edges. \(U_\pm([l,r])\) count unmatched signed tokens in that date interval; \(X_{\rm cross}(n)\) counts selected matching edges with negative date \(\le n\) and positive date \(>n\), and is zero for \(n<0\). This crossing stock is not \(X_a\) or \(X_{L,q}\).

## Tight source-time notation

The strict earlier record is \(T(q)=\max_{t<q}d(t)\), with \(T(0)=0\). The penultimate cell is \(v(q)=f(q,q-1)\), defined for \(q>0\). Define \(E(q)=d(q)+A(q)-(2q+1)\). In a mortal missing-booker context, \(p=\sigma_a\), \(h<a\), \(h\notin P_a\), \(r=\sigma_h\), and \(a+1<r<p\). For a gap-three context additionally require \(p=r+3\). Put \(F(h)=2h-r-A(h)\), \(L=r-h\), \(U_h=\{c<h:\sigma_c>h\}\). This scalar \(F(h)\) is not the future-diagonal token count \(F_q\). All tight statements explicitly assume the required \(E=0,F=0\), and record statements also require \(H(h)=0\). No predecessor \(F=0\) or missing-booker membership is implied by predecessor \(E=0\).

These definitions supply no nonnegative victim gate, direct-Q transport A1, canonical uniform-integrability estimate, convergence theorem or efficient algorithm.
