# Private history, increasing source exits and departure resources

Use [Canonical definitions](CANONICAL-DEFINITIONS.md) and the [canonical foundation](../../audit/full/CANONICAL-FOUNDATIONS.md). Full journals and strict source boundaries are essential. This supplement gives the actual source maps; it does not treat counts as substitutes for cell witnesses.

## Inversion and arbitrary private-source packing

Suppose \(c<r\le q\), \(f(q,c)>q\), and \(x=f(q,r)<f(q,c)\). The cell at \(c\) is recomputed, and row injectivity means \(x\) is not in its strict left prefix: its unique current host is later at \(r\). MEX therefore places \(x\) in the journal of \(c\).

It is not an inherited seed \(d(i)\), \(i<c\), or its birth diagonal \(d(c)\): either would have diagonal owner strictly below the current host \(r\), contrary to diagonal general no-attack. Thus there is a genuine strict postbirth source \(c<a<q\), \(f(a,c)=x\), with \(x<d(a)\) by strict row maximality. Nonreuse makes that source unique when the column survives to the present.

Let \(T\ge q\) bound every earlier diagonal \(d(a)\), \(a<q\). Every earlier journal label is at most \(T\). A **fresh** old host has current output \(>T\), and an **old return** has current output \(x\le T\). If \(j\) fresh hosts precede an old return, apply the inversion argument at each. The source rows are distinct, since equal rows would repeat \(x\) at different columns. Their distinct diagonal labels lie in \((x,T]\), so \(j\le T-x\). Fresh outputs occur in increasing numeric order: a later smaller fresh output would be absent from the current prefix and would have to be in an earlier journal bounded by \(T\), impossible. This does not make fresh hosts a physical suffix, nor require the returning cell to be live.

## Saturated rightmost-host handover

For a record row \(q\ge1\), take \(T=T(q)=\max_{a<q}d(a)\) and \(k=d(q)-T-1\ge1\). Coverage supplies every fresh label \(T+1,\ldots,T+k\) in old columns. Their increasing order implies that the rightmost fresh old host \(c_*\) has \(f(q,c_*)=T+k\). Every strict old tail column \(c_*<r<q\) carries an old return.

Each tail value \(x\) has private sources at all \(k\) fresh hosts, with \(k\) distinct earlier diagonals in \((x,T]\). Hence \(x\le T-k\). At the fixed host \(c_*\), the distinct tail values inject into the equally numerous strict postbirth rows \(c_*<a<q\). The injection is therefore a bijection, proving

\[
\{f(a,c_*):c_*<a<q\}=\{f(q,r):c_*<r<q\}.
\]

All \(q-c_*-1\) values on either side are distinct and at most \(T-k\). If \(c_*\le q-2\), row \(q-1\) is among them; its value is at most \(T-k\), while the current value is \(T+k\), giving a jump at least \(2k\). If \(c_*=q-1\), both sets are empty and that jump conclusion is not asserted.

For an earlier fresh host \(c_i<c_*\), its private postbirth history \(H_i\) contains the whole right-tail set \(H\), by the same inversion map. All its private awards are distinct because it never froze. Thus \(|H_i\setminus H|=c_*-c_i\).

If \(H\ne\varnothing\), let \(x_0=\min H\), and let \(a_*\) be its unique source row at \(c_*\). It is not an inherited seed at any earlier fresh host, because its current tail occurrence lies right of those hosts. If \(c_i\) has not served \(x_0\) before \(a_*\), then \(x_0\) is absent from both its journal and current left prefix at that row; the unique current \(x_0\) is later at \(c_*\). Its MEX output \(y\le x_0\), and row injectivity forces \(y<x_0\). Since \(c_i\) survives through \(q\), its award is strictly greater than \(a_*\) (equality would freeze it). It is a private postbirth award because \(a_*>c_*>c_i\). Therefore

\[
a_*<y<x_0,\qquad y\in H_i\setminus H.
\]

Several such late hosts give distinct smaller extras in the same row. These are permitted extras, not a contradiction.

## Full-history source map and the corrected exit count

Fix any currently fresh old column \(c\), not necessarily the rightmost one, and use its entire strict postbirth history

\[
H=\{f(a,c):c<a<q\},\qquad G=\{d(a):c<a<q\}.
\]

Survival means all these private awards are distinct, and seeds cannot reappear. The actual source-row map is a bijection \(H\to\{c+1,\ldots,q-1\}\). Compose it with the injective diagonal map:

\[
\Phi(f(a,c))=d(a).
\]

It is a bijection \(H\to G\) and satisfies \(\Phi(h)>h\), by strict row maximality. This is pointwise inflationarity, **not** order preservation between different inputs.

Every past diagonal has owner at most \(c\) or in \((c,q)\); seeds of the first class are absent from \(H\), so the nonpast history is exactly \(H\setminus G\). Equal finite cardinalities give \(|H\setminus G|=|G\setminus H|\). In the directed graph \(h\to\Phi(h)\), every vertex has indegree/outdegree at most one and edges strictly increase numeric labels. Thus no cycle exists. Its paths pair exactly the roots \(H\setminus G\) with exits \(G\setminus H\).

An exit \(z\) is also absent from the diagonal seeds by diagonal injectivity, hence from the whole journal. It is at most \(T< f(q,c)\), so positive MEX places it at a unique current host before \(c\). It must have \(z>q\): any cell at or below \(q\) is a death/frozen blocker, whereas \(z\) is diagonal. Thus it is a genuine pending old diagonal ghost. Different exits have different hosts. In particular \(|H\setminus G|\le c\); if a separately defined visible surplus \(P\subseteq H\) is also held before \(c\), it is disjoint from the exits, so \(|H\setminus G|+|P|\le c\). This last statement requires that exact surplus definition.

## A fourth source after three fresh hosts

Assume \(c_0<c_1<c_2<r\le q\), \(q\le T\), every earlier \(d(a)\le T\), fresh outputs at \(c_i\), and \(x=f(q,r)\le T\). A model-level proof additionally needs the explicit LowCellRowStart property

\[
c\le q,\ f(q,c)\le q
\quad\Longrightarrow\quad c<f(q,c)\ \hbox{and}\ f(f(q,c),c)=f(q,c).
\]

For the actual game this follows from the exact encoding: a value below the row represents the row-start losing position, and completeness puts it at its own death row. Equality is immediate. This is also the frozen/death-label partition in the canonical foundation; no new kernel certificate for the combined four-source conclusion is claimed here.

The inversion sources place \(x\) in the complete strict postbirth history \(H\) of \(c_2\). Every \(h\in H\) has unique source \(c_2<a<q\) with \(a<h<d(a)\le T\), because survival to \(q\) excludes earlier awards at or below their rows. Starting from \(x\), replace \(h\) by its source diagonal if that diagonal is also in \(H\). Labels strictly increase and are bounded by \(T\), so this ends at \(z=d(b)\notin H\), \(c_2<b<q\), \(x<z\le T\). Source dates need not increase.

The exit \(z\) is neither seed nor private-history label. MEX at the fresh \(c_2\) cell places it at a host \(h<c_2\). LowCellRowStart and diagonal/death disjointness imply \(q<z\), so that host is recomputed. The later \(x<z\) at \(r\) gives an additional private \(x\)-source at \(h\). Its host differs from each \(c_i\): its current award is old \(z\le T\), whereas theirs are fresh. Four distinct hosts yield four distinct source rows and four distinct diagonals in \((x,T]\), proving \(x+4\le T\). Different roots may share increasing-path exits; no reuse bound, K2 or NoTriple theorem follows.

## Full-history no-return and exact relay hypotheses

For a full triangular history \(F\), COPY/MEX uses \(V(t,c)=\{F(s,\min(s,c)):s<t\}\) and strict current prefix. If \(F(s,c)=v\) and \(F(s+1,c)\ne v\), choose a least later return. COPY preserves the previous different value; MEX forbids the old \(v\) in \(V\). Both contradict return. If \(v\le s\) is present at row \(s\), COPY preserves it on every later row.

If \(F(q-1,c)=v=F(q,d)\), \(d\ne c\), row injectivity makes the old/current hosts unique. The new host is MEX rather than COPY (including newborn \(d=q\)), and its whole blocker set omits \(v\). Thus no earlier award in the existing part of that column had \(v\). Also \(q\le v\), since otherwise old host \(c\) would COPY \(v\).

For a same-transition relay, require \(q\ge3\), a root label \(x\) at strict old host \(b<q-2\), absence of \(x\) from the **new retained prefix**, and an exact finite path of drop edges \(c\to d\) satisfying

\[
d<c,\qquad F(q,c)=F(q-1,d).
\]

It ends at a rising host with \(F(q,c)>F(q-1,c)\). Old-row injectivity makes outgoing drop edges deterministic; new-row injectivity gives indegree at most one. If two paths from distinct absent roots meet, backward tracing either makes the roots identical or places one root on the other's path. In the latter case that path emits the root's old label into the new retained prefix, contradicting its absence. Therefore their rising endpoints are distinct. This requires actual absent roots, not labels merely annotated as descendants of earlier roots.

Charge a certified original root \((q,x)\) to its endpoint's old payload and column \((y,c)\), where \(y=F(q-1,c)\), \(F(q,c)>y\). Equal-clock collisions contradict endpoint distinction. At clocks \(q_1<q_2\), the first rise is a departure of \(y\) from column \(c\); no-return forbids \(F(q_2-1,c)=y\). Thus the charge is injective in one fixed history; different histories require a history identifier in the key.

The rise cannot be COPY, so \(y\ge q\ge3\). Leftward relays starting at \(b<q-2\) end at \(0\le c\le q-3\le y-3\). Consequently, **for an arising endpoint payload \(y\ge3\)**, at most \(y-2\) roots are charged to that payload. For arbitrary \(y\ge0\), the total bound is \(\max(0,y-2)\), with no charged roots for \(y<3\). This explicit domain repairs the literal unguarded \(y-2\) wording. Relay existence, absent-root guards and earlier replacement absence remain premises.

## Component overlap identity

Let old and new injective rows \(a_c,b_c\) share the same finite retained column domain \(U\). Put \(A=\{a_c:c\in U\}\), \(B=\{b_c:c\in U\}\); these are finite label sets, not the blocker-count function. Let \(O\) be any fixed ownership set. Draw \(c\to d\) when \(b_c=a_d\). Injectivity gives degree at most one in each direction. A root path cannot enter a cycle or merge with another root path without giving a vertex two predecessors. Components are paths or cycles.

On a path \(c_0\to\cdots\to c_k\), new labels \(b_{c_i}=a_{c_{i+1}}\) cancel internal old labels. The lost root is \(x=a_{c_0}\), the gained exit \(z=b_{c_k}\), so ownership overlap changes by \(1_O(z)-1_O(x)\). Cycle label sets coincide. If every new label is positive and below an old ceiling \(D\), and every positive label below \(D\) lies in \(O\cup A\), then an exit, which is absent from \(A\), belongs to \(O\). Root labels are exactly \(A\setminus B\); owned roots contribute zero and unowned roots one. Summing proves

\[
|B\cap O|-|A\cap O|=|(A\setminus B)\setminus O|.
\]

For a canonical diagonal-drop application, choose a retained domain for which the stated coverage premise is valid. Positivity and drop alone do not restore a removed penultimate source label. This generic component identity does not establish the additional LowLoss guards or capacity one for all paths.
