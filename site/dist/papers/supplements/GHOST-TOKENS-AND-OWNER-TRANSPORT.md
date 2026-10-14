# Ghost tokens, owner transport and the exact unpaid endpoints

Use [Canonical definitions](CANONICAL-DEFINITIONS.md) throughout. The [canonical foundation](../../audit/full/CANONICAL-FOUNDATIONS.md) supplies positive MEX, injectivity, strict diagonal maximality, seeded-column nonreuse, diagonal/blocker disjointness, future-freeze and victim propagation. This supplement proves the stated finite identities and injections; it supplies no asymptotic cancellation assumption.

## 1. Live-mortal cancellation and the spatial ledger

The overlap formula follows by counting the union of the \(q\) earlier diagonals and \(q\) current-prefix labels. It contains every positive label below \(d(q)\), excludes \(d(q)\), and has precisely \(H_q\) labels above it. Inclusion-exclusion gives \(d+I+H=2q+1\). Exactly \(A(q)\) victim columns have frozen by the completed row, hence \(m=q+1-A(q)\) and \(Q=2I+2H-m-1\).

An old diagonal \(y=d(a)\) currently served has physical host \(c<a\), and cannot freeze because a frozen label is a blocker. For a mortal owner still alive, \(q<\sigma_a<y<d(q)\). Its blocker \(\sigma_a\) is nonpast and below \(d(q)\), so coverage puts it in the row prefix; it is live because it exceeds \(q\). Each such owner has a distinct death blocker, and every predeath service of that blocker has host below its victim \(a\). This proves the live-mortal injection. Partition the live row as its own diagonal, old diagonal services \(I\), live blockers \(B\), and future diagonals \(F\). Substituting \(I=L+J+D\), \(B=L+B_0\) gives

\[
Q+2=J+D+2H-B_0-F.
\]

At \(q=0\), \(d=1,A=0,Q=-2\), with all residual counts zero, so the constant is checked.

For the spatial ghost graph, one emitted label and row/diagonal injectivity give indegree and outdegree at most one. Every edge \(c\to a\) has \(c<a\), so finite components are paths. Nonterminal vertices are live current service hosts. A path with \(e\ge1\) edges contains \(e+1\) live vertices if its terminal is live, and \(e\) if its terminal is dead. Its contribution to \(2I-m\) is therefore \(e-1\) or \(e\). An isolated live vertex contributes \(-1\). Consequently

\[
Q=X_L+X_D+2H-Z-1.
\]

This keeps every dead terminal and every isolate; it does not assert that either number is bounded.

For a path \(v_0\to\cdots\to v_e\) with \(k\) available vertices, capacity one bounds the endpoint matching by \(\min(e,k)\). If all vertices are available, pair edge \(i\) to target \(v_{i+1}\), obtaining \(e\) matches. Otherwise choose a nonavailable \(v_j\). Pair available \(v_i\), \(i<j\), to edge \(i\), and available \(v_i\), \(i>j\), to edge \(i-1\). The two edge-index ranges are disjoint and each assignment is incident, saturating all \(k\) available vertices. This proves the optimal size. For nonsource vertices, availability is exactly mortality with survival after \(q\), by future-freeze and current service of their diagonal. The source can add one match relative to target-only pairing exactly when it is available and some target is unavailable. No matching rule here establishes an endpoint or cut asymptotic.

## 2. Completed lifetime demand and its quadratic caps

For an owner \(a\), write \(y=d(a)\). There are \(a-A(a)\) older columns alive after its birth. At such a host \(h<a\), a private \(y\) service occurs before \(y\), or the host dies unserved before \(y\). Indeed a host still live at row \(y\) recomputes above \(y\), while \(y\) cannot occur at its own numerical deadline. MEX must put \(y\) in its private journal; it is not an inherited seed at \(h<a\). Birth \(a\) cannot be its service row, since \(y\) occurs only at the diagonal cell there. Death exactly at \(y\) is impossible because \(y\) is diagonal.

Prebirth services \(t<a\) have \(d(t)>y\), at most \(H_a\) of them by row injectivity. Postbirth services are actual old-diagonal \(I_t\) cells, with \(a<t<y\le2a+1\), so owners \(a\le N\) finish by row \(2N\).

An unserved death at blocker \(p\) with victim \(s(p)=h\) satisfies \(s(p)<a<p<d(a)\). For fixed \(p\), at most \((\min(N,p-1)-s(p))_+\) owner indexes qualify. Also there are at most \(A(p)-1\): predeath rows with \(d(a)>p\) number exactly \(A(p)\), and the row \(a=s(p)\) is one of them by future-freeze but does not qualify. Thus, with the definitions in the result,

\[
M_N:=\sum_{a=0}^N(a-A(a))
\le\sum_{q=0}^{2N}I_q+\sum_{a=0}^NH_a+C_N.
\]

To check the coefficient, write \(p_j,s_j\) for blocker rank \(j\) and victim. Reach and the count floor give \(2j\le p_j\le3j+O(1)\). The first row \(\tau(p)\) with \(d(\tau)>p\) has \(\tau\ge\lceil p/2\rceil\); all \(A(\tau)\) already-dead victims are unavailable to the \(j\) distinct bookers below \(s_j\). Therefore \(s_j\ge j+A(\tau)\ge j+p_j/6-O(1)\). Maximizing the cap over \(p\in[2j,3j+O(1)]\), with all fixed errors absorbed uniformly, gives the piecewise envelope

\[
j\ (j\le5N/12),\quad 5N/6-j\ (5N/12<j\le N/2),
\quad N-4j/3\ (N/2<j\le3N/4),\quad0.
\]

Its integrals are \(25/288,9/288,12/288\) times \(N^2\), yielding \(23/144\). The upper count \(A(a)\le\lfloor a/2\rfloor\) gives \(M_N\ge N(N+1)/4\). Enlarging the \(H\) sum to \(2N\) and replacing \(N\) by \(\lfloor X/2\rfloor\) gives

\[
\liminf_X X^{-2}\sum_{q\le X}(I_q+H_q)\ge13/576.
\]

Finally \(K_q=I_q+H_q=2q+1-d(q)\le q/2-3/2\) eventually by the checked lower diagonal bound. Thus \(K_q\le m_q+1\), and
\((m_q+1-2K_q)_+\le m_q+1-K_q\). The lower count floor bounds \(\sum(m_q+1)\le N^2/3+O(N)\). This gives the negative-energy coefficient \(1/3-13/576=179/576\). A quadratic bound is not an \(o(N^2)\) estimate.

## 3. The two-label owner partition

Fix mortal \(a\), \(p=\sigma_a\), \(y=d(a)\). Each postdeath \(y\)-service \((t,h)\), \(p\le t<y\), has \(h<a\) and has survived to row \(p\). There \(p\) occurs uniquely at victim \(a>h\), so \(f(p,h)>p\). MEX forces \(p\) into that host's earlier journal, not its prefix; \(p\) is a blocker, hence not a seed. The unique private source \((u_h,h)\) has \(u_h<p\). Distinct \(y\)-services use distinct hosts and give distinct \(p\)-cells. This proves the historical source injection but does not declare those cells free \(B_0\).

Every \(P_a\) host has exactly one of the four mutually exclusive \(y\) types: prebirth \(X_a\), predeath \(E_a\setminus C_a\), postdeath \(D_a\), or never \(W_a\). Therefore

\[
|P_a|=|X_a|+|E_a|-|C_a|+|D_a|+|W_a|.
\]

Each \(E_a\) row contains a unique \(p\)-service by coverage. Different \(E\) rows use different private \(p\)-hosts, so \(R_a\) omits exactly \(|E_a|\) of the \(|P_a|\) services. Subtraction proves

\[
|D_a|-|R_a|=|C_a|-|X_a|-|W_a|.
\]

A \(C_a\) host dies after its \(y\)-service but before \(p\): if it survived to \(p\), the preceding MEX argument would make it a \(p\)-booker. A \(W_a\) host dies before \(y\) by the diagonal-deadline argument. Its death need not be after \(p\).

With the signed \(V_a\) from the definition sheet, the difference counts all \(p\)-services positively and the corresponding \(y\)-services or \(W\)-deaths negatively:

\[
\Delta V_a=R_a+C_a-X_a-D_a-W_a
\]

as dated event counts. The virtual \(E\)-event and its same-row \(p\)-service cancel; reverse intervals are retained. For fixed \(q\), a relevant award before \(q\) has numeric label at most \(2q+1\), hence only finitely many possible owners; a relevant \(W\) death has an earlier \(p\)-award. Summation is therefore legitimate and yields

\[
D_q-B_{0,q}=C_q-X_q-W_q-\Delta V(q).
\]

This is an actual service stock, not a stock defined by integrating \(Q\). Its derivative remains uncontrolled.

## 4. Inversion sources and the degree-two multigraph

For \(t<a\), \(d(t)>y=d(a)\), \(y\) is nonpast and below the diagonal in row \(t\). Coverage gives one unique actual future-diagonal cell. Conversely every future-diagonal service yields precisely this inversion. This is the \(H_1(a,t)\leftrightarrow F(t,a)\) bijection, with dates \(a\) and \(t\).

If \(a\) is mortal, \(t<a<p<y<d(t)\), so the same row also serves \(p\). Its victim is not yet an old owner, hence this \(p\)-token is \(B_0\), not a canceled \(L\). The pair (row, death label) uniquely determines \((t,a)\), giving the mortal \(H_2\) injection. The two \(H\) copies are distinct positive tokens.

For each mortal owner temporarily retain all \(E\) positives and their same-row \(p\) negatives. Matching \(S\) joins each \(p\)-service to its \(y\)-service at the same physical host, if present; nonreuse gives degree at most one on each side. Matching \(T\) joins each \(E\) to the same-row \(p\), and each prebirth \(H_2\) to its actual source-row \(p\). Their source row ranges \(t>a\) and \(t<a\) are disjoint. Different owners have different blocker labels, so no cross-owner collision occurs.

The union is an opposite-sign multigraph of maximum degree two. Remove each virtual \(E/p\) pair: two external edges splice opposite-sign endpoints, one leaves its endpoint with lower degree, and a fully virtual cycle disappears. Parallel walks are kept separately. Degrees cannot increase above two, and signed row charge is unchanged because each removed pair had a common date. Remaining mortal vertices are \(H_2,D,B_0\); add the separate \(H_1/F\) matching and retain immortal \(J,H_2\) as isolates.

A predeath \(p\)-service row \(u\) obeys \(p<d(u)\le2u+1\), thus \(u\ge p/2>a/2\), and \(u<p\le2a+1\), thus \(u\le2a\). The remaining \(H_2\) date is \(a\), and \(D\) dates lie in \([p,y)\subset(a,2a]\). Every surviving contracted mortal edge therefore has endpoint ratio \(<4\). Likewise \(d(t)>d(a)>a\) and reach imply \(t>a/2\), giving ratio \(a/t<2\) for \(H_1/F\). No zero-date exception occurs. Isolated \(D\)-vertices after contraction are allowed, not silently paired.

## 5. The complete chronological ray and exact crossings

The canonical count floor implies infinitely many blockers, and distinct victims give infinitely many mortal owners. Each has a birth-row \(B_0\) service of its death blocker. Column zero follows \(f(q,0)=q+1\) by direct induction: its journal contains \(1,\ldots,q\), with no COPY. At row \(y-1\), it serves a mortal owner's \(y=d(a)\) after the owner's death \(p<y\), producing a \(D\)-token. Hence both residual signs occur infinitely often.

Order all positive tokens \(u_k\) and all negative tokens \(v_k\) by date and fixed type/owner/host/source/copy tags. Each date is finite, so this enumerates every token once. Edges \(u_k-v_k\), \(v_k-u_{k+1}\) form one alternating ray. Every vertex has degree two except \(u_1\), of degree one; its total intrinsic deficit is one. This assertion is about the constructed ray, not historical MEX causation.

If \(p_n,m_n\) count the positive and negative tokens through date \(n\), the first edge family crosses the cut in the symmetric difference of the rank intervals \([1,p_n]\), \([1,m_n]\). The second uses \([1,\max(p_n-1,0)]\), \([1,m_n]\). Thus

\[
W_{\rm rank}(n)=|p_n-m_n|+|m_n-\max(p_n-1,0)|,\quad
p_n-m_n=\sum_{q\le n}(Q(q)+2).
\]

No bound on this signed prefix is supplied by the construction.

## 6. Reverse-source forest and the repaired death identity

At a \(C\)-host's \(y\)-service, \(p\) is absent from its whole journal. At a reverse \(P\)-host's \(y\)-service, its unique \(p\)-service is later, so \(p\) is again absent. Positive MEX places \(p\) at a strictly lower host in the same row. Distinct domain \(y\)-cells use distinct rows, and target \(p\)-cells have distinct hosts by private nonreuse. This gives an injective, host-decreasing map from \(C_a\) and reverse \(P_a\) hosts into \(P_a\).

Follow outgoing edges at reverse targets. Finite strict host decrease prevents cycles; indegree at most one and starts outside \(P_a\) prevent two \(C\)-paths merging. A terminal lies in \(P_a\) outside the reverse set, hence is forward or \(W\). At each continuation its \(y\)-service precedes the incoming \(p\)-source row, so time also decreases along successive source steps.

At a \(C\)-start, \(a<t<\sigma_h<p\), so \(t\le p-2\). Every terminal \(p\)-source row remains at most \(p-2\). Rail zero serves \(p\) exactly at \(p-1\), and hence is excluded. Restricting the first-source injection to domain hosts at most \(b\) gives the host-prefix inequality with target hosts strictly below \(b\). A forward terminal can be an unpaid postdeath \(D\), so this is not direct-Q A1.

For the death-swap identity, use the universe \(\{0,\ldots,a-1\}\), \(V_a^{\rm dead}=\{h<a:\sigma_h\le a+1\}\), \(S=P_a\cap V_a^{\rm dead}\), and \(M=\{h<a:\sigma_h>a+1,\ h\notin P_a\}\). The only victim of a blocker through \(a+1\) possibly outside the universe is \(a\) itself, precisely when \(p=a+1\). Thus

\[
|P_a|=A(p),\quad |V_a^{\rm dead}|=A(a+1)-1[p=a+1],
\quad P_a\cup V_a^{\rm dead}=\{0,\ldots,a-1\}\setminus M.
\]

Inclusion-exclusion proves \(A(p)+A(a+1)-a=|S|-|M|+1[p=a+1]\). At \(a=1,p=2\), the literal rows \([1],[2,3],[3,2,4]\) give \(P=\{0\}\), \(S=M=\varnothing\), and \(K=1\), checking the correction. It proves no sign inequality.

## 7. The specified dated owner matching

Pair each \(F\) with its \(H_1\) and each mortal \(H_2\) with its prebirth \(R\) source, negative date first. Let \(T_a\) count those \(R\) sources. From the remaining \(R'_a\), select the latest \(m=\min(|D_a|,|R'_a|)\) dates; select the earliest \(m\) \(D_a\) dates and pair the two sorted lists. Every \(R'\) date is below \(p\), every \(D\) date at least \(p\), so all edges are forward and capacity one. Unmatched owner counts are the positive/negative parts of \(\chi_a=T_a+|D_a|-|R_a|\). The completed partition gives \(\chi_a=|C_a|+T_a-|X_a|-|W_a|\), retaining the prebirth correction.

For one matched edge with negative date \(u\), positive date \(v>u\), its signed contribution on \([l,r]\) equals \(1[u\le l-1<v]-1[u\le r<v]\). Summing finite crossing inventories gives

\[
\sum_{q=l}^r(Q(q)+2)=U_+([l,r])-U_-([l,r])
+X_{\rm cross}(l-1)-X_{\rm cross}(r).
\]

The stock splits into all inversion crossings, mortal inversion crossings, and selected \(D/R'\) crossings. Latest \(R'\) minimizes crossings before \(p\), earliest \(D\) minimizes them after \(p\); the bijection between the chosen lists does not change cut counts. None bounds that minimum.

## 8. Immortal mass and a limited forward source

For blocker rank \(j\), all \(j\) distinct bookers lie below \(s_j\). Every other column below \(s_j\) is an already-frozen victim: if live at \(p_j\), it must have booked \(p_j\) by MEX and the unique later victim. There are at most \(j-1\) earlier victims, proving \(s_j\le2j-1\). A victim \(s_i\) with \(p_i+s_i<p_j\) never served \(p_j\), by cell reach before its death and COPY afterwards. Propagation puts it below \(s_j\). Hence

\[
s_j\ge j+\#\{i:p_i+s_i<p_j\}.
\]

For \(A(x)\ge\alpha x-C\), \(p_i\le(i+C)/\alpha\), \(s_i\le2i-1\), \(p_j\ge2j\). Ranks through \(2\alpha j/(1+2\alpha)-O(1)\) are reach-excluded. Therefore \(s_j\ge[(1+4\alpha)/(1+2\alpha)]j-O(1)\), and counting distinct victims below \(x\) gives
\(\operatorname{Imm}(x)\ge[2\alpha/(1+4\alpha)]x-O(1)\). The proved count floor permits \(\alpha=1/3\), yielding \(2x/7-O(1)\).

For every immortal pair \(h<a\), the older host serves \(y=d(a)\) before deadline \(y\), once. If its date exceeds \(a\), it gives actual \(J\); if before \(a\), its unique source row gives immortal \(H_2\). The date of the token is in \([a,2a]\). Distinct pairs give distinct tagged tokens. Restrict both indexes to \([\lceil N/7\rceil,N)\): there are at least \(N/7-O(1)\) immortal indexes, hence at least \(N^2/98-O(N)\) pairs in the annulus \([\lceil N/7\rceil,2N)\). A mortal-only matching leaves all such tokens unmatched. Covering the annulus by \(O(\sqrt N)\) consecutive forward square-root windows would give only \(O(N^{3/2})\) unmatched tokens under a uniform \(O(q)\) window bound, a contradiction. This obstructs mortal-only matching, not all matching or canonical \(Q=o(n)\).

Finally fix an immortal **physical host** \(h\). Infinitely many distinct blocker victims lie to its right. At each corresponding death row \(p\), host \(h\) is live and strictly left of the unique \(p\)-cell, so MEX forces an earlier private \(p\)-service there. If \(p>N+h+1\), reach excludes service at any time at most \(N\). Thus services occur arbitrarily late. Enumerate immortal-positive tokens whose underlying actual diagonal service host is this immortal \(h\) (a \(J\)-token dated at its service, or an immortal-owner \(H_2\) dated at its owner). Recursively choose a same-host blocker service after both the current token date and all earlier chosen dates. This yields an injective forward assignment. Different hosts give different cells. Selected blockers need not be free \(B_0\), and delays/crossings are uncontrolled. The hypothesis on the physical host is essential; mortality of another service host is not ignored.

## What remains unpaid

All these proofs keep their actual host, owner, token multiplicity and date. They do not prove a nonnegative victim gate, direct-Q A1, bounded crossing load, uniform square-root-window unmatched count or pointwise \(Q=o(n)\). An identity of signed inventories is not an estimate of its absolute terms.
