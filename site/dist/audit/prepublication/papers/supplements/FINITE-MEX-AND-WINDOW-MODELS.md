# Finite MEX insertion, periodic queues and window graph conventions

These models use explicit finite inputs. Their exact output identities do not assert that a canonical growing cascade can be supplied efficiently. No private state is identified merely because two carrier responses agree.

## Two-owner insertion definitions and linkage

For a finite subset \(G\subseteq\mathbb N_0\), let \(\operatorname{mex}_0(G)\) be its least absent nonnegative integer. For a finite context \(S\), define the carrier map
\[
P_G(S)=S\cup\{\operatorname{mex}_0(G\cup S)\}.
\]
For ordered journals \(A,B\), put \(u=\operatorname{mex}_0(A\cup S)\), \(v=\operatorname{mex}_0(B\cup S\cup\{u\})\); \(u\ne v\). The response is the **unordered pair** \(\{u,v\}\), not the updated private journals. For \(x<y\) define
\[
\mathcal E_{AB}(x,y)
= [x\notin A,\ y\notin B]\ \lor\
[x\in A\setminus B,\ y\notin A].
\]

The least output \(x\) is the first label outside \(S\) and \(A\cap B\): every smaller label is either context-blocked or belongs to both journals. If \(x\notin A\), the first owner takes it and the second takes the first later label outside \(S\cup B\). If \(x\in A\setminus B\), the first owner instead takes the first later label outside \(S\cup A\), and the second takes \(x\). This proves the exact sorted-response formula in [response content](../results/two-owner-response-content.md).

For sufficiently large \(z\), \(\mathcal E(x,z)\) holds exactly when \(x\notin A\cap B\), so the relation recovers the intersection. If \(r=\min(A\setminus B)\) exists, \(A\) below \(r\) is the intersection, \(r\in A\), and for \(x>r\), \(\mathcal E(r,x)\) holds exactly when \(x\notin A\). If no such \(r\) exists, \(A=A\cap B\). Once \(A\) is recovered, let \(a=\operatorname{mex}_0(A)\). Below \(a\), membership of \(B\) agrees with the intersection; at \(a\) it is the one bit \(\beta=1[a\in B]\); above \(a\), \(\mathcal E(a,x)\) holds exactly when \(x\notin B\). This is the [phase reconstruction](../results/two-owner-phase-reconstruction.md), which uses exactly the same relation.

The [commutation criterion](../results/two-owner-commutation.md) compares the two carrier orders. If their first MEX values \(a,b\) differ, adding the smaller one does not change the other's MEX: it was already forbidden there. If they coincide at \(t\), \(t\) is outside \(A\cup B\), and equality of the journals above \(t\) makes the second values coincide. Conversely a first disagreement \(w\ge c=\operatorname{mex}_0(A\cup B)\) has \(w>c\). Taking \(S=\{0,\ldots,w\}\setminus\{c,w\}\) makes both first outputs \(c\), but only one second output \(w\). This proves equality in every finite context iff \(A\triangle B\subseteq\{0,\ldots,c-1\}\), without any canonical-state interpretation.

## Periodic forcing and the arrival clock

Let \(p\ge1\), and give finite sets \(U_t\subseteq\mathbb Z_{>0}\), \(U_{t+p}=U_t\), for all nonnegative times. A queue \(Q_t\subseteq\mathbb N_0\) is a finite set of appointment offsets before time \(t\); it survives that arrival iff \(0\in Q_t\). Only for a surviving queue define its ordinary update
\[
F_t(Q_t)=\{v-1:v\in Q_t,\ v>0\}
\cup\{\operatorname{mex}_0(Q_t\cup U_t)-1\}.
\]
Because \(0\in Q_t\) and \(U_t\) is positive, the MEX is at least one, so every output offset is nonnegative. A seed dies at the first arrival without zero. The update preserves cardinality: the MEX is not already in \(Q_t\), and removing its old zero then shifting cannot collide with a retained appointment.

Define the **rescued** update \(G_t(Q)=F_t(Q)\cup\{0\}\), and \(K_0=\{0\}\), \(K_{t+1}=G_t(K_t)\). Every rescued iterate contains zero. For surviving \(Q\subseteq R\), the smaller MEX is no larger than the larger. If they differ, the smaller belongs to \(R\), because it is absent from \(U_t\) and is blocked in \(R\cup U_t\). Therefore \(Q\cup\{\operatorname{mex}Q\}\subseteq R\cup\{\operatorname{mex}R\}\); shifting/removing zero proves monotonicity of \(F_t\) and \(G_t\).

Put \(B=1+\max\bigcup_{t<p}U_t\), with \(B=1\) for an empty union. Inductively \(K_t\subseteq\{0,\ldots,B-1\}\): the MEX is at most \(B\), since \(B\) is in neither queue nor forcing set, and its new offset is at most \(B-1\). Every rescue that was needed increases cardinality by one, while ordinary \(F\) preserves it.

The phase-zero \(p\)-step rescued map is monotone. Since \(K_0\) contains only the mandatory zero, \(K_0\subseteq K_p\), and monotonicity gives
\[
K_0\subseteq K_p\subseteq K_{2p}\subseteq\cdots.
\]
The finite rail forces a first equal pair \(K_{jp}=K_{(j+1)p}\). Equality of endpoint cardinalities means no rescue occurred during that entire block. It is therefore an ordinary, surviving periodic cycle. Let \(h=jp\) and \(\nu=|K_h|\le B\). Every previous strict block increased cardinality at least once, so \(j\le\nu-1\), \(h\le p(\nu-1)\), and detecting the first equality takes \((j+1)p\le p\nu\) queue updates.

For any seed queue that survives arrivals through \(t\), induction gives \(K_t\subseteq Q_t\): ordinary updates are monotone, and an actual surviving arrival contains the zero inserted by rescue. If it survives through \(h\), it contains the immortal cycle at that phase and survives forever by monotonicity. Otherwise it dies at an arrival at most \(h\). This includes \(h=0\). The theorem is a bound in **queue updates**, not bit operations or a fast algorithm for generating the canonical upstream word.

The seed's appointments above \(h\) cannot affect survival before \(h\): until that time they remain positive, and any MEX producing an appointment that arrives by \(h\) is determined by the smaller offsets. This also follows by induction on time comparing queues intersected with the remaining horizon \([0,h-t]\). Once time \(h\) is reached, both either die or contain the same immortal phase. Thus survival depends only on \(Q_0\cap[0,h]\).

## Dyadic matching and square-root windows

Here tokens have signs \(\pm1\) and positive integer dates; every finite date range contains finitely many tokens. A matching pairs opposite signs, each vertex at most once. An endpoint-ratio bound \(\kappa\ge1\) means the larger date is at most \(\kappa\) times the smaller. Define \(W_M(n)\) as the number of matching edges with one endpoint at date at most \(n\), the other after \(n\), and \(U(I)\) as the number of unmatched vertices dated in \(I\).

Bucket each matched pair by \(k=\lfloor\log_2\min(\text{dates})\rfloor\). Its endpoints are in \([2^k,2\kappa2^k)\), so each bucket is finite. Sort its pairs by positive endpoint date; for a nonsingleton bucket add a cyclic edge from each positive endpoint to the next pair's negative endpoint. Parallel edges, if any, count with multiplicity. A singleton adds no edge. The completed graph has degree two at nonsingleton vertices, one at singleton endpoints, zero at unmatched vertices.

At a cut, let \(x_i=1[\text{positive date}_i\le n]\) and \(z_i=1[\text{negative date}_i\le n]\). Sorted \(x_i\) has at most two cyclic transitions. The triangle inequality gives
\[
\sum_i|x_i-z_{i+1}|\le\sum_i|x_i-x_{i+1}|+\sum_i|x_i-z_i|.
\]
Only buckets with \(n/(2\kappa)<2^k\le n\) have nonconstant \(x\), at most \(\lceil\log_2(2\kappa)\rceil\). Thus \(W_G(n)\le2W_M(n)+2\lceil\log_2(2\kappa)\rceil\).

For \(N\ge4\), \(L=\lceil\sqrt N\rceil\), either \(I=[N,N+L-1]\) or \(I=[N-L+1,N]\) lies in \([N/2,2N]\). A singleton pair touching it has bucket scale \(N/(4\kappa)<2^k\le2N\), at most \(\lceil\log_2(8\kappa)\rceil\) scales. Consequently its degree deficit obeys
\[
2U(I)\le\sum_{v\text{ dated in }I}(2-\deg v)
\le2U(I)+2\lceil\log_2(8\kappa)\rceil.
\]

If this matching is on the actual residual canonical tokens, their signed count at row \(q\) is \(Q(q)+2\), with distinct multiplicity as in the definition sheet. Opposite-sign edges cancel internally, yielding
\[
2\sum_{I}\operatorname{sign}(v)
=\sum_I\operatorname{sign}(v)(2-\deg v)
+\sum_{\partial I}\operatorname{sign}(\text{inside endpoint}).
\]
Uniform \(U(I)=O(N)\) in both window directions and \(W_M(n)=O(n)\) imply \(|\sum_I(Q+2)|=O(N)\). If additionally \(Q(q)-Q(q-1)\le K\), take \(K\ge0\) without loss. Backwards \(Q(N-j)\ge Q(N)-Kj\), and forwards \(Q(N+j)\le Q(N)+Kj\). Summing \(L\) terms gives both \(Q(N)\) and \(-Q(N)\) at most \(O(N/L)+KL/2+O(1)\), hence \(Q(N)=O(\sqrt N)\). Each canonical matching, window, cut and increment supplier remains an explicit assumption.

Finally the unit-delay counterexample is self-contained: at date \(2k\) put \(2k\) positive tokens, at \(2k+1\) put \(2k\) negative tokens, pairing equal local indexes. Its crossing inventory is \(2k\) at even cuts and zero at odd cuts, \(O(n)\), but pointwise signed charge has absolute value \(2k\) on both dates and is not \(o(n)\). This is an abstract event stream, not a canonical Chomp realization.
