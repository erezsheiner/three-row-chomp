# Two bottom cuts exclude every penultimate lag through 124

This is the complete written argument for the result `legacy-bottom-two-cut-124`. It uses the canonical three-row Chomp completion theorem and explicitly specified finite certificates. The derived lag bound is a paper theorem supported by exact finite checks; it is not itself a Lean theorem. The definitions, finite obligations and induction connecting them to all rows are given below.

## 1. Game conventions and statement

A position is an ordered triple of natural row lengths `(a,b,c)`, with `a >= b >= c` and `a > 0`. The upper-left cell is poison. The legal moves are:

* a top-row cut to `x`, where `1 <= x < a`, producing `(x,min(b,x),min(c,x))`;
* a middle-row cut to `y`, where `0 <= y < b`, producing `(a,y,min(c,y))`;
* a bottom-row cut to `z`, where `0 <= z < c`, producing `(a,b,z)`.

A P-position has no P-position among its legal options; an N-position has at least one P-position among its legal options. These statements follow by induction on the number of cells, with the poison-only position `(1,0,0)` a P-position.

Write `F(q,c)` for the canonical completion table on `0 <= c <= q`, and `d(q)=F(q,q)`. Its actual-game interpretation, proved in `ChompLean/Encoding.lean` and `ChompLean/Proof.lean`, gives

\[
 (a,q,c)\text{ is P}\quad\Longleftrightarrow\quad F(q,c)=a
 \qquad(a\ge q).
\]

If `F(q,c)<q`, there is therefore no P-position `(a,q,c)` with `a>=q`. This possibility is not discarded in the argument. The penultimate value is always at least `q`, and the diagonal is strictly larger than every earlier entry of its own row. The latter follows from diagonal maximality and row injectivity.

For `k>=0`, `m>=1` and `b>=m`, let

\[
 E(k,m;b)\quad\text{mean that }(b+k,b,b-m)\text{ is P}.
\]

The lag is `k`, the age is `m`, and the phase is `b mod 2`. Let `W(X)` denote the set of **P-position targets**, as ordered triples, obtainable from `X` by one legal move; it is not merely the set of names of winning cuts.

**Theorem.** For every integer `b>=500`,

\[
 F(b,b-1)>b+124.
\]

Consequently, for every `0<=k<=124`,

\[
 W(b+k,b,b-1)=W(b+k,b,b).
\]

No claim about lag tending to infinity, arbitrary lag cutoffs or a general decision algorithm follows from this theorem.

## 2. Exact periodic column certificate

The portable data file `certificates/inputs/periodic_C300_and_lag120.json` contains, for each column `0<=c<=300`, either a frozen value `v_c<500` or two positive integers `g_c(0),g_c(1)`. Its asserted formulas are

\[
 F(q,c)=v_c\quad\text{or}\quad F(q,c)=q+g_c(q\bmod2)
 \qquad(q\ge500).
\]

The data, not a textual status label, specify the finite certificate. They can be checked with `certificates/run_checks.py`, whose input manifest authenticates their bytes. In particular both phases have lag 123 in column 208 and lag 124 in column 210.

Here is why the finite periodic check implies the formulas for all `q>=500`. The canonical recurrence copies `F(q-1,c)` precisely when `c<q` and that value is below `q`. Otherwise it chooses the least positive integer absent from the union of the current strict row prefix and the column journal. That journal consists of the diagonal seeds `F(t,t)` for `t<c`, together with `F(t,c)` for `c<=t<q`. The canonical game theorem also supplies the live-floor property: in a noncopy cell the value is at least `q`.

The checker rebuilds a triangular prefix directly from this recurrence, starting at `F(0,0)=1`; it does not use a cached research engine. Uniqueness by induction on `(q,c)` identifies this table with the actual completion table. The periodic certificate has maximum offset `G=176`, and the maximum label in relevant history before row 500, including inherited diagonal seeds, is `H=675`. Put `T=max(500+G,H+1)=676`.

All 52,976 cells in columns 0 through 300 and rows 500 through 675 are checked against the proposed formulas. A frozen column also satisfies `F(499,c)=v_c<500`, so COPY preserves it forever. For a periodic column the previous value is at least the new row, since its previous offset is positive; hence this column always recomputes. For each such column and each phase `r`, the checker verifies

\[
 g_c(r)=\operatorname{mex}_{\ge0}\left(
 \{g_c(r-s\bmod2)-s:1\le s\le G\}
 \cup\{g_e(r):e<c\text{ is periodic}\}\right).
\]

There are 250 such identities. For `q>=T`, all history before row 500 is below `q`. A later historical entry more than `G` rows old is also below `q`, since `q-s+g_c(r-s)<q` when `s>G`. Frozen current-prefix entries are below `q`. Thus the displayed finite set is exactly the nonnegative-offset part of the real source, after subtracting `q`. The live-floor property takes care of all smaller positive labels. Induction first on the row and then on the column now proves the formulas. This is an all-index induction, not an inference from observed periodicity.

For each phase `r`, let `R_r` be the dictionary that maps each occurring periodic lag to its host column. The checker verifies that it is a function: two periodic columns do not have the same lag in a phase. Whenever

\[
 k\in R_r,\quad b\equiv r\pmod2,\quad b\ge500,\quad R_r(k)<b-m,
\]

the position in `E(k,m;b)` can shorten its bottom row to the P-position `(b+k,b,R_r(k))`. It is therefore N. We call this a **rail exclusion**; its strict host-below-bottom condition is essential.

## 3. All new replies after a bottom cut

Suppose `X=(b+k,b,b-m)` is P. Shorten its bottom row by `t>=1`, with `t<=b-m`, obtaining the N-position

\[
 Y_t=(b+k,b,b-m-t).
\]

Every option of `Y_t` which was already an option of `X` is N. The remaining possible P replies are exactly

\[
\begin{array}{ll}
 E(k+j,m+t-j;b-j), & 1\le j\le m+t-1,\\
 E(0,h;b-m-t+h), & 1\le h\le m+t-1,\\
 E(\ell,m+t;b), & 0\le\ell<k.
\end{array}\tag{1}
\]

To verify completeness, a further bottom cut is already an option of `X`. A middle cut to at most `b-m-t` is also an old option, since both lower rows then have that length. The other middle cuts have new middle length `b-j`, with `1<=j<=m+t-1`, giving the first family. A top cut to at most `b-m-t` is an old option. Top cuts strictly between that length and `b` give equal first and second rows of length `b-m-t+h`, hence the second family. Top cuts from `b` to `b+k-1` give the third family. This exhausts the three kinds of legal move, including their boundary values.

For the one-cell cut `t=1`, encode a child by `(k',m',s)`, where its middle row is `b-s`. The three families become

\[
 (k+j,m+1-j,j),\quad(0,h,m+1-h),\quad(\ell,m+1,0).
\tag{2}
\]

Each transition either decreases `b` or keeps `b` fixed and strictly decreases `k`. It never increases the top coordinate: `b-s+k'<=b+k`. In the middle-cut family equality holds; in both top-cut families it decreases. Consequently these transitions are well-founded in lexicographic order on `(b,k)`.

## 4. The prior bound through lag 120

The finite state set `S_120` in the same data file is independently reconstructed as follows. Start with every non-rail state `(k,1,r)` with `0<=k<=120` and both phases. For each state and each child in (2), shift phase to `r-s mod 2`. Discard rail-excluded children; retain all other children and repeat until closed. The checker compares the resulting set, rather than just its size, with the saved finite set.

The reconstructed set has 1,284 states and 82,217 examined child entries. Every rail child has `host+m'<500`; the maximum age and backward jump of the retained construction are 36. Direct recurrence checks establish that each phase-matching state is N at each row from 500 through 535, giving 23,112 checks.

Induct lexicographically on `(b,k)` to show that every state of `S_120` is N at every matching row `b>=500`. The checked rows are the base. Above them `b>=536`, so a backward jump of at most 36 stays at or above 500. If a state were P, its one-cell shortening would be N and would have a P reply from (2). A rail child is N by the strict host inequality. Every retained child is N by the induction hypothesis, either at an earlier row or at the same row with smaller lag. This is a contradiction. The legal cut condition holds because every age is at most 36 and every row is at least 500.

It follows, using the root states and rail exclusions, that

\[
 F(b,b-1)>b+120\qquad(b\ge500).
\tag{3}
\]

The same proof supplies every auxiliary state actually in `S_120`, including the needed lag-zero states of ages one and two. Membership, rather than an informal name for an auxiliary lemma, is checked by the portable checker.

## 5. The finite context graph

To retain simultaneous P information, a state is now `(k,m,r,h)`, where `h` is a word of length at most three over the two letters `A,B`, recording the final consecutive special transitions. Start with the empty-history states `(k,1,r,empty)` for all non-rail `0<=k<=122`.

Generate all one-cell children (2). A rail child is removed only after checking its host condition. Label a non-rail transition by

\[
 A:(121,m;b)\longrightarrow(122,m;b-1),
 \qquad
 B:(122,m;b)\longrightarrow(121,m+1;b).
\]

Any other transition clears the history. For an `A` or `B`, append the letter. If its last four letters are `ABAB` or `BABA`, stop that edge; otherwise retain the last at most three letters and continue closure. A stopped edge is **not** treated as impossible. It records five simultaneous P events whenever an actual P path takes it.

The following are explicit finite obligations checked from this construction:

* the closed set has 1,510 states and 104,995 examined child entries;
* each retained step has the coordinate monotonicity from (2), and every backward jump is at most 39;
* every removed rail child has age at most 40 and `host+age<500`;
* reversing each stopped four-letter trace reconstructs a root of age exactly one and lag 121 for `ABAB`, or lag 122 for `BABA`, in either phase; the middle row drops by two over the four steps;
* each phase-matching projected state `(k,m,r)` is N at each row 500 through 538; these are 29,339 direct checks and do not depend on assuming its remembered past;
* for every phase and every non-rail `0<=ell<=120`, the empty-history states `(ell,2,r,empty)` and `(ell,3,r,empty)` belong to the graph.

These conditions can be reproduced from the included periodic data using the stated finite closure rule. No unreleased graph file or historical success label is required.

**Empty-history descent lemma.** If `(k,m,r,empty)` belongs to the context graph and `E(k,m;b)` holds at a matching `b>=500`, then some penultimate P event satisfies

\[
 E(j,1;b'),\qquad j\in\{121,122\},\qquad
 500\le b'\le b,\qquad b'+j\le b+k.
\tag{4}
\]

Indeed, shorten one bottom cell and choose a P reply from (2). Rail exclusions prevent choosing a discarded rail child. A retained child continues the actual P path with its genuine history; a stopped child displays the five P events. The process cannot continue indefinitely, because `(b,k)` decreases lexicographically. From any row at least 539 a jump of at most 39 stays at or above 500. The path cannot enter rows 500 through 538, whose projected events are all N. Therefore it stops in one of the two traces. Its reconstructed first event has age one by the checked trace reversal. Because the initial history was empty, this first event lies on the actual path, not in an assumed past before the starting event. The monotonicity of middle and top coordinates proves (4).

For clarity, the five states in an `ABAB` stop rooted at `b` are

\[
 E(121,1;b),\ E(122,1;b-1),\ E(121,2;b-1),\
 E(122,2;b-2),\ E(121,3;b-2).
\]

For `BABA` they are

\[
 E(122,1;b),\ E(121,2;b),\ E(122,2;b-1),\
 E(121,3;b-1),\ E(122,3;b-2).
\]

One must not erase nonempty history and then claim that an arbitrary projected state is impossible. Only the explicitly checked empty-history memberships above are used as starting points for (4).

## 6. Minimality and the lag-121 contradiction

Assume some `b>=500` has `F(b,b-1)<=b+122`, and let `B` be the least such row. By (3) its lag is 121 or 122. The direct base checks for the corresponding roots imply `B>=539`.

For every `0<=ell<=120`, both

\[
 (B+\ell,B,B-2),\qquad(B+\ell,B,B-3)
\tag{5}
\]

are N. A rail lag has a fixed-column P option because its host is at most 300 and the bottom is at least 536. A non-rail lag has the required empty-history graph state. If it were P, (4) would give a penultimate failure at `b'<=B`. If `b'<B`, this contradicts minimality. If `b'=B`, its top is at least `B+121`, contradicting the bound `b'+j<=B+ell<=B+120`.

Apply the same descent to the first-failure root itself. The stopped pattern has a penultimate root at a row `b'<=B`; minimality gives `b'=B`, and uniqueness of the completion at `(B,B-1)` fixes its lag and orientation. Thus a first failure of lag 121 must start an `ABAB` pattern. Its second event is `E(122,1;B-1)`, which is a penultimate failure at the earlier row `B-1>=500`. This contradiction excludes lag 121.

## 7. Lag 122 and the second bottom cut

It remains to suppose

\[
 X=(a,B,B-1)\text{ is P},\qquad a=B+122.
\]

The `BABA` pattern forces the P-position

\[
 Q=(a-1,B,B-2).
\tag{6}
\]

There is also a direct check of this consequence: after one bottom cut, formula (1) has the middle child at lag 123, excluded by its rail; a lag-zero face, excluded by Section 4; and the top children. The top children of lags at most 120 are N by (5), leaving precisely `Q`.

Now make a different move from `X`: shorten its bottom by **two** cells. This gives the N-position

\[
 Y=(a,B,B-3).
\]

It must have a P reply. Formula (1), with `(k,m,t)=(122,1,2)`, lists the following new candidates; all other options were already options of the P-position `X`:

1. `(a,B-1,B-3)` and `(a,B-2,B-3)`, at lags 123 and 124. Their rows are at least 537 and their bottoms at least 536, so the certified hosts 208 and 210 lie strictly below the bottom. Both positions are N.
2. `(B-2,B-2,B-3)` and `(B-1,B-1,B-3)`, the lag-zero states of ages one and two. Their rows are at least 537, so Section 4 makes both N.
3. `(B+ell,B,B-3)` for `0<=ell<122`. Those with `ell<=120` are N by (5). The remaining position `(B+121,B,B-3)` is a legal one-bottom-cell option of the P-position `Q` in (6), and is therefore N as well.

There are 126 candidate entries per phase, hence 252 phase cases in the portable finite check. The final `(121,3,0)` entry is deliberately left as the written `Q`-attack argument above; it is not certified merely by a numerical observation. Every possible P reply of `Y` has now been excluded, contradicting that `Y` is N.

There is no first failure at lag 121 or 122. Thus `F(b,b-1)>b+122` for every `b>=500`. The lag-123 and lag-124 rails also exclude the next two possible penultimate completions, with hosts strictly below `b-1`. This proves the asserted bound through 124.

## 8. Equality of the neighboring winning-target sets

Fix `b>=500` and `a=b+k` with `0<=k<=124`. Put

\[
 X=(a,b,b),\qquad Y=(a,b,b-1),\qquad f=F(b,b-1).
\]

The bound just proved gives `a<f`. Row maximality and injectivity give `f<d(b)`, so also `a<d(b)`. Compare their moves as sets of position targets:

* Middle cuts agree exactly, since a new middle length below `b` is at most `b-1` and truncates both bottoms to that length.
* Bottom cuts agree except that `X` has the extra option `Y`. This extra option is N because its top `a` is below the unique completion `f`.
* Top cuts to a length below `b` agree exactly: both yield a square triple. Top cuts to a length `t` with `b<=t<a` may differ. The target `(t,b,b)` is N because `t<d(b)`; the target `(t,b,b-1)` is N because `t<f`.

Every differing option is therefore N, while the common options have the same outcomes. Hence the sets of P targets are equal, proving the second assertion without a separate asymptotic diagonal estimate.

## 9. Reproducibility and scope

The only finite input needed for this proof is `periodic_C300_and_lag120.json`, authenticated by `certificates/INPUT-MANIFEST.json`. The public checker rebuilds the recurrence through row 810, reconstructs both finite closures, checks all their relevant bases and phases, and checks the complete terminal classification. The finite counts reported here are reproducibility checks, not substitutes for the move classification, periodic induction, well-founded descent or first-failure argument supplied in Sections 2–8.

The canonical recurrence and game interpretation are formalized in the attached Lean sources. The combination of that foundation, the finite certificate, and this written derivation is the evidence for the paper theorem. This model-assisted reconstruction is not external human peer review or certification of novelty.
