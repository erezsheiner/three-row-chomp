> Work in progress. This project is under active development and may contain errors. Results, proofs, and documentation may be revised.

# Reviewed paper proofs — 14 October publication edition

This edition contains 59 paper-result entries, each with explicit hypotheses and full linked definitions and derivations. The historical review admitted 56 statements and repaired three; the renewed review additionally clarifies the relay domain and three compact proof passages. Eight entries remain conditional. The three excluded open or unresolved claims are not result entries.

The review is model-assisted mathematical examination. These paper conclusions are not all Lean formalizations. [Complete proof navigation](supplements/INDEX.md) · [Audit scope](../docs/AUDIT-SCOPE.md) · [Renewed per-result review](../audit/prepublication/papers/PAPER-REVIEW.json).

<a id="q-mortal-echo-injection"></a>

## A surviving mortal diagonal echo has a distinct death-blocker partner

**Statement.** At every canonical row q, each old diagonal echo d(a) with mortal owner a and q<sigma_a maps injectively to the row-q service of sigma_a at a host<a. With L, J, D partitioning old echoes and B0=B-L, Q(q)+2=J+D+2H-B0-F.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- q>=0; live means value>q after the row; D includes sigma_a=q, L uses strict q<sigma_a.
- Blockers are positive non-diagonal labels; A excludes 0.

### Argument

1. For a live mortal echo, q<sigma_a<d(a)<d(q). Thus P11 supplies sigma_a in the prefix and its value>q makes it live. Distinct owners have distinct death labels; otherwise the unique victim at that row would be two columns. Whole-history host exclusion gives host<a, including prebirth services.

2. Exactly A(q) columns have died by completed row q: each blocker p<=q has one victim, and a victim cannot die twice since COPY persists. Thus m=q+1-A(q). The union of q old diagonals and q prefix labels has d(q)-1+H elements by positive-MEX coverage and maximality; inclusion-exclusion gives d+I+H=2q+1 and Q=2(I+H)-m-1.

3. The live row partitions into own diagonal, I old diagonals, B blockers, F later-owned diagonals. Diagonal values cannot be frozen; no class overlaps. Hence m=1+I+B+F. Substitute I=L+J+D and B=L+B0 to get Q+2=J+D+2H-B0-F.

4. At q=0, d=1, A=0, Q=-2 and all residual classes empty, so the constant +2 is correct. Nothing estimates the residual difference or proves Q=o(q).

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/q-mortal-echo-injection.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

---

<a id="q-ghost-path-ledger"></a>

## Exact signed ledger of the current ghost paths

**Statement.** Q(q)=X_L+X_D+2H_q−Z−1.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.

### Argument

1. A currently served old diagonal cannot be a frozen blocker, so its physical host is live after the row. Seed exclusion gives host<owner. One emitted value and row/diagonal injectivity give outdegree and indegree at most 1. Strictly increasing indexes exclude cycles.

2. An e-edge path has e+1 live vertices if its terminal is live and e otherwise: every nonterminal is an actual current service host. Its contribution to 2I−m is e−1 in the first case and e in the second. Each isolated live vertex contributes−1.

3. Summing path contributions gives 2I−m=X_L+X_D−Z, including current column q among the isolates. The exact overlap equation d+I+H=2q+1 and live count m=q+1−A(q) imply Q=2I+2H−m−1.

4. Substitution proves Q=X_L+X_D+2H−Z−1. At q=0, Z=1 and Q=−2, so the initial constant is consistent. The proof makes no bound on long paths, dead endpoints or Z.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/q-ghost-path-ledger.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

---

<a id="q-completed-lifetime-energy"></a>

## Completed lifetimes give a weak quadratic negative-energy bound

**Statement.** For M_N=sum_{a=0}^N(a-A(a)), C_N=sum_{p blocker, p<=2N} min(A(p)-1,(min(N, p-1)-s(p))_+), M_N<=sum_{q=0}^{2N}I_q+sum_{a=0}^NH_a+C_N. Consequently limsup C_N/N^2<=23/144, liminf sum_{q<=N}(I_q+H_q)/N^2>=13/576, and limsup sum_{q<=N}(-Q(q))_+/N^2<=179/576.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- Canonical recurrence and positive blocker convention.
- P98 victim bound; A(x)<=floor(x/2); A(x)>=x/3-O(1); 2d(q)>=3q+5 for q>=16.

### Argument

1. Fix a and y=d(a). Older hosts alive after a split into: unique private y service before a; unique service a<t<y; or no service and death a<p<y. A survivor at row y cannot omit y from its journal: no row-y cell may equal the diagonal label y, a live old cell is>y, and positive MEX forces historical y. It cannot be an inherited seed when c<a. Birth/death endpoint equalities are excluded by injectivity and D/S disjointness.

2. Prebirth y source rows have d(t)>y and are distinct for different hosts, so count<=H_a. Postbirth services for a<=N occur at t<d(a)<=2a+1, hence t<=2N, and inject into actual I_t cells.

3. Unserved deaths inject into pairs(p, a) with s(p)<a<p<d(a). One cap is (min(N, p-1)-s(p))_+. The other is A(p)-1: exactly A(p) predeath rows serve p, while s(p) is one such row by FFD and is excluded by a>s(p). Thus the finite inequality keeps completion horizon 2N.

4. Write p_j for blocker rank j. P98 and count bounds give 2j<=p_j<=3j+o(j) and s_j>=j+p_j/6-o(p_j). Maximize min(j,(min(N, p)-j-p/6)_+) over p in[2j,3j]. The cap is j through 5N/12, 5N/6-j through N/2, N-4j/3 through 3N/4, then0. Integrals are25/288,9/288,12/288 times N^2, summing23/144. Uniform o(N) errors over O(N) ranks give o(N^2), with a finite initial segment harmless.

5. A<=q/2 gives M_N>=N(N+1)/4. Enlarge the H sum to 2N, replace N by floor(X/2), and obtain13X^2/576-o(X^2). Put K=I+H. The lower diagonal bound gives K<=q/2-3/2<=m+1 eventually. Therefore(m+1-2K)_+<=m+1-K. Sum and use A>=q/3-o(q): coefficient1/3-13/576=179/576.

6. The quadratic coefficient is not a subquadratic estimate, does not meet a smaller consumer threshold, and does not prove a density improvement. No finite lifetime panel is used as an asymptotic premise.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/q-completed-lifetime-energy.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

---

<a id="q-postdeath-source"></a>

## Every postdeath diagonal service has an earlier same-host blocker source

**Statement.** D-service at (t,h), σ_a≤t<d(a), injects into a private σ_a-service at (u,h) with u<σ_a.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.

### Argument

1. For mortal a put p=σ_a,y=d(a), with a<p<y. A postdeath private y service at(t,h), p≤t<y, has h<a by seed exclusion; its continuing host remains live at row p.

2. At row p the unique p cell is the victim a, strictly right of h. Thus f(p,h)>p: it is recomputed and cannot equal the victim label.

3. Positive MEX then requires p in h’s earlier journal. Because p is a blocker it is not an inherited diagonal seed; its source is a genuine private service(u,h), u<p.

4. Two y services have different hosts by column nonreuse; two extracted p services therefore have different cells. Source uniqueness follows from private nonreuse. The case t=p is allowed. This does not assert the source is a free B0 cell.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/q-postdeath-source.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

---

<a id="q-completed-owner-transport"></a>

## Completed and dated mortal-owner transport retain every endpoint

**Statement.** For every mortal a with p=sigma_a, y=d(a), |D_a|-|R_a|=|C_a|-|X_a|-|W_a|. For actual dated interval stock V(q), D_q-B0_q=C_q-X_q-W_q-[V(q)-V(q-1)].

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- P_a contains private p-service hosts before p, all<a.
- E_a uses a<t<p; D_a uses p<=t<y; X_a is prebirth y on P_a hosts; C_a is E_a off P_a; W_a never privately serves y. W is dated by actual death.

### Argument

1. A D service host h<a survives to p. At row p, p appears uniquely at a to its right and the h cell is>p, so MEX forces an earlier p source at h. Thus D hosts lie in P. A C host must die strictly between its y service and p by the same deadline contradiction; a W host dies after its p source but before y. W deaths need not be after p.

2. Each P host has precisely one y-service type X, E minus C, D or none(W). Thus |P|=|X|+|E|-|C|+|D|+|W|. Each E row has one p service, and distinct E rows consume distinct P services; R excludes exactly them, so |R|=|P|-|E|. Subtract to get the completed identity.

3. For h in P take u_h=p service time and z_h=y service time, or actual death when y never served. Define V_a(q)=sum_h(1[u_h<=q]-1[z_h<=q]), with V_a(-1)=0. A private y before p yields a negative interval and must remain. Differences give R+C-X-D-W because the paired p and E events cancel in the same row.

4. For each fixed q only finitely many owners contribute: any relevant earlier p/y award is<=2q+1; its owner/victim is smaller than its label, and a W death also has an earlier p award. Thus sums may be differentiated rowwise. Summing the owner identity produces the advertised formula with the minus sign on Delta V.

5. The auxiliary waiting bounds retain exact dates: for q>=p-1 stock counts hosts still alive and lacking y; future y services number<=y-q-1 and future missing-y deaths<=A(y-1)-A(q). An immortal h<y-q-1 cannot have served y by reach f(t, h)<=t+h+1 but has served p by its deadline, giving the lower bound Imm(max(0, y-q-1)). Neither bounds the global derivative sublinearly.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/q-completed-owner-transport.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

---

<a id="q-ghost-path-maximal-matching"></a>

## Optimal blocker matching on one ghost path

**Statement.** A ghost path with e edges and k available blocker vertices has maximum matching size min(e,k).

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.

### Argument

1. A path v0→…→ve has e candidate ghost edges, and k available endpoint vertices. Capacity one on edges and vertices bounds every matching by min(e,k).

2. If all e+1 vertices are available, assign each edge to its target, obtaining e matches.

3. Otherwise choose a nonavailable vj. Assign every available vi with i<j to edge i and every available vi with i>j to edge i−1. On either side edge indexes are distinct, and the two sets are disjoint, so all k available vertices are saturated.

4. There are e+1−k nonavailable vertices, hence unmatched edge count max(0,e−k)=max(0,r−1). An available non-source vertex is exactly a surviving mortal echo owner, since q<σ_a<d(a)<d(q) gives its actual blocker service.

5. Owner-only matching already uses every available target. The source gains one additional match precisely when it is available and some target is unavailable. This proves μ=L+T and the stated U,V,Q formulas, without any asymptotic assertion.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/q-ghost-path-maximal-matching.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

---

<a id="q-short-delay-counterexample"></a>

## Counterexample: unit transport delay does not imply pointwise sublinearity

**Statement.** There exists an abstract signed event stream with a capacity-one opposite-sign matching of delay exactly1 and signed crossing inventory O(n), but pointwise imbalance not o(n).

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)
- [Finite MEX insertion, periodic queues and window graph conventions](supplements/FINITE-MEX-AND-WINDOW-MODELS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Abstract dated token stream only, not a canonical Chomp realization.

### Argument

1. For each k>=1 put2k positive tokens at2k and2k negative tokens at2k+1, pairing equal local indices. Every token has one distinct partner one row away.

2. Every completed two-row pair contributes zero to the signed prefix. At cut2k the prefix and crossing stock are2k; at cut2k+1 they are0. Hence stock<=n, also o(n^2).

3. Pointwise imbalance is2k at2k and-2k at2k+1, so its absolute value divided by n tends to 1 on both subsequences. This refutes exactly the claimed inference, without asserting any canonical counterexample.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/q-short-delay-counterexample.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)
- [Full proof and definitions: Finite MEX insertion, periodic queues and window graph conventions](supplements/FINITE-MEX-AND-WINDOW-MODELS.md)

---

<a id="q-inversion-source-links"></a>

## Two exact inversion-source links

**Statement.** H1(a,t) ↔ F(t,a); mortal H2(a,t) ↪ B0(t,σ_a).

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.

### Argument

1. For t<a and d(t)>d(a)=y, y>a>t is nonpast at row t. Coverage and strict row maximum supply one actual interior private y cell. Row injectivity makes its host unique.

2. Conversely each future-diagonal service y=d(a) at row t has a>t and y<d(t), so it determines exactly that inversion. Injective diagonal labels and row indexes make the correspondence bijective.

3. For mortal a, p=σ_a satisfies t<a<p<y<d(t), so coverage also supplies a private p cell at row t. This blocker cannot belong to the L cancellation, because its victim a is not yet an old owner. Hence it is B0.

4. The pair(row t, blocker p) determines the victim a uniquely; distinct mortal inversions thus have distinct target cells. H1 and H2 are distinct copies, not two claims on one positive token. No equality between their different dates is assumed.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/q-inversion-source-links.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

---

<a id="q-source-multigraph"></a>

## A degree-two source multigraph preserves mortal service provenance

**Statement.** The residual dated tokens admit the described recurrence-native opposite-sign multigraph of maximum degree2. Each contracted mortal edge has endpoint-row ratio<4; every H1/F edge has ratio<2. Immortal J/H2 and some other endpoints remain explicit.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- Token multiplicity is retained; two H copies are distinct vertices.
- Virtual E positives and their same-row p negatives are contracted as paired vertices; spliced walks retained as witnesses.

### Argument

1. An inversion t<a, d(t)>d(a) gives the unique future-diagonal cell in rowt by coverage, bijecting H1(a, t) and F(t, a). For mortal a, p=sigma_a satisfies t<a<p<d(a)<d(t), so the same row supplies unique blocker p; since a is unborn it is B0. Equality of target row and death label recovers(t, a), giving H2 injection.

2. For each mortal owner, same-host p/y matching S has degree<=1 on each side by private nonreuse; same-row T joins E to p and H2 to its prebirth source p. Their row ranges exclude a and are disjoint, so T is also a matching. Different owners use different blocker labels.

3. The union has degree<=2 including parallel edges. Contracting an E/p T-pair splices two external endpoints of opposite sign; one external edge leaves an endpoint; no external edges delete the pair/cycle. No degree can increase above2. Same-row opposite signs cancel with zero signed row charge.

4. A p service at u has p<d(u)<=2u+1 and a<p<=2a+1, hence a/2<u<=2a. Remaining H2 dates equal a and D dates satisfy a<=v<=2a. Thus any splice endpoint ratio<4, independent of walk length. For H1/F, d(t)>d(a)>a and integrality/reach give2t>a, hence a/t<2. There is no zero-date endpoint with these inequalities.

5. The construction alone says nothing about how many isolates occur or how many edges cross a cut. In particular D vertices can become isolated after contraction; their original source does not give an automatic surviving edge.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/q-source-multigraph.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

---

<a id="q-complete-rank-ray"></a>

## A complete chronological signed rank ray

**Statement.** Edges u_k—v_k and v_k—u_{k+1}: opposite signs, degree≤2, total intrinsic endpoint defect 1.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.

### Argument

1. The exact source theorem gameFBlockerCountThrough_strict_square states 2N<(A(N)+3)^2, so blocker count cannot be bounded. Each distinct blocker has a distinct mortal owner; therefore mortal owners are infinite.

2. For each mortal a, a<p<y. At its birth row a the p service exists and is B0, since a is not an old owner. This produces infinitely many distinct negative tokens.

3. The col0 rail follows directly by induction from literal MEX: its private awards are1,…,q, so f(q,0)=q+1. At q=y−1 this serves y after its owner’s death p<y, producing a D token. Distinct diagonal owners yield distinct positive tokens.

4. Every date contains finitely many tokens. Chronological order with deterministic tags therefore enumerates each positive and negative token exactly once. Classification is finite: σ_a<d(a)≤2a+1 resolves old mortal status and d(a)>a resolves value ownership.

5. The edges uk—vk and vk—u(k+1) form one alternating ray. Every vertex has degree2 except u1 of degree1, proving complete coverage and intrinsic defect1. The construction supplies no timing/cut bound.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/q-complete-rank-ray.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

---

<a id="q-rank-ray-cut"></a>

## The rank-ray crossing count identifies its exact quantitative gap

**Statement.** For chronological positive tokens u_1, u_2,... and negative tokens v_1, v_2,... with ray edges u_k-v_k and v_k-u_(k+1), cut width equals |p_n-m_n|+|m_n-max(p_n-1,0)|. For canonical residual tokens p_n-m_n=sum_{q<=n}(Q(q)+2).

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- Both token types infinite; finitely many tokens per date; fixed tie-breaking tags.
- In canonical application, infinitely many blockers and rail0 provide infinite negative/positive populations.

### Argument

1. The first edge family crosses exactly when k lies in the symmetric difference of initial segments[1, p_n] and[1, m_n], so contributes|p_n-m_n|. In the second family u_(k+1) is before the cut iff k<=p_n-1, while v_k is iff k<=m_n. Its symmetric difference gives the second term, including p_n=0.

2. At p_n>=1 the second absolute value differs from the first by1 in magnitude; therefore W differs from2|p_n-m_n| by exactly1. O(n) cut width is equivalent to an O(n) signed-prefix estimate for this ray, which remains open.

3. Each mortal owner a yields B0 at birth because sigma_a<d(a), and yields a postdeath D token at y-1 on rail0 because a<sigma_a<y. Distinct owners give distinct death labels and diagonal labels. The established positive blocker count tends to infinity, so both lists are infinite. Source row q tokens can be classified using deaths through 2a+1 and owners below the numeric labels, but decidability is not a quantitative cut estimate.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/q-rank-ray-cut.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

---

<a id="q-ordered-cycle-crossing"></a>

## Ordered dyadic cycle completion controls crossings

**Statement.** W_G(n)≤2W_M(n)+2⌈log₂(2κ)⌉; κ=4 gives +6.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Finite MEX insertion, periodic queues and window graph conventions](supplements/FINITE-MEX-AND-WINDOW-MODELS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- One fixed matching of opposite-sign tokens with positive, locally finite dates, matched endpoint ratio at most κ≥1.
- In each bucket indexed by floor(log₂ minimum endpoint date), matched pairs are ordered by positive endpoint date before cyclic completion.

### Argument

1. Bucket each matched pair by k=floor(log2 minimum date). Endpoint ratioκ places the entire pair in [2^k,2κ2^k), so each bucket is finite.

2. At cut n, x_i=1[P_i≤n] is nonincreasing under the specified positive-date sorting, while z_i=1[M_i≤n]. For a cyclic bucket, triangle inequality gives Σ|x_i−z_(i+1)|≤Σ|x_i−x_(i+1)|+Σ|x_(i+1)−z_(i+1)|.

3. The last sum is the bucket’s original matching crossings. The cyclic x transition count is0 if constant and2 otherwise. Every nonconstant bucket has 2^k≤n and2κ2^k>n.

4. The half-open scale interval n/(2κ)<2^k≤n has at most ceil(log2(2κ)) powers of2. Adding original and added crossings yields W_G≤2W_M+2ceil(log2(2κ)). Singleton buckets add nothing; tied positive dates do not change monotonicity.

5. For κ=4 the correction is6. This bound requires the chosen order; it does not hold by this argument for arbitrary bucket permutations.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/q-ordered-cycle-crossing.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Finite MEX insertion, periodic queues and window graph conventions](supplements/FINITE-MEX-AND-WINDOW-MODELS.md)

---

<a id="q-cycle-endpoint-windows"></a>

## Dyadic completion has bounded singleton endpoint cost in both window directions

**Statement.** For the specified dyadic cycle completion of a fixed kappa-local matching, kappa>=1, N>=4 and L=ceil(sqrt N), in either I=[N, N+L-1] or[N-L+1, N], 2U(I)<=sum_{v in I}(2-deg v)<=2U(I)+2ceil(log2(8kappa)).

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Finite MEX insertion, periodic queues and window graph conventions](supplements/FINITE-MEX-AND-WINDOW-MODELS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Positive integer dates, finite token count per date.
- Buckets defined by floor(log2(minimum pair date)); positive endpoints sorted by date; nonsingletons receive cyclic opposite-sign edges.

### Argument

1. In a nonsingleton bucket each vertex acquires exactly one new edge in addition to its matching edge. Singleton vertices have degree1, unmatched vertices0. Thus the deficit consists exactly of2 per unmatched vertex and1 per singleton endpoint.

2. Every I date lies in[N/2,2N]: the backward lower endpoint uses ceil(sqrt N)<=N/2+1 for N>=4; forward endpoint<=2N. A singleton pair touching I has minimum m in[N/(2kappa),2N]. Its bucket scale obeys N/(4kappa)<2^k<=2N. A half-open log interval of length log2(8kappa) contains at most its ceiling integer scales; at most two singleton endpoints per scale prove both bounds.

3. Supporting crossing lemma: for x_i=1[P_i<=n], z_i=1[M_i<=n], triangle inequality gives sum|x_i-z_(i+1)|<=sum|x_i-x_(i+1)|+sum|x_i-z_i|. Sorted x has0 or2 cyclic changes; varying buckets have n/(2kappa)<2^k<=n. Thus completed W<=2W_matching+2ceil(log2(2kappa)).

4. The optional final consumer needs one fixed matching with U(window)=O(N), W(cut)=O(n), plus bounded upward increments Q(q)-Q(q-1)<=K. Signed edge cancellation then bounds both window sums; backward positive spikes and forward negative spikes yield |Q(N)|=O(sqrt N). None of those canonical suppliers is established by the endpoint theorem.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/q-cycle-endpoint-windows.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Finite MEX insertion, periodic queues and window graph conventions](supplements/FINITE-MEX-AND-WINDOW-MODELS.md)

---

<a id="q-sqrt-block-consumer"></a>

## Dated matching and one-sided variation imply a square-root discrepancy bound

**Statement.** U(I_N±)=O(N), W_M(n)=O(n), Q(q)−Q(q−1)≤K ⇒ |Q(N)|=O(√N).

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Finite MEX insertion, periodic queues and window graph conventions](supplements/FINITE-MEX-AND-WINDOW-MODELS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- One fixed matching on all actual residual tokens, with constant endpoint ratio κ.
- O(N) unmatched counts in both √N window directions.
- O(n) matching crossings at every cut.
- A constant upper bound on Q(q)−Q(q−1). These canonical suppliers remain open.

### Argument

1. The degree≤2 completed graph satisfies 2Σ_inside sign=Σ_inside sign(2−degree)+Σ_boundary sign(inside endpoint). An internal opposite-sign edge cancels; each boundary edge contributes its inside sign.

2. Ordered-cycle crossing control gives O(N) cut counts at either end of a√N-window. UnmatchedO(N) and bounded singleton endpoints give O(N) total intrinsic defect. Therefore |Σ_window(Q+2)|≤CN in both orientations.

3. With Q(q)−Q(q−1)≤K, backward values obey Q(N−j)≥Q(N)−Kj; forward values obey Q(N+j)≤Q(N)+Kj. Replacing K by max(K,0) if needed preserves the premise.

4. Summing L=ceil√N terms in the backward and forward windows gives Q(N)≤CN/L+K(L−1)/2−2 and −Q(N)≤CN/L+K(L−1)/2+2. Hence Q=O(√N).

5. Edges jumping across the full window have no inside endpoint, but counting both boundary cuts only enlarges an upper bound. The initial finite exceptions are absorbed into C. Every canonical matching/endpoint/crossing/increment supplier remains a premise.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/q-sqrt-block-consumer.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Finite MEX insertion, periodic queues and window graph conventions](supplements/FINITE-MEX-AND-WINDOW-MODELS.md)

---

<a id="q-reverse-source-forest"></a>

## A reverse-source forest injects C events into forward or missing hosts

**Statement.** For every mortal owner a there is a source-defined injection C_a to F_a disjoint-union W_a, whose terminal physical host is strictly left of the starting C host. It avoids the p-service at row p-1 and host0. For any integer b<=a, |{C hosts<=b}|+|{reverse hosts<=b}|<=|{P hosts<b}|.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- p=sigma_a, y=d(a), P actual predeath p hosts. Reverse hosts have v_y<u_p; forward hosts have u_p<v_y; W has no y service.

### Argument

1. At a C or reverse y cell, p<y is absent from that host journal: C never books p, reverse books it only later. MEX puts p strictly left in the same row. That source is an actual predeath private p cell because the current row< p.

2. All domain y cells occupy distinct rows; row injectivity forbids two y cells in one row, and private nonreuse forbids duplicating one host service. Distinct target p cells also have distinct hosts by p nonreuse. Thus the first-source map from C union reverse hosts toP is injective and strictly decreases host.

3. Each reverse P vertex has one outgoing edge, and every P vertex indegree<=1. C starts are outside P. Finite strictly decreasing host chains cannot cycle or merge from distinct C starts; they terminate at P outside reverse, hence forward or W. A continuation through a reverse target also strictly decreases y source time since its y precedes its current p service.

4. C starts satisfy t<sigma_h<p, hence t<=p-2. Later steps only decrease source time, so terminal p service is before p-1; rail0 serves p exactly at p-1 and is excluded. The host-prefix inequality follows by restricting the first-source injection, not by assuming terminal F is compensation.

5. A forward terminal can be a D service after owner death. Therefore this injection does not prove C maps to X/W, A1, or |C|<=|X|+|W|.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/q-reverse-source-forest.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

---

<a id="q-last-source-exclusion"></a>

## The reverse forest cannot terminate at the final blocker source

**Statement.** Every reverse-forest terminal has blocker source date ≤p−2; host 0 is not a terminal.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.

### Argument

1. A C event has a<t<σ_h<p, so its y row is at most p−2. At that recomputed y cell the smaller blocker p must occur in the strict left prefix because it is absent from the C host’s journal.

2. At a reverse host the unique y service precedes the unique p service. Traversing to its same-row left p source strictly reduces the physical host, and the next reverse y row is strictly earlier than the preceding p row.

3. Distinct y source rows give distinct same-row p cells; private p nonreuse then gives distinct p hosts. Thus no two C paths merge, and every finite descending path ends at a forward or W host.

4. Every terminal’s p row remains≤p−2. Col0’s unique private p service is at p−1 by the independently derived rail, so it cannot be a terminal.

5. The host-prefix Hall consequence counts each initial C/B domain host through its distinct strictly lower source. It allows unpaid forward D endpoints and does not prove A1. Unrestricted E-host descent is not used.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/q-last-source-exclusion.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

---

<a id="q-death-swap-gate"></a>

## An exact death-swap identity, including immediate deaths

**Statement.** For every mortal a, with p=sigma_a, P=predeath p-service hosts, V={h<a:sigma_h<=a+1}, S=P intersect V and M={h<a:sigma_h>a+1, h not in P}, A(p)+A(a+1)-a=|S|-|M|+1[p=a+1]. In particular the indicator vanishes when p>a+1.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- A counts positive blocker labels; sigma=infinity for immortal columns.
- The indicator vanishes when p>a+1. This strict inequality is automatic when C_a is nonempty.

### Argument

1. P is inside the a older columns. Blockers t<=a have victims<a. Among blockers<=a+1 the sole possible victim outside that universe is a itself at death a+1, occurring iff p=a+1. Thus |V|=A(a+1)-1[p=a+1].

2. Inside the a-element universe, complement(P union V)=M and intersection(P, V)=S. Inclusion-exclusion gives |P|+|V|=a-|M|+|S|; substitute counts.

3. Exact literal initial witness: rows[1],[2,3],[3,2,4], a1, p2, P{0}, V/S/M empty. Then K=1 while |S|-|M|=0. This refutes the unguarded displayed catalogue identity.

4. The source itself states p>a+1 where needed; the publication summary dropped that quantifier. The repair preserves the original C-case gate without proving its nonnegative sign. Under X=W empty, early-dead P hostsS empty and a C host lies in M; a nonnegative gate would contradict C, but that gate remains open.

### Review and supporting evidence

- Historical original-claim verdict: repaired.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/q-death-swap-gate.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Detailed audit proof or correction](../audit/full/paper-a/DEATH-SWAP-REPAIR.md)
- [Detailed audit proof or correction](../audit/full/paper-b/SECOND-REVIEW-A.json)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

---

<a id="q-proximity-slack-split"></a>

## Gap-three birth exposure reduces to three nonnegative slack pairs

**Statement.** For a mortal missing-p host h in the gap-three setting p=sigma_a=r+3, r=sigma_h and h<a<a+1<r, E=d(h)+A(h)-(2h+1)>=0 and F=2h-r-A(h)>=0 satisfy d(h)-r=1+E+F. If d(h)<p then (E, F) is(0,0),(1,0)or(0,1).

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Source-time capacity and the precisely scoped tight cases](supplements/SOURCE-TIME-AND-TIGHTNESS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- Gap-three p=r+3 is essential; the conclusion is an exhaustive remaining-case split, not exclusion.

### Argument

1. Alive-after-h count is h+1-A(h); each live award>h and<=d(h), so d(h)-h>=h+1-A(h), giving E>=0. FFD and victim propagation supply r on every row h,..., r-1, in distinct surviving old hosts<h; there are h-A(h) of them, so F>=0.

2. Adding definitions cancels A and2h, leaving d(h)-r=1+E+F exactly. FFD gives d(h)>r. Since p blocker cannot equal a diagonal and d(h)<p=r+3, d(h)-r is1or2. Integer nonnegative E, F therefore have sum0or1, yielding exactly three pairs.

3. At E0 all live awards fill their available integer interval; old survivors fill[h+1, d(h)-1]. At F0 the r-host injection saturates the survivor roster. These are equality structures only; neither forces a private p booking or excludes gap four.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/q-proximity-slack-split.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Source-time capacity and the precisely scoped tight cases](supplements/SOURCE-TIME-AND-TIGHTNESS.md)

---

<a id="q-tight-width-eighteen"></a>

## Tight gap-three missing-booker widths at most 18 are excluded at all indices

**Statement.** Under the stated gap-three M context and E=F=0, L=r−h≥19.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Source-time capacity and the precisely scoped tight cases](supplements/SOURCE-TIME-AND-TIGHTNESS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Mortal owner a with p=σ_a; missing-booker host h<a, r=σ_h, a+1<r<p=r+3.
- Tight slacks E=d(h)+A(h)−(2h+1)=0 and F=2h−r−A(h)=0.
- Banked gameF_col31_rail for q≥44 and reviewed exact initial recurrence prefix.

### Argument

1. E=F=0 gives d(h)=r+1 and old survivor roster U of sizer−h filling [h+1,r]. An active old affine rail with offsetg has birth-row outputh+g, so g≤r−h. This uses birth-row saturation before appealing to any future service date.

2. The exact declaration gameF_col31_rail(q), q≥44, gives f(q,31)=q+19. For h≥44, col31 is old and its rail remains live, so every tight width is at least 19.

3. For h7,…,43, independent literal replay gives E(h)>0 with minimum1. The initial h<7 domain in a gap3 M context is excluded by its actual death data: h0,2,5 immortal; h1 death2 and h3 death5 are too early for a+1<r with a>h; h4 death7 would force p10, which is diagonal; h6 death9 would force p12 victim8, contradicting a+1<9.

4. Together no tight gap3 M host of width≤18 exists. Width≥19 is not excluded. No global no-(h+3) row-gap premise, service-order monotonicity or future F0 transfer is used.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/q-tight-width-eighteen.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Reproducible finite certificate data and checker](../certificates/README.md)
- [Exact certificate input hashes](../certificates/INPUT-MANIFEST.json)
- [Finite obligation replay receipt](../certificates/CHECK-RESULTS.json)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Source-time capacity and the precisely scoped tight cases](supplements/SOURCE-TIME-AND-TIGHTNESS.md)

---

<a id="q-terminal-service-capacity"></a>

## Higher cells before the penultimate column inject into earlier service rows

**Statement.** For every q>=3, y=f(q, q-1), the higher earlier cells inject into source rows t<q with d(t)>y, hence #{c<q-1:f(q, c)>y}<=#{t<q:d(t)>y}.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Source-time capacity and the precisely scoped tight cases](supplements/SOURCE-TIME-AND-TIGHTNESS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- q>=3 ensures y>=q+1; actual full journal, not a truncated history.

### Argument

1. A higher current cell is recomputed since its value>y>=q+1. The unique current y is later atq-1, so y is absent from the cell left prefix and MEX forces y in its journal.

2. P10 says y is not a past diagonal; it does not assert that y is a diagonal label. This excludes both inherited seeds and the source column birth diagonal. There is an actual private y award at a strict old column on some earlier row t<q. Row injectivity makes these t distinct between columns; strict row maximality gives d(t)>y.

3. This injection has capacity one and no record/tightness/density assumption. The finite q>=3 guard is retained rather than derived by an unproved penultimate live-floor extension.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/q-terminal-service-capacity.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Source-time capacity and the precisely scoped tight cases](supplements/SOURCE-TIME-AND-TIGHTNESS.md)

---

<a id="q-sharp-penultimate-rank"></a>

## At a row-sharp birth, the penultimate blocker has an exact rank bound

**Statement.** For h≥3, E(h)=0 and r=d(h)−1 imply A(v(h))≥r−h and A(r)−A(v(h))≤H(h).

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Source-time capacity and the precisely scoped tight cases](supplements/SOURCE-TIME-AND-TIGHTNESS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.
- h≥3 is required.

### Argument

1. Row-sharp follows by counting distinct after-row live values>h: d(h)≥2h+1−A(h). Its lower envelope increases by1 or2 at each step. Equality E(h)=0 therefore forces every later diagonal strictly above d(h)=r+1.

2. The h−A(h)=r−h old after-row survivors have distinct values in[h+1,r], so they fill that interval. The penultimate y lies there for h≥3 and is not a prior diagonal by the penultimate core lemma. No future owner has value≤r, so y is a blocker.

3. Each of the r−y higher survivor awards occurs before the last-old y source, forcing y into a distinct older private journal; row injectivity supplies distinct prior service rows with d(t)>y.

4. All diagonal values≤y have owners<h. Hence the available prior source count is h−R(y)=h−y+A(y), giving A(y)≥r−h.

5. Because r is below current diagonal, R(r)=h−H(h); therefore A(r)=r−h+H(h), and A(r)−A(y)≤H(h). To conclude y=r one needs both H(h)=0 and r blocker. The general two rank inequalities do not need r to be a blocker.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/q-sharp-penultimate-rank.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Source-time capacity and the precisely scoped tight cases](supplements/SOURCE-TIME-AND-TIGHTNESS.md)

---

<a id="q-tight-suffix-death-injection"></a>

## Every nonrecord high suffix row needs a distinct later actual death

**Statement.** In the canonical E(h)=F(h)=0 missing-booker context with r=sigma_h, for every integer 0<=u<h, #{t:u<=t<h, d(t)>r}<=A(h)-A(u).

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Source-time capacity and the precisely scoped tight cases](supplements/SOURCE-TIME-AND-TIGHTNESS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- E0 gives d(h)=r+1; F0 requires every older survivor after h to privately book r on[h, r).
- Deaths are counted by their actual blocker rows, including death h and excluding death u.

### Argument

1. Because r is a blocker, P11 supplies it in each prebirth row with d(t)>r, and maximality excludes it on the other rows. Its prebirth service hosts c_t are distinct and strictly old c_t<t, since r cannot be a diagonal.

2. No such host survives after h: F0 makes all survivors book r again on[h, r), contradicting private nonreuse. Each has death b_t<=h; the prebirth service value r>t cannot be a death cell, so t<b_t. Victim uniqueness makes b_t distinct.

3. For t>=u, the target death lies in(u, h], whose blocker count is A(h)-A(u). This proves every suffix inequality and the total bound H<=A(h). It does not show that a strict suffix deficit exists.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/q-tight-suffix-death-injection.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Source-time capacity and the precisely scoped tight cases](supplements/SOURCE-TIME-AND-TIGHTNESS.md)

---

<a id="q-tight-predecessor-dichotomy"></a>

## Tight births have an exact diagonal/blocker predecessor dichotomy

**Statement.** h diagonal ⇒ d(h−1)=r−1, E(h−1)=0; h blocker ⇒ d(h−1)≥r+2, E(h−1)≥2.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Source-time capacity and the precisely scoped tight cases](supplements/SOURCE-TIME-AND-TIGHTNESS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.
- Mortal owner a with death p and a missing-booker host h<a; r=σ_h satisfies a+1<r<p, and h≥3.
- Tight slacks E(h)=d(h)+A(h)−(2h+1)=0 and F(h)=2h−r−A(h)=0. No predecessor F(h−1)=0 or predecessor missing-booker membership is supplied.

### Argument

1. Under E=F=0 and r=σ_h, prebirth r-service rows are exactly t<h with d(t)>r. Their source hosts cannot be in U because F0 requires a new r service from every U host. Nonreuse thus forces their distinct actual deaths into(t,h].

2. This gives for each u<h the suffix injection #{t∈[u,h):d(t)>r}≤A(h)−A(u). It uses actual deaths, not guessed deadlines.

3. If numeric h is diagonal, A(h)=A(h−1), so the u=h−1 bound excludes d(h−1)>r. Row-sharp gives d(h−1)≥r−1, while r is a blocker; equality follows and E(h−1)=0.

4. If numeric h is a blocker, row-sharp gives d(h−1)≥r. It cannot equal blocker r or repeat current diagonal r+1, hence≥r+2. The row h−1 r booker must die after h−1 and by h, so it is the actual victim c=s(h). Thus f(h−1,c)=r and f(h,c)=h.

5. Substituting A(h−1)=A(h)−1 yields E(h−1)=d(h−1)−r≥2. Neither branch proves F(h−1)=0 or predecessor M membership.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/q-tight-predecessor-dichotomy.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Source-time capacity and the precisely scoped tight cases](supplements/SOURCE-TIME-AND-TIGHTNESS.md)

---

<a id="q-tight-fresh-permutations"></a>

## Near-top fresh labels admit only disjoint adjacent swaps

**Statement.** In a record-tight E=F=0 birth h with r=sigma_h and m=T(h-1), the row-h subsequence of labels F=[max(h+1, m+1), r-2], ordered by physical source column, is the increasing list up to disjoint adjacent-value swaps.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Source-time capacity and the precisely scoped tight cases](supplements/SOURCE-TIME-AND-TIGHTNESS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- Record H(h)=0 and gap/tight context; F may be empty or singleton.
- Claim concerns only F, allowing historical/outside-F labels to interleave. The main terminal-capacity argument uses h>=3; h=1,2 are checked separately below.

### Argument

1. E0 implies every future d(j)>d(h): ROW-SHARP gives d(j)>=2j+1-A(j)>=d(h)+(j-h) using A one-Lipschitz. Record and r blocker give T(h)<=r-1. If h blocker, ROW-SHARP at h-1 gives d(h-1)>=r, impossible; thus h diagonal and d(h-1)=r-1, E(h-1)=0.

2. If y=v(h)<r, the r-y higher awards require r-y distinct earlier y sources by terminal capacity. Earlier diagonals lie<=r-1 and are distinct, allowing only r-1-y. Contradiction; v(h)=r. Since no old host dies at h, continuing hosts V=U minus{h-1} have full rosters[h, r-2] before and[h+1, r-1] after.

3. For y in F, every earlier row before h-1 has maximum<=m<y, so the only old journal containing y at h is its unique row h-1 service host k_y. It is not a seed: earlier diagonals<=m, birth diagonals r-1, r+1 are outside F, and future diagonals>r+1. All F labels are therefore blockers.

4. If a higher current award z precedes current y, MEX forces y into that host journal, so that host is k_y. Thus y has at most one larger F predecessor. One host cannot skip two F labels since its only new pre-row h award was one value, so each z has at most one smaller F successor.

5. Inversion graph of the F permutation has degree<=1 at both endpoints. An inversion between values with an intermediate value b would force a second inversion at one endpoint: b lies before the lower endpoint or after the higher endpoint. Therefore every inversion is between numerically adjacent F values and such pairs are disjoint. Empty/singleton intervals satisfy the statement vacuously. No hostwise+1 conclusion follows.

6. Small indices do not use the q>=3 terminal-capacity lemma outside its domain. Column 0 is immortal by the exact rail. The literal first rows give h=1, r=2, d(1)=3 and an empty F interval, so the conclusion is vacuous. For h=2, E=F=0 would force r=3 from d(2)=4 and A(2)=1, contradicting the q=3 penultimate no-death theorem. Thus no omitted small tight case remains.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- Renewed clarification: Repair a garbled English sentence without changing the small-index proof or hypotheses.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/q-tight-fresh-permutations.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Source-time capacity and the precisely scoped tight cases](supplements/SOURCE-TIME-AND-TIGHTNESS.md)

---

<a id="q-dated-owner-bridge"></a>

## One fixed dated owner matching gives an exact interval ledger

**Statement.** Σ_{q∈[l,r]}(Q(q)+2)=U₊([l,r])−U₋([l,r])+X(l−1)−X(r).

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.

### Argument

1. Retain H1/F and mortal H2/R source pairs. Their negative source rows t precede the positive owner row a. Their token types are disjoint and all sources have capacity1.

2. For each mortal owner remove the T paired R tokens. Choose the earliest m=min(|D|,|R|−T) D services and latest m remaining R services. All R dates<p≤all D dates; pairing selected lists preserves capacity and forward time. Unmatched D and R counts are the positive/negative parts of χ=T+|D|−|R|.

3. Partition actual p-booker hosts by their unique y service: prebirth X, living E−C, postdeath D, or never-y W. Thus |P|=X+(E−C)+D+W and R=|P|−E, proving D−R=C−X−W and χ=C+T−X−W.

4. On any finite interval each forward matched edge contributes−1 if its negative date is inside and+1 if its positive date is inside. This equals its crossing indicator at the left cut minus that at the right cut. Local finiteness permits summation; unmatched signs give U+−U−.

5. Therefore Σ(Q+2)=U+−U−+X(l−1)−X(r). The inversion components are Inv+Inv_m; remaining selected D/R crossings add X_DR. Before p the latest R selection minimizes crossings, after p the earliest D selection does; the bijection itself does not change these cut counts. This is not a bound on that minimum.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/q-dated-owner-bridge.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

---

<a id="q-immortal-mass-obstruction"></a>

## Mortal-only matching cannot pay the required short-block endpoint budget

**Statement.** Let I_imm count the J and immortal-H2 residual tokens. Then I_imm([ceil(N/7),2N))>=N^2/98-O(N). Any matching that only adds mortal-owner edges leaves these isolated and cannot have U([q, q+ceil(sqrt q)-1])=O(q) uniformly for all large q.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- Canonical history; Imm(x) counts immortal indices strictly below x.
- The obstruction is specific to mortal-only completion, not to all matchings or Q=o(n).

### Argument

1. P50 derivation: predeath p_j hosts plus earlier frozen hosts cover[0, s_j), giving s_j<=2j-1. A mortal victim s_i never awards above p_i+s_i; if p_i+s_i<p, it is below s(p) by P43 and cannot be a p host. Hence s(p)>=A(p)+#{i:p_i+s_i<p}. Under A>=alpha x-C, p_i<=(i+C)/alpha and s_i<=2i-1; use p_j>=2j to obtain s_j>=((1+4alpha)/(1+2alpha))j-O(1). Counting distinct victim ranks below x yields Imm(x)>=2alpha/(1+4alpha)x-O(1); alpha1/3 gives2/7.

2. For immortal h<a, diagonal deadline y=d(a) forces a unique private y service at h before y. It is not at birth a. If service time t>a, assign actual J cell(t, h); if t<a, assign H2(a, t), which exists by d(t)>y. Row injectivity and diagonal injectivity make ordered pairs(h, a) inject into these tokens. Token date lies[a,2a].

3. Restrict both immortal indices to[b, N), b=ceil(N/7). Their count>=2N/7-b-O(1)>=N/7-O(1). The binomial number of ordered earlier/later pairs is>=N^2/98-O(N), with dates in[b,2N).

4. The annulus is covered by O(sqrt N) consecutive legal forward sqrt-window blocks, allowing final overhang. Uniform U=O(q)=O(N) would total O(N^(3/2)), contradicting quadratic isolated mass. This uses uniformity over all large q, not one favorable sequence of windows.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/q-immortal-mass-obstruction.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

---

<a id="q-immortal-forward-source"></a>

## An immortal host has arbitrarily late private blocker services

**Statement.** Immortal-host positive tokens inject into distinct later same-host blocker-service cells.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.

### Argument

1. There are infinitely many blockers by the exact square certificate. Distinct blocker victims give arbitrarily large victim indexes; hence infinitely many lie to the right of any fixed immortal physical host h.

2. For each such p, host h is live at row p and lies left of its unique victim. Its row-p award is greater than p, so MEX forces a prior private p service at h; p cannot be a diagonal seed.

3. Cell reach f(t,h)≤t+h+1 implies p>N+h+1 cannot be served at any t≤N. Thus private blocker services at h occur arbitrarily late.

4. Enumerate the tagged positive tokens associated with h and recursively choose a service after the preceding chosen date and the current token date. This is an injective, forward, same-host assignment. Different hosts use different service cells.

5. Chosen blockers need not be free B0, and service delays are uncontrolled. Every immortal host h<a also serves d(a) before its numerical deadline, so it cannot be a W endpoint for a blocker owner. This follows by live MEX at d(a), no current diagonal-deadline occurrence and seed exclusion.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/q-immortal-forward-source.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

---

<a id="q-journal-mex-ceiling"></a>

## Positive MEX imposes a literal journal ceiling and diagonal capacity bound

**Statement.** For h<N live at START N, let K count actual private diagonal awards on h<=t<N, including birth, S(t)=t+1-A(d(t)), M=max_{t<N}S(t), T_h=max_{a<h}d(a), u_i increasing diagonal labels, L=h+K+M and Z=max(T_h, u_(L+1)). Then max J_N(h)<=Z and K>=N-A(Z)-Imm(h).

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- N>=1 and 0<=h<N. Column h is live at START N; consequently every private award counted before N is recomputed and no COPY has occurred there.
- Set T_0=0 for the empty seed set. K includes birth and future-owner diagonal awards; M counts every diagonal label in the whole row.

### Argument

1. The pre-N journal consists of h distinct seeds and N-h distinct private awards, disjoint by seed exclusion/nonreuse, total N labels. Its diagonal part has h+K labels.

2. For any private award z, literal positive MEX covers every diagonal label<z using its earlier journal and current left prefix. Their diagonal-label counts are at most h+K and M, so R(z-1)<=L. If z>u_(L+1) there would be L+1 such labels, contradiction. Seeds<=T_h supply the other ceiling.

3. Each eventually mortal a<h has a distinct blocker death sigma_a<d(a)<=T_h<=Z. Whole-history host exclusion forbids it from J_N(h), even when its death lies after N. Thus h-Imm(h) blockers inside[1, Z] are unavailable. Journal blocker count N-h-K<=A(Z)-(h-Imm(h)); rearrange.

4. No efficient recognition of future diagonal/blocker status is claimed. A dead/copied column would violate distinct-journal size and is excluded. Any slope-limit corollary requires the explicit existence premise; neither finite inequality supplies it.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/q-journal-mex-ceiling.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

---

<a id="q-multi-owner-barrier"></a>

## Many earlier diagonal barriers share one current ghost capacity

**Statement.** #{b<q:q≤d(b)<d(q), A(d(q))−A(d(b))>H(b)+2(q−b)−1}≤2q+1−d(q)−H(q).

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.

### Argument

1. For owner b<q, M=d(b), q≤M<d(q), the hosts<h=b having M in their start-q journal are exactly its H(b) prebirth services plus G_b(q) postbirth services. Birth occurs only at b, inherited seed membership at h<b is impossible, and private nonreuse makes all such hosts distinct.

2. If M is absent now, each blocker M<x<d(q) has a genuine recomputed current cell by coverage and x>q. At a host<h=b, MEX forces M into its journal because M is absent from the full current prefix.

3. These lower hosts have capacity H+G; hosts b,…,q−1 add at most q−b. Birth column q is diagonal. Absence therefore implies A(d(q))−A(M)≤H(b)+G_b(q)+q−b.

4. Contraposition forces every violating owner’s distinct diagonal into an actual current ghost cell. Row injectivity bounds their number by I(q)=2q+1−d(q)−H(q).

5. Finally G_b(q)≤q−b−1 gives MB3. The guard M≥q is essential to rule out frozen blocker cells; the theorem does not certify joint history/placement feasibility.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/q-multi-owner-barrier.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

---

<a id="q-count-clock-consumer"></a>

## Signed cumulative balance plus downward blocker-clock regularity implies Q=o(n)

**Statement.** For an injective positive-integer sequence d(n) satisfying n<d(n)<=2n+1, with A complementary count and Q(n)=3n+A(n)-2d(n), signed prefix balance sum_{n<N}Q(n)=o(N^2) and lim_{K->infinity}limsup_N N^-1 sum_{n<=N}(u_n-K)_+=0, u_n=(A(d(n-1))-A(d(n)))_+, imply Q(n)=o(n).

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Count-clock implication and its abstract boundary](supplements/COUNT-CLOCK-AND-ABSTRACT-BOUNDARY.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- d is an injective positive-integer sequence with n<d(n)<=2n+1. A counts the complement of its entire range and is linearly interpolated at real arguments.
- Signed prefix balance SB and downward-count-clock uniform integrability CU are assumptions; neither is proved here for the canonical table.
- Define u_n for n>=1; the CU sum uses 1<=n<=N. No limiting density is assumed.

### Argument

1. Let g=(3n+A(n))/2 and E=A(d(n))-A(g(n)). Since A is increasing1-Lipschitz and1.5<=Delta g<=2, E(n-1)-E(n)<=K+2+(u_n-K)_+. For a positive E spike eta N choose fixed K with tail through 2N<=eta N/4 and fixed window delta N with(K+2)delta<=eta/4. E remains>=eta N/2 forward, hence Q<=-eta N throughout. Negative E spikes persist backward with Q>=eta N. Either contradicts SB because proportional-window sums are differences of o(N^2) prefixes. Thus E=o(n), uniformly in prefix maxima through C N.

2. Complementarity gives M_N=sum_{q<N}(q-A(q))=sum_{i<N}(N-d(i))_+ and sum_{i<N}d(i)=N^2-M_N+Dhead. Algebra yields sum_{n<N}(Q(n)+2)=M_N-2Dhead. There are A(N-1)+1 emitted values>=N, each<=2N-1, so Dhead<=N(A(N)+1). Also M_N>=N(N-1)/2-NA(N). Therefore A(N)>=N/6-5/6-S2(N)/(3N), and SB implies liminf A(N)/N>=1/6.

3. Along any scaling subsequence, one-Lipschitz a_N(x)=A(Nx)/N has a locally uniform limit a by compactness/diagonal extraction; a(x)>=x/6. If it has a nontrivial plateau, its maximal level set[l, r] has0<l<r<infinity. For smallε, the interior label interval contains(r-l-2ε)N+o(N) distinct diagonal labels.

4. Their distinct owners i<rN have uniform E(i)=o(N), forcing g(i)/N in(l-ε, r+ε), since a(l-ε) and a(r+ε) lie strictly below/above the plateau. But g increments>=3/2 permit at most(2/3)(r-l+2ε)N+1 owners. Takingε<(r-l)/20 contradicts cardinality. Thus every scaling limit a is strictly increasing.

5. A Q spike gives separated subsequential limits z=d(N)/N and w=g(N)/N. Clock tracking and local uniform convergence imply a(z)=a(w); strict increase forces z=w, contradicting the spike. No density, monotonicity, absolute-energy or canonical service hypothesis entered this argument.

6. Checked endpoints: d(0)=1 follows from reach; all d-values<=x have owners<x; A(0)=0; forward/backward windows stay nonnegative for delta<1/2. The compactness proof does not assume uniqueness of scaling limits.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/q-count-clock-consumer.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Count-clock implication and its abstract boundary](supplements/COUNT-CLOCK-AND-ABSTRACT-BOUNDARY.md)

---

<a id="q-existing-slope-upper-bound"></a>

## If a diagonal slope exists, it is below 1.868565865679

**Statement.** For the canonical table, if d(n)/n→c, then c≤c_*<1.868565865679, where c_* is the unique root in [9/5,15/8] of 7c⁷−25c⁶+22c⁵+25c⁴−58c³+11c²+27c−9.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Independent completion of the existing-slope upper bound](../audit/full/paper-b/SLOPE-REPAIR.md)
- [Exact algebra checks](../audit/full/paper-b/exact-algebra-checks.json)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.
- Existence of the ordered diagonal slope d(n)/n→c. The proof supplies all service, union-exclusion, rank-area and logarithmic-population inequalities used by this conditional consumer.
- See the full independently reconstructed SLOPE-REPAIR.md; no convergence, Q=o(n), or count-uniform-integrability conclusion is asserted.

### Argument

1. Existence d(n)/n→c and reach give c≤2, R(x)=x/c+o(x), A(x)=(1−1/c)x+o(x), and uniform errors on bounded multiples. P98 is rederived by excluding victims dying before the first p-service row from its j distinct bookers; P99 adds reach-forbidden victims with p_i+s_i<p_j. Both exclusion classes lie below s_j and are disjoint from bookers.

2. With v_j=s_j/j, L=1+1/c, r_j=j/c+o(j) and m_i=i(1+bv_i)+o(i), the full union yields s_j≥j+r_j+#{i>r_j:m_i<j}. Weighted summation over j gives liminf(logJ)^−1Σ(v_i−L−φ(v_i))/i≥0. The sufficient j interval is (1+bv_i+ξ)i<j<i/(1/c+ξ); omitted proportional tails and integer boundaries have Oξ(1) weight.

3. For φ=[1/(1+bv)−1/c]+, H(v)=1/v+k(v−L−φ) is convex on[L,c] and[c,2]. Chord coefficient k equalizes outer endpoint values; the kink is smaller by(2−c)(k−1/(2c))≥0. Thus reciprocal-victim mean≤C, and actual victim census gives log-average Imm(h)/h≥V=1−C. V−1/(c+1)>0 because c²−c−1>0; V<1/2 because2c²−1>0.

4. MEX diagonal-rank counting bounds each live journal ceiling, giving cK_h≥B N−(c−1)h−Imm(h), while direct journal exclusions give K_h≥N/c−b h−Imm(h). Integrating the maximum at a fixed immortal host has exact coefficient Ψ=B²/[c(c−1+u)]+bz²/u. The line crossing is N=u h/z and is after birth/positivity thresholds. Summing hosts and Stieltjes integration gives the concave integrand g=uΨ, with bounded endpoint primitive.

5. The chord of g on[u0,1/2] at meanV yields U10. Independent polynomial expansion gives[-9,27,11,−58,25,22,−25,7]. Exact Bernstein positivity of its derivative on[9/5,15/8] and a90-step rational bracket prove the unique root c_*<1.868565865679.

6. The source’s vague prior upper-endpoint exclusion is replaced by a self-contained repair: the rank-integrated two-line MEX inequality M8 has positive surplus159327/60696000 at15/8. Its derivative is positive throughout[15/8,2), using |(1/(cD))′|<15/64 and positive derivative of(c−1)^3(c²−3)^2/(c³D). At c=2, a positive fraction of immortal hosts demandsΩ(N²) diagonal cells while row capacity is o(N²). Thus no c≥15/8 occurs; c<9/5 trivially satisfies the final bound.

### Review and supporting evidence

- Historical original-claim verdict: repaired.
- The complete repaired paper argument was independently reconstructed and second-reviewed. No matching Lean certificate for this derived bound was identified.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/q-existing-slope-upper-bound.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Detailed audit proof or correction](../audit/full/paper-b/SLOPE-REPAIR.md)
- [Detailed audit proof or correction](../audit/full/paper-b/exact-algebra-checks.json)
- [Detailed audit proof or correction](../audit/full/paper-a/SLOPE-SECOND-REVIEW.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Independent completion of the existing-slope upper bound](../audit/full/paper-b/SLOPE-REPAIR.md)
- [Full proof and definitions: Exact algebra checks](../audit/full/paper-b/exact-algebra-checks.json)

---

<a id="q-unconditional-liminf-gap"></a>

## A strict unconditional improvement below the earlier liminf endpoint

**Statement.** For the canonical table, let b_dagger be the unique root in[.467,.469] of3b^4-34b^3-70b^2+27b+6 and a_*=b_dagger-10^-50. Then liminf A(n)/n<=a_* and liminf d(n)/n<=1/(1-a_*). No convergence or limsup statement is asserted.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Independent reconstruction of the strict liminf gap](../audit/full/paper-a/STRICT-LIMINF-DERIVATION.md)
- [Second review of the strict unconditional liminf gap](../audit/full/INDEPENDENT-ASYMPTOTIC-CROSSCHECK.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- The full positive-MEX/COPY journal, FFD and victim propagation are supplied by the shared foundation.
- The P108 budget, retained chronological slack, local missing-rank coercivity and local MEX gap are reconstructed in the linked full audit; they are not additional unproved hypotheses.
- The conclusion concerns liminf only. The microscopic margin 10^-50 is explicit and is not a practical numerical approximation.

### Argument

1. Independently rebuilt the P108 budget: weighted row census, Abel identity, sorted diagonal rank bound u_i<=2i-1, concave tangent of2-1/(1-z), retained chronological prefix slack; victim envelope/Hall swap; two-anchor rational certificate; immortal mean and deficit budgets; chord lower bound; disjoint column service integration. Every error is O_{a, C}(1), not an unproved o(N). Detailed derivation is in the adjacent document.

2. Set P_m=sum_{i<=m}[A(d(i-1))-A(u_i)]>=0. Abel gives weighted slack=P_N/N^2+J_N, J_N=2 integral_1^N P_floor(t)/t^3dt. Retaining this term strengthens budget to kappa_a Ecal_a+J<=D(a)logX+O(1), with kappa>.1336 and D(a)=aP(a)/[(1-a)(3a+1)(6a^2+9a+2)].

3. Every missing numerical rank r<=m is replaced by an emitted rank>m, giving P_m>=sum_missing[A(u_(m+1))-A(u_r)]. On a near-linear counting profile, anη fraction of ε-low chronological rows has rank delay>=δN. Each missing label persists over at leastδN/5 prefix indices, contributing at least aδN/4 each. Weighted energy per bad row>=aδ²/(10N), so J_local>=aηδ²/100. Lower bound d(i-1)>=i already places labels aboveηN/2; the stronger1.5reach quoted in source is unnecessary.

4. Local MEX contradiction independently reconstructed: local density gives Imm(h)>=h/3-δN. Discard at mostρN bad award rows; positive MEX forces remaining awards<=u_(h+K+T+1). This quantile exceeds2h, so all earlier-death forbidden labels are counted. Combining new and old service lines gives S_N>=F(c)N²-eN²-4N. Rational identity F(c)-(2-c)/2>1/2560 on[1.877,1.878] contradicts good-row capacity wheneverε+7δ+2ρ+5/N<1/2560.

5. Use ε=ρ=10^-5,ν=δ_count=10^-15, M=10^16, w0=10^-35. If W_a(N)<w0, any E_a>=νN/2 on[N/M,4N] creates a triangle of integral>=ν²/400>w0; small initial x and C/N handle the remainder. If≥ρN low rows, discard only firstρN/4; remaining>ηN withη=ε_prime=5e-6 force J_local>=g>10^-31, hence W>=g/2>w0. Therefore every large scale has W>=w0.

6. Fubini gives logarithmic mean W<=16logM D(a). Mean-value/rational bounds give D(a_*)<=100*10^-50=10^-48 and16logM<800, so upper mean<8e-46<w0/2. Contradiction rules out any global A>=a_*x-C. If liminfA/n>a_* such C would exist. For ell=liminf d/n, injectivity and eventual d(n)>=(ell-ε)n imply R(x)<=x/(ell-ε)+O(1), yielding ell<=1/(1-a_*).

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/q-unconditional-liminf-gap.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Detailed audit proof or correction](../audit/full/paper-a/STRICT-LIMINF-DERIVATION.md)
- [Detailed audit proof or correction](../audit/full/INDEPENDENT-ASYMPTOTIC-CROSSCHECK.md)
- [Detailed audit proof or correction](../audit/full/paper-b/SECOND-REVIEW-A.json)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Independent reconstruction of the strict liminf gap](../audit/full/paper-a/STRICT-LIMINF-DERIVATION.md)
- [Full proof and definitions: Second review of the strict unconditional liminf gap](../audit/full/INDEPENDENT-ASYMPTOTIC-CROSSCHECK.md)
- [Fresh exact algebra replay](../audit/prepublication/root/strict-gap-algebra.json)
- [Exact algebra checker (Sympy 1.14.0)](../audit/prepublication/root/replay_strict_gap_algebra.py)
- [Historical exact algebra receipt](../audit/full/paper-a/independent-checks.json)

---

<a id="q-signed-balance-abstract-boundary"></a>

## Abstract counterexample: signed balance does not force pointwise sublinearity

**Statement.** In the abstract injective-sequence domain, n<d(n)≤2n+1, signed prefix balance Σ_{q≤N}Q(q)=O(N), and the eventual MB3 and ROW-SHARP count inequalities do not imply Q(n)=o(n). The canonical Q=o(n) claim is not refuted.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Count-clock implication and its abstract boundary](supplements/COUNT-CLOCK-AND-ABSTRACT-BOUNDARY.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- The explicitly defined abstract sequence and its complementary count A; Q(n)=3n+A(n)−2d(n).
- MB3 and ROW-SHARP are required eventually. No compatible canonical joint column/history placement is asserted.

### Argument

1. The170-period splits80 low and90 high positions. Low outputs2floor(4n/5)+2 are even, high outputs2floor(9n/10)+3 are odd. Adjacent floor repetition pairs are never assigned twice to the same phase. d(0)=1 is unique, so the complete sequence is injective and n<d(n)≤2n+1.

2. Translated low/high images have counts80/272 and90/306, giving R(x)=10x/17+O(1) and A(x)=7x/17+O(1). Earlier-owner inversions are H=q/17+O(1) on low rows and O(1) on high rows.

3. Q low=(18/85)n+O(1), Q high=−(16/85)n+O(1). The weighted coefficients sum80*18−90*16=0 in each period; complete and partial period sums are O(N), while each phase has a nonzero Q/n limit.

4. At high rows MB3 forces only(16/1853)q+O(1) owners versus capacityq/5+O(1). At low rows both forcing expressions have a strict negative linear margin, with capacity29q/85+O(1). Therefore MB3 holds eventually. ROW-SHARP also has a positive q/85 margin on low rows.

5. Every n≡1 mod10 follows low→high and every n≡2 mod10 follows high→low, giving a clock increment/decrement(7/85)n+O(1). Each fixed clipped tail has quadratic mass at least 7N²/1700−O_K(N). Thus SB and eventual cardinality barriers do not imply pointwise sublinearity or clock uniform integrability. No canonical journal realization is constructed.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- The abstract counterexample was independently checked arithmetically. It is a refutation of the stated abstract implication, not of the canonical sublinearity target; no matching Lean certificate was identified.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/q-signed-balance-abstract-boundary.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Count-clock implication and its abstract boundary](supplements/COUNT-CLOCK-AND-ABSTRACT-BOUNDARY.md)

---

<a id="eta-envelope"></a>

## A record-drop envelope bounds the ordering error

**Statement.** For injective positive integer d with n<d(n)<=2n+1, M_n=max_{r<n}d(r), and nonnegative nondecreasing integer b satisfying d(n)>=M_n-b(n), F_n=#{r>n:d(r)<d(n)}<=b(2n+1), B_n=#{r<n:d(r)>d(n)}<=b(n), and|F_n-B_n|<=b(2n+1).

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Count-clock implication and its abstract boundary](supplements/COUNT-CLOCK-AND-ABSTRACT-BOUNDARY.md)
- [Ordering error, Pell windows and conditional discrepancy consumers](supplements/PELL-RECURRENCES.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Use M_0=0; envelope holds for all relevant indices.
- No canonical constant/logarithmic envelope is proved.

### Argument

1. Backward inversion values are distinct integers in(d(n), M_n], at most M_n-d(n)<=b(n); if d(n)>=M_n the set is empty.

2. Forward contributor r obeys r<d(r)<d(n)<=2n+1. Its earlier record M_r>=d(n), so d(r)>=d(n)-b(r)>=d(n)-b(2n+1). Distinct integers in[d(n)-b(2n+1), d(n))number at most b(2n+1).

3. The absolute difference of two nonnegative counts is bounded by their maximum; monotonicity of b compares the backward bound. At n=0 the F/B sets are empty and formulas remain valid.

4. Any J-based central-discrepancy consumer additionally requires the exact algebraic I3 identity and a supplied J bound; the envelope theorem supplies neither a canonical b nor J bound.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/eta-envelope.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Count-clock implication and its abstract boundary](supplements/COUNT-CLOCK-AND-ABSTRACT-BOUNDARY.md)
- [Full proof and definitions: Ordering error, Pell windows and conditional discrepancy consumers](supplements/PELL-RECURRENCES.md)

---

<a id="pell-sublinear-two-supplier"></a>

## Two sublinear suppliers suffice for central discrepancy

**Statement.** μ_n≥−h(n), h=o(n), and b_j/q_j→0 ⇒ D_cen(n)=o(n).

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Ordering error, Pell windows and conditional discrepancy consumers](supplements/PELL-RECURRENCES.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- The canonical complementary count and reach identities, with the exact central-discrepancy/counting coupling in the attached proof.
- A nonnegative nondecreasing h=o(n) bounds the record drop μ_n from below.
- Uniform Pell-window discrepancy norms satisfy b_j=o(q_j). These two quantitative canonical suppliers remain open.

### Argument

1. From a nonnegative nondecreasing record-drop envelope h, earlier inversions lie in(d(n),M_n], giving B_n≤h(n). Any later owner contributing d(r)<d(n) has r<d(r)<d(n)≤2n+1 and d(r)≥d(n)−h(2n+1); injectivity gives F_n≤h(2n+1). Hence |η_n|≤h(2n+1)=o(n).

2. Uniform Pell-window bound b_j=o(q_j) gives density by elementary tiling, avoiding an external Ostrowski theorem: fix j, tile[0,N] into q_j intervals, and bound |A(N)−βN|/N≤(b_j+|p_j−βq_j|)/q_j+O(q_j/N). First letN→∞, thenj→∞, using p_j/q_j→β.

3. Rank counting gives η=d(n)−A(d(n))−n−1. Expanding J(n)−(2+√2)J(d(n))−√2(1+η) and using(2+√2)(√2−1)=√2 proves I3 directly.

4. Since n<d(n)≤2n+1, J(d(n))=o(n). All three I3 terms are o(n), so D_cen=o(n). No game supplier is proved.

5. The source’s additional subcritical recurrence corollary has its displayed endpoint rate already corrected: at coefficienta=0 with additiveC>0 the rate is O(j), not O(1). Both rates remain o(q_j).

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/pell-sublinear-two-supplier.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ordering error, Pell windows and conditional discrepancy consumers](supplements/PELL-RECURRENCES.md)

---

<a id="pell-cumulative-transfer"></a>

## Divergent cumulative relative Pell slack gives sublinear scale defects

**Statement.** Let q_-1=0, q_0=1, q_(j+1)=2q_j+q_(j-1), b_j>=0, S_j=2b_j+b_(j-1)-b_(j+1)>=0. If sum_j min(2, S_j/max(1, b_j)) diverges, then b_j/q_j->0. More generally the same conclusion holds if b_(j+1)<=(2-delta_j)b_j+b_(j-1)+C, 0<=delta_j<=2, C>=0and sum delta_j diverges.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Ordering error, Pell windows and conditional discrepancy consumers](supplements/PELL-RECURRENCES.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- The displayed nonnegative Pell defect recurrence holds after a finite initial segment, and any additive constant C is fixed.
- The sum of capped relative slacks diverges. It can be indexed from j=1; changing a finite prefix has no effect.
- In the window application, b_j is the supremum over all starting positions. The required canonical slack supply is not proved here.

### Argument

1. Letρ=1+sqrt2, x_j=b_j/ρ^j, e_j=C/ρ^(j+1), M_j=max(x_j, x_(j-1)). Normalized coefficients sum1-delta_j/ρ. Hence x_(j+1)<=(1-delta_j/ρ)M_j+e_j.

2. At next step discard its nonnegative saving. Substitute previous bound to get x_(j+2)<=(1-2delta_j/ρ²)M_j+(2/ρ)e_j+e_(j+1). Since2/ρ<1, both entries of M_(j+2) obey(1-c delta_j)M_j+g_j with c=min(1/ρ,2/ρ²), g=e_j+e_(j+1). 0<=c delta_j<1 and sum g finite.

3. At least one parity has sum delta infinite. On that parity the product of contraction factors tends0 by log(1-u)<=-u. Every fixed prefix of error contributions vanishes under future products; remaining tail is bounded by sum tail g. Thus M tends0 along that parity; its adjacent entries cover every x_j, so full sequence x->0. Pell q_j is comparable toρ^j.

4. For capped relative slack delta=min(2, S/max(1, b)), delta*b<=S even for b=0or0<b<1, so recurrence holds with C0. No saving is assumed canonical.

5. Optional J(N)=o(N) bridge can be proved without an Ostrowski supplier: tile[0, N] by fixed q_j windows and one remainder. Then limsup_N |J(N)|/N<=(b_j+|p_j-beta q_j|)/q_j; let j grow. This requires exact Pell approximants and bounded unit word increments, explicit in the window application.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/pell-cumulative-transfer.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ordering error, Pell windows and conditional discrepancy consumers](supplements/PELL-RECURRENCES.md)

---

<a id="pell-short-cancel"></a>

## Pell slack splits exactly into magnitude shortfall and signed cancellation

**Statement.** S_j=min_s(Short_j(s)+Cancel_j(s)); at a selected maximizing parent window, S_j=Short_j+Cancel_j.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Ordering error, Pell windows and conditional discrepancy consumers](supplements/PELL-RECURRENCES.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Pell three-child window decomposition and finite-window maximizing starts; Short and Cancel are nonnegative and use the selected parent sign.
- The equality for one selected window requires that it maximizes the parent norm; no positive-slack supplier is assumed.

### Argument

1. For one exact child triple x,y,z, magnitude shortfall is2b_j+b_(j−1)−|x|−|y|−|z|≥0.

2. Writing P as positive mass and M as negative absolute mass gives cancellation P+M−|P−M|=2min(P,M)≥0.

3. Adding gives Short+Cancel=2b_j+b_(j−1)−|W_(j+1)(s)|. Bounded integer window defects attain their maxima, so minimizing over starts gives S_j=2b_j+b_(j−1)−b_(j+1).

4. The identity S=Short+Cancel applies at a parent maximizer (or after taking minimum), not indiscriminately at every start. S=0 requires all child norms saturated and no nonzero opposite-sign child.

5. For δ=min(2,S/max(1,b)), δb≤S even at b=0, so the cumulative-transfer premise follows ifΣδ diverges. Divergence itself is not proved by the identity.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/pell-short-cancel.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ordering error, Pell windows and conditional discrepancy consumers](supplements/PELL-RECURRENCES.md)

---

<a id="pell-multilevel-rigidity"></a>

## Exact multilevel Pell rigidity on every finite frontier

**Statement.** For an exact three-child Pell window recursion with finite globally attained maxima b_j, fixed orientationσ, and a maximizing root at n, the sum of oriented leaf gaps in a complete decomposition to scales k, k-1 equals Lambda_(n, k)=sum_{ell=k}^{n-1}q_(n-ell-1)S_ell. The stated finite frontier/ray corollaries hold with their positive-capacity guards.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Ordering error, Pell windows and conditional discrepancy consumers](supplements/PELL-RECURRENCES.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- n>k>=1; q_-1=0, q_0=1; W_(j+1)(s)=W_j(s)+W_j(s+q_j)+W_(j-1)(s+2q_j).
- b_j=max_s|W_j(s)|; for integer word discrepancies suprema are attained because range at fixed length finite.
- Ray theorem requires b_(k-1),..., b_n>0and D=sum_{ell=k}^{n-1}S_ell/b_ell<1.

### Argument

1. Define Gσ(m, s)=b_m-σW_m(s)>=0. Sum of child capacities is b_m+S_(m-1), while defects sum W_m; hence G(parent)+S=sum G(children). Each frontier expansion adds exactly its S, proving the general finite frontier identity by induction.

2. Complete silver-tree internal-node counts are q_(n-ell-1) at slack scale ell; check base n=k+1:(2leaves k,1leaf k-1,1internal). The 2,1 recursion propagates these and the leaf counts q_(n-k), q_(n-k-1). A maximizing aligned root has G0, proving the formula.

3. Every descendant subtree leaf set is a subset of the fixed root leaf set; nonnegativity gives G(v)+Lambda_(m, k)<=Lambda_(n, k). This is scoped to that tree. G=shortfall+2opposite-sign mass yields both unsigned identities; absolute-value telescope cancels internal defects.

4. Pell product bounds q_a q_c<=q_(a+c+1), proved by induction in the positive 2,1 recursion, yield Lambda<=D*C_(n, k), where the zero-slack capacity C=q_(n-k)b_k+q_(n-k-1)b_(k-1). Thus b_n=C-Lambda>=(1-D)C.

5. Normalized child gaps capacity-average to(g_parent+alpha)/(1+alpha), alpha=S_(m-1)/b_m. Choose a child with minimum ratio. Its1-g is at least(1-g_parent)/(1+alpha). D<1givesb_(ell+1)>b_ell and alpha_ell<=S_ell/b_ell. Products or1-product<=sum give every selected gap<=D and positive aligned defect.

6. For integer b, S with summable capped slack, eventually delta<1. Either b stays0, or once positive it stays positive and increases, and tail relative-slack sums tend0; this yields arbitrarily long finite near-rigid rays. No infinite ray in the original word follows: starts may drift. Counterframe/scalar stress claims are not premises for the identity or finite-ray theorem.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/pell-multilevel-rigidity.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ordering error, Pell windows and conditional discrepancy consumers](supplements/PELL-RECURRENCES.md)

---

<a id="pell-positive-response"></a>

## A masked positive extremizer has a one-way response with sharp buffer

**Statement.** For 0<ω≤1 and C≥1, a positive maximizing Pell parent with a valid masked fibre≤C response has CE+K/2≥ωb_j and S_j=K+2E≥2ωb_j/C. The clipped normalized slack is at least 2ω/C on active scales.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Ordering error, Pell windows and conditional discrepancy consumers](supplements/PELL-RECURRENCES.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- The three-child Pell inventory at a positive parent maximizer; K is its magnitude shortfall and E its actual negative-sign tail mass.
- A predeclared eligible source set of size max(0,ceil(ωb_j−K/2)) and an actual extra-owner-tail response map with fibres at most C. Masking, support and orientation are required.
- Canonical response incidence and divergent active weights remain open suppliers. The argument is a conditional inventory mechanism.

### Argument

1. For a positive parent maximizer, D−E=b_(j+1), D+E+K=2b_j+b_(j−1), so S=K+2E. Also D=(T−K+b_(j+1))/2≥b_j−K/2.

2. Integer D therefore contains the selected m=max(0,ceil(ωb_j−K/2)) sources for 0<ω≤1. A predeclared fibre≤C map into the actual extra-owner tails yields m≤CE, so CE+K/2≥ωb_j.

3. For C≥1, S=K+2E≥2ωb_j/C. If b_(j+1)=0, S=T≥2b_j and the same conclusion holds without a response map.

4. Active b_j>0 are integer, so division by max(1,b_j) is division by b_j. Clipping at2 still leavesδ≥2ω/C. Divergent predeclared active weight therefore supplies the cumulative-transfer hypothesis; the even lane’s transfer plus fixed-window tiling gives J=o(N).

5. For positive integer C and rational 0<ω≤1, choose a sufficiently divisible integer b and put e=ωb/C. The saturated inventory triple (b,b,−e), at capacities (b,b,e), has K=0, integer E=e and selected sample size ωb=CE. A map with exactly C preimages per target attains S=2ωb/C. This proves inventory-level sharpness for compatible integer data; it does not assert canonical-word realizability or exact equality for every real C or irrational ω. The inequality remains valid for real C≥1, whose fibre bound effectively uses floor(C). Scale tagging allows repeated absolute days across scales but still requires actual tail incidence; arbitrary membership or postselected weights cannot replace that premise.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- Renewed clarification: Align the compact proof with the independently reviewed complete supplement: literal sharpness requires compatible integer cardinalities, and a real fibre bound is effectively its floor.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/pell-positive-response.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ordering error, Pell windows and conditional discrepancy consumers](supplements/PELL-RECURRENCES.md)

---

<a id="two-owner-response-content"></a>

## Two-owner MEX response has an exact carrier normal form

**Statement.** For arbitrary finite A, B, S subset N0, u=mex(A union S), v=mex(B union S union{u}). With I=A intersect B and E(x, y)=[x notin A, y not inB]or[x in A minus B, y notin A], sorted outputs x<y satisfy x=mex(S union I), y=min{t>x:t notinS, E(x, t)}. Equality of E is exactly equality of carrier response in all finite contexts.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Finite MEX insertion, periodic queues and window graph conventions](supplements/FINITE-MEX-AND-WINDOW-MODELS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Zero-based MEX; finite journal/context sets; outputs distinct.

### Argument

1. Every label below x is either in S or banned by both owners. If x notin A, first owner takes x; the second takes first later label outside B union S. If x in A, then x notin B and first owner takes first later label outside A union S; second take x. These are exactly the two clauses of E.

2. Finite bans ensure existence of y. The description is also lexicographically first edge outsideS. Therefore equal E implies equal responses.

3. Conversely if E and E prime differ at(x, y), choose S={0,..., y}minus{x, y}. The pair accepting the edge emits exactly{x, y}; the other cannot emit this pair by the already proved normal form. Thus responses differ. E recovers I because x notin I iff E(x, z) for all sufficiently large z, so no additional hidden coordinate is needed.

4. This concerns current carrier response only. It does not claim private journal updates agree or canonical state compression.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/two-owner-response-content.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Finite MEX insertion, periodic queues and window graph conventions](supplements/FINITE-MEX-AND-WINDOW-MODELS.md)

---

<a id="two-owner-phase-reconstruction"></a>

## Response content plus one label and one bit reconstructs the ordered journals

**Statement.** The exact response relation E_AB, r=min(A∖B) (r=∞ when A∖B is empty), and β=1[mex(A)∈B] determine the ordered finite journals (A,B).

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Finite MEX insertion, periodic queues and window graph conventions](supplements/FINITE-MEX-AND-WINDOW-MODELS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Arbitrary ordered finite subsets A,B of ℕ, ordinary mex on ℕ including zero, and the exact response relation E_AB defined by the two-owner protocol.

### Argument

1. The response relation E determines I=A∩B because x∉I iff E(x,z) holds for all sufficiently large z (both finite journals eventually omit z).

2. If r=min(A∖B) is infinite, A=I. Otherwise below r, A membership equals I; r∈A, and for x>r the first clause of E(r,x) is false while the second says x∉A. This reconstructs all A.

3. Put a=mex(A). Below a every label is in A, so B membership equals I membership. At a the missing bit is preciselyβ=1[a∈B]. For x>a, E(a,x) reduces to x∉B because a∉A. This reconstructs all B.

4. The two-owner response normal form itself follows by examining the smallest label allowed by at least one owner outsideS. Whichever owner can take it does so, and the other takes the first admissible larger label. This proves the E relation used above.

5. For alphabet0..M−1 the phase choices give at most 2(M+1) pairs. AtM≥2 the unrestricted-response class has A=empty or one singleton and B=empty or{mexA}, all allowed and distinct, attaining the bound. The label and bit are each independently necessary. No storage compression of the potentially quadratic E table is inferred.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/two-owner-phase-reconstruction.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Finite MEX insertion, periodic queues and window graph conventions](supplements/FINITE-MEX-AND-WINDOW-MODELS.md)

---

<a id="two-owner-commutation"></a>

## Exact commutation criterion for two MEX insertion factors

**Statement.** For finite journals A, B subset N0, maps P_G(S)=S union{mex(G union S)} commute on every finite contextS iff A symmetric_difference B subset{0,..., c-1}, c=mex(A union B).

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Finite MEX insertion, periodic queues and window graph conventions](supplements/FINITE-MEX-AND-WINDOW-MODELS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- All finite contexts; equality of carrier maps, not owner memories.

### Argument

1. Put a=mex(A union S), b=mex(B union S). If a<b, adding a cannot change B mex b because a was already B-banned or in S; adding b cannot change A mex a. Thus both orders yield{a, b}. Symmetric argument handles a>b.

2. If a=b=t, t is outside A union B and hence t>=c. If all disagreements are<c, journals agree above t, while all labels belowt were blocked. After first service t, both second MEX values coincide.

3. If a disagreement u exists at/above c, then u>c since c belongs neither journal. Let S={0,..., u}minus{c, u}. Both first MEX values are c; after c the owner allowing u emits u, the other cannot. The two order response sets differ. This also handles c0 and empty journals without special exceptions.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/two-owner-commutation.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Finite MEX insertion, periodic queues and window graph conventions](supplements/FINITE-MEX-AND-WINDOW-MODELS.md)

---

<a id="periodic-forcing-seed-decision"></a>

## A supplied periodic forcing word gives a finite seed-survival decision horizon

**Statement.** For a supplied p-periodic forcing word, the rescued least core stabilizes at a phase h≤p(ν−1), with capacity ν≤B. Every finite seed dies by h or contains that immortal phase and survives forever. Detecting stabilization takes at most pν queue updates.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Finite MEX insertion, periodic queues and window graph conventions](supplements/FINITE-MEX-AND-WINDOW-MODELS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- A supplied p-periodic upstream word of finite positive sets U_t; B=1+max(∪U_t), with B=1 if the union is empty.
- The exact update is F_t(Q)={v−1:v∈Q,v>0}∪{mex₀(Q∪U_t)−1}; a queue must contain zero to survive.
- This is a queue-update bound. Efficiently supplying the canonical growing cascade word remains open.

### Argument

1. For Q⊆R containing0, mex(Q∪U)≤mex(R∪U). If strict, the smaller mex lies inR because it is not inU. Thus Q∪{mexQ}⊆R∪{mexR}; dropping0 and shifting preserves inclusion. F preserves cardinality; G=F∪{0} never decreases it.

2. The fixed rail0..B−1 contains every rescued iterate, sinceB is absent fromU. StartingK0={0}, the p-step monotone map givesK0⊆Kp⊆K2p⊆…; each strict inclusion increases cardinality.

3. At the first equal-endpoint p-block, no rescue occurred because rescues increase cardinality while ordinary updates preserve it. The block is therefore a genuine immortal periodic phase of capacityν≤B. If j strict blocks preceded it, j≤ν−1 and h=jp≤p(ν−1); detecting it costs(j+1)p≤pν updates.

4. Every actual queue surviving through rowt containsK_t by induction using monotonicity and its arrival0. At timeh it contains the immortal phase and survives forever. Otherwise it dies byh. This includesh=0 and arbitrary finite seed maxima.

5. For every p-periodic immortal phaseS, K0⊆S0 and propagation givesK_h⊆S_h=S0. The stabilized cycle is inclusion-least phase. Truncating initial appointments aboveh cannot affect arrival checks≤h or MEX choices landing≤h, so survival depends only on Q0∩[0,h].

6. ReplacingB by the first positive integer absent from∪U givesν≤1+|∪U|. The theorem counts queue updates rather than unit bit-cost and requires an explicitly supplied period. The optional identification with stable matching flux is a separate dependency, not needed for the headline seed decision.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/periodic-forcing-seed-decision.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Finite MEX insertion, periodic queues and window graph conventions](supplements/FINITE-MEX-AND-WINDOW-MODELS.md)

---

<a id="recovery-no-return"></a>

## No return to a column after a value departs

**Statement.** In a full positive-MEX/COPY triangular history, once value v leaves column c after row s, it never returns there. With row injectivity, a recovery of v at another host at transition q is a fresh-column MEX event with q<=v. If v<=s is present at row s, it persists forever.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Private history, increasing source exits and departure resources](supplements/PRIVATE-HISTORY-AND-RELAY.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Explicit full-history journal V(t, c)={F(r, min(r, c)):r<t}.
- COPY iff old value<t, otherwise positive MEX of V and strict current prefix. Row injectivity needed for host-recovery conclusion.

### Argument

1. Assume a return and choose least t>s+1. COPY would preserve previous value which is not v, while MEX has v in V from row s because c<=s. Both branches contradict a return; induction not needed beyond least finite counterexample.

2. At recovery d!=c, row injectivity makes old hostc unique and current F(q, c)!=v. If d<q, old F(q-1, d)!=v so COPY cannot produce v; newborn q also MEX. Hence v absent from entire V(q, d), proving no earlier award in existing part of column. If v<q then old c would COPY v, contradiction; so q<=v.

3. If v<=s, at next row v<s+1 so COPY preserves it, and induction covers all later rows. No UnitDip, canonical reach, owner-map injectivity, or restriction on movement direction was used.

4. The additional relay/nonmerging R4/R5 claims in the source have stronger absent-root/endpoint guards and are separate catalogue records; none is needed for R1-R3. No finite counterexample log is used as a proof.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/recovery-no-return.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Private history, increasing source exits and departure resources](supplements/PRIVATE-HISTORY-AND-RELAY.md)

---

<a id="cross-clock-departure-injection"></a>

## Cross-clock injection into original departure events

**Statement.** Distinct original roots with certified same-transition absent-root relays inject into their endpoint old payload and original endpoint column, across all clocks in one fixed history. Every arising endpoint payload y satisfies y>=3; its charged-root count is at most the number of relay-eligible departure columns, hence at most y-2. For an arbitrary nonnegative payload y, the bound is max(0,y-2), with no arising endpoints when y<3.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Private history, increasing source exits and departure resources](supplements/PRIVATE-HISTORY-AND-RELAY.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- One fixed full history; distinct original roots with exact absent-root guards and certified rising relay endpoints. Does not prove relay existence or capacity one.
- Every relay starts at a strict old-core host b<q-2, so q>=3; its finite exact leftward path ends at a rising column c<=q-3. Endpoint old payload y>=q>=3. Root absence is in the new retained prefix, and all row/source domains are as defined in the public relay supplement.

### Argument

1. A departing value v cannot return to the same column: choose a first return, COPY would retain a different previous value, while MEX forbids the earlier v already in that column’s full history.

2. At one clock, exact leftward relay maps have indegree/outdegree≤1 by old/new row injectivity. Two paths meeting would imply one root lies on the other path, but the earlier path then emits that root’s old value in the new retained prefix, contradicting root absence. Distinct absent roots therefore have distinct rise endpoints.

3. Charge an original root to(endpoint old value y, endpoint column c). Equal-clock equality contradicts distinct endpoints. If clocksq1<q2 share the same key, the rise atq1 is a departure of y, forbidding y at rowq2−1 by no-return.

4. A rise cannot be COPY, so its old value y>=q. The strict old-core starting host b<q-2 requires q>=3, and a leftward relay ends at 0<=c<=q-3<=y-3. Thus every arising endpoint payload has y>=3, and there are at most y-2 eligible columns for that payload. For arbitrary y>=0 use max(0,y-2); no endpoint with y<3 can arise. This is the restricted departure-resource count, not a bound on all value departures.

5. Different histories require a source identifier in the key. Actual relay existence, exact absence guards and earlier replacement absence are not proved by this accounting. The optional min(y−2,r) refinement needs the separate row-start-owner theorem; it is not part of the headline injection.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- Renewed clarification: With no endpoints, the unguarded expression at y=1 could read 0<=-1. Arising endpoints have y>=q>=3; the nonnegative totalized bound retains exactly the proved resource count.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/cross-clock-departure-injection.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Private history, increasing source exits and departure resources](supplements/PRIVATE-HISTORY-AND-RELAY.md)

---

<a id="component-signed-overlap"></a>

## Component-local signed overlap identity

**Statement.** For old/new injective rows a, b on the same finite column set U, edges c->d when b_c=a_d form paths/cycles. For path root old label x and exit new label z, overlap with fixed O changes by1_O(z)-1_O(x); cycles contribute0. If every new label is below old D and every positive label below D lies in O union A, then all path exits owned and |B intersect O|-|A intersect O|=|(A minus B)minus O|.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Private history, increasing source exits and departure resources](supplements/PRIVATE-HISTORY-AND-RELAY.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Identical retained domain U={0,..., q-2}, q>=2.
- Drop corollary uses positivity, strict new diagonal maximum<old D and old diagonal MEX cover.

### Argument

1. Injectivity bounds in/outdegrees by1. A root with indegree0 cannot enter a cycle: the first cycle entry would have an external predecessor besides its cycle predecessor. Distinct root paths cannot merge by the same indegree bound. Finite components are paths or cycles.

2. On path c0->...->ck, b_ci=a_c(i+1) for i<k. Internal old/new labels cancel as sets; exactly x=a_c0 is lost and z=b_ck gained. Cycle label sets coincide. This does not require monotonic labels along edges.

3. Every exit belongs B minus A globally: otherwise it would have an outgoing edge. Under drop z<D and positive, old MEX coverage forces z in O. Root labels are exactly A minus B; thus owned roots contribute0 and unowned roots1. Sum components for global formula.

4. The old penultimate p belongs A but is notin the project strict old source; actual LowLoss excludes p and D-1and requires absence/nonpast guards. The identity cannot replace all those guards or bound eligible paths by1.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/component-signed-overlap.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Private history, increasing source exits and departure resources](supplements/PRIVATE-HISTORY-AND-RELAY.md)

---

<a id="private-ancestry-arbitrary-packing"></a>

## Private ancestry packing across any number of fresh hosts

**Statement.** An old-value return x to the right of j fresh hosts has j distinct earlier private source rows, whose distinct diagonals lie in (x,T]. Therefore j≤T−x. Fresh hosts occur in increasing value order but need not be a physical suffix.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Private history, increasing source exits and departure resources](supplements/PRIVATE-HISTORY-AND-RELAY.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical table, P02/P03/P05/P14/P16 and exact journal identity. No K2 or NoTriple assumption.

### Argument

1. At a record row, earlier fresh outputs exceedT≥q. For a later returning valuex≤T, MEX inversion placesx in each earlier fresh host’s journal.

2. It is not an inherited seed: a diagonal owner left of a fresh host is also left of the current return host and seed exclusion forbids that current occurrence. A source at the fresh host’s birth is likewise forbidden by seed exclusion.

3. Thus every one ofj fresh hosts supplies a private source row c<a_c<q with valuex. Its source diagonal is strictly above x by row maximality and injectivity.

4. Two hosts cannot share a source row, or that row would repeatx. Their diagonal values are also distinct, all lying in(x,T], so j≤#{a<q:d(a)>x}≤T−x.

5. Fresh hosts themselves are in increasing value order: a later smaller fresh output would have to be in an earlier journal, contradicting journal ceilingT. This does not make the hosts a physical suffix, and the returning cell need not be live.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/private-ancestry-arbitrary-packing.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Private history, increasing source exits and departure resources](supplements/PRIVATE-HISTORY-AND-RELAY.md)

---

<a id="fresh-host-saturated-handover"></a>

## Saturated private-history handover and a jump of at least 2k

**Statement.** For record rowq>=1 with k=d(q)-T(q)-1>=1, let c*<q be rightmost old fresh host. Then {f(a, c*):c*<a<q}={f(q, r):c*<r<q}, both sets with q-c*-1 distinct labels, each<=T-k. If c*<=q-2, f(q, c*)-f(q-1, c*)>=2k.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Private history, increasing source exits and departure resources](supplements/PRIVATE-HISTORY-AND-RELAY.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- Full canonical journals; fresh means value>T(q).
- C19 age>=17 corollary is separately conditional and not part of unconditional statement.

### Argument

1. Fresh labels T+1,..., d-1 all occur by P11 and cannot belong to old journals. Two fresh hosts in physical order cannot decline: MEX would place the later fresh value in the earlier journal<=T. Thus c* holds T+k and all strict right tail cells are<=T.

2. For any tail valuex and any fresh hostc<r, MEX forces x into that journal. It cannot be a seed d(i), i<c, or own birth d(c), because current column r>c cannot emit any earlier diagonal. Therefore x was privately served at some c<a<q with d(a)>x.

3. Different fresh hosts for fixed x have distinct source rows by row injectivity. Therefore k<=#{a<q:d(a)>x}<=T-x, giving x<=T-k.

4. At fixed c*, the distinct q-c*-1 tail values map into the equally many postbirth rows(c*, q). They cannot share one source row because one cell has one value. Thus bijection onto all rows and all postbirth values distinct; no historical row is omitted. Birth row excluded essentially.

5. If previous postbirth row exists, its value<=T-k while current is T+k, giving jump>=2k. If c*=q-1, history and tail are empty and jump corollary is inapplicable. Nothing bounds positive column jumps or proves NoTriple.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/fresh-host-saturated-handover.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Private history, increasing source exits and departure resources](supplements/PRIVATE-HISTORY-AND-RELAY.md)

---

<a id="minimum-common-private-extra"></a>

## A reversed minimum common source requires smaller private extras

**Statement.** Let x0 be the minimum label in the rightmost fresh host's postbirth history. If an earlier fresh host has not received x0 before its rightmost-host source row a*, it receives a distinct smaller private extra y with a*<y<x0 at that row. Several late hosts require distinct extras.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Private history, increasing source exits and departure resources](supplements/PRIVATE-HISTORY-AND-RELAY.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY table, record row, nonempty saturated right-tail history. Does not rule out extras.

### Argument

1. The rightmost fresh host’s postbirth historyH equals its current right tail: packing injects each distinct tail value into an equally sized set of private source rows, so the injection is bijective. Every earlier fresh host’s historyH_i containsH and has |H_i\H|=c_*−c_i.

2. Letx0=minH and let a* be its unique source row atc*. It has no inherited seed at an earlier fresh host, since its current tail occurrence is right of all those hosts; seed exclusion forbids earlier ownership.

3. For a host that has not previously receivedx0, x0 is absent from its journal at a*. It is also absent from its current left prefix because the row’s unique x0 lies later atc*. MEX therefore returns at mostx0, and row injectivity makes it strictly smaller.

4. That host remains live throughq, so its source output exceedsa* (equality would freeze it). The source row a*>c*>c_i is postbirth, hence its output belongs toH_i, and minimality ofx0 excludes membership inH.

5. Several late hosts produce distinct smaller extras in the same row. An extra can be legitimate; no contradiction or NoTriple conclusion follows. The signed source permutation has total displacement0; positive displacement needs backward compensation, but this is accounting, not a prohibition.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/minimum-common-private-extra.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Private history, increasing source exits and departure resources](supplements/PRIVATE-HISTORY-AND-RELAY.md)

---

<a id="full-history-exact-exit-count"></a>

## Full-history nonpast roots biject with pending diagonal holes

**Statement.** For currently fresh old column c at rowq, H={f(a, c):c<a<q}, G={d(a):c<a<q}, the actual source map Phi:H->G is bijective and satisfies Phi(h)>h for every h. Nonpast(H)=H minus G; |nonpast(H)|=|G minus H|. Directed Phi paths biject original nonpast roots H minus G with pending diagonal holes G minus H.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Private history, increasing source exits and departure resources](supplements/PRIVATE-HISTORY-AND-RELAY.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- The current value in old column c exceeds the previous diagonal record. H uses the entire strict postbirth private history c<a<q.
- The source map satisfies Phi(h)>h for each input. No order-preserving comparison between different inputs is asserted.

### Argument

1. Current fresh cell cannot be copied, so column has not frozen earlier. All private awards are distinct and outside seeds D_<=c; each original row a has one award. Thus source row map H->(c, q) is bijective, and distinct diagonals yield Phi image G. Since c<a, strict row max gives Phi(h)=d(a)>h.

2. Every past diagonal owner is<=c or in(c, q); the seed part is excluded from H, so exactly H intersect G are past labels. Equal cardinalities give|H minus G|=|G minus H|.

3. For z in G minus H, diagonal injectivity also excludes the seed set, so z is absent from full journal. Since z<=T<current fresh MEX, it must occur before c in rowq. A currently present diagonal label cannot be<=q: values<q are frozen blockers and value q would be a blocker by P07. Thus q<z<=T; distinct exits have unique distinct holders.

4. The finite graph h->Phi(h) has indegree/outdegree<=1 and strictly increases along edges, so acyclic. Roots H minus G and exits G minus H pair exactly along paths. This needs inflationarity only. Max G is outsideH because each h<Phi(h)<=max G, giving a nonempty exit when H nonempty.

5. If visible first-fresh surplus P is defined as actual H-labels held before c, it is disjoint from exits and prefix capacity gives|nonpast H|+|P|<=c. This is conditional on the precise surplus definition and does not assert arbitrary surplus labels are roots.

### Review and supporting evidence

- Historical original-claim verdict: repaired.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/full-history-exact-exit-count.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Private history, increasing source exits and departure resources](supplements/PRIVATE-HISTORY-AND-RELAY.md)

---

<a id="four-private-sources"></a>

## A fourth private source for an old return after three fresh hosts

**Statement.** If q≤T bounds all earlier diagonals, three current fresh hosts precede an old return x≤T, then an increasing private-source path supplies a fourth distinct source for that same x and x+4≤T.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Private history, increasing source exits and departure resources](supplements/PRIVATE-HISTORY-AND-RELAY.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- RecurrenceModel with explicit LowCellRowStart hook, paid for gameF by named adapter; source/current ordering and diagonal ceiling. No K2 or NoTriple conclusion.

### Argument

1. The three fresh-host inversions give private x sources; focus on the rightmost fresh hostc2 and its complete postbirth historyH. Because the host is still live atq, every y∈H has source c2<a<q with a<y<d(a)≤T.

2. Startingx∈H, replace each current labely by the diagonal at its actual source row if that diagonal is still inH. This strictly increases positive integer labels bounded byT; it terminates atz=d(b)≤T outsideH with c2<b<q. Source dates need not increase.

3. The endpoint is not in c2’s seeds (its ownerb>c2) or privateH. At the current fresh c2 cell, positive no-skip therefore places z at an actual hosth<c2. The LowCellRowStart hook plus diagonal/death disjointness excludes z≤q, giving q<z.

4. The current x at r lies right of h and below z. Inversion gives a new private x source at h. Its host differs from all three fresh hosts because its current valuez≤T, whereas theirs exceedT.

5. All four x source rows are distinct by row injectivity, and their four diagonals are distinct and lie in(x,T]. Hence x+4≤T. This is a paper proof requiring the explicit actual LowCellRowStart hook, not a claimed kernel certificate or NoTriple exclusion.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/four-private-sources.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Private history, increasing source exits and departure resources](supplements/PRIVATE-HISTORY-AND-RELAY.md)

---

<a id="legacy-bottom-two-cut-124"></a>

## Two bottom cuts exclude penultimate lags through 124

**Statement.** For everyb>=500, f(b, b-1)>b+124. For0<=k<=124 the actual winning-target sets satisfy W(b+k, b, b-1)=W(b+k, b, b).

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Two bottom cuts exclude every penultimate lag through 124](supplements/lag124-proof.md)
- [Finite certificates and the all-index bridge](supplements/FINITE-CERTIFICATE-INDUCTION.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- Exact canonical completion/game dictionary; legal moves are ordinary three-row Chomp; positive-MEX/COPY floor.
- Verified C300 periodic certificate, prior120closure, and finite context certificate all independently replayed.

### Argument

1. Independent replay in independent-checks.json rebuilt228826cells from literal MEX starting at1. C300 certificate:all 52976base cells,250normalized phase MEX identities, G176, H675, T676. At b>=T, inherited/pre500labels<b and own history older than Grows<b; normalized recent history/prefix is exact. Induction on row then column proves patterns for all b>=500. Frozen columns COPY forever.

2. Complete new replies after t-bottom deletion from P(a=b+k, b, b-m): middle cuts b-j with1<=j<=m+t-1 yield E(k+j, m+t-j; b-j); top cuts b-m-t+h yield faces E(0, h; b-m-t+h); remaining top cuts b+ell,0<=ell<k yield E(ell, m+t; b). All other legal options were already options of the original P and therefore N. This is a derivation from moves, not a graph assumption.

3. Prior120finite closure rebuilt1284states,82217edges and23112base N checks on500..535. All nonrail children stay in the closed set of states; earlier row jump<=36or same-row lag decrease gives well-founded induction. Rails use bottom>host and row>=500.

4. Context graph rebuilt1510states,104995edges,29339base checks on500..538. Every retained step decreases middle or lag; maximum back jump39cannot jump below500from539up. Each ABAB/BABA stop reconstructs age1 root at lag121/122with nonincreasing top/middle coordinates. Empty context age2/3 states for every uncovered lag<=120were rechecked. Therefore actual P in states must descend to an earlier/equal low top penultimate failure, never to an assumed N state with unpaid memory.

5. Choose least penultimate failure B. Base forces B>=539; prior120leaves121or122. Empty context descent excludes all age2/3 lower lag<=120states at B by minimality or strictly smaller top. A121start ABAB forces122at B-1, contradiction. A122start forces Q=(B+121, B, B-2)P. Its two-bottom neighbor Y=(B+122, B, B-3)N has252phase classified possible replies: lags123/124rails, lag0faces, top ell<=120by descent, and ell121attacked by Q. All N contradicts N having a P reply. Rails123/124then finish bound.

6. For the winning-target sets write X=(a, b, b), Y=(a, b, b-1), and f=f(b, b-1), with b<=a<d(b). Middle-cut target lists coincide. Bottom-cut lists differ only by the extra target Y of X. Top cuts below b coincide in both positions, so their outcomes need not be evaluated. The remaining top cuts of X cannot be P because their top is below d(b); those of Y can be P only at top f. When f>a, none of these differing top cuts is P and Y itself is N, proving W(X)=W(Y). When f=a, Y is an extra P target of X. When f<a, (f, b, b-1) is a P target of Y but is not any one-move target of X. The bound a<=b+124<f<d(b) gives exactly the equal-set case. No unbounded-lag or proof-grammar exhaustion claim follows.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/legacy-bottom-two-cut-124.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Reproducible finite certificate data and checker](../certificates/README.md)
- [Exact certificate input hashes](../certificates/INPUT-MANIFEST.json)
- [Finite obligation replay receipt](../certificates/CHECK-RESULTS.json)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Two bottom cuts exclude every penultimate lag through 124](supplements/lag124-proof.md)
- [Full proof and definitions: Finite certificates and the all-index bridge](supplements/FINITE-CERTIFICATE-INDUCTION.md)

---

<a id="legacy-multiple-bottom-cuts"></a>

## A finite multi-cut certificate theorem, with penultimate lag 211 application

**Statement.** Distinct bottom cuts require distinct residual top lags. A Hall deficiency therefore excludes a P-position. A phase-aware finite induction certificate with independent periodic rails yields f(b,b−1)>b+211 for every b≥600.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Finite certificates and the all-index bridge](supplements/FINITE-CERTIFICATE-INDUCTION.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical completion function for actual three-row Chomp and the exact legal-move P/N dictionary.
- The supplied multi_cut_K211_T6 and periodic_prefix_C360 certificates satisfy the independently checked state/cut, backward-support, phase and normalized MEX identities.
- Finite seeds were replayed using the literal canonical recurrence; all-index validity follows from the proved double induction, not from finite horizon extrapolation. No arbitrary-lag theorem is asserted.

### Argument

1. Assuming X=(b+k,b,b−m) isP, every legal bottom-cut Y_t isN and has aP reply. Complete legal move enumeration, after removing replies already reachable fromX, yields typeI E(k+j,m+t−j;b−j), typeII E(0,h;b−m−t+h), and typeIII E(ell,m+t;b), with the stated strictly positive/backward ranges.

2. If all I/II candidates areN and surviving III lags lie inL_t, two cuts cannot reuse a lag: their twoP positions have equal top/middle but different bottom, and the larger-bottom one moves to the smaller. Hence selected cuts inject into the union of residual lags, contradicting a cardinality deficit.

3. A finite state family is proved by outer induction onb and inner induction onk. I/II supports decreaseb by1..J; III supports decreasek in the same row. J consecutive verified base rows prevent any backward edge skipping belowT. Correct shifted phases and cut legality must be checked for each support.

4. The periodic prefix lemma is independently reconstructed: inherited/pre-q0 values are belowT, old pattern awards more thanG rows earlier are below currentb, and only the lastG awards contribute nonnegative normalized offsets. LIVE-FLOOR blocks lower labels, and finite normalized MEX identities close induction inb then incolumn.

5. Independent literal positive-MEX replay through 810 checks76171 periodic base cells,300 normalized MEX identities and505860 W bases. Independent support reading checks8431 unique states, every residual union/deficit and all 1,355,278 support calls (the extra424 are target coverage calls). All targetlags0..211 are covered. Thus f(b,b−1)>b+211 for everyb≥600.

6. For the source’s neighboring-W corollary W is the set ofP targets, not an outcome bit. At b≤a<d(b), second-row targets of X=(a,b,b) andY=(a,b,b−1) agree, and third-row target lists differ only byY. First-rowX has noP target; first-rowY has one iff f(b,b−1)<a. If f>a, both first-row lists are empty andY isN, proving equality. If f=a,Y itself is the extraP target; if f<a, target(f,b,b−1) is reachable fromY and no one-move channel ofX. Thus equality iff f>a.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- The paper induction and computational certificate were independently audited and replayed in finite-certificate-checks.json. No matching Lean proof of the combined lag-211 result was identified.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/legacy-multiple-bottom-cuts.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Reproducible finite certificate data and checker](../certificates/README.md)
- [Exact certificate input hashes](../certificates/INPUT-MANIFEST.json)
- [Finite obligation replay receipt](../certificates/CHECK-RESULTS.json)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Finite certificates and the all-index bridge](supplements/FINITE-CERTIFICATE-INDUCTION.md)

---

<a id="legacy-charged-shell-criterion"></a>

## A complete criterion for the specified charged bounded-shell certificate class

**Statement.** In the specified charged bounded-shell class, with all I/II replies covered and typeIII same-shell jumps>J charged, largest cut n has exact residual union D_J=#{ell<k hole:A_ell<n}+#{ell<k hole:A_ell=n, k-ell>J}. A_v+1,..., n cuts are certified by n-A_v>D_J. Any successful cut subset normalizes to an initial interval; a least successful terminal has no far equality charge.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Finite certificates and the all-index bridge](supplements/FINITE-CERTIFICATE-INDUCTION.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Fixed periodic rail mask, positive cap A_v, common zero cap M; positive-lag terminal n<=M; lag zero terminal M+1.
- This is exact for prescribed overcount/coverage class, not a necessary condition for all Chomp proofs.

### Argument

1. At cut u, unresolved III lower lag ell occurs iff A_ell<u, or A_ell=u and k-ell>J. Taking union for u<=n gives exactly the two sets displayed: interior far equality cap u<n is already in first set. Every lower lag can provide at most one P across cuts because same top/middle with different bottoms are mutually reachable. Distinct N cut neighbors require one P each and no one P can be a reply for two different cut bottoms. Thus more cuts than residual lags is contradiction.

2. The largest cut n already contains every lag with cap<n; adding missing interior cuts does not add new union members. I/II coverage at n implies coverage at lower u: the parameter ranges shrink and required child ages u-j/u-d decrease. Hence initial cut intervals lose no generality in this class.

3. As n increases, near contributions switch at cap n-1 and far at cap n, so D(n)-D(n-1)=#near(cap n-1)+#far(cap n)>=0. If success at n includes a far equality charge, increment>=1 and(n-1)-A_v>D(n-1). This automatically requires n-1>A_v, since RHS nonnegative. Support is monotone easier at n-1, contradicting least success.

4. The published claim is the local Hall criterion in the specified finite charged-shell class. Increasing a child cap can only weaken the residual near/far indicators and enlarge the allowed support ranges; this gives the monotonicity used in the local normalization. No greatest-table or complete-search theorem is asserted here. Such a theorem would additionally require a fully defined update operator, finite admissible lag/rank box and paid boundary states. Numeric C460 obstruction/search counts are not inputs to this statement.

5. Uniform shaving by c retains n-c>0, for which(A_ell-c)_+<n-c iff A_ell<n, and equality iff A_ell=n. This justifies normalization with the stated positive cap guard. The recorded numeric C460 obstruction is a separate certificate claim; this catalogue statement is the local criterion, proved without trusting those search counts.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- Renewed clarification: The undefined T(A) and greatest-table pruning narration are unnecessary for the local Hall criterion; remove that ancillary assertion rather than implying an unprovided complete-search theorem.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/legacy-charged-shell-criterion.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Finite certificates and the all-index bridge](supplements/FINITE-CERTIFICATE-INDUCTION.md)

---

<a id="legacy-counting-extremizer-incompatibility"></a>

## Quantitative incompatibility of two counting extremizers

**Statement.** For the canonical table, liminf A(n)/n≤b_new, the unique root in [0.469,0.471] of 12496+112497b−24984b²−524992b³−237524b⁴+249993b⁵+87520b⁶−100006b⁷+25000b⁸=0; consequently liminf d(n)/n≤1/(1−b_new)<1.886593095.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [The finite counting service budget and baseline bound](supplements/counting-service-budget.md)
- [Quantitative incompatibility of the two counting extremizers](supplements/counting-extremizer-proof.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.
- The actual prebooker/victim and completed-diagonal service inventories are independently reconstructed in the audit. Exact coefficient positivity and root isolation were independently checked.
- For each fixed a<liminf A(n)/n, take N→∞ before a approaches that liminf. No convergence or limsup ceiling is asserted.

### Argument

1. The actual booker/victim facts give distinct s_j, s_j≤2j−1 and s_j≥j+#{i:p_i+s_i<p_j}. Under global A≥a x−C, put e_j=j−a p_j+C. The baseline ranks i≤floor((j−e_j)/h) are strictly reach-excluded because a(p_i+s_i)≤h i+C−a<j+C−e_j. Thus δ_j=e_j−2g j+h s_j+h≥0; every additional excluded rank adds h.

2. For selected retired indexesI belowm, summingδ and exact rank gaps gives X=S_N−B_ret=Σ_Iδ+2gΓ+Σ_notI e_j+hm/2−aK≥0, with the last term≥m/2. Missing ranks below b m cost at least K−b m inΓ; no victim order is assumed.

3. For the latest selected rankJ≥K, e_J≥2gJ−hm and e_J−e_j≤(1−a)(J−j). On v=u/m in[.332,.336], the resulting ramp starts after .58m. Its integral givesB_peak, while target e_j in[.56m,.58m] is disjoint from ramp support. Thus Y=S_N−B_peak≥that separate target mass.

4. Good source/target counts use distinct rank omissions and Markov bounds: G_s≥(.01m−2−21X/m)+ and G_t≥(.02m−2−4.1X/m−100Y/m)+. Exact source-time and baseline inequalities show every good source is an extra reach exclusion for every good target. Hence X≥h G_sG_t; the product lower bound and h0=.969*2 imply X+Y≥m²/5000−.06m.

5. The prior finite service budget is independently reconstructed from distinct completed diagonal demands and high journal labels: full lower excess area remains after canceling distinct E(N+r) samples; the exact square identity retains the endpoint E(N−1)^2/(2a). This yields U_N≥m u−aW−u²/2+S_N/a−E_endpoint²/(2a)−O(N).

6. Optimizing over unrestricted real first momentz is a valid lower relaxation. The old quadratic J_a has its vertex in(.332,.336); both outside boundary gaps and the inside incompatibility gain exceed1/25000. Independent polynomial/Fraction/Bernstein checks confirm denominator positivity, vertex, ramp, baseline/source margins, outer/inner gains and the degree8 coefficients.

7. Fixa<β=liminfA/n before choosingC and taking a subsequence toβ. The high-sample range holds with a fixed margin. Only after N→∞ let a↑β, so no uniform-in-C error is needed. The necessary newQ(β)≥0 and exact decreasing/root bracket give β≤b_new. Injectivity transfers a hypothetical larger diagonal liminf into a contradictory larger blocker liminf.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- The full paper derivation and its inherited service budget were independently reconstructed, with exact rational checks in exact-algebra-checks.json. The original source had no referee or Lean verification; this publication adds a mathematical audit, not a Lean certificate.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/legacy-counting-extremizer-incompatibility.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: The finite counting service budget and baseline bound](supplements/counting-service-budget.md)
- [Full proof and definitions: Quantitative incompatibility of the two counting extremizers](supplements/counting-extremizer-proof.md)

---

<a id="silver-block-ghost-identities"></a>

## Exact block ghost laws retain the full older-diagonal history

**Statement.** For canonical rowt>=4, dG4(t)=2-step(t)-(H_t-H_(t-1))-ygh(t)+ygh2p(t); and Q_t=I(t)-pool(t)+b_t-2+2H_t, with precisely the revision2 block/young ghost definitions.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Block ghost identities, composed density and the C50 lineage ledger](supplements/BLOCK-GHOSTS-AND-C50.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- dG4=G4(t)-G4p(t), which is not the other N4session Delta G.
- Pool contains non-past non-diagonal row labels>=t, including death row blocker t when present; frozen labels are<t.

### Argument

1. A column copied at rowt has last recomputation r<t with val>=r but copied at r+1 means val<r+1, hence label r. P07makes r blocker; COPY keeps it forever. Conversely every blocker p<t occupies its unique victim. Thus frozen label count A(t-1), and no diagonal ghost can freeze.

2. Overlap ledger gives I=2t+1-d-H; subtract young ghost count for G4. The previous block on columns<=t-4 equals old block<=t-5 plus age3ghost, with no lost threshold ghost label t-1 because such label would be a blocker. Thus G4p=G4(t-1)+ygh3(t-1). Subtract row ledgers and use ygh(t-1)-ygh3=ygh2p to obtain first formula.

3. Row partition has A(t-1)frozen, I ghosts, pool, own diagonal, total t+1. Hence pool=t-A(t-1)-I. Substitute b_t=A(t)-A(t-1) and I=2t+1-d-H into I-pool+b_t-2+2H to obtain3t+A(t)-2d exactly.

4. Pool also equals A(d(t)-1)-A(t-1)+F_t by P11 and maximality. The definitional changes dG4versus Delta G cannot be dropped, and young indicator identities do not by themselves imply global density/sublinear Q. All finite corroboration outside flat data range is excluded from this proof.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/silver-block-ghost-identities.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Block ghost identities, composed density and the C50 lineage ledger](supplements/BLOCK-GHOSTS-AND-C50.md)

---

<a id="silver-composed-count-density"></a>

## Sublinear composed blocker-count defect is equivalent to silver blocker density

**Statement.** E_AA(N)=A(A(N))+2A(N)−N=o(N) ⇔ A(x)/x→√2−1.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Block ghost identities, composed density and the C50 lineage ledger](supplements/BLOCK-GHOSTS-AND-C50.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.
- Canonical injectivity and reach give an upper count bound; the independently supplied quantitative count floor gives liminf A(x)/x≥1/3.
- The conclusion concerns blocker value-set density. A bridge to the ordered diagonal slope is not part of this entry.

### Argument

1. If A(x)/x→β=√2−1, then A(N)→∞ and A(A(N))=β A(N)+o(N)=β²N+o(N). Sinceβ²+2β−1=0, E_AA=o(N).

2. Conversely E_AA=o(N) and lower boundliminfA(N)/N≥1/3 imply A(N)→∞. Setx_N=A(N)/N; division byA(N) gives x_(A(N))=1/x_N−2+o(1).

3. The compact cluster setC lies in[1/3,1/2], the upper bound following from distinct d(i)≤2i+1. For eachc∈C, subsequence convergence and A(N)→∞ give G(c)=1/c−2∈C.

4. Thus eachc∈C isH(y)=1/(y+2) for somey∈C, so C⊆H(C). On y≥0, H has Lipschitz constant≤1/4. Diameter(C)≤diameter(C)/4 forces a singleton.

5. Its unique value satisfiesc=1/c−2, so c=√2−1. This is blocker value-set density only; ordering discrepancyε remains unpaid. No inference to d(n)/n is made.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/silver-composed-count-density.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Block ghost identities, composed density and the C50 lineage ledger](supplements/BLOCK-GHOSTS-AND-C50.md)

---

<a id="c50-lineage-sandwich-conditional"></a>

## Exact C50 lineage identities and the young-root absence relations

**Statement.** For the canonical table and positive integers m,n, put N=m+n and X=Abs_young(m,N). Then Delta_old=AbsB(m)-Abs_old(m,N)=X-[AbsB(N)-AbsB(m)], and Delta_young=AbsB(n)-X+defA(m,n). The required inclusion Hosted_q subset Pend_q is a proved consequence of the canonical frozen-blocker partition.

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Block ghost identities, composed density and the C50 lineage ledger](supplements/BLOCK-GHOSTS-AND-C50.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- m,n>=1; Pend_q={x<q:d(x)>=q}; orbit roots are 0 and the positive blocker labels. The exact row-overlap ledger is used.
- Hosted_q subset Pend_q is derived, not an unresolved admission. It is distinct from the direct-Q transport assertion also called A1.
- No sublinear flux estimates or slope-existence claim are supplied. Such estimates would be additional hypotheses for an asymptotic C50 consumer.

### Argument

1. Repeated preimages strictly decrease because d(x)>x, so every integer has unique root0or blocker. Forward orbits are strictly increasing and unbounded. For every root r<q exactly one orbit node satisfies x<q<=d(x); hence|Pend_q|=1+A(q-1). Old root class count at N is1+A(m-1), young count A(N-1)-A(m-1).

2. A hosted old-diagonal value<q would be a frozen blocker, impossible. Thus Hosted subset Pend. Above values>d(q)>q also lie in Pend, and hosted/above/absent partition Pend by row max and diag injectivity. So AbsB=1+A(q-1)-(2q+1-d(q))=d(q)-2q+A(q-1). This is a logical reconciliation of A1, not a new empirical premise.

3. Subtract the old root Pend count minus Abs_old from|H_m|=1+A(m-1)-AbsB(m). Analogously subtract|H_n| from young root count minus Abs_young; the remainder is defA=A(N-1)-A(m-1)-A(n-1)-1. Both lineage identities follow.

4. Abs_old+Abs_young=AbsB(N) gives X forms. Adding Delta identities gives-(1+d(N)-d(m)-d(n)). Therefore two lower flux bounds by sublinear b_old, b_young imply the Fekete defect upper bound. No reverse implication or either-sided canonical bound is proved; the source phrase "neither alone implies" is read as no implication supplied here, unless a separate counterexample is provided.

5. Boundary m, n>=1is explicitly added for negative A arguments. Conditions m>=n enter only the C50 uniform-asymptotic consumer, not the finite identities. No assumption that slope exists enters.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-a/c50-lineage-sandwich-conditional.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Block ghost identities, composed density and the C50 lineage ledger](supplements/BLOCK-GHOSTS-AND-C50.md)

---

<a id="c50-absence-flux"></a>

## Exact one-row absence flux for any root class

**Statement.** Abs_C(q+1)−Abs_C(q)=F⁺_C(q)−F⁻_C(q)+E_C(q)−Out_C(q).

### Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Block ghost identities, composed density and the C50 lineage ledger](supplements/BLOCK-GHOSTS-AND-C50.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

### Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.
- A fixed class C of orbit roots and the source’s exact pending/hosted/above/absent and flux definitions.
- Hosted⊆Pending is a proved canonical membership lemma, distinct from open direct-Q transport A1. No asymptotic flux or matching bound is assumed or proved.

### Argument

1. By definition Pend_(q+1)=(Pend_q\{x:d(x)=q})∪{q}, because d(x)>x and integer thresholds change by1.

2. For owners remaining in both pending sets, split change of absence into not-absent→absent (F+) and absent→not-absent (F−). Hosted and above cases are disjoint by diagonal maximum and injectivity.

3. The entrantq contributes E_C exactly when root(q)∈C and d(q) is absent on rowq+1.

4. An exit with d(x)=q is absent at rowq: a diagonal label cannot occur in the prefix at its numerical deadline, and q<d(q). Its class is root(x)=root(q), so its contribution is−Out_C.

5. Summing gives ΔAbs_C=F+−F−+E−Out. The direct inventory identity does not need a separate Hosted⊆Pending premise. That membership follows from the canonical frozen-blocker partition: an old hosted diagonal below q would be a frozen blocker, contradicting diagonal/blocker disjointness. Hence the C50 lineage reconciliation is also supplied. Sublinear flux bounds remain unproved; the distinct direct-Q transport A1 is not supplied by this lemma.

### Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../audit/full/paper-b/c50-absence-flux.json)
- [Shared canonical foundation and exact Lean bridges](../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Block ghost identities, composed density and the C50 lineage ledger](supplements/BLOCK-GHOSTS-AND-C50.md)
