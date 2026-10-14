# Two bottom cuts exclude penultimate lags through 124

**Statement.** For everyb>=500, f(b, b-1)>b+124. For0<=k<=124 the actual winning-target sets satisfy W(b+k, b, b-1)=W(b+k, b, b).

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Two bottom cuts exclude every penultimate lag through 124](../supplements/lag124-proof.md)
- [Finite certificates and the all-index bridge](../supplements/FINITE-CERTIFICATE-INDUCTION.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- Exact canonical completion/game dictionary; legal moves are ordinary three-row Chomp; positive-MEX/COPY floor.
- Verified C300 periodic certificate, prior120closure, and finite context certificate all independently replayed.

## Argument

1. Independent replay in independent-checks.json rebuilt228826cells from literal MEX starting at1. C300 certificate:all 52976base cells,250normalized phase MEX identities, G176, H675, T676. At b>=T, inherited/pre500labels<b and own history older than Grows<b; normalized recent history/prefix is exact. Induction on row then column proves patterns for all b>=500. Frozen columns COPY forever.

2. Complete new replies after t-bottom deletion from P(a=b+k, b, b-m): middle cuts b-j with1<=j<=m+t-1 yield E(k+j, m+t-j; b-j); top cuts b-m-t+h yield faces E(0, h; b-m-t+h); remaining top cuts b+ell,0<=ell<k yield E(ell, m+t; b). All other legal options were already options of the original P and therefore N. This is a derivation from moves, not a graph assumption.

3. Prior120finite closure rebuilt1284states,82217edges and23112base N checks on500..535. All nonrail children stay in the closed set of states; earlier row jump<=36or same-row lag decrease gives well-founded induction. Rails use bottom>host and row>=500.

4. Context graph rebuilt1510states,104995edges,29339base checks on500..538. Every retained step decreases middle or lag; maximum back jump39cannot jump below500from539up. Each ABAB/BABA stop reconstructs age1 root at lag121/122with nonincreasing top/middle coordinates. Empty context age2/3 states for every uncovered lag<=120were rechecked. Therefore actual P in states must descend to an earlier/equal low top penultimate failure, never to an assumed N state with unpaid memory.

5. Choose least penultimate failure B. Base forces B>=539; prior120leaves121or122. Empty context descent excludes all age2/3 lower lag<=120states at B by minimality or strictly smaller top. A121start ABAB forces122at B-1, contradiction. A122start forces Q=(B+121, B, B-2)P. Its two-bottom neighbor Y=(B+122, B, B-3)N has252phase classified possible replies: lags123/124rails, lag0faces, top ell<=120by descent, and ell121attacked by Q. All N contradicts N having a P reply. Rails123/124then finish bound.

6. For the winning-target sets write X=(a, b, b), Y=(a, b, b-1), and f=f(b, b-1), with b<=a<d(b). Middle-cut target lists coincide. Bottom-cut lists differ only by the extra target Y of X. Top cuts below b coincide in both positions, so their outcomes need not be evaluated. The remaining top cuts of X cannot be P because their top is below d(b); those of Y can be P only at top f. When f>a, none of these differing top cuts is P and Y itself is N, proving W(X)=W(Y). When f=a, Y is an extra P target of X. When f<a, (f, b, b-1) is a P target of Y but is not any one-move target of X. The bound a<=b+124<f<d(b) gives exactly the equal-set case. No unbounded-lag or proof-grammar exhaustion claim follows.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/legacy-bottom-two-cut-124.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Reproducible finite certificate data and checker](../../certificates/README.md)
- [Exact certificate input hashes](../../certificates/INPUT-MANIFEST.json)
- [Finite obligation replay receipt](../../certificates/CHECK-RESULTS.json)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Two bottom cuts exclude every penultimate lag through 124](../supplements/lag124-proof.md)
- [Full proof and definitions: Finite certificates and the all-index bridge](../supplements/FINITE-CERTIFICATE-INDUCTION.md)
