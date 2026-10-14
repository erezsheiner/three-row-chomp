# Near-top fresh labels admit only disjoint adjacent swaps

**Statement.** In a record-tight E=F=0 birth h with r=sigma_h and m=T(h-1), the row-h subsequence of labels F=[max(h+1, m+1), r-2], ordered by physical source column, is the increasing list up to disjoint adjacent-value swaps.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Source-time capacity and the precisely scoped tight cases](../supplements/SOURCE-TIME-AND-TIGHTNESS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- Record H(h)=0 and gap/tight context; F may be empty or singleton.
- Claim concerns only F, allowing historical/outside-F labels to interleave. The main terminal-capacity argument uses h>=3; h=1,2 are checked separately below.

## Argument

1. E0 implies every future d(j)>d(h): ROW-SHARP gives d(j)>=2j+1-A(j)>=d(h)+(j-h) using A one-Lipschitz. Record and r blocker give T(h)<=r-1. If h blocker, ROW-SHARP at h-1 gives d(h-1)>=r, impossible; thus h diagonal and d(h-1)=r-1, E(h-1)=0.

2. If y=v(h)<r, the r-y higher awards require r-y distinct earlier y sources by terminal capacity. Earlier diagonals lie<=r-1 and are distinct, allowing only r-1-y. Contradiction; v(h)=r. Since no old host dies at h, continuing hosts V=U minus{h-1} have full rosters[h, r-2] before and[h+1, r-1] after.

3. For y in F, every earlier row before h-1 has maximum<=m<y, so the only old journal containing y at h is its unique row h-1 service host k_y. It is not a seed: earlier diagonals<=m, birth diagonals r-1, r+1 are outside F, and future diagonals>r+1. All F labels are therefore blockers.

4. If a higher current award z precedes current y, MEX forces y into that host journal, so that host is k_y. Thus y has at most one larger F predecessor. One host cannot skip two F labels since its only new pre-row h award was one value, so each z has at most one smaller F successor.

5. Inversion graph of the F permutation has degree<=1 at both endpoints. An inversion between values with an intermediate value b would force a second inversion at one endpoint: b lies before the lower endpoint or after the higher endpoint. Therefore every inversion is between numerically adjacent F values and such pairs are disjoint. Empty/singleton intervals satisfy the statement vacuously. No hostwise+1 conclusion follows.

6. Small indices do not use the q>=3 terminal-capacity lemma outside its domain. Column 0 is immortal by the exact rail. The literal first rows give h=1, r=2, d(1)=3 and an empty F interval, so the conclusion is vacuous. For h=2, E=F=0 would force r=3 from d(2)=4 and A(2)=1, contradicting the q=3 penultimate no-death theorem. Thus no omitted small tight case remains.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- Renewed clarification: Repair a garbled English sentence without changing the small-index proof or hypotheses.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/q-tight-fresh-permutations.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Source-time capacity and the precisely scoped tight cases](../supplements/SOURCE-TIME-AND-TIGHTNESS.md)
