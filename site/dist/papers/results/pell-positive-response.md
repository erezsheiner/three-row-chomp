# A masked positive extremizer has a one-way response with sharp buffer

**Statement.** For 0<ω≤1 and C≥1, a positive maximizing Pell parent with a valid masked fibre≤C response has CE+K/2≥ωb_j and S_j=K+2E≥2ωb_j/C. The clipped normalized slack is at least 2ω/C on active scales.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Ordering error, Pell windows and conditional discrepancy consumers](../supplements/PELL-RECURRENCES.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- The three-child Pell inventory at a positive parent maximizer; K is its magnitude shortfall and E its actual negative-sign tail mass.
- A predeclared eligible source set of size max(0,ceil(ωb_j−K/2)) and an actual extra-owner-tail response map with fibres at most C. Masking, support and orientation are required.
- Canonical response incidence and divergent active weights remain open suppliers. The argument is a conditional inventory mechanism.

## Argument

1. For a positive parent maximizer, D−E=b_(j+1), D+E+K=2b_j+b_(j−1), so S=K+2E. Also D=(T−K+b_(j+1))/2≥b_j−K/2.

2. Integer D therefore contains the selected m=max(0,ceil(ωb_j−K/2)) sources for 0<ω≤1. A predeclared fibre≤C map into the actual extra-owner tails yields m≤CE, so CE+K/2≥ωb_j.

3. For C≥1, S=K+2E≥2ωb_j/C. If b_(j+1)=0, S=T≥2b_j and the same conclusion holds without a response map.

4. Active b_j>0 are integer, so division by max(1,b_j) is division by b_j. Clipping at2 still leavesδ≥2ω/C. Divergent predeclared active weight therefore supplies the cumulative-transfer hypothesis; the even lane’s transfer plus fixed-window tiling gives J=o(N).

5. For positive integer C and rational 0<ω≤1, choose a sufficiently divisible integer b and put e=ωb/C. The saturated inventory triple (b,b,−e), at capacities (b,b,e), has K=0, integer E=e and selected sample size ωb=CE. A map with exactly C preimages per target attains S=2ωb/C. This proves inventory-level sharpness for compatible integer data; it does not assert canonical-word realizability or exact equality for every real C or irrational ω. The inequality remains valid for real C≥1, whose fibre bound effectively uses floor(C). Scale tagging allows repeated absolute days across scales but still requires actual tail incidence; arbitrary membership or postselected weights cannot replace that premise.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- Renewed clarification: Align the compact proof with the independently reviewed complete supplement: literal sharpness requires compatible integer cardinalities, and a real fibre bound is effectively its floor.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/pell-positive-response.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ordering error, Pell windows and conditional discrepancy consumers](../supplements/PELL-RECURRENCES.md)
