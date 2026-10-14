# Abstract counterexample: signed balance does not force pointwise sublinearity

**Statement.** In the abstract injective-sequence domain, n<d(n)≤2n+1, signed prefix balance Σ_{q≤N}Q(q)=O(N), and the eventual MB3 and ROW-SHARP count inequalities do not imply Q(n)=o(n). The canonical Q=o(n) claim is not refuted.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Count-clock implication and its abstract boundary](../supplements/COUNT-CLOCK-AND-ABSTRACT-BOUNDARY.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- The explicitly defined abstract sequence and its complementary count A; Q(n)=3n+A(n)−2d(n).
- MB3 and ROW-SHARP are required eventually. No compatible canonical joint column/history placement is asserted.

## Argument

1. The170-period splits80 low and90 high positions. Low outputs2floor(4n/5)+2 are even, high outputs2floor(9n/10)+3 are odd. Adjacent floor repetition pairs are never assigned twice to the same phase. d(0)=1 is unique, so the complete sequence is injective and n<d(n)≤2n+1.

2. Translated low/high images have counts80/272 and90/306, giving R(x)=10x/17+O(1) and A(x)=7x/17+O(1). Earlier-owner inversions are H=q/17+O(1) on low rows and O(1) on high rows.

3. Q low=(18/85)n+O(1), Q high=−(16/85)n+O(1). The weighted coefficients sum80*18−90*16=0 in each period; complete and partial period sums are O(N), while each phase has a nonzero Q/n limit.

4. At high rows MB3 forces only(16/1853)q+O(1) owners versus capacityq/5+O(1). At low rows both forcing expressions have a strict negative linear margin, with capacity29q/85+O(1). Therefore MB3 holds eventually. ROW-SHARP also has a positive q/85 margin on low rows.

5. Every n≡1 mod10 follows low→high and every n≡2 mod10 follows high→low, giving a clock increment/decrement(7/85)n+O(1). Each fixed clipped tail has quadratic mass at least 7N²/1700−O_K(N). Thus SB and eventual cardinality barriers do not imply pointwise sublinearity or clock uniform integrability. No canonical journal realization is constructed.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- The abstract counterexample was independently checked arithmetically. It is a refutation of the stated abstract implication, not of the canonical sublinearity target; no matching Lean certificate was identified.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/q-signed-balance-abstract-boundary.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Count-clock implication and its abstract boundary](../supplements/COUNT-CLOCK-AND-ABSTRACT-BOUNDARY.md)
