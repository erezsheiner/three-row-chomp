# A record-drop envelope bounds the ordering error

**Statement.** For injective positive integer d with n<d(n)<=2n+1, M_n=max_{r<n}d(r), and nonnegative nondecreasing integer b satisfying d(n)>=M_n-b(n), F_n=#{r>n:d(r)<d(n)}<=b(2n+1), B_n=#{r<n:d(r)>d(n)}<=b(n), and|F_n-B_n|<=b(2n+1).

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Count-clock implication and its abstract boundary](../supplements/COUNT-CLOCK-AND-ABSTRACT-BOUNDARY.md)
- [Ordering error, Pell windows and conditional discrepancy consumers](../supplements/PELL-RECURRENCES.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Use M_0=0; envelope holds for all relevant indices.
- No canonical constant/logarithmic envelope is proved.

## Argument

1. Backward inversion values are distinct integers in(d(n), M_n], at most M_n-d(n)<=b(n); if d(n)>=M_n the set is empty.

2. Forward contributor r obeys r<d(r)<d(n)<=2n+1. Its earlier record M_r>=d(n), so d(r)>=d(n)-b(r)>=d(n)-b(2n+1). Distinct integers in[d(n)-b(2n+1), d(n))number at most b(2n+1).

3. The absolute difference of two nonnegative counts is bounded by their maximum; monotonicity of b compares the backward bound. At n=0 the F/B sets are empty and formulas remain valid.

4. Any J-based central-discrepancy consumer additionally requires the exact algebraic I3 identity and a supplied J bound; the envelope theorem supplies neither a canonical b nor J bound.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/eta-envelope.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Count-clock implication and its abstract boundary](../supplements/COUNT-CLOCK-AND-ABSTRACT-BOUNDARY.md)
- [Full proof and definitions: Ordering error, Pell windows and conditional discrepancy consumers](../supplements/PELL-RECURRENCES.md)
