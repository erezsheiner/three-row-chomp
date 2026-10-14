# Counterexample: unit transport delay does not imply pointwise sublinearity

**Statement.** There exists an abstract signed event stream with a capacity-one opposite-sign matching of delay exactly1 and signed crossing inventory O(n), but pointwise imbalance not o(n).

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)
- [Finite MEX insertion, periodic queues and window graph conventions](../supplements/FINITE-MEX-AND-WINDOW-MODELS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Abstract dated token stream only, not a canonical Chomp realization.

## Argument

1. For each k>=1 put2k positive tokens at2k and2k negative tokens at2k+1, pairing equal local indices. Every token has one distinct partner one row away.

2. Every completed two-row pair contributes zero to the signed prefix. At cut2k the prefix and crossing stock are2k; at cut2k+1 they are0. Hence stock<=n, also o(n^2).

3. Pointwise imbalance is2k at2k and-2k at2k+1, so its absolute value divided by n tends to 1 on both subsequences. This refutes exactly the claimed inference, without asserting any canonical counterexample.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/q-short-delay-counterexample.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)
- [Full proof and definitions: Finite MEX insertion, periodic queues and window graph conventions](../supplements/FINITE-MEX-AND-WINDOW-MODELS.md)
