# Ordered dyadic cycle completion controls crossings

**Statement.** W_G(n)≤2W_M(n)+2⌈log₂(2κ)⌉; κ=4 gives +6.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Finite MEX insertion, periodic queues and window graph conventions](../supplements/FINITE-MEX-AND-WINDOW-MODELS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- One fixed matching of opposite-sign tokens with positive, locally finite dates, matched endpoint ratio at most κ≥1.
- In each bucket indexed by floor(log₂ minimum endpoint date), matched pairs are ordered by positive endpoint date before cyclic completion.

## Argument

1. Bucket each matched pair by k=floor(log2 minimum date). Endpoint ratioκ places the entire pair in [2^k,2κ2^k), so each bucket is finite.

2. At cut n, x_i=1[P_i≤n] is nonincreasing under the specified positive-date sorting, while z_i=1[M_i≤n]. For a cyclic bucket, triangle inequality gives Σ|x_i−z_(i+1)|≤Σ|x_i−x_(i+1)|+Σ|x_(i+1)−z_(i+1)|.

3. The last sum is the bucket’s original matching crossings. The cyclic x transition count is0 if constant and2 otherwise. Every nonconstant bucket has 2^k≤n and2κ2^k>n.

4. The half-open scale interval n/(2κ)<2^k≤n has at most ceil(log2(2κ)) powers of2. Adding original and added crossings yields W_G≤2W_M+2ceil(log2(2κ)). Singleton buckets add nothing; tied positive dates do not change monotonicity.

5. For κ=4 the correction is6. This bound requires the chosen order; it does not hold by this argument for arbitrary bucket permutations.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/q-ordered-cycle-crossing.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Finite MEX insertion, periodic queues and window graph conventions](../supplements/FINITE-MEX-AND-WINDOW-MODELS.md)
