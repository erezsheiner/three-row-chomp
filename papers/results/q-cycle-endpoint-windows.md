# Dyadic completion has bounded singleton endpoint cost in both window directions

**Statement.** For the specified dyadic cycle completion of a fixed kappa-local matching, kappa>=1, N>=4 and L=ceil(sqrt N), in either I=[N, N+L-1] or[N-L+1, N], 2U(I)<=sum_{v in I}(2-deg v)<=2U(I)+2ceil(log2(8kappa)).

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Finite MEX insertion, periodic queues and window graph conventions](../supplements/FINITE-MEX-AND-WINDOW-MODELS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Positive integer dates, finite token count per date.
- Buckets defined by floor(log2(minimum pair date)); positive endpoints sorted by date; nonsingletons receive cyclic opposite-sign edges.

## Argument

1. In a nonsingleton bucket each vertex acquires exactly one new edge in addition to its matching edge. Singleton vertices have degree1, unmatched vertices0. Thus the deficit consists exactly of2 per unmatched vertex and1 per singleton endpoint.

2. Every I date lies in[N/2,2N]: the backward lower endpoint uses ceil(sqrt N)<=N/2+1 for N>=4; forward endpoint<=2N. A singleton pair touching I has minimum m in[N/(2kappa),2N]. Its bucket scale obeys N/(4kappa)<2^k<=2N. A half-open log interval of length log2(8kappa) contains at most its ceiling integer scales; at most two singleton endpoints per scale prove both bounds.

3. Supporting crossing lemma: for x_i=1[P_i<=n], z_i=1[M_i<=n], triangle inequality gives sum|x_i-z_(i+1)|<=sum|x_i-x_(i+1)|+sum|x_i-z_i|. Sorted x has0 or2 cyclic changes; varying buckets have n/(2kappa)<2^k<=n. Thus completed W<=2W_matching+2ceil(log2(2kappa)).

4. The optional final consumer needs one fixed matching with U(window)=O(N), W(cut)=O(n), plus bounded upward increments Q(q)-Q(q-1)<=K. Signed edge cancellation then bounds both window sums; backward positive spikes and forward negative spikes yield |Q(N)|=O(sqrt N). None of those canonical suppliers is established by the endpoint theorem.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/q-cycle-endpoint-windows.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Finite MEX insertion, periodic queues and window graph conventions](../supplements/FINITE-MEX-AND-WINDOW-MODELS.md)
