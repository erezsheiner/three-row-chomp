# A complete criterion for the specified charged bounded-shell certificate class

**Statement.** In the specified charged bounded-shell class, with all I/II replies covered and typeIII same-shell jumps>J charged, largest cut n has exact residual union D_J=#{ell<k hole:A_ell<n}+#{ell<k hole:A_ell=n, k-ell>J}. A_v+1,..., n cuts are certified by n-A_v>D_J. Any successful cut subset normalizes to an initial interval; a least successful terminal has no far equality charge.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Finite certificates and the all-index bridge](../supplements/FINITE-CERTIFICATE-INDUCTION.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Fixed periodic rail mask, positive cap A_v, common zero cap M; positive-lag terminal n<=M; lag zero terminal M+1.
- This is exact for prescribed overcount/coverage class, not a necessary condition for all Chomp proofs.

## Argument

1. At cut u, unresolved III lower lag ell occurs iff A_ell<u, or A_ell=u and k-ell>J. Taking union for u<=n gives exactly the two sets displayed: interior far equality cap u<n is already in first set. Every lower lag can provide at most one P across cuts because same top/middle with different bottoms are mutually reachable. Distinct N cut neighbors require one P each and no one P can be a reply for two different cut bottoms. Thus more cuts than residual lags is contradiction.

2. The largest cut n already contains every lag with cap<n; adding missing interior cuts does not add new union members. I/II coverage at n implies coverage at lower u: the parameter ranges shrink and required child ages u-j/u-d decrease. Hence initial cut intervals lose no generality in this class.

3. As n increases, near contributions switch at cap n-1 and far at cap n, so D(n)-D(n-1)=#near(cap n-1)+#far(cap n)>=0. If success at n includes a far equality charge, increment>=1 and(n-1)-A_v>D(n-1). This automatically requires n-1>A_v, since RHS nonnegative. Support is monotone easier at n-1, contradicting least success.

4. The published claim is the local Hall criterion in the specified finite charged-shell class. Increasing a child cap can only weaken the residual near/far indicators and enlarge the allowed support ranges; this gives the monotonicity used in the local normalization. No greatest-table or complete-search theorem is asserted here. Such a theorem would additionally require a fully defined update operator, finite admissible lag/rank box and paid boundary states. Numeric C460 obstruction/search counts are not inputs to this statement.

5. Uniform shaving by c retains n-c>0, for which(A_ell-c)_+<n-c iff A_ell<n, and equality iff A_ell=n. This justifies normalization with the stated positive cap guard. The recorded numeric C460 obstruction is a separate certificate claim; this catalogue statement is the local criterion, proved without trusting those search counts.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- Renewed clarification: The undefined T(A) and greatest-table pruning narration are unnecessary for the local Hall criterion; remove that ancillary assertion rather than implying an unprovided complete-search theorem.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/legacy-charged-shell-criterion.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Finite certificates and the all-index bridge](../supplements/FINITE-CERTIFICATE-INDUCTION.md)
