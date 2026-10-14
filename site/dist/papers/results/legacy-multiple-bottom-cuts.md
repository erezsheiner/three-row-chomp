# A finite multi-cut certificate theorem, with penultimate lag 211 application

**Statement.** Distinct bottom cuts require distinct residual top lags. A Hall deficiency therefore excludes a P-position. A phase-aware finite induction certificate with independent periodic rails yields f(b,b−1)>b+211 for every b≥600.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Finite certificates and the all-index bridge](../supplements/FINITE-CERTIFICATE-INDUCTION.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical completion function for actual three-row Chomp and the exact legal-move P/N dictionary.
- The supplied multi_cut_K211_T6 and periodic_prefix_C360 certificates satisfy the independently checked state/cut, backward-support, phase and normalized MEX identities.
- Finite seeds were replayed using the literal canonical recurrence; all-index validity follows from the proved double induction, not from finite horizon extrapolation. No arbitrary-lag theorem is asserted.

## Argument

1. Assuming X=(b+k,b,b−m) isP, every legal bottom-cut Y_t isN and has aP reply. Complete legal move enumeration, after removing replies already reachable fromX, yields typeI E(k+j,m+t−j;b−j), typeII E(0,h;b−m−t+h), and typeIII E(ell,m+t;b), with the stated strictly positive/backward ranges.

2. If all I/II candidates areN and surviving III lags lie inL_t, two cuts cannot reuse a lag: their twoP positions have equal top/middle but different bottom, and the larger-bottom one moves to the smaller. Hence selected cuts inject into the union of residual lags, contradicting a cardinality deficit.

3. A finite state family is proved by outer induction onb and inner induction onk. I/II supports decreaseb by1..J; III supports decreasek in the same row. J consecutive verified base rows prevent any backward edge skipping belowT. Correct shifted phases and cut legality must be checked for each support.

4. The periodic prefix lemma is independently reconstructed: inherited/pre-q0 values are belowT, old pattern awards more thanG rows earlier are below currentb, and only the lastG awards contribute nonnegative normalized offsets. LIVE-FLOOR blocks lower labels, and finite normalized MEX identities close induction inb then incolumn.

5. Independent literal positive-MEX replay through 810 checks76171 periodic base cells,300 normalized MEX identities and505860 W bases. Independent support reading checks8431 unique states, every residual union/deficit and all 1,355,278 support calls (the extra424 are target coverage calls). All targetlags0..211 are covered. Thus f(b,b−1)>b+211 for everyb≥600.

6. For the source’s neighboring-W corollary W is the set ofP targets, not an outcome bit. At b≤a<d(b), second-row targets of X=(a,b,b) andY=(a,b,b−1) agree, and third-row target lists differ only byY. First-rowX has noP target; first-rowY has one iff f(b,b−1)<a. If f>a, both first-row lists are empty andY isN, proving equality. If f=a,Y itself is the extraP target; if f<a, target(f,b,b−1) is reachable fromY and no one-move channel ofX. Thus equality iff f>a.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- The paper induction and computational certificate were independently audited and replayed in finite-certificate-checks.json. No matching Lean proof of the combined lag-211 result was identified.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/legacy-multiple-bottom-cuts.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Reproducible finite certificate data and checker](../../certificates/README.md)
- [Exact certificate input hashes](../../certificates/INPUT-MANIFEST.json)
- [Finite obligation replay receipt](../../certificates/CHECK-RESULTS.json)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Finite certificates and the all-index bridge](../supplements/FINITE-CERTIFICATE-INDUCTION.md)
