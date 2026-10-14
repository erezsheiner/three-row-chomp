# No return to a column after a value departs

**Statement.** In a full positive-MEX/COPY triangular history, once value v leaves column c after row s, it never returns there. With row injectivity, a recovery of v at another host at transition q is a fresh-column MEX event with q<=v. If v<=s is present at row s, it persists forever.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Private history, increasing source exits and departure resources](../supplements/PRIVATE-HISTORY-AND-RELAY.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Explicit full-history journal V(t, c)={F(r, min(r, c)):r<t}.
- COPY iff old value<t, otherwise positive MEX of V and strict current prefix. Row injectivity needed for host-recovery conclusion.

## Argument

1. Assume a return and choose least t>s+1. COPY would preserve previous value which is not v, while MEX has v in V from row s because c<=s. Both branches contradict a return; induction not needed beyond least finite counterexample.

2. At recovery d!=c, row injectivity makes old hostc unique and current F(q, c)!=v. If d<q, old F(q-1, d)!=v so COPY cannot produce v; newborn q also MEX. Hence v absent from entire V(q, d), proving no earlier award in existing part of column. If v<q then old c would COPY v, contradiction; so q<=v.

3. If v<=s, at next row v<s+1 so COPY preserves it, and induction covers all later rows. No UnitDip, canonical reach, owner-map injectivity, or restriction on movement direction was used.

4. The additional relay/nonmerging R4/R5 claims in the source have stronger absent-root/endpoint guards and are separate catalogue records; none is needed for R1-R3. No finite counterexample log is used as a proof.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/recovery-no-return.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Private history, increasing source exits and departure resources](../supplements/PRIVATE-HISTORY-AND-RELAY.md)
