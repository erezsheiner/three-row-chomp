# An immortal host has arbitrarily late private blocker services

**Statement.** Immortal-host positive tokens inject into distinct later same-host blocker-service cells.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY table, with d the diagonal map and A the count of positive labels not in its image; token and service inventories use the attached proof definitions.

## Argument

1. There are infinitely many blockers by the exact square certificate. Distinct blocker victims give arbitrarily large victim indexes; hence infinitely many lie to the right of any fixed immortal physical host h.

2. For each such p, host h is live at row p and lies left of its unique victim. Its row-p award is greater than p, so MEX forces a prior private p service at h; p cannot be a diagonal seed.

3. Cell reach f(t,h)≤t+h+1 implies p>N+h+1 cannot be served at any t≤N. Thus private blocker services at h occur arbitrarily late.

4. Enumerate the tagged positive tokens associated with h and recursively choose a service after the preceding chosen date and the current token date. This is an injective, forward, same-host assignment. Different hosts use different service cells.

5. Chosen blockers need not be free B0, and service delays are uncontrolled. Every immortal host h<a also serves d(a) before its numerical deadline, so it cannot be a W endpoint for a blocker owner. This follows by live MEX at d(a), no current diagonal-deadline occurrence and seed exclusion.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/q-immortal-forward-source.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)
