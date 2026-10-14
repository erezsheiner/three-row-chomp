# A surviving mortal diagonal echo has a distinct death-blocker partner

**Statement.** At every canonical row q, each old diagonal echo d(a) with mortal owner a and q<sigma_a maps injectively to the row-q service of sigma_a at a host<a. With L, J, D partitioning old echoes and B0=B-L, Q(q)+2=J+D+2H-B0-F.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- q>=0; live means value>q after the row; D includes sigma_a=q, L uses strict q<sigma_a.
- Blockers are positive non-diagonal labels; A excludes 0.

## Argument

1. For a live mortal echo, q<sigma_a<d(a)<d(q). Thus P11 supplies sigma_a in the prefix and its value>q makes it live. Distinct owners have distinct death labels; otherwise the unique victim at that row would be two columns. Whole-history host exclusion gives host<a, including prebirth services.

2. Exactly A(q) columns have died by completed row q: each blocker p<=q has one victim, and a victim cannot die twice since COPY persists. Thus m=q+1-A(q). The union of q old diagonals and q prefix labels has d(q)-1+H elements by positive-MEX coverage and maximality; inclusion-exclusion gives d+I+H=2q+1 and Q=2(I+H)-m-1.

3. The live row partitions into own diagonal, I old diagonals, B blockers, F later-owned diagonals. Diagonal values cannot be frozen; no class overlaps. Hence m=1+I+B+F. Substitute I=L+J+D and B=L+B0 to get Q+2=J+D+2H-B0-F.

4. At q=0, d=1, A=0, Q=-2 and all residual classes empty, so the constant +2 is correct. Nothing estimates the residual difference or proves Q=o(q).

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/q-mortal-echo-injection.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)
