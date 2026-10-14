# An exact death-swap identity, including immediate deaths

**Statement.** For every mortal a, with p=sigma_a, P=predeath p-service hosts, V={h<a:sigma_h<=a+1}, S=P intersect V and M={h<a:sigma_h>a+1, h not in P}, A(p)+A(a+1)-a=|S|-|M|+1[p=a+1]. In particular the indicator vanishes when p>a+1.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- A counts positive blocker labels; sigma=infinity for immortal columns.
- The indicator vanishes when p>a+1. This strict inequality is automatic when C_a is nonempty.

## Argument

1. P is inside the a older columns. Blockers t<=a have victims<a. Among blockers<=a+1 the sole possible victim outside that universe is a itself at death a+1, occurring iff p=a+1. Thus |V|=A(a+1)-1[p=a+1].

2. Inside the a-element universe, complement(P union V)=M and intersection(P, V)=S. Inclusion-exclusion gives |P|+|V|=a-|M|+|S|; substitute counts.

3. Exact literal initial witness: rows[1],[2,3],[3,2,4], a1, p2, P{0}, V/S/M empty. Then K=1 while |S|-|M|=0. This refutes the unguarded displayed catalogue identity.

4. The source itself states p>a+1 where needed; the publication summary dropped that quantifier. The repair preserves the original C-case gate without proving its nonnegative sign. Under X=W empty, early-dead P hostsS empty and a C host lies in M; a nonnegative gate would contradict C, but that gate remains open.

## Review and supporting evidence

- Historical original-claim verdict: repaired.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/q-death-swap-gate.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Detailed audit proof or correction](../../audit/full/paper-a/DEATH-SWAP-REPAIR.md)
- [Detailed audit proof or correction](../../audit/full/paper-b/SECOND-REVIEW-A.json)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)
