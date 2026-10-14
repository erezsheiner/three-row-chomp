# Positive MEX imposes a literal journal ceiling and diagonal capacity bound

**Statement.** For h<N live at START N, let K count actual private diagonal awards on h<=t<N, including birth, S(t)=t+1-A(d(t)), M=max_{t<N}S(t), T_h=max_{a<h}d(a), u_i increasing diagonal labels, L=h+K+M and Z=max(T_h, u_(L+1)). Then max J_N(h)<=Z and K>=N-A(Z)-Imm(h).

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- N>=1 and 0<=h<N. Column h is live at START N; consequently every private award counted before N is recomputed and no COPY has occurred there.
- Set T_0=0 for the empty seed set. K includes birth and future-owner diagonal awards; M counts every diagonal label in the whole row.

## Argument

1. The pre-N journal consists of h distinct seeds and N-h distinct private awards, disjoint by seed exclusion/nonreuse, total N labels. Its diagonal part has h+K labels.

2. For any private award z, literal positive MEX covers every diagonal label<z using its earlier journal and current left prefix. Their diagonal-label counts are at most h+K and M, so R(z-1)<=L. If z>u_(L+1) there would be L+1 such labels, contradiction. Seeds<=T_h supply the other ceiling.

3. Each eventually mortal a<h has a distinct blocker death sigma_a<d(a)<=T_h<=Z. Whole-history host exclusion forbids it from J_N(h), even when its death lies after N. Thus h-Imm(h) blockers inside[1, Z] are unavailable. Journal blocker count N-h-K<=A(Z)-(h-Imm(h)); rearrange.

4. No efficient recognition of future diagonal/blocker status is claimed. A dead/copied column would violate distinct-journal size and is excluded. Any slope-limit corollary requires the explicit existence premise; neither finite inequality supplies it.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/q-journal-mex-ceiling.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)
