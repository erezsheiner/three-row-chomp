# Completed and dated mortal-owner transport retain every endpoint

**Statement.** For every mortal a with p=sigma_a, y=d(a), |D_a|-|R_a|=|C_a|-|X_a|-|W_a|. For actual dated interval stock V(q), D_q-B0_q=C_q-X_q-W_q-[V(q)-V(q-1)].

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- P_a contains private p-service hosts before p, all<a.
- E_a uses a<t<p; D_a uses p<=t<y; X_a is prebirth y on P_a hosts; C_a is E_a off P_a; W_a never privately serves y. W is dated by actual death.

## Argument

1. A D service host h<a survives to p. At row p, p appears uniquely at a to its right and the h cell is>p, so MEX forces an earlier p source at h. Thus D hosts lie in P. A C host must die strictly between its y service and p by the same deadline contradiction; a W host dies after its p source but before y. W deaths need not be after p.

2. Each P host has precisely one y-service type X, E minus C, D or none(W). Thus |P|=|X|+|E|-|C|+|D|+|W|. Each E row has one p service, and distinct E rows consume distinct P services; R excludes exactly them, so |R|=|P|-|E|. Subtract to get the completed identity.

3. For h in P take u_h=p service time and z_h=y service time, or actual death when y never served. Define V_a(q)=sum_h(1[u_h<=q]-1[z_h<=q]), with V_a(-1)=0. A private y before p yields a negative interval and must remain. Differences give R+C-X-D-W because the paired p and E events cancel in the same row.

4. For each fixed q only finitely many owners contribute: any relevant earlier p/y award is<=2q+1; its owner/victim is smaller than its label, and a W death also has an earlier p award. Thus sums may be differentiated rowwise. Summing the owner identity produces the advertised formula with the minus sign on Delta V.

5. The auxiliary waiting bounds retain exact dates: for q>=p-1 stock counts hosts still alive and lacking y; future y services number<=y-q-1 and future missing-y deaths<=A(y-1)-A(q). An immortal h<y-q-1 cannot have served y by reach f(t, h)<=t+h+1 but has served p by its deadline, giving the lower bound Imm(max(0, y-q-1)). Neither bounds the global derivative sublinearly.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/q-completed-owner-transport.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Ghost tokens, owner transport and the exact unpaid endpoints](../supplements/GHOST-TOKENS-AND-OWNER-TRANSPORT.md)
