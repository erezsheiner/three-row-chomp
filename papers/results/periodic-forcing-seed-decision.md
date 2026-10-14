# A supplied periodic forcing word gives a finite seed-survival decision horizon

**Statement.** For a supplied p-periodic forcing word, the rescued least core stabilizes at a phase h≤p(ν−1), with capacity ν≤B. Every finite seed dies by h or contains that immortal phase and survives forever. Detecting stabilization takes at most pν queue updates.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Finite MEX insertion, periodic queues and window graph conventions](../supplements/FINITE-MEX-AND-WINDOW-MODELS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- A supplied p-periodic upstream word of finite positive sets U_t; B=1+max(∪U_t), with B=1 if the union is empty.
- The exact update is F_t(Q)={v−1:v∈Q,v>0}∪{mex₀(Q∪U_t)−1}; a queue must contain zero to survive.
- This is a queue-update bound. Efficiently supplying the canonical growing cascade word remains open.

## Argument

1. For Q⊆R containing0, mex(Q∪U)≤mex(R∪U). If strict, the smaller mex lies inR because it is not inU. Thus Q∪{mexQ}⊆R∪{mexR}; dropping0 and shifting preserves inclusion. F preserves cardinality; G=F∪{0} never decreases it.

2. The fixed rail0..B−1 contains every rescued iterate, sinceB is absent fromU. StartingK0={0}, the p-step monotone map givesK0⊆Kp⊆K2p⊆…; each strict inclusion increases cardinality.

3. At the first equal-endpoint p-block, no rescue occurred because rescues increase cardinality while ordinary updates preserve it. The block is therefore a genuine immortal periodic phase of capacityν≤B. If j strict blocks preceded it, j≤ν−1 and h=jp≤p(ν−1); detecting it costs(j+1)p≤pν updates.

4. Every actual queue surviving through rowt containsK_t by induction using monotonicity and its arrival0. At timeh it contains the immortal phase and survives forever. Otherwise it dies byh. This includesh=0 and arbitrary finite seed maxima.

5. For every p-periodic immortal phaseS, K0⊆S0 and propagation givesK_h⊆S_h=S0. The stabilized cycle is inclusion-least phase. Truncating initial appointments aboveh cannot affect arrival checks≤h or MEX choices landing≤h, so survival depends only on Q0∩[0,h].

6. ReplacingB by the first positive integer absent from∪U givesν≤1+|∪U|. The theorem counts queue updates rather than unit bit-cost and requires an explicitly supplied period. The optional identification with stable matching flux is a separate dependency, not needed for the headline seed decision.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/periodic-forcing-seed-decision.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Finite MEX insertion, periodic queues and window graph conventions](../supplements/FINITE-MEX-AND-WINDOW-MODELS.md)
