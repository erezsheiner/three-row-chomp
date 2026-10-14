# Exact block ghost laws retain the full older-diagonal history

**Statement.** For canonical rowt>=4, dG4(t)=2-step(t)-(H_t-H_(t-1))-ygh(t)+ygh2p(t); and Q_t=I(t)-pool(t)+b_t-2+2H_t, with precisely the revision2 block/young ghost definitions.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Block ghost identities, composed density and the C50 lineage ledger](../supplements/BLOCK-GHOSTS-AND-C50.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Canonical positive-MEX/COPY three-row Chomp history, with the structural facts proved in the shared canonical foundation review.
- dG4=G4(t)-G4p(t), which is not the other N4session Delta G.
- Pool contains non-past non-diagonal row labels>=t, including death row blocker t when present; frozen labels are<t.

## Argument

1. A column copied at rowt has last recomputation r<t with val>=r but copied at r+1 means val<r+1, hence label r. P07makes r blocker; COPY keeps it forever. Conversely every blocker p<t occupies its unique victim. Thus frozen label count A(t-1), and no diagonal ghost can freeze.

2. Overlap ledger gives I=2t+1-d-H; subtract young ghost count for G4. The previous block on columns<=t-4 equals old block<=t-5 plus age3ghost, with no lost threshold ghost label t-1 because such label would be a blocker. Thus G4p=G4(t-1)+ygh3(t-1). Subtract row ledgers and use ygh(t-1)-ygh3=ygh2p to obtain first formula.

3. Row partition has A(t-1)frozen, I ghosts, pool, own diagonal, total t+1. Hence pool=t-A(t-1)-I. Substitute b_t=A(t)-A(t-1) and I=2t+1-d-H into I-pool+b_t-2+2H to obtain3t+A(t)-2d exactly.

4. Pool also equals A(d(t)-1)-A(t-1)+F_t by P11 and maximality. The definitional changes dG4versus Delta G cannot be dropped, and young indicator identities do not by themselves imply global density/sublinear Q. All finite corroboration outside flat data range is excluded from this proof.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This statement was independently audited on paper. The audit did not produce a new Lean formalization of the derived statement; its listed formal dependencies have separate verification receipts.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-a/silver-block-ghost-identities.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Block ghost identities, composed density and the C50 lineage ledger](../supplements/BLOCK-GHOSTS-AND-C50.md)
