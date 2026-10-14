# Tight gap-three missing-booker widths at most 18 are excluded at all indices

**Statement.** Under the stated gap-three M context and E=F=0, L=r−h≥19.

## Complete proof and definitions

- [Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Source-time capacity and the precisely scoped tight cases](../supplements/SOURCE-TIME-AND-TIGHTNESS.md)

The argument below and the linked full derivations form the reviewed proof. All stated hypotheses remain part of the result.

## Hypotheses and scope

- Mortal owner a with p=σ_a; missing-booker host h<a, r=σ_h, a+1<r<p=r+3.
- Tight slacks E=d(h)+A(h)−(2h+1)=0 and F=2h−r−A(h)=0.
- Banked gameF_col31_rail for q≥44 and reviewed exact initial recurrence prefix.

## Argument

1. E=F=0 gives d(h)=r+1 and old survivor roster U of sizer−h filling [h+1,r]. An active old affine rail with offsetg has birth-row outputh+g, so g≤r−h. This uses birth-row saturation before appealing to any future service date.

2. The exact declaration gameF_col31_rail(q), q≥44, gives f(q,31)=q+19. For h≥44, col31 is old and its rail remains live, so every tight width is at least 19.

3. For h7,…,43, independent literal replay gives E(h)>0 with minimum1. The initial h<7 domain in a gap3 M context is excluded by its actual death data: h0,2,5 immortal; h1 death2 and h3 death5 are too early for a+1<r with a>h; h4 death7 would force p10, which is diagonal; h6 death9 would force p12 victim8, contradicting a+1<9.

4. Together no tight gap3 M host of width≤18 exists. Width≥19 is not excluded. No global no-(h+3) row-gap premise, service-order monotonicity or future F0 transfer is used.

## Review and supporting evidence

- Historical original-claim verdict: accepted.
- This entry has a paper audit with an explicit verdict. Its formal dependencies have separate Lean receipts; this audit did not produce a Lean formalization of the derived statement.
- [Renewed statement and proof-completeness review](../../audit/prepublication/papers/PAPER-REVIEW.json)
- [Full independent audit and original-claim verdict](../../audit/full/paper-b/q-tight-width-eighteen.json)
- [Shared canonical foundation and exact Lean bridges](../../audit/full/CANONICAL-FOUNDATIONS.md)
- [Reproducible finite certificate data and checker](../../certificates/README.md)
- [Exact certificate input hashes](../../certificates/INPUT-MANIFEST.json)
- [Finite obligation replay receipt](../../certificates/CHECK-RESULTS.json)
- [Full proof and definitions: Canonical definitions for the corrected paper proofs](../supplements/CANONICAL-DEFINITIONS.md)
- [Full proof and definitions: Source-time capacity and the precisely scoped tight cases](../supplements/SOURCE-TIME-AND-TIGHTNESS.md)
