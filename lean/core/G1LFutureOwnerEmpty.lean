import R201DiagDoubleSlackCeilingChain
import R136PreviewHighRunScalarCounterframe
import R55OverlapLedgerEventEEchoStaircase

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
# G1-L: the future-owner branch of the first-cut opening trichotomy is empty

At the selected first active cut of logical row `u` (`q = u-3`, carry count
`C`, budget `T = q + C + 1`), the middle disjunct

  `∃ a, q < a ∧ a < w ∧ gameF a a = w`

of `gameF_high_cell_opening_trichotomy`
(`R136PreviewHighRunScalarCounterframe`) is impossible for every base hole
`w ≤ T`.  Equivalently, no diagonal value strictly above the cut row `q` ever
lands in the closed budget interval `[·, T]`.

## What is proved unconditionally here

Given the carry-count bound `C ≤ gameFBlockerCountThrough (q-1)` and `q ≥ 17`:

* `selectedCut_no_future_owner`  — the literal goal theorem
  (`∀ x ≤ T, ∀ a > q, gameF a a ≠ x`);
* `selectedCut_future_owner_empty` — the middle disjunct is empty;
* `selectedCut_opening_dichotomy` — the compiled trichotomy collapses to the
  past-owner / row-start dichotomy.

The two number-theoretic inputs are banked:

* upper ceiling `gameFBlockerCountThrough_ceiling` (`R201`:
  `2 * gameFBlockerCountThrough a + 4 ≤ a + 1` for `a ≥ 16`);
* the unconditional `3/2` diagonal envelope `gameF_overlap_env_lower_bound`
  (`R55`: `t + 1 + (t+1)/2 ≤ gameF t t`, no guard — replaces the earlier
  `gameF_FloorPlus` route per the NOVELTY-N simplification,
  `G1L-NOVELTY-VERDICT-2026-07-16.md`).

## The one interface input

The carry-count bound is reduced (`carryCount_le_blockerCount`) to the raw
structural facts about the carry list of `Row_q(< c)`: it is duplicate-free,
has length `C`, and every carry value is a positive blocker below `q`.
Producing such a list from the actual carry cells is the honest game-level
obligation (see `missing_bank_pieces`); it is NOT proved from `gameF` here,
so it enters as an explicit hypothesis, never as a receipt or `sorry`.

Circularity fence: this file consumes only `gameF`, the blocker-count
list machinery, the two `R201` diagonal facts, and the `R136` trichotomy.
It does NOT use `RetentionEnsemble`, `CausalLeftInitializer30`,
`FirstCutBaseOneHole`, or any RLE3 / G1-S item.
-/

/-- **Carry-count reduction.**  A duplicate-free list of length `C` whose
members are positive blockers below `q` has length at most the number of
blockers through `q-1`.  This is the only place the carry structural facts
are consumed, and it is proved outright from the blocker-list membership
characterisation. -/
theorem carryCount_le_blockerCount
    {q C : Nat} (carries : List Nat)
    (hlen : carries.length = C)
    (hnodup : carries.Nodup)
    (hmem : ∀ v ∈ carries, 0 < v ∧ v < q ∧ S gameF v) :
    C ≤ gameFBlockerCountThrough (q - 1) := by
  have hsub : carries ⊆ gameFBlockersThroughList (q - 1) := by
    intro v hv
    obtain ⟨hpos, hlt, hS⟩ := hmem v hv
    exact gameF_mem_blockersThroughList.mpr ⟨hpos, by omega, hS⟩
  calc C = carries.length := hlen.symm
    _ ≤ (gameFBlockersThroughList (q - 1)).length :=
          nodup_subset_length_le hnodup hsub
    _ = gameFBlockerCountThrough (q - 1) := rfl

/-- **Core arithmetic gap.**  Under the carry-count bound and `q ≥ 17`, every
diagonal value strictly above `q` overshoots the budget `T = q + C + 1`.

`2C ≤ q-4` from the blocker ceiling, so `T ≤ (3q-2)/2`, while the unconditional
`R55` envelope gives `gameF a a ≥ a+1+(a+1)/2 ≥ q+2+(q+2)/2` at `a ≥ q+1`;
the strict gap closes by `omega`. -/
theorem selectedCut_diag_gt_budget
    {q C : Nat} (hq : 17 ≤ q)
    (hC : C ≤ gameFBlockerCountThrough (q - 1)) :
    ∀ a, q < a → q + C + 1 < gameF a a := by
  intro a hqa
  have hceil := gameFBlockerCountThrough_ceiling (a := q - 1) (by omega)
  have henv := gameF_overlap_env_lower_bound a
  omega

/-- **Goal theorem `SelectedCutNoFutureOwner`.**  At the selected cut, no
diagonal value above the cut row `q` equals any value in the closed budget
interval `[·, T]`. -/
theorem selectedCut_no_future_owner
    {q C T : Nat} (hq : 17 ≤ q)
    (hT : T = q + C + 1)
    (hC : C ≤ gameFBlockerCountThrough (q - 1)) :
    ∀ x, x ≤ T → ∀ a, q < a → gameF a a ≠ x := by
  intro x hx a hqa
  have hgt := selectedCut_diag_gt_budget hq hC a hqa
  rw [hT] at hx
  omega

/-- **Future-owner disjunct empty.**  For every base hole `w ≤ T`, the middle
branch `∃ a, q < a ∧ a < w ∧ gameF a a = w` of the opening trichotomy is
impossible. -/
theorem selectedCut_future_owner_empty
    {q C T w : Nat} (hq : 17 ≤ q)
    (hT : T = q + C + 1)
    (hC : C ≤ gameFBlockerCountThrough (q - 1))
    (hwT : w ≤ T) :
    ¬ ∃ a, q < a ∧ a < w ∧ gameF a a = w := by
  rintro ⟨a, hqa, _haw, hval⟩
  have hgt := selectedCut_diag_gt_budget hq hC a hqa
  rw [hval] at hgt
  omega

/-- **Trichotomy collapse.**  With the future-owner branch eliminated, the
compiled `gameF_high_cell_opening_trichotomy` at the selected cut reduces to
the past-owner / row-start dichotomy. -/
theorem selectedCut_opening_dichotomy
    {q e w C T : Nat}
    (hq : 17 ≤ q)
    (hT : T = q + C + 1)
    (hC : C ≤ gameFBlockerCountThrough (q - 1))
    (hwT : w ≤ T)
    (heq : e < q) (hvalue : gameF q e = w) (hqw : q < w) :
    (∃ a, e < a ∧ a < q ∧ gameF a a = w) ∨
      (∃ c, e < c ∧ c < w ∧ gameF w c = w) := by
  rcases gameF_high_cell_opening_trichotomy heq hvalue hqw with
    hpast | hfut | hrow
  · exact Or.inl hpast
  · exact absurd hfut (selectedCut_future_owner_empty hq hT hC hwT)
  · exact Or.inr hrow

/-- **End-to-end from the raw carry facts.**  The future-owner branch is empty
whenever the carry cells of `Row_q(< c)` present as a duplicate-free length-`C`
list of positive blockers below `q`. -/
theorem selectedCut_future_owner_empty_of_carries
    {q C T w : Nat} (hq : 17 ≤ q)
    (hT : T = q + C + 1)
    (carries : List Nat)
    (hlen : carries.length = C)
    (hnodup : carries.Nodup)
    (hmem : ∀ v ∈ carries, 0 < v ∧ v < q ∧ S gameF v)
    (hwT : w ≤ T) :
    ¬ ∃ a, q < a ∧ a < w ∧ gameF a a = w :=
  selectedCut_future_owner_empty hq hT
    (carryCount_le_blockerCount carries hlen hnodup hmem) hwT

end ChompLean

#print axioms ChompLean.carryCount_le_blockerCount
#print axioms ChompLean.selectedCut_diag_gt_budget
#print axioms ChompLean.selectedCut_no_future_owner
#print axioms ChompLean.selectedCut_future_owner_empty
#print axioms ChompLean.selectedCut_opening_dichotomy
#print axioms ChompLean.selectedCut_future_owner_empty_of_carries
