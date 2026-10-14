import G1LFutureOwnerEmpty
import R130AssignmentNoGapReduction

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
# G1-L round 2: discharging the carry-list interface hypothesis

`G1LFutureOwnerEmpty` proves the future-owner branch empty *conditionally* on one
interface input, consumed by `carryCount_le_blockerCount`: a duplicate-free
length-`C` list of positive blockers below `q`.  This file produces that list
directly from `gameF`, removing the hypothesis.

## The structural core (banked)

`[CarryDescendsToRowStart]` (`gameF_carry_descends_to_rowStart`): if column
`j < q` carries at row `q` — `gameF q j = v` with `v < q` — then the same value
already appears as the row-start of its own row, `gameF v j = v`.

Per the NOVELTY-N audit (`G1L-NOVELTY-VERDICT-2026-07-16.md`), this fact is an
immediate specialization of the banked, compiled
`gameF_low_cell_has_rowstart` (`R130AssignmentNoGapReduction`), which also
supplies the `j < v` witness.  An earlier revision of this file reproved it by
a fresh downward carry-branch induction; that proof is superseded here by the
direct citation.  Remaining local content:

* `gameF_carry_col_inj` — same-value carry columns coincide
  (`encoding_fixed_q_injective` at row `v`);
* the `carryList` constructor and its counting.

## What becomes unconditional

`selectedCut_no_future_owner_unconditional`,
`selectedCut_future_owner_empty_unconditional`,
`selectedCut_opening_dichotomy_unconditional`, phrased with the explicit carry
list `carryList q c` and `C = (carryList q c).length`, needing only `17 ≤ q`
and `c ≤ q`.
-/

/-- **[CarryDescendsToRowStart].**  A carry column `j < q` at row `q` with value
`v = gameF q j < q` already hosts that value as the row-start of row `v`:
`gameF v j = v`.  Direct corollary of the banked `gameF_low_cell_has_rowstart`
(`R130`). -/
theorem gameF_carry_descends_to_rowStart {q j v : Nat}
    (hjq : j < q) (hval : gameF q j = v) (hvq : v < q) :
    gameF v j = v := by
  have h := gameF_low_cell_has_rowstart (q := q) (c := j)
    (Nat.le_of_lt hjq) (by rw [hval]; omega)
  rw [hval] at h
  exact h.2

/-- **[C1].**  A carry value is a genuine row-start blocker: `S gameF v`,
witnessed by its own carry column `j` (with `j < v` from `R130`'s first
conjunct). -/
theorem gameF_carry_is_rowStart {q j v : Nat}
    (hjq : j < q) (hval : gameF q j = v) (hvq : v < q) :
    S gameF v := by
  have h := gameF_low_cell_has_rowstart (q := q) (c := j)
    (Nat.le_of_lt hjq) (by rw [hval]; omega)
  rw [hval] at h
  exact ⟨j, h.1, h.2⟩

/-- **[C2].**  Two carry columns below `q` carrying the same value coincide:
they descend to the same row-start value, then fixed-`q` injectivity at row `v`
identifies the columns. -/
theorem gameF_carry_col_inj {q j j' v : Nat}
    (hjq : j < q) (hj'q : j' < q)
    (hval : gameF q j = v) (hval' : gameF q j' = v) (hvq : v < q) :
    j = j' := by
  have hjv : j < v := by
    have h := encoded_gt game_encodes (Nat.le_of_lt hjq)
    rw [hval] at h; exact h
  have hj'v : j' < v := by
    have h := encoded_gt game_encodes (Nat.le_of_lt hj'q)
    rw [hval'] at h; exact h
  have h1 : gameF v j = v := gameF_carry_descends_to_rowStart hjq hval hvq
  have h2 : gameF v j' = v := gameF_carry_descends_to_rowStart hj'q hval' hvq
  have heq : gameF v j = gameF v j' := by rw [h1, h2]
  exact encoding_fixed_q_injective game_encodes (Nat.le_of_lt hjv) (Nat.le_of_lt hj'v) heq

/-- `map` of an on-list-injective function preserves `Nodup` (Std-only helper). -/
private theorem nodup_map_inj_on
    {f : Nat → Nat} {xs : List Nat}
    (hxs : xs.Nodup)
    (hinj : ∀ x, x ∈ xs → ∀ y, y ∈ xs → f x = f y → x = y) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a as ih =>
      rw [List.nodup_cons] at hxs
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih hxs.2 (fun x hx y hy => hinj x (by simp [hx]) y (by simp [hy]))⟩
      intro hmem
      rcases List.mem_map.mp hmem with ⟨b, hb, hab⟩
      have hbeq : a = b := hinj a (by simp) b (by simp [hb]) hab.symm
      exact hxs.1 (by rw [hbeq]; exact hb)

/-- **[C3] constructor.**  The carry columns of `Row_q(< c)`: those `j < c`
whose row-`q` value stays below the row (the CARRY-branch columns). -/
noncomputable def carryList (q c : Nat) : List Nat :=
  (List.range c).filter (fun j => decide (gameF q j < q))

theorem mem_carryList {q c j : Nat} :
    j ∈ carryList q c ↔ j < c ∧ gameF q j < q := by
  simp only [carryList, List.mem_filter, decide_eq_true_eq, List.mem_range]

theorem carryList_nodup (q c : Nat) : (carryList q c).Nodup := by
  unfold carryList
  exact List.filter_sublist.nodup List.nodup_range

/-- The carry-value list `carries = (carryList q c).map (gameF q)` is
duplicate-free (via `gameF_carry_col_inj`). -/
theorem carryList_carries_nodup {q c : Nat} (hcq : c ≤ q) :
    ((carryList q c).map (gameF q)).Nodup := by
  apply nodup_map_inj_on (carryList_nodup q c)
  intro x hx y hy hxy
  rw [mem_carryList] at hx hy
  exact gameF_carry_col_inj (v := gameF q x) (by omega) (by omega) rfl hxy.symm hx.2

/-- Every member of the carry-value list is a positive blocker below `q`. -/
theorem carryList_carries_mem {q c : Nat} (hcq : c ≤ q) :
    ∀ v ∈ (carryList q c).map (gameF q), 0 < v ∧ v < q ∧ S gameF v := by
  intro v hv
  rcases List.mem_map.mp hv with ⟨j, hjmem, hjv⟩
  rw [mem_carryList] at hjmem
  have hjq : j < q := by omega
  have hvq : v < q := by rw [← hjv]; exact hjmem.2
  refine ⟨?_, hvq, ?_⟩
  · have h := encoded_gt game_encodes (Nat.le_of_lt hjq)
    rw [hjv] at h
    omega
  · exact gameF_carry_is_rowStart hjq hjv hvq

/-- The carry-count bound, now discharged from `gameF` for the explicit carry
list.  `C = (carryList q c).length` is at most the blocker count through
`q-1`. -/
theorem carryList_count_le_blockerCount {q c C : Nat} (hcq : c ≤ q)
    (hC : C = (carryList q c).length) :
    C ≤ gameFBlockerCountThrough (q - 1) := by
  have hlen : ((carryList q c).map (gameF q)).length = C := by
    rw [List.length_map]; exact hC.symm
  exact carryCount_le_blockerCount ((carryList q c).map (gameF q))
    hlen (carryList_carries_nodup hcq) (carryList_carries_mem hcq)

/-- **[FINAL] `SelectedCutNoFutureOwner`, unconditional.**  At the selected cut
(`q ≥ 17`, `c ≤ q`, `C = (carryList q c).length`, `T = q+C+1`), no future
owner `a > q` has diagonal value `gameF a a <= T`. -/
theorem selectedCut_no_future_owner_unconditional
    {q c C T : Nat} (hq : 17 ≤ q) (hcq : c ≤ q)
    (hC : C = (carryList q c).length) (hT : T = q + C + 1) :
    ∀ x, x ≤ T → ∀ a, q < a → gameF a a ≠ x :=
  selectedCut_no_future_owner hq hT (carryList_count_le_blockerCount hcq hC)

/-- **[FINAL] future-owner disjunct empty, unconditional.** -/
theorem selectedCut_future_owner_empty_unconditional
    {q c C T w : Nat} (hq : 17 ≤ q) (hcq : c ≤ q)
    (hC : C = (carryList q c).length) (hT : T = q + C + 1)
    (hwT : w ≤ T) :
    ¬ ∃ a, q < a ∧ a < w ∧ gameF a a = w :=
  selectedCut_future_owner_empty hq hT (carryList_count_le_blockerCount hcq hC) hwT

/-- **[FINAL] trichotomy collapse, unconditional.** -/
theorem selectedCut_opening_dichotomy_unconditional
    {q c C T e w : Nat} (hq : 17 ≤ q) (hcq : c ≤ q)
    (hC : C = (carryList q c).length) (hT : T = q + C + 1)
    (hwT : w ≤ T)
    (heq : e < q) (hvalue : gameF q e = w) (hqw : q < w) :
    (∃ a, e < a ∧ a < q ∧ gameF a a = w) ∨
      (∃ cc, e < cc ∧ cc < w ∧ gameF w cc = w) :=
  selectedCut_opening_dichotomy hq hT (carryList_count_le_blockerCount hcq hC)
    hwT heq hvalue hqw

end ChompLean

#print axioms ChompLean.gameF_carry_descends_to_rowStart
#print axioms ChompLean.gameF_carry_is_rowStart
#print axioms ChompLean.gameF_carry_col_inj
#print axioms ChompLean.mem_carryList
#print axioms ChompLean.carryList_nodup
#print axioms ChompLean.carryList_carries_nodup
#print axioms ChompLean.carryList_carries_mem
#print axioms ChompLean.carryList_count_le_blockerCount
#print axioms ChompLean.selectedCut_no_future_owner_unconditional
#print axioms ChompLean.selectedCut_future_owner_empty_unconditional
#print axioms ChompLean.selectedCut_opening_dichotomy_unconditional
