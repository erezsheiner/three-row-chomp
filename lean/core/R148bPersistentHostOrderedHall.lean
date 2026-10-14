import R148cFreezeCrossIncidence
import R147BackwardHistoryGraftObstruction

set_option autoImplicit false

namespace ChompLean

/-!
R148b: the ordered Hall inequality forced by the full blocker host trail.

For a blocker `v` with freeze column `c`, HostCensusRigidity supplies one
distinct host column for every row in `[r,v)`, where `c < r < v`.  Full
FreezeOrder puts the distinct freeze columns of all blockers at most `r`
strictly below `c`.  At rows at least `r` those columns are carries, hence
they cannot be host columns for the larger value `v`.  The two packets are
therefore disjoint subsets of the `c` columns below `c`.

The first theorem is the finite Hall core.  The recurrence-specific work is
exactly what constructs its two injections and their cross-disjointness.
-/

/-- Elementary pigeonhole principle for finite initial intervals.  This is
proved from the bank's `interval_inj_surj`, so no external cardinal library
is needed. -/
theorem r148b_fin_injective_card_le
    {n c : Nat} (f : Fin n -> Fin c) (hf : Function.Injective f) :
    n <= c := by
  apply Nat.le_of_not_gt
  intro hcn
  let g : Nat -> Nat := fun x =>
    if hx : 0 < x /\ x < c + 1 then
      (f ⟨x - 1, by omega⟩).val + 1
    else
      0
  have hmap : forall x, 0 < x -> x < c + 1 ->
      0 < g x /\ g x < c + 1 := by
    intro x hx0 hxc
    rw [show g x = (f ⟨x - 1, by omega⟩).val + 1 by
      simp [g, hx0, hxc]]
    exact ⟨by omega, by have := (f ⟨x - 1, by omega⟩).isLt; omega⟩
  have hinj : forall x y, 0 < x -> x < c + 1 ->
      0 < y -> y < c + 1 -> g x = g y -> x = y := by
    intro x y hx0 hxc hy0 hyc hxy
    have hfx : g x = (f ⟨x - 1, by omega⟩).val + 1 := by
      simp [g, hx0, hxc]
    have hfy : g y = (f ⟨y - 1, by omega⟩).val + 1 := by
      simp [g, hy0, hyc]
    have hval : (f ⟨x - 1, by omega⟩).val =
        (f ⟨y - 1, by omega⟩).val := by omega
    have hfin : f ⟨x - 1, by omega⟩ = f ⟨y - 1, by omega⟩ :=
      Fin.ext hval
    have harg : x - 1 = y - 1 := congrArg Fin.val (hf hfin)
    omega
  let extra : Fin n := ⟨c, hcn⟩
  let k : Nat := (f extra).val + 1
  have hk0 : 0 < k := by simp [k]
  have hkc : k < c + 1 := by
    have := (f extra).isLt
    dsimp [k]
    omega
  rcases interval_inj_surj (q := 0) (p := c + 1) (by omega) g hmap hinj
      k hk0 hkc with ⟨x, hx0, hxc, hgx⟩
  have hgform : g x = (f ⟨x - 1, by omega⟩).val + 1 := by
    simp [g, hx0, hxc]
  have hval : (f ⟨x - 1, by omega⟩).val = (f extra).val := by
    rw [hgform] at hgx
    simp [k] at hgx
    omega
  have hfin : f ⟨x - 1, by omega⟩ = f extra := Fin.ext hval
  have harg := congrArg Fin.val (hf hfin)
  dsimp [extra] at harg
  omega

/-- Two disjoint injective packets living in `c` slots obey the exact Hall
capacity inequality. -/
theorem r148b_two_packet_ordered_hall
    {hostCount frozenCount c : Nat}
    (host : Fin hostCount -> Fin c)
    (frozen : Fin frozenCount -> Fin c)
    (hHost : Function.Injective host)
    (hFrozen : Function.Injective frozen)
    (hCross : forall i j, host i ≠ frozen j) :
    hostCount + frozenCount <= c := by
  let allocation : Fin (hostCount + frozenCount) -> Fin c := fun i =>
    if hi : i.val < hostCount then
      host ⟨i.val, hi⟩
    else
      frozen ⟨i.val - hostCount, by omega⟩
  have hAllocation : Function.Injective allocation := by
    intro i j hij
    by_cases hi : i.val < hostCount
    · by_cases hj : j.val < hostCount
      · have hhosts : host ⟨i.val, hi⟩ = host ⟨j.val, hj⟩ := by
          simpa [allocation, hi, hj] using hij
        have hargs := congrArg Fin.val (hHost hhosts)
        exact Fin.ext hargs
      · have hbad : host ⟨i.val, hi⟩ =
            frozen ⟨j.val - hostCount, by omega⟩ := by
          simpa [allocation, hi, hj] using hij
        exact False.elim (hCross _ _ hbad)
    · by_cases hj : j.val < hostCount
      · have hbad : frozen ⟨i.val - hostCount, by omega⟩ =
            host ⟨j.val, hj⟩ := by
          simpa [allocation, hi, hj] using hij
        exact False.elim (hCross _ _ hbad.symm)
      · have hfrozen : frozen ⟨i.val - hostCount, by omega⟩ =
            frozen ⟨j.val - hostCount, by omega⟩ := by
          simpa [allocation, hi, hj] using hij
        have hargs := congrArg Fin.val (hFrozen hfrozen)
        have hsub : i.val - hostCount = j.val - hostCount := hargs
        have hilower : hostCount <= i.val := Nat.le_of_not_gt hi
        have hjlower : hostCount <= j.val := Nat.le_of_not_gt hj
        apply Fin.ext
        omega
  exact r148b_fin_injective_card_le allocation hAllocation

/-- Recurrence-interface form.  `blockersThrough r` is `A(r)`.  Under HCR
and local FreezeOrder below `v`, the two functions are respectively the
host columns of rows `[r,v)` and the freeze columns of blockers `<= r`.
-/
theorem r148b_persistent_host_ordered_hall
    {v c r blockersThrough : Nat}
    (_hvr : r <= v)
    (host : Fin (v - r) -> Fin c)
    (frozen : Fin blockersThrough -> Fin c)
    (hHost : Function.Injective host)
    (hFrozen : Function.Injective frozen)
    (hCross : forall i j, host i ≠ frozen j) :
    v - r + blockersThrough <= c := by
  exact r148b_two_packet_ordered_hall host frozen hHost hFrozen hCross

/-- The endpoint form at `r=c+1`.  This is the strengthened TNEW inequality
`v + A(c+1) <= 2c+1`. -/
theorem r148b_host_hall_endpoint
    {v c blockersThrough : Nat}
    (hcv : c + 1 <= v)
    (hHall : v - (c + 1) + blockersThrough <= c) :
    v + blockersThrough <= 2 * c + 1 := by
  omega

/-! ## The two R145 outer schedules fail the new necessary condition. -/

theorem r148b_bridge0_outer_schedule_fails :
    ¬ (61 - 37 + 15 <= 36) := by
  omega

theorem r148b_bridgeMinus1_outer_schedule_fails :
    ¬ (52 - 32 + 13 <= 31) := by
  omega

/-!
## The R146 `A_k` late-freeze schedule fails already at its first late
blocker.

For `k>0`, that blocker is `v=4k+4`, its advertised freeze column is
`c=2k+2`, and the first host row is `r=2k+3`.  The early half of `A_k` has
`A_k(r)=k+1`.  Ordered Hall would say `3k+2 <= 2k+2`, impossible.
-/

theorem r148b_Ak_first_late_freeze_fails
    (k : Nat) (hk : 0 < k) :
    ¬ ((4 * k + 4) - (2 * k + 3) + (k + 1) <= 2 * k + 2) := by
  intro h
  have hsub : (4 * k + 4) - (2 * k + 3) = 2 * k + 1 := by omega
  rw [hsub] at h
  omega

/-! ## The R148c high-freeze repair and the R147 additive packet -/

/-- Once a column freezes at `(w,e)`, the constant branch carries `w`
forever upward.  This is the actual Brouwer recurrence, not a scalar freeze
ledger. -/
theorem r148b_freeze_value_carries_upward
    (M : RecurrenceModel) {w e row : Nat}
    (hew : e < w) (hwrow : w <= row)
    (hfreeze : M.f w e = w) :
    M.f row e = w := by
  have hsmall : M.f w e < w + 1 := by
    rw [hfreeze]
    omega
  have hcarry := constant_from M hew hsmall (row - w)
  have hsum : w + (row - w) = row := by omega
  simpa [hsum, hfreeze] using hcarry

/-- Consequently a frozen column cannot support a different advertised
high MEX value at a later row. -/
theorem r148b_frozen_column_rejects_later_value
    (M : RecurrenceModel) {w e row x : Nat}
    (hew : e < w) (hwrow : w <= row) (hwx : w ≠ x)
    (hfreeze : M.f w e = w) :
    M.f row e ≠ x := by
  intro hout
  have hcarry := r148b_freeze_value_carries_upward M hew hwrow hfreeze
  exact hwx (hcarry.symm.trans hout)

/-- If `k=2m`, the high schedule freezes the first R147 target column
`c0=14m` at the earlier late blocker `17m+4`.  For `m>=2` this is before
the first target row `20m`, so the additive output cannot occupy that cell.
-/
theorem r148b_highFreeze_even_k_kills_additive_target
    (m : Nat) (hm : 2 <= m)
    (hfreeze :
      gameF (r146LateBlocker (2 * m) (3 * m + 1))
          (R148HighFreeze (7 * m + 1)) =
        r146LateBlocker (2 * m) (3 * m + 1)) :
    gameF (r147R0 (2 * m)) (r147C0 (2 * m)) ≠
      r147AddValue (r147SeedM (2 * m)) 0 0 := by
  have he : R148HighFreeze (7 * m + 1) = r147C0 (2 * m) := by
    simp [R148HighFreeze, r147C0]
    omega
  rw [← he]
  apply r148b_frozen_column_rejects_later_value gameRecurrenceModel
      (w := r146LateBlocker (2 * m) (3 * m + 1))
      (e := R148HighFreeze (7 * m + 1))
  · simp [r146LateBlocker, R148HighFreeze]
    omega
  · simp [r146LateBlocker, r147R0, FrameV]
    omega
  · simp [r146LateBlocker, r147AddValue, r147SeedM]
    omega
  · exact hfreeze

/-- If `k=2m+1`, the high schedule freezes the middle R147 target column
`c0+1=14m+8` at the earlier late blocker `17m+14`.  Again the target cell
is already a carry. -/
theorem r148b_highFreeze_odd_k_kills_additive_target
    (m : Nat) (hm : 2 <= m)
    (hfreeze :
      gameF (r146LateBlocker (2 * m + 1) (3 * m + 3))
          (R148HighFreeze (7 * m + 5)) =
        r146LateBlocker (2 * m + 1) (3 * m + 3)) :
    gameF (r147R0 (2 * m + 1)) (r147C0 (2 * m + 1) + 1) ≠
      r147AddValue (r147SeedM (2 * m + 1)) 0 1 := by
  have he : R148HighFreeze (7 * m + 5) = r147C0 (2 * m + 1) + 1 := by
    simp [R148HighFreeze, r147C0]
    omega
  rw [← he]
  apply r148b_frozen_column_rejects_later_value gameRecurrenceModel
      (w := r146LateBlocker (2 * m + 1) (3 * m + 3))
      (e := R148HighFreeze (7 * m + 5))
  · simp [r146LateBlocker, R148HighFreeze]
    omega
  · simp [r146LateBlocker, r147R0, FrameV]
    omega
  · simp [r146LateBlocker, r147AddValue, r147SeedM]
    omega
  · exact hfreeze

/-- The even one-frozen-target surgery in R148c deliberately retains this
same frozen target, so it remains incompatible with using that column as the
first R147 additive output cell. -/
theorem r148b_even_oneFrozen_surgery_is_not_threeOutput_R147
    (m : Nat) (hm : 2 <= m)
    (hfreeze :
      gameF (r146LateBlocker (2 * m) (3 * m + 1))
          (R148HighFreeze (7 * m + 1)) =
        r146LateBlocker (2 * m) (3 * m + 1)) :
    gameF (r147R0 (2 * m)) (r147C0 (2 * m)) ≠
      r147AddValue (r147SeedM (2 * m)) 0 0 :=
  r148b_highFreeze_even_k_kills_additive_target m hm hfreeze

/-- The odd baseline/one-frozen repair retains the middle target, so its
second R147 output cell is likewise a carry. -/
theorem r148b_odd_oneFrozen_surgery_is_not_threeOutput_R147
    (m : Nat) (hm : 2 <= m)
    (hfreeze :
      gameF (r146LateBlocker (2 * m + 1) (3 * m + 3))
          (R148HighFreeze (7 * m + 5)) =
        r146LateBlocker (2 * m + 1) (3 * m + 3)) :
    gameF (r147R0 (2 * m + 1)) (r147C0 (2 * m + 1) + 1) ≠
      r147AddValue (r147SeedM (2 * m + 1)) 0 1 :=
  r148b_highFreeze_odd_k_kills_additive_target m hm hfreeze

/-! The carry obstruction kills the literal even-column schedule, but not
the whole high-freeze idea.  The following arithmetic certificates exhibit
a local kink which leaves all three target columns out of the freeze image
while preserving strict order and the PiZero load equation. -/

theorem r148b_even_local_kink_leaves_target_gap
    (m : Nat) (hm : 2 <= m) :
    let i := 7 * m + 1
    let cA := 14 * m - 1
    let cB := 14 * m + 3
    R148HighFreeze (i - 1) < cA /\
    cA < r147C0 (2 * m) /\
    r147C0 (2 * m) + 2 < cB /\
    cB < R148HighFreeze (i + 2) /\
    cA + 2 = 2 * i - 1 /\
    cB + 0 = 2 * (i + 1) - 1 := by
  dsimp [R148HighFreeze, r147C0]
  omega

theorem r148b_odd_local_kink_leaves_target_gap
    (m : Nat) (hm : 2 <= m) :
    let i := 7 * m + 5
    let cA := 14 * m + 5
    let cB := 14 * m + 6
    R148HighFreeze (i - 2) < cA /\
    cA < cB /\
    cB < r147C0 (2 * m + 1) /\
    r147C0 (2 * m + 1) + 2 < R148HighFreeze (i + 1) /\
    cA + 2 = 2 * (i - 1) - 1 /\
    cB + 3 = 2 * i - 1 := by
  dsimp [R148HighFreeze, r147C0]
  omega

/-- The two predecessor columns needed by the even kink meet the sharp
freeze-cross reach condition. -/
theorem r148b_even_kink_two_predecessors_reach
    (m : Nat) (hm : 2 <= m) :
    let k := 2 * m
    let j := 3 * m + 1
    r146LateBlocker k j <=
        r146LateBlocker k (j - 1) + R148HighFreeze (7 * m) /\
    r146LateBlocker k j <=
        r146LateBlocker k (j - 2) + R148HighFreeze (7 * m - 1) := by
  dsimp [r146LateBlocker, R148HighFreeze]
  omega

/-- The three predecessor columns needed by the odd kink likewise meet the
reach condition. -/
theorem r148b_odd_kink_three_predecessors_reach
    (m : Nat) (hm : 2 <= m) :
    let k := 2 * m + 1
    let j := 3 * m + 3
    r146LateBlocker k j <=
        r146LateBlocker k (j - 1) + (14 * m + 5) /\
    r146LateBlocker k j <=
        r146LateBlocker k (j - 2) + R148HighFreeze (7 * m + 3) /\
    r146LateBlocker k j <=
        r146LateBlocker k (j - 3) + R148HighFreeze (7 * m + 2) := by
  dsimp [r146LateBlocker, R148HighFreeze]
  omega

def r148bTargetHostRow (k j : Nat) : Nat := r147C0 k + j + 3

/-- Three distinct, pre-target rows can host the critical blocker in the
three persistent target columns.  The cell ceiling has ample slack. -/
theorem r148b_target_host_geometry
    (k j : Nat) (hk : 4 <= k) (hj : j <= 2) :
    r147C0 k + j < r148bTargetHostRow k j /\
    r148bTargetHostRow k j < r147R0 k /\
    FrameQ k <= r148bTargetHostRow k j + (r147C0 k + j) + 1 := by
  simp [r148bTargetHostRow, r147C0, r147R0, FrameV, FrameQ]
  omega

/-- A host in the same column at an earlier row is literally an `R`-source
entry for every later target cell. -/
theorem r148b_same_column_host_enters_later_source
    (f : Nat -> Nat -> Nat) {x e row q : Nat}
    (hex : e < x) (hxr : x < row) (hhost : f x e = q) :
    R f row e q := by
  refine ⟨x, hxr, ?_⟩
  have hmin : min x e = e := Nat.min_eq_right (Nat.le_of_lt hex)
  simpa [hmin] using hhost

/-- The critical blocker `q=10k+1` is already one of the low labels which
the R147 additive source declares present.  Thus its forced target-column
hosts add no new forbidden label; they pay an existing MEX obligation. -/
theorem r148b_critical_q_is_in_additive_base
    (k n j : Nat) (hk : 1 <= k) :
    R147AddSource (r147SeedM k) n j (FrameQ k) := by
  left
  simp [r147SeedM, FrameQ]
  omega

#print axioms r148b_persistent_host_ordered_hall
#print axioms r148b_host_hall_endpoint
#print axioms r148b_highFreeze_even_k_kills_additive_target
#print axioms r148b_highFreeze_odd_k_kills_additive_target
#print axioms r148b_even_oneFrozen_surgery_is_not_threeOutput_R147
#print axioms r148b_odd_oneFrozen_surgery_is_not_threeOutput_R147
#print axioms r148b_even_local_kink_leaves_target_gap
#print axioms r148b_odd_local_kink_leaves_target_gap
#print axioms r148b_same_column_host_enters_later_source

end ChompLean
