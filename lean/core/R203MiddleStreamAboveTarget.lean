import R202LowTargetMexRowInvariance
import R200FloorPlusFromDiagDoubleSlack

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ChompLean

/-!
# R203: the early W4 middle stream lies strictly above the target

The apparent rail-shadow problem concerns values in the `K = 10` midpoint
cohort on a row `u-L`. The sharp blocker-count ceiling now proves that,
past a small explicit base, every such value is larger than `u` itself.
Combined with `R202.mexRow_low_output_invariant`, the entire middle stream
is therefore a high tail: its rail bookkeeping cannot move the terminal
target `u` or any smaller output.
-/

/-- A filtered blocker prefix cannot contain more entries than its source
interval. -/
theorem gameFBlockerCountThrough_le_index (n : Nat) :
    gameFBlockerCountThrough n <= n := by
  classical
  have h := List.length_filter_le
    (fun k : Nat => decide (S gameF k)) (List.range' 1 n)
  simpa [gameFBlockerCountThrough, gameFBlockersThroughList] using h

/-- The actual midpoint never exceeds its value index. This elementary
bound is used only to enter the sharp `n >= 16` blocker-count regime. -/
theorem actualBlockerMidpoint_le_index (v : Nat) :
    actualBlockerMidpoint v <= v := by
  have hcount := gameFBlockerCountThrough_le_index (v - 1)
  unfold actualBlockerMidpoint countMidpoint
  omega

/-- Quantitative separation. On row `u-L`, membership above the lower edge
of the `K=10` midpoint band forces `v>u` once `u >= 4L+33`.

DDS gives `2*A(v-1)+4 <= v`, while strict lower-band membership gives
`g(v) >= u-L-9`; combining `2g(v) <= v+A(v-1)` contradicts `v<=u`. -/
theorem actualBlockerMidpoint_lowerBand10_above_target
    {u L v : Nat}
    (hDDS : ActualDiagDoubleSlack)
    (hu : 4 * L + 33 <= u)
    (hband : (u - L) - 10 < actualBlockerMidpoint v) :
    u < v := by
  have hmidLe : actualBlockerMidpoint v <= v :=
    actualBlockerMidpoint_le_index v
  have hv17 : 17 <= v := by
    omega
  have hcount := gameFBlockerCountThrough_ceiling_of_diagDoubleSlack
    hDDS (a := v - 1) (by omega)
  have hmidFloor :
      2 * actualBlockerMidpoint v <=
        v + gameFBlockerCountThrough (v - 1) := by
    unfold actualBlockerMidpoint countMidpoint
    omega
  apply Nat.lt_of_not_ge
  intro hvu
  omega

/-- Literal list-membership form for the actual `K=10` middle cohort. -/
theorem actualBlockerMiddleCohort_K10_above_target
    {u L v : Nat}
    (hDDS : ActualDiagDoubleSlack)
    (hu : 4 * L + 33 <= u)
    (hv : List.Mem v (actualBlockerMiddleCohortList (u - L) 10)) :
    u < v := by
  have hband := (gameF_mem_actualBlockerMiddleCohortList.mp hv).1
  exact actualBlockerMidpoint_lowerBand10_above_target hDDS hu hband

/-- Uniform wrapper for all three early rows used by the W4 relay. -/
theorem actualBlockerMiddleCohort_earlyW4_above_target
    {u L v : Nat}
    (hDDS : ActualDiagDoubleSlack)
    (hu : 113 <= u)
    (hL : L = 13 \/ L = 18 \/ L = 20)
    (hv : List.Mem v (actualBlockerMiddleCohortList (u - L) 10)) :
    u < v := by
  refine actualBlockerMiddleCohort_K10_above_target
    (L := L) (v := v) hDDS ?_ hv
  rcases hL with rfl | rfl | rfl <;> omega

/-- Target-specific rail-shadow erasure interface. If two MEX rows have the
same vertical sources through `u`, arbitrary differences in the (now proved
high) middle stream cannot change the host of `u` or of any smaller value.
This is the recurrence-level replacement for a full rail-shadow simulation
theorem. -/
theorem earlyW4_highMiddleTail_cannot_move_low_output
    {f g : Nat -> Nat -> Nat} {q u c : Nat}
    (hvertical : VerticalSourceAgreeThrough f g q u)
    (hmexF : forall x, x <= q -> IsMex (B f q x) (f q x))
    (hmexG : forall x, x <= q -> IsMex (B g q x) (g q x))
    (hcq : c <= q)
    (hlow : f q c <= u \/ g q c <= u) :
    f q c = g q c := by
  exact mexRow_low_output_invariant hvertical hmexF hmexG c hcq hlow

/-- Physical mixed-scan form. Sealed/pinned columns may be handled by exact
agreement and all other columns by their MEX branch. Once the shadow error
is confined to middle-cohort values (hence values above `u` by the theorem
above), the physical host column of the terminal target `u` is invariant. -/
theorem earlyW4_railShadow_cannot_move_target
    {f g : Nat -> Nat -> Nat} {q u c : Nat}
    (hvertical : VerticalSourceAgreeThrough f g q u)
    (hstep : forall x, x <= q ->
      f q x = g q x \/
        (IsMex (B f q x) (f q x) /\
          IsMex (B g q x) (g q x)))
    (hcq : c <= q) :
    f q c = u <-> g q c = u := by
  exact mixedRow_low_host_iff hvertical hstep hcq (Nat.le_refl u)

end ChompLean

#print axioms ChompLean.gameFBlockerCountThrough_le_index
#print axioms ChompLean.actualBlockerMidpoint_le_index
#print axioms ChompLean.actualBlockerMidpoint_lowerBand10_above_target
#print axioms ChompLean.actualBlockerMiddleCohort_K10_above_target
#print axioms ChompLean.actualBlockerMiddleCohort_earlyW4_above_target
#print axioms ChompLean.earlyW4_highMiddleTail_cannot_move_low_output
#print axioms ChompLean.earlyW4_railShadow_cannot_move_target
