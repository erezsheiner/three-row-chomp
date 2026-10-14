import R194BlockerMidpointFiniteCohort
import R181ActualTerminalBlockerOrderedHall

set_option autoImplicit false

namespace ChompLean

/-!
# Actual-game blocker midpoint has uniformly finite cohorts

`gameFBlockerCountThrough n` is the length of the filtered list of actual
row-start blockers in `[1,n]`.  Extending the prefix by one appends exactly
the candidate `n+1`, so the count increment is zero or one.  This closes the
only abstract interface in `R194BlockerMidpointFiniteCohort` and yields an
unconditional all-index cohort bound for the actual game.
-/

/-- The actual blocker-prefix count changes by exactly zero or one. -/
theorem gameFBlockerCountThrough_unitIncrement01 :
    UnitIncrement01 gameFBlockerCountThrough := by
  classical
  intro n
  by_cases hS : S gameF (n + 1)
  . right
    have hS' : S gameF (1 + n) := by
      simpa [Nat.add_comm] using hS
    simp only [gameFBlockerCountThrough, gameFBlockersThroughList]
    rw [List.range'_concat, List.filter_append, List.length_append]
    simp [hS']
  . left
    have hS' : Not (S gameF (1 + n)) := by
      simpa [Nat.add_comm] using hS
    simp only [gameFBlockerCountThrough, gameFBlockersThroughList]
    rw [List.range'_concat, List.filter_append, List.length_append]
    simp [hS']

/-- The actual midpoint coordinate used by the upper-rail argument. -/
noncomputable def actualBlockerMidpoint (v : Nat) : Nat :=
  countMidpoint gameFBlockerCountThrough v

theorem actualBlockerMidpoint_monotone :
    NatMonotone actualBlockerMidpoint := by
  intro a b hab
  exact blockerMidpoint_monotone_of_unitIncrement01
    gameFBlockerCountThrough_unitIncrement01 hab

theorem actualBlockerMidpoint_strict_after_two (v : Nat) :
    actualBlockerMidpoint v < actualBlockerMidpoint (v + 2) := by
  exact blockerMidpoint_strict_after_two
    gameFBlockerCountThrough_unitIncrement01 v

/-- Every strictly increasing enumeration of one actual midpoint fiber has
at most two elements. -/
theorem actualBlockerMidpoint_fiber_list_length_le_two
    {y : Nat} (xs : List Nat)
    (hpair : xs.Pairwise (fun a b => a < b))
    (hfiber : forall v, v ∈ xs -> actualBlockerMidpoint v = y) :
    xs.length <= 2 := by
  exact blockerMidpoint_fiber_list_length_le_two
    gameFBlockerCountThrough_unitIncrement01 xs hpair hfiber

/-- Unconditional all-`N` finite-cohort theorem for the actual game. -/
theorem actualBlockerMidpoint_middle_cohort_length_le
    {r K : Nat} (xs : List Nat)
    (hpair : xs.Pairwise (fun a b => a < b))
    (hcohort : forall v, v ∈ xs ->
      r - K < actualBlockerMidpoint v /\
        actualBlockerMidpoint v <= r + K) :
    xs.length <= 4 * K + 2 := by
  exact blockerMidpoint_middle_cohort_length_le
    gameFBlockerCountThrough_unitIncrement01 xs hpair hcohort

/-- The actual cohort is contained in a concrete finite prefix. -/
theorem actualBlockerMidpoint_index_lt_of_le
    {v R : Nat} (hupper : actualBlockerMidpoint v <= R) :
    v < 2 * R + 2 := by
  exact countMidpoint_index_lt_of_le hupper

/-- Canonical increasing enumeration of the complete actual middle cohort.
The range cutoff is complete by `actualBlockerMidpoint_index_lt_of_le`. -/
noncomputable def actualBlockerMiddleCohortList (r K : Nat) : List Nat := by
  classical
  exact (List.range (2 * (r + K) + 2)).filter (fun v =>
    decide (r - K < actualBlockerMidpoint v /\
      actualBlockerMidpoint v <= r + K))

theorem gameF_mem_actualBlockerMiddleCohortList
    {r K v : Nat} :
    v ∈ actualBlockerMiddleCohortList r K <->
      r - K < actualBlockerMidpoint v /\
        actualBlockerMidpoint v <= r + K := by
  classical
  simp only [actualBlockerMiddleCohortList, List.mem_filter,
    List.mem_range, decide_eq_true_eq]
  constructor
  . rintro ⟨_hv, hband⟩
    exact hband
  . intro hband
    exact ⟨actualBlockerMidpoint_index_lt_of_le hband.2, hband⟩

theorem actualBlockerMiddleCohortList_pairwise_lt (r K : Nat) :
    (actualBlockerMiddleCohortList r K).Pairwise
      (fun a b => a < b) := by
  classical
  unfold actualBlockerMiddleCohortList
  exact List.Pairwise.filter _ List.pairwise_lt_range

/-- Direct cardinal statement for the complete actual cohort, not merely an
arbitrary sub-enumeration. -/
theorem actualBlockerMiddleCohortList_length_le (r K : Nat) :
    (actualBlockerMiddleCohortList r K).length <= 4 * K + 2 := by
  apply actualBlockerMidpoint_middle_cohort_length_le
    (actualBlockerMiddleCohortList r K)
    (actualBlockerMiddleCohortList_pairwise_lt r K)
  intro v hv
  exact gameF_mem_actualBlockerMiddleCohortList.mp hv

/-- The concrete cardinal bound used by the audited `K = 10` dual stream. -/
theorem actualBlockerMiddleCohortList_length_le_10 (r : Nat) :
    (actualBlockerMiddleCohortList r 10).length <= 42 := by
  simpa using actualBlockerMiddleCohortList_length_le r 10

#print axioms gameFBlockerCountThrough_unitIncrement01
#print axioms actualBlockerMidpoint_monotone
#print axioms actualBlockerMidpoint_strict_after_two
#print axioms actualBlockerMidpoint_fiber_list_length_le_two
#print axioms actualBlockerMidpoint_middle_cohort_length_le
#print axioms actualBlockerMidpoint_index_lt_of_le
#print axioms gameF_mem_actualBlockerMiddleCohortList
#print axioms actualBlockerMiddleCohortList_length_le
#print axioms actualBlockerMiddleCohortList_length_le_10

end ChompLean
