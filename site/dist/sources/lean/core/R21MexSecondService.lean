import R20MexQueueCapacity

set_option autoImplicit false

namespace ChompLean

/-!
R21: exact obstruction to serving a persistent entry debt in the second
post-entry MEX cell.

Under the R20 entry-loss cap, the first post-entry source has no hole
strictly between its MEX `m` and a persistent hole `z`.  Consequently, if
the next MEX is not `z`, it must be a genuinely new loss `q < z` created on
the intervening edge.  This replaces a broad no-mix premise by a directed
lower-loss premise.
-/

/-- With entry-loss capacity two, a persistent hole `z` and the first
post-entry MEX `m` exhaust the possible holes of the first post-entry source
below `z`: every other positive value below `z` is covered there. -/
theorem entry_cap_two_forces_mex_gap
    {f : Nat -> Nat -> Nat} {t e u z : Nat}
    (hmexEntry : IsMex (B f t e) (f t e))
    (honeEntry :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B f t e y) -> Not (B f t e z) -> y = z)
    (hmexOne : IsMex (B f t (e + 1)) (f t (e + 1)))
    (hEntryLossCapTwo :
      forall x y z,
        0 < x -> x < u -> 0 < y -> y < u -> 0 < z -> z < u ->
        B f t e x -> Not (B f t (e + 1) x) ->
        B f t e y -> Not (B f t (e + 1) y) ->
        B f t e z -> Not (B f t (e + 1) z) ->
        x = y \/ x = z \/ y = z)
    (hz : 0 < z) (hzu : z < u)
    (hzMissingOne : Not (B f t (e + 1) z))
    (hzMissingTwo : Not (B f t (e + 2) z)) :
    forall w, 0 < w -> w < z -> w ≠ f t (e + 1) ->
      B f t (e + 1) w := by
  intro w hw hwz hwm
  let m := f t (e + 1)
  have hpersist := persistent_hole_has_lower_mex_hole
    hmexOne hz hzMissingOne hzMissingTwo
  have hm : 0 < m := hmexOne.1
  have hmz : m < z := hpersist.1
  by_cases hwmOrder : w < m
  · exact hmexOne.2.2 w hw hwmOrder
  · have hmw : m < w := by
      have hmwLe : m <= w := Nat.le_of_not_gt hwmOrder
      omega
    have hwu : w < u := Nat.lt_trans hwz hzu
    by_cases hwCovered : B f t (e + 1) w
    · exact hwCovered
    · have hmu : m < u := Nat.lt_trans hmz hzu
      have hmEntry := successor_hole_was_entry_loss
        hmexEntry honeEntry hm hmu hmexOne.2.1
      have hwEntry := successor_hole_was_entry_loss
        hmexEntry honeEntry hw hwu hwCovered
      have hzEntry := successor_hole_was_entry_loss
        hmexEntry honeEntry hz hzu hzMissingOne
      rcases hEntryLossCapTwo m w z hm hmu hw hwu hz hzu
          hmEntry.1 hmEntry.2 hwEntry.1 hwEntry.2 hzEntry.1 hzEntry.2 with
          hmwEq | hmzEq | hwzEq
      · omega
      · omega
      · omega

/-- Exact obstruction theorem.  If the second post-entry MEX does not serve
the persistent hole `z`, that MEX is a strictly smaller value which was
covered at the preceding source and is newly lost at the next source. -/
theorem unserved_persistent_hole_forces_lower_new_loss
    {f : Nat -> Nat -> Nat} {t e u z : Nat}
    (hmexEntry : IsMex (B f t e) (f t e))
    (honeEntry :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B f t e y) -> Not (B f t e z) -> y = z)
    (hmexOne : IsMex (B f t (e + 1)) (f t (e + 1)))
    (hmexTwo : IsMex (B f t (e + 2)) (f t (e + 2)))
    (hEntryLossCapTwo :
      forall x y z,
        0 < x -> x < u -> 0 < y -> y < u -> 0 < z -> z < u ->
        B f t e x -> Not (B f t (e + 1) x) ->
        B f t e y -> Not (B f t (e + 1) y) ->
        B f t e z -> Not (B f t (e + 1) z) ->
        x = y \/ x = z \/ y = z)
    (hz : 0 < z) (hzu : z < u)
    (hzMissingOne : Not (B f t (e + 1) z))
    (hzMissingTwo : Not (B f t (e + 2) z))
    (hNotServed : f t (e + 2) ≠ z) :
    let q := f t (e + 2)
    0 < q /\ q < z /\ B f t (e + 1) q /\ Not (B f t (e + 2) q) := by
  let q := f t (e + 2)
  have hq : 0 < q := hmexTwo.1
  have hqMissing : Not (B f t (e + 2) q) := hmexTwo.2.1
  have hqz : q < z := by
    rcases Nat.lt_trichotomy q z with h | h | h
    · exact h
    · exact False.elim (hNotServed h)
    · exact False.elim (hzMissingTwo (hmexTwo.2.2 z hz h))
  have hpersist := persistent_hole_has_lower_mex_hole
    hmexOne hz hzMissingOne hzMissingTwo
  have hqm : q ≠ f t (e + 1) := by
    intro h
    apply hqMissing
    simpa [h] using hpersist.2.2
  have hqCovered := entry_cap_two_forces_mex_gap
    hmexEntry honeEntry hmexOne hEntryLossCapTwo
    hz hzu hzMissingOne hzMissingTwo q hq hqz hqm
  exact ⟨hq, hqz, hqCovered, hqMissing⟩

/-- Directed replacement for a broad no-mix law: it is enough to know that
the edge creates no new loss below the persistent value.  Then the second
MEX serves that value, and the fresh row-prefix channel covers it at the
following source. -/
theorem persistent_hole_second_service_of_no_lower_new_loss
    {f : Nat -> Nat -> Nat} {t e u z : Nat}
    (hmexEntry : IsMex (B f t e) (f t e))
    (honeEntry :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B f t e y) -> Not (B f t e z) -> y = z)
    (hmexOne : IsMex (B f t (e + 1)) (f t (e + 1)))
    (hmexTwo : IsMex (B f t (e + 2)) (f t (e + 2)))
    (hEntryLossCapTwo :
      forall x y z,
        0 < x -> x < u -> 0 < y -> y < u -> 0 < z -> z < u ->
        B f t e x -> Not (B f t (e + 1) x) ->
        B f t e y -> Not (B f t (e + 1) y) ->
        B f t e z -> Not (B f t (e + 1) z) ->
        x = y \/ x = z \/ y = z)
    (hz : 0 < z) (hzu : z < u)
    (hzMissingOne : Not (B f t (e + 1) z))
    (hzMissingTwo : Not (B f t (e + 2) z))
    (hNoLowerNewLoss :
      forall q, 0 < q -> q < z ->
        B f t (e + 1) q -> B f t (e + 2) q) :
    f t (e + 2) = z /\ B f t (e + 3) z := by
  have hserved : f t (e + 2) = z := by
    by_cases h : f t (e + 2) = z
    · exact h
    · have hobs := unserved_persistent_hole_forces_lower_new_loss
        hmexEntry honeEntry hmexOne hmexTwo hEntryLossCapTwo
        hz hzu hzMissingOne hzMissingTwo h
      exact False.elim (hobs.2.2.2 (hNoLowerNewLoss
        (f t (e + 2)) hobs.1 hobs.2.1 hobs.2.2.1))
  have hcovered : B f t (e + 3) z := by
    simpa [Nat.add_assoc] using
      (fresh_emission_closes_next (e := e + 2) hserved)
  exact ⟨hserved, hcovered⟩

end ChompLean
