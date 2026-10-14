import R56TopTwoHoles
import R56VCatchGate

set_option autoImplicit false

namespace ChompLean

/-!
R56: unconditional first-hole retention for the actual game.

`R56TopTwoHoles` identifies `gameF (t+1) t` as the first positive hole of
the two-edge source.  In particular it is not an earlier diagonal value.
The row-weak V-catch gate from `R56VCatchGate` then applies even in the
borderline case where the first hole equals the row index.
-/

/-- The V1/first-hole value is not any earlier diagonal value. -/
theorem gameF_first_hole_not_past_diagonal (t : Nat) :
    forall a, a < t + 1 ->
      gameF a a ≠ gameF (t + 1) t := by
  intro a ha hEq
  have hholes := gameF_nextRow_top_two_positive_holes t
  have habsent : Not
      (TwoEdgeSigma gameF (t + 1) (gameF (t + 1) t)) :=
    hholes.1.2.1
  apply habsent
  exact Or.inl ⟨a, ha, hEq⟩

/-- Unconditional V-CATCH GATE for the actual first hole.  Every strict
prefix cell above V1 lies in a column which hosted V1 on an earlier row. -/
theorem gameF_first_hole_vCatch_gate (t : Nat) :
    forall b, b < t ->
      gameF (t + 1) t < gameF (t + 1) b ->
      PastHostColumn gameRecurrenceModel (t + 1)
        (gameF (t + 1) t) b := by
  apply vCatch_gate_at_V1_host gameRecurrenceModel (u := gameF (t + 1) t)
  · rfl
  · exact gameF_first_hole_not_past_diagonal t

/-- Unconditional first-hole form of the last-two-column age sentinel.
Only the explicit five-cell `deep` exclusion remains as a hypothesis. -/
theorem gameF_first_hole_last_two_columns_below
    {t : Nat} (ht : 2 <= t)
    (hdeep : DeepBeyondLastTwoColumnHistories gameRecurrenceModel t
      (gameF (t + 1) t)) :
    gameF (t + 1) (t - 1) < gameF (t + 1) t /\
    gameF (t + 1) (t - 2) < gameF (t + 1) t := by
  exact vCatch_at_V1_last_two_columns_below
    gameRecurrenceModel ht rfl
      (gameF_first_hole_not_past_diagonal t) hdeep

#print axioms gameF_first_hole_not_past_diagonal
#print axioms gameF_first_hole_vCatch_gate
#print axioms gameF_first_hole_last_two_columns_below

end ChompLean
