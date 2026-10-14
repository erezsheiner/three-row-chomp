import R56FirstHoleRetention
import R44FutureFirstGapTripleBackfillCharge

set_option autoImplicit false

namespace ChompLean

/-!
R56: ECHO-LEFT.

A diagonal value owned at row `a` can only be re-emitted on a later row in
a column strictly left of `a`.  Columns strictly right of `a` are excluded
by diagonal/general non-attack; the owner's own column is excluded by the
encoding theorem already banked in R44.
-/

/-- Every later echo of a game diagonal lies strictly left of its owner. -/
theorem gameF_past_diagonal_echo_strictly_left
    {a q r : Nat} (haq : a < q) (hrq : r <= q)
    (hvalue : gameF q r = gameF a a) :
    r < a := by
  apply Nat.lt_of_not_ge
  intro har
  by_cases hra : r = a
  · subst r
    exact (encoding_diagonal_value_not_reemitted_in_owner_column
      game_encodes haq) hvalue
  · have harStrict : a < r := by omega
    exact gameRecurrenceModel.diagonal_general_no_attack
      harStrict hrq hvalue.symm

/-- Equivalent exclusion form, convenient for source/ledger arguments. -/
theorem gameF_past_diagonal_not_echoed_at_or_right_of_owner
    {a q r : Nat} (haq : a < q) (har : a <= r) (hrq : r <= q) :
    gameF q r ≠ gameF a a := by
  intro hvalue
  have hleft := gameF_past_diagonal_echo_strictly_left haq hrq hvalue
  omega

#print axioms gameF_past_diagonal_echo_strictly_left
#print axioms gameF_past_diagonal_not_echoed_at_or_right_of_owner

end ChompLean
