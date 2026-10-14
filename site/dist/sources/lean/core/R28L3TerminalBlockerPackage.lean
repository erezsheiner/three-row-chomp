import PrefreezeHostDiagonalCriterion

set_option autoImplicit false

namespace ChompLean

/-!
R28 integration package for the length-three rescue.

R24 says that an unserved persistent value which is still missing at the
backstop comes with two witnesses: a strictly lower fresh loss `q`, and a
late row-start occurrence of the unpaid value `z`.  The exact row-hosting
criterion proved in `PrefreezeHostDiagonalCriterion` turns the second witness,
under RM2, into a host on the current rescue row.  Since the backstop source
does not contain `z`, that host must be one of the three terminal cells.

Thus the former "future-freeze" alternative is eliminated from the L=3
residual: the obstruction is entirely visible in the current top-three strip.
-/

/-- Full L=3 specialization of the R21--R24 residual, with the late blocker
localized to the three terminal cells of the current rescue row. -/
theorem l3_unserved_missing_backstop_is_lower_loss_plus_terminal_blocker
    (M : RecurrenceModel) {e u z : Nat}
    (hmexEntry :
      IsMex (B M.f (e + 6) e) (M.f (e + 6) e))
    (honeEntry :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B M.f (e + 6) e y) ->
        Not (B M.f (e + 6) e z) -> y = z)
    (hmexOne :
      IsMex (B M.f (e + 6) (e + 1))
        (M.f (e + 6) (e + 1)))
    (hmexTwo :
      IsMex (B M.f (e + 6) (e + 2))
        (M.f (e + 6) (e + 2)))
    (hEntryLossCapTwo :
      forall x y z,
        0 < x -> x < u -> 0 < y -> y < u -> 0 < z -> z < u ->
        B M.f (e + 6) e x ->
          Not (B M.f (e + 6) (e + 1) x) ->
        B M.f (e + 6) e y ->
          Not (B M.f (e + 6) (e + 1) y) ->
        B M.f (e + 6) e z ->
          Not (B M.f (e + 6) (e + 1) z) ->
        x = y \/ x = z \/ y = z)
    (hz : 0 < z) (hzu : z < u)
    (hzMissingOne : Not (B M.f (e + 6) (e + 1) z))
    (hzMissingTwo : Not (B M.f (e + 6) (e + 2) z))
    (hNotServed : M.f (e + 6) (e + 2) ≠ z)
    (huSeat : M.f (e + 5) (e + 4) = u)
    (hPrevDiagonalAbove : u < M.f (e + 4) (e + 4))
    (hzMissingBackstop : Not (B M.f (e + 6) (e + 3) z))
    (hRM2 : TwoStepDiagonalRecordLaw M) :
    let q := M.f (e + 6) (e + 2)
    0 < q /\ q < z /\
      B M.f (e + 6) (e + 1) q /\
      Not (B M.f (e + 6) (e + 2) q) /\
      B M.f (e + 6) (e + 3) q /\
      (exists b,
        (b = e + 3 \/ b = e + 4 \/ b = e + 5) /\
        M.f (e + 6) b = z) := by
  have hres :=
    rescue_unserved_missing_backstop_is_lower_loss_plus_late_blocker
      (M := M) (e := e) (L := 3) (by omega)
      hmexEntry honeEntry hmexOne hmexTwo hEntryLossCapTwo
      hz hzu hzMissingOne hzMissingTwo hNotServed
      huSeat hPrevDiagonalAbove hzMissingBackstop hRM2
  rcases hres with
    ⟨hqPos, hqz, hqBefore, hqLost, hqBackstop,
      r, hrLower, hrz, hstart⟩
  have hterminal :=
    rm2_missing_l3_backstop_rowstart_has_terminal_host
      M hPrevDiagonalAbove hzu hrz hstart hRM2 hzMissingBackstop
  exact ⟨hqPos, hqz, hqBefore, hqLost, hqBackstop, hterminal⟩

/-- Equivalent top-three-cell formulation: the unpaid value is exactly one
of the current row's `V3`, `V2`, or `V1` cells. -/
theorem l3_unserved_missing_backstop_hits_current_top_three
    (M : RecurrenceModel) {e u z : Nat}
    (hmexEntry :
      IsMex (B M.f (e + 6) e) (M.f (e + 6) e))
    (honeEntry :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B M.f (e + 6) e y) ->
        Not (B M.f (e + 6) e z) -> y = z)
    (hmexOne :
      IsMex (B M.f (e + 6) (e + 1))
        (M.f (e + 6) (e + 1)))
    (hmexTwo :
      IsMex (B M.f (e + 6) (e + 2))
        (M.f (e + 6) (e + 2)))
    (hEntryLossCapTwo :
      forall x y z,
        0 < x -> x < u -> 0 < y -> y < u -> 0 < z -> z < u ->
        B M.f (e + 6) e x ->
          Not (B M.f (e + 6) (e + 1) x) ->
        B M.f (e + 6) e y ->
          Not (B M.f (e + 6) (e + 1) y) ->
        B M.f (e + 6) e z ->
          Not (B M.f (e + 6) (e + 1) z) ->
        x = y \/ x = z \/ y = z)
    (hz : 0 < z) (hzu : z < u)
    (hzMissingOne : Not (B M.f (e + 6) (e + 1) z))
    (hzMissingTwo : Not (B M.f (e + 6) (e + 2) z))
    (hNotServed : M.f (e + 6) (e + 2) ≠ z)
    (huSeat : M.f (e + 5) (e + 4) = u)
    (hPrevDiagonalAbove : u < M.f (e + 4) (e + 4))
    (hzMissingBackstop : Not (B M.f (e + 6) (e + 3) z))
    (hRM2 : TwoStepDiagonalRecordLaw M) :
    let q := M.f (e + 6) (e + 2)
    0 < q /\ q < z /\
      B M.f (e + 6) (e + 1) q /\
      Not (B M.f (e + 6) (e + 2) q) /\
      B M.f (e + 6) (e + 3) q /\
      (M.f (e + 6) (e + 3) = z \/
       M.f (e + 6) (e + 4) = z \/
       M.f (e + 6) (e + 5) = z) := by
  have hres :=
    l3_unserved_missing_backstop_is_lower_loss_plus_terminal_blocker
      (M := M) hmexEntry honeEntry hmexOne hmexTwo hEntryLossCapTwo
      hz hzu hzMissingOne hzMissingTwo hNotServed
      huSeat hPrevDiagonalAbove hzMissingBackstop hRM2
  rcases hres with
    ⟨hqPos, hqz, hqBefore, hqLost, hqBackstop,
      b, hb, hvalue⟩
  have htop :
      M.f (e + 6) (e + 3) = z \/
      M.f (e + 6) (e + 4) = z \/
      M.f (e + 6) (e + 5) = z := by
    rcases hb with h3 | h4 | h5
    · simpa [h3] using Or.inl hvalue
    · exact Or.inr (Or.inl (by simpa [h4] using hvalue))
    · exact Or.inr (Or.inr (by simpa [h5] using hvalue))
  exact ⟨hqPos, hqz, hqBefore, hqLost, hqBackstop, htop⟩

end ChompLean
