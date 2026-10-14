import R28L3TerminalBlockerPackage

set_option autoImplicit false

namespace ChompLean

/-!
R29: a terminal blocker is not merely present; in the genuine game it is
served by a MEX cell.

R28 localizes the unpaid blocker to one of the three terminal cells of the
current `L=3` rescue row.  The first lemma below removes the only possible
low/carry regime.  If the row-start value were strictly below the current
row, source absence would force its freeze strictly past the backstop.  The
three-cell geometry would then identify it with the preceding rescue seat,
contrary to `z<u`.

Consequently the terminal host has value at least the current row.  Such a
cell cannot be on the constant branch, whose carried value is strictly below
the row, so the Brouwer recurrence makes it a genuine MEX cell.  In
particular, its source contains every positive value below `z`.
-/

/-- A late blocker which is absent from the `L=3` backstop cannot lie below
the current row.  The only apparent strict-below configuration is
`r=e+4`, `z=e+5`, but that is exactly the rescue seat and contradicts
`z<u`. -/
theorem missing_l3_backstop_late_rowstart_is_at_least_current_row
    (M : RecurrenceModel) {e u z r : Nat}
    (huSeat : M.f (e + 5) (e + 4) = u)
    (hzu : z < u)
    (hrLower : e + 3 <= r) (hrz : r < z)
    (hstart : M.f z r = z)
    (hmissing : Not (B M.f (e + 6) (e + 3) z)) :
    e + 6 <= z := by
  by_cases htz : e + 6 <= z
  · exact htz
  have hzt : z < e + 6 := by omega
  have hrc : r ≠ e + 3 := by
    intro hre
    subst r
    apply hmissing
    left
    refine ⟨z, hzt, ?_⟩
    have hcz : e + 3 <= z := by omega
    simpa [Nat.min_eq_right hcz] using hstart
  have hrStrict : e + 3 < r := by omega
  have hrEq : r = e + 4 := by omega
  have hzEq : z = e + 5 := by omega
  rw [hrEq, hzEq] at hstart
  have huz : u = e + 5 := huSeat.symm.trans hstart
  omega

/-- Any recurrence cell whose output is at least its row is a MEX cell:
the constant branch could only copy a value strictly below the row. -/
theorem recurrence_host_at_least_row_is_mex
    {f : Nat -> Nat -> Nat} (hrec : BrouwerRecurrence f)
    {t b z : Nat} (hbt : b < t) (htz : t <= z)
    (hhost : f t b = z) :
    IsMex (B f t b) z := by
  rw [← hhost]
  apply hrec.2 (Nat.le_of_lt hbt)
  intro hcarry
  have heq := hrec.1 hcarry.1 hcarry.2
  rw [hhost] at heq
  omega

/-- Actual-game terminal-completion theorem.  Under RM2, a sub-`u` late
blocker missing from the `L=3` backstop is hosted by one of the three terminal
cells, and that host is a genuine MEX cell for `z`. -/
theorem gameF_rm2_missing_l3_backstop_late_blocker_has_terminal_mex
    {e u z r : Nat}
    (huSeat : gameF (e + 5) (e + 4) = u)
    (hPrevDiagonalAbove : u < gameF (e + 4) (e + 4))
    (hzu : z < u)
    (hrLower : e + 3 <= r) (hrz : r < z)
    (hstart : gameF z r = z)
    (hmissing : Not (B gameF (e + 6) (e + 3) z))
    (hRM2 : TwoStepDiagonalRecordLaw gameRecurrenceModel) :
    exists b,
      (b = e + 3 \/ b = e + 4 \/ b = e + 5) /\
      gameF (e + 6) b = z /\
      IsMex (B gameF (e + 6) b) z := by
  have hterminal :=
    rm2_missing_l3_backstop_rowstart_has_terminal_host
      gameRecurrenceModel hPrevDiagonalAbove hzu hrz hstart hRM2 hmissing
  rcases hterminal with ⟨b, hb, hhost⟩
  have hbt : b < e + 6 := by
    rcases hb with rfl | rfl | rfl <;> omega
  have htz : e + 6 <= z :=
    missing_l3_backstop_late_rowstart_is_at_least_current_row
      gameRecurrenceModel huSeat hzu hrLower hrz hstart hmissing
  have hrec : BrouwerRecurrence gameF :=
    recurrence_of_encoding_and_mex game_encodes game_complete
      (mex_branch_of_encoding_and_lower game_encodes game_complete
        game_lower_blocked)
  have hmex : IsMex (B gameF (e + 6) b) z :=
    recurrence_host_at_least_row_is_mex hrec hbt htz hhost
  exact ⟨b, hb, hhost, hmex⟩

/-- Explicit lower-completion consequence: at the terminal service column,
every positive value below the unpaid blocker is already in the source. -/
theorem gameF_rm2_missing_l3_backstop_late_blocker_completes_lower_prefix
    {e u z r : Nat}
    (huSeat : gameF (e + 5) (e + 4) = u)
    (hPrevDiagonalAbove : u < gameF (e + 4) (e + 4))
    (hzu : z < u)
    (hrLower : e + 3 <= r) (hrz : r < z)
    (hstart : gameF z r = z)
    (hmissing : Not (B gameF (e + 6) (e + 3) z))
    (hRM2 : TwoStepDiagonalRecordLaw gameRecurrenceModel) :
    exists b,
      (b = e + 3 \/ b = e + 4 \/ b = e + 5) /\
      gameF (e + 6) b = z /\
      forall v, 0 < v -> v < z -> B gameF (e + 6) b v := by
  rcases gameF_rm2_missing_l3_backstop_late_blocker_has_terminal_mex
      huSeat hPrevDiagonalAbove hzu hrLower hrz hstart hmissing hRM2 with
    ⟨b, hb, hhost, hmex⟩
  exact ⟨b, hb, hhost, hmex.2.2⟩

/-- Full actual-game `L=3` completion package.  Backstop absence already
rules out second-cell service, so no separate `hNotServed` assumption is
needed: if `gameF (e+6) (e+2) = z`, that cell itself is a `C`-witness in
the backstop source.  R21--R24 then supply the lower loss and late-blocker
witness, and the preceding theorem upgrades the terminal host to a MEX
cell. -/
theorem gameF_l3_missing_backstop_residual_has_terminal_mex
    {e u z : Nat}
    (hmexEntry :
      IsMex (B gameF (e + 6) e) (gameF (e + 6) e))
    (honeEntry :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B gameF (e + 6) e y) ->
        Not (B gameF (e + 6) e z) -> y = z)
    (hmexOne :
      IsMex (B gameF (e + 6) (e + 1))
        (gameF (e + 6) (e + 1)))
    (hmexTwo :
      IsMex (B gameF (e + 6) (e + 2))
        (gameF (e + 6) (e + 2)))
    (hEntryLossCapTwo :
      forall x y z,
        0 < x -> x < u -> 0 < y -> y < u -> 0 < z -> z < u ->
        B gameF (e + 6) e x ->
          Not (B gameF (e + 6) (e + 1) x) ->
        B gameF (e + 6) e y ->
          Not (B gameF (e + 6) (e + 1) y) ->
        B gameF (e + 6) e z ->
          Not (B gameF (e + 6) (e + 1) z) ->
        x = y \/ x = z \/ y = z)
    (hz : 0 < z) (hzu : z < u)
    (hzMissingOne : Not (B gameF (e + 6) (e + 1) z))
    (hzMissingTwo : Not (B gameF (e + 6) (e + 2) z))
    (huSeat : gameF (e + 5) (e + 4) = u)
    (hPrevDiagonalAbove : u < gameF (e + 4) (e + 4))
    (hzMissingBackstop : Not (B gameF (e + 6) (e + 3) z))
    (hRM2 : TwoStepDiagonalRecordLaw gameRecurrenceModel) :
    let q := gameF (e + 6) (e + 2)
    0 < q /\ q < z /\
      B gameF (e + 6) (e + 1) q /\
      Not (B gameF (e + 6) (e + 2) q) /\
      B gameF (e + 6) (e + 3) q /\
      exists b,
        (b = e + 3 \/ b = e + 4 \/ b = e + 5) /\
        gameF (e + 6) b = z /\
        IsMex (B gameF (e + 6) b) z /\
        forall v, 0 < v -> v < z -> B gameF (e + 6) b v := by
  have hNotServed : gameF (e + 6) (e + 2) ≠ z := by
    intro hserved
    apply hzMissingBackstop
    exact Or.inr ⟨e + 2, by omega, hserved⟩
  have hres :=
    rescue_unserved_missing_backstop_is_lower_loss_plus_late_blocker
      (M := gameRecurrenceModel) (e := e) (L := 3) (by omega)
      hmexEntry honeEntry hmexOne hmexTwo hEntryLossCapTwo
      hz hzu hzMissingOne hzMissingTwo hNotServed
      huSeat hPrevDiagonalAbove hzMissingBackstop hRM2
  rcases hres with
    ⟨hqPos, hqz, hqBefore, hqLost, hqBackstop,
      r, hrLower, hrz, hstart⟩
  rcases gameF_rm2_missing_l3_backstop_late_blocker_has_terminal_mex
      huSeat hPrevDiagonalAbove hzu hrLower hrz hstart
      hzMissingBackstop hRM2 with
    ⟨b, hb, hhost, hmex⟩
  exact ⟨hqPos, hqz, hqBefore, hqLost, hqBackstop,
    b, hb, hhost, hmex, hmex.2.2⟩

end ChompLean
