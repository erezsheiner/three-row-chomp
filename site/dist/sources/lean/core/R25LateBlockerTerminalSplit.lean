import R24LateBlockerResidual

set_option autoImplicit false

namespace ChompLean

/-!
R25: terminal service for the near part of the late-blocker residual.

R24 leaves a row start `f z r = z` with freeze column `r >= c`, where
the rescue backstop is `c` and the current row is `t=c+3`.  There are only
two genuinely different geometric regimes.

* If `r<t`, recurrence chronology forces the current row to emit `z`
  between columns `c` and `r`.  Thus one of the three terminal cells
  `c,c+1,c+2` serves it, and the completed-row source contains `z`.
* If `t<=r`, then necessarily `t<z`; this is a genuinely future freeze.
  Comparing it with R21's lower new MEX `q<z` gives a further honest split:
  either `r<q`, in which case `rowStartPropagation` supplies a certified
  left return in row `q`, or `q<=r`, the sole residual branch.

No service, capacity, or no-loss premise is assumed in this file's new
lemmas.  The last theorem merely feeds R24's proved late-blocker witness
and R21's proved `q<z` into this recurrence-theoretic split.
-/

/-- If a row-start value is missing just before column `c`, but its freeze
column lies between `c` and the current row, then the current row emits the
value at some column between `c` and the freeze.

Before row `z` this is `rowStartPropagation`; from row `z` onward it is the
constant branch.  Source absence is used only to exclude an emission
strictly left of `c`. -/
theorem missing_rowstart_freeze_before_current_has_terminal_emission
    (M : RecurrenceModel) {t c z r : Nat}
    (hcr : c <= r) (hrt : r < t)
    (hrz : r < z) (hstart : M.f z r = z)
    (hmissing : Not (B M.f t c z)) :
    exists b,
      c <= b /\ b <= r /\ b < t /\ M.f t b = z := by
  by_cases htz : t < z
  · rcases rowStartPropagation M hstart hrz hrt htz with
      ⟨b, hbr, hvalue⟩
    have hcb : c <= b := by
      by_cases hbc : b < c
      · exact False.elim (hmissing (Or.inr ⟨b, hbc, hvalue⟩))
      · omega
    exact ⟨b, hcb, Nat.le_of_lt hbr, Nat.lt_trans hbr hrt, hvalue⟩
  · have hzt : z <= t := Nat.le_of_not_gt htz
    have hsmall : M.f z r < z + 1 := by
      rw [hstart]
      omega
    have hconst := constant_from M hrz hsmall (t - z)
    have hsum : z + (t - z) = t := by omega
    have hcurrent : M.f t r = z := by
      simpa [hsum, hstart] using hconst
    exact ⟨r, hcr, Nat.le_refl _, hrt, hcurrent⟩

/-- The generic blocker dichotomy behind R25.  A missing late row start is
either still pre-freeze at the current row (`t<=r`), or it already has a
current-row host between the source column and its freeze column. -/
theorem missing_late_rowstart_prefreeze_or_current_host
    (M : RecurrenceModel) {t c z r : Nat}
    (hcr : c <= r) (hrz : r < z) (hstart : M.f z r = z)
    (hmissing : Not (B M.f t c z)) :
    t <= r \/
      exists b, c <= b /\ b <= r /\ b < t /\ M.f t b = z := by
  by_cases hrt : r < t
  · exact Or.inr
      (missing_rowstart_freeze_before_current_has_terminal_emission
        M hcr hrt hrz hstart hmissing)
  · exact Or.inl (by omega)

/-- In the rescue geometry `t=c+3`, every missing blocker with
`c<=r<t` is served by one of the three terminal cells.  In particular it
belongs to the source after the current row has been completed. -/
theorem near_late_blocker_is_served_in_terminal_three
    (M : RecurrenceModel) {c z r : Nat}
    (hcr : c <= r) (hrt : r < c + 3)
    (hrz : r < z) (hstart : M.f z r = z)
    (hmissing : Not (B M.f (c + 3) c z)) :
    (M.f (c + 3) c = z \/
      M.f (c + 3) (c + 1) = z \/
      M.f (c + 3) (c + 2) = z) /\
    B M.f (c + 3) (c + 3) z := by
  rcases missing_rowstart_freeze_before_current_has_terminal_emission
      M hcr hrt hrz hstart hmissing with
      ⟨b, hcb, hbr, hbt, hvalue⟩
  have hbCases : b = c \/ b = c + 1 \/ b = c + 2 := by omega
  have hservice :
      M.f (c + 3) c = z \/
        M.f (c + 3) (c + 1) = z \/
        M.f (c + 3) (c + 2) = z := by
    rcases hbCases with rfl | h
    · exact Or.inl hvalue
    · rcases h with rfl | rfl
      · exact Or.inr (Or.inl hvalue)
      · exact Or.inr (Or.inr hvalue)
  have hcompleted : B M.f (c + 3) (c + 3) z :=
    Or.inr ⟨b, hbt, hvalue⟩
  exact ⟨hservice, hcompleted⟩

/-- If the blocker is absent even after all three terminal cells, its
freeze is not merely at/after the backstop: it is at/after the current row.
This removes the entire finite strip `c,c+1,c+2` from the residual. -/
theorem missing_completed_rowstart_forces_future_freeze
    (M : RecurrenceModel) {c z r : Nat}
    (hcr : c <= r) (hrz : r < z) (hstart : M.f z r = z)
    (hmissingBackstop : Not (B M.f (c + 3) c z))
    (hmissingCompleted : Not (B M.f (c + 3) (c + 3) z)) :
    c + 3 <= r /\ c + 3 < z := by
  have hfuture : c + 3 <= r := by
    by_cases hrt : r < c + 3
    · exact False.elim (hmissingCompleted
        (near_late_blocker_is_served_in_terminal_three
          M hcr hrt hrz hstart hmissingBackstop).2)
    · omega
  exact ⟨hfuture, Nat.lt_of_le_of_lt hfuture hrz⟩

/-- Exact comparison with a lower value `q<z` (in R21, the newly emitted
second MEX).  A late blocker is in exactly one of three proof-relevant
regions:

1. its freeze is before the current row, hence a terminal cell serves it;
2. its freeze is after the current row but before `q`, hence `z` makes a
   certified left return in row `q`;
3. its freeze is at/after both the current row and `q`.

The third disjunct is the only branch not supplied with a return channel. -/
theorem missing_late_rowstart_terminal_or_q_left_return_or_beyond_q
    (M : RecurrenceModel) {c q z : Nat}
    (hqz : q < z)
    (hmissing : Not (B M.f (c + 3) c z))
    (hlate : exists r, c <= r /\ r < z /\ M.f z r = z) :
    ((M.f (c + 3) c = z \/
        M.f (c + 3) (c + 1) = z \/
        M.f (c + 3) (c + 2) = z) /\
      B M.f (c + 3) (c + 3) z) \/
    (exists r,
      c + 3 <= r /\ r < q /\ r < z /\ M.f z r = z /\
        C M.f q r z) \/
    (exists r,
      c + 3 <= r /\ q <= r /\ r < z /\ M.f z r = z) := by
  rcases hlate with ⟨r, hcr, hrz, hstart⟩
  by_cases hrt : r < c + 3
  · exact Or.inl
      (near_late_blocker_is_served_in_terminal_three
        M hcr hrt hrz hstart hmissing)
  · have hfuture : c + 3 <= r := by omega
    by_cases hrq : r < q
    · have hreturn : C M.f q r z :=
        rowStartPropagation M hstart hrz hrq hqz
      exact Or.inr (Or.inl
        ⟨r, hfuture, hrq, hrz, hstart, hreturn⟩)
    · have hqr : q <= r := by omega
      exact Or.inr (Or.inr ⟨r, hfuture, hqr, hrz, hstart⟩)

/-- Proof-facing R21--R25 package.  Under the same hypotheses as R24, an
unserved persistent debt produces the lower new loss `q`, which reaches the
backstop.  The unpaid blocker then has the exact terminal/left-return/hard
split above.  Thus the sole residual is a freeze satisfying
`max(c+3,q) <= r < z`; all other late blockers have an explicit service or
return certificate. -/
theorem rescue_unserved_late_blocker_terminal_split_of_rm2
    (M : RecurrenceModel) {e L u z : Nat}
    (hL : 3 <= L)
    (hmexEntry :
      IsMex (B M.f (e + L + 3) e) (M.f (e + L + 3) e))
    (honeEntry :
      forall y z, 0 < y -> y < u -> 0 < z -> z < u ->
        Not (B M.f (e + L + 3) e y) ->
        Not (B M.f (e + L + 3) e z) -> y = z)
    (hmexOne :
      IsMex (B M.f (e + L + 3) (e + 1))
        (M.f (e + L + 3) (e + 1)))
    (hmexTwo :
      IsMex (B M.f (e + L + 3) (e + 2))
        (M.f (e + L + 3) (e + 2)))
    (hEntryLossCapTwo :
      forall x y z,
        0 < x -> x < u -> 0 < y -> y < u -> 0 < z -> z < u ->
        B M.f (e + L + 3) e x ->
          Not (B M.f (e + L + 3) (e + 1) x) ->
        B M.f (e + L + 3) e y ->
          Not (B M.f (e + L + 3) (e + 1) y) ->
        B M.f (e + L + 3) e z ->
          Not (B M.f (e + L + 3) (e + 1) z) ->
        x = y \/ x = z \/ y = z)
    (hz : 0 < z) (hzu : z < u)
    (hzMissingOne : Not (B M.f (e + L + 3) (e + 1) z))
    (hzMissingTwo : Not (B M.f (e + L + 3) (e + 2) z))
    (hNotServed : M.f (e + L + 3) (e + 2) ≠ z)
    (huSeat : M.f (e + L + 2) (e + L + 1) = u)
    (hPrevDiagonalAbove : u < M.f (e + L + 1) (e + L + 1))
    (hzMissingBackstop : Not (B M.f (e + L + 3) (e + L) z))
    (hRM2 : TwoStepDiagonalRecordLaw M) :
    let q := M.f (e + L + 3) (e + 2)
    0 < q /\ q < z /\
      B M.f (e + L + 3) (e + 1) q /\
      Not (B M.f (e + L + 3) (e + 2) q) /\
      B M.f (e + L + 3) (e + L) q /\
      (((M.f (e + L + 3) (e + L) = z \/
          M.f (e + L + 3) (e + L + 1) = z \/
          M.f (e + L + 3) (e + L + 2) = z) /\
        B M.f (e + L + 3) (e + L + 3) z) \/
       (exists r,
          e + L + 3 <= r /\ r < q /\ r < z /\ M.f z r = z /\
            C M.f q r z) \/
       (exists r,
          e + L + 3 <= r /\ q <= r /\ r < z /\ M.f z r = z)) := by
  let q := M.f (e + L + 3) (e + 2)
  have hres := rescue_unserved_missing_backstop_is_lower_loss_plus_late_blocker
    M hL hmexEntry honeEntry hmexOne hmexTwo hEntryLossCapTwo
      hz hzu hzMissingOne hzMissingTwo hNotServed huSeat
      hPrevDiagonalAbove hzMissingBackstop hRM2
  dsimp only at hres
  rcases hres with
    ⟨hq, hqz, hqOne, hqMissingTwo, hqBackstop, hlate⟩
  have hsplit :=
    missing_late_rowstart_terminal_or_q_left_return_or_beyond_q
      M (c := e + L) (q := q) (z := z)
        hqz (by simpa [Nat.add_assoc] using hzMissingBackstop) hlate
  exact ⟨hq, hqz, hqOne, hqMissingTwo, hqBackstop, hsplit⟩

end ChompLean
