import EarlyCol10ConstantRail
import R152Col5Lag4Collapse

set_option autoImplicit false

namespace ChompLean

/-!
# Direct removal of the `a=q-3` R151 burn

The affine column-nine rail hosts the target `q+3` on row `q-3`, so
fixed-row injectivity pins the terminal freeze column to ten.  The
constant column-ten rail then contradicts the actual target freeze.
-/

/-- The terminal burn on row `q-3` is impossible in an actual target
freeze frame.  The exact threshold is `q >= 15`, which is precisely what
is needed to place row `q-3` on the column-nine affine tail. -/
theorem gameF_no_q_sub_three_terminal_burn
    {q r : Nat}
    (hq : 15 <= q)
    (hra : r <= q - 3)
    (hstart : gameF (q + 3) r = q + 3)
    (hburn : gameF (q - 3) (r - 1) = q + 3) :
    False := by
  have hr : r = 10 :=
    gameF_q_sub_three_terminal_burn_pins_ten hq hra hburn
  subst r
  have hfreeze := gameF_col10_rail (q := q + 3) (by omega)
  rw [hfreeze] at hstart
  omega

/-- Combining the column-five, column-seven, and column-nine rail pairs
pushes the first-failure terminal burn strictly before row `q-3`, with no
midpoint assumption. -/
theorem gameF_firstFailure_burn_ladder_pre_lag6_actual
    {q r g H : Nat}
    (hq : 15 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hfailure : g + 1 < r)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3) :
    exists a, r <= a /\ a < q - 3 /\
      gameF a (r - 1) = q + 3 /\
      (forall e, g < e -> e < r - 1 ->
        exists w, e < w /\ w < a /\ gameF w e = q + 3) /\
      (forall s, a < s -> s < q + 3 ->
        exists b, b <= g /\ gameF s b = q + 3) := by
  rcases gameF_firstFailure_burn_ladder_normal_form
      (by omega) hrv hstart howners hfailure hinterior hpreviewLe
      hpreviewLeft hpreview with ⟨a, hra, haq, hburn, hband, htail⟩
  by_cases haearly : a < q - 3
  · exact ⟨a, hra, haearly, hburn, hband, htail⟩
  · have hcases : a = q - 3 \/ a = q - 2 \/ a = q - 1 := by omega
    rcases hcases with ha3 | ha2 | ha1
    · subst a
      exact False.elim
        (gameF_no_q_sub_three_terminal_burn hq hra hstart hburn)
    · subst a
      exact False.elim
        (gameF_no_q_sub_two_terminal_burn (by omega) hra hstart hburn)
    · subst a
      exact False.elim
        (gameF_no_lag4_blocker_terminal (by omega) hra hstart hburn)

#print axioms gameF_no_q_sub_three_terminal_burn
#print axioms gameF_firstFailure_burn_ladder_pre_lag6_actual

end ChompLean
