import EarlyCol15ConstantRail
import R152Col11Lag7Collapse

set_option autoImplicit false

namespace ChompLean

/-!
# Skip the rigid lag-nine face while retaining adaptive lag eight

The first adaptive face `a=q-5` is deliberately left open.  The next face,
`a=q-6`, has target offset nine and is rigid again: column fourteen carries
the target, pins the terminal column to fifteen, and the frozen column-fifteen
rail contradicts the actual target freeze.
-/

/-- The offset-nine burn row pins the terminal column to fifteen. -/
theorem gameF_q_sub_six_terminal_burn_pins_fifteen
    {q r : Nat}
    (hq : 26 <= q)
    (hra : r <= q - 6)
    (hburn : gameF (q - 6) (r - 1) = q + 3) :
    r = 15 := by
  have hrpos : 0 < r := by
    by_cases hr0 : r = 0
    · subst r
      rw [show 0 - 1 = 0 by omega, gameF_col0] at hburn
      omega
    · omega
  have hrow : 20 <= q - 6 := by omega
  have hrail := gameF_col14_rail (q := q - 6) hrow
  have hhost : gameF (q - 6) 14 = q + 3 := by
    rw [hrail]
    omega
  exact gameF_terminal_burn_column_of_same_row_host
    (a := q - 6) (r := r) (v := q + 3) (c := 14)
    hrpos hra (by omega) hburn hhost

/-- The actual target freeze rules out the lag-nine face `a=q-6`. -/
theorem gameF_no_q_sub_six_terminal_burn
    {q r : Nat}
    (hq : 26 <= q)
    (hra : r <= q - 6)
    (hstart : gameF (q + 3) r = q + 3)
    (hburn : gameF (q - 6) (r - 1) = q + 3) :
    False := by
  have hr : r = 15 :=
    gameF_q_sub_six_terminal_burn_pins_fifteen hq hra hburn
  subst r
  have hfreeze := gameF_col15_rail (q := q + 3) (by omega)
  rw [hfreeze] at hstart
  omega

/-- Exact post-sieve normal form.  Adaptive lag eight remains an explicit
branch; if it does not occur, the witness jumps strictly past lag nine. -/
theorem gameF_firstFailure_burn_ladder_lag8_or_pre_lag10_actual
    {q r g H : Nat}
    (hq : 26 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hfailure : g + 1 < r)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3) :
    exists a, r <= a /\ (a = q - 5 \/ a < q - 6) /\
      gameF a (r - 1) = q + 3 /\
      (forall e, g < e -> e < r - 1 ->
        exists w, e < w /\ w < a /\ gameF w e = q + 3) /\
      (forall s, a < s -> s < q + 3 ->
        exists b, b <= g /\ gameF s b = q + 3) := by
  rcases gameF_firstFailure_burn_ladder_pre_lag8_actual
      (by omega) hrv hstart howners hfailure hinterior hpreviewLe
      hpreviewLeft hpreview with ⟨a, hra, haq, hburn, hband, htail⟩
  by_cases ha8 : a = q - 5
  · exact ⟨a, hra, Or.inl ha8, hburn, hband, htail⟩
  · by_cases ha9 : a = q - 6
    · subst a
      exact False.elim
        (gameF_no_q_sub_six_terminal_burn hq hra hstart hburn)
    · have haearly : a < q - 6 := by omega
      exact ⟨a, hra, Or.inr haearly, hburn, hband, htail⟩

#print axioms gameF_no_q_sub_six_terminal_burn
#print axioms gameF_firstFailure_burn_ladder_lag8_or_pre_lag10_actual

end ChompLean
