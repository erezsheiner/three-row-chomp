import EarlyCol12ConstantRail
import R152Col9Lag6Collapse

set_option autoImplicit false

namespace ChompLean

/-!
# Direct removal of the `a=q-4` R151 burn

The column-eleven affine rail pins this burn to terminal column twelve;
the constant column-twelve rail then contradicts the actual target freeze.
-/

/-- The offset-seven burn row pins the terminal column to twelve. -/
theorem gameF_q_sub_four_terminal_burn_pins_twelve
    {q r : Nat}
    (hq : 23 <= q)
    (hra : r <= q - 4)
    (hburn : gameF (q - 4) (r - 1) = q + 3) :
    r = 12 := by
  have hrpos : 0 < r := by
    by_cases hr0 : r = 0
    · subst r
      rw [show 0 - 1 = 0 by omega, gameF_col0] at hburn
      omega
    · omega
  have hrow : 19 <= q - 4 := by omega
  have hrail := gameF_col11_rail (q := q - 4) hrow
  have hhost : gameF (q - 4) 11 = q + 3 := by
    rw [hrail]
    omega
  exact gameF_terminal_burn_column_of_same_row_host
    (a := q - 4) (r := r) (v := q + 3) (c := 11)
    hrpos hra (by omega) hburn hhost

/-- The actual target freeze makes the `a=q-4` burn impossible. -/
theorem gameF_no_q_sub_four_terminal_burn
    {q r : Nat}
    (hq : 23 <= q)
    (hra : r <= q - 4)
    (hstart : gameF (q + 3) r = q + 3)
    (hburn : gameF (q - 4) (r - 1) = q + 3) :
    False := by
  have hr : r = 12 :=
    gameF_q_sub_four_terminal_burn_pins_twelve hq hra hburn
  subst r
  have hfreeze := gameF_col12_rail (q := q + 3) (by omega)
  rw [hfreeze] at hstart
  omega

/-- The complete R151 first-failure normal form now starts at adaptive lag
eight: its terminal burn row satisfies `a <= q-5`. -/
theorem gameF_firstFailure_burn_ladder_pre_lag8_actual
    {q r g H : Nat}
    (hq : 23 <= q)
    (hrv : r < q + 3)
    (hstart : gameF (q + 3) r = q + 3)
    (howners : LowerOwnerCoveredBy (q + 3) g)
    (hfailure : g + 1 < r)
    (hinterior : 2 < g + 1)
    (hpreviewLe : H <= q)
    (hpreviewLeft : H <= g)
    (hpreview : gameF q H = q + 3) :
    exists a, r <= a /\ a < q - 4 /\
      gameF a (r - 1) = q + 3 /\
      (forall e, g < e -> e < r - 1 ->
        exists w, e < w /\ w < a /\ gameF w e = q + 3) /\
      (forall s, a < s -> s < q + 3 ->
        exists b, b <= g /\ gameF s b = q + 3) := by
  rcases gameF_firstFailure_burn_ladder_pre_lag6_actual
      (by omega) hrv hstart howners hfailure hinterior hpreviewLe
      hpreviewLeft hpreview with ⟨a, hra, haq, hburn, hband, htail⟩
  by_cases haearly : a < q - 4
  · exact ⟨a, hra, haearly, hburn, hband, htail⟩
  · have ha : a = q - 4 := by omega
    subst a
    exact False.elim
      (gameF_no_q_sub_four_terminal_burn hq hra hstart hburn)

#print axioms gameF_no_q_sub_four_terminal_burn
#print axioms gameF_firstFailure_burn_ladder_pre_lag8_actual

end ChompLean
