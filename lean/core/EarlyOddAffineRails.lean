import EarlyEvenConstantRails

set_option autoImplicit false

namespace ChompLean

/-!
# Odd affine rails after column seven

Column eight supplies the last permanent low value needed to start the
column-nine affine tail.
-/

/-- `d(9)=16`. -/
theorem gameF_diag_nine : gameF 9 9 = 16 := by
  apply gameF_value_of_source_mex (q := 9) (r := 9) (m := 16)
  · omega
  · omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/
          a = 5 \/ a = 6 \/ a = 7 \/ a = 8 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [gameF_zero_zero] at hval
      · simp [gameF_one_one] at hval
      · simp [gameF_diag_two] at hval
      · simp [gameF_diag_three] at hval
      · simp [gameF_diag_four] at hval
      · simp [gameF_diag_five] at hval
      · simp [gameF_diag_six] at hval
      · simp [gameF_seven_seven] at hval
      · simp [gameF_diag_eight] at hval
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/
          b = 5 \/ b = 6 \/ b = 7 \/ b = 8 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 9) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 9) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 9) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 9) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 9) (by omega)] at hval; omega
      · rw [gameF_col6_rail (q := 9) (by omega)] at hval; omega
      · rw [gameF_nine_seven] at hval; omega
      · rw [gameF_nine_eight] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 \/ k = 15 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 9) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := 9) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, gameF_col4_rail (q := 9) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, gameF_nine_six⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨7, by omega, gameF_nine_seven⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨8, by omega, gameF_nine_eight⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩

/-- The first post-diagonal entry in the column-nine start window. -/
theorem gameF_ten_nine : gameF 10 9 = 17 := by
  apply gameF_value_of_source_mex (q := 10) (r := 9) (m := 17)
  · omega
  · rw [gameF_diag_nine]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/
          a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [gameF_zero_zero] at hval
      · simp [gameF_one_one] at hval
      · simp [gameF_diag_two] at hval
      · simp [gameF_diag_three] at hval
      · simp [gameF_diag_four] at hval
      · simp [gameF_diag_five] at hval
      · simp [gameF_diag_six] at hval
      · simp [gameF_seven_seven] at hval
      · simp [gameF_diag_eight] at hval
      · simp [gameF_diag_nine] at hval
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/
          b = 5 \/ b = 6 \/ b = 7 \/ b = 8 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 10) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 10) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 10) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 10) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 10) (by omega)] at hval; omega
      · rw [gameF_col6_rail (q := 10) (by omega)] at hval; omega
      · rw [gameF_col7_rail (q := 10) (by omega)] at hval; omega
      · rw [gameF_ten_eight] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 10) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := 10) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, gameF_col4_rail (q := 10) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, gameF_col6_rail (q := 10) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inr ⟨0, by omega, by simpa using gameF_col0 10⟩
    · exact Or.inr ⟨2, by omega, gameF_col2_rail (q := 10) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨5, by omega, gameF_col5_rail (q := 10) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inr ⟨8, by omega, gameF_ten_eight⟩

/-- The final exceptional value before the column-nine affine tail. -/
theorem gameF_eleven_nine : gameF 11 9 = 14 := by
  apply gameF_value_of_source_mex (q := 11) (r := 9) (m := 14)
  · omega
  · rw [gameF_ten_nine]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/
          a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [gameF_zero_zero] at hval
      · simp [gameF_one_one] at hval
      · simp [gameF_diag_two] at hval
      · simp [gameF_diag_three] at hval
      · simp [gameF_diag_four] at hval
      · simp [gameF_diag_five] at hval
      · simp [gameF_diag_six] at hval
      · simp [gameF_seven_seven] at hval
      · simp [gameF_diag_eight] at hval
      · simp [gameF_diag_nine] at hval
      · simp [gameF_ten_nine] at hval
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/
          b = 5 \/ b = 6 \/ b = 7 \/ b = 8 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 11) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 11) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 11) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 11) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 11) (by omega)] at hval; omega
      · rw [gameF_col6_rail (q := 11) (by omega)] at hval; omega
      · rw [gameF_col7_rail (q := 11) (by omega)] at hval; omega
      · rw [gameF_eleven_eight] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 11) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := 11) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, gameF_col4_rail (q := 11) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, gameF_col6_rail (q := 11) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨0, by omega, by simpa using gameF_col0 11⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩

/-- Affine column-nine rail: `F(q,9)=q+6` from row twelve onward. -/
theorem gameF_col9_rail {q : Nat} (hq : 12 <= q) : gameF q 9 = q + 6 := by
  apply gameF_affine_fixed_column_of_source_frame
      (c := 9) (t := 12) (d := 6) (q := q) (by omega) (by omega)
  · rw [gameF_eleven_nine]
    omega
  · intro a ha
    have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/
        a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [gameF_zero_zero]
    · simp [gameF_one_one]
    · simp [gameF_diag_two]
    · simp [gameF_diag_three]
    · simp [gameF_diag_four]
    · simp [gameF_diag_five]
    · simp [gameF_diag_six]
    · simp [gameF_seven_seven]
    · simp [gameF_diag_eight]
    · simp [gameF_diag_nine]
    · simp [gameF_ten_nine]
    · simp [gameF_eleven_nine]
  · intro row hrow b hb
    have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/
        b = 5 \/ b = 6 \/ b = 7 \/ b = 8 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [gameF_col0]; omega
    · rw [gameF_col1_rail (q := row) (by omega)]; omega
    · rw [gameF_col2_rail (q := row) (by omega)]; omega
    · rw [gameF_col3_rail (q := row) (by omega)]; omega
    · rw [gameF_col4_rail (q := row) (by omega)]; omega
    · rw [gameF_col5_rail (q := row) (by omega)]; omega
    · rw [gameF_col6_rail (q := row) (by omega)]; omega
    · rw [gameF_col7_rail (q := row) (by omega)]; omega
    · rw [gameF_col8_rail (q := row) (by omega)]; omega
  · intro row hrow k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, gameF_col4_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, gameF_col6_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, gameF_col8_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_eleven_nine⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_ten_nine⟩
  · exact hq

/-! ## Burn-row consequences -/

/-- The column-eight freeze immediately contradicts the target freeze after
the column-seven rail has pinned a burn on `a=q-2` to `r=8`.  This removes
the lag-five R151 burn without any midpoint hypothesis. -/
theorem gameF_no_q_sub_two_terminal_burn
    {q r : Nat}
    (hq : 12 <= q)
    (hra : r <= q - 2)
    (hstart : gameF (q + 3) r = q + 3)
    (hburn : gameF (q - 2) (r - 1) = q + 3) :
    False := by
  have hr : r = 8 :=
    gameF_q_sub_two_terminal_burn_pins_eight hq hra hburn
  subst r
  have hfreeze := gameF_col8_rail (q := q + 3) (by omega)
  rw [hfreeze] at hstart
  omega

/-- A burn on `a=q-3` has offset six, so the column-nine rail pins `r=10`. -/
theorem gameF_q_sub_three_terminal_burn_pins_ten
    {q r : Nat}
    (hq : 15 <= q)
    (hra : r <= q - 3)
    (hburn : gameF (q - 3) (r - 1) = q + 3) :
    r = 10 := by
  have hrpos : 0 < r := by
    by_cases hr0 : r = 0
    · subst r
      rw [show 0 - 1 = 0 by omega, gameF_col0] at hburn
      omega
    · omega
  have hrow : 12 <= q - 3 := by omega
  have hrail := gameF_col9_rail (q := q - 3) hrow
  have hhost : gameF (q - 3) 9 = q + 3 := by
    rw [hrail]
    omega
  exact gameF_terminal_burn_column_of_same_row_host
    (a := q - 3) (r := r) (v := q + 3) (c := 9)
    hrpos hra (by omega) hburn hhost

/-- Even before the column-ten freeze is imported, the midpoint lower bound
and strict failure exclude the `a=q-3` burn. -/
theorem gameF_no_q_sub_three_terminal_burn_of_midpoint
    {q r g : Nat}
    (hq : 15 <= q)
    (hra : r <= q - 3)
    (hfailure : g + 1 < r)
    (hmid : q + 2 <= 2 * g)
    (hburn : gameF (q - 3) (r - 1) = q + 3) :
    False := by
  have hr : r = 10 :=
    gameF_q_sub_three_terminal_burn_pins_ten hq hra hburn
  omega

end ChompLean
