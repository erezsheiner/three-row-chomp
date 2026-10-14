import EarlyCol10ConstantRail

set_option autoImplicit false

namespace ChompLean

/-!
# Affine column-eleven rail

The finite start window is exposed cell by cell.  Its values are
`20,19,22,17,23,24,25,21` on rows `11,...,18`; from row 19 onward the
column is the affine rail `F(q,11)=q+7`.
-/

/-- `d(11)=20`. -/
theorem gameF_diag_eleven : gameF 11 11 = 20 := by
  apply gameF_value_of_source_mex (q := 11) (r := 11) (m := 20)
  · omega
  · omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨
          a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
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
      · simp [gameF_diag_ten] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨
          b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 11) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 11) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 11) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 11) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 11) (by omega)] at hval; omega
      · rw [gameF_col6_rail (q := 11) (by omega)] at hval; omega
      · rw [gameF_col7_rail (q := 11) (by omega)] at hval; omega
      · rw [gameF_eleven_eight] at hval; omega
      · rw [gameF_eleven_nine] at hval; omega
      · rw [gameF_eleven_ten] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
        k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨
        k = 18 ∨ k = 19 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨9, by omega, gameF_eleven_nine⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inr ⟨8, by omega, gameF_eleven_eight⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inr ⟨10, by omega, gameF_eleven_ten⟩

/-- First exceptional value after the diagonal in column eleven. -/
theorem gameF_twelve_eleven : gameF 12 11 = 19 := by
  apply gameF_value_of_source_mex (q := 12) (r := 11) (m := 19)
  · omega
  · rw [gameF_diag_eleven]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨
          a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
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
      · simp [gameF_diag_ten] at hval
      · simp [gameF_diag_eleven] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨
          b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 12) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 12) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 12) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 12) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 12) (by omega)] at hval; omega
      · rw [gameF_col6_rail (q := 12) (by omega)] at hval; omega
      · rw [gameF_col7_rail (q := 12) (by omega)] at hval; omega
      · rw [gameF_col8_rail (q := 12) (by omega)] at hval; omega
      · rw [gameF_col9_rail (q := 12) (by omega)] at hval; omega
      · rw [gameF_twelve_ten] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
        k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 12) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := 12) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, gameF_col4_rail (q := 12) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, gameF_col6_rail (q := 12) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, gameF_col8_rail (q := 12) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨2, by omega, gameF_col2_rail (q := 12) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inr ⟨7, by omega, gameF_col7_rail (q := 12) (by omega)⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩

/-- Second exceptional value in column eleven. -/
theorem gameF_thirteen_eleven : gameF 13 11 = 22 := by
  apply gameF_value_of_source_mex (q := 13) (r := 11) (m := 22)
  · omega
  · rw [gameF_twelve_eleven]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨
          a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨
          a = 11 ∨ a = 12 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · simp [gameF_diag_ten] at hval
      · simp [gameF_diag_eleven] at hval
      · simp [gameF_twelve_eleven] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨
          b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 13) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 13) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 13) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 13) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 13) (by omega)] at hval; omega
      · rw [gameF_col6_rail (q := 13) (by omega)] at hval; omega
      · rw [gameF_col7_rail (q := 13) (by omega)] at hval; omega
      · rw [gameF_col8_rail (q := 13) (by omega)] at hval; omega
      · rw [gameF_col9_rail (q := 13) (by omega)] at hval; omega
      · rw [gameF_thirteen_ten] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
        k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨
        k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 13) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := 13) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, gameF_col4_rail (q := 13) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, gameF_col6_rail (q := 13) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, gameF_col8_rail (q := 13) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨0, by omega, by simpa using gameF_col0 13⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inr ⟨5, by omega, gameF_col5_rail (q := 13) (by omega)⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inl ⟨12, by omega, gameF_twelve_eleven⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inr ⟨10, by omega, gameF_thirteen_ten⟩

/-- The low reset in the column-eleven start window. -/
theorem gameF_fourteen_eleven : gameF 14 11 = 17 := by
  apply gameF_value_of_source_mex (q := 14) (r := 11) (m := 17)
  · omega
  · rw [gameF_thirteen_eleven]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨
          a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨
          a = 11 ∨ a = 12 ∨ a = 13 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · simp [gameF_diag_ten] at hval
      · simp [gameF_diag_eleven] at hval
      · simp [gameF_twelve_eleven] at hval
      · simp [gameF_thirteen_eleven] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨
          b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 14) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 14) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 14) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 14) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 14) (by omega)] at hval; omega
      · rw [gameF_col6_rail (q := 14) (by omega)] at hval; omega
      · rw [gameF_col7_rail (q := 14) (by omega)] at hval; omega
      · rw [gameF_col8_rail (q := 14) (by omega)] at hval; omega
      · rw [gameF_col9_rail (q := 14) (by omega)] at hval; omega
      · rw [gameF_col10_rail (q := 14) (by omega)] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
        k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 14) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := 14) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, gameF_col4_rail (q := 14) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, gameF_col6_rail (q := 14) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, gameF_col8_rail (q := 14) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨10, by omega, gameF_col10_rail (q := 14) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩

/-- Return to the high run in column eleven. -/
theorem gameF_fifteen_eleven : gameF 15 11 = 23 := by
  apply gameF_value_of_source_mex (q := 15) (r := 11) (m := 23)
  · omega
  · rw [gameF_fourteen_eleven]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨
          a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨
          a = 11 ∨ a = 12 ∨ a = 13 ∨ a = 14 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · simp [gameF_diag_ten] at hval
      · simp [gameF_diag_eleven] at hval
      · simp [gameF_twelve_eleven] at hval
      · simp [gameF_thirteen_eleven] at hval
      · simp [gameF_fourteen_eleven] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨
          b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 15) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 15) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 15) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 15) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 15) (by omega)] at hval; omega
      · rw [gameF_col6_rail (q := 15) (by omega)] at hval; omega
      · rw [gameF_col7_rail (q := 15) (by omega)] at hval; omega
      · rw [gameF_col8_rail (q := 15) (by omega)] at hval; omega
      · rw [gameF_col9_rail (q := 15) (by omega)] at hval; omega
      · rw [gameF_col10_rail (q := 15) (by omega)] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
        k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨
        k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, gameF_col4_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, gameF_col6_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, gameF_col8_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨10, by omega, gameF_col10_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inl ⟨14, by omega, gameF_fourteen_eleven⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inl ⟨12, by omega, gameF_twelve_eleven⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inr ⟨9, by omega, gameF_col9_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨13, by omega, gameF_thirteen_eleven⟩

/-- Penultimate high run, first cell. -/
theorem gameF_sixteen_eleven : gameF 16 11 = 24 := by
  apply gameF_value_of_source_mex (q := 16) (r := 11) (m := 24)
  · omega
  · rw [gameF_fifteen_eleven]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨
          a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨
          a = 11 ∨ a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · simp [gameF_diag_ten] at hval
      · simp [gameF_diag_eleven] at hval
      · simp [gameF_twelve_eleven] at hval
      · simp [gameF_thirteen_eleven] at hval
      · simp [gameF_fourteen_eleven] at hval
      · simp [gameF_fifteen_eleven] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨
          b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 16) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 16) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 16) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 16) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 16) (by omega)] at hval; omega
      · rw [gameF_col6_rail (q := 16) (by omega)] at hval; omega
      · rw [gameF_col7_rail (q := 16) (by omega)] at hval; omega
      · rw [gameF_col8_rail (q := 16) (by omega)] at hval; omega
      · rw [gameF_col9_rail (q := 16) (by omega)] at hval; omega
      · rw [gameF_col10_rail (q := 16) (by omega)] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
        k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨
        k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 16) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := 16) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, gameF_col4_rail (q := 16) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, gameF_col6_rail (q := 16) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, gameF_col8_rail (q := 16) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨10, by omega, gameF_col10_rail (q := 16) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inl ⟨14, by omega, gameF_fourteen_eleven⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inl ⟨12, by omega, gameF_twelve_eleven⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inr ⟨7, by omega, gameF_col7_rail (q := 16) (by omega)⟩
    · exact Or.inl ⟨13, by omega, gameF_thirteen_eleven⟩
    · exact Or.inl ⟨15, by omega, gameF_fifteen_eleven⟩

/-- Penultimate high run, second cell. -/
theorem gameF_seventeen_eleven : gameF 17 11 = 25 := by
  apply gameF_value_of_source_mex (q := 17) (r := 11) (m := 25)
  · omega
  · rw [gameF_sixteen_eleven]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨
          a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨
          a = 11 ∨ a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15 ∨ a = 16 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · simp [gameF_diag_ten] at hval
      · simp [gameF_diag_eleven] at hval
      · simp [gameF_twelve_eleven] at hval
      · simp [gameF_thirteen_eleven] at hval
      · simp [gameF_fourteen_eleven] at hval
      · simp [gameF_fifteen_eleven] at hval
      · simp [gameF_sixteen_eleven] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨
          b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 17) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 17) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 17) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 17) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 17) (by omega)] at hval; omega
      · rw [gameF_col6_rail (q := 17) (by omega)] at hval; omega
      · rw [gameF_col7_rail (q := 17) (by omega)] at hval; omega
      · rw [gameF_col8_rail (q := 17) (by omega)] at hval; omega
      · rw [gameF_col9_rail (q := 17) (by omega)] at hval; omega
      · rw [gameF_col10_rail (q := 17) (by omega)] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
        k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨
        k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 17) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := 17) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, gameF_col4_rail (q := 17) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, gameF_col6_rail (q := 17) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, gameF_col8_rail (q := 17) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨10, by omega, gameF_col10_rail (q := 17) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inl ⟨14, by omega, gameF_fourteen_eleven⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inl ⟨12, by omega, gameF_twelve_eleven⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inr ⟨5, by omega, gameF_col5_rail (q := 17) (by omega)⟩
    · exact Or.inl ⟨13, by omega, gameF_thirteen_eleven⟩
    · exact Or.inl ⟨15, by omega, gameF_fifteen_eleven⟩
    · exact Or.inl ⟨16, by omega, gameF_sixteen_eleven⟩

/-- Final exceptional value before the affine column-eleven rail. -/
theorem gameF_eighteen_eleven : gameF 18 11 = 21 := by
  apply gameF_value_of_source_mex (q := 18) (r := 11) (m := 21)
  · omega
  · rw [gameF_seventeen_eleven]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨
          a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨
          a = 11 ∨ a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15 ∨ a = 16 ∨
          a = 17 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · simp [gameF_diag_ten] at hval
      · simp [gameF_diag_eleven] at hval
      · simp [gameF_twelve_eleven] at hval
      · simp [gameF_thirteen_eleven] at hval
      · simp [gameF_fourteen_eleven] at hval
      · simp [gameF_fifteen_eleven] at hval
      · simp [gameF_sixteen_eleven] at hval
      · simp [gameF_seventeen_eleven] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨
          b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 18) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 18) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 18) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 18) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 18) (by omega)] at hval; omega
      · rw [gameF_col6_rail (q := 18) (by omega)] at hval; omega
      · rw [gameF_col7_rail (q := 18) (by omega)] at hval; omega
      · rw [gameF_col8_rail (q := 18) (by omega)] at hval; omega
      · rw [gameF_col9_rail (q := 18) (by omega)] at hval; omega
      · rw [gameF_col10_rail (q := 18) (by omega)] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
        k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨
        k = 18 ∨ k = 19 ∨ k = 20 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 18) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := 18) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, gameF_col4_rail (q := 18) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, gameF_col6_rail (q := 18) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, gameF_col8_rail (q := 18) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨10, by omega, gameF_col10_rail (q := 18) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inl ⟨14, by omega, gameF_fourteen_eleven⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inl ⟨12, by omega, gameF_twelve_eleven⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩

/-- Affine column-eleven rail: `F(q,11)=q+7` from row nineteen onward. -/
theorem gameF_col11_rail {q : Nat} (hq : 19 ≤ q) : gameF q 11 = q + 7 := by
  apply gameF_affine_fixed_column_of_source_frame
      (c := 11) (t := 19) (d := 7) (q := q) (by omega) (by omega)
  · rw [gameF_eighteen_eleven]
    omega
  · intro a ha
    have hcase : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨
        a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨
        a = 11 ∨ a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15 ∨ a = 16 ∨
        a = 17 ∨ a = 18 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · simp [gameF_diag_ten]
    · simp [gameF_diag_eleven]
    · simp [gameF_twelve_eleven]
    · simp [gameF_thirteen_eleven]
    · simp [gameF_fourteen_eleven]
    · simp [gameF_fifteen_eleven]
    · simp [gameF_sixteen_eleven]
    · simp [gameF_seventeen_eleven]
    · simp [gameF_eighteen_eleven]
  · intro row hrow b hb
    have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨
        b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    · rw [gameF_col0]; omega
    · rw [gameF_col1_rail (q := row) (by omega)]; omega
    · rw [gameF_col2_rail (q := row) (by omega)]; omega
    · rw [gameF_col3_rail (q := row) (by omega)]; omega
    · rw [gameF_col4_rail (q := row) (by omega)]; omega
    · rw [gameF_col5_rail (q := row) (by omega)]; omega
    · rw [gameF_col6_rail (q := row) (by omega)]; omega
    · rw [gameF_col7_rail (q := row) (by omega)]; omega
    · rw [gameF_col8_rail (q := row) (by omega)]; omega
    · rw [gameF_col9_rail (q := row) (by omega)]; omega
    · rw [gameF_col10_rail (q := row) (by omega)]; omega
  · intro row hrow k hkpos hklt
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
        k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨
        k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨
        k = 24 ∨ k = 25 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨10, by omega, gameF_col10_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inl ⟨14, by omega, gameF_fourteen_eleven⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inl ⟨12, by omega, gameF_twelve_eleven⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inl ⟨18, by omega, gameF_eighteen_eleven⟩
    · exact Or.inl ⟨13, by omega, gameF_thirteen_eleven⟩
    · exact Or.inl ⟨15, by omega, gameF_fifteen_eleven⟩
    · exact Or.inl ⟨16, by omega, gameF_sixteen_eleven⟩
    · exact Or.inl ⟨17, by omega, gameF_seventeen_eleven⟩
  · exact hq

end ChompLean
