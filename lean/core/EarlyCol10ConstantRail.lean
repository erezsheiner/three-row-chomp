import EarlyOddAffineRails

set_option autoImplicit false

namespace ChompLean

/-!
# Constant column-ten rail

Finite MEX chain: `d(10)=18`, then column-ten values
`19,20,21,14`; the last value propagates forever by the constant branch.
-/

/-- `d(10)=18`. -/
theorem gameF_diag_ten : gameF 10 10 = 18 := by
  apply gameF_value_of_source_mex (q := 10) (r := 10) (m := 18)
  · omega
  · omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨
          a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 := by omega
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
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨
          b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 10) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 10) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 10) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 10) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 10) (by omega)] at hval; omega
      · rw [gameF_col6_rail (q := 10) (by omega)] at hval; omega
      · rw [gameF_col7_rail (q := 10) (by omega)] at hval; omega
      · rw [gameF_ten_eight] at hval; omega
      · rw [gameF_ten_nine] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
        k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨2, by omega, gameF_col2_rail (q := 10) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨5, by omega, gameF_col5_rail (q := 10) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inr ⟨9, by omega, gameF_ten_nine⟩

/-- First post-diagonal value in column ten. -/
theorem gameF_eleven_ten : gameF 11 10 = 19 := by
  apply gameF_value_of_source_mex (q := 11) (r := 10) (m := 19)
  · omega
  · rw [gameF_diag_ten]
    omega
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
          b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · intro k hkpos hklt
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
        k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

/-- Second high value in column ten. -/
theorem gameF_twelve_ten : gameF 12 10 = 20 := by
  apply gameF_value_of_source_mex (q := 12) (r := 10) (m := 20)
  · omega
  · rw [gameF_eleven_ten]
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
      · simp [gameF_eleven_ten] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨
          b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · intro k hkpos hklt
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
        k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨
        k = 18 ∨ k = 19 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inl ⟨11, by omega, gameF_eleven_ten⟩

/-- Final high value before the column-ten freeze. -/
theorem gameF_thirteen_ten : gameF 13 10 = 21 := by
  apply gameF_value_of_source_mex (q := 13) (r := 10) (m := 21)
  · omega
  · rw [gameF_twelve_ten]
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
      · simp [gameF_eleven_ten] at hval
      · simp [gameF_twelve_ten] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨
          b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · intro k hkpos hklt
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
        k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨
        k = 18 ∨ k = 19 ∨ k = 20 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inl ⟨11, by omega, gameF_eleven_ten⟩
    · exact Or.inl ⟨12, by omega, gameF_twelve_ten⟩

/-- The freeze cell that starts the constant column-ten rail. -/
theorem gameF_fourteen_ten : gameF 14 10 = 14 := by
  apply gameF_value_of_source_mex (q := 14) (r := 10) (m := 14)
  · omega
  · rw [gameF_thirteen_ten]
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
      · simp [gameF_eleven_ten] at hval
      · simp [gameF_twelve_ten] at hval
      · simp [gameF_thirteen_ten] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨
          b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · intro k hkpos hklt
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
        k = 12 ∨ k = 13 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
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

/-- Constant column-ten rail: `F(q,10)=14` for every `q≥14`. -/
theorem gameF_col10_rail {q : Nat} (hq : 14 ≤ q) : gameF q 10 = 14 := by
  have hsmall : gameF 14 10 < 14 + 1 := by rw [gameF_fourteen_ten]; omega
  have hconst := constant_from gameRecurrenceModel
    (q := 14) (r := 10) (by omega) hsmall (q - 14)
  change gameF (14 + (q - 14)) 10 = gameF 14 10 at hconst
  have hsum : 14 + (q - 14) = q := by omega
  rw [hsum, gameF_fourteen_ten] at hconst
  exact hconst

end ChompLean
