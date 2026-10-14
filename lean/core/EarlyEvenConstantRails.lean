import EarlyAffineRails

set_option autoImplicit false

namespace ChompLean

/-!
# Early constant rails in even columns

This file certifies the finite column-eight start window and then propagates
the freeze at `(12,8)` by the recurrence's constant branch.
-/

/-- `d(8)=15`. -/
theorem gameF_diag_eight : gameF 8 8 = 15 := by
  apply gameF_value_of_source_mex (q := 8) (r := 8) (m := 15)
  · omega
  · omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨
          a = 5 ∨ a = 6 ∨ a = 7 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [gameF_zero_zero] at hval
      · simp [gameF_one_one] at hval
      · simp [gameF_diag_two] at hval
      · simp [gameF_diag_three] at hval
      · simp [gameF_diag_four] at hval
      · simp [gameF_diag_five] at hval
      · simp [gameF_diag_six] at hval
      · simp [gameF_seven_seven] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨
          b = 5 ∨ b = 6 ∨ b = 7 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 8) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 8) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 8) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 8) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 8) (by omega)] at hval; omega
      · rw [gameF_eight_six] at hval; omega
      · rw [gameF_eight_seven] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
        k = 12 ∨ k = 13 ∨ k = 14 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 8) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := 8) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, gameF_col4_rail (q := 8) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨0, by omega, by simpa using gameF_col0 8⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨5, by omega, gameF_col5_rail (q := 8) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨7, by omega, gameF_eight_seven⟩

/-- First post-diagonal value in column eight. -/
theorem gameF_nine_eight : gameF 9 8 = 14 := by
  apply gameF_value_of_source_mex (q := 9) (r := 8) (m := 14)
  · omega
  · rw [gameF_diag_eight]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨
          a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 := by omega
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
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨
          b = 5 ∨ b = 6 ∨ b = 7 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 9) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 9) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 9) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 9) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 9) (by omega)] at hval; omega
      · rw [gameF_col6_rail (q := 9) (by omega)] at hval; omega
      · rw [gameF_nine_seven] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
        k = 12 ∨ k = 13 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 9) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := 9) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, gameF_col4_rail (q := 9) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, gameF_col6_rail (q := 9) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨7, by omega, gameF_nine_seven⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩

/-- Second post-diagonal value in column eight. -/
theorem gameF_ten_eight : gameF 10 8 = 16 := by
  apply gameF_value_of_source_mex (q := 10) (r := 8) (m := 16)
  · omega
  · rw [gameF_nine_eight]
    omega
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
      · simp [gameF_nine_eight] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨
          b = 5 ∨ b = 6 ∨ b = 7 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 10) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 10) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 10) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 10) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 10) (by omega)] at hval; omega
      · rw [gameF_col6_rail (q := 10) (by omega)] at hval; omega
      · rw [gameF_col7_rail (q := 10) (by omega)] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
        k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inl ⟨9, by omega, gameF_nine_eight⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩

/-- Last high value before the column-eight freeze. -/
theorem gameF_eleven_eight : gameF 11 8 = 17 := by
  apply gameF_value_of_source_mex (q := 11) (r := 8) (m := 17)
  · omega
  · rw [gameF_ten_eight]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨
          a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 := by omega
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
      · simp [gameF_nine_eight] at hval
      · simp [gameF_ten_eight] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨
          b = 5 ∨ b = 6 ∨ b = 7 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 11) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 11) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 11) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 11) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 11) (by omega)] at hval; omega
      · rw [gameF_col6_rail (q := 11) (by omega)] at hval; omega
      · rw [gameF_col7_rail (q := 11) (by omega)] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
        k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inl ⟨9, by omega, gameF_nine_eight⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨10, by omega, gameF_ten_eight⟩

/-- The freeze cell that starts the constant column-eight rail. -/
theorem gameF_twelve_eight : gameF 12 8 = 12 := by
  apply gameF_value_of_source_mex (q := 12) (r := 8) (m := 12)
  · omega
  · rw [gameF_eleven_eight]
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
      · simp [gameF_nine_eight] at hval
      · simp [gameF_ten_eight] at hval
      · simp [gameF_eleven_eight] at hval
    · have hcase : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨
          b = 5 ∨ b = 6 ∨ b = 7 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 12) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 12) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 12) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 12) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 12) (by omega)] at hval; omega
      · rw [gameF_col6_rail (q := 12) (by omega)] at hval; omega
      · rw [gameF_col7_rail (q := 12) (by omega)] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
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

/-- Constant column-eight rail: `F(q,8)=12` for every `q≥12`. -/
theorem gameF_col8_rail {q : Nat} (hq : 12 ≤ q) : gameF q 8 = 12 := by
  have hsmall : gameF 12 8 < 12 + 1 := by rw [gameF_twelve_eight]; omega
  have hconst := constant_from gameRecurrenceModel
    (q := 12) (r := 8) (by omega) hsmall (q - 12)
  change gameF (12 + (q - 12)) 8 = gameF 12 8 at hconst
  have hsum : 12 + (q - 12) = q := by omega
  rw [hsum, gameF_twelve_eight] at hconst
  exact hconst

end ChompLean

