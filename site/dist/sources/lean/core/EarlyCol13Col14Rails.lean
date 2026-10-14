import EarlyCol12ConstantRail

set_option autoImplicit false

namespace ChompLean

/-!
# Column thirteen and fourteen rails

The finite MEX windows terminate in the constant rail `F(q,13)=19` and
the affine rail `F(q,14)=q+9`.
-/

/-! ## Column thirteen -/

/-- Exact finite cell F(13,13)=24. -/
theorem gameF_diag_thirteen : gameF 13 13 = 24 := by
  apply gameF_value_of_source_mex (q := 13) (r := 13) (m := 24)
  · omega
  · omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase :
        a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨
        a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨
        a = 12 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
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
      · simp [gameF_diag_eleven] at hval
      · simp [gameF_diag_twelve] at hval
    · have hcase :
        b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨
        b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨
        b = 12 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0 13] at hval; omega
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
      · rw [gameF_thirteen_eleven] at hval; omega
      · rw [gameF_thirteen_twelve] at hval; omega
  · intro k hkpos hklt
    have hcase :
        k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
        k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨
        k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨
        k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, by simpa using gameF_col1_rail (q := 13) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, by simpa using gameF_col3_rail (q := 13) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, by simpa using gameF_col4_rail (q := 13) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, by simpa using gameF_col6_rail (q := 13) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, by simpa using gameF_col8_rail (q := 13) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨0, by omega, by simpa using gameF_col0 13⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inr ⟨5, by omega, by simpa using gameF_col5_rail (q := 13) (by omega)⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inr ⟨9, by omega, by simpa using gameF_col9_rail (q := 13) (by omega)⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inl ⟨12, by omega, by simpa using gameF_diag_twelve⟩
    · exact Or.inr ⟨11, by omega, by simpa using gameF_thirteen_eleven⟩
    · exact Or.inr ⟨12, by omega, by simpa using gameF_thirteen_twelve⟩

/-- Exact finite cell F(14,13)=23. -/
theorem gameF_fourteen_thirteen : gameF 14 13 = 23 := by
  apply gameF_value_of_source_mex (q := 14) (r := 13) (m := 23)
  · omega
  · rw [gameF_diag_thirteen]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase :
        a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨
        a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨
        a = 12 ∨ a = 13 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
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
      · simp [gameF_diag_twelve] at hval
      · simp [gameF_diag_thirteen] at hval
    · have hcase :
        b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨
        b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨
        b = 12 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0 14] at hval; omega
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
      · rw [gameF_fourteen_eleven] at hval; omega
      · rw [gameF_fourteen_twelve] at hval; omega
  · intro k hkpos hklt
    have hcase :
        k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
        k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨
        k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨
        k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, by simpa using gameF_col1_rail (q := 14) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, by simpa using gameF_col3_rail (q := 14) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, by simpa using gameF_col4_rail (q := 14) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, by simpa using gameF_col6_rail (q := 14) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, by simpa using gameF_col8_rail (q := 14) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨10, by omega, by simpa using gameF_col10_rail (q := 14) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inr ⟨11, by omega, by simpa using gameF_fourteen_eleven⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inr ⟨7, by omega, by simpa using gameF_col7_rail (q := 14) (by omega)⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inl ⟨12, by omega, by simpa using gameF_diag_twelve⟩
    · exact Or.inr ⟨12, by omega, by simpa using gameF_fourteen_twelve⟩

/-- Exact finite cell F(15,13)=22. -/
theorem gameF_fifteen_thirteen : gameF 15 13 = 22 := by
  apply gameF_value_of_source_mex (q := 15) (r := 13) (m := 22)
  · omega
  · rw [gameF_fourteen_thirteen]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase :
        a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨
        a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨
        a = 12 ∨ a = 13 ∨ a = 14 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
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
      · simp [gameF_diag_twelve] at hval
      · simp [gameF_diag_thirteen] at hval
      · simp [gameF_fourteen_thirteen] at hval
    · have hcase :
        b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨
        b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨
        b = 12 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0 15] at hval; omega
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
      · rw [gameF_fifteen_eleven] at hval; omega
      · rw [gameF_fifteen_twelve] at hval; omega
  · intro k hkpos hklt
    have hcase :
        k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
        k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨
        k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨
        k = 19 ∨ k = 20 ∨ k = 21 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, by simpa using gameF_col1_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, by simpa using gameF_col3_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, by simpa using gameF_col4_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, by simpa using gameF_col6_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, by simpa using gameF_col8_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨10, by omega, by simpa using gameF_col10_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inr ⟨2, by omega, by simpa using gameF_col2_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inr ⟨5, by omega, by simpa using gameF_col5_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inl ⟨12, by omega, by simpa using gameF_diag_twelve⟩

/-- Exact finite cell F(16,13)=25. -/
theorem gameF_sixteen_thirteen : gameF 16 13 = 25 := by
  apply gameF_value_of_source_mex (q := 16) (r := 13) (m := 25)
  · omega
  · rw [gameF_fifteen_thirteen]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase :
        a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨
        a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨
        a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
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
      · simp [gameF_diag_twelve] at hval
      · simp [gameF_diag_thirteen] at hval
      · simp [gameF_fourteen_thirteen] at hval
      · simp [gameF_fifteen_thirteen] at hval
    · have hcase :
        b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨
        b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨
        b = 12 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0 16] at hval; omega
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
      · rw [gameF_sixteen_eleven] at hval; omega
      · rw [gameF_sixteen_twelve] at hval; omega
  · intro k hkpos hklt
    have hcase :
        k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
        k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨
        k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨
        k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, by simpa using gameF_col1_rail (q := 16) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, by simpa using gameF_col3_rail (q := 16) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, by simpa using gameF_col4_rail (q := 16) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, by simpa using gameF_col6_rail (q := 16) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, by simpa using gameF_col8_rail (q := 16) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨10, by omega, by simpa using gameF_col10_rail (q := 16) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inr ⟨0, by omega, by simpa using gameF_col0 16⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inr ⟨12, by omega, by simpa using gameF_sixteen_twelve⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inl ⟨12, by omega, by simpa using gameF_diag_twelve⟩
    · exact Or.inl ⟨15, by omega, by simpa using gameF_fifteen_thirteen⟩
    · exact Or.inl ⟨14, by omega, by simpa using gameF_fourteen_thirteen⟩
    · exact Or.inl ⟨13, by omega, by simpa using gameF_diag_thirteen⟩

/-- Exact finite cell F(17,13)=26. -/
theorem gameF_seventeen_thirteen : gameF 17 13 = 26 := by
  apply gameF_value_of_source_mex (q := 17) (r := 13) (m := 26)
  · omega
  · rw [gameF_sixteen_thirteen]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase :
        a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨
        a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨
        a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15 ∨ a = 16 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl
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
      · simp [gameF_diag_twelve] at hval
      · simp [gameF_diag_thirteen] at hval
      · simp [gameF_fourteen_thirteen] at hval
      · simp [gameF_fifteen_thirteen] at hval
      · simp [gameF_sixteen_thirteen] at hval
    · have hcase :
        b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨
        b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨
        b = 12 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0 17] at hval; omega
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
      · rw [gameF_seventeen_eleven] at hval; omega
      · rw [gameF_col12_rail (q := 17) (by omega)] at hval; omega
  · intro k hkpos hklt
    have hcase :
        k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
        k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨
        k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨
        k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨
        k = 25 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, by simpa using gameF_col1_rail (q := 17) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, by simpa using gameF_col3_rail (q := 17) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, by simpa using gameF_col4_rail (q := 17) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, by simpa using gameF_col6_rail (q := 17) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, by simpa using gameF_col8_rail (q := 17) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨10, by omega, by simpa using gameF_col10_rail (q := 17) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inr ⟨12, by omega, by simpa using gameF_col12_rail (q := 17) (by omega)⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inr ⟨2, by omega, by simpa using gameF_col2_rail (q := 17) (by omega)⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inl ⟨12, by omega, by simpa using gameF_diag_twelve⟩
    · exact Or.inl ⟨15, by omega, by simpa using gameF_fifteen_thirteen⟩
    · exact Or.inl ⟨14, by omega, by simpa using gameF_fourteen_thirteen⟩
    · exact Or.inl ⟨13, by omega, by simpa using gameF_diag_thirteen⟩
    · exact Or.inl ⟨16, by omega, by simpa using gameF_sixteen_thirteen⟩

/-- Exact finite cell F(18,13)=27. -/
theorem gameF_eighteen_thirteen : gameF 18 13 = 27 := by
  apply gameF_value_of_source_mex (q := 18) (r := 13) (m := 27)
  · omega
  · rw [gameF_seventeen_thirteen]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase :
        a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨
        a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨
        a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15 ∨ a = 16 ∨ a = 17 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl
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
      · simp [gameF_diag_twelve] at hval
      · simp [gameF_diag_thirteen] at hval
      · simp [gameF_fourteen_thirteen] at hval
      · simp [gameF_fifteen_thirteen] at hval
      · simp [gameF_sixteen_thirteen] at hval
      · simp [gameF_seventeen_thirteen] at hval
    · have hcase :
        b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨
        b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨
        b = 12 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0 18] at hval; omega
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
      · rw [gameF_eighteen_eleven] at hval; omega
      · rw [gameF_col12_rail (q := 18) (by omega)] at hval; omega
  · intro k hkpos hklt
    have hcase :
        k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
        k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨
        k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨
        k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨
        k = 25 ∨ k = 26 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, by simpa using gameF_col1_rail (q := 18) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, by simpa using gameF_col3_rail (q := 18) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, by simpa using gameF_col4_rail (q := 18) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, by simpa using gameF_col6_rail (q := 18) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, by simpa using gameF_col8_rail (q := 18) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨10, by omega, by simpa using gameF_col10_rail (q := 18) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inr ⟨12, by omega, by simpa using gameF_col12_rail (q := 18) (by omega)⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inr ⟨0, by omega, by simpa using gameF_col0 18⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inl ⟨12, by omega, by simpa using gameF_diag_twelve⟩
    · exact Or.inl ⟨15, by omega, by simpa using gameF_fifteen_thirteen⟩
    · exact Or.inl ⟨14, by omega, by simpa using gameF_fourteen_thirteen⟩
    · exact Or.inl ⟨13, by omega, by simpa using gameF_diag_thirteen⟩
    · exact Or.inl ⟨16, by omega, by simpa using gameF_sixteen_thirteen⟩
    · exact Or.inl ⟨17, by omega, by simpa using gameF_seventeen_thirteen⟩

/-- Exact finite cell F(19,13)=19. -/
theorem gameF_nineteen_thirteen : gameF 19 13 = 19 := by
  apply gameF_value_of_source_mex (q := 19) (r := 13) (m := 19)
  · omega
  · rw [gameF_eighteen_thirteen]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase :
        a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨
        a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨
        a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15 ∨ a = 16 ∨ a = 17 ∨
        a = 18 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl
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
      · simp [gameF_diag_twelve] at hval
      · simp [gameF_diag_thirteen] at hval
      · simp [gameF_fourteen_thirteen] at hval
      · simp [gameF_fifteen_thirteen] at hval
      · simp [gameF_sixteen_thirteen] at hval
      · simp [gameF_seventeen_thirteen] at hval
      · simp [gameF_eighteen_thirteen] at hval
    · have hcase :
        b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨
        b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨
        b = 12 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0 19] at hval; omega
      · rw [gameF_col1_rail (q := 19) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 19) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 19) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 19) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 19) (by omega)] at hval; omega
      · rw [gameF_col6_rail (q := 19) (by omega)] at hval; omega
      · rw [gameF_col7_rail (q := 19) (by omega)] at hval; omega
      · rw [gameF_col8_rail (q := 19) (by omega)] at hval; omega
      · rw [gameF_col9_rail (q := 19) (by omega)] at hval; omega
      · rw [gameF_col10_rail (q := 19) (by omega)] at hval; omega
      · rw [gameF_col11_rail (q := 19) (by omega)] at hval; omega
      · rw [gameF_col12_rail (q := 19) (by omega)] at hval; omega
  · intro k hkpos hklt
    have hcase :
        k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
        k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨
        k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, by simpa using gameF_col1_rail (q := 19) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, by simpa using gameF_col3_rail (q := 19) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, by simpa using gameF_col4_rail (q := 19) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, by simpa using gameF_col6_rail (q := 19) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, by simpa using gameF_col8_rail (q := 19) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨10, by omega, by simpa using gameF_col10_rail (q := 19) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inr ⟨12, by omega, by simpa using gameF_col12_rail (q := 19) (by omega)⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩

/-- Constant column-thirteen rail: F(q,13)=19 for q≥19. -/
theorem gameF_col13_rail {q : Nat} (hq : 19 ≤ q) : gameF q 13 = 19 := by
  have hsmall : gameF 19 13 < 19 + 1 := by rw [gameF_nineteen_thirteen]; omega
  have hconst := constant_from gameRecurrenceModel
    (q := 19) (r := 13) (by omega) hsmall (q - 19)
  change gameF (19 + (q - 19)) 13 = gameF 19 13 at hconst
  have hsum : 19 + (q - 19) = q := by omega
  rw [hsum, gameF_nineteen_thirteen] at hconst
  exact hconst



/-! ## Column fourteen -/

/-- Exact finite cell F(14,14)=25. -/
theorem gameF_diag_fourteen : gameF 14 14 = 25 := by
  apply gameF_value_of_source_mex (q := 14) (r := 14) (m := 25)
  · omega
  · omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase :
        a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨
        a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨
        a = 12 ∨ a = 13 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
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
      · simp [gameF_diag_twelve] at hval
      · simp [gameF_diag_thirteen] at hval
    · have hcase :
        b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨
        b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨
        b = 12 ∨ b = 13 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0 14] at hval; omega
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
      · rw [gameF_fourteen_eleven] at hval; omega
      · rw [gameF_fourteen_twelve] at hval; omega
      · rw [gameF_fourteen_thirteen] at hval; omega
  · intro k hkpos hklt
    have hcase :
        k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
        k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨
        k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨
        k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, by simpa using gameF_col1_rail (q := 14) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, by simpa using gameF_col3_rail (q := 14) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, by simpa using gameF_col4_rail (q := 14) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, by simpa using gameF_col6_rail (q := 14) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, by simpa using gameF_col8_rail (q := 14) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨10, by omega, by simpa using gameF_col10_rail (q := 14) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inr ⟨11, by omega, by simpa using gameF_fourteen_eleven⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inr ⟨7, by omega, by simpa using gameF_col7_rail (q := 14) (by omega)⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inl ⟨12, by omega, by simpa using gameF_diag_twelve⟩
    · exact Or.inr ⟨12, by omega, by simpa using gameF_fourteen_twelve⟩
    · exact Or.inr ⟨13, by omega, by simpa using gameF_fourteen_thirteen⟩
    · exact Or.inl ⟨13, by omega, by simpa using gameF_diag_thirteen⟩

/-- Exact finite cell F(15,14)=26. -/
theorem gameF_fifteen_fourteen : gameF 15 14 = 26 := by
  apply gameF_value_of_source_mex (q := 15) (r := 14) (m := 26)
  · omega
  · rw [gameF_diag_fourteen]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase :
        a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨
        a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨
        a = 12 ∨ a = 13 ∨ a = 14 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
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
      · simp [gameF_diag_twelve] at hval
      · simp [gameF_diag_thirteen] at hval
      · simp [gameF_diag_fourteen] at hval
    · have hcase :
        b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨
        b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨
        b = 12 ∨ b = 13 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0 15] at hval; omega
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
      · rw [gameF_fifteen_eleven] at hval; omega
      · rw [gameF_fifteen_twelve] at hval; omega
      · rw [gameF_fifteen_thirteen] at hval; omega
  · intro k hkpos hklt
    have hcase :
        k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
        k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨
        k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨
        k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨
        k = 25 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, by simpa using gameF_col1_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, by simpa using gameF_col3_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, by simpa using gameF_col4_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, by simpa using gameF_col6_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, by simpa using gameF_col8_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨10, by omega, by simpa using gameF_col10_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inr ⟨2, by omega, by simpa using gameF_col2_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inr ⟨5, by omega, by simpa using gameF_col5_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inl ⟨12, by omega, by simpa using gameF_diag_twelve⟩
    · exact Or.inr ⟨13, by omega, by simpa using gameF_fifteen_thirteen⟩
    · exact Or.inr ⟨11, by omega, by simpa using gameF_fifteen_eleven⟩
    · exact Or.inl ⟨13, by omega, by simpa using gameF_diag_thirteen⟩
    · exact Or.inl ⟨14, by omega, by simpa using gameF_diag_fourteen⟩

/-- Exact finite cell F(16,14)=23. -/
theorem gameF_sixteen_fourteen : gameF 16 14 = 23 := by
  apply gameF_value_of_source_mex (q := 16) (r := 14) (m := 23)
  · omega
  · rw [gameF_fifteen_fourteen]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase :
        a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨
        a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨
        a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
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
      · simp [gameF_diag_twelve] at hval
      · simp [gameF_diag_thirteen] at hval
      · simp [gameF_diag_fourteen] at hval
      · simp [gameF_fifteen_fourteen] at hval
    · have hcase :
        b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨
        b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨
        b = 12 ∨ b = 13 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0 16] at hval; omega
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
      · rw [gameF_sixteen_eleven] at hval; omega
      · rw [gameF_sixteen_twelve] at hval; omega
      · rw [gameF_sixteen_thirteen] at hval; omega
  · intro k hkpos hklt
    have hcase :
        k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
        k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨
        k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨
        k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, by simpa using gameF_col1_rail (q := 16) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, by simpa using gameF_col3_rail (q := 16) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, by simpa using gameF_col4_rail (q := 16) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, by simpa using gameF_col6_rail (q := 16) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, by simpa using gameF_col8_rail (q := 16) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨10, by omega, by simpa using gameF_col10_rail (q := 16) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inr ⟨0, by omega, by simpa using gameF_col0 16⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inr ⟨12, by omega, by simpa using gameF_sixteen_twelve⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inl ⟨12, by omega, by simpa using gameF_diag_twelve⟩
    · exact Or.inr ⟨9, by omega, by simpa using gameF_col9_rail (q := 16) (by omega)⟩

/-- Exact finite cell F(17,14)=27. -/
theorem gameF_seventeen_fourteen : gameF 17 14 = 27 := by
  apply gameF_value_of_source_mex (q := 17) (r := 14) (m := 27)
  · omega
  · rw [gameF_sixteen_fourteen]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase :
        a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨
        a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨
        a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15 ∨ a = 16 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl
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
      · simp [gameF_diag_twelve] at hval
      · simp [gameF_diag_thirteen] at hval
      · simp [gameF_diag_fourteen] at hval
      · simp [gameF_fifteen_fourteen] at hval
      · simp [gameF_sixteen_fourteen] at hval
    · have hcase :
        b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨
        b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨
        b = 12 ∨ b = 13 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0 17] at hval; omega
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
      · rw [gameF_seventeen_eleven] at hval; omega
      · rw [gameF_col12_rail (q := 17) (by omega)] at hval; omega
      · rw [gameF_seventeen_thirteen] at hval; omega
  · intro k hkpos hklt
    have hcase :
        k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
        k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨
        k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨
        k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨
        k = 25 ∨ k = 26 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, by simpa using gameF_col1_rail (q := 17) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, by simpa using gameF_col3_rail (q := 17) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, by simpa using gameF_col4_rail (q := 17) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, by simpa using gameF_col6_rail (q := 17) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, by simpa using gameF_col8_rail (q := 17) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨10, by omega, by simpa using gameF_col10_rail (q := 17) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inr ⟨12, by omega, by simpa using gameF_col12_rail (q := 17) (by omega)⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inr ⟨2, by omega, by simpa using gameF_col2_rail (q := 17) (by omega)⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inl ⟨12, by omega, by simpa using gameF_diag_twelve⟩
    · exact Or.inr ⟨7, by omega, by simpa using gameF_col7_rail (q := 17) (by omega)⟩
    · exact Or.inl ⟨16, by omega, by simpa using gameF_sixteen_fourteen⟩
    · exact Or.inl ⟨13, by omega, by simpa using gameF_diag_thirteen⟩
    · exact Or.inl ⟨14, by omega, by simpa using gameF_diag_fourteen⟩
    · exact Or.inl ⟨15, by omega, by simpa using gameF_fifteen_fourteen⟩

/-- Exact finite cell F(18,14)=28. -/
theorem gameF_eighteen_fourteen : gameF 18 14 = 28 := by
  apply gameF_value_of_source_mex (q := 18) (r := 14) (m := 28)
  · omega
  · rw [gameF_seventeen_fourteen]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase :
        a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨
        a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨
        a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15 ∨ a = 16 ∨ a = 17 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl
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
      · simp [gameF_diag_twelve] at hval
      · simp [gameF_diag_thirteen] at hval
      · simp [gameF_diag_fourteen] at hval
      · simp [gameF_fifteen_fourteen] at hval
      · simp [gameF_sixteen_fourteen] at hval
      · simp [gameF_seventeen_fourteen] at hval
    · have hcase :
        b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨
        b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨
        b = 12 ∨ b = 13 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0 18] at hval; omega
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
      · rw [gameF_eighteen_eleven] at hval; omega
      · rw [gameF_col12_rail (q := 18) (by omega)] at hval; omega
      · rw [gameF_eighteen_thirteen] at hval; omega
  · intro k hkpos hklt
    have hcase :
        k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
        k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨
        k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨
        k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨
        k = 25 ∨ k = 26 ∨ k = 27 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, by simpa using gameF_col1_rail (q := 18) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, by simpa using gameF_col3_rail (q := 18) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, by simpa using gameF_col4_rail (q := 18) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, by simpa using gameF_col6_rail (q := 18) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, by simpa using gameF_col8_rail (q := 18) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨10, by omega, by simpa using gameF_col10_rail (q := 18) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inr ⟨12, by omega, by simpa using gameF_col12_rail (q := 18) (by omega)⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inr ⟨0, by omega, by simpa using gameF_col0 18⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inl ⟨12, by omega, by simpa using gameF_diag_twelve⟩
    · exact Or.inr ⟨5, by omega, by simpa using gameF_col5_rail (q := 18) (by omega)⟩
    · exact Or.inl ⟨16, by omega, by simpa using gameF_sixteen_fourteen⟩
    · exact Or.inl ⟨13, by omega, by simpa using gameF_diag_thirteen⟩
    · exact Or.inl ⟨14, by omega, by simpa using gameF_diag_fourteen⟩
    · exact Or.inl ⟨15, by omega, by simpa using gameF_fifteen_fourteen⟩
    · exact Or.inl ⟨17, by omega, by simpa using gameF_seventeen_fourteen⟩

/-- Exact finite cell F(19,14)=22. -/
theorem gameF_nineteen_fourteen : gameF 19 14 = 22 := by
  apply gameF_value_of_source_mex (q := 19) (r := 14) (m := 22)
  · omega
  · rw [gameF_eighteen_fourteen]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase :
        a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨
        a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨
        a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15 ∨ a = 16 ∨ a = 17 ∨
        a = 18 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl
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
      · simp [gameF_diag_twelve] at hval
      · simp [gameF_diag_thirteen] at hval
      · simp [gameF_diag_fourteen] at hval
      · simp [gameF_fifteen_fourteen] at hval
      · simp [gameF_sixteen_fourteen] at hval
      · simp [gameF_seventeen_fourteen] at hval
      · simp [gameF_eighteen_fourteen] at hval
    · have hcase :
        b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨
        b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨
        b = 12 ∨ b = 13 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0 19] at hval; omega
      · rw [gameF_col1_rail (q := 19) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 19) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 19) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 19) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 19) (by omega)] at hval; omega
      · rw [gameF_col6_rail (q := 19) (by omega)] at hval; omega
      · rw [gameF_col7_rail (q := 19) (by omega)] at hval; omega
      · rw [gameF_col8_rail (q := 19) (by omega)] at hval; omega
      · rw [gameF_col9_rail (q := 19) (by omega)] at hval; omega
      · rw [gameF_col10_rail (q := 19) (by omega)] at hval; omega
      · rw [gameF_col11_rail (q := 19) (by omega)] at hval; omega
      · rw [gameF_col12_rail (q := 19) (by omega)] at hval; omega
      · rw [gameF_nineteen_thirteen] at hval; omega
  · intro k hkpos hklt
    have hcase :
        k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
        k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨
        k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨
        k = 19 ∨ k = 20 ∨ k = 21 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, by simpa using gameF_col1_rail (q := 19) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, by simpa using gameF_col3_rail (q := 19) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, by simpa using gameF_col4_rail (q := 19) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, by simpa using gameF_col6_rail (q := 19) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, by simpa using gameF_col8_rail (q := 19) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨10, by omega, by simpa using gameF_col10_rail (q := 19) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inr ⟨12, by omega, by simpa using gameF_col12_rail (q := 19) (by omega)⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inr ⟨13, by omega, by simpa using gameF_nineteen_thirteen⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inl ⟨12, by omega, by simpa using gameF_diag_twelve⟩

/-- Exact finite cell F(20,14)=29. -/
theorem gameF_twenty_fourteen : gameF 20 14 = 29 := by
  apply gameF_value_of_source_mex (q := 20) (r := 14) (m := 29)
  · omega
  · rw [gameF_nineteen_fourteen]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase :
        a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨
        a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨
        a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15 ∨ a = 16 ∨ a = 17 ∨
        a = 18 ∨ a = 19 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl
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
      · simp [gameF_diag_twelve] at hval
      · simp [gameF_diag_thirteen] at hval
      · simp [gameF_diag_fourteen] at hval
      · simp [gameF_fifteen_fourteen] at hval
      · simp [gameF_sixteen_fourteen] at hval
      · simp [gameF_seventeen_fourteen] at hval
      · simp [gameF_eighteen_fourteen] at hval
      · simp [gameF_nineteen_fourteen] at hval
    · have hcase :
        b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨
        b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨
        b = 12 ∨ b = 13 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0 20] at hval; omega
      · rw [gameF_col1_rail (q := 20) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 20) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 20) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 20) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 20) (by omega)] at hval; omega
      · rw [gameF_col6_rail (q := 20) (by omega)] at hval; omega
      · rw [gameF_col7_rail (q := 20) (by omega)] at hval; omega
      · rw [gameF_col8_rail (q := 20) (by omega)] at hval; omega
      · rw [gameF_col9_rail (q := 20) (by omega)] at hval; omega
      · rw [gameF_col10_rail (q := 20) (by omega)] at hval; omega
      · rw [gameF_col11_rail (q := 20) (by omega)] at hval; omega
      · rw [gameF_col12_rail (q := 20) (by omega)] at hval; omega
      · rw [gameF_col13_rail (q := 20) (by omega)] at hval; omega
  · intro k hkpos hklt
    have hcase :
        k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
        k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨
        k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨
        k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨
        k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, by simpa using gameF_col1_rail (q := 20) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, by simpa using gameF_col3_rail (q := 20) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, by simpa using gameF_col4_rail (q := 20) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, by simpa using gameF_col6_rail (q := 20) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, by simpa using gameF_col8_rail (q := 20) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨10, by omega, by simpa using gameF_col10_rail (q := 20) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inr ⟨12, by omega, by simpa using gameF_col12_rail (q := 20) (by omega)⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inr ⟨13, by omega, by simpa using gameF_col13_rail (q := 20) (by omega)⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inl ⟨12, by omega, by simpa using gameF_diag_twelve⟩
    · exact Or.inl ⟨19, by omega, by simpa using gameF_nineteen_fourteen⟩
    · exact Or.inl ⟨16, by omega, by simpa using gameF_sixteen_fourteen⟩
    · exact Or.inl ⟨13, by omega, by simpa using gameF_diag_thirteen⟩
    · exact Or.inl ⟨14, by omega, by simpa using gameF_diag_fourteen⟩
    · exact Or.inl ⟨15, by omega, by simpa using gameF_fifteen_fourteen⟩
    · exact Or.inl ⟨17, by omega, by simpa using gameF_seventeen_fourteen⟩
    · exact Or.inl ⟨18, by omega, by simpa using gameF_eighteen_fourteen⟩


/-- Affine column-fourteen rail: F(q,14)=q+9 for q≥20. -/
theorem gameF_col14_rail {q : Nat} (hq : 20 ≤ q) : gameF q 14 = q + 9 := by
  apply gameF_affine_fixed_column_of_source_frame
      (c := 14) (t := 20) (d := 9) (q := q) (by omega) (by omega)
  · rw [gameF_nineteen_fourteen]
    omega
  · intro a ha
    have hcase :
        a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨
        a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨
        a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15 ∨ a = 16 ∨ a = 17 ∨
        a = 18 ∨ a = 19 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
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
    · simp [gameF_diag_twelve]
    · simp [gameF_diag_thirteen]
    · simp [gameF_diag_fourteen]
    · simp [gameF_fifteen_fourteen]
    · simp [gameF_sixteen_fourteen]
    · simp [gameF_seventeen_fourteen]
    · simp [gameF_eighteen_fourteen]
    · simp [gameF_nineteen_fourteen]
  · intro row hrow b hb
    have hcase :
        b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨
        b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨
        b = 12 ∨ b = 13 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    · rw [gameF_col0 row]; omega
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
    · rw [gameF_col11_rail (q := row) (by omega)]; omega
    · rw [gameF_col12_rail (q := row) (by omega)]; omega
    · rw [gameF_col13_rail (q := row) (by omega)]; omega
  · intro row hrow k hkpos hklt
    have hcase :
        k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
        k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨
        k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨
        k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨
        k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, by simpa using gameF_col1_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, by simpa using gameF_col3_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, by simpa using gameF_col4_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, by simpa using gameF_col6_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, by simpa using gameF_col8_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨10, by omega, by simpa using gameF_col10_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inr ⟨12, by omega, by simpa using gameF_col12_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inr ⟨13, by omega, by simpa using gameF_col13_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inl ⟨12, by omega, by simpa using gameF_diag_twelve⟩
    · exact Or.inl ⟨19, by omega, by simpa using gameF_nineteen_fourteen⟩
    · exact Or.inl ⟨16, by omega, by simpa using gameF_sixteen_fourteen⟩
    · exact Or.inl ⟨13, by omega, by simpa using gameF_diag_thirteen⟩
    · exact Or.inl ⟨14, by omega, by simpa using gameF_diag_fourteen⟩
    · exact Or.inl ⟨15, by omega, by simpa using gameF_fifteen_fourteen⟩
    · exact Or.inl ⟨17, by omega, by simpa using gameF_seventeen_fourteen⟩
    · exact Or.inl ⟨18, by omega, by simpa using gameF_eighteen_fourteen⟩
  · exact hq


end ChompLean
