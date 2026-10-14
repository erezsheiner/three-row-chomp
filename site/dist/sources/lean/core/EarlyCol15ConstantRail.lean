import EarlyCol13Col14Rails

set_option autoImplicit false

namespace ChompLean

/-!
# Constant column-fifteen rail

This is the frozen partner of the affine column-fourteen rail.
-/

/-- `d(15)=27`. -/
theorem gameF_diag_fifteen : gameF 15 15 = 27 := by
  apply gameF_value_of_source_mex (q := 15) (r := 15) (m := 27)
  · omega
  · omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/
          a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/
          a = 11 \/ a = 12 \/ a = 13 \/ a = 14 := by omega
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
      · simp [gameF_diag_twelve] at hval
      · simp [gameF_diag_thirteen] at hval
      · simp [gameF_diag_fourteen] at hval
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/
          b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/
          b = 11 \/ b = 12 \/ b = 13 \/ b = 14 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · rw [gameF_fifteen_eleven] at hval; omega
      · rw [gameF_fifteen_twelve] at hval; omega
      · rw [gameF_fifteen_thirteen] at hval; omega
      · rw [gameF_fifteen_fourteen] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/
        k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/
        k = 24 \/ k = 25 \/ k = 26 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨2, by omega, gameF_col2_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inr ⟨5, by omega, gameF_col5_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inl ⟨12, by omega, by simpa using gameF_diag_twelve⟩
    · exact Or.inr ⟨13, by omega, gameF_fifteen_thirteen⟩
    · exact Or.inr ⟨11, by omega, gameF_fifteen_eleven⟩
    · exact Or.inl ⟨13, by omega, by simpa using gameF_diag_thirteen⟩
    · exact Or.inl ⟨14, by omega, by simpa using gameF_diag_fourteen⟩
    · exact Or.inr ⟨14, by omega, gameF_fifteen_fourteen⟩

/-- First post-diagonal column-fifteen value. -/
theorem gameF_sixteen_fifteen : gameF 16 15 = 26 := by
  apply gameF_value_of_source_mex (q := 16) (r := 15) (m := 26)
  · omega
  · rw [gameF_diag_fifteen]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/
          a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/
          a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 := by omega
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
      · simp [gameF_diag_twelve] at hval
      · simp [gameF_diag_thirteen] at hval
      · simp [gameF_diag_fourteen] at hval
      · simp [gameF_diag_fifteen] at hval
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/
          b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/
          b = 11 \/ b = 12 \/ b = 13 \/ b = 14 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · rw [gameF_sixteen_eleven] at hval; omega
      · rw [gameF_sixteen_twelve] at hval; omega
      · rw [gameF_sixteen_thirteen] at hval; omega
      · rw [gameF_sixteen_fourteen] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/
        k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/
        k = 24 \/ k = 25 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨0, by omega, by simpa using gameF_col0 16⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inr ⟨12, by omega, gameF_sixteen_twelve⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inl ⟨12, by omega, by simpa using gameF_diag_twelve⟩
    · exact Or.inr ⟨9, by omega, gameF_col9_rail (q := 16) (by omega)⟩
    · exact Or.inr ⟨14, by omega, gameF_sixteen_fourteen⟩
    · exact Or.inl ⟨13, by omega, by simpa using gameF_diag_thirteen⟩
    · exact Or.inl ⟨14, by omega, by simpa using gameF_diag_fourteen⟩

/-- Second column-fifteen window value. -/
theorem gameF_seventeen_fifteen : gameF 17 15 = 28 := by
  apply gameF_value_of_source_mex (q := 17) (r := 15) (m := 28)
  · omega
  · rw [gameF_sixteen_fifteen]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/
          a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/
          a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 := by omega
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
      · simp [gameF_diag_twelve] at hval
      · simp [gameF_diag_thirteen] at hval
      · simp [gameF_diag_fourteen] at hval
      · simp [gameF_diag_fifteen] at hval
      · simp [gameF_sixteen_fifteen] at hval
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/
          b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/
          b = 11 \/ b = 12 \/ b = 13 \/ b = 14 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · rw [gameF_seventeen_eleven] at hval; omega
      · rw [gameF_seventeen_twelve] at hval; omega
      · rw [gameF_seventeen_thirteen] at hval; omega
      · rw [gameF_seventeen_fourteen] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/
        k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/
        k = 24 \/ k = 25 \/ k = 26 \/ k = 27 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨12, by omega, gameF_seventeen_twelve⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inr ⟨2, by omega, gameF_col2_rail (q := 17) (by omega)⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inl ⟨12, by omega, by simpa using gameF_diag_twelve⟩
    · exact Or.inr ⟨7, by omega, gameF_col7_rail (q := 17) (by omega)⟩
    · exact Or.inr ⟨9, by omega, gameF_col9_rail (q := 17) (by omega)⟩
    · exact Or.inl ⟨13, by omega, by simpa using gameF_diag_thirteen⟩
    · exact Or.inl ⟨14, by omega, by simpa using gameF_diag_fourteen⟩
    · exact Or.inl ⟨16, by omega, by simpa using gameF_sixteen_fifteen⟩
    · exact Or.inl ⟨15, by omega, by simpa using gameF_diag_fifteen⟩

/-- Third column-fifteen window value. -/
theorem gameF_eighteen_fifteen : gameF 18 15 = 29 := by
  apply gameF_value_of_source_mex (q := 18) (r := 15) (m := 29)
  · omega
  · rw [gameF_seventeen_fifteen]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/
          a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/
          a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/
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
      · simp [gameF_diag_twelve] at hval
      · simp [gameF_diag_thirteen] at hval
      · simp [gameF_diag_fourteen] at hval
      · simp [gameF_diag_fifteen] at hval
      · simp [gameF_sixteen_fifteen] at hval
      · simp [gameF_seventeen_fifteen] at hval
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/
          b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/
          b = 11 \/ b = 12 \/ b = 13 \/ b = 14 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · rw [gameF_eighteen_eleven] at hval; omega
      · rw [gameF_col12_rail (q := 18) (by omega)] at hval; omega
      · rw [gameF_eighteen_thirteen] at hval; omega
      · rw [gameF_eighteen_fourteen] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/
        k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/
        k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨12, by omega, gameF_col12_rail (q := 18) (by omega)⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inr ⟨0, by omega, by simpa using gameF_col0 18⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inr ⟨11, by omega, gameF_eighteen_eleven⟩
    · exact Or.inr ⟨5, by omega, gameF_col5_rail (q := 18) (by omega)⟩
    · exact Or.inr ⟨7, by omega, gameF_col7_rail (q := 18) (by omega)⟩
    · exact Or.inl ⟨13, by omega, by simpa using gameF_diag_thirteen⟩
    · exact Or.inl ⟨14, by omega, by simpa using gameF_diag_fourteen⟩
    · exact Or.inl ⟨16, by omega, by simpa using gameF_sixteen_fifteen⟩
    · exact Or.inl ⟨15, by omega, by simpa using gameF_diag_fifteen⟩
    · exact Or.inl ⟨17, by omega, by simpa using gameF_seventeen_fifteen⟩

/-- Fourth column-fifteen window value. -/
theorem gameF_nineteen_fifteen : gameF 19 15 = 30 := by
  apply gameF_value_of_source_mex (q := 19) (r := 15) (m := 30)
  · omega
  · rw [gameF_eighteen_fifteen]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/
          a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/
          a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/
          a = 17 \/ a = 18 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
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
      · simp [gameF_diag_fifteen] at hval
      · simp [gameF_sixteen_fifteen] at hval
      · simp [gameF_seventeen_fifteen] at hval
      · simp [gameF_eighteen_fifteen] at hval
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/
          b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/
          b = 11 \/ b = 12 \/ b = 13 \/ b = 14 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
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
      · rw [gameF_col13_rail (q := 19) (by omega)] at hval; omega
      · rw [gameF_nineteen_fourteen] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/
        k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/
        k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 19) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := 19) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, gameF_col4_rail (q := 19) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, gameF_col6_rail (q := 19) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, gameF_col8_rail (q := 19) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨10, by omega, gameF_col10_rail (q := 19) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inr ⟨12, by omega, gameF_col12_rail (q := 19) (by omega)⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inr ⟨13, by omega, gameF_col13_rail (q := 19) (by omega)⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inl ⟨12, by omega, by simpa using gameF_diag_twelve⟩
    · exact Or.inr ⟨14, by omega, gameF_nineteen_fourteen⟩
    · exact Or.inr ⟨5, by omega, gameF_col5_rail (q := 19) (by omega)⟩
    · exact Or.inl ⟨13, by omega, by simpa using gameF_diag_thirteen⟩
    · exact Or.inl ⟨14, by omega, by simpa using gameF_diag_fourteen⟩
    · exact Or.inl ⟨16, by omega, by simpa using gameF_sixteen_fifteen⟩
    · exact Or.inl ⟨15, by omega, by simpa using gameF_diag_fifteen⟩
    · exact Or.inl ⟨17, by omega, by simpa using gameF_seventeen_fifteen⟩
    · exact Or.inl ⟨18, by omega, by simpa using gameF_eighteen_fifteen⟩

/-- The low notch in the column-fifteen start window. -/
theorem gameF_twenty_fifteen : gameF 20 15 = 23 := by
  apply gameF_value_of_source_mex (q := 20) (r := 15) (m := 23)
  · omega
  · rw [gameF_nineteen_fifteen]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/
          a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/
          a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/
          a = 17 \/ a = 18 \/ a = 19 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
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
      · simp [gameF_diag_fifteen] at hval
      · simp [gameF_sixteen_fifteen] at hval
      · simp [gameF_seventeen_fifteen] at hval
      · simp [gameF_eighteen_fifteen] at hval
      · simp [gameF_nineteen_fifteen] at hval
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/
          b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/
          b = 11 \/ b = 12 \/ b = 13 \/ b = 14 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
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
      · rw [gameF_twenty_fourteen] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/
        k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 20) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := 20) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, gameF_col4_rail (q := 20) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, gameF_col6_rail (q := 20) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, gameF_col8_rail (q := 20) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨10, by omega, gameF_col10_rail (q := 20) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inr ⟨12, by omega, gameF_col12_rail (q := 20) (by omega)⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inr ⟨13, by omega, gameF_col13_rail (q := 20) (by omega)⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inl ⟨12, by omega, by simpa using gameF_diag_twelve⟩
    · exact Or.inr ⟨2, by omega, gameF_col2_rail (q := 20) (by omega)⟩

/-- Last high value before the column-fifteen freeze. -/
theorem gameF_twentyone_fifteen : gameF 21 15 = 31 := by
  apply gameF_value_of_source_mex (q := 21) (r := 15) (m := 31)
  · omega
  · rw [gameF_twenty_fifteen]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/
          a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/
          a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/
          a = 17 \/ a = 18 \/ a = 19 \/ a = 20 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
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
      · simp [gameF_diag_fifteen] at hval
      · simp [gameF_sixteen_fifteen] at hval
      · simp [gameF_seventeen_fifteen] at hval
      · simp [gameF_eighteen_fifteen] at hval
      · simp [gameF_nineteen_fifteen] at hval
      · simp [gameF_twenty_fifteen] at hval
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/
          b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/
          b = 11 \/ b = 12 \/ b = 13 \/ b = 14 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 21) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 21) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 21) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 21) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 21) (by omega)] at hval; omega
      · rw [gameF_col6_rail (q := 21) (by omega)] at hval; omega
      · rw [gameF_col7_rail (q := 21) (by omega)] at hval; omega
      · rw [gameF_col8_rail (q := 21) (by omega)] at hval; omega
      · rw [gameF_col9_rail (q := 21) (by omega)] at hval; omega
      · rw [gameF_col10_rail (q := 21) (by omega)] at hval; omega
      · rw [gameF_col11_rail (q := 21) (by omega)] at hval; omega
      · rw [gameF_col12_rail (q := 21) (by omega)] at hval; omega
      · rw [gameF_col13_rail (q := 21) (by omega)] at hval; omega
      · rw [gameF_col14_rail (q := 21) (by omega)] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/
        k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/
        k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/
        k = 30 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 21) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := 21) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, gameF_col4_rail (q := 21) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, gameF_col6_rail (q := 21) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, gameF_col8_rail (q := 21) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨10, by omega, gameF_col10_rail (q := 21) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inr ⟨12, by omega, gameF_col12_rail (q := 21) (by omega)⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inr ⟨13, by omega, gameF_col13_rail (q := 21) (by omega)⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inl ⟨12, by omega, by simpa using gameF_diag_twelve⟩
    · exact Or.inr ⟨0, by omega, by simpa using gameF_col0 21⟩
    · exact Or.inl ⟨20, by omega, by simpa using gameF_twenty_fifteen⟩
    · exact Or.inl ⟨13, by omega, by simpa using gameF_diag_thirteen⟩
    · exact Or.inl ⟨14, by omega, by simpa using gameF_diag_fourteen⟩
    · exact Or.inl ⟨16, by omega, by simpa using gameF_sixteen_fifteen⟩
    · exact Or.inl ⟨15, by omega, by simpa using gameF_diag_fifteen⟩
    · exact Or.inl ⟨17, by omega, by simpa using gameF_seventeen_fifteen⟩
    · exact Or.inl ⟨18, by omega, by simpa using gameF_eighteen_fifteen⟩
    · exact Or.inl ⟨19, by omega, by simpa using gameF_nineteen_fifteen⟩

/-- Freeze cell for column fifteen. -/
theorem gameF_twentytwo_fifteen : gameF 22 15 = 22 := by
  apply gameF_value_of_source_mex (q := 22) (r := 15) (m := 22)
  · omega
  · rw [gameF_twentyone_fifteen]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/
          a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/
          a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/
          a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
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
      · simp [gameF_diag_thirteen] at hval
      · simp [gameF_diag_fourteen] at hval
      · simp [gameF_diag_fifteen] at hval
      · simp [gameF_sixteen_fifteen] at hval
      · simp [gameF_seventeen_fifteen] at hval
      · simp [gameF_eighteen_fifteen] at hval
      · simp [gameF_nineteen_fifteen] at hval
      · simp [gameF_twenty_fifteen] at hval
      · simp [gameF_twentyone_fifteen] at hval
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/
          b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/
          b = 11 \/ b = 12 \/ b = 13 \/ b = 14 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gameF_col0] at hval; omega
      · rw [gameF_col1_rail (q := 22) (by omega)] at hval; omega
      · rw [gameF_col2_rail (q := 22) (by omega)] at hval; omega
      · rw [gameF_col3_rail (q := 22) (by omega)] at hval; omega
      · rw [gameF_col4_rail (q := 22) (by omega)] at hval; omega
      · rw [gameF_col5_rail (q := 22) (by omega)] at hval; omega
      · rw [gameF_col6_rail (q := 22) (by omega)] at hval; omega
      · rw [gameF_col7_rail (q := 22) (by omega)] at hval; omega
      · rw [gameF_col8_rail (q := 22) (by omega)] at hval; omega
      · rw [gameF_col9_rail (q := 22) (by omega)] at hval; omega
      · rw [gameF_col10_rail (q := 22) (by omega)] at hval; omega
      · rw [gameF_col11_rail (q := 22) (by omega)] at hval; omega
      · rw [gameF_col12_rail (q := 22) (by omega)] at hval; omega
      · rw [gameF_col13_rail (q := 22) (by omega)] at hval; omega
      · rw [gameF_col14_rail (q := 22) (by omega)] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/
        k = 18 \/ k = 19 \/ k = 20 \/ k = 21 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa using gameF_zero_zero⟩
    · exact Or.inr ⟨1, by omega, gameF_col1_rail (q := 22) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa using gameF_one_one⟩
    · exact Or.inl ⟨2, by omega, by simpa using gameF_diag_two⟩
    · exact Or.inr ⟨3, by omega, gameF_col3_rail (q := 22) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa using gameF_diag_three⟩
    · exact Or.inr ⟨4, by omega, gameF_col4_rail (q := 22) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa using gameF_diag_four⟩
    · exact Or.inr ⟨6, by omega, gameF_col6_rail (q := 22) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa using gameF_diag_five⟩
    · exact Or.inl ⟨6, by omega, by simpa using gameF_diag_six⟩
    · exact Or.inr ⟨8, by omega, gameF_col8_rail (q := 22) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa using gameF_seven_seven⟩
    · exact Or.inr ⟨10, by omega, gameF_col10_rail (q := 22) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa using gameF_diag_eight⟩
    · exact Or.inl ⟨9, by omega, by simpa using gameF_diag_nine⟩
    · exact Or.inr ⟨12, by omega, gameF_col12_rail (q := 22) (by omega)⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inr ⟨13, by omega, gameF_col13_rail (q := 22) (by omega)⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inl ⟨12, by omega, by simpa using gameF_diag_twelve⟩

/-- Constant column-fifteen rail. -/
theorem gameF_col15_rail {q : Nat} (hq : 22 <= q) : gameF q 15 = 22 := by
  have hsmall : gameF 22 15 < 22 + 1 := by
    rw [gameF_twentytwo_fifteen]
    omega
  have hconst := constant_from gameRecurrenceModel
    (q := 22) (r := 15) (by omega) hsmall (q - 22)
  change gameF (22 + (q - 22)) 15 = gameF 22 15 at hconst
  have hsum : 22 + (q - 22) = q := by omega
  rw [hsum, gameF_twentytwo_fifteen] at hconst
  exact hconst

end ChompLean
