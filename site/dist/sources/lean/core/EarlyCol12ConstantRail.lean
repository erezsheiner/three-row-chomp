import EarlyCol11AffineRail

set_option autoImplicit false

namespace ChompLean

/-!
# Constant column-twelve rail

The column-eleven affine rail will pin an R151 `a=q-4` burn to column
twelve.  This file certifies the paired constant rail `F(q,12)=17`.
-/

/-- `d(12)=21`. -/
theorem gameF_diag_twelve : gameF 12 12 = 21 := by
  apply gameF_value_of_source_mex (q := 12) (r := 12) (m := 21)
  · omega
  · omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/
          a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/
          a = 11 := by omega
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
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/
          b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/
          b = 11 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
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
      · rw [gameF_twelve_eleven] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/
        k = 18 \/ k = 19 \/ k = 20 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
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
    · exact Or.inr ⟨9, by omega, gameF_col9_rail (q := 12) (by omega)⟩
    · exact Or.inr ⟨11, by omega, gameF_twelve_eleven⟩
    · exact Or.inr ⟨10, by omega, gameF_twelve_ten⟩

/-- First post-diagonal column-twelve value. -/
theorem gameF_thirteen_twelve : gameF 13 12 = 23 := by
  apply gameF_value_of_source_mex (q := 13) (r := 12) (m := 23)
  · omega
  · rw [gameF_diag_twelve]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/
          a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/
          a = 11 \/ a = 12 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
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
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/
          b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/
          b = 11 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
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
      · rw [gameF_thirteen_eleven] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/
        k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨9, by omega, gameF_col9_rail (q := 13) (by omega)⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inl ⟨12, by omega, by simpa using gameF_diag_twelve⟩
    · exact Or.inr ⟨11, by omega, gameF_thirteen_eleven⟩

/-- Second exceptional column-twelve value. -/
theorem gameF_fourteen_twelve : gameF 14 12 = 22 := by
  apply gameF_value_of_source_mex (q := 14) (r := 12) (m := 22)
  · omega
  · rw [gameF_thirteen_twelve]
    omega
  · omega
  · rintro (⟨a, ha, hval⟩ | ⟨b, hb, hval⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/
          a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/
          a = 11 \/ a = 12 \/ a = 13 := by omega
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
      · simp [gameF_diag_twelve] at hval
      · simp [gameF_thirteen_twelve] at hval
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/
          b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/
          b = 11 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
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
      · rw [gameF_fourteen_eleven] at hval; omega
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/
        k = 18 \/ k = 19 \/ k = 20 \/ k = 21 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
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
    · exact Or.inr ⟨11, by omega, gameF_fourteen_eleven⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inr ⟨7, by omega, gameF_col7_rail (q := 14) (by omega)⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inl ⟨12, by omega, by simpa using gameF_diag_twelve⟩

/-- Third exceptional column-twelve value. -/
theorem gameF_fifteen_twelve : gameF 15 12 = 24 := by
  apply gameF_value_of_source_mex (q := 15) (r := 12) (m := 24)
  · omega
  · rw [gameF_fourteen_twelve]
    omega
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
      · simp [gameF_thirteen_twelve] at hval
      · simp [gameF_fourteen_twelve] at hval
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/
          b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/
          b = 11 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
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
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/
        k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
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
    · exact Or.inr ⟨2, by omega, gameF_col2_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨10, by omega, by simpa using gameF_diag_ten⟩
    · exact Or.inr ⟨5, by omega, gameF_col5_rail (q := 15) (by omega)⟩
    · exact Or.inl ⟨11, by omega, by simpa using gameF_diag_eleven⟩
    · exact Or.inl ⟨12, by omega, by simpa using gameF_diag_twelve⟩
    · exact Or.inl ⟨14, by omega, by simpa using gameF_fourteen_twelve⟩
    · exact Or.inl ⟨13, by omega, by simpa using gameF_thirteen_twelve⟩

/-- Penultimate value before the column-twelve freeze. -/
theorem gameF_sixteen_twelve : gameF 16 12 = 19 := by
  apply gameF_value_of_source_mex (q := 16) (r := 12) (m := 19)
  · omega
  · rw [gameF_fifteen_twelve]
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
      · simp [gameF_thirteen_twelve] at hval
      · simp [gameF_fourteen_twelve] at hval
      · simp [gameF_fifteen_twelve] at hval
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/
          b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/
          b = 11 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
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
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/
        k = 18 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

/-- Freeze cell for column twelve. -/
theorem gameF_seventeen_twelve : gameF 17 12 = 17 := by
  apply gameF_value_of_source_mex (q := 17) (r := 12) (m := 17)
  · omega
  · rw [gameF_sixteen_twelve]
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
      · simp [gameF_thirteen_twelve] at hval
      · simp [gameF_fourteen_twelve] at hval
      · simp [gameF_fifteen_twelve] at hval
      · simp [gameF_sixteen_twelve] at hval
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/
          b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/
          b = 11 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
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
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/
        k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/
        k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

/-- Constant column-twelve rail. -/
theorem gameF_col12_rail {q : Nat} (hq : 17 <= q) : gameF q 12 = 17 := by
  have hsmall : gameF 17 12 < 17 + 1 := by
    rw [gameF_seventeen_twelve]
    omega
  have hconst := constant_from gameRecurrenceModel
    (q := 17) (r := 12) (by omega) hsmall (q - 17)
  change gameF (17 + (q - 17)) 12 = gameF 17 12 at hconst
  have hsum : 17 + (q - 17) = q := by omega
  rw [hsum, gameF_seventeen_twelve] at hconst
  exact hconst

end ChompLean
