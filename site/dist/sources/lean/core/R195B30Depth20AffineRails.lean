import EarlyCol16Col17Rails

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unnecessarySimpa false

namespace ChompLean

/-!
# R195 B30: completion of the depth-twenty affine rail schedule

All finite cells below are proved directly from the positive-MEX recurrence.
The external cache was used only to discover the expected numerals; it is not
a premise of any theorem in this file.
-/

attribute [local simp]
  gameF_col0 gameF_col1_rail gameF_col2_rail gameF_col3_rail
  gameF_col4_rail gameF_col5_rail gameF_col6_rail gameF_col7_rail
  gameF_col8_rail gameF_col9_rail gameF_col10_rail gameF_col11_rail
  gameF_col12_rail gameF_col13_rail gameF_col14_rail gameF_col15_rail
  gameF_col16_rail gameF_col17_rail gameF_col18_rail gameF_col19_rail
  gameF_col20_rail gameF_col21_rail gameF_col22_rail gameF_col23_rail
  gameF_col24_rail
  gameF_zero_zero gameF_one_one gameF_diag_two gameF_diag_three
  gameF_diag_four gameF_diag_five gameF_diag_six gameF_seven_seven
  gameF_diag_eight gameF_diag_nine gameF_diag_ten gameF_diag_eleven
  gameF_diag_twelve gameF_diag_thirteen gameF_diag_fourteen
  gameF_diag_fifteen

/-! ## Column 25 -/

@[simp] theorem r195_gameF_25_25 : gameF 25 25 = 44 := by
  apply gameF_value_of_source_mex (q := 25) (r := 25) (m := 44)
  · omega
  · omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨24, by omega, by simpa⟩

@[simp] theorem r195_gameF_26_25 : gameF 26 25 = 43 := by
  apply gameF_value_of_source_mex (q := 26) (r := 25) (m := 43)
  · omega
  · rw [r195_gameF_25_25]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩

@[simp] theorem r195_gameF_27_25 : gameF 27 25 = 46 := by
  apply gameF_value_of_source_mex (q := 27) (r := 25) (m := 46)
  · omega
  · rw [r195_gameF_26_25]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inr ⟨24, by omega, by simpa⟩

@[simp] theorem r195_gameF_28_25 : gameF 28 25 = 41 := by
  apply gameF_value_of_source_mex (q := 28) (r := 25) (m := 41)
  · omega
  · rw [r195_gameF_27_25]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩

@[simp] theorem r195_gameF_29_25 : gameF 29 25 = 47 := by
  apply gameF_value_of_source_mex (q := 29) (r := 25) (m := 47)
  · omega
  · rw [r195_gameF_28_25]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩

@[simp] theorem r195_gameF_30_25 : gameF 30 25 = 38 := by
  apply gameF_value_of_source_mex (q := 30) (r := 25) (m := 38)
  · omega
  · rw [r195_gameF_29_25]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩

@[simp] theorem r195_gameF_31_25 : gameF 31 25 = 48 := by
  apply gameF_value_of_source_mex (q := 31) (r := 25) (m := 48)
  · omega
  · rw [r195_gameF_30_25]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inr ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩

@[simp] theorem r195_gameF_32_25 : gameF 32 25 = 45 := by
  apply gameF_value_of_source_mex (q := 32) (r := 25) (m := 45)
  · omega
  · rw [r195_gameF_31_25]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩

@[simp] theorem r195_gameF_33_25 : gameF 33 25 = 49 := by
  apply gameF_value_of_source_mex (q := 33) (r := 25) (m := 49)
  · omega
  · rw [r195_gameF_32_25]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩

@[simp] theorem r195_gameF_34_25 : gameF 34 25 = 50 := by
  apply gameF_value_of_source_mex (q := 34) (r := 25) (m := 50)
  · omega
  · rw [r195_gameF_33_25]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩

@[simp] theorem r195_gameF_35_25 : gameF 35 25 = 51 := by
  apply gameF_value_of_source_mex (q := 35) (r := 25) (m := 51)
  · omega
  · rw [r195_gameF_34_25]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨34, by omega, by simpa⟩

@[simp] theorem r195_gameF_36_25 : gameF 36 25 = 36 := by
  apply gameF_value_of_source_mex (q := 36) (r := 25) (m := 36)
  · omega
  · rw [r195_gameF_35_25]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩

/-- Constant rail in column 25, stabilized at row 36. -/
@[simp] theorem gameF_col25_rail {q : Nat} (hq : 36 <= q) : gameF q 25 = 36 := by
  have hsmall : gameF 36 25 < 36 + 1 := by
    rw [r195_gameF_36_25]
    omega
  have hconst := constant_from gameRecurrenceModel
    (q := 36) (r := 25) (by omega) hsmall (q - 36)
  change gameF (36 + (q - 36)) 25 = gameF 36 25 at hconst
  have hsum : 36 + (q - 36) = q := by omega
  rw [hsum, r195_gameF_36_25] at hconst
  exact hconst

attribute [local simp] gameF_col25_rail

/-! ## Column 26 -/

@[simp] theorem r195_gameF_26_26 : gameF 26 26 = 45 := by
  apply gameF_value_of_source_mex (q := 26) (r := 26) (m := 45)
  · omega
  · omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩

@[simp] theorem r195_gameF_27_26 : gameF 27 26 = 47 := by
  apply gameF_value_of_source_mex (q := 27) (r := 26) (m := 47)
  · omega
  · rw [r195_gameF_26_26]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩

@[simp] theorem r195_gameF_28_26 : gameF 28 26 = 46 := by
  apply gameF_value_of_source_mex (q := 28) (r := 26) (m := 46)
  · omega
  · rw [r195_gameF_27_26]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩

@[simp] theorem r195_gameF_29_26 : gameF 29 26 = 48 := by
  apply gameF_value_of_source_mex (q := 29) (r := 26) (m := 48)
  · omega
  · rw [r195_gameF_28_26]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩

@[simp] theorem r195_gameF_30_26 : gameF 30 26 = 43 := by
  apply gameF_value_of_source_mex (q := 30) (r := 26) (m := 43)
  · omega
  · rw [r195_gameF_29_26]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩

@[simp] theorem r195_gameF_31_26 : gameF 31 26 = 49 := by
  apply gameF_value_of_source_mex (q := 31) (r := 26) (m := 49)
  · omega
  · rw [r195_gameF_30_26]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩

@[simp] theorem r195_gameF_32_26 : gameF 32 26 = 50 := by
  apply gameF_value_of_source_mex (q := 32) (r := 26) (m := 50)
  · omega
  · rw [r195_gameF_31_26]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩

@[simp] theorem r195_gameF_33_26 : gameF 33 26 = 41 := by
  apply gameF_value_of_source_mex (q := 33) (r := 26) (m := 41)
  · omega
  · rw [r195_gameF_32_26]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩

@[simp] theorem r195_gameF_34_26 : gameF 34 26 = 51 := by
  apply gameF_value_of_source_mex (q := 34) (r := 26) (m := 51)
  · omega
  · rw [r195_gameF_33_26]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩

@[simp] theorem r195_gameF_35_26 : gameF 35 26 = 38 := by
  apply gameF_value_of_source_mex (q := 35) (r := 26) (m := 38)
  · omega
  · rw [r195_gameF_34_26]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩

/-- Affine rail in column 26: F(q,26)=q+16 from row 36. -/
theorem gameF_col26_rail {q : Nat} (hq : 36 <= q) : gameF q 26 = q + 16 := by
  apply gameF_affine_fixed_column_of_source_frame
      (c := 26) (t := 36) (d := 16) (q := q) (by omega) (by omega)
  · rw [r195_gameF_35_26]
    omega
  · intro a ha
    have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro row hrow b hb
    have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [gameF_col14_rail (q := row) (by omega)]; omega
    · rw [gameF_col15_rail (q := row) (by omega)]; omega
    · rw [gameF_col16_rail (q := row) (by omega)]; omega
    · rw [gameF_col17_rail (q := row) (by omega)]; omega
    · rw [gameF_col18_rail (q := row) (by omega)]; omega
    · rw [gameF_col19_rail (q := row) (by omega)]; omega
    · rw [gameF_col20_rail (q := row) (by omega)]; omega
    · rw [gameF_col21_rail (q := row) (by omega)]; omega
    · rw [gameF_col22_rail (q := row) (by omega)]; omega
    · rw [gameF_col23_rail (q := row) (by omega)]; omega
    · rw [gameF_col24_rail (q := row) (by omega)]; omega
    · rw [gameF_col25_rail (q := row) (by omega)]; omega
  · intro row hrow k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa using gameF_col1_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa using gameF_col3_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa using gameF_col4_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa using gameF_col6_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa using gameF_col8_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa using gameF_col10_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa using gameF_col12_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa using gameF_col13_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa using gameF_col15_rail (q := row) (by omega)⟩
    · exact Or.inr ⟨16, by omega, by simpa using gameF_col16_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa using gameF_col18_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa using gameF_col20_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa using gameF_col21_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa using gameF_col23_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa using gameF_col25_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨35, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨34, by omega, by simpa⟩
  · exact hq

attribute [local simp] gameF_col26_rail

/-! ## Column 27 -/

@[simp] theorem r195_gameF_27_27 : gameF 27 27 = 48 := by
  apply gameF_value_of_source_mex (q := 27) (r := 27) (m := 48)
  · omega
  · omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inr ⟨26, by omega, by simpa⟩

@[simp] theorem r195_gameF_28_27 : gameF 28 27 = 47 := by
  apply gameF_value_of_source_mex (q := 28) (r := 27) (m := 47)
  · omega
  · rw [r195_gameF_27_27]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨26, by omega, by simpa⟩

@[simp] theorem r195_gameF_29_27 : gameF 29 27 = 49 := by
  apply gameF_value_of_source_mex (q := 29) (r := 27) (m := 49)
  · omega
  · rw [r195_gameF_28_27]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩

@[simp] theorem r195_gameF_30_27 : gameF 30 27 = 50 := by
  apply gameF_value_of_source_mex (q := 30) (r := 27) (m := 50)
  · omega
  · rw [r195_gameF_29_27]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩

@[simp] theorem r195_gameF_31_27 : gameF 31 27 = 46 := by
  apply gameF_value_of_source_mex (q := 31) (r := 27) (m := 46)
  · omega
  · rw [r195_gameF_30_27]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩

@[simp] theorem r195_gameF_32_27 : gameF 32 27 = 51 := by
  apply gameF_value_of_source_mex (q := 32) (r := 27) (m := 51)
  · omega
  · rw [r195_gameF_31_27]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩

@[simp] theorem r195_gameF_33_27 : gameF 33 27 = 43 := by
  apply gameF_value_of_source_mex (q := 33) (r := 27) (m := 43)
  · omega
  · rw [r195_gameF_32_27]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩

@[simp] theorem r195_gameF_34_27 : gameF 34 27 = 52 := by
  apply gameF_value_of_source_mex (q := 34) (r := 27) (m := 52)
  · omega
  · rw [r195_gameF_33_27]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩

@[simp] theorem r195_gameF_35_27 : gameF 35 27 = 53 := by
  apply gameF_value_of_source_mex (q := 35) (r := 27) (m := 53)
  · omega
  · rw [r195_gameF_34_27]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨34, by omega, by simpa⟩

@[simp] theorem r195_gameF_36_27 : gameF 36 27 = 54 := by
  apply gameF_value_of_source_mex (q := 36) (r := 27) (m := 54)
  · omega
  · rw [r195_gameF_35_27]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨34, by omega, by simpa⟩
    · exact Or.inl ⟨35, by omega, by simpa⟩

@[simp] theorem r195_gameF_37_27 : gameF 37 27 = 55 := by
  apply gameF_value_of_source_mex (q := 37) (r := 27) (m := 55)
  · omega
  · rw [r195_gameF_36_27]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 \/ a = 36 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 \/ k = 54 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨34, by omega, by simpa⟩
    · exact Or.inl ⟨35, by omega, by simpa⟩
    · exact Or.inl ⟨36, by omega, by simpa⟩

@[simp] theorem r195_gameF_38_27 : gameF 38 27 = 38 := by
  apply gameF_value_of_source_mex (q := 38) (r := 27) (m := 38)
  · omega
  · rw [r195_gameF_37_27]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 \/ a = 36 \/ a = 37 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩

/-- Constant rail in column 27, stabilized at row 38. -/
@[simp] theorem gameF_col27_rail {q : Nat} (hq : 38 <= q) : gameF q 27 = 38 := by
  have hsmall : gameF 38 27 < 38 + 1 := by
    rw [r195_gameF_38_27]
    omega
  have hconst := constant_from gameRecurrenceModel
    (q := 38) (r := 27) (by omega) hsmall (q - 38)
  change gameF (38 + (q - 38)) 27 = gameF 38 27 at hconst
  have hsum : 38 + (q - 38) = q := by omega
  rw [hsum, r195_gameF_38_27] at hconst
  exact hconst

attribute [local simp] gameF_col27_rail

/-! ## Column 28 -/

@[simp] theorem r195_gameF_28_28 : gameF 28 28 = 49 := by
  apply gameF_value_of_source_mex (q := 28) (r := 28) (m := 49)
  · omega
  · omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩

@[simp] theorem r195_gameF_29_28 : gameF 29 28 = 50 := by
  apply gameF_value_of_source_mex (q := 29) (r := 28) (m := 50)
  · omega
  · rw [r195_gameF_28_28]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩

@[simp] theorem r195_gameF_30_28 : gameF 30 28 = 51 := by
  apply gameF_value_of_source_mex (q := 30) (r := 28) (m := 51)
  · omega
  · rw [r195_gameF_29_28]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩

@[simp] theorem r195_gameF_31_28 : gameF 31 28 = 47 := by
  apply gameF_value_of_source_mex (q := 31) (r := 28) (m := 47)
  · omega
  · rw [r195_gameF_30_28]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩

@[simp] theorem r195_gameF_32_28 : gameF 32 28 = 52 := by
  apply gameF_value_of_source_mex (q := 32) (r := 28) (m := 52)
  · omega
  · rw [r195_gameF_31_28]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩

@[simp] theorem r195_gameF_33_28 : gameF 33 28 = 46 := by
  apply gameF_value_of_source_mex (q := 33) (r := 28) (m := 46)
  · omega
  · rw [r195_gameF_32_28]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩

@[simp] theorem r195_gameF_34_28 : gameF 34 28 = 53 := by
  apply gameF_value_of_source_mex (q := 34) (r := 28) (m := 53)
  · omega
  · rw [r195_gameF_33_28]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩

@[simp] theorem r195_gameF_35_28 : gameF 35 28 = 43 := by
  apply gameF_value_of_source_mex (q := 35) (r := 28) (m := 43)
  · omega
  · rw [r195_gameF_34_28]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩

@[simp] theorem r195_gameF_36_28 : gameF 36 28 = 55 := by
  apply gameF_value_of_source_mex (q := 36) (r := 28) (m := 55)
  · omega
  · rw [r195_gameF_35_28]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 \/ k = 54 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨35, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨34, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩

@[simp] theorem r195_gameF_37_28 : gameF 37 28 = 54 := by
  apply gameF_value_of_source_mex (q := 37) (r := 28) (m := 54)
  · omega
  · rw [r195_gameF_36_28]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 \/ a = 36 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨35, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨34, by omega, by simpa⟩

@[simp] theorem r195_gameF_38_28 : gameF 38 28 = 41 := by
  apply gameF_value_of_source_mex (q := 38) (r := 28) (m := 41)
  · omega
  · rw [r195_gameF_37_28]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 \/ a = 36 \/ a = 37 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩

/-- Affine rail in column 28: F(q,28)=q+17 from row 39. -/
theorem gameF_col28_rail {q : Nat} (hq : 39 <= q) : gameF q 28 = q + 17 := by
  apply gameF_affine_fixed_column_of_source_frame
      (c := 28) (t := 39) (d := 17) (q := q) (by omega) (by omega)
  · rw [r195_gameF_38_28]
    omega
  · intro a ha
    have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 \/ a = 36 \/ a = 37 \/ a = 38 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro row hrow b hb
    have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [gameF_col14_rail (q := row) (by omega)]; omega
    · rw [gameF_col15_rail (q := row) (by omega)]; omega
    · rw [gameF_col16_rail (q := row) (by omega)]; omega
    · rw [gameF_col17_rail (q := row) (by omega)]; omega
    · rw [gameF_col18_rail (q := row) (by omega)]; omega
    · rw [gameF_col19_rail (q := row) (by omega)]; omega
    · rw [gameF_col20_rail (q := row) (by omega)]; omega
    · rw [gameF_col21_rail (q := row) (by omega)]; omega
    · rw [gameF_col22_rail (q := row) (by omega)]; omega
    · rw [gameF_col23_rail (q := row) (by omega)]; omega
    · rw [gameF_col24_rail (q := row) (by omega)]; omega
    · rw [gameF_col25_rail (q := row) (by omega)]; omega
    · rw [gameF_col26_rail (q := row) (by omega)]; omega
    · rw [gameF_col27_rail (q := row) (by omega)]; omega
  · intro row hrow k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 \/ k = 54 \/ k = 55 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa using gameF_col1_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa using gameF_col3_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa using gameF_col4_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa using gameF_col6_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa using gameF_col8_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa using gameF_col10_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa using gameF_col12_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa using gameF_col13_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa using gameF_col15_rail (q := row) (by omega)⟩
    · exact Or.inr ⟨16, by omega, by simpa using gameF_col16_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa using gameF_col18_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa using gameF_col20_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa using gameF_col21_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa using gameF_col23_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa using gameF_col25_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa using gameF_col27_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨38, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨35, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨34, by omega, by simpa⟩
    · exact Or.inl ⟨37, by omega, by simpa⟩
    · exact Or.inl ⟨36, by omega, by simpa⟩
  · exact hq

attribute [local simp] gameF_col28_rail

/-! ## Column 29 -/

@[simp] theorem r195_gameF_29_29 : gameF 29 29 = 51 := by
  apply gameF_value_of_source_mex (q := 29) (r := 29) (m := 51)
  · omega
  · omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inr ⟨28, by omega, by simpa⟩

@[simp] theorem r195_gameF_30_29 : gameF 30 29 = 52 := by
  apply gameF_value_of_source_mex (q := 30) (r := 29) (m := 52)
  · omega
  · rw [r195_gameF_29_29]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩

@[simp] theorem r195_gameF_31_29 : gameF 31 29 = 50 := by
  apply gameF_value_of_source_mex (q := 31) (r := 29) (m := 50)
  · omega
  · rw [r195_gameF_30_29]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inr ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩

@[simp] theorem r195_gameF_32_29 : gameF 32 29 = 53 := by
  apply gameF_value_of_source_mex (q := 32) (r := 29) (m := 53)
  · omega
  · rw [r195_gameF_31_29]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨22, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩

@[simp] theorem r195_gameF_33_29 : gameF 33 29 = 54 := by
  apply gameF_value_of_source_mex (q := 33) (r := 29) (m := 54)
  · omega
  · rw [r195_gameF_32_29]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨28, by omega, by simpa⟩
    · exact Or.inr ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩

@[simp] theorem r195_gameF_34_29 : gameF 34 29 = 47 := by
  apply gameF_value_of_source_mex (q := 34) (r := 29) (m := 47)
  · omega
  · rw [r195_gameF_33_29]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨19, by omega, by simpa⟩

@[simp] theorem r195_gameF_35_29 : gameF 35 29 = 55 := by
  apply gameF_value_of_source_mex (q := 35) (r := 29) (m := 55)
  · omega
  · rw [r195_gameF_34_29]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 \/ k = 54 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨34, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩

@[simp] theorem r195_gameF_36_29 : gameF 36 29 = 46 := by
  apply gameF_value_of_source_mex (q := 36) (r := 29) (m := 46)
  · omega
  · rw [r195_gameF_35_29]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩

@[simp] theorem r195_gameF_37_29 : gameF 37 29 = 56 := by
  apply gameF_value_of_source_mex (q := 37) (r := 29) (m := 56)
  · omega
  · rw [r195_gameF_36_29]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 \/ a = 36 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 \/ k = 54 \/ k = 55 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨36, by omega, by simpa⟩
    · exact Or.inl ⟨34, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨35, by omega, by simpa⟩

@[simp] theorem r195_gameF_38_29 : gameF 38 29 = 57 := by
  apply gameF_value_of_source_mex (q := 38) (r := 29) (m := 57)
  · omega
  · rw [r195_gameF_37_29]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 \/ a = 36 \/ a = 37 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 \/ k = 54 \/ k = 55 \/ k = 56 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨36, by omega, by simpa⟩
    · exact Or.inl ⟨34, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨35, by omega, by simpa⟩
    · exact Or.inl ⟨37, by omega, by simpa⟩

@[simp] theorem r195_gameF_39_29 : gameF 39 29 = 58 := by
  apply gameF_value_of_source_mex (q := 39) (r := 29) (m := 58)
  · omega
  · rw [r195_gameF_38_29]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 \/ a = 36 \/ a = 37 \/ a = 38 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 \/ k = 54 \/ k = 55 \/ k = 56 \/ k = 57 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨36, by omega, by simpa⟩
    · exact Or.inl ⟨34, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨35, by omega, by simpa⟩
    · exact Or.inl ⟨37, by omega, by simpa⟩
    · exact Or.inl ⟨38, by omega, by simpa⟩

@[simp] theorem r195_gameF_40_29 : gameF 40 29 = 43 := by
  apply gameF_value_of_source_mex (q := 40) (r := 29) (m := 43)
  · omega
  · rw [r195_gameF_39_29]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 \/ a = 36 \/ a = 37 \/ a = 38 \/ a = 39 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩

@[simp] theorem r195_gameF_41_29 : gameF 41 29 = 41 := by
  apply gameF_value_of_source_mex (q := 41) (r := 29) (m := 41)
  · omega
  · rw [r195_gameF_40_29]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 \/ a = 36 \/ a = 37 \/ a = 38 \/ a = 39 \/ a = 40 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩

/-- Constant rail in column 29, stabilized at row 41. -/
@[simp] theorem gameF_col29_rail {q : Nat} (hq : 41 <= q) : gameF q 29 = 41 := by
  have hsmall : gameF 41 29 < 41 + 1 := by
    rw [r195_gameF_41_29]
    omega
  have hconst := constant_from gameRecurrenceModel
    (q := 41) (r := 29) (by omega) hsmall (q - 41)
  change gameF (41 + (q - 41)) 29 = gameF 41 29 at hconst
  have hsum : 41 + (q - 41) = q := by omega
  rw [hsum, r195_gameF_41_29] at hconst
  exact hconst

attribute [local simp] gameF_col29_rail

/-! ## Column 30 -/

@[simp] theorem r195_gameF_30_30 : gameF 30 30 = 53 := by
  apply gameF_value_of_source_mex (q := 30) (r := 30) (m := 53)
  · omega
  · omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inr ⟨29, by omega, by simpa⟩

@[simp] theorem r195_gameF_31_30 : gameF 31 30 = 52 := by
  apply gameF_value_of_source_mex (q := 31) (r := 30) (m := 52)
  · omega
  · rw [r195_gameF_30_30]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inr ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inr ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩

@[simp] theorem r195_gameF_32_30 : gameF 32 30 = 54 := by
  apply gameF_value_of_source_mex (q := 32) (r := 30) (m := 54)
  · omega
  · rw [r195_gameF_31_30]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨22, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inr ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩

@[simp] theorem r195_gameF_33_30 : gameF 33 30 = 50 := by
  apply gameF_value_of_source_mex (q := 33) (r := 30) (m := 50)
  · omega
  · rw [r195_gameF_32_30]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨28, by omega, by simpa⟩
    · exact Or.inr ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩

@[simp] theorem r195_gameF_34_30 : gameF 34 30 = 55 := by
  apply gameF_value_of_source_mex (q := 34) (r := 30) (m := 55)
  · omega
  · rw [r195_gameF_33_30]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 \/ k = 54 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inr ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩

@[simp] theorem r195_gameF_35_30 : gameF 35 30 = 56 := by
  apply gameF_value_of_source_mex (q := 35) (r := 30) (m := 56)
  · omega
  · rw [r195_gameF_34_30]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 \/ k = 54 \/ k = 55 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨34, by omega, by simpa⟩

@[simp] theorem r195_gameF_36_30 : gameF 36 30 = 57 := by
  apply gameF_value_of_source_mex (q := 36) (r := 30) (m := 57)
  · omega
  · rw [r195_gameF_35_30]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 \/ k = 54 \/ k = 55 \/ k = 56 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨29, by omega, by simpa⟩
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨34, by omega, by simpa⟩
    · exact Or.inl ⟨35, by omega, by simpa⟩

@[simp] theorem r195_gameF_37_30 : gameF 37 30 = 47 := by
  apply gameF_value_of_source_mex (q := 37) (r := 30) (m := 47)
  · omega
  · rw [r195_gameF_36_30]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 \/ a = 36 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩

@[simp] theorem r195_gameF_38_30 : gameF 38 30 = 46 := by
  apply gameF_value_of_source_mex (q := 38) (r := 30) (m := 46)
  · omega
  · rw [r195_gameF_37_30]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 \/ a = 36 \/ a = 37 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩

@[simp] theorem r195_gameF_39_30 : gameF 39 30 = 59 := by
  apply gameF_value_of_source_mex (q := 39) (r := 30) (m := 59)
  · omega
  · rw [r195_gameF_38_30]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 \/ a = 36 \/ a = 37 \/ a = 38 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 \/ k = 54 \/ k = 55 \/ k = 56 \/ k = 57 \/ k = 58 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨38, by omega, by simpa⟩
    · exact Or.inl ⟨37, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨34, by omega, by simpa⟩
    · exact Or.inl ⟨35, by omega, by simpa⟩
    · exact Or.inl ⟨36, by omega, by simpa⟩
    · exact Or.inr ⟨29, by omega, by simpa⟩

@[simp] theorem r195_gameF_40_30 : gameF 40 30 = 58 := by
  apply gameF_value_of_source_mex (q := 40) (r := 30) (m := 58)
  · omega
  · rw [r195_gameF_39_30]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 \/ a = 36 \/ a = 37 \/ a = 38 \/ a = 39 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 \/ k = 54 \/ k = 55 \/ k = 56 \/ k = 57 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨38, by omega, by simpa⟩
    · exact Or.inl ⟨37, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨34, by omega, by simpa⟩
    · exact Or.inl ⟨35, by omega, by simpa⟩
    · exact Or.inl ⟨36, by omega, by simpa⟩

@[simp] theorem r195_gameF_41_30 : gameF 41 30 = 60 := by
  apply gameF_value_of_source_mex (q := 41) (r := 30) (m := 60)
  · omega
  · rw [r195_gameF_40_30]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 \/ a = 36 \/ a = 37 \/ a = 38 \/ a = 39 \/ a = 40 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 \/ k = 54 \/ k = 55 \/ k = 56 \/ k = 57 \/ k = 58 \/ k = 59 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨38, by omega, by simpa⟩
    · exact Or.inl ⟨37, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨34, by omega, by simpa⟩
    · exact Or.inl ⟨35, by omega, by simpa⟩
    · exact Or.inl ⟨36, by omega, by simpa⟩
    · exact Or.inl ⟨40, by omega, by simpa⟩
    · exact Or.inl ⟨39, by omega, by simpa⟩

@[simp] theorem r195_gameF_42_30 : gameF 42 30 = 61 := by
  apply gameF_value_of_source_mex (q := 42) (r := 30) (m := 61)
  · omega
  · rw [r195_gameF_41_30]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 \/ a = 36 \/ a = 37 \/ a = 38 \/ a = 39 \/ a = 40 \/ a = 41 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 \/ k = 54 \/ k = 55 \/ k = 56 \/ k = 57 \/ k = 58 \/ k = 59 \/ k = 60 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨38, by omega, by simpa⟩
    · exact Or.inl ⟨37, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨34, by omega, by simpa⟩
    · exact Or.inl ⟨35, by omega, by simpa⟩
    · exact Or.inl ⟨36, by omega, by simpa⟩
    · exact Or.inl ⟨40, by omega, by simpa⟩
    · exact Or.inl ⟨39, by omega, by simpa⟩
    · exact Or.inl ⟨41, by omega, by simpa⟩

@[simp] theorem r195_gameF_43_30 : gameF 43 30 = 43 := by
  apply gameF_value_of_source_mex (q := 43) (r := 30) (m := 43)
  · omega
  · rw [r195_gameF_42_30]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 \/ a = 36 \/ a = 37 \/ a = 38 \/ a = 39 \/ a = 40 \/ a = 41 \/ a = 42 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩

/-- Constant rail in column 30, stabilized at row 43. -/
@[simp] theorem gameF_col30_rail {q : Nat} (hq : 43 <= q) : gameF q 30 = 43 := by
  have hsmall : gameF 43 30 < 43 + 1 := by
    rw [r195_gameF_43_30]
    omega
  have hconst := constant_from gameRecurrenceModel
    (q := 43) (r := 30) (by omega) hsmall (q - 43)
  change gameF (43 + (q - 43)) 30 = gameF 43 30 at hconst
  have hsum : 43 + (q - 43) = q := by omega
  rw [hsum, r195_gameF_43_30] at hconst
  exact hconst

attribute [local simp] gameF_col30_rail

/-! ## Column 31 -/

@[simp] theorem r195_gameF_31_31 : gameF 31 31 = 54 := by
  apply gameF_value_of_source_mex (q := 31) (r := 31) (m := 54)
  · omega
  · omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 \/ b = 30 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inr ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inr ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inr ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩

@[simp] theorem r195_gameF_32_31 : gameF 32 31 = 55 := by
  apply gameF_value_of_source_mex (q := 32) (r := 31) (m := 55)
  · omega
  · rw [r195_gameF_31_31]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 \/ b = 30 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 \/ k = 54 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨22, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inr ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inr ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩

@[simp] theorem r195_gameF_33_31 : gameF 33 31 = 52 := by
  apply gameF_value_of_source_mex (q := 33) (r := 31) (m := 52)
  · omega
  · rw [r195_gameF_32_31]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 \/ b = 30 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨28, by omega, by simpa⟩
    · exact Or.inr ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inr ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩

@[simp] theorem r195_gameF_34_31 : gameF 34 31 = 56 := by
  apply gameF_value_of_source_mex (q := 34) (r := 31) (m := 56)
  · omega
  · rw [r195_gameF_33_31]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 \/ b = 30 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 \/ k = 54 \/ k = 55 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inr ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩

@[simp] theorem r195_gameF_35_31 : gameF 35 31 = 57 := by
  apply gameF_value_of_source_mex (q := 35) (r := 31) (m := 57)
  · omega
  · rw [r195_gameF_34_31]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 \/ b = 30 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 \/ k = 54 \/ k = 55 \/ k = 56 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inr ⟨24, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨34, by omega, by simpa⟩

@[simp] theorem r195_gameF_36_31 : gameF 36 31 = 58 := by
  apply gameF_value_of_source_mex (q := 36) (r := 31) (m := 58)
  · omega
  · rw [r195_gameF_35_31]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 \/ b = 30 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 \/ k = 54 \/ k = 55 \/ k = 56 \/ k = 57 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨29, by omega, by simpa⟩
    · exact Or.inr ⟨17, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inr ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨34, by omega, by simpa⟩
    · exact Or.inl ⟨35, by omega, by simpa⟩

@[simp] theorem r195_gameF_37_31 : gameF 37 31 = 50 := by
  apply gameF_value_of_source_mex (q := 37) (r := 31) (m := 50)
  · omega
  · rw [r195_gameF_36_31]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 \/ a = 36 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 \/ b = 30 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩

@[simp] theorem r195_gameF_38_31 : gameF 38 31 = 59 := by
  apply gameF_value_of_source_mex (q := 38) (r := 31) (m := 59)
  · omega
  · rw [r195_gameF_37_31]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 \/ a = 36 \/ a = 37 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 \/ b = 30 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 \/ k = 54 \/ k = 55 \/ k = 56 \/ k = 57 \/ k = 58 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨30, by omega, by simpa⟩
    · exact Or.inr ⟨14, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨37, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨34, by omega, by simpa⟩
    · exact Or.inl ⟨35, by omega, by simpa⟩
    · exact Or.inl ⟨36, by omega, by simpa⟩

@[simp] theorem r195_gameF_39_31 : gameF 39 31 = 47 := by
  apply gameF_value_of_source_mex (q := 39) (r := 31) (m := 47)
  · omega
  · rw [r195_gameF_38_31]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 \/ a = 36 \/ a = 37 \/ a = 38 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 \/ b = 30 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨11, by omega, by simpa⟩

@[simp] theorem r195_gameF_40_31 : gameF 40 31 = 60 := by
  apply gameF_value_of_source_mex (q := 40) (r := 31) (m := 60)
  · omega
  · rw [r195_gameF_39_31]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 \/ a = 36 \/ a = 37 \/ a = 38 \/ a = 39 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 \/ b = 30 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 \/ k = 54 \/ k = 55 \/ k = 56 \/ k = 57 \/ k = 58 \/ k = 59 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨9, by omega, by simpa⟩
    · exact Or.inl ⟨39, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨37, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨34, by omega, by simpa⟩
    · exact Or.inl ⟨35, by omega, by simpa⟩
    · exact Or.inl ⟨36, by omega, by simpa⟩
    · exact Or.inl ⟨38, by omega, by simpa⟩

@[simp] theorem r195_gameF_41_31 : gameF 41 31 = 61 := by
  apply gameF_value_of_source_mex (q := 41) (r := 31) (m := 61)
  · omega
  · rw [r195_gameF_40_31]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 \/ a = 36 \/ a = 37 \/ a = 38 \/ a = 39 \/ a = 40 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 \/ b = 30 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 \/ k = 54 \/ k = 55 \/ k = 56 \/ k = 57 \/ k = 58 \/ k = 59 \/ k = 60 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨2, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨7, by omega, by simpa⟩
    · exact Or.inl ⟨39, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨37, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨34, by omega, by simpa⟩
    · exact Or.inl ⟨35, by omega, by simpa⟩
    · exact Or.inl ⟨36, by omega, by simpa⟩
    · exact Or.inl ⟨38, by omega, by simpa⟩
    · exact Or.inl ⟨40, by omega, by simpa⟩

@[simp] theorem r195_gameF_42_31 : gameF 42 31 = 62 := by
  apply gameF_value_of_source_mex (q := 42) (r := 31) (m := 62)
  · omega
  · rw [r195_gameF_41_31]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 \/ a = 36 \/ a = 37 \/ a = 38 \/ a = 39 \/ a = 40 \/ a = 41 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 \/ b = 30 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 \/ k = 54 \/ k = 55 \/ k = 56 \/ k = 57 \/ k = 58 \/ k = 59 \/ k = 60 \/ k = 61 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨0, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inr ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨39, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨37, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨34, by omega, by simpa⟩
    · exact Or.inl ⟨35, by omega, by simpa⟩
    · exact Or.inl ⟨36, by omega, by simpa⟩
    · exact Or.inl ⟨38, by omega, by simpa⟩
    · exact Or.inl ⟨40, by omega, by simpa⟩
    · exact Or.inl ⟨41, by omega, by simpa⟩

@[simp] theorem r195_gameF_43_31 : gameF 43 31 = 46 := by
  apply gameF_value_of_source_mex (q := 43) (r := 31) (m := 46)
  · omega
  · rw [r195_gameF_42_31]; omega
  · omega
  · rintro (⟨a, ha, hv⟩ | ⟨b, hb, hv⟩)
    · have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 \/ a = 36 \/ a = 37 \/ a = 38 \/ a = 39 \/ a = 40 \/ a = 41 \/ a = 42 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    · have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 \/ b = 30 := by omega
      rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa⟩
    · exact Or.inr ⟨16, by omega, by simpa⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩

/-- Affine rail in column 31: F(q,31)=q+19 from row 44. -/
theorem gameF_col31_rail {q : Nat} (hq : 44 <= q) : gameF q 31 = q + 19 := by
  apply gameF_affine_fixed_column_of_source_frame
      (c := 31) (t := 44) (d := 19) (q := q) (by omega) (by omega)
  · rw [r195_gameF_43_31]
    omega
  · intro a ha
    have hcase : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31 \/ a = 32 \/ a = 33 \/ a = 34 \/ a = 35 \/ a = 36 \/ a = 37 \/ a = 38 \/ a = 39 \/ a = 40 \/ a = 41 \/ a = 42 \/ a = 43 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro row hrow b hb
    have hcase : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 \/ b = 30 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [gameF_col14_rail (q := row) (by omega)]; omega
    · rw [gameF_col15_rail (q := row) (by omega)]; omega
    · rw [gameF_col16_rail (q := row) (by omega)]; omega
    · rw [gameF_col17_rail (q := row) (by omega)]; omega
    · rw [gameF_col18_rail (q := row) (by omega)]; omega
    · rw [gameF_col19_rail (q := row) (by omega)]; omega
    · rw [gameF_col20_rail (q := row) (by omega)]; omega
    · rw [gameF_col21_rail (q := row) (by omega)]; omega
    · rw [gameF_col22_rail (q := row) (by omega)]; omega
    · rw [gameF_col23_rail (q := row) (by omega)]; omega
    · rw [gameF_col24_rail (q := row) (by omega)]; omega
    · rw [gameF_col25_rail (q := row) (by omega)]; omega
    · rw [gameF_col26_rail (q := row) (by omega)]; omega
    · rw [gameF_col27_rail (q := row) (by omega)]; omega
    · rw [gameF_col28_rail (q := row) (by omega)]; omega
    · rw [gameF_col29_rail (q := row) (by omega)]; omega
    · rw [gameF_col30_rail (q := row) (by omega)]; omega
  · intro row hrow k hkpos hklt
    have hcase : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/ k = 34 \/ k = 35 \/ k = 36 \/ k = 37 \/ k = 38 \/ k = 39 \/ k = 40 \/ k = 41 \/ k = 42 \/ k = 43 \/ k = 44 \/ k = 45 \/ k = 46 \/ k = 47 \/ k = 48 \/ k = 49 \/ k = 50 \/ k = 51 \/ k = 52 \/ k = 53 \/ k = 54 \/ k = 55 \/ k = 56 \/ k = 57 \/ k = 58 \/ k = 59 \/ k = 60 \/ k = 61 \/ k = 62 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, by omega, by simpa⟩
    · exact Or.inr ⟨1, by omega, by simpa using gameF_col1_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨1, by omega, by simpa⟩
    · exact Or.inl ⟨2, by omega, by simpa⟩
    · exact Or.inr ⟨3, by omega, by simpa using gameF_col3_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨3, by omega, by simpa⟩
    · exact Or.inr ⟨4, by omega, by simpa using gameF_col4_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨4, by omega, by simpa⟩
    · exact Or.inr ⟨6, by omega, by simpa using gameF_col6_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨5, by omega, by simpa⟩
    · exact Or.inl ⟨6, by omega, by simpa⟩
    · exact Or.inr ⟨8, by omega, by simpa using gameF_col8_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨7, by omega, by simpa⟩
    · exact Or.inr ⟨10, by omega, by simpa using gameF_col10_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨8, by omega, by simpa⟩
    · exact Or.inl ⟨9, by omega, by simpa⟩
    · exact Or.inr ⟨12, by omega, by simpa using gameF_col12_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨10, by omega, by simpa⟩
    · exact Or.inr ⟨13, by omega, by simpa using gameF_col13_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨11, by omega, by simpa⟩
    · exact Or.inl ⟨12, by omega, by simpa⟩
    · exact Or.inr ⟨15, by omega, by simpa using gameF_col15_rail (q := row) (by omega)⟩
    · exact Or.inr ⟨16, by omega, by simpa using gameF_col16_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨13, by omega, by simpa⟩
    · exact Or.inl ⟨14, by omega, by simpa⟩
    · exact Or.inr ⟨18, by omega, by simpa using gameF_col18_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨15, by omega, by simpa⟩
    · exact Or.inl ⟨16, by omega, by simpa⟩
    · exact Or.inr ⟨20, by omega, by simpa using gameF_col20_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨17, by omega, by simpa⟩
    · exact Or.inr ⟨21, by omega, by simpa using gameF_col21_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨18, by omega, by simpa⟩
    · exact Or.inr ⟨23, by omega, by simpa using gameF_col23_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨19, by omega, by simpa⟩
    · exact Or.inl ⟨20, by omega, by simpa⟩
    · exact Or.inr ⟨25, by omega, by simpa using gameF_col25_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨21, by omega, by simpa⟩
    · exact Or.inr ⟨27, by omega, by simpa using gameF_col27_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨22, by omega, by simpa⟩
    · exact Or.inl ⟨23, by omega, by simpa⟩
    · exact Or.inr ⟨29, by omega, by simpa using gameF_col29_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨24, by omega, by simpa⟩
    · exact Or.inr ⟨30, by omega, by simpa using gameF_col30_rail (q := row) (by omega)⟩
    · exact Or.inl ⟨25, by omega, by simpa⟩
    · exact Or.inl ⟨26, by omega, by simpa⟩
    · exact Or.inl ⟨43, by omega, by simpa⟩
    · exact Or.inl ⟨39, by omega, by simpa⟩
    · exact Or.inl ⟨27, by omega, by simpa⟩
    · exact Or.inl ⟨28, by omega, by simpa⟩
    · exact Or.inl ⟨37, by omega, by simpa⟩
    · exact Or.inl ⟨29, by omega, by simpa⟩
    · exact Or.inl ⟨33, by omega, by simpa⟩
    · exact Or.inl ⟨30, by omega, by simpa⟩
    · exact Or.inl ⟨31, by omega, by simpa⟩
    · exact Or.inl ⟨32, by omega, by simpa⟩
    · exact Or.inl ⟨34, by omega, by simpa⟩
    · exact Or.inl ⟨35, by omega, by simpa⟩
    · exact Or.inl ⟨36, by omega, by simpa⟩
    · exact Or.inl ⟨38, by omega, by simpa⟩
    · exact Or.inl ⟨40, by omega, by simpa⟩
    · exact Or.inl ⟨41, by omega, by simpa⟩
    · exact Or.inl ⟨42, by omega, by simpa⟩
  · exact hq

attribute [local simp] gameF_col31_rail

#print axioms gameF_col25_rail
#print axioms gameF_col26_rail
#print axioms gameF_col27_rail
#print axioms gameF_col28_rail
#print axioms gameF_col29_rail
#print axioms gameF_col30_rail
#print axioms gameF_col31_rail

end ChompLean

